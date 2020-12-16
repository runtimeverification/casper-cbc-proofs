Require Import List ListSet.
Require Import Lia.

From CasperCBC
Require Import
  Lib.Preamble
  Lib.Classes
  CBC.FullNode.Validator.State
  VLSM.Common
  VLSM.Liveness
  VLSM.Composition
  VLSM.Equivocation (* for has_been_sent *)
.

(**
This module defines a simple consensus protocol, and
proves that it is live when there are no synchronization faults.
 *)

(** * Validators

The components are similar to [CBC.FullNode.Validator], except
that the states and messages all carry times, and the nodes
only send messages at the times given in a [Plan].
 *)
Section Define_Component.

  Context
    (C V:Type)
    {EqC: EqDecision C}
    {EqV: EqDecision V}
    (c0:C)
    (plan : nat -> V -> Prop)
  .

  Inductive validator_message : Type :=
    Msg (time:nat) (proposal:C) (proposer:V) (history:list validator_message).
  Global Instance validator_message_eq_dec : EqDecision validator_message.
  Proof using C V EqC EqV.
  refine (fix validator_message_eq_dec (m n : validator_message) {struct m} : Decision (m=n) :=
    match m, n with
    | Msg t1 c1 v1 msgs1, Msg t2 c2 v2 msgs2 =>
      if decide (t1 = t2) then
        if decide (c1 = c2) then
          if decide (v1 = v2) then
            if list_eq_dec validator_message_eq_dec msgs1 msgs2 then
              left _
            else right _
          else right _
        else right _
      else right _
    end);congruence.
  Defined.

  Fixpoint message_height (m: validator_message) {struct m}: nat :=
    match m with
    | Msg _ _ _ history => S (list_max (map message_height history))
    end.

  Lemma validator_message_well_founded:
    forall time c v history,
      ~In (Msg time c v history) history.
  Proof.
    intros t c v hist Hin.
    apply in_map with (f:=message_height) in Hin.
    assert (Forall (fun k => k <= list_max (map message_height hist)) (map message_height hist))
      by (apply list_max_le;reflexivity).
    rewrite Forall_forall in H.
    specialize (H _ Hin).
    revert H.
    apply PeanoNat.Nat.nle_succ_diag_l.
  Qed.

  Inductive validator_state : Type :=
    State (time:nat)
          (received:list validator_message)
          (sent:list validator_message)
          (finished_send:bool).

  Definition validator_time : validator_state -> nat :=
    fun '(State t _ _ _) => t.

  Definition initial_validator_state (s:validator_state) : Prop :=
    let (t,msgs,log,flag) := s in t = 0 /\ msgs = nil /\ log = nil /\ ~flag.
  Definition initial_validator_message (m:validator_message) : Prop := False.
  Inductive validator_label : Type :=
  | Proposal (c:C)
  | Tick.

  Definition record_receive
    : validator_message -> validator_state -> validator_state :=
    fun msg '(State t msgs log flag) =>
      State t (set_add decide_eq msg msgs) log flag.
  Definition record_send
    : validator_message -> validator_state -> validator_state :=
    fun msg '(State t msgs log flag) =>
      State t (set_add decide_eq msg msgs) (msg::log) flag.

  Context
    (estimator: list validator_message -> C -> Prop)
    (v:V)
    .

  Definition validator_transition (l:option validator_label) (sim:(validator_state * option validator_message)) : (validator_state * option validator_message) :=
    let (s,im) := sim in
    match l with
    | None =>
      (* Label is None for receiving messages *)
      match im with
      (* Receive the message *)
      | Some m => (record_receive m s,None)
      (* Receiving with no message will actually be ruled out
         by the validity predicate, just leave s unchanged *)
      | None => (s,None)
      end
    | Some Tick =>
      (* Advance clock *)
      let (n,msgs,log,f) := s in ((State (1+n) msgs log false),None)
    | Some (Proposal c) =>
      (* Send a proposal *)
      let (n,msgs,_,_) := s in
      let m := Msg n c v msgs in
      (record_send m s,Some m)
    end.


  (** "Mandatory flip-flopping"
     If the estimator allows multiple consensus values
     and the state has previously sent a proposals,
     the new proposal cannot match the immediately
     preceeding proposal.

     TODO: Is this sufficient for non-binary decisions?
   *)
  Definition flip_condition : validator_state -> C -> Prop :=
    fun '(State _ msgs log _) c =>
      match log with
      | nil => True
      | (Msg _ c' _ _::_) =>
        c <> c' \/ (forall c2, estimator msgs c2 -> c2 = c)
      end.

  (* TODO: This needs to be altered to require that we have recieved
     all earlier plan messages before we can assert or tick *)
  Definition validator_valid (l:option validator_label) (sim:(validator_state * option validator_message)) : Prop :=
    let (s,im) := sim in
    match l with
    | None =>
      match im with
        (* May not receive with no message *)
      | None => False
        (* A recevied message must
           (1) have not already been received,
           (2) satisfy the full node condition
           (3) must come from a time no earlier later than the clock of s,
               and can only be received from the current clock if either
               s has already produced its own mesage for this time,
               or this validator is not in the plan for this time at all
         *)
      | Some ((Msg n  _ _ msg_just) as m) => let (n',msgs,log,f) := s in
                              ~In m msgs
                              /\ incl msg_just msgs (* "full node condition" *)
                              /\ (n < n' \/ (n = n' /\ (f \/ ~plan n v)))
      end
    | Some Tick =>
      match im with
      | None => let (n,_,_,f) := s in f \/ ~plan n v
      | Some _ => False
      end
    | Some (Proposal c) =>
      match im with
      | None => let (n,msgs,log,f) := s in
                estimator msgs c
                /\ flip_condition s c
                /\ plan n v /\ ~f
      | Some _ => False
      end
    end.

  Instance Validator_type : VLSM_type validator_message :=
             {|state := validator_state
              ;label:= option validator_label
             |}.
  Instance Validator_sign : VLSM_sign Validator_type :=
    {| initial_state_prop := initial_validator_state;
       initial_message_prop := initial_validator_message;
       s0 := exist initial_validator_state (State 0 nil nil false)
                   (conj (eq_refl _) (conj (eq_refl _) (conj (eq_refl _) (fun H => H))));
       m0 := (Msg 0 c0 v nil);
       l0 := None
   |}.

  Instance Validator_machine : VLSM_class Validator_sign :=
    {| transition := validator_transition;
       valid := validator_valid
    |}.

  Definition Validator : VLSM validator_message :=
    mk_vlsm Validator_machine.

  Definition validator_clock_fn (s : vstate Validator) : nat
    := let '(State n _ _ _) := s in n.

  Lemma validator_clock_monotone: forall l s om s' om',
      vtransition Validator l (s,om) = (s',om') -> validator_clock_fn s <= validator_clock_fn s'.
  Proof using C V.
    intros l s om s' om' H.
    apply (f_equal fst) in H.
    simpl in H. subst s'.
    destruct s.
    unfold vtransition. simpl.
    repeat lazymatch goal with |- context [fst (match ?X with _ => _ end)] => destruct X end;
      simpl;solve[auto].
  Defined.

  Definition validator_clock: ClockFor Validator :=
    {| clock := validator_clock_fn;
       clock_monotone := validator_clock_monotone
    |}.


  Definition validator_has_been_sent : state_message_oracle Validator :=
    fun '(State _ _ sent _) m => In m sent.
  Definition validator_has_been_sent_dec : RelDecision validator_has_been_sent :=
    fun s m => let '(State _ _ sent _) := s in in_dec decide_eq m sent.

  Lemma validator_initial_not_sent:
    forall (s : vstate Validator),
      initial_state_prop s -> forall m : validator_message, ~ validator_has_been_sent s m.
  Proof using.
    intros [] Hinit m.
    simpl. assert (sent = nil) as -> by apply Hinit. tauto.
  Qed.

  Lemma validator_transition_updates_sent:
       forall l s im s' om,
         vtransition Validator l (s,im) = (s',om) ->
         forall msg, validator_has_been_sent s' msg
                     <-> (om = Some msg \/ validator_has_been_sent s msg).
  Proof using.
    intros l s im s' om Htrans msg.
    destruct s.
    unfold vtransition in Htrans.
    simpl in Htrans.
    destruct l as [[]|];[| |destruct im];
      inversion_clear Htrans;simpl;
      firstorder congruence.
  Qed.

  Definition validator_proper_sent :=
    prove_proper_sent_from_stepwise
      _ _ validator_has_been_sent
      validator_initial_not_sent
      validator_transition_updates_sent.
  Definition validator_proper_not_sent :=
    prove_proper_not_sent_from_stepwise
      _ _ validator_has_been_sent
      validator_initial_not_sent
      validator_transition_updates_sent.

  Global Instance validator_has_been_sent_capability : has_been_sent_capability Validator
    :=
      { has_been_sent := validator_has_been_sent;
        has_been_sent_dec := validator_has_been_sent_dec;
        proper_sent := validator_proper_sent;
        proper_not_sent := validator_proper_not_sent;
      }.

  (** N.B. this is not actually a [has_been_received_capability],
      because a validator counts a message as "received" when it
      sends it itself
   *)
  Definition validator_has_been_observed : validator_state -> validator_message -> Prop.
  Proof using.
    exact (fun '(State _ received _ _) m => In m received).
  Defined.
  Definition validator_has_been_observed_dec : RelDecision validator_has_been_observed.
  Proof using EqV EqC.
    exact (fun s m => let '(State _ received _ _) := s in in_dec decide_eq m received).
  Defined.

  Lemma validator_initial_not_observed:
    forall (s : vstate Validator),
      initial_state_prop s -> forall m : validator_message, ~ validator_has_been_observed s m.
  Proof using.
    intros [] Hinit m.
    simpl. assert (received = nil) as -> by apply Hinit. tauto.
  Qed.

  Lemma validator_transition_updates_observed:
       forall l s im s' om,
         protocol_transition Validator l (s,im) (s',om) ->
         forall msg, validator_has_been_observed s' msg
                     <-> (im = Some msg \/ om = Some msg \/ validator_has_been_observed s msg).
  Proof using.
    intros l s im s' om [[_ [_ Hvalid]] Htrans] msg.
    destruct s.
    unfold vtransition in Htrans.
    simpl in Htrans.
    cbn -[In flip_condition] in Hvalid.
    destruct l as [l'|].
    - destruct l'.
      + destruct im;[exfalso;assumption|clear Hvalid].
        inversion_clear Htrans.
        simpl;rewrite set_add_iff;firstorder congruence.
      + destruct im;[exfalso;assumption|clear Hvalid].
        inversion_clear Htrans.
        simpl;firstorder congruence.
    - destruct im;[|exfalso;assumption].
      inversion_clear Htrans;simpl.
      rewrite set_add_iff.
      destruct v0.
      firstorder congruence.
  Qed.
End Define_Component.

(** * Composition and Proofs

This section defines the composed protocol,
and gives proofs about it.
*)

Section Protocol_Proofs.
  Context
    (C V:Type)
    {EqC: EqDecision C}
    {EqV: EqDecision V}
    (c0:C)
    (plan : nat -> V -> Prop)
    {plan_dec : RelDecision plan}
    (ClientState := State.justification C V)
    (estimator: list (validator_message C V) -> C -> Prop)
    (validator_list: list V)
    (validators_finite: FinFun.Listing validator_list)
    (v0:V)
  .

  Definition IM : V -> VLSM (validator_message C V) :=
    fun v => Validator C V c0 plan estimator v.

  Definition simple_liveness_VLSM :=
    (Composition.composite_vlsm IM v0).

  Definition message_time (m: validator_message C V) : nat :=
    let (n,_,_,_) := m in n.

  (** *** Constructing a variant to show that
      a component's clock eventually ticks.
   *)

  Definition message_slots_before (t:nat) : list (nat * V) :=
    filter (fun '(n,v) => bool_decide (plan n v)) (set_prod (seq 0 t) validator_list).

  Definition received_message_slots (msgs:list (validator_message C V)) : list (nat * V) :=
    map (fun '(Msg _ _ n _ v _) => (n,v)) msgs.

  Definition unreceived_message_count_before (t:nat) (s: validator_state C V) : nat :=
    let '(State _ _ _ msgs _ _) := s in
    let received := received_message_slots msgs in
    length (filter (fun slot => if in_dec decide_eq slot received then false else true)
                   (message_slots_before t)).
  Definition validator_ticks_before (t:nat) (s: validator_state C V) : nat :=
    let '(State _ _ time _ _ _) := s in t - time.

  (** The component variant is an upper bound on the number of transitions the component
      can take before its clock exceeds <<t>>, by counting the number of plan
      slots for which it hasn't sent or received a message, and the number
      of times it can tick.
   *)
  Definition validator_variant (t:nat) (s: validator_state C V) : nat :=
    unreceived_message_count_before t s
    + validator_ticks_before t s.

  Context
    (constraint : composite_label IM -> composite_state IM * option (validator_message C V) -> Prop
       := no_synch_faults_no_equivocation_constraint v0 validators_finite IM
                 (fun v => validator_has_been_observed C V:state_message_oracle (IM v))
                 (validator_clock C V c0 plan estimator)
             message_time)
    (X: VLSM (validator_message C V) := composite_vlsm IM v0 constraint)
  .

  (** The overall variant used to show a given component eventually
      ticks adds up the bound for each component.
      To show that a given component eventually reaches a time <<t0>>,
      an argument about the structure of the plan
   *)
  Definition eventually_ticks_variant t (s: vstate X) : nat :=
    list_sum (map (fun v => validator_variant t (s v)) validator_list).

  Lemma state_update_variant_progress:
    forall t s i si',
      validator_variant t si' < validator_variant t (s i) ->
      eventually_ticks_variant t (state_update IM s i si') < eventually_ticks_variant t s.
  Proof.
    clear -validators_finite.
    intros t s i si' Hs'.
    set (s' := state_update IM s i si').
    assert (forall v, validator_variant t (s' v) <= validator_variant t (s v)).
    {
      intro v.
      unfold s',state_update.
      destruct (decide (v = i)).
      - destruct e. unfold eq_rect_r. simpl. apply PeanoNat.Nat.lt_le_incl. assumption.
      - apply le_n.
    }
    unfold eventually_ticks_variant.
    assert (In i validator_list) by (apply validators_finite).
    revert H0.
    clear X constraint validators_finite.
    induction validator_list;simpl;intro Hin.
    - exfalso;exact Hin.
    - destruct Hin as [->|Hin].
      + apply PeanoNat.Nat.add_lt_le_mono.
        * replace (s' i) with si'. assumption.
          unfold s',state_update.
          destruct (decide (i = i));[|congruence].
          destruct e.
          reflexivity.
        * clear -H.
          induction l as [|a l'];simpl;[|specialize (H a)];Lia.lia.
      + apply PeanoNat.Nat.add_le_lt_mono;auto.
  Qed.

  (* TODO: this property will not actually be true until
     we add a restriction about waiting for expected messages
     to the synchronization constraint and the validator definition.
     Perhaps this will also need to use a later time than <<<= t>>
     in <<H_times>> and the conclusion, depending how closely the
     modified conditions will keep the times of different nodes.
   *)
  Lemma early_validator_limits_clock_advance
        v t (s:vstate X)
      (H_time : validator_time _ _ (s v) < t)
      (H_plan : plan t v)
      (H_times : forall i, validator_time _ _ (s i) <= t):
    forall l im s' om,
      protocol_transition X l (s,im) (s',om) ->
      forall i, validator_time _ _ (s' i) <= t.
  Admitted.

  (** If all validator clock are below the time used in the
      variant, the the variant decreases.
   *)
  Lemma eventually_ticks_variant_progress t
        l (s:vstate X) im s' om
        (H_times : forall i, validator_time _ _ (s i) < t):
    protocol_transition X l (s,im) (s',om) ->
    eventually_ticks_variant t s' < eventually_ticks_variant t s.
  Proof.
    intros [Hvalid Htrans].
    destruct l as [i li] eqn:Heq_l.
    simpl in Htrans.
    rename om into _om.
    destruct (vtransition (IM i) li (s i, im)) as [si' om] eqn:H_transition.
    inversion_clear Htrans.
    destruct li as [[c|]|].
    - (* When sending a message, the sender recording their
         own message decreases the number of unreceived slots
         in their own variant *)
      apply state_update_variant_progress.
      unfold vtransition in H_transition.
      destruct (s i).
      simpl in Hvalid.
      simpl in H_transition.
      inversion_clear H_transition.
      unfold validator_variant.
      unfold validator_ticks_before.
      apply Plus.plus_lt_compat_r.
      (* we will need to rely on an invariant to
         conclude that received can't already have a
         message for the slot (time,i)
         and finish this inequality *)
      admit.
    - (* A node ticking decreases the clock-based apart
         of the variant *)
      apply state_update_variant_progress.
      unfold vtransition in H_transition.
      specialize (H_times i).
      destruct (s i).
      simpl in Hvalid, H_times, H_transition.
      inversion_clear H_transition.
      unfold validator_variant.
      unfold validator_ticks_before.
      apply Plus.plus_lt_compat_l.
      lia.
    - (* Receiving a message fills one of the
         receivers slots *)
      apply state_update_variant_progress.
      unfold vtransition in H_transition.
      destruct (s i).
      simpl in Hvalid.
      simpl in H_transition.
      destruct im.
      2:{ (* input message cannot be None *)
        destruct Hvalid as [_ [_ [Hcomponent_valid _]]].
        exfalso;exact Hcomponent_valid.
      }
      inversion_clear H_transition.
      unfold validator_variant.
      apply Plus.plus_lt_compat_r.
      (* we will need to rely on an invariant to
         conclude that received can't already have a
         message for the slot (time,i)
         and finish this inequality *)
      admit.
  Admitted.
End Protocol_Proofs.
