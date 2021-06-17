From Coq Require Import List ListSet Lia.

From CasperCBC
Require Import
  Lib.Preamble
  Lib.Classes
  Lib.ListSetExtras
  Lib.Measurable
  CBC.FullNode.Validator.State
  VLSM.Common
  VLSM.Liveness
  VLSM.Composition
  VLSM.Equivocation (* for has_been_sent *)
.

(** * VLSM Simple Live Protocol *)

(**
This module defines a simple consensus protocol, and
proves that it is live when there are no synchronization faults.
 *)

(** ** Validators

The components are similar to [CBC.FullNode.Validator], except
that the states and messages all carry times, and the nodes
only send messages at the times given in a [Plan].
 *)
Section Define_Component.

  Context
    {C V:Type}
    {EqC: EqDecision C}
    {EqV: EqDecision V}
    (c0:C)
    (plan : nat -> V -> Prop)
  .

  Inductive validator_message : Type :=
    Msg {message_time:nat;
         message_proposal: C;
         message_sender: V;
         message_justification: list validator_message
        }.
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

  Definition message_slot (m : validator_message) : (nat * V) :=
    let '(Msg t _ v _) := m in (t, v).

  Fixpoint message_height (m: validator_message) {struct m}: nat :=
    S (list_max (map message_height (message_justification m))).

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

  Definition validator_sends : validator_state -> list validator_message :=
    fun '(State _ _ sends _) => sends.

  Definition validator_received : validator_state -> list validator_message :=
    fun '(State _ received _ _) => received.

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
      let (n,known,sent,_) := s in
      let m := Msg n c v known in
      (State n
             (set_add decide_eq m known)
             (m::sent)
             true,
       Some m)
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

  Definition validator_valid (l:option validator_label)
             (sim:(validator_state * option validator_message)) : Prop :=
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
      | None =>
        (let (n,_,_,f) := s in f \/ ~plan n v)
        /\ (let (t,received,_,_) := s in
            forall v, plan t v -> In (t,v) (map message_slot received))
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
    {| state := validator_state;
       label:= option validator_label
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

  Lemma validator_clock_monotone: forall l s om s' om',
      vtransition Validator l (s,om) = (s',om') -> validator_time s <= validator_time s'.
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
    {| clock := validator_time: vstate Validator -> nat;
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

  Definition validator_sent_stepwise_props:
    has_been_sent_stepwise_props validator_has_been_sent :=
    {| oracle_no_inits := validator_initial_not_sent;
       oracle_step_update l s im s' om H :=
         (validator_transition_updates_sent l s im s' om (proj2 H));
    |}.

  Global Instance validator_has_been_sent_capability : has_been_sent_capability Validator
    := has_been_sent_capability_from_stepwise
         validator_has_been_sent_dec
         validator_sent_stepwise_props.

  Definition validator_has_been_observed : validator_state -> validator_message -> Prop
    := fun '(State _ received _ _) m => In m received.
  Definition validator_has_been_observed_dec : RelDecision validator_has_been_observed
    := fun s m => let '(State _ received _ _) := s in in_dec decide_eq m received.

  Lemma validator_initial_not_observed:
    forall (s : vstate Validator),
      initial_state_prop s -> forall m : validator_message, ~ validator_has_been_observed s m.
  Proof using.
    intros [] Hinit m.
    simpl. assert (received = nil) as -> by apply Hinit. tauto.
  Qed.

  Lemma validator_transition_updates_observed
        [l s im s' om]
        (Hptrans: protocol_transition (pre_loaded_with_all_messages_vlsm Validator) l (s,im) (s',om)):
    forall msg, validator_has_been_observed s' msg
                <-> ((im = Some msg \/ om = Some msg) \/ validator_has_been_observed s msg).
  Proof using.
    intro msg.
    destruct Hptrans as [[_ [_ Hvalid]] Htrans].
    destruct s.
    unfold vtransition in Htrans.
    simpl in Htrans.
    cbn -[In flip_condition] in Hvalid.
    destruct l as [l'|].
    - destruct l'.
      + destruct im;[exfalso;assumption|clear Hvalid].
        inversion_clear Htrans.
        simpl;rewrite set_add_iff.
        clear;intuition congruence.
      + destruct im;[exfalso;assumption|clear Hvalid].
        inversion_clear Htrans.
        simpl.
        clear;intuition congruence.
    - destruct im;[|exfalso;assumption].
      inversion_clear Htrans;simpl.
      rewrite set_add_iff.
      destruct v0.
      clear.
      clear;intuition congruence.
  Qed.

  Definition validator_observed_stepwise_props :
    oracle_stepwise_props (vlsm:=Validator) item_sends_or_receives validator_has_been_observed
    := {| oracle_no_inits := validator_initial_not_observed;
          oracle_step_update := validator_transition_updates_observed|}.

  Global Instance validator_has_been_observed_capability:
    has_been_observed_capability Validator :=
      {|has_been_observed := validator_has_been_observed: state_message_oracle Validator;
        has_been_observed_dec := validator_has_been_observed_dec;
        has_been_observed_stepwise_props :=
          validator_observed_stepwise_props |}.

  Definition unsent_time (s:validator_state) :=
    let (t,_,_,f) := s in
    (if f then 1 else 0) + t.

  Definition sends_respect_plan (s: validator_state) : Prop :=
    forall m, validator_has_been_sent s m ->
              plan (message_time m) v
              /\ message_sender m = v
              /\ message_time m < unsent_time s.

  Definition sends_fill_plan (s: validator_state) : Prop :=
    forall t, plan t v -> t < unsent_time s ->
    exists m, message_slot m = (t,v) /\ validator_has_been_sent s m.

  Definition sends_unique (s: validator_state) : Prop :=
    forall m1, validator_has_been_sent s m1 ->
    forall m2, validator_has_been_sent s m2 ->
               message_slot m1 = message_slot m2 -> m1 = m2.

  Lemma message_send_invariant_init s:
    initial_validator_state s ->
    sends_respect_plan s /\ sends_fill_plan s /\ sends_unique s.
  Proof.
    destruct s; simpl.
    intros (-> & -> & -> & Hfinished).
    destruct finished_send;[elim Hfinished;exact I|clear Hfinished].
    unfold sends_respect_plan, sends_fill_plan, sends_unique;simpl.
    pose proof PeanoNat.Nat.nlt_0_r.
    firstorder.
  Qed.

  Lemma message_send_invariant_maintained
        l s im s' om:
    validator_valid l (s,im) ->
    validator_transition l (s,im) = (s',om) ->
    sends_respect_plan s /\ sends_fill_plan s /\ sends_unique s ->
    sends_respect_plan s' /\ sends_fill_plan s' /\ sends_unique s'.
  Proof.
    intros Hvalid Htrans IH.
    destruct l as [[c|]|].
    + (* sending a proposal message, unsent_time advances and
           the set of sent messages grows *)
      destruct s.
      simpl in Htrans.
      inversion_clear Htrans.
      simpl in Hvalid.
      destruct im;[exfalso;exact Hvalid|].
      destruct Hvalid as [_ [_ [Hplan Hflag]]].
      destruct finished_send;[elim Hflag;exact I|clear Hflag].
      destruct IH as [Hrespect [Hfill Hunique]].
      split;[|split].
      * unfold sends_respect_plan;simpl.
        intros m [<-|Hsent];[solve[auto with arith]|].
        apply Hrespect in Hsent.
        simpl in Hsent.
        pose proof (PeanoNat.Nat.lt_lt_succ_r (message_time m) time).
        tauto.
      * unfold sends_fill_plan;simpl.
        intros t Hplan_t Hlt.
        apply le_S_n, Lt.le_lt_or_eq in Hlt.
        destruct Hlt as [H| ->].
        -- specialize (Hfill t Hplan_t H).
           simpl in Hfill. firstorder.
        -- eexists;split;[|left;reflexivity].
           simpl. congruence.
      * revert Hunique;unfold sends_unique;simpl;intros Hunique.
        assert (forall m, message_slot m = (time,v) -> ~In m sent).
        {
          clear -Hrespect.
          intros m Hslot Hsent.
          assert (message_time m < time) by (apply Hrespect;assumption).
          apply PeanoNat.Nat.lt_neq in H.
          revert Hslot H.
          clear.
          destruct m;simpl;congruence.
        }
        intros m1 [<-|Hm1] m2 [<-|Hm2].
        -- congruence.
        -- simpl. intro Hslot. symmetry in Hslot.
           destruct (H m2 Hslot);assumption.
        -- simpl. intro Hslot.
           destruct (H m1 Hslot);assumption.
        -- auto.
    + assert (validator_sends s = validator_sends s'
              /\ forall t, plan t v -> t < unsent_time s <-> t < unsent_time s').
      {
        destruct s.
        simpl in Htrans.
        inversion_clear Htrans.
        split;[reflexivity|].
        destruct finished_send;[reflexivity|].
        simpl.
        clear IH.
        split;[auto with arith|].
        intro Hle.
        apply le_S_n, Lt.le_lt_or_eq in Hle.
        destruct Hle;[assumption|exfalso;subst t].
        simpl in Hvalid.
        destruct im;[solve[destruct Hvalid]|].
        tauto.
      }
      clear Htrans.
      revert IH.
      unfold sends_respect_plan, sends_fill_plan, sends_unique.
      set (st := unsent_time s) in H |- *.
      set (s't := unsent_time s') in H |- *.
      clearbody st s't.
      destruct s, s';simpl in * |- *.
      destruct H as [<- H].
      intros [Ha [Hb Hc]].
      firstorder.
    + (* receiving a message, none of the parts of
           the state mentioned in these properties change *)
      destruct s.
      simpl in Htrans.
      destruct im;inversion_clear Htrans;assumption.
  Qed.

  Lemma message_send_invariant (s : validator_state) :
    protocol_state_prop Validator s ->
    sends_respect_plan s /\ sends_fill_plan s /\ sends_unique s.
  Proof.
    intro Hproto.
    induction Hproto using @protocol_state_prop_ind.
    - apply message_send_invariant_init;assumption.
    - revert IHHproto;apply (message_send_invariant_maintained l s om s' om');apply Ht.
  Qed.
  Lemma message_send_invariant_preloaded (s : validator_state) :
    protocol_state_prop (pre_loaded_with_all_messages_vlsm Validator) s ->
    sends_respect_plan s /\ sends_fill_plan s /\ sends_unique s.
  Proof.
    intro Hproto.
    induction Hproto using @protocol_state_prop_ind.
    - apply message_send_invariant_init;assumption.
    - revert IHHproto;apply (message_send_invariant_maintained l s om s' om');apply Ht.
  Qed.

End Define_Component.
Arguments validator_message _ _ : clear implicits.
Arguments validator_state _ _ : clear implicits.
Arguments Validator {C V} {EqC EqV} _ _ _ _.


(** ** Composition and Proofs

This section defines the composed protocol,
and gives proofs about it.
*)

Section Protocol_Proofs.
  Context
    (C V:Type)
    {EqC: EqDecision C}
    {EqV: EqDecision V}
    (c0:C)
    {Hweights: Measurable.Measurable V}
    (plan : nat -> V -> Prop)
    {plan_dec : RelDecision plan}
    {HPlan : Plan V plan}
    (ClientState := State.justification C V)
    (estimator: list (validator_message C V) -> C -> Prop)
    (validator_list: list V)
    (validators_finite: FinFun.Listing validator_list)
    {v0: Inhabited V}
  .

  Definition IM : V -> VLSM (validator_message C V) :=
    fun v => Validator c0 plan estimator v.

  Definition simple_liveness_VLSM :=
    (Composition.composite_vlsm IM).

  (** Constructing a variant to show that
      a component's clock eventually ticks.
   *)

  Definition message_slots_before (t:nat) : list (nat * V) :=
    filter (fun '(n,v) => bool_decide (plan n v)) (set_prod (seq 0 t) validator_list).

  Lemma In_message_slots_before tm v t :
    In (tm,v) (message_slots_before t) <-> (plan tm v /\ tm < t).
  Proof.
    split.
    - intro Hin.
      apply filter_In in Hin.
      destruct Hin as [Hin Hplan].
      split.
      + apply bool_decide_eq_true in Hplan.
        assumption.
      + rewrite in_prod_iff in Hin.
        destruct Hin as [Hin_t _].
        apply in_seq in Hin_t.
        destruct Hin_t.
        assumption.
    - intros [Hplan Htime].
      apply filter_In.
      split.
      + apply in_prod_iff.
        split.
        * apply in_seq. lia.
        * apply validators_finite.
      + apply bool_decide_eq_true.
        assumption.
  Qed.

  Definition unreceived_message_count_before (t:nat) (s: validator_state C V) : nat :=
    length (set_diff_filter (message_slots_before t)
                            (map message_slot (validator_received s))).

  Definition validator_ticks_before (t:nat) (s: validator_state C V) : nat :=
     t - validator_time s.

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
       := no_synch_faults_no_equivocation_constraint validators_finite IM
                 (validator_clock c0 plan estimator)
             message_time)
    (X: VLSM (validator_message C V) := composite_vlsm IM constraint)
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

  Definition received_were_sent s : Prop :=
    forall i msg, validator_has_been_observed (s i) msg ->
    let j := message_sender msg in has_been_sent (IM j) (s j) msg.

  Lemma received_were_sent_invariant s:
    protocol_state_prop X s ->
    received_were_sent s.
  Proof.
    intro H.
    pose (composite_has_been_sent_capability _ _ validators_finite _
         : has_been_sent_capability X) as Hhbs.
    pose (composite_has_been_observed_capability _ _ validators_finite _
         : has_been_observed_capability X) as Hhbo.
    assert (observed_were_sent_or_initial _ X _ _ s).
    {
      apply observed_were_sent_invariant;[|assumption].
      clear.
      intros l s om [_ [H _]].
      exact H.
    }
    intros i msg Hi.
    specialize (H0 msg (ex_intro _ i Hi)).
    destruct H0 as [H0 | [k [[mk Hmk] H0]]]; [|inversion Hmk].
    destruct H0 as [j Hj].
    (* The [observed_were_sent_invariant] only says that
       some component sent the message.
       To finish, use the property from [message_send_invariant]
       that the [message_sender] meaches the component ID.
     *)
    enough (message_sender msg = j) as <- by assumption.
    apply protocol_state_project_preloaded with (i:=j) in H.
    apply message_send_invariant_preloaded in H.
    destruct H as [Hresp _].
    specialize (Hresp msg Hj).
    apply Hresp.
  Qed.

  Definition clock_limit_invariant (s: vstate X): Prop
    := forall v t,
      plan t v ->
      validator_time (s v) < t ->
      forall i, validator_time (s i) <= t.

  Lemma clock_limit_invariant_init (s: vstate X):
    vinitial_state_prop X s ->
    clock_limit_invariant s.
  Proof.
    intros Hinit _ t _ _ i.
    specialize (Hinit i).
    cbn in Hinit.
    destruct (s i).
    simpl.
    destruct Hinit as [-> _].
    auto with arith.
  Qed.

  Lemma clock_limit_invariant_step l s im s' om:
    protocol_transition X l (s,im) (s',om) ->
    clock_limit_invariant s ->
    clock_limit_invariant s'.
  Proof.
    intros Hptrans IH v t Hplan Hlt i.
    specialize (IH v t Hplan).
    assert (validator_time (s v) < t) as Hlt2.
    {
      apply PeanoNat.Nat.le_lt_trans with (validator_time (s' v));[|assumption].
      apply (protocol_transition_project_any v) in Hptrans.
      destruct Hptrans as [?|[lj [-> ?]]].
      - rewrite H. reflexivity.
      - destruct H as [_ Htrans].
        revert Htrans.
        apply validator_clock_monotone.
    }
    assert (forall i msg, message_slot msg = (t,v) ->
                          ~has_been_observed (IM i) (s i) msg)
           as Hunknown.
    {
      destruct Hptrans as [[Hproto _] _].
      clear i.
      intros i msg Hslot Hobserved.
      pose proof (received_were_sent_invariant s Hproto i msg Hobserved) as Hsent.
      replace (message_sender msg) with v in Hsent
        by (destruct msg;simpl in Hslot |- *;congruence).
      simpl in Hsent.
      apply protocol_state_project_preloaded with (i:=v) in Hproto.
      pose proof (message_send_invariant_preloaded _ _ _ _ _ Hproto) as Hsend_inv.
      destruct Hsend_inv as [Hsend_inv _].
      specialize (Hsend_inv msg Hsent).
      destruct Hsend_inv as [_ [_ Hsend_early]].
      clear -Hlt2 Hsend_early Hslot.
      replace (message_time msg) with t in Hsend_early
        by (destruct msg; simpl in Hslot |- *; congruence).
      clear Hslot.
      destruct (s v);simpl in Hlt2, Hsend_early.
      destruct finished_send;lia.
    }
    specialize (IH Hlt2 i).
    apply (protocol_transition_project_any i) in Hptrans.
    destruct Hptrans as [|[li [-> Hptrans]]].
    - rewrite <- H;assumption.
    - simpl in Hptrans.
      destruct Hptrans as [[_ [_ Hvalid]] Htrans].

      specialize (Hunknown i).
      set (si := s i) in *;clearbody si.
      set (si' := s' i) in *;clearbody si'.
      clear Hlt Hlt2.
      clear s s'.

      destruct li as [[c|]|].
      + (* protosal *)
        replace (validator_time si') with (validator_time si);[assumption|].
        destruct si.
        cbn in Htrans;inversion_clear Htrans;reflexivity.
      + (* tick *)
        destruct si.
        cbn in Htrans; inversion_clear Htrans.
        simpl in Hunknown, IH |- *.
        fold (time < t).
        apply PeanoNat.Nat.le_lteq in IH.
        destruct IH as [| ->];[assumption|exfalso].

        cbn in Hvalid.
        destruct im;[exfalso;assumption|].
        destruct Hvalid as [_ Hhave_plan].
        specialize (Hhave_plan v Hplan).
        apply in_map_iff in Hhave_plan.
        destruct Hhave_plan as [m [Hslot HIn]].
        exact (Hunknown m Hslot HIn).
      + (* receive *)
        replace (validator_time si') with (validator_time si);[assumption|].
        destruct si.
        destruct im;cbn in Htrans;inversion_clear Htrans;reflexivity.
  Qed.

  Lemma early_validator_limits_clock_advance
        v t (H_plan : plan t v)
        (s:vstate X):
    protocol_state_prop X s ->
    validator_time (s v) < t ->
    forall i, validator_time (s i) <= t.
  Proof.
    intros Hproto H_time.
    revert v t H_plan H_time.
    change (clock_limit_invariant s).
    apply protocol_state_has_trace in Hproto.
    destruct Hproto as [is [tr [Htr Hinit]]].
    apply clock_limit_invariant_init in Hinit.
    induction Htr.
    - assumption.
    - apply IHHtr.
      revert H Hinit.
      apply clock_limit_invariant_step.
  Qed.

  Lemma sending_decreases_validator_variant t i c (si si':vstate (IM i)) im om
        (H_protocol: protocol_state_prop (pre_loaded_with_all_messages_vlsm (IM i)) si)
        (H_valid: validator_valid plan estimator i (Some (Proposal c)) (si, im))
        (H_time: validator_time si < t)
        (H_know_own_sends: forall m,
            message_sender m = i ->
            validator_has_been_observed si m ->
            validator_has_been_sent c0 plan estimator i si m)
    (H_transition: validator_transition i (Some (Proposal c)) (si, im) = (si', om))
    :
    validator_variant t si' < validator_variant t si.
  Proof.
    destruct si eqn:Heq_si.
    destruct im;[solve[exfalso;exact H_valid]|].
    assert (finished_send = false)
      by (apply Bool.not_true_is_false;intro;subst finished_send;apply H_valid;exact I).
    subst finished_send.
    assert (plan time i) as H_plan by apply H_valid;clear H_valid.
    simpl in H_transition.
    inversion_clear H_transition.
    unfold validator_variant.
    unfold validator_ticks_before.
    apply Plus.plus_lt_compat_r.

    unfold unreceived_message_count_before.
    assert (~In (time,i) (map message_slot received)) as H_msg_new.
    {
      (* by known_own_sends, we already sent it *)
      assert (unsent_time si = time) as H_unsent_time by (rewrite Heq_si;reflexivity).
      apply message_send_invariant_preloaded in H_protocol.
      destruct H_protocol as [H_inv _].
      unfold sends_respect_plan in H_inv.
      intro H_in.
      apply in_map_iff in H_in.
      destruct H_in as [old_msg [H_old_slot H_in]].
      destruct old_msg.
      injection H_old_slot;clear H_old_slot;intros -> ->.
      apply H_know_own_sends in H_in;[|reflexivity].
      simpl in H_in.
      apply H_inv in H_in.
      simpl in H_in.
      apply (PeanoNat.Nat.lt_irrefl time).
      apply H_in.
    }

    simpl validator_received.
    apply len_set_diff_map_set_add.
    - assumption.
    - apply In_message_slots_before.
      split;assumption.
  Qed.

  (** If all validator clock are below the time used in the
      variant, the the variant decreases.
   *)
  Lemma eventually_ticks_variant_progress t
        l (s:vstate X) im s' om
        (H_times : forall i, validator_time (s i) < t)
    :
    protocol_transition X l (s,im) (s',om) ->
    eventually_ticks_variant t s' < eventually_ticks_variant t s.
  Proof.
    intros [Hvalid Htrans].
    assert (received_were_sent s) as H_received_were_sent
        by apply received_were_sent_invariant, Hvalid.
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
      apply sending_decreases_validator_variant with c im om.
      + apply protocol_state_project_preloaded.
        apply Hvalid.
      + apply Hvalid.
      + apply H_times.
      + clear -H_received_were_sent.
        intros m Hsender Hobs.
        rewrite <- Hsender.
        apply (H_received_were_sent _ _ Hobs).
      + apply H_transition.
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
      simpl.
      lia.
    - (* Receiving a message fills one of the
         receivers slots *)
      apply state_update_variant_progress.
      unfold vtransition in H_transition.
      destruct (s i) eqn:Heq_si.
      simpl in Hvalid.
      simpl in H_transition.
      (* message cannot be None *)
      destruct im;[|solve[exfalso;apply Hvalid]].
      inversion_clear H_transition.
      unfold validator_variant.
      apply Plus.plus_lt_compat_r.

      rename Hvalid into Hcomposite_valid.
      destruct (id Hcomposite_valid)
        as [Hproto [_ [Hvalidator_valid [[[ix Hsent]| [k [[mk Hmk] _]]] _]]]]
        ; [| inversion Hmk].
      simpl in Hvalidator_valid.
      (* The validity condition ensures that the exact
         message has not been received before, but to
         show there is also no previously-received message
         for that slot we need to use the invariants *)
      apply protocol_state_project_preloaded with (i:=ix) in Hproto.
      pose Hproto as Hinvariants;apply message_send_invariant_preloaded in Hinvariants.

      assert (message_sender v = ix) as Hsender.
      {
        destruct Hinvariants as [Hsend _].
        apply Hsend in Hsent.
        apply Hsent.
      }
      assert (~In (message_slot v) (map message_slot received)).
      {
        intro H_in.
        apply in_map_iff in H_in.
        destruct H_in as [v2 [Hslots Hin2]].
        assert (v <> v2) as Hneq.
        { (* because by the validity condition, new message [v]
             cannot have already been received, but [Hin2: In v2 received]. *)
          cbn in Hvalidator_valid.
          rewrite Heq_si in Hvalidator_valid.
          destruct v.
          destruct Hvalidator_valid as [H_not_in _].
          congruence.
        }
        assert (has_been_sent (IM (message_sender v2)) (s (message_sender v2)) v2).
        {
          apply H_received_were_sent with (i:=i).
          rewrite Heq_si.
          simpl.
          assumption.
        }
        replace (message_sender v2) with ix in H
          by (destruct v,v2;simpl in Hsender, Hslots |- *;congruence).
        destruct Hinvariants as [_ [_ Hunique]].
        unfold sends_unique in Hunique.
        specialize (Hunique v Hsent v2 H).
        symmetry in Hslots.
        apply Hneq, Hunique, Hslots.
      }
      apply len_set_diff_map_set_add.
      assumption.
      apply (proj1 Hinvariants) in Hsent.
      destruct v.
      simpl in Hsent.
      destruct Hsent as [Hplan [-> Htime_ix]].
      apply In_message_slots_before.
      split.
      assumption.
      apply PeanoNat.Nat.lt_le_trans with (unsent_time (s ix)).
      apply Htime_ix.
      clear -H_times.
      specialize (H_times ix).
      revert H_times.
      destruct (s ix);simpl.
      destruct finished_send;lia.
  Qed.

  Theorem eventually_ticks
          s (Hproto: protocol_state_prop X s)
          tr (Htr: infinite_protocol_trace_from X s tr):
    forall v, exists n, validator_time (s v) < validator_time (destination (Streams.Str_nth n tr) v).
  Proof.
    intro v.
    (* First, find a time greater than v's current clock for which it is in the plan *)
    destruct (recurring_sends _ _ HPlan (validator_time (s v)) v) as [t [Hlt Hplan]].
    (* Then strengthen the goal to finding a step where <<v>>'s clock is at least
       <<t>> *)
    cut (exists n, t <= validator_time (destination (Streams.Str_nth n tr) v));
      [intros [n Hn];exists n;lia|].
    (* Use [early_validator_limits_clock_advance] to reduce that to
       to finding a time where any validators clock is greater than <<t>> *)
    assert (forall n, protocol_state_prop X (destination (Streams.Str_nth n tr))) as Hall_proto.
    {
      intro n.
      clear Hproto Hlt.
      revert s tr Htr.
      clear -n.
      induction n;intros s tr Htr.
      - destruct Htr.
        simpl.
        revert H.
        apply protocol_transition_destination.
      - destruct Htr.
        apply (IHn s tl Htr).
    }
    pose proof (early_validator_limits_clock_advance _ _ Hplan) as clocks_inv.
    cut (exists n, ~(forall i, validator_time (destination (Streams.Str_nth n tr) i) < S t)).
    {
      intros [n Htimes];exists n.
      apply PeanoNat.Nat.nlt_ge.
      contradict Htimes.
      intro i.
      apply le_n_S.
      apply (clocks_inv _ (Hall_proto n)).
      assumption.
    }
    (*
       This happens within <<validator_variant (S t) s>> steps, by well-foudned
       induction on the remaining value of the variant.
       First sharpen the claim to existing in a given prefix of the stream.
     *)
    remember (eventually_ticks_variant (S t) s) as len.
    set (P := fun (s:vstate X) => forall i, validator_time (s i) < S t).
    cut (Exists (fun item => ~P (destination item))
                (StreamExtras.stream_prefix tr len)).
    {
      intro H.
      apply Exists_exists in H.
      destruct H as [x [Hin HP]].
      apply StreamExtras.stream_prefix_in in Hin.
      destruct Hin as [k [_ Hnth]].
      exists k.
      rewrite Hnth.
      assumption.
    }
    (*
      Now we set up for the induction.
     *)
    assert (P s) as Hstart.
    {
      intro i.
      apply le_n_S.
      apply clocks_inv;assumption.
    }
    assert (forall s, Decision (P s)) as P_dec.
    {
      intros s0.
      unfold P.
      eapply Decision_iff.
      symmetry.
      eapply ListExtras.forall_finite;apply validators_finite.
      apply Forall_dec.
      intro x.
      apply Compare_dec.lt_dec.
    }
    clear Hall_proto clocks_inv Hproto Hlt.
    revert s Heqlen tr Htr Hstart.
    clear -P_dec.
    apply (Wf_nat.lt_wf_ind len);clear len.
    intros len IH s Hlen tr Htr HP.
    destruct Htr.
    pose proof (eventually_ticks_variant_progress _ _ _ _ _ _ HP H).
    rewrite <- Hlen in H0.
    specialize (IH _ H0 s (eq_refl _) tl Htr).
    destruct (decide (P s));last first.
    - destruct len;[exfalso;lia|].
      apply Exists_cons_hd.
      assumption.
    - remember (eventually_ticks_variant (S t) s) as len' in IH, H0.
      specialize (IH p).
      clear -H IH H0.
      unfold lt in H0.
      destruct len;[exfalso;lia|].
      apply le_S_n in H0.
      simpl.
      apply Exists_cons_tl.
      pose proof @StreamExtras.stream_prefix_segment as Hprefix.
      specialize (Hprefix _ tl len' len H0).
      progress simpl in Hprefix.
      rewrite <- Hprefix.
      apply Exists_app.
      left.
      assumption.
  Qed.
End Protocol_Proofs.
