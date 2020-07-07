Require Import Coq.Logic.FinFun.
Require Import Bool List Streams Logic.Epsilon.
Import List Notations.
From CasperCBC
Require Import Lib.Preamble Lib.ListExtras Lib.ListSetExtras Lib.RealsExtras CBC.Protocol CBC.Common CBC.Definitions VLSM.Common VLSM.Composition.

(* 3.1 Decisions on consensus values *)

(* Need to add consensus values (and decision functions) to VLSM definitions? *)
Class consensus_values :=
  { C : Type;
    about_C : exists (c1 c2 : C), c1 <> c2;
  }.

Definition decision {message} (T : VLSM_type message) {CV : consensus_values}
  := @state _ T -> option C.

Section CommuteSingleton.

  Context
    {message : Type}
    {T : VLSM_type message}
    {S : VLSM_sign T}
    {CV : consensus_values}
    (V : VLSM S).

  (* 3.2.1 Decision finality *)
  (* Program Definition prot_state0 {VLSM} : protocol_state :=
    exist protocol_state_prop (proj1_sig s0) _.
  Next Obligation.
    red.
    exists None.
    constructor.
  Defined. *)

  (* Definition of finality per document. *)
  Definition final_original : decision T -> Prop :=
    fun (D : decision T) => forall (tr : protocol_trace V),
        forall (n1 n2 : nat) (s1 s2 : state) (c1 c2 : C),
          (trace_nth (proj1_sig tr) n1 = Some s1) ->
          (trace_nth (proj1_sig tr) n2 = Some s2) ->
          (D s1 = (Some c1)) ->
          (D s2 = (Some c2)) ->
          c1 = c2.

  (* Definition of finality using in_futures, which plays better with the estimator property *)
  Definition final: decision T -> Prop :=
  fun (D : decision T) => forall (s1 s2 : protocol_state V) (c1 c2 : C),
        in_futures V s1 s2 ->
        (D (proj1_sig s1) = (Some c1)) ->
        (D (proj1_sig s2) = (Some c2)) ->
        c1 = c2.

  (* 3.3.1 Initial protocol state bivalence *)
  Definition bivalent : decision T -> Prop :=
    fun (D : decision T) =>
      (* All initial states decide on None *)
      (forall (s0 : state),
        initial_state_prop s0 ->
        D s0 = None) /\
      (* Every protocol trace (already beginning from an initial state) contains a state deciding on each consensus value *)
      (forall (c : C) ,
          exists (tr : protocol_trace V) (s : state) (n : nat),
            (trace_nth (proj1_sig tr) n) = Some s /\ D s = (Some c)).

  (* 3.3.2 No stuck states *)

  Definition stuck_free : decision T -> Prop :=
    fun (D : decision T) =>
      (forall (s : state),
          exists (tr : protocol_trace V)
                 (decided_state : state)
                 (n_s n_decided : nat)
                 (c : C),
         trace_nth (proj1_sig tr) n_s = Some s /\
         trace_nth (proj1_sig tr) n_decided = Some decided_state /\
         n_decided >= n_s /\
         D decided_state = Some c).

  (* 3.3.3 Protocol definition symmetry *)
  (* How do we formalize this property set-theoretically? *)

  Definition behavior : decision T -> Prop :=
    fun _ => True.

  Definition symmetric : decision T -> Prop :=
    fun (D : decision T) =>
    exists (f : decision T -> decision T),
      behavior D = behavior (f D).

End CommuteSingleton.

Section CommuteIndexed.

  Context
    {CV : consensus_values}
    {index : Set}
    {Heqd : EqDec index}
    {message : Type}
    {IT : index -> VLSM_type message}
    {IS : forall i : index, VLSM_sign (IT i)}
    (Hi : index)
    (IM : forall i : index, VLSM (IS i))
    (constraint : composite_label IT -> composite_state IT * option message -> Prop)
    (X := composite_vlsm Hi IM constraint)
    (ID : forall i : index, decision (IT i)).

  (* 3.2.2 Decision consistency *)

  Definition consistent :=
      forall (tr : protocol_trace X),
      forall (n1 n2 : nat),
      forall (j k : index),
      forall (s1 s2 : @state _ (composite_type IT)),
      forall (c1 c2 : C),
      j <> k ->
      trace_nth (proj1_sig tr) n1 = (Some s1) ->
      trace_nth (proj1_sig tr) n2 = (Some s2) ->
      (ID j) (s1 j) = (Some c1) ->
      (ID k) (s2 k) = (Some c2) ->
      c1 = c2.

  (** The following is an attempt to include finality in the definition of consistency by dropping the requirement
      that (j <> k). **)

  Definition final_and_consistent : Prop :=
      forall (tr : protocol_trace X),
      forall (n1 n2 : nat),
      forall (j k : index),
      forall (s1 s2 : @state _ (composite_type IT)),
      forall (c1 c2 : C),
      trace_nth (proj1_sig tr) n1 = (Some s1) ->
      trace_nth (proj1_sig tr) n2 = (Some s2) ->
      (ID j) (s1 j) = (Some c1) ->
      (ID k) (s2 k) = (Some c2) ->
      c1 = c2.

  Lemma final_and_consistent_implies_final :
      final_and_consistent ->
      forall i : index, final (composite_vlsm_constrained_projection Hi IM constraint i) (ID i).

  Proof.
    unfold final_and_consistent.
    intros.
    unfold final.
    intros.
    Admitted.

  Definition live :=
    forall (tr : @Trace _ (type X)),
      complete_trace_prop X tr ->
      exists (s : @state _ (composite_type IT)) (n : nat) (i : index) (c : C),
        trace_nth tr n = Some s /\
        (ID i) (s i) = Some c.

End CommuteIndexed.

(* Section 5 *)

Section Estimators.
  Context
    {CV : consensus_values}
    {index : Set}
    {index_listing : list index}
    (finite_index : Listing index_listing)
    {Heqd : EqDec index}
    {message : Type}
    {IT : index -> VLSM_type message}
    (IS : forall i : index, VLSM_sign (IT i))
    (IM : forall i : index, VLSM (IS i))
    (Hi : index)
    (constraint : composite_label IT -> composite_state IT * option message -> Prop)
    (X := composite_vlsm Hi IM constraint)
    (ID : forall i : index, decision (IT i))
    (IE : forall i : index, Estimator (@state _ (IT i)) C).

  Definition decision_estimator_property
    (i : index)
    (Xi := composite_vlsm_constrained_projection Hi IM constraint i)
    (Ei := @estimator _ _ (IE i))
    := forall
      (psigma : protocol_state Xi)
      (sigma := proj1_sig psigma)
      (c : C)
      (HD : ID i sigma = Some c)
      (psigma' : protocol_state Xi)
      (sigma' := proj1_sig psigma')
      (Hreach : in_futures Xi psigma psigma')
      (c' : C),
      Ei sigma' c'
      -> c' = c.

  Lemma estimator_only_has_decision
     (i : index)
     (Xi := composite_vlsm_constrained_projection Hi IM constraint i)
     (Ei := @estimator _ _ (IE i))
      : decision_estimator_property i ->
      forall (s : protocol_state Xi) (c c_other : C), (ID i (proj1_sig s)) = (Some c) ->
      (Ei (proj1_sig s) c_other) ->
      c_other = c.
  Proof.
    intros.
    unfold decision_estimator_property in H.
    apply H with (psigma := s) (psigma':= s).
    assumption.
    apply in_futures_reflexive.
    assumption.
  Qed.

  Lemma estimator_surely_has_decision
     (i : index)
     (Xi := composite_vlsm_constrained_projection Hi IM constraint i)
     (Ei := @estimator _ _ (IE i))
      : decision_estimator_property i ->
      forall (s : protocol_state Xi) (c : C), (ID i (proj1_sig s)) = (Some c) ->
      (Ei (proj1_sig s) c).
   Proof.
    intros.
    unfold decision_estimator_property in H.
    assert(exists (c_other : C), (Ei (proj1_sig s) c_other)). {
      apply estimator_total.
    }
    destruct H1.
    assert (x = c). {
      apply H with (psigma := s) (psigma' := s).
      assumption.
      apply in_futures_reflexive.
      auto.
   }
    rewrite <- H2.
    assumption.
   Qed.

  (* We use the following intermediate result,
     proven above (in two steps) via the estimator property:
     (1) If D(state) = Some c then Estimator(state) = {c}.

     We then fix s1 and s2, such that (in_futures s1 s2) and both are decided and note the following:
     (2) Estimator(s2) = {Decision(s2)}, by (1)
     (3) Estimator(s2) = {Decision(s1)}, by the estimator property.

     Thus Decision(s2) = Decision(s1).
   *)

  Theorem decision_estimator_finality
    (i : index)
    (Xi := composite_vlsm_constrained_projection Hi IM constraint i)
    : decision_estimator_property i -> final Xi (ID i).
  Proof.
    intros.
    unfold final.
    intros.
    apply estimator_only_has_decision with (i := i) (s := s2).
    assumption.
    assumption.
    unfold decision_estimator_property in H.
    assert(c2 = c1). {
      apply H with (psigma := s1) (psigma' := s2).
      assumption.
      assumption.
      apply estimator_surely_has_decision.
      assumption.
      assumption.
    }
    rewrite <- H3.
    apply estimator_surely_has_decision.
    assumption.
    assumption.
   Qed.
End Estimators.
