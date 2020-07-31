Require Import Coq.Logic.FinFun.
Require Import Bool List Streams Logic.Epsilon.
Require Import Coq.Arith.Compare_dec.
Require Import Lia.
Import List Notations.
From CasperCBC
  Require Import
    Lib.Preamble Lib.ListExtras Lib.ListSetExtras Lib.RealsExtras
    CBC.Protocol CBC.Common CBC.Definitions
    VLSM.Common VLSM.Composition VLSM.ProjectionTraces.

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
  fun (D : decision T) => forall (s1 s2 : @state _ T) (c1 c2 : C),
        in_futures V s1 s2 ->
        (D s1 = (Some c1)) ->
        (D s2 = (Some c2)) ->
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
    {index : Type}
    {Heqd : EqDec index}
    {message : Type}
    {IT : index -> VLSM_type message}
    {IS : forall i : index, VLSM_sign (IT i)}
    (Hi : index)
    (IM : forall i : index, VLSM (IS i))
    (constraint : composite_label IT -> composite_state IT * option message -> Prop)
    (X := composite_vlsm Hi IM constraint)
    (ID : forall i : index, decision (IT i)).

  (* ** Decision consistency

  First, let us introduce a definition of consistency which
  looks at states as belonging to a trace.
  *)

  Definition consistent_original :=
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

  (**

  Now let us give an alternative definition based on [in_futures]:
  *)

  Definition consistent :=
      forall
        (s1 s2 : @state _ (composite_type IT))
        (Hfuture : in_futures X s1 s2)
        (j k : index)
        (Hneq : j <> k)
        (c1 c2 : C)
        (HDecided1 : (ID j) (s1 j) = Some c1)
        (HDecided2 : (ID k) (s2 k) = Some c2)
        , c1 = c2.


  (**
  Next two results show that the two definitions above are equivalent.
  *)

  Lemma consistent_to_original
    (Hconsistent : consistent)
    : consistent_original.
  Proof.
    intros tr n1 n2 j k s1 s2 c1 c2 Hneq Hs1 Hs2 HD1 HD2.
    destruct (le_lt_dec n1 n2).
    - specialize (in_futures_witness_reverse X s1 s2 tr n1 n2 l Hs1 Hs2)
      ; intros Hfutures.
      specialize (Hconsistent s1 s2 Hfutures j k Hneq c1 c2 HD1 HD2).
      assumption.
    - assert (Hle : n2 <= n1) by lia.
      clear l.
      specialize (in_futures_witness_reverse X s2 s1 tr n2 n1 Hle Hs2 Hs1)
      ; intros Hfutures.
      assert (Hneq' : k <> j)
        by (intro Heq; elim Hneq; symmetry; assumption).
      specialize (Hconsistent s2 s1 Hfutures k j Hneq' c2 c1 HD2 HD1).
      symmetry.
      assumption.
    Qed.

  Lemma original_to_consistent
    (Horiginal : consistent_original)
    : consistent.
  Proof.
    unfold consistent; intros.
    specialize (in_futures_witness X s1 s2 Hfuture)
    ; intros [tr [n1 [n2 [Hle [Hs1 Hs2]]]]].
    specialize (Horiginal tr n1 n2 j k s1 s2 c1 c2 Hneq Hs1 Hs2 HDecided1 HDecided2).
    assumption.
  Qed.

  (** The following is an attempt to include finality in the definition of consistency by dropping the requirement
      that (j <> k). **)

  Definition final_and_consistent :=
      forall
        (s1 s2 : @state _ (composite_type IT))
        (Hfuture : in_futures X s1 s2)
        (j k : index)
        (c1 c2 : C)
        (HDecided1 : (ID j) (s1 j) = Some c1)
        (HDecided2 : (ID k) (s2 k) = Some c2)
        , c1 = c2.

  Lemma final_and_consistent_implies_final
      (Hcons : final_and_consistent)
      (i : index)
      (Hfr : finite_projection_friendly Hi IM constraint i)
      : final (composite_vlsm_constrained_projection Hi IM constraint i) (ID i).
  Proof.
    intros s1 s2 c1 c2 Hfuturesi HD1 HD2.
    specialize (projection_friendly_in_futures Hi IM constraint i Hfr s1 s2 Hfuturesi)
    ; intros [sX1 [sX2 [Hs1 [Hs2 HfuturesX]]]].
    subst.
    apply (Hcons sX1 sX2 HfuturesX i i c1 c2 HD1 HD2).
  Qed.

  Lemma final_and_consistent_implies_consistent
      (Hcons : final_and_consistent)
      : consistent.
  Proof.
    unfold consistent; intros.
    apply (Hcons s1 s2 Hfuture j k c1 c2 HDecided1 HDecided2).
  Qed.

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
    {message : Type}
    {index : Type}
    {Heqd : EqDec index}
    (Hi : index)
    {IT : index -> VLSM_type message}
    {IS : forall i : index, VLSM_sign (IT i)}
    (IM : forall i : index, VLSM (IS i))
    (constraint : composite_label IT -> composite_state IT * option message -> Prop)
    (X := composite_vlsm Hi IM constraint)
    (ID : forall i : index, decision (IT i))
    (IE : forall i : index, Estimator (@state _ (IT i)) C).

  Definition decision_estimator_property
    (i : index)
    (Xi := composite_vlsm_constrained_projection Hi IM constraint i)
    (Ei := @estimator _ _ (IE i))
    := forall
      (sigma : @state _ (IT i))
      (c : C)
      (HD : ID i sigma = Some c)
      (sigma' : @state _ (IT i))
      (Hreach : in_futures Xi sigma sigma')
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
    destruct s as [s Hs].
    unfold decision_estimator_property in H.
    apply H with (sigma := s) (sigma':= s); try assumption.
    apply in_futures_refl.
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
    destruct s as [s Hs].
    assert (x = c). {
      apply H with (sigma := s) (sigma' := s); try assumption.
      apply in_futures_refl.
      assumption.
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
    specialize (in_futures_protocol_snd Xi s1 s2 H0); intro Hps2.
    apply estimator_only_has_decision with (i := i) (s := (exist _ s2 Hps2)).
    assumption.
    assumption.
    unfold decision_estimator_property in H.
    assert(c2 = c1). {
      apply H with (sigma := s1) (sigma' := s2).
      assumption.
      assumption.
      apply (estimator_surely_has_decision i H (exist _ s2 Hps2)).
      assumption.
    }
    rewrite <- H3.
    apply estimator_surely_has_decision.
    assumption.
    assumption.
   Qed.
End Estimators.
