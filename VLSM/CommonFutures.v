From CasperCBC
  Require Import
    Lib.Preamble
    VLSM.Common VLSM.Composition VLSM.Decisions VLSM.ProjectionTraces
    CBC.Common
    .

(** * Common Futures and Decision Consistency *)

(**
In this section we provide a definition for the [HasCommonFuturesEstimates]
property and then we show that a VLSM equiped with this property
has [final_and_consistent] decisions.
*)

Section CommonFutures.

Context
  {message : Type}
  {index : Type}
  {IndEqDec : EqDec index}
  (i0 : index)
  {IT : index -> VLSM_type message}
  {IS : forall i : index, VLSM_sign (IT i)}
  (IM : forall n : index, VLSM (IS n))
  (T := composite_type IT)
  (S := composite_sig i0 IS)
  (constraint : @label _ T -> @state _ T * option message -> Prop)
  (X := composite_vlsm i0 IM constraint)
  {CV : consensus_values}
  (IE : forall i : index, Estimator (@state _ (IT i)) C)
  (ID : forall i : index, decision (IT i))
  (DE : forall i : index, decision_estimator_property i0 IM constraint ID IE i)
  .

(**
Let us fix an indexed set of VLSMs <<IM>> and their composition <<X>> using <<constraint>>.
For each component of index i, let <<IE i>> be an [Estimator] for Xi and let
<<ID i>> be a [decision] function for Xi, linked together by the
[decision_estimator_property].

*)

(** ** Common futures estimates definition *)

(**
We say that the composition <<X>> [HasCommonFutureEstimates] if there
exists a function [union] taking composite states to composit states
such that for each composite state <<s>>, its [union_is_reachable] from <<s>>,
and the [union_has_consistent_estimators]; i.e.,
all components yields the same estimates.
*)

Class HasCommonFutureEstimates :=
  { union : @state _ T -> @state _ T
  ; union_is_reachable
    : forall
      (s : @state _ T)
      (Hps : protocol_state_prop X s)
      , in_futures X s (union s)
  ; union_has_consistent_estimators
    : forall
      (s : @state _ T)
      (Hps : protocol_state_prop X s)
      (i j : index)
      (c : C),
      estimator (union s i) c <-> estimator (union s j) c
  }.

(** ** Final and consistent decisions

If a [VLSM] composition <<X>> [HasCommonFuturesEstimates] and its component
decisions are linked with the corresponding estimators through the
[decision_estimator_property], then <<X>> has [final_and_consistent]
decisions.
*)


Lemma consistent_estimator_decisions
  (HCFE : HasCommonFutureEstimates)
  : final_and_consistent i0 IM constraint ID.
Proof.
  unfold final_and_consistent; intros.
  specialize (in_futures_protocol_snd X s1 s2 Hfuture); intros Hps2.
  specialize (union_is_reachable s2 Hps2); intro HcmnFuture.
  specialize (union_has_consistent_estimators s2 Hps2 j k)
  ; intros HconsEst.
  specialize (in_futures_trans X s1 s2 (union s2) Hfuture HcmnFuture)
  ; intro HcmnFuture1.
  specialize (in_futures_projection i0 IM constraint j s1 (union s2) HcmnFuture1)
  ; intros HFuture1.
  assert (Dej := DE j).
  specialize (Dej (s1 j) c1 HDecided1 (union s2 j) HFuture1).
  specialize (in_futures_projection i0 IM constraint k s2 (union s2) HcmnFuture)
  ; intros HFuture2.
  assert (Dek := DE k).
  specialize (Dek (s2 k) c2 HDecided2 (union s2 k) HFuture2).
  specialize (estimator_total (union s2 j)); intros [c Hc].
  specialize (HconsEst c).
  specialize (Dej c Hc).
  apply HconsEst in Hc.
  specialize (Dek c Hc).
  subst.
  reflexivity.
Qed.

End CommonFutures.