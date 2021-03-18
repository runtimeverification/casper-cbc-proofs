From Coq Require Import Reals List.
From CasperCBC
    Require Import
      VLSM.CBC.SumWeights
    .

(* Defining the estimator function as a relation *)
Class Estimator state C :=
  { estimator : state -> C -> Prop
  ; estimator_total : forall s : state, exists c : C, estimator s c
  }.

Class ReachableThreshold V `{Hm : Measurable V} :=
  { threshold : {r | (r >= 0)%R}
  ; reachable_threshold : exists (vs:list V), NoDup vs /\ (sum_weights vs > (proj1_sig threshold))%R
  }.
