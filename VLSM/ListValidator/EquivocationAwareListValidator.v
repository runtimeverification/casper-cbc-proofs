Require Import
  List ListSet FinFun
  .
Import ListNotations.
From CasperCBC
Require Import
  Lib.Preamble
  CBC.Common
  CBC.Equivocation
  VLSM.Common
  VLSM.ListValidator.ListValidator
  VLSM.ListValidator.Equivocation
  .
(*
Section EquivocationAwareValidator.

  Context
    {index : Type}
    {index_self : index}
    {index_listing : list index}
    {Hfinite : Listing index_listing}
    {idec : EqDecision index}
    (X := @VLSM_list _ index_self index_listing idec)
    {Mindex : Measurable index}
    {Rindex : ReachableThreshold index}
    (eqv := @lv_basic_equivocation index index_listing Hfinite idec Mindex Rindex)
    .

  Existing Instance eqv.

  Definition get_no_equivocating_states
    (s : @state index index_listing)
    (eqv_validators : list index)
    : list state
    :=
    map (fun i: index => project s i)
      (set_diff decide_eq index_listing eqv_validators).

  Definition no_equivocating_decisions
    (s : @state index index_listing)
    (eqv_validators : list index)
    : list (option bool)
    :=
    match s with
    | Bottom => []
    | _ => List.map decision (get_no_equivocating_states s eqv_validators)
    end.

  Definition equivocation_aware_estimator (s : state) (b : bool) : Prop :=
    let eqv_validators := equivocating_validators s in
    let decisions := no_equivocating_decisions s eqv_validators in
    let none_count := List.count_occ decide_eq decisions None in
    let our_count := List.count_occ decide_eq decisions (Some b) in
    let other_count := List.count_occ decide_eq decisions (Some (negb b)) in
    match s with
    | Bottom => True
    | Something c some => (none_count >= our_count /\ none_count >= other_count) \/ our_count >= other_count
    end.

  Definition VLSM_equivocation_aware_list : VLSM message
    :=
    @VLSM_list index index_self index_listing idec equivocation_aware_estimator.

End EquivocationAwareValidator. *)
