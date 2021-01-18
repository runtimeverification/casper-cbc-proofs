Require Import Bool List ListSet Reals FinFun RelationClasses Relations Relations_1 Sorting.
Require Import Lia.
Import ListNotations.
From CasperCBC
Require Import
  Lib.Preamble
  Lib.ListExtras
  Lib.SortedLists
  VLSM.Common
  VLSM.Composition
  VLSM.Equivocation
  VLSM.ListValidator.ListValidator
  VLSM.ListValidator.Equivocation
  VLSM.ObservableEquivocation
  CBC.Common
  CBC.Equivocation.

Section Composition.

Context
  {index : Type}
  {i0 : Inhabited index}
  {index_listing : list index}
  {Hfinite : Listing index_listing}
  {idec : EqDecision index}
  (IM_index := fun (i : index) => @VLSM_list index i index_listing idec ListValidator.estimator)
  {constraint : composite_label IM_index -> (composite_state IM_index) * option (@message index index_listing) -> Prop}
  (has_been_sent_capabilities := fun i : index => @has_been_sent_lv index i index_listing Hfinite idec ListValidator.estimator)
  (Free := @free_composite_vlsm _ _ idec IM_index _ )
  (composite_has_been_sent_capability : has_been_sent_capability Free := composite_has_been_sent_capability IM_index (free_constraint IM_index) Hfinite has_been_sent_capabilities)
  (X := composite_vlsm IM_index (no_equivocations Free))
  (preX := pre_loaded_with_all_messages_vlsm X)
  {Mindex : Measurable index}
  {Rindex : ReachableThreshold index}.

End Composition.
