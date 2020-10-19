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
  {i0 : index}
  {index_listing : list index}
  {Hfinite : Listing index_listing}
  {idec : EqDecision index}
  (IM_index := fun (i : index) => @VLSM_list index i index_listing idec ListValidator.estimator)
  {constraint : composite_label IM_index -> (composite_state IM_index) * option (@message index index_listing) -> Prop}
  (has_been_sent_capabilities := fun i : index => @has_been_sent_lv index i index_listing Hfinite idec ListValidator.estimator)
  (X := composite_vlsm IM_index i0 (no_equivocations IM_index i0 constraint has_been_sent_capabilities))
  (preX := pre_loaded_with_all_messages_vlsm X)
  {Mindex : Measurable index}
  {Rindex : ReachableThreshold index}.

End Composition.
