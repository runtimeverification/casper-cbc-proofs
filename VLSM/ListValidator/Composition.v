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
  {idec : EqDec index}
  (IM_index := fun (i : index) => @VLSM_list index i index_listing idec)
  {constraint : composite_label IM_index -> (composite_state IM_index) * option (@message index index_listing) -> Prop}
  (X := composite_vlsm IM_index i0 constraint)
  (preX := pre_loaded_vlsm X)
  (Hevidence : forall (i : index),
    computable_observable_equivocation_evidence
        (vstate (IM_index i)) 
        index 
        (@state index index_listing) 
        state_eq_dec 
        (@comparable_states index index_listing idec state_eq_dec)).
  
  
  
  
  
End Composition.