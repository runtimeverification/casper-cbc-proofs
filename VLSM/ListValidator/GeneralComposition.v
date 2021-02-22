Require Import Bool List ListSet Reals FinFun RelationClasses Relations Relations_1 Sorting.
Require Import Lia.
Import ListNotations.
From CasperCBC
Require Import
  Lib.Preamble
  Lib.ListExtras
  Lib.ListSetExtras
  Lib.SortedLists
  VLSM.Common
  VLSM.Composition
  VLSM.ProjectionTraces
  VLSM.Equivocation
  VLSM.ListValidator.ListValidator
  VLSM.ListValidator.Equivocation
  VLSM.ListValidator.Observations
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
  (message := @ListValidator.message index index_listing)
  (state := @ListValidator.state index index_listing)
  (est : index -> state -> bool -> Prop)
  (IM_index := fun (i : index) => @VLSM_list index i index_listing idec (est i))
  {constraint : composite_label IM_index -> (composite_state IM_index) * option message -> Prop}
  (X := composite_vlsm IM_index constraint)
  (preX := pre_loaded_with_all_messages_vlsm X)
  (Hevidence := fun (i : index) => @simp_observable_full index i index_listing idec)
  {Mindex : Measurable index}
  {Rindex : ReachableThreshold index}
  .
  
  Lemma protocol_state_component_no_bottom 
    (s : vstate X)
    (i : index)
    (Hprs : protocol_state_prop X s) :
    (s i) <> Bottom.
  Proof.
    apply (@protocol_prop_no_bottom index i _ _ (est i)).
    apply (protocol_state_projection IM_index constraint i) in Hprs.
    unfold protocol_state_prop in Hprs.
    destruct Hprs as [om Hprs] in Hprs.
    apply (proj_pre_loaded_with_all_messages_protocol_prop IM_index constraint i) in Hprs.
    unfold protocol_state_prop.
    exists om.
    assumption.
  Qed.

End Composition.
