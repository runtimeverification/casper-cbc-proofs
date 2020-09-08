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
  VLSM.ProjectionTraces
  VLSM.Equivocation
  VLSM.ListValidator.ListValidator
  VLSM.ListValidator.Equivocation
  VLSM.ObservableEquivocation
  CBC.Common
  CBC.Equivocation.
  
Section Composition.

Print composed_computable_observable_equivocation_evidence.

Context
  {index : Type}
  {i0 : index}
  {index_listing : list index}
  {Hfinite : Listing index_listing}
  {idec : EqDec index}
  (message := @ListValidator.message index index_listing)
  (state := @ListValidator.state index index_listing)
  (est : state -> bool -> Prop)
  (IM_index := fun (i : index) => @VLSM_list index i index_listing idec est)
  {constraint : composite_label IM_index -> (composite_state IM_index) * option message -> Prop}
  (X := composite_vlsm IM_index i0 constraint)
  (preX := pre_loaded_vlsm X)
  (Hevidence := fun (i : index) => @observable_full index index_listing idec)
  {Mindex : Measurable index}
  {Rindex : ReachableThreshold index}
  .
  
  Definition composed_eqv_evidence
  : computable_observable_equivocation_evidence (vstate X) index state state_eq_dec comparable_states
  :=
  (@composed_computable_observable_equivocation_evidence
    message index state
    state_eq_dec comparable_states
    index idec index_listing IM_index Hevidence i0 constraint
  ).

  Existing Instance composed_eqv_evidence.
  
  Definition message_observable_events_lv (m : message) (target : index) : set state :=
    @full_observations index index_listing idec (snd m) target. 
  
  Lemma message_observable_consistency_lv
      (m : message)
      (i : index)
      (som : (vstate X) * option message)
      (l : label)
      (dest : vstate X)
      (Ht : protocol_transition X l som (dest, Some m))
      : incl (message_observable_events_lv m i)
      (@observable_events _ _ _ _ _ (Hevidence i) (dest (projT1 l)) i).
   Proof.
    unfold message_observable_events_lv.
    unfold observable_events.
    unfold Hevidence.
    unfold observable_full.
    destruct Ht as [Hv Ht].
    simpl in Ht. unfold composite_transition in Ht.
    destruct som as (s, om). destruct l as (il, l).
    simpl in *.  unfold vtransition in Ht. simpl in Ht.
    destruct l as [c|].
    - inversion Ht. subst m. simpl.
      rewrite state_update_eq.
      replace (s il) with (project (update_consensus (update_state (s il) (s il) il) c) il) at 1.
      + apply @observations_in_project with Mindex; try assumption.
        apply message_eq_dec.
      + rewrite <- update_consensus_clean.
        apply @project_same; try assumption.
        apply @protocol_prop_no_bottom with il idec est.
        destruct Hv as [Hs _].
        apply
          (@protocol_state_projection message index idec IM_index i0 constraint il)
          in Hs.
        destruct Hs as [_om Hs].
        apply proj_pre_loaded_protocol_prop in Hs.
        exists _om. assumption.
    - destruct om as [im|]; inversion Ht.
   Qed.
 
End Composition.