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
        (@comparable_states index index_listing idec))
  {Mindex : Measurable index}
  {Rindex : ReachableThreshold index}.
  
  Definition composed_computable_observable_equivocation_evidence
  : computable_observable_equivocation_evidence (vstate X) index state state_eq_dec comparable_states
  :=
  {| observable_events := (@composed_observable_events _ _ _ state_eq_dec _ _ _ index_listing IM_index Hevidence i0 constraint)|}.

  Existing Instance composed_computable_observable_equivocation_evidence.
  
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
      (@observable_events _ _ _ _ _ observable_full (dest (projT1 l)) i).
   
   Proof.
    unfold message_observable_events_lv.
    unfold observable_events.
    unfold observable_full.
    unfold incl.
    intros.
    unfold protocol_transition in Ht.
    destruct Ht as [Hvalid Htransition].
    simpl in *.
    unfold composite_transition in Htransition.
    destruct som as [source om] in Htransition.
    destruct l as [t_index l'] in Htransition.
    unfold vtransition in Htransition.
    simpl in *.
    destruct l' eqn: eq_label.
    - inversion Htransition.
      rewrite <- H2 in H.
      inversion H1.
      destruct (eq_dec t_index i).
      + assert (source t_index = project (dest t_index) i). {
          admit.
        }
        rewrite H0.
        assert (projT1 l = t_index). {
          admit.
        }
        rewrite H4.
        simpl in H.
        rewrite H3 in H.
        specialize (@observations_in_project _ i index_listing Hfinite idec message_eq_dec Mindex Rindex).
        intros.
        specialize (H5 (dest t_index) a i i).
        apply H5.
        assumption.
      + 
      
   Admitted.
 
End Composition.