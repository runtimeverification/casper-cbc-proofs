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
    let obs := @full_observations index index_listing idec (snd m) target in
    if (eq_dec (fst m) target) then set_add eq_dec (snd m) obs else obs.

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
      rewrite (@observations_disregards_cv index i index_listing Hfinite idec est message_eq_dec
        Mindex Rindex).
      destruct (eq_dec il i).
      + subst il. intros ob Hob.
        apply (@observations_update_eq index i index_listing Hfinite idec est message_eq_dec
          Mindex Rindex).
        apply set_add_iff. apply set_add_iff in Hob.
        destruct Hob as [Hob | Hob]; try (left; assumption).
        right. apply set_union_iff. left. assumption.
      + intros ob Hob.
       apply (@observations_update_neq index i index_listing Hfinite idec est message_eq_dec
          Mindex Rindex); try assumption.
        apply set_union_iff. left. assumption.
    - destruct om as [im|]; inversion Ht.
   Qed.

  Program Instance Hcomposite
    : composite_vlsm_observable_messages index_listing IM_index Hevidence i0 constraint (fun i:index => i)
    :=
    { message_observable_events := message_observable_events_lv;
      message_observable_consistency := message_observable_consistency_lv;
    }.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
 
  Let id := fun i : index => i.
  Existing Instance comparable_states.
  Let trace_generated_event_lv := trace_generated_event index_listing IM_index Hevidence i0 constraint id.
  Let trace_generated_index_lv := trace_generated_index index_listing IM_index Hevidence i0 constraint id.

  Lemma generated_events_lv_sent
    (is : vstate X)
    (tr : list transition_item)
    (Htr : finite_protocol_trace X is tr)
    (v : index)
    (e : state)
    (He : trace_generated_event_lv is tr v e)
    : exists
      (prefix suffix : list transition_item)
      (item : transition_item)
      (Heq : tr = prefix ++ [item] ++ suffix),
      v = projT1 (l item) /\ output item = Some (v, e).
  Proof.
    destruct He as [prefix [suffix [item [Heq He]]]].
    exists prefix. exists suffix. exists item. exists Heq.
    specialize (trace_generated_index_lv is tr Htr v e prefix suffix item Heq He).
    unfold id in trace_generated_index_lv.
    split; try assumption.
    rewrite <- trace_generated_index_lv in He.
    apply set_diff_iff in He. destruct He as [He Hne].
    specialize (protocol_transition_to X is item tr prefix suffix Heq (proj1 Htr))
      as Ht.
    destruct Ht as [Hv Ht]. simpl in Ht.
    destruct
      ( @l (@ListValidator.message index index_listing)
      (@composite_type (@ListValidator.message index index_listing)
         index IM_index) item)
      as (i, li) eqn:Hl.
    replace (l item) with (existT (fun n : index => vlabel (IM_index n)) i li)
      in trace_generated_index_lv. simpl in trace_generated_index_lv. subst i.
    unfold vtransition in Ht. simpl in Ht.
    destruct li as [c|].
    - inversion Ht.
      replace
        ((@output (@ListValidator.message index index_listing)
        (@type (@ListValidator.message index index_listing) X) item))
        with (Some (v, last (map destination prefix) is v)).
      f_equal. f_equal.
      replace
        (@destination (@ListValidator.message index index_listing)
        (@type (@ListValidator.message index index_listing)
           (@composite_vlsm (@ListValidator.message index index_listing)
              index idec IM_index i0 constraint)) item)
        with
          (state_update IM_index (last (map destination prefix) is) v
          (update_consensus
             (update_state (last (map destination prefix) is v)
                (last (map destination prefix) is v) v) c))
        in He.
      rewrite state_update_eq in He.
      unfold observable_events in He. simpl in He.
      unfold observable_events in Hne. simpl in Hne.
      rewrite (@observations_disregards_cv index v index_listing Hfinite idec est message_eq_dec
        Mindex Rindex) in He.
      apply (@observations_update_eq index v index_listing Hfinite idec est message_eq_dec
        Mindex Rindex) in He.
      apply set_add_iff in He. symmetry.
      destruct He as [He | He]; try assumption.
      elim Hne. apply set_union_iff. left.
      apply set_union_iff in He. destruct He; assumption.
    - elim Hne. apply set_union_iff.
      destruct
        (@input (@ListValidator.message index index_listing)
        (@composite_type (@ListValidator.message index index_listing)
           index IM_index) item)
        as [m|] eqn:Hinput; inversion Ht.
      + replace
          (@destination (@ListValidator.message index index_listing)
            (@type (@ListValidator.message index index_listing)
               (@composite_vlsm (@ListValidator.message index index_listing)
                  index idec IM_index i0 constraint)) item)
          with
            (state_update IM_index (last (map destination prefix) is) v
            (update_state (last (map destination prefix) is v) (snd m) (fst m)))
          in He.
        rewrite state_update_eq in He.
        unfold observable_events in He. simpl in He.
        replace
          ((@input (@ListValidator.message index index_listing)
          (@type (@ListValidator.message index index_listing)
             (@composite_vlsm (@ListValidator.message index index_listing)
                index idec IM_index i0 constraint)) item))
          with (Some m).
        unfold option_message_observable_events. unfold message_observable_events.
        simpl. unfold message_observable_events_lv.
        destruct (eq_dec (fst m) v).
        * subst v.
          apply (@observations_update_eq index (fst m) index_listing Hfinite idec est message_eq_dec
              Mindex Rindex) in He.
  Admitted.
      

  Lemma comparable_generated_events
    (is : vstate X)
    (tr : list transition_item)
    (Htr : finite_protocol_trace X is tr)
    (v : index)
    (e1 e2 : state)
    (He1 : trace_generated_event_lv is tr v e1)
    (He2 : trace_generated_event_lv is tr v e2)
    : comparableb happens_before_fn e1 e2 = true.
  Proof.
    

  Admitted.
  

End Composition.