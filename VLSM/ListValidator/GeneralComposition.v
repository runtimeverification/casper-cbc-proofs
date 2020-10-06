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
  (preX := pre_loaded_with_all_messages_vlsm X)
  (Hevidence := fun (i : index) => @observable_full index index_listing idec)
  {Mindex : Measurable index}
  {Rindex : ReachableThreshold index}
  .

  Definition composed_eqv_evidence
  : observation_based_equivocation_evidence (vstate X) index state state_eq_dec comparable_states
  :=
  (@composed_observation_based_equivocation_evidence
    message index state
    state_eq_dec comparable_states
    index index_listing IM_index Hevidence
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
    - assert ((s i) <> Bottom). {
          apply (@protocol_prop_no_bottom index i _ _ est).
          destruct Hv as [Hv _].
          apply (protocol_state_projection IM_index i0 constraint i) in Hv.
          destruct Hv as [_oms Hv].
          apply proj_pre_loaded_with_all_messages_protocol_prop in Hv.
          unfold protocol_state_prop.
          exists _oms.
          assumption.
      }
      assert ((s il) <> Bottom). {
          apply (@protocol_prop_no_bottom index il _ _ est).
          destruct Hv as [Hv _].
          apply (protocol_state_projection IM_index i0 constraint il) in Hv.
          destruct Hv as [_oms Hv].
          apply proj_pre_loaded_with_all_messages_protocol_prop in Hv.
          unfold protocol_state_prop.
          exists _oms.
          assumption.
      }
      inversion Ht. subst m. simpl.
      rewrite state_update_eq.
      rewrite (@observations_disregards_cv index i index_listing idec est).
      destruct (eq_dec il i).
      + subst il. intros ob Hob.
        apply (@observations_update_eq index i index_listing Hfinite idec est).
        assumption.
        assumption.
        reflexivity.
        apply set_add_iff. apply set_add_iff in Hob.
        destruct Hob as [Hob | Hob]; try (left; assumption).
        right. apply set_union_iff. left. assumption.
      + intros ob Hob.
       apply (@observations_update_neq index i index_listing Hfinite idec est); try assumption.
       reflexivity.
        apply set_union_iff. left. assumption.
    - destruct om as [im|]; inversion Ht.
   Qed.

  Program Instance Hcomposite
    : composite_vlsm_observable_messages index_listing IM_index Hevidence i0 constraint
    :=
    { message_observable_events := message_observable_events_lv;
      message_observable_consistency := message_observable_consistency_lv;
    }.
  Next Obligation.
  unfold composed_observable_events.
  unfold vinitial_state_prop in His.
  simpl in His.
  unfold composite_initial_state_prop in His.
  unfold vinitial_state_prop in His.
  simpl in His.
  unfold initial_state_prop in His.
  apply set_union_iterated_empty.
  intros.
  rewrite in_map_iff in H.
  destruct H.
  unfold observable_events in H.
  unfold Hevidence in H.
  unfold observable_full in H.
  specialize (His x).
  destruct His as [cv Heq].
  rewrite Heq in H.
  destruct H as [H _].
  unfold full_observations in H.
  destruct s0.
  reflexivity.
  assert (In s0 (get_observations v (@depth index index_listing (Something cv all_bottom)) (Something cv all_bottom))). {
    rewrite H.
    intuition.
  }
  assert (s0 <> Bottom). {
    apply (@no_bottom_in_observations index index_listing Hfinite) in H0.
    assumption.
  }
  apply (@unfold_full_observations index index_listing Hfinite) in H0.
  destruct H0.
  simpl in H0.
  rewrite project_all_bottom in H0.
  elim H1.
  intuition.
  destruct H0 as [i Hin].
  simpl in Hin.
  rewrite project_all_bottom in Hin.
  simpl in Hin.
  exfalso.
  assumption.
  intros contra.
  discriminate contra.
  assumption.
  Qed.

  Program Instance Hunforgeable
    : unforgeable_messages index_listing IM_index Hevidence i0 constraint (fun i:index => i)
    := {}.
  Next Obligation.
    unfold message_observable_events_lv.
    unfold observable_events.
    unfold Hevidence.
    unfold observable_full.
    destruct Ht as [Hvalid Ht].
    simpl in Ht. unfold composite_transition in Ht.
    destruct l as (il, l).
    simpl in *.  unfold vtransition in Ht. simpl in Ht.
        assert (Hnb : (s il) <> Bottom). {
          apply (@protocol_prop_no_bottom index il _ _ est).
          destruct Hvalid as [Hvalid _].
          apply (protocol_state_projection IM_index i0 constraint il) in Hvalid.
          destruct Hvalid as [_oms Hvalid].
          apply proj_pre_loaded_with_all_messages_protocol_prop in Hvalid.
          unfold protocol_state_prop.
          exists _oms.
          assumption.
        }
    destruct l as [c|] eqn : eq_l.
    - inversion Ht.
      unfold incl.
      intros.
      destruct om as [m|] eqn : eq_om.
      + destruct Hvalid as [_ [_ Hcvalid]].
        unfold constrained_composite_valid in Hcvalid.
        unfold free_composite_valid in Hcvalid.
        unfold vvalid in Hcvalid.
        unfold valid in Hcvalid.
        unfold machine in Hcvalid.
        simpl in Hcvalid.
        destruct Hcvalid.
        destruct H2 as [_ contra].
        discriminate contra.
      + rewrite state_update_eq in H.
        rewrite (@observations_disregards_cv index il index_listing idec est) in H.
        specialize (@observations_update_neq index il index_listing Hfinite idec est).
        intros.
        specialize (H2 (s il) (s il) Hnb Hnb v il eq_refl).
        spec H2.
        intuition.
        unfold set_eq in H2.
        destruct H2 as [H2 _].
        unfold incl in H2.
        specialize (H2 a H).
        apply set_union_elim in H2.
        destruct H2; intuition.
    - destruct om as [m|] eqn : eq_om.
      + inversion Ht.
        destruct Hvalid as [_ [_ Hcvalid]].
          unfold constrained_composite_valid in Hcvalid.
          unfold free_composite_valid in Hcvalid.
          unfold vvalid in Hcvalid.
          unfold valid in Hcvalid.
          unfold machine in Hcvalid.
          simpl in Hcvalid.
          destruct Hcvalid as [Hcvalid _].
          destruct Hcvalid as [Hproject [Hnb2 Hother]].
        destruct (eq_dec (fst m) v).
        * rewrite state_update_eq.
          unfold incl.
          intros.
          specialize (@observations_update_eq index v index_listing Hfinite idec est (s il)).
          intros.
          specialize (H2 (snd m) Hnb).
          rewrite e in Hproject.
          symmetry in Hproject.
          specialize (H2 Hnb2 v Hproject).
          unfold set_eq in H2.
          destruct H2 as [H2 _].
          unfold incl in H2.
          rewrite e in H.
          specialize (H2 a H).
          apply set_add_elim in H2.
          destruct H2.
          apply set_union_intro.
          right.
          simpl.
          unfold message_observable_events_lv.
          rewrite eq_dec_if_true.
          rewrite H2.
          apply set_add_intro2.
          reflexivity.
          assumption.
          simpl.
          unfold message_observable_events_lv.
          rewrite eq_dec_if_true.
          apply set_union_intro.
          apply set_union_elim in H2.
          destruct H2.
          left. assumption.
          right. apply set_add_intro1.
          assumption.
          assumption.
        * rewrite state_update_eq.
          unfold incl.
          intros.
          specialize (@observations_update_neq index v index_listing Hfinite idec est (s il) (snd m)).
          intros.
          symmetry in Hproject.
          specialize (H2 Hnb Hnb2 v (fst m) Hproject n).
          unfold set_eq in H2.
          destruct H2 as [H2 _].
          unfold incl in H2.
          specialize (H2 a H).
          simpl.
          unfold message_observable_events_lv.
          rewrite eq_dec_if_false.
          assumption.
          assumption.
       + unfold constrained_composite_valid in Hvalid.
         unfold free_composite_valid in Hvalid.
         unfold vvalid in Hvalid.
         unfold valid in Hvalid.
         unfold machine in Hvalid.
         simpl in Hvalid.
         intuition.
  Qed.

  Let id := fun i : index => i.
  Existing Instance comparable_states.
  Let trace_generated_event_lv := trace_generated_event index_listing IM_index Hevidence i0 constraint.
  Let trace_generated_index_lv := trace_generated_index index_listing IM_index Hevidence i0 constraint (fun i:index => i).

  Lemma generated_events_lv_sent
    (is : vstate X)
    (tr : list transition_item)
    (Htr : finite_protocol_trace X is tr)
    (v : index)
    (e : state)
    (He : trace_generated_event_lv is tr v e)
    : exists
      (prefix suffix : list (transition_item))
      (Heq : tr = prefix ++ suffix),
      e = last (map destination prefix) is v.
  Proof.
    destruct He as [prefix [suffix [item [Heq He]]]].
    exists prefix. exists ([item] ++ suffix). exists Heq.
    specialize (trace_generated_index_lv is tr Htr v e prefix suffix item Heq He).
    unfold id in trace_generated_index_lv.
    rewrite <- trace_generated_index_lv in He.
    apply set_diff_iff in He. destruct He as [He Hne].
    specialize (protocol_transition_to X is item tr prefix suffix Heq (proj1 Htr))
      as Ht.
    destruct Ht as [[Ha [_ [Hv _]]] Ht]. simpl in Ht. simpl in Hv.
    assert (Hnb : last (map destination prefix) is v <> Bottom). {
        apply (@protocol_prop_no_bottom index v _ _ est).
          apply (protocol_state_projection IM_index i0 constraint v) in Ha.
          destruct Ha as [_oms Ha].
          apply proj_pre_loaded_with_all_messages_protocol_prop in Ha.
          unfold protocol_state_prop.
          exists _oms.
          assumption.
      }
    destruct
      ( @l (@ListValidator.message index index_listing)
      (@composite_type (@ListValidator.message index index_listing)
         index IM_index) item)
      as (i, li) eqn:Hl.
    replace (l item) with (existT (fun n : index => vlabel (IM_index n)) i li)
      in trace_generated_index_lv. simpl in trace_generated_index_lv. subst i.
    unfold vtransition in Ht. simpl in Ht. unfold vvalid in Hv. simpl in Hv.
    destruct li as [c|].
    - inversion Ht.
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
      rewrite (@observations_disregards_cv index v index_listing idec est) in He.
      apply (@observations_update_eq index v index_listing Hfinite idec est) in He.
      apply set_add_iff in He.
      destruct He as [He | He]; try assumption.
      elim Hne. apply set_union_iff. left.
      apply set_union_iff in He. destruct He; assumption.
      assumption.
      assumption.
      reflexivity.
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
          intuition.
        * apply (@observations_update_neq index v index_listing Hfinite idec est) in He; try assumption.
          apply set_union_iff in He.
          assumption.
          intuition.
          intuition.
      + inversion Hv.
  Qed.

  Lemma comparable_generated_events_lv
    (is : vstate X)
    (tr : list transition_item)
    (Htr : finite_protocol_trace X is tr)
    (v : index)
    (e1 e2 : state)
    (He1 : trace_generated_event_lv is tr v e1)
    (He2 : trace_generated_event_lv is tr v e2)
    : comparableb happens_before_fn e1 e2 = true.
  Proof.
    apply generated_events_lv_sent in He1; try assumption.
    apply generated_events_lv_sent in He2; try assumption.
    destruct He1 as [pre1 [suf1 [Heq1 He1]]].
    destruct He2 as [pre2 [suf2 [Heq2 He2]]].
    assert (Heq := Heq2).
    rewrite Heq1 in Heq.
    apply order_decompositions in Heq.
    unfold comparableb.
    destruct (eq_dec e1 e2); try reflexivity.
    destruct Heq as [Heq | [Hgt | Hlt]]
    ; try (elim n; subst; reflexivity)
    ; apply orb_true_iff.
    - right.
      apply @state_lt_function; try assumption.
      apply
        (@state_lt_in_futures index v index_listing Hfinite idec est e2 e1)
      ; try (intro contra; elim n; symmetry; assumption).
      remember (composite_vlsm_constrained_projection IM_index i0 constraint v) as Xj.
      apply
        (VLSM_incl_in_futures
          (composite_vlsm_constrained_projection_machine IM_index i0 constraint v)
          (pre_loaded_with_all_messages_vlsm_machine (@VLSM_list index v index_listing idec est))
        )
      ; try apply (proj_pre_loaded_with_all_messages_incl IM_index i0 constraint v).
      subst e1 e2.
      apply (in_futures_projection IM_index i0 constraint v).
      destruct Hgt as [suf1' Hgt].
      exists suf1'.
      split.
      + clear Heq2. subst tr. subst pre1.
        destruct Htr as [Htr Hinit].
        apply (finite_protocol_trace_from_app_iff X) in Htr.
        destruct Htr as [Htr _].
        apply (finite_protocol_trace_from_app_iff X) in Htr.
        destruct Htr as [_ Htr].
        assumption.
      + subst pre1. rewrite map_app. rewrite last_app. reflexivity.
    - left.
      apply @state_lt_function; try assumption.
      apply
        (@state_lt_in_futures index v index_listing Hfinite idec est e1 e2)
      ; try assumption.
      remember (composite_vlsm_constrained_projection IM_index i0 constraint v) as Xj.
      apply
        (VLSM_incl_in_futures
          (composite_vlsm_constrained_projection_machine IM_index i0 constraint v)
          (pre_loaded_with_all_messages_vlsm_machine (@VLSM_list index v index_listing idec est))
        )
      ; try apply (proj_pre_loaded_with_all_messages_incl IM_index i0 constraint v).
      subst e1 e2.
      apply (in_futures_projection IM_index i0 constraint v).
      destruct Hlt as [suf2' Hlt].
      exists suf2'.
      split.
      + clear Heq1. subst tr. subst pre2.
        destruct Htr as [Htr Hinit].
        apply (finite_protocol_trace_from_app_iff X) in Htr.
        destruct Htr as [Htr _].
        apply (finite_protocol_trace_from_app_iff X) in Htr.
        destruct Htr as [_ Htr].
        assumption.
      + subst pre2. rewrite map_app. rewrite last_app. reflexivity.
  Qed.

  Instance composite_vlsm_comparable_generated_events_lv
    : composite_vlsm_comparable_generated_events index_listing IM_index Hevidence i0 constraint
    :=
    {
      comparable_generated_events := comparable_generated_events_lv
    }.

End Composition.
