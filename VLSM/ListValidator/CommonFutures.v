Require Import Bool List ListSet Reals FinFun RelationClasses Relations Relations_1 Sorting Basics.
Require Import Lia.
Import ListNotations.
From CasperCBC
Require Import
  Lib.Preamble
  Lib.ListExtras
  Lib.ListSetExtras
  Lib.SortedLists
  VLSM.Common
  VLSM.Plans
  VLSM.Composition
  VLSM.Equivocation
  VLSM.ListValidator.ListValidator
  VLSM.ListValidator.Equivocation
  VLSM.ListValidator.EquivocationAwareListValidator
  VLSM.ListValidator.GeneralComposition
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
  {Mindex : Measurable index}
  {Rindex : ReachableThreshold index}
  (Rtemp := fun (i : index) => RelDecision (@state_lt' index index_listing _ i))
  (est' := fun (i : index) => (@EquivocationAwareListValidator.equivocation_aware_estimator _ i _ Hfinite _ _ _ ))
  (IM_index := fun (i : index) => @VLSM_list index i index_listing idec (est' i))
  (has_been_sent_capabilities := fun i : index => @has_been_sent_lv index i index_listing Hfinite idec (est' i))
  (has_been_received_capabilities := fun i : index => @has_been_received_lv index i index_listing Hfinite idec (est' i))
  (X := composite_vlsm IM_index i0 (free_constraint IM_index))
  (preX := pre_loaded_with_all_messages_vlsm X)
  (complete_observations := @complete_observations index i0 index_listing decide_eq)
  (Hevents_set' := fun (i : index) => @simp_lv_observable_events index i index_listing _)
  (Hstate_events_set := fun (i : index) => @simp_lv_state_observations index i index_listing _)
  (Hevidence := fun (i : index) => @simp_observable_full index i index_listing idec)
  (Hstate_events_fn := fun (i : index) => (@simp_lv_observations index i index_listing _))
  (Hbasic := fun (i : index) => @simp_lv_basic_equivocation index i index_listing Hfinite idec Mindex Rindex).
  
  Local Notation in_listing := (proj2 Hfinite).
  
  Proposition self_projections_same_after_receive
    (s : vstate X)
    (Hpr : protocol_state_prop X s)
    (i : index)
    (ai : vplan_item X)
    (Hrec : projT2 (label_a ai) = receive)
    (Hprai : finite_protocol_plan_from X s [ai]) :
    project ((snd (apply_plan X s [ai])) i) i = project (s i) i.
  Proof.
    apply finite_protocol_plan_from_one in Hprai.
    destruct Hprai as [Hprotocol Htransition].
    unfold protocol_valid in Hprotocol.
    unfold valid in Hprotocol.
    simpl in Hprotocol.
    unfold constrained_composite_valid in Hprotocol.
    unfold free_composite_valid in Hprotocol.
    unfold vvalid in Hprotocol.
    unfold valid in Hprotocol.
    simpl in Hprotocol.
    simpl in Hrec. 
    destruct ai. simpl in *.
    destruct label_a. simpl in *. subst v. simpl in *.
    destruct input_a eqn : eq_input.
    + simpl in Htransition.
      assert (x <> fst m) by intuition.
      simpl.
      destruct (decide (i = x)).
      * subst x. rewrite state_update_eq. 
        rewrite (@project_different index index_listing Hfinite).
        intuition. intuition.
        apply protocol_state_component_no_bottom. intuition.
     * rewrite state_update_neq by intuition.
       intuition.
    + intuition. 
  Qed.
  
  Proposition self_projections_same_after_receives
    (s : vstate X)
    (Hpr : protocol_state_prop X s)
    (a : vplan X)
    (Hpra : finite_protocol_plan_from X s a)
    (Hrec : forall (ai : vplan_item X), In ai a -> projT2 (label_a ai) = receive) :
    let res := snd (apply_plan X s a) in
    forall (i : index), project (res i) i = project (s i) i.
  Proof.
    induction a using rev_ind.
    - intuition.
    - simpl in *.
      intros.
      rewrite apply_plan_app.
      destruct (apply_plan X s a) as (tr_long, res_long) eqn : eq_long.
      destruct (apply_plan X res_long [x]) as (tr_short, res_short) eqn : eq_short.
      
      assert (Hres_long : res_long = snd ((apply_plan X s a))) by (rewrite eq_long; intuition).
      assert (Hres_short : res_short = snd (apply_plan X res_long [x])) by (rewrite eq_short; intuition).
      simpl in *.
      
      apply finite_protocol_plan_from_app_iff in Hpra.
      destruct Hpra as [Hpra_long Hpra_short].
      
      specialize (IHa Hpra_long).
      
      spec IHa. {
        intros. specialize (Hrec ai). 
        spec Hrec. apply in_app_iff. intuition. intuition.
      }
      
      specialize (IHa i).
      rewrite <- IHa.
      
      assert (Hpr_long : protocol_state_prop X res_long). {
        rewrite Hres_long.
        apply apply_plan_last_protocol.
        all : intuition.
      }
      
      specialize (self_projections_same_after_receive res_long Hpr_long i x) as Hone.
      spec Hone. {
        specialize (Hrec x). spec Hrec. apply in_app_iff. intuition.
        intuition.
     }
     rewrite Hres_long in Hone.
     specialize (Hone Hpra_short).
     rewrite Hres_long. rewrite Hres_short.
     rewrite Hres_long.
     intuition.
  Qed.
  
  Proposition non_self_projections_same_after_send
    (s : vstate X)
    (Hpr : protocol_state_prop X s)
    (i j : index)
    (Hdif : i <> j)
    (ai : vplan_item X)
    (Hrec : exists (c : bool), projT2 (label_a ai) = update c)
    (Hprai : finite_protocol_plan_from X s [ai]) :
    project ((snd (apply_plan X s [ai])) i) j = project (s i) j.
  Proof.
    apply finite_protocol_plan_from_one in Hprai.
    destruct Hprai as [Hprotocol Htransition].
    unfold protocol_valid in Hprotocol.
    unfold valid in Hprotocol.
    simpl in Hprotocol.
    unfold constrained_composite_valid in Hprotocol.
    unfold free_composite_valid in Hprotocol.
    unfold vvalid in Hprotocol.
    unfold valid in Hprotocol.
    simpl in Hprotocol.
    simpl in Hrec. 
    destruct ai. simpl in *.
    destruct label_a. simpl in *. 
    destruct Hrec as [c Heqv].
    subst v. simpl in *.
    destruct input_a eqn : eq_input.
    + simpl in Htransition.
      intuition congruence.
    + destruct (decide (x = i)).
      * subst x.
        rewrite state_update_eq.
        rewrite <- update_consensus_clean with (value := c).
        rewrite (@project_different index index_listing Hfinite).
        intuition. intuition.
        apply protocol_state_component_no_bottom. intuition.
      * rewrite state_update_neq by intuition.
        intuition.
  Qed.
  
  Proposition non_self_projections_same_after_sends
    (s : vstate X)
    (Hpr : protocol_state_prop X s)
    (a : vplan X)
    (Hpra : finite_protocol_plan_from X s a)
    (Hrec : forall (ai : vplan_item X), In ai a -> exists (c : bool), projT2 (label_a ai) = update c) :
    let res := snd (apply_plan X s a) in
    forall (i j : index), i <> j -> project (res i) j = project (s i) j.
  Proof.
    induction a using rev_ind.
    - intuition.
    - simpl in *.
      intros.
      rewrite apply_plan_app.
      destruct (apply_plan X s a) as (tr_long, res_long) eqn : eq_long.
      destruct (apply_plan X res_long [x]) as (tr_short, res_short) eqn : eq_short.
      
      assert (Hres_long : res_long = snd ((apply_plan X s a))) by (rewrite eq_long; intuition).
      assert (Hres_short : res_short = snd (apply_plan X res_long [x])) by (rewrite eq_short; intuition).
      simpl in *.
      
      apply finite_protocol_plan_from_app_iff in Hpra.
      destruct Hpra as [Hpra_long Hpra_short].
      
      specialize (IHa Hpra_long).
      
      spec IHa. {
        intros. specialize (Hrec ai).
        spec Hrec. apply in_app_iff. intuition. intuition.
      }
      
      specialize (IHa i).
      rewrite <- IHa.
      
      assert (Hpr_long : protocol_state_prop X res_long). {
        rewrite Hres_long.
        apply apply_plan_last_protocol.
        all : intuition.
      }
      
      specialize (non_self_projections_same_after_send res_long Hpr_long i j H x) as Hone.
      spec Hone. {
        specialize (Hrec x). spec Hrec. apply in_app_iff. intuition.
        intuition.
     }
     rewrite Hres_long in Hone.
     specialize (Hone Hpra_short).
     rewrite Hres_long. rewrite Hres_short.
     rewrite Hres_long.
     intuition.
     intuition.
  Qed.
  
  Definition get_message_providers_from_plan
   (a : vplan X) : list index :=
    List.map fst (messages_a X a).
  
  Definition component_list (s : vstate X) (li : list index) :=
    List.map s li.
  
  Definition obs 
    (i : index) 
    := (@lv_observations index i index_listing _).
  
  Section EquivObsUtils.
  Context
  {ws : set index}.
  
  Definition Hstate_validators := fun (i : index) => (fun (s : vstate (IM_index i)) => index_listing).
  
  Program Instance lv_composed_observable_events :
     observable_events (vstate X) simp_lv_event := 
     composite_state_observable_events_instance
     index_listing
     ws
     IM_index
     Hstate_events_fn
     Hstate_validators.
  
  Definition ce := 
  @composite_observable_events_equivocation_evidence
    message index simp_lv_event
    decide_eq
    index index_listing ws IM_index
    Hstate_events_fn
    Hstate_validators
    decide_eq
    simp_lv_event_lt
    simp_lv_event_lt_dec
    get_simp_event_subject_some.
  
  Definition wH (s : vstate X) : set index := 
    List.filter (fun i : index => negb (
    @bool_decide _ (@composite_observable_events_equivocation_evidence_dec
      message index simp_lv_event
      decide_eq
      index index_listing ws IM_index
      Hstate_events_fn
      Hstate_validators
      decide_eq
      simp_lv_event_lt
      simp_lv_event_lt_dec
      get_simp_event_subject_some s i))) index_listing.
    
  Definition wE (s : vstate X) : set index := 
    List.filter (fun i : index => 
    @bool_decide _ (@composite_observable_events_equivocation_evidence_dec
      message index simp_lv_event
      decide_eq
      index index_listing ws IM_index
      Hstate_events_fn
      Hstate_validators
      decide_eq
      simp_lv_event_lt
      simp_lv_event_lt_dec
      get_simp_event_subject_some s i)) index_listing.
  
  Definition wcobs := 
    (composite_state_events_fn ws IM_index Hstate_events_fn).
  
  Definition wcobs_messages 
    (s : vstate X)
    (target : index) :=
  fold_right (set_union decide_eq) [] (List.map (fun (i : index) => (simp_lv_message_observations (s i) target)) ws).
  
  Definition wcobs_states
    (s : vstate X)
    (target : index) : set simp_lv_event :=
    fold_right (set_union decide_eq) [] (List.map (fun (i : index) => (@simp_lv_state_observations index i index_listing _) (s i) target) ws).
  
  Lemma in_cobs_messages
    (s : vstate X)
    (target : index)
    (e : simp_lv_event)
    (Hin : In e (wcobs_messages s target)) :
    get_simp_event_type e = Message'.
  Proof.
    unfold wcobs_messages in Hin.
    apply set_union_in_iterated in Hin.
    rewrite Exists_exists in Hin.
    destruct Hin as [le [Hinle Hine]].
    apply in_map_iff in Hinle.
    destruct Hinle as [s' [Heqmess _]].
    unfold flip in Heqmess.
    rewrite <- Heqmess in Hine.
    apply in_simp_lv_message_observations in Hine.
    intuition.
  Qed.
  
  Lemma in_cobs_states
    (s : vstate X)
    (target : index)
    (e : simp_lv_event)
    (Hin : In e (wcobs_states s target)) :
    get_simp_event_type e = State'.
  Proof.
    unfold wcobs_messages in Hin.
    apply set_union_in_iterated in Hin.
    rewrite Exists_exists in Hin.
    destruct Hin as [le [Hinle Hine]].
    apply in_map_iff in Hinle.
    destruct Hinle as [s' [Heqmess _]].
    unfold flip in Heqmess.
    rewrite <- Heqmess in Hine.
    apply in_simp_lv_state_observations in Hine.
    intuition.
  Qed.
  
  Lemma cobs_single
    (s : vstate X)
    (target : index)
    (e : simp_lv_event) :
    In e (wcobs_messages s target) <->
    exists (i : index), (In i ws) /\ (In e (simp_lv_message_observations (s i) target)).
  Proof.
    split; intros.
    - apply set_union_in_iterated in H. rewrite Exists_exists in H.
      destruct H as [le [Hinle Hine]].
      apply in_map_iff in Hinle.
      destruct Hinle as [ii [Heqle Hini]].
      exists ii. rewrite <- Heqle in Hine. intuition.
    - apply set_union_in_iterated. rewrite Exists_exists.
      destruct H as [i Hi].
      exists (simp_lv_message_observations (s i) target).
      split.
      + apply in_map_iff. exists i. split;intuition.
      + intuition.
  Qed.
  
  Lemma cobs_messages_states
    (s : vstate X)
    (target : index) :
    set_eq (wcobs s target) (set_union decide_eq (wcobs_states s target) (wcobs_messages s target)).
  Proof.
    unfold wcobs, wcobs_states, wcobs_messages.
    unfold composite_state_events_fn.
    remember (map (fun i : index => Hstate_events_fn i (s i) target) ws) as ss.
    specialize (@set_union_iterated_part (@simp_lv_event index index_listing) decide_eq ss) as Hpart.
    remember (filter (fun (e : simp_lv_event) => @bool_decide ((@get_simp_event_type index index_listing) e = Message') _)) as f.
    remember (filter (fun (e : simp_lv_event) => @bool_decide ((@get_simp_event_type index index_listing) e = State') _)) as g.
    specialize (Hpart f g).
    
    spec Hpart. {
      intros.
      rewrite Heqss in H.
      apply in_map_iff in H.
      destruct H as [i [Heq Hini]].
      unfold Hstate_events_fn in Heq. 
      rewrite <- Heq. rewrite Heqf. rewrite Heqg.
      unfold simp_lv_observations at 1.
      apply set_eq_extract_forall. intros e.
      split; intros.
      - apply set_union_iff in H.
        destruct H.
        + setoid_rewrite simp_lv_message_f_eq in H.
          apply set_union_iff. left. intuition.
        + setoid_rewrite simp_lv_state_f_eq in H.
          apply set_union_iff. right. intuition.
      - apply set_union_iff in H.
        destruct H.
        + apply set_union_iff. left.
          setoid_rewrite simp_lv_message_f_eq.
          intuition.
        + apply set_union_iff. right.
          setoid_rewrite simp_lv_state_f_eq.
          intuition.
      }
      apply set_eq_extract_forall. intros e.
      specialize (Hpart e).
      rewrite Heqf in Hpart. rewrite Heqg in Hpart.
      split.
      - intros.
        apply Hpart in H.
        apply set_union_iff in H.
        apply set_union_iff.
        destruct H.
        + right. apply set_union_in_iterated in H. rewrite Exists_exists in H.
  Admitted.
  
  Lemma in_cobs_and_message
    (s : vstate X)
    (target : index)
    (e : simp_lv_event)
    (Hm : get_simp_event_type e = Message')
    (Hin : In e (wcobs s target)) :
    In e (wcobs_messages s target).
  Proof.
    setoid_rewrite cobs_messages_states in Hin.
    apply set_union_iff in Hin.
    destruct Hin.
    - apply in_cobs_states in H. congruence.
    - intuition.
  Qed.
  
  Lemma in_cobs_states'
    (s : vstate X)
    (target : index)
    (e : simp_lv_event)
    (Hin : In e (wcobs_states s target)) :
    In e (wcobs s target).
  Proof.
    setoid_rewrite cobs_messages_states.
    apply set_union_iff.
    left. intuition.
  Qed.
  
  Lemma in_cobs_messages'
    (s : vstate X)
    (target : index)
    (e : simp_lv_event)
    (Hin : In e (wcobs_messages s target)) :
    In e (wcobs s target).
  Proof.
    setoid_rewrite cobs_messages_states.
    apply set_union_iff.
    right. intuition.
  Qed.
  
  Definition cequiv_evidence
    := (@equivocation_evidence 
    (vstate X) index simp_lv_event 
    _ decide_eq 
    simp_lv_event_lt simp_lv_event_lt_dec 
    get_simp_event_subject_some ce).
  
  Lemma unique_state_observation 
    (s : vstate X)
    (i : index)
    (e : simp_lv_event)
    (Hin : In e (wcobs_states s i)) : 
    e = SimpObs State' i (s i).
  Proof.
    unfold wcobs in Hin.
    unfold composite_state_events_fn in Hin; simpl in Hin.
    apply set_union_in_iterated in Hin.
    rewrite Exists_exists in Hin.
    destruct Hin as [le [Hinle Hine]].
    rewrite in_map_iff in Hinle.
    destruct Hinle as [j [Heq Hj]].
    rewrite <- Heq in Hine.
    unfold simp_lv_state_observations in Hine.
    destruct (decide (i = j)).
    - subst j.
      destruct Hine; intuition.
    - intuition.
  Qed.
  
  Lemma state_obs_present
    (s : vstate X)
    (i : index)
    (Hin : In i ws) :
    In (SimpObs State' i (s i)) (wcobs_states s i).
  Proof.
    unfold wcobs_states.
    apply set_union_in_iterated.
    rewrite Exists_exists.
    exists (@simp_lv_state_observations index i index_listing _ (s i) i).
    split.
    - apply in_map_iff.
      exists i.
      split;intuition.
    - unfold simp_lv_state_observations.
      rewrite decide_True.
      all : intuition.
  Qed.
  
  Lemma GE_direct 
    (s : vstate X)
    (i : index) :
    In i (wE s) <-> (cequiv_evidence s i).
  Proof.
    split; intros.
    - unfold wE in H.
      unfold wH in H.
      apply filter_In in H.
      destruct H as [_ H].
      apply bool_decide_eq_true in H.
      intuition.
    - unfold wE.
      apply filter_In.
      split.
      apply ((proj2 Hfinite) i).
      apply bool_decide_eq_true.
      intuition.
  Qed.
  
  Lemma hbo_cobs
    (s : vstate X)
    (e : simp_lv_event) :
    has_been_observed s e <->
    In e (wcobs s (get_simp_event_subject e)).
  Proof.
    unfold has_been_observed in *. simpl in *.
    unfold observable_events_has_been_observed in *.
    unfold state_observable_events_fn in *. simpl in *.
    unfold composite_state_events_fn in *. simpl in *.
    split; intros Hine.
    - apply set_union_in_iterated in Hine.
      rewrite Exists_exists in Hine.
      destruct Hine as [le [Hinle Hine]].
      apply in_map_iff in Hinle.
      destruct Hinle as [i [Heqle Hini]].
      assert (i = get_simp_event_subject e). {
        destruct (decide (i = get_simp_event_subject e)); [intuition|].
        rewrite <- Heqle in Hine.
        apply set_union_in_iterated in Hine.
        rewrite Exists_exists in Hine.
        destruct Hine as [le' [Hinle' Hine']].
        apply in_map_iff in Hinle'.
        destruct Hinle' as [k [Heqk Hink]].
        unfold Hstate_events_fn in Heqk.
        rewrite <- Heqk in Hine'.
        apply in_simp_lv_observations in Hine'.
        congruence.
      }
      rewrite <- H.
      unfold wcobs.
      unfold composite_state_events_fn.
      rewrite <- Heqle in Hine.
      intuition.
    - apply set_union_in_iterated.
      rewrite Exists_exists.
      exists (wcobs s (get_simp_event_subject e)).
      split.
      + apply in_map_iff.
        exists (get_simp_event_subject e).
        split.
        * intuition.
        * unfold composite_validators.
          unfold Hstate_validators.
          apply set_union_in_iterated.
          rewrite Exists_exists.
          exists index_listing.
          split.
          -- apply in_map_iff.
             exists i0.
             split;[intuition|]. apply (proj2 Hfinite).
          -- apply ((proj2 Hfinite) (get_simp_event_subject e)).
     + intuition.
  Qed.
    
  Lemma wH_wE'
    (s : vstate X)
    (i : index) :
    In i (wH s) <-> ~ In i (wE s).
  Proof.
    unfold wH.
    unfold wE.
    split; intros.
    - apply filter_In in H.
      intros contra.
      apply filter_In in contra.
      destruct H as [_ H].
      destruct contra as [_ contra].
      rewrite contra in H.
      unfold negb in H. congruence.
    - apply filter_In.
      split; [apply (proj2 Hfinite)|].
      rewrite negb_true_iff.
      match goal with
      |- ?e = _ =>
         destruct e eqn : eq_d end.
      + contradict H.
        apply filter_In.
        split; [apply (proj2 Hfinite)|].
        intuition.
      + intuition.
  Qed.
  
  Lemma wH_wE
    (s : vstate X) :
    set_eq (wH s) (set_diff decide_eq index_listing (wE s)).
  Proof.
    apply set_eq_extract_forall.
    intros i.
    split; intros H.
    - apply set_diff_intro.
      apply (proj2 Hfinite i).
      apply wH_wE' in H.
      intuition.
    - apply set_diff_iff in H.
      destruct H as [_ H].
      apply wH_wE'.
      intuition. 
  Qed.
  
  Lemma HE_eq_equiv
    (s s' : vstate X) :
    set_eq (wH s) (wH s') <-> set_eq (wE s) (wE s').
  Proof.
  Admitted.
  
  End EquivObsUtils.
  
  Definition GE := @wE index_listing.
  Definition GH := @wH index_listing. 
  
  Definition cobs (s : vstate X) := @wcobs index_listing s.
  Definition cobs_messages (s : vstate X) := @wcobs_messages index_listing s.
  Definition cobs_states (s : vstate X) := @wcobs_states index_listing s.
  
  Lemma cobs_message_existing_other_lf
    (s : vstate X)
    (Hpr : protocol_state_prop X s)
    (so : state)
    (i j target : index)
    (Hdif : i <> j)
    (s' := state_update IM_index s i (update_state (s i) so j))
    (Hfull : project (s i) j = project so j)
    (Hhave : In (SimpObs Message' j so) (cobs s j)) :
    incl (cobs_messages s' target) (cobs_messages s target).
  Proof.
    assert (Hsnb : forall (k : index), (s k) <> Bottom). {
      intros k.
      apply protocol_state_component_no_bottom. intuition.
    }
    
    assert (Hsonb : so <> Bottom). {
        apply in_cobs_and_message in Hhave.
        apply cobs_single in Hhave.
        destruct Hhave as [k Hhave].
        destruct Hhave as [_ Hhave].
        apply (@in_message_observations_nb index index_listing Hfinite) in Hhave.
        all : intuition.
    }
    unfold incl.
    intros e.
    intros H.
    unfold cobs_messages in H.
    apply cobs_single in H.
    destruct H as [k Hink].
    destruct (decide (k = i)).
    - subst k.
      unfold s' in Hink.
      rewrite state_update_eq in Hink.
      destruct (decide (j = target)).
      + subst target.
        destruct Hink as [_ Hink].
        apply (@new_incl_rest_same index index_listing Hfinite) in Hink.
        2 : {
          split. apply Hsnb; intuition. intuition.
        }
        2 : intuition. 
       
        apply set_union_iff in Hink.
        destruct Hink as [Hink|Hink].
        * apply set_union_iff in Hink.
          destruct Hink as [Hink|Hink].
          -- apply cobs_single.
             exists i. intuition.
             apply (proj2 Hfinite).
          -- apply in_cobs_and_message in Hhave.
             apply cobs_single in Hhave. 
             destruct Hhave as [l Hhave].
             apply cobs_single.
             exists l.
             split;[apply in_listing|].
             apply (@message_cross_observations index index_listing Hfinite) with (e1 := (SimpObs Message' j so)) (i := j).
             all : intuition.
       * destruct Hink;[|intuition].
         rewrite <- H.
         apply in_cobs_and_message in Hhave.
         all : intuition.
   
      + destruct Hink as [_ Hink].
        apply (@new_incl_rest_diff index index_listing Hfinite) in Hink.
        2 : {
          split. apply Hsnb; intuition. intuition.
        }
        2 : intuition. 
        
        apply set_union_iff in Hink.
        destruct Hink as [Hink|Hink]. 
        apply cobs_single.
        exists i.
        split;[apply in_listing|].
        intuition.
        apply in_cobs_and_message in Hhave.
        2 : intuition.  
        apply cobs_single in Hhave.
        destruct Hhave as [l Hhave].
        apply cobs_single.
        exists l.
        split;[apply in_listing|].
        apply (@message_cross_observations index index_listing Hfinite) with (e1 := (SimpObs Message' j so)) (i := j).
        intuition.
        simpl.
        intuition.
        intuition.
    - unfold s' in Hink.
      rewrite state_update_neq in Hink by intuition.
      apply cobs_single.
      exists k.
      intuition.
  Qed.
  
  Lemma cobs_message_existing_other_rt
    (s : vstate X)
    (Hpr : protocol_state_prop X s)
    (so : state)
    (i j target : index)
    (Hdif : i <> j)
    (s' := state_update IM_index s i (update_state (s i) so j))
    (Hfull : project (s i) j = project so j)
    (Hhave : In (SimpObs Message' j so) (cobs s j)) :
    incl (cobs_messages s target) (cobs_messages s' target).
  Proof.
    assert (Hsnb : forall (k : index), (s k) <> Bottom). {
      intros k.
      apply protocol_state_component_no_bottom. intuition.
    }
    
    assert (Hsonb : so <> Bottom). {
        apply in_cobs_and_message in Hhave.
        apply cobs_single in Hhave.
        destruct Hhave as [k Hhave].
        destruct Hhave as [_ Hhave].
        apply (@in_message_observations_nb index index_listing Hfinite) in Hhave.
        all : intuition.
    }
  
    unfold incl.
    intros.
    apply cobs_single in H.
    destruct H as [k H].
    destruct (decide (i = k)).
    - subst k.
      apply cobs_single.
      exists i.
      split;[apply in_listing|].
      destruct H as [_ H].
      apply (@old_incl_new index index_listing Hfinite) with (so := so) (i := j) in H.
      unfold s'.
      rewrite state_update_eq.
      intuition.
      split. apply Hsnb. intuition.
      intuition.
   - apply cobs_single.
     exists k.
     unfold s'.
     rewrite state_update_neq.
     all : intuition.
  Qed.
  
  Lemma cobs_message_existing_other_rt'
    (s : vstate X)
    (Hpr : protocol_state_prop X s)
    (so : state)
    (Hsonb : so <> Bottom)
    (i j target : index)
    (Hdif : i <> j)
    (s' := state_update IM_index s i (update_state (s i) so j))
    (Hfull : project (s i) j = project so j) :
    incl (cobs_messages s target) (cobs_messages s' target).
  Proof.
    assert (Hsnb : forall (k : index), (s k) <> Bottom). {
      intros k.
      apply protocol_state_component_no_bottom. intuition.
    }
  
    unfold incl.
    intros.
    apply cobs_single in H.
    destruct H as [k H].
    destruct (decide (i = k)).
    - subst k.
      apply cobs_single.
      exists i.
      split;[apply in_listing|].
      destruct H as [_ H].
      apply (@old_incl_new index index_listing Hfinite) with (so := so) (i := j) in H.
      unfold s'.
      rewrite state_update_eq.
      intuition.
      split. apply Hsnb. intuition.
      intuition.
   - apply cobs_single.
     exists k.
     unfold s'.
     rewrite state_update_neq.
     all : intuition.
  Qed.
  
  Lemma cobs_message_existing_other
    (s : vstate X)
    (Hpr : protocol_state_prop X s)
    (so : state)
    (i j target : index)
    (Hdif : i <> j)
    (s' := state_update IM_index s i (update_state (s i) so j))
    (Hfull : project (s i) j = project so j)
    (Hhave : In (SimpObs Message' j so) (cobs s j)) :
    set_eq (cobs_messages s target) (cobs_messages s' target).
  Proof.
    unfold set_eq.
    split.
    - apply cobs_message_existing_other_rt.
      all : intuition.
    - apply cobs_message_existing_other_lf.
      all : intuition.
  Qed.
  
  Lemma cobs_message_existing_same1
    (s : vstate X)
    (Hpr : protocol_state_prop X s)
    (b : bool)
    (i target : index)
    (Hdif : i <> target)
    (s' := state_update IM_index s i (update_consensus (update_state (s i) (s i) i) b)) :
    set_eq (cobs_messages s' target) (cobs_messages s target).
  Proof.
    assert (Hsnb : forall (k : index), (s k) <> Bottom). {
      intros k.
      apply protocol_state_component_no_bottom. intuition.
    }
    
    apply set_eq_extract_forall.
    intros e.
    split; intros H.
    - apply cobs_single in H.
      destruct H as [k H].
      destruct (decide (k = i)).
      + subst k.
        unfold s' in H.
        rewrite state_update_eq in H.
        rewrite <- cons_clean_message_obs in H.
        destruct H as [_ H].
        apply (@new_incl_rest_diff index index_listing Hfinite) in H.
        apply set_union_iff in H.
        destruct H; (apply cobs_single; exists i; split;[apply in_listing|intuition]).
        split; apply Hsnb.
        all :intuition.
      + unfold s' in H.
        rewrite state_update_neq in H.
        apply cobs_single.
        exists k. all : intuition.
    - apply cobs_single in H.
      destruct H as [k H].
      destruct (decide (k = i)).
      + subst k.
        destruct H as [_ H].
        apply (@old_incl_new index index_listing Hfinite) with (so := (s i)) (i := i) in H. 
        apply cobs_single.
        exists i.
        unfold s'.
        rewrite state_update_eq.
        rewrite cons_clean_message_obs with (b0 := b) in H.
        split;[apply in_listing|].
        intuition.
        split; apply Hsnb.
        intuition.
      + apply cobs_single.
        exists k.
        unfold s'.
        rewrite state_update_neq.
        all : intuition.
  Qed.
  
  Lemma cobs_message_existing_same2
    (s : vstate X)
    (Hpr : protocol_state_prop X s)
    (b : bool)
    (i : index)
    (s' := state_update IM_index s i (update_consensus (update_state (s i) (s i) i) b)) :
    set_eq (cobs_messages s' i) (set_union decide_eq (cobs_messages s i) [SimpObs Message' i (s i)]).
  Proof.
    assert (Hsnb : forall (k : index), (s k) <> Bottom). {
      intros k.
      apply protocol_state_component_no_bottom. intuition.
    }
  
    apply set_eq_extract_forall.
    intros e.
    split; intros H.
    - apply cobs_single in H.
      apply set_union_iff.
      destruct H as [k H].
      destruct (decide (i = k)).
      + subst k.
        unfold s' in H.
        rewrite state_update_eq in H by intuition.
        rewrite <- cons_clean_message_obs with (b0 := b) in H.
        destruct H as [_ H].
        apply (@new_incl_rest_same index index_listing Hfinite) in H.
        apply set_union_iff in H.
        destruct H as [H|H];[|right;intuition].
        apply set_union_iff in H.
        destruct H; left; apply cobs_single; exists i; (split;[apply in_listing|intuition]).
        split; apply Hsnb.
        intuition.
      + left.
        unfold s' in H.
        rewrite state_update_neq in H by intuition.
        apply cobs_single. exists k. intuition.
    - apply set_union_iff in H.
      destruct H as [H | H].
      + apply cobs_single in H.
        destruct H as [k [_ H]].
        destruct (decide (i = k)).
        * subst k. 
          apply (@old_incl_new index index_listing Hfinite) with (so := (s i)) (i := i) in H.
          apply cobs_single.
          exists i.
          unfold s'.
          rewrite state_update_eq.
          rewrite cons_clean_message_obs with (b0 := b) in H.
          split;[apply in_listing|].
          intuition.
          split; apply Hsnb.
          intuition.
        * apply cobs_single.
          exists k.
          unfold s'.
          rewrite state_update_neq.
          split;[apply in_listing|].
          all : intuition.
      + apply cobs_single.
        exists i.
        unfold s'.
        rewrite state_update_eq by intuition.
        destruct H;[|intuition].
        rewrite <- cons_clean_message_obs with (b0 := b).
        assert (project (update_state (s i) (s i) i) i = s i). {
          rewrite (@project_same index index_listing).
          intuition.
          intuition.
          apply Hsnb.
        }
        split;[apply in_listing|]. 
        apply refold_simp_lv_observations1.
        unfold update_state.
        destruct (s i) eqn : eq_si.
        specialize (Hsnb i). congruence.
        congruence.
        rewrite H0.
        apply Hsnb.
        rewrite H0.
        intuition.
  Qed.
  
  Lemma GE_existing_same
    (s : vstate X)
    (Hprs : protocol_state_prop X s)
    (b : bool)
    (i : index)
    (s' := state_update IM_index s i (update_consensus (update_state (s i) (s i) i) b)) :
    incl (GE s') (GE s).
  Proof.
    assert (Hsnb : forall (k : index), (s k) <> Bottom). {
      intros k.
      apply protocol_state_component_no_bottom. intuition.
    }
  
    unfold incl; intros v H.
    apply GE_direct in H as Hev.
    apply GE_direct.
    unfold cequiv_evidence in *.
    unfold equivocation_evidence in *.
    destruct Hev as [e1 [Hine1 [He1subj Hrem]]].
    destruct Hrem as [e2 [Hine2 [He2subj Hcomp]]].
    destruct e1 as [et1 ev1 es1] eqn : eq_e1. 
    destruct e2 as [et2 ev2 es2] eqn : eq_e2.
    apply hbo_cobs in Hine1. 
    apply hbo_cobs in Hine2.
    
    setoid_rewrite hbo_cobs.
    unfold get_simp_event_subject_some.
    
    assert (Hv : ev1 = v /\ ev2 = v). {
      rewrite <- He2subj in He1subj.
      unfold get_simp_event_subject_some in He1subj.
      inversion He1subj.
      unfold get_simp_event_subject_some in He2subj.
      inversion He2subj.
      intuition.
    }
    
    destruct Hv as [Hv1 Hv2].
    subst ev1. subst ev2.
    
    setoid_rewrite cobs_messages_states in Hine1.
    setoid_rewrite cobs_messages_states in Hine2.
    apply set_union_iff in Hine1.
    apply set_union_iff in Hine2.
    destruct Hine1 as [Hine1|Hine1].
    - apply in_cobs_states in Hine1 as Het1.
      simpl in Het1.
      subst et1.
      apply unique_state_observation in Hine1.
      simpl in Hine1.
      inversion Hine1.
      subst es1.
      destruct Hine2 as [Hine2|Hine2]. 
      + (* State and state : immediate contradiction *)
        apply in_cobs_states in Hine2 as Het2.
        simpl in Het2.
        subst et2.
        apply unique_state_observation in Hine2.
        simpl in Hine2.
        inversion Hine2.
        subst es2.
        unfold comparable in Hcomp.
        contradict Hcomp.
        left. intuition.
      + (* State and message *)
        apply in_cobs_messages in Hine2 as Het2.
        simpl in Het2.
        subst et2.
        simpl in Hine1, Hine2.
        destruct (decide (i = v)).
        * subst i.
          unfold s' in Hine2.
          setoid_rewrite cobs_message_existing_same2 in Hine2.
          2 : intuition.
          apply set_union_iff in Hine2.
          destruct Hine2 as [Hine2|Hine2].
          -- exists (SimpObs State' v (s v)).
             split.
             ++ simpl.
                apply in_cobs_states'.
                apply state_obs_present.
                apply in_listing.
             ++ split; [simpl;intuition|].
                exists e2.
                subst e2.
                split.
                ** simpl. apply in_cobs_messages'. intuition.
                ** split;[simpl;intuition|].
                   intros contra.
                   apply comparable_commutative in contra.
                   apply (@state_obs_stuff index v index_listing Hfinite) with (so := (s v)) (i := v) (b := b) in contra.
                   unfold s' in Hcomp.
                   apply comparable_commutative in contra.
                   rewrite state_update_eq in Hcomp.
                   intuition.
                   split;apply Hsnb.
                   intuition.
                   simpl. congruence.
                   simpl. congruence.
          -- destruct Hine2; [|intuition].
             inversion H0.
             subst es2.
             contradict Hcomp.
             unfold comparable.
             right. right.
             unfold simp_lv_event_lt.
             rewrite decide_True by intuition.
             unfold s'.
             rewrite state_update_eq.
             unfold state_lt'.
             rewrite history_disregards_cv.
             rewrite (@unfold_history_cons index index_listing Hfinite).
             simpl. left.
             rewrite (@project_same index index_listing Hfinite).
             intuition.
             apply Hsnb.
             rewrite (@project_same index index_listing Hfinite).
             apply Hsnb.
             apply Hsnb.
         * unfold s' in Hine2.
           setoid_rewrite cobs_message_existing_same1 in Hine2.
           2, 3 : intuition.
           exists (SimpObs State' v (s v)).
             split.
             ++ simpl.
                apply in_cobs_states'.
                apply state_obs_present.
                apply in_listing.
             ++ split; [simpl;intuition|].
                exists e2.
                subst e2.
                split.
                ** simpl. apply in_cobs_messages'. intuition.
                ** split;[simpl;intuition|].
                   intros contra.
                   apply comparable_commutative in contra.
                   unfold s' in Hcomp.
                   rewrite state_update_neq in Hcomp.
                   apply comparable_commutative in contra.
                   all : intuition.
     - apply in_cobs_messages in Hine1 as Het1.
       simpl in Het1. subst et1.
       simpl in Hine1, Hine2.
       destruct Hine2 as [Hine2|Hine2]. (* Copy paste below *)
       + apply in_cobs_states in Hine2 as Het2.
         simpl in Het2.
         subst et2.
         apply unique_state_observation in Hine2.
         apply in_cobs_messages in Hine1 as Het1.
         simpl in Het1.
         simpl in Hine1, Hine2.
        destruct (decide (i = v)).
        * subst i.
          unfold s' in Hine1.
          inversion Hine2.
          subst es2.
          setoid_rewrite cobs_message_existing_same2 in Hine1.
          2 : intuition.
          apply set_union_iff in Hine1.
          destruct Hine1 as [Hine1|Hine1].
          -- exists (SimpObs State' v (s v)).
             split.
             ++ simpl.
                apply in_cobs_states'.
                apply state_obs_present.
                apply in_listing.
             ++ split; [simpl;intuition|].
                exists e1.
                subst e1.
                split.
                ** simpl. apply in_cobs_messages'. intuition.
                ** split;[simpl;intuition|].
                   intros contra.
                   apply comparable_commutative in contra.
                   apply (@state_obs_stuff index v index_listing Hfinite) with (so := (s v)) (i := v) (b := b) in contra.
                   unfold s' in Hcomp.
                   rewrite state_update_eq in Hcomp.
                   intuition.
                   split;apply Hsnb.
                   intuition.
                   simpl. congruence.
                   simpl. congruence.
          -- destruct Hine1; [|intuition].
             inversion H0.
             subst es1.
             contradict Hcomp.
             unfold comparable.
             right. left.
             unfold simp_lv_event_lt.
             rewrite decide_True by intuition.
             unfold s'.
             rewrite state_update_eq.
             unfold state_lt'.
             rewrite history_disregards_cv.
             rewrite (@unfold_history_cons index index_listing Hfinite).
             simpl. left.
             rewrite (@project_same index index_listing Hfinite).
             intuition.
             apply Hsnb.
             rewrite (@project_same index index_listing Hfinite).
             apply Hsnb.
             apply Hsnb.
         * unfold s' in Hine1.
           setoid_rewrite cobs_message_existing_same1 in Hine1.
           2, 3 : intuition.
           exists (SimpObs State' v (s v)).
             split.
             ++ simpl.
                apply in_cobs_states'.
                apply state_obs_present.
                apply in_listing.
             ++ split; [simpl;intuition|].
                exists e1.
                subst e1.
                split.
                ** simpl. apply in_cobs_messages'. intuition.
                ** split;[simpl;intuition|].
                   intros contra.
                   inversion Hine2.
                   subst es2.
                   unfold s' in Hcomp.
                   rewrite state_update_neq in Hcomp.
                   apply comparable_commutative in contra.
                   all : intuition.
       + apply in_cobs_messages in Hine2 as Het2.
         simpl in Het2. subst et2.
         destruct (decide (i = v)).
         * subst v.
           unfold s' in Hine1, Hine2.
           setoid_rewrite cobs_message_existing_same2 in Hine1.
           2 : intuition.
           setoid_rewrite cobs_message_existing_same2 in Hine2.
           2 : intuition.
           apply set_union_iff in Hine1.
           apply set_union_iff in Hine2.
           
           destruct Hine1 as [Hine1|Hine1].
           -- destruct Hine2 as [Hine2|Hine2].
              ++ exists e1. subst e1. simpl.
                 split;[apply in_cobs_messages' in Hine1; intuition|].
                 split;[intuition|].
                 exists e2. subst e2. simpl.
                 split;[apply in_cobs_messages' in Hine2; intuition|].
                 split;[intuition|].
                 intuition.
              ++ destruct Hine2;[|intuition].
                 inversion H0. subst es2.
                 exists e1. subst e1. simpl.
                 split;[apply in_cobs_messages' in Hine1; intuition|].
                 split;[intuition|].
                 exists (SimpObs State' i (s i)). simpl.
                 split;[apply in_cobs_states';apply state_obs_present; intuition|].
                 apply in_listing.
                 split;[intuition|].
                 intros contra.
                 unfold comparable in contra.
                 destruct contra as [contra|contra];[congruence|].
                 destruct contra as [contra|contra].
                 ** unfold simp_lv_event_lt in contra.
                    rewrite decide_True in contra by intuition.
                    contradict Hcomp.
                    unfold comparable.
                    right. left.
                    unfold simp_lv_event_lt.
                    rewrite decide_True by intuition.
                    intuition.
                 ** unfold simp_lv_event_lt in contra.
                    rewrite decide_True in contra by intuition.
                    intuition.
           -- destruct Hine2 as [Hine2|Hine2].
              ++ destruct Hine1;[|intuition].
                 inversion H0. subst es1.
                 exists e2. subst e2. simpl.
                 split;[apply in_cobs_messages' in Hine2; intuition|].
                 split;[intuition|].
                 exists (SimpObs State' i (s i)). simpl.
                 split;[apply in_cobs_states';apply state_obs_present; intuition|].
                 apply in_listing.
                 split;[intuition|].
                 intros contra.
                 unfold comparable in contra.
                 destruct contra as [contra|contra];[congruence|].
                 destruct contra as [contra|contra].
                 ** unfold simp_lv_event_lt in contra.
                    rewrite decide_True in contra by intuition.
                    contradict Hcomp.
                    unfold comparable.
                    right. right.
                    unfold simp_lv_event_lt.
                    rewrite decide_True by intuition.
                    intuition.
                 ** unfold simp_lv_event_lt in contra.
                    rewrite decide_True in contra by intuition.
                    intuition.
              ++ destruct Hine1 as [Hine1|];[|intuition].
                 destruct Hine2 as [Hine2|];[|intuition].
                 inversion Hine1. inversion Hine2.
                 subst es1. subst es2.
                 contradict Hcomp.
                 unfold comparable.
                 left. intuition.
        * unfold s' in Hine1, Hine2.
          setoid_rewrite cobs_message_existing_same1 in Hine1.
          2, 3 : intuition.
          setoid_rewrite cobs_message_existing_same1 in Hine2.
          2, 3 : intuition.
          exists e1. subst e1. simpl.
          split;[apply in_cobs_messages';intuition|].
          split;[intuition|].
          exists e2. subst e2. simpl.
          split;[apply in_cobs_messages';intuition|].
          split;[intuition|].
          intuition.
  Qed.
  
  Lemma GE_existing_different
    (s : vstate X)
    (Hpr : protocol_state_prop X s)
    (so : state)
    (i j : index)
    (Hdif : i <> j)
    (s' := state_update IM_index s i (update_state (s i) so j))
    (Hfull : project (s i) j = project so j)
    (Hhave : In (SimpObs Message' j so) (cobs s j)) :
    incl (GE s') (GE s).
  Proof.
    assert (Hsnb : forall (k : index), (s k) <> Bottom). {
      intros k.
      apply protocol_state_component_no_bottom. intuition.
    }
    
    assert (Hsonb : so <> Bottom). {
        apply in_cobs_and_message in Hhave.
        apply cobs_single in Hhave.
        destruct Hhave as [k [_ Hhave]].
        apply (@in_message_observations_nb index index_listing Hfinite) in Hhave.
        all : intuition.
    }
  
    unfold incl; intros v H.
    apply GE_direct in H as Hev.
    apply GE_direct.
    unfold cequiv_evidence in *.
    unfold equivocation_evidence in *.
    destruct Hev as [e1 [Hine1 [He1subj Hrem]]].
    destruct Hrem as [e2 [Hine2 [He2subj Hcomp]]].
    destruct e1 as [et1 ev1 es1] eqn : eq_e1. 
    destruct e2 as [et2 ev2 es2] eqn : eq_e2.
    apply hbo_cobs in Hine1. 
    apply hbo_cobs in Hine2.
    
    setoid_rewrite hbo_cobs.
    unfold get_simp_event_subject_some.
    
    assert (Hv : ev1 = v /\ ev2 = v). {
      rewrite <- He2subj in He1subj.
      unfold get_simp_event_subject_some in He1subj.
      inversion He1subj.
      unfold get_simp_event_subject_some in He2subj.
      inversion He2subj.
      intuition.
    }
    
    destruct Hv as [Hv1 Hv2].
    subst ev1. subst ev2.
    
    setoid_rewrite cobs_messages_states in Hine1.
    setoid_rewrite cobs_messages_states in Hine2.
    apply set_union_iff in Hine1.
    apply set_union_iff in Hine2.
    
    destruct Hine1 as [Hine1|Hine1].
    - apply in_cobs_states in Hine1 as Het1.
      simpl in Het1. subst et1.
      apply unique_state_observation in Hine1. simpl in Hine1.
      inversion Hine1. subst es1.
      destruct Hine2 as [Hine2|Hine2].
      + apply in_cobs_states in Hine2 as Het2.
        simpl in Het2. subst et2.
        apply unique_state_observation in Hine2. simpl in Hine2.
        inversion Hine2. subst es2.
        contradict Hcomp.
        unfold comparable. left. intuition.
      + apply in_cobs_messages in Hine2 as Het2.
        simpl in Het2. subst et2. simpl in Hine2.
        unfold s' in Hine2.
        setoid_rewrite <- cobs_message_existing_other in Hine2.
        2, 3, 4, 5: intuition.
        exists e2. subst e2. simpl.
        split;[apply in_cobs_messages';intuition|].
        split;[intuition|].
        destruct (decide (i = v)).
        * exists (SimpObs State' v (s v)). simpl.
          subst v.
          split;[apply in_cobs_states'; apply state_obs_present|].
          apply in_listing.
          split;[intuition|].
          intros contra.
          apply (@state_obs_stuff_no_cons index i index_listing Hfinite) with (so := so) (i0 := j) in contra.
          unfold s' in Hcomp.
          apply comparable_commutative in contra.
          rewrite state_update_eq in Hcomp by intuition.
          intuition.
          split;[apply Hsnb|intuition].
          intuition.
          simpl. congruence.
          simpl. intuition.
        * unfold s' in *.
          rewrite state_update_neq in eq_e1.
          subst e1.
          rewrite state_update_neq in Hcomp.
          exists (SimpObs State' v (s v)).
          simpl.
          split;[apply in_cobs_states';apply state_obs_present|].
          apply in_listing.
          split;[simpl;intuition|].
          intros contra.
          apply comparable_commutative in contra.
          all : intuition.
    - apply in_cobs_messages in Hine1 as Het1.
      simpl in Het1. subst et1. simpl in Hine1.
      unfold s' in Hine1.
      setoid_rewrite <- cobs_message_existing_other in Hine1.
      2, 3, 4, 5: intuition.
      destruct Hine2 as [Hine2|Hine2].
      + exists e1. subst e1. simpl.
        split;[apply in_cobs_messages';intuition|].
        split;[intuition|].
        
        apply in_cobs_states in Hine2 as Het2.
        simpl in Het2. subst et2.
        apply unique_state_observation in Hine2. simpl in Hine2.
        inversion Hine2. subst es2.
        
        destruct (decide (i = v)).
        * exists (SimpObs State' v (s v)). simpl.
          subst v.
          split;[apply in_cobs_states'; apply state_obs_present|].
          apply in_listing.
          split;[intuition|].
          intros contra.
          apply (@state_obs_stuff_no_cons index i index_listing Hfinite) with (so := so) (i0 := j) in contra.
          unfold s' in Hcomp.
          rewrite state_update_eq in Hcomp by intuition.
          intuition.
          split;[apply Hsnb|intuition].
          intuition.
          simpl. congruence.
          simpl. intuition.
        * unfold s' in *.
          rewrite state_update_neq in eq_e2.
          subst e2.
          rewrite state_update_neq in Hcomp.
          exists (SimpObs State' v (s v)).
          simpl.
          split;[apply in_cobs_states';apply state_obs_present|].
          apply in_listing.
          split;[simpl;intuition|].
          intros contra.
          all : intuition.
      + apply in_cobs_messages in Hine2 as Het2.
        simpl in Het2. subst et2. simpl in Hine2.
        unfold s' in Hine2.
        setoid_rewrite <- cobs_message_existing_other in Hine2.
        2, 3, 4, 5: intuition.
        exists e1. subst e1. simpl.
        split;[apply in_cobs_messages';intuition|].
        split;[intuition|]. 
        exists e2. subst e2. simpl.
        split;[apply in_cobs_messages';intuition|].
        split;[intuition|]. 
        intuition.
  Qed.
  
  Lemma GE_existing_same_rev
    (s : vstate X)
    (Hprs : protocol_state_prop X s)
    (b : bool)
    (i : index)
    (Hhonest : ~ In i (GE s))
    (s' := state_update IM_index s i (update_consensus (update_state (s i) (s i) i) b)) :
    incl (GE s) (GE s').
  Proof.
    assert (Hsnb : forall (k : index), (s k) <> Bottom). {
      intros k.
      apply protocol_state_component_no_bottom. intuition.
    }
  
    unfold incl; intros v H.
    apply GE_direct in H as Hev.
    apply GE_direct.
    unfold cequiv_evidence in *.
    unfold equivocation_evidence in *.
    destruct Hev as [e1 [Hine1 [He1subj Hrem]]].
    destruct Hrem as [e2 [Hine2 [He2subj Hcomp]]].
    destruct e1 as [et1 ev1 es1] eqn : eq_e1. 
    destruct e2 as [et2 ev2 es2] eqn : eq_e2.
    apply hbo_cobs in Hine1. 
    apply hbo_cobs in Hine2.
    
    setoid_rewrite hbo_cobs.
    unfold get_simp_event_subject_some.
    
    assert (Hv : ev1 = v /\ ev2 = v). {
      rewrite <- He2subj in He1subj.
      unfold get_simp_event_subject_some in He1subj.
      inversion He1subj.
      unfold get_simp_event_subject_some in He2subj.
      inversion He2subj.
      intuition.
    }
    
    destruct Hv as [Hv1 Hv2].
    subst ev1. subst ev2.
    
    setoid_rewrite cobs_messages_states in Hine1.
    setoid_rewrite cobs_messages_states in Hine2.
    apply set_union_iff in Hine1.
    apply set_union_iff in Hine2.
    
    destruct Hine1 as [Hine1|Hine1].
    - apply in_cobs_states in Hine1 as Het1.
      simpl in Het1.
      subst et1.
      apply unique_state_observation in Hine1.
      simpl in Hine1.
      inversion Hine1.
      subst es1.
      destruct Hine2 as [Hine2|Hine2]. 
      + (* State and state : immediate contradiction *)
        apply in_cobs_states in Hine2 as Het2.
        simpl in Het2.
        subst et2.
        apply unique_state_observation in Hine2.
        simpl in Hine2.
        inversion Hine2.
        subst es2.
        unfold comparable in Hcomp.
        contradict Hcomp.
        left. intuition.
      + apply in_cobs_messages in Hine2 as Het2.
        simpl in Het2.
        subst et2.
        destruct (decide (i = v)).
        * subst v.
          intuition.
        * exists (SimpObs State' v (s' v)).
          split;[apply in_cobs_states';apply state_obs_present|].
          apply in_listing.
          split;[intuition|].
          exists e2. subst e2.
          simpl in *.
          unfold s'.
          rewrite state_update_neq by intuition.
          split.
          -- apply in_cobs_messages'.
             setoid_rewrite cobs_message_existing_same1.
             all : intuition.
          -- split;intuition.
     - apply in_cobs_messages in Hine1 as Het1.
       simpl in Het1. subst et1.
       destruct Hine2 as [Hine2|Hine2].
       + apply in_cobs_states in Hine2 as Het2.
         simpl in Het2. subst et2.
         apply unique_state_observation in Hine2.
         simpl in Hine2.
         inversion Hine2. subst es2.
         destruct (decide (i = v)).
        * subst v.
          intuition.
        * exists (SimpObs State' v (s' v)).
          split;[apply in_cobs_states';apply state_obs_present|].
          apply in_listing.
          split;[intuition|].
          exists e1. subst e1.
          simpl in *.
          unfold s'.
          rewrite state_update_neq by intuition.
          split.
          -- apply in_cobs_messages'.
             setoid_rewrite cobs_message_existing_same1.
             all : intuition.
          -- split;[intuition|].
             intros contra.
             apply comparable_commutative in contra.
             intuition.
       + apply in_cobs_messages in Hine2 as Het2.
         simpl in Het2.
         subst et2.
         
         destruct (decide (i = v)); [subst v;intuition|].
         
         exists e1. subst e1. simpl in *.
         split.
         * apply in_cobs_messages'.
           unfold s'.
           setoid_rewrite cobs_message_existing_same1.
           all : intuition.
         * split;[intuition|].
           exists e2. subst e2. simpl in *.
           split.
           -- apply in_cobs_messages'.
              unfold s'.
              setoid_rewrite cobs_message_existing_same1.
              all : intuition.
           -- intuition.
  Qed.
  
  Lemma GE_existing_different_rev
    (s : vstate X)
    (Hpr : protocol_state_prop X s)
    (so : state)
    (i j : index)
    (Hdif : i <> j)
    (s' := state_update IM_index s i (update_state (s i) so j))
    (Hfull : project (s i) j = project so j)
    (Hhave : In (SimpObs Message' j so) (cobs s j)) :
    incl (GE s) (GE s').
  Proof.
    assert (Hsnb : forall (k : index), (s k) <> Bottom). {
      intros k.
      apply protocol_state_component_no_bottom. intuition.
    }
    
    assert (Hsonb : so <> Bottom). {
        apply in_cobs_and_message in Hhave.
        apply cobs_single in Hhave.
        destruct Hhave as [k [_ Hhave]].
        apply (@in_message_observations_nb index index_listing Hfinite) in Hhave.
        all : intuition.
    }
  
    unfold incl; intros v H.
    apply GE_direct in H as Hev.
    apply GE_direct.
    unfold cequiv_evidence in *.
    unfold equivocation_evidence in *.
    destruct Hev as [e1 [Hine1 [He1subj Hrem]]].
    destruct Hrem as [e2 [Hine2 [He2subj Hcomp]]].
    destruct e1 as [et1 ev1 es1] eqn : eq_e1. 
    destruct e2 as [et2 ev2 es2] eqn : eq_e2.
    apply hbo_cobs in Hine1. 
    apply hbo_cobs in Hine2.
    
    setoid_rewrite hbo_cobs.
    unfold get_simp_event_subject_some.
    
    assert (Hv : ev1 = v /\ ev2 = v). {
      rewrite <- He2subj in He1subj.
      unfold get_simp_event_subject_some in He1subj.
      inversion He1subj.
      unfold get_simp_event_subject_some in He2subj.
      inversion He2subj.
      intuition.
    }
    
    destruct Hv as [Hv1 Hv2].
    subst ev1. subst ev2.
    
    setoid_rewrite cobs_messages_states in Hine1.
    setoid_rewrite cobs_messages_states in Hine2.
    apply set_union_iff in Hine1.
    apply set_union_iff in Hine2.
    
    destruct Hine1 as [Hine1|Hine1].
    - apply in_cobs_states in Hine1 as Het1.
      simpl in Het1. subst et1.
      apply unique_state_observation in Hine1. simpl in Hine1.
      inversion Hine1. subst es1.
      destruct Hine2 as [Hine2|Hine2].
      + apply in_cobs_states in Hine2 as Het2.
        simpl in Het2. subst et2.
        apply unique_state_observation in Hine2. simpl in Hine2.
        inversion Hine2. subst es2.
        contradict Hcomp.
        unfold comparable. left. intuition.
      + apply in_cobs_messages in Hine2 as Het2.
        simpl in Het2. subst et2. simpl in Hine2.
        
        exists (SimpObs State' v (s' v)). simpl.
        split;[apply in_cobs_states';apply state_obs_present|].
        apply in_listing.
        split;[intuition|].
        exists e2. subst e2. simpl in *.
        split.
        * apply in_cobs_messages'.
          unfold s'.
          setoid_rewrite <- cobs_message_existing_other.
          all :intuition.
        * split;[intuition|].
          unfold s'.
          destruct (decide (i = v)).
          -- subst v.
             rewrite state_update_eq.
             intros contra.
             unfold comparable in contra.
             destruct contra as [contra|contra];[congruence|].
             unfold simp_lv_event_lt in contra.
             rewrite decide_True in contra by intuition.
             destruct contra as [contra|contra];[intuition|].
             rewrite decide_True in contra by intuition.
             unfold state_lt' in contra.
             
             contradict Hcomp.
             unfold comparable.
             right.
             right.
             unfold simp_lv_event_lt.
             rewrite decide_True by intuition.
             unfold state_lt'.
             
             assert (get_history (update_state (s i) so j) i = get_history (s i) i). {
              apply (@eq_history_eq_project index index_listing Hfinite).
              rewrite (@project_different index index_listing Hfinite).
              intuition.
              intuition.
              apply Hsnb.
             } 
             
             rewrite <- H0.
             intuition.
          -- rewrite state_update_neq by intuition.
             intuition.
    - apply in_cobs_messages in Hine1 as Het1.
      simpl in Het1. subst et1. simpl in Hine1.
      
      destruct Hine2 as [Hine2|Hine2].
      + apply in_cobs_states in Hine2 as Het2.
        simpl in Het2. subst et2.
        apply unique_state_observation in Hine2. simpl in Hine2.
        inversion Hine2. subst es2.
        
        exists (SimpObs State' v (s' v)). simpl.
        split;[apply in_cobs_states';apply state_obs_present|].
        apply in_listing.
        split;[intuition|].
        exists e1. subst e1. simpl in *.
        split.
        * apply in_cobs_messages'.
          unfold s'.
          setoid_rewrite <- cobs_message_existing_other.
          all :intuition.
        * split;[intuition|].
          unfold s'.
          destruct (decide (i = v)).
          -- subst v.
             rewrite state_update_eq.
             intros contra.
             unfold comparable in contra.
             destruct contra as [contra|contra];[congruence|].
             unfold simp_lv_event_lt in contra.
             rewrite decide_True in contra by intuition.
             destruct contra as [contra|contra];[intuition|].
             rewrite decide_True in contra by intuition.
             unfold state_lt' in contra.
             
             contradict Hcomp.
             unfold comparable.
             right.
             left.
             unfold simp_lv_event_lt.
             rewrite decide_True by intuition.
             unfold state_lt'.
             
             assert (get_history (update_state (s i) so j) i = get_history (s i) i). {
              apply (@eq_history_eq_project index index_listing Hfinite).
              rewrite (@project_different index index_listing Hfinite).
              intuition.
              intuition.
              apply Hsnb.
             } 
             
             rewrite <- H0.
             intuition.
          -- rewrite state_update_neq by intuition.
             intros contra.
             apply comparable_commutative in contra.
             intuition.
      + apply in_cobs_messages in Hine2 as Het2.
        simpl in Het2. subst et2. simpl in Hine2.
        
        exists e1. subst e1. simpl in *.
        split.
        * apply in_cobs_messages'.
          unfold s'.
          setoid_rewrite <- cobs_message_existing_other.
          all :intuition.
        * split;[intuition|].
          exists e2. subst e2. simpl in *.
          split.
          -- apply in_cobs_messages'.
             unfold s'.
             setoid_rewrite <- cobs_message_existing_other. 
             all : intuition.
          -- split;[intuition|].
             intuition.
  Qed.
  
  Lemma in_future_message_obs
    (s s' : vstate X)
    (Hprs : protocol_state_prop X s)
    (target : index)
    (Hf : in_futures X s s') 
    (e : simp_lv_event)
    (Hin : In e (cobs_messages s target)) :
    In e (cobs_messages s' target).
  Proof.
    unfold in_futures in Hf.
    destruct Hf as [tr [Hpr Hlst]].
    generalize dependent s.
    induction tr.
    - intros. simpl in *. rewrite <- Hlst. intuition.
    - intros.
      inversion Hpr.
      rewrite map_cons in Hlst.
      rewrite unroll_last in Hlst.
      assert (Hproto' := H3).
      destruct H3 as [Hproto Htrans].
      unfold transition in Htrans.
      simpl in Htrans.
      destruct l. simpl in *.
      unfold constrained_composite_valid in Hproto.
      unfold free_composite_valid in Hproto.
      unfold vvalid in Hproto. unfold valid in Hproto. simpl in *.
      unfold vtransition in Htrans.
      unfold transition in Htrans. simpl in Htrans.
      destruct a. simpl in *.
      inversion H.
      specialize (IHtr s0).
      spec IHtr. {
        apply protocol_transition_destination in Hproto'.
        intuition.
      }
      spec IHtr. intuition.
      spec IHtr. {
        rewrite H6.
        intuition.
      }
      apply IHtr.
      destruct v eqn : eq_v.
      + subst v.
        inversion Htrans.
        destruct (decide (x = target)).
        * subst x.
          setoid_rewrite cobs_message_existing_same2.
          apply set_union_iff.
          left. intuition.
          intuition.
        * setoid_rewrite cobs_message_existing_same1.
          all : intuition.
      + inversion Htrans.
        destruct iom eqn : eq_iom;[|intuition].
        inversion H8.
        specialize (cobs_message_existing_other_rt' s Hprs (snd m)) as Hex.
        spec Hex. intuition.
        specialize (Hex x (fst m) target).
        spec Hex. intuition. simpl in Hex.
        spec Hex. intuition.
        unfold incl in Hex.
        specialize (Hex e).
        apply Hex.
        intuition.
  Qed. 
  
  Lemma ep_plan 
    (s : vstate X)
    (Hpr : protocol_state_prop X s)
    (a : vplan X)
    (Hpr_a : finite_protocol_plan_from X s a)
    (Hgood : forall (ai : vplan_item X), In ai a ->
      (projT2 (label_a ai)) = receive /\
      exists (so : state) (from : index),
      input_a ai = Some (from, so) /\
      In (SimpObs Message' from so) (cobs_messages s from)) :
    let res := snd (apply_plan X s a) in
    set_eq (GE s) (GE res).
  Proof.
    simpl.
    induction a using rev_ind.
    - simpl in *. intuition.
    - assert (Hpr_a' := Hpr_a).
      apply finite_protocol_plan_from_app_iff in Hpr_a.
      spec IHa. intuition.
        
      rewrite apply_plan_app.
      destruct (apply_plan X s a) as (tr_long, res_long) eqn : eq_long.
        destruct (apply_plan X res_long [x]) as (tr_short, res_short) eqn : eq_short.
        
        assert (res_long = snd (apply_plan X s a)) by (rewrite eq_long; intuition).
        assert (res_short = snd (apply_plan X res_long [x])) by (rewrite eq_short; intuition).
        
        simpl.
        apply set_eq_tran with (s2 := GE res_long).
        spec IHa. {
          intros ai Hai.
          specialize (Hgood ai).
          spec Hgood. apply in_app_iff. left. intuition.
          intuition.
        }
        simpl in IHa.
        intuition.
        rewrite H0.
        unfold apply_plan. simpl.
        
        specialize (Hgood x).
        spec Hgood. {
          apply in_app_iff. right. intuition.
        }
        
        destruct x. simpl in *.
        
        destruct (vtransition X label_a (res_long, input_a)) eqn : eq_trans.
        unfold vtransition in eq_trans.
        unfold transition in eq_trans.
        simpl in eq_trans.
        unfold vtransition in eq_trans.
        unfold transition in eq_trans.
        simpl in eq_trans.
        destruct label_a. simpl in *.
        destruct Hgood as [Hv Hgood].
        destruct Hpr_a as [Hpr_a2 Hpr_a].
        apply finite_protocol_plan_from_one in Hpr_a. simpl in Hpr_a.
        move Hpr_a at bottom.
        destruct Hpr_a as [Hpr_a _].
        unfold protocol_valid in Hpr_a.
        unfold valid in Hpr_a.
        simpl in Hpr_a.
        unfold constrained_composite_valid in Hpr_a.
        unfold free_composite_valid in Hpr_a.
        unfold vvalid in Hpr_a.
        unfold valid in Hpr_a. simpl in Hpr_a.
        subst v.
        destruct input_a eqn : eq_input.
        + destruct Hgood as [so [from [Heqm Hinso]]].
          inversion Heqm.
          subst m. simpl in *.
          unfold set_eq.
          inversion eq_trans. clear H3.
          assert (In (SimpObs Message' from so) (cobs res_long from)). {
            specialize (in_future_message_obs s res_long Hpr from) as Hf.
            spec Hf. {
              unfold in_futures.
              exists (fst (apply_plan X s a)).
              split.
              - assert (finite_protocol_plan_from X s a). {
                  intuition. 
                }
                unfold finite_protocol_plan_from in H1.
                intuition.
              - rewrite H.
                apply apply_plan_last.
                
            }
            specialize (Hf (SimpObs Message' from so)).
            apply in_cobs_messages'.
            apply Hf.
            intuition.
          }

          split.
          * apply GE_existing_different_rev.
            all : intuition.
          * apply GE_existing_different.
            all : intuition.
        + intuition. 
  Qed.
  
  Lemma GH_NoDup  
    (s : vstate X) :
    NoDup (GH s).
  Proof.
    unfold GH.
    apply NoDup_filter.
    apply (proj1 Hfinite).
  Qed.
  
  Definition others (i : index) (s : vstate X) := 
    set_remove idec i (GH s).
      
  Lemma NoDup_others
    (i : index) (s : vstate X) :
    NoDup (others i s).
  Proof.
    unfold others.
    apply set_remove_nodup.
    apply GH_NoDup.
  Qed.
    
  Lemma others_correct
    (i : index)
    (s : vstate X) :
     ~ In i (others i s).
  Proof.
    unfold others.
    intros contra.
    apply set_remove_2 in contra.
    intuition.
    apply GH_NoDup.
  Qed.
    
  Definition feasible_update_value (s : (@state index index_listing)) (who : index) : bool :=
    match s with
    | Bottom => false
    | Something c is => match (@equivocation_aware_estimatorb index who index_listing Hfinite decide_eq _ _ s false) with
                        | true => false
                        | false => true
                        end
    end.
  
  Definition not_all_equivocating
    (s : (@state index index_listing))
    (who : index) 
    : Prop
    := @no_equivocating_decisions index index_listing idec s 
      (@equivocating_validators (@state index index_listing) index Mindex Rindex (Hbasic who) s) <> [].
  
  Definition no_component_fully_equivocating
    (s : vstate X)
    (li : list index) : Prop
    := forall (i : index), In i li -> not_all_equivocating (s i) i.
  
  Lemma feasible_update_value_correct 
    (s : (@state index index_listing))
    (who : index)
    (Hne : not_all_equivocating s who) :
    (@equivocation_aware_estimator index who index_listing Hfinite decide_eq _ _ s (feasible_update_value s who)).
  Proof.
   destruct (feasible_update_value s who) eqn : eq_fv.
   - unfold feasible_update_value in eq_fv.
     destruct s.
     discriminate eq_fv.
     destruct (equivocation_aware_estimatorb (Something b is)) eqn : eq_ewb.
     discriminate eq_fv.
     apply ea_estimator_total in eq_ewb.
     assumption.
     assumption.
   - unfold feasible_update_value in eq_fv.
     destruct s.
     simpl.
     apply I.
     destruct (equivocation_aware_estimatorb (Something b is) false) eqn : eq_ewb.
     unfold equivocation_aware_estimator. 
     assumption.
     discriminate eq_fv.
  Qed.
  
  Definition feasible_update_single (s : (@state index index_listing)) (who : index) : plan_item :=
    let cv := feasible_update_value s who in
    let res := @list_transition index who _ _ (update cv) (s, None) in
    @Build_plan_item _ (type (IM_index who)) (update cv) None.
  
  Definition feasible_update_composite (s : vstate X) (who : index) : vplan_item X :=
    lift_to_composite_plan_item IM_index who (feasible_update_single (s who) who).
  
  Lemma feasible_update_protocol 
    (s : vstate X)
    (Hprs : protocol_state_prop _ s)
    (who : index) 
    (Hne : not_all_equivocating (s who) who)
    (item := feasible_update_composite s who) :
    protocol_valid X (label_a item) (s, input_a item).
  Proof.
    unfold protocol_transition.
    repeat split.
    assumption.
    simpl.
    apply option_protocol_message_None.
    apply feasible_update_value_correct with (s := s who) (who := who).
    assumption.
  Qed.
  
  Definition chain_updates (li : list index) (s : vstate X) : vplan X :=
    List.map (feasible_update_composite s) li.
  
  Lemma chain_updates_projections_out 
    (s : vstate X)
    (li : list index)
    (i : index)
    (Hi : ~In i li)
    (s' := snd (apply_plan X s (chain_updates li s))) :
    (s' i) = (s i).
  Proof.
    apply irrelevant_components.
    intros contra.
    apply in_map_iff in contra.
    destruct contra as [x [Heqproj contra]].
    apply in_map_iff in contra.
    destruct contra as [a [Heqlabel contra]].
    unfold chain_updates in contra.
    apply in_map_iff in contra.
    destruct contra as [j [Hfease Hj]].
    rewrite <- Heqlabel in Heqproj.
    rewrite <- Hfease in Heqproj.
    unfold feasible_update_composite in Heqproj.
    simpl in Heqproj.
    rewrite Heqproj in Hj.
    intuition.
  Qed.
  
  Lemma chain_updates_protocol
    (s : vstate X)
    (Hprs : protocol_state_prop _ s)
    (li : list index)
    (Hnodup : NoDup li)
    (Hhonest : incl li (GH s))
    (Hnf : no_component_fully_equivocating s li) :
    let res := snd (apply_plan X s (chain_updates li s)) in
    finite_protocol_plan_from _ s (chain_updates li s) /\
    (forall (i : index), In i li -> project (res i) i = s i) /\ 
    set_eq (GE res) (GE s).
  Proof.
    unfold no_component_fully_equivocating in Hnf.
    generalize dependent s.
    induction li as [|i li].
    - intros.
      simpl.
      split.
      + apply finite_ptrace_empty.
        assumption.
      + split; [intuition|].
        simpl in res.
        unfold res. intuition.
    - intros.
      remember (feasible_update_composite s i) as a.
      specialize (Hnf i) as Hnfi.
      spec Hnfi. {
        intuition.
      }
      remember (vtransition X (label_a a) (s, input_a a)) as res_a.
      
      assert (protocol_transition X (label_a a) (s, input_a a) res_a). {
        rewrite Heqa.
        unfold protocol_transition.
        split.
        - apply feasible_update_protocol.
          all : assumption.
        - rewrite Heqres_a.
          unfold vtransition.
          rewrite Heqa.
          reflexivity.
      }
       
      unfold chain_updates.
      replace (i :: li) with ([i] ++ li) by intuition.
      rewrite map_app.
      
      remember (snd (apply_plan X s (map (feasible_update_composite s) [i]))) as s'.
      
      apply NoDup_cons_iff in Hnodup.
      destruct Hnodup as [Hnoa Hnoli].
      specialize (IHli Hnoli s').
      
      spec IHli. {
        rewrite Heqs'.
        apply apply_plan_last_protocol.
        assumption.
        simpl.
        apply finite_protocol_plan_from_one.
        unfold protocol_transition in H.
        rewrite <- Heqa.
        unfold protocol_transition.
        intuition.
      }
      
      assert (Hindif : forall (i : index), In i li -> s' i = s i). {
        intros.
        rewrite Heqs'.
        apply irrelevant_components_one.
        simpl.
        intros contra.
        rewrite contra in H0.
        intuition.
      }
      
      assert (HGEs' : set_eq (GE s') (GE s)). {
        unfold set_eq.
        simpl in Heqs'.
        rewrite Heqs'.
        split.
        - apply GE_existing_same.
          intuition.
        - apply GE_existing_same_rev.
          intuition.
          unfold GE.
          rewrite <- wH_wE'.
          apply Hhonest. intuition.
      }
      
      spec IHli. {
        unfold incl in *.
        intros idx Hidx.
        unfold GE.
        apply wH_wE'.
        specialize (Hhonest idx).
        setoid_rewrite HGEs'.
        apply wH_wE'.
        apply Hhonest.
        intuition.
      }
    
      spec IHli. {
        intros.
        destruct (decide (i1 = i)).
        - rewrite e in H0; intuition.
        - specialize (Hindif i1 H0).
          rewrite Hindif.
          apply Hnf.
          simpl.
          right; intuition.
      }
      
      assert (Hchain : (map (feasible_update_composite s) li) = (map (feasible_update_composite s') li)). {
        apply map_ext_in; intros j Hjli.
        unfold feasible_update_composite.
        replace (s' j) with (s j). 
        reflexivity.
        symmetry.
        apply Hindif.
        intuition.
      }
      
      simpl in IHli.
      
      split.
      + apply finite_protocol_plan_from_app_iff.
        split.
        * unfold feasible_update_composite; simpl.
          apply finite_protocol_plan_from_one.
          unfold protocol_transition.
          split.
          apply feasible_update_protocol.
          all : intuition.
        * rewrite Heqs' in IHli at 1.
          unfold chain_updates in IHli.
          rewrite Hchain; intuition.
      +
        unfold res; simpl.
        replace (feasible_update_composite s i :: chain_updates li s) with 
                ([feasible_update_composite s i] ++ chain_updates li s) by intuition.
        rewrite apply_plan_app.
        destruct (apply_plan X s [feasible_update_composite s i]) as (tr_short, res_short) eqn : eq_short.
        assert (res_short = snd (apply_plan X s [feasible_update_composite s i])) by (rewrite eq_short; intuition).
        destruct (apply_plan X res_short (chain_updates li s)) as (tr_long, res_long) eqn : eq_long.
        assert (res_long = snd (apply_plan X res_short (chain_updates li s))) by (rewrite eq_long; intuition).

        assert (s' = res_short). {
          rewrite Heqs'.
          rewrite H0.
          simpl.
          reflexivity.
        }
        
        assert (Hsame : res_long i = res_short i). {
          rewrite H1.
          unfold chain_updates.
          rewrite Hchain.
          rewrite H2.
          apply chain_updates_projections_out.
          assumption.
        }
        
        split.
        intros j Hjli.
        * destruct (decide (j = i)).
          -- simpl.
             rewrite e.
             rewrite Hsame.
             rewrite H0.
             unfold apply_plan.
             unfold apply_plan_folder; simpl. 
             rewrite state_update_eq.
             rewrite <- update_consensus_clean with (value := (feasible_update_value (s i) i)).
             rewrite (@project_same index index_listing).
             reflexivity.
             apply Hfinite.
             apply protocol_state_component_no_bottom.
             assumption.
          -- destruct IHli as [_ [IHli _]].
             specialize (IHli j).
             spec_save IHli. {
               destruct Hjli.
               simpl in H0.
               simpl in H3.
               intuition.
               assumption.
             }
             specialize (Hindif j H3).
             rewrite <- Hindif.
             rewrite <- IHli.
             simpl.
             f_equal.
             unfold chain_updates.
             rewrite <- Hchain.
             rewrite H2.
             rewrite H1.
             unfold chain_updates.
             reflexivity.
        * simpl.
          assert (Hge_short : set_eq (GE res_short) (GE s)). {
            remember (update_consensus (update_state (s i) (s i) i) (feasible_update_value (s i) i)) as new_si.
            remember (state_update IM_index s i new_si) as new_s.
            assert (Hu: res_short = new_s). {
              rewrite H0.
              rewrite Heqnew_s.
              unfold apply_plan.
              unfold feasible_update_composite; simpl.
              rewrite Heqnew_si.
              reflexivity.
            }
            specialize (GE_existing_same s Hprs (feasible_update_value (s i) i) i) as Hexist.
            specialize (GE_existing_same_rev s Hprs (feasible_update_value (s i) i) i) as Hexist'.
            
            spec Hexist'. {
              unfold GE.
              apply wH_wE'.
              intuition.
            }
            simpl in Hexist, Hexist'.
            
            rewrite Hu.
            rewrite Heqnew_s.
            rewrite Heqnew_si.
            unfold set_eq.
            split.
            - apply Hexist.
            - apply Hexist'. 
          }
          
          assert (Hge_long : set_eq (GE res_long) (GE res_short)). {
            destruct IHli as [_ [_ IHli]].
            unfold chain_updates in IHli.
            rewrite <- Hchain in IHli.
            rewrite H2 in IHli.
            unfold chain_updates in H1.
            rewrite H1.
            apply IHli.
          }
          
          apply set_eq_tran with (s2 := (GE res_short)).
          assumption.
          assumption.
  Qed.
  
  Definition send_phase_plan (s : vstate X) : vplan X :=
    chain_updates (GH s) s.
 
  Definition send_phase (s : vstate X) : list (vtransition_item X) * vstate X :=
    apply_plan X s (send_phase_plan s).
  
  Definition send_phase_result 
    (s : vstate X) :=
    snd (send_phase s).
 
  Definition send_phase_transitions
    (s : vstate X) :=
    fst (send_phase s).
  
  Lemma send_phase_protocol
    (s : vstate X)
    (Hprs : protocol_state_prop X s)
    (Hnf : no_component_fully_equivocating s (GH s)) :
    finite_protocol_plan_from X s (send_phase_plan s).
  Proof.
    unfold send_phase_plan.
    specialize (chain_updates_protocol s Hprs (GH s) (GH_NoDup s)) as Hchain.
    spec Hchain. intuition.
    specialize (Hchain Hnf). simpl in Hchain.
    unfold send_phase_result.
    destruct Hchain as [Hchain1 [Hchain2 Hchain3]].
    intuition.
  Qed.
  
  Corollary send_phase_result_protocol
    (s : vstate X)
    (Hprs : protocol_state_prop X s)
    (Hnf : no_component_fully_equivocating s (GH s)) 
    (res_send := send_phase_result s) :
    protocol_state_prop X res_send.
  Proof. 
    apply apply_plan_last_protocol.
    intuition.
    apply send_phase_protocol.
    all : intuition.
  Qed.
  
  Lemma send_phase_GE
    (s : vstate X)
    (Hprs : protocol_state_prop X s)
    (Hnf : no_component_fully_equivocating s (GH s)) :
    set_eq (GE (send_phase_result s)) (GE s).
  Proof.
    unfold send_phase_plan.
    specialize (chain_updates_protocol s Hprs (GH s) (GH_NoDup s)) as Hchain.
    spec Hchain. intuition.
    specialize (Hchain Hnf). simpl in Hchain.
    unfold send_phase_result.
    destruct Hchain as [Hchain1 [Hchain2 Hchain3]].
    unfold send_phase. intuition.
  Qed.
  
  Lemma send_phase_future 
    (s : vstate X)
    (Hnf : no_component_fully_equivocating s (GH s))
    (Hspr : protocol_state_prop _ s) :
    in_futures _ s (send_phase_result s).
  Proof.
    unfold in_futures.
    exists (send_phase_transitions s).
    split.
    apply send_phase_protocol.
    assumption.
    assumption.
    unfold send_phase_transitions.
    unfold send_phase_result.
    apply apply_plan_last.
  Qed.
  
  Remark send_phase_result_projections 
    (s : vstate X)
    (Hprss : protocol_state_prop _ s)
    (Hnf : no_component_fully_equivocating s (GH s))
    (i : index)
    (Hin : In i (GH s))
    (s' := send_phase_result s) :
    project (s' i) i = (s i).
  Proof.
    apply chain_updates_protocol.
    intuition.
    apply GH_NoDup.
    all : intuition.
  Qed.
  
  Remark non_self_projections_same_after_send_phase
    (s : vstate X)
    (Hpr : protocol_state_prop X s)
    (Hnf : no_component_fully_equivocating s (GH s))
    (res_send := send_phase_result s) :
    forall (i j : index), i <> j -> project (res_send i) j = project (s i) j.
  Proof.
    intros.
    specialize (non_self_projections_same_after_sends s Hpr (send_phase_plan s)) as Hsame.
    spec Hsame. {
      apply send_phase_protocol. 
      intuition.
      intuition.
    }
    spec Hsame. {
      intros.
      apply in_map_iff in H0.
      destruct H0 as [k [Heq Hink]].
      unfold feasible_update_composite in Heq.
      unfold feasible_update_single in Heq.
      simpl in Heq.
      rewrite <- Heq.
      simpl.
      exists (feasible_update_value (s k) k).
      intuition.
    }
    specialize (Hsame i j H).
    intuition.
  Qed.
  
  Definition lift_to_receive_item (to from : index) (s : state): vplan_item (IM_index to) :=
    @Build_plan_item _ (type (IM_index to)) receive (Some (from, s)).
  
  Definition sync_plan (to from : index) (ls : list state) : (vplan X) := 
    let tmp := List.map (lift_to_receive_item to from) ls in
    List.map (lift_to_composite_plan_item IM_index to) tmp.
  
  Definition sync (s : vstate X) (s': state) (to from : index) : option (vplan X) :=
    let history_s := get_history (s to) from in
    let history_s' := get_history s' from in
    let rem_states := complete_suffix history_s' history_s in
    match rem_states with
    | None => None
    | Some ss => let rem_plan := sync_plan to from (rev ss) in
                 Some rem_plan
    end.
   
  Lemma one_sender_receive_protocol
    (s s': vstate X)
    (Hpr : protocol_state_prop X s)
    (Hpr' : protocol_state_prop X s')
    (to inter from : index)
    (Hhist : get_history (s inter) from = get_history (s' inter) from) 
    (Hdif : to <> from)
    (a : vplan X)
    (Hsync : sync s (s' inter) to from = Some a) :
    let res := snd (apply_plan X s a) in
    finite_protocol_plan_from X s a /\
    (project (res to) from = project (s' inter) from) /\ set_eq (GE res) (GE s).
   Proof. 
    generalize dependent s.
    induction a.
    - intros. simpl in *.
      unfold finite_protocol_plan_from. simpl.
      repeat split.
        + apply finite_ptrace_empty.
          assumption. 
        + unfold res.
          unfold sync in Hsync.
          destruct (complete_suffix (get_history (s' inter) from) (get_history (s to) from)) eqn : eq_cs.
          2 : discriminate Hsync.
          apply complete_suffix_correct in eq_cs.
          assert (l = []). {
            inversion Hsync.
            assert (length l = 0). {
              assert (length (sync_plan to from (rev l)) = 0). {
                apply length_zero_iff_nil. assumption.
              }
              unfold sync_plan in H.
              rewrite map_length in H.
              rewrite map_length in H.
              rewrite rev_length in H.
              assumption.
            }
            apply length_zero_iff_nil. assumption.
          }
          rewrite H in eq_cs.
          simpl in eq_cs.
          symmetry in eq_cs.
          apply (@eq_history_eq_project index index_listing Hfinite) in eq_cs.
          assumption.
        + intuition.
        + unfold res. intuition. 
    - intros. simpl in *.
      
      replace (a :: a0) with ([a] ++ a0). 2: auto.
      rewrite <- finite_protocol_plan_from_app_iff.
      
      unfold sync in Hsync.
      destruct (complete_suffix (get_history (s' inter) from) (get_history (s to) from)) eqn : eq_cs. 2: discriminate Hsync.
      
      inversion Hsync.
      unfold sync_plan in H0.
      apply map_eq_cons in H0.
      destruct H0 as [a1 [tl [H0 [Hh Htl]]]].
      apply map_eq_cons in H0.
      destruct H0 as [sa [tls [H0 [Hh' Htl']]]].
      assert (eq_cs_orig := eq_cs).
      apply complete_suffix_correct in eq_cs.
      replace (sa :: tls) with ([sa] ++ tls) in H0. 2: auto.
      apply rev_eq_app in H0. simpl in H0.
      
      rewrite H0 in eq_cs.
      assert (eq_cs' := eq_cs).
      rewrite <- app_assoc in eq_cs.
      apply (@unfold_history index index_listing Hfinite) in eq_cs.
      
      assert (Hecs: project (s to) from = project sa from). {
        apply (@eq_history_eq_project index index_listing Hfinite _ (s to) sa from).
        assumption.
      }
      
      assert (Hinsa: In sa (get_history (s' inter) from)). {
        rewrite eq_cs'.
        rewrite <- app_assoc.
        apply in_elt.
      }
      
      destruct a.
      destruct (vtransition X label_a (s, input_a)) eqn : eq_vtrans. simpl.
      
      unfold lift_to_receive_item in Hh'.
      rewrite <- Hh' in Hh.
      unfold lift_to_composite_plan_item in Hh.
      
      assert (Hinp: input_a = Some (from, sa)). {
        inversion Hh.
        reflexivity.
      }
      
      assert (protocol_transition X label_a (s, input_a) (s0, o)). {
        unfold protocol_transition.
        repeat split.
        - assumption.
        - subst input_a.
          apply option_protocol_message_Some.
          destruct (decide (inter = from)).
          + specialize (sent_component_protocol_composed IM_index i0 (free_constraint IM_index) has_been_sent_capabilities (fun m => Some (fst m)) s') as Hope.
            spec Hope. assumption.
            specialize (Hope inter (from, sa)).
            apply Hope.
            unfold has_been_sent.
            unfold has_been_sent_capabilities.
            unfold has_been_sent_lv.
            unfold send_oracle; simpl.
            rewrite decide_True.
            apply Is_true_eq_left. 
            rewrite existsb_exists.
            exists sa.
            split.
            rewrite <- e in Hinsa.
            rewrite <- e.
            assumption.
            unfold state_eqb. rewrite eq_dec_if_true. all : auto.
          + specialize (received_component_protocol_composed IM_index i0 (free_constraint IM_index) (fun m => Some (fst m)) has_been_received_capabilities s') as Hope.
            spec Hope. assumption.
            specialize (Hope inter (from, sa)).
            apply Hope.
            unfold has_been_received.
            unfold has_been_received_capabilities.
            unfold has_been_received_lv.
            unfold receive_oracle; simpl.
            rewrite decide_False.
            apply Is_true_eq_left.
            apply existsb_exists.
            exists sa.
            split.
            assumption.
            unfold state_eqb. rewrite eq_dec_if_true. all : auto.
        - simpl in *.
          inversion Hh.
          unfold vvalid.
          apply (@no_bottom_in_history index index_listing Hfinite) in Hinsa.
          unfold valid. simpl.
          repeat split.
          assumption.
          assumption.
          assumption.
        - assumption.
      }
      
      subst input_a.
      unfold res.
      
      specialize (IHa s0).
      spec IHa.
      apply protocol_transition_destination in H.
      assumption.
      
      assert (Honefold: get_history (s0 to) from = [sa] ++ get_history (s to) from). {
          assert (project (s0 to) from = sa). {
              unfold protocol_transition in H.
              unfold vtransition in eq_vtrans.
              unfold transition in eq_vtrans.
              inversion Hh.
              rewrite <- H2 in eq_vtrans.
              simpl in eq_vtrans.
              unfold vtransition in eq_vtrans.
              unfold transition in eq_vtrans.
              simpl in eq_vtrans.
              inversion eq_vtrans.
              rewrite state_update_eq.
              apply (@project_same index index_listing Hfinite).
              apply protocol_state_component_no_bottom.
              assumption.
          }
            rewrite <- H1. simpl.
            rewrite eq_cs.
            rewrite <- H1.
            apply (@unfold_history_cons index index_listing Hfinite).
            rewrite H1.
            apply (@no_bottom_in_history index index_listing Hfinite) in Hinsa.
            assumption.
        }
        assert (Hs0 : s0 = (state_update IM_index s to (update_state (s to) sa from))). {
            destruct H as [_ H].
            unfold transition in H.
            simpl in H. unfold vtransition in H. unfold transition in H. simpl in H.
            inversion Hh.
            rewrite <- H2 in H.
            inversion H.
            intuition.
          }
        
      assert (Hneed : s0 inter = s inter). {
        rewrite Hs0.
        destruct (decide(to = inter)).
        - subst inter.
          rewrite Hhist in eq_cs'.
          clear -eq_cs'.
          remember (length (get_history (s' to) from)) as len.
          assert (length (get_history (s' to) from) = length ((rev tls ++ [sa]) ++ get_history (s' to) from)). {
            rewrite <- eq_cs'.
            intuition.
          }
          rewrite <- Heqlen in H.
          rewrite app_length in H.
          rewrite <- Heqlen in H.
          rewrite app_length in H.
          simpl in H.
          lia.
        - rewrite state_update_neq.
          all : intuition.
      }
      
      spec IHa. {
        rewrite Hneed.
        intuition.
      }
        
      spec IHa. {
        unfold sync.
        destruct (complete_suffix (get_history (s' inter) from) (get_history (s0 to) from)) eqn : eq_cs2.
        f_equal.
          unfold sync_plan.
          rewrite <- Htl.
          rewrite <- Htl'.
          repeat f_equal.
          apply complete_suffix_correct in eq_cs2.
          rewrite Honefold in eq_cs2.
          rewrite eq_cs' in eq_cs2.
          rewrite app_assoc in eq_cs2.
          apply app_inv_tail in eq_cs2.
          apply app_inj_tail in eq_cs2.
          destruct eq_cs2.
          rewrite <- H1.
          apply rev_involutive.
        + rewrite Honefold in eq_cs2.
          rewrite eq_cs' in eq_cs2.
          rewrite <- app_assoc in eq_cs2.
          assert (complete_suffix (rev tls ++ [sa] ++ get_history (s to) from)
           ([sa] ++ get_history (s to) from) = Some (rev tls)). {
            apply complete_suffix_correct.
            reflexivity.  
          }
          rewrite H1 in eq_cs2.
          discriminate eq_cs2.
      }
    
      split. split. 
      + unfold finite_protocol_plan_from.
        unfold apply_plan. simpl in *.
        rewrite eq_vtrans. simpl.
        apply finite_ptrace_extend.
        apply finite_ptrace_empty.
        apply protocol_transition_destination in H. 
        assumption.
        assumption.
      + unfold apply_plan. simpl.
        rewrite eq_vtrans. simpl.
        apply IHa.
      + split.
        destruct IHa as [_ IHa].
        destruct IHa as [IHa _].
        rewrite <- IHa.
        f_equal.
        unfold apply_plan. simpl.
        rewrite fold_right_app. simpl.
        rewrite eq_vtrans. simpl.
        specialize (@apply_plan_folder_additive _ X s0 (rev a0) [{| l := label_a; input := Some (from, sa); destination := s0; output := o |}]) as Hadd.
        
        match goal with
        |- _ = snd (let (final, items) := ?f in _) to =>
          destruct f as (tr', dest') eqn : eqf2 end.
        
        match goal with
        |- snd (let (final, items) := ?f in _) to = _ =>
           match type of Hadd with ?f1 = _ =>
              change f with f1
           end
        end.
        rewrite Hadd.
        reflexivity.
        destruct IHa as [Iha1 [Iha2 Iha3]].
        replace ({| label_a := label_a; input_a := Some (from, sa) |} :: a0) with
                ([{| label_a := label_a; input_a := Some (from, sa) |}] ++ a0) by intuition.
        rewrite apply_plan_cons.
        match goal with
        |- context[apply_plan X s ?a] =>
          destruct (apply_plan X s a) as (tr_short, res_short) eqn : eq_short end.
        match goal with
        |- context[apply_plan X ?s ?a] =>
          destruct (apply_plan X s a) as (tr_long, res_long) eqn : eq_long end.
        simpl.
        
        assert (res_short = s0). {
           replace res_short with (snd (apply_plan X s [{| label_a := label_a; input_a := Some (from, sa) |}])).
           unfold apply_plan. simpl.
           rewrite eq_vtrans. simpl.
           intuition.
           match goal with
           |- snd ?a = _ => 
              replace a with (tr_short, res_short) by intuition end.
           intuition.
        }
        
        assert (snd (apply_plan X s0 a0) = res_long). {
          rewrite <- H1.
          match goal with
          |- snd ?a = _ =>
              replace a with (tr_long, res_long) by intuition end.
          intuition.
        }
        
        apply set_eq_tran with (s2 := GE res_short).
        * rewrite <- H1 in Iha3 at 2.
          rewrite H2 in Iha3.
          intuition.
        * rewrite H1.
          specialize (GE_existing_different s Hpr sa to from Hdif Hecs) as Hexisting.
          specialize (GE_existing_different_rev s Hpr sa to from Hdif Hecs) as Hexisting'.
          
          assert (s0 = (state_update IM_index s to (update_state (s to) sa from))). {
            destruct H as [_ H].
            unfold transition in H.
            simpl in H. unfold vtransition in H. unfold transition in H. simpl in H.
            inversion Hh.
            rewrite <- H4 in H.
            inversion H.
            intuition.
          }
          
          assert (In (SimpObs Message' from sa) (cobs s from)). {
             rewrite <- Hhist in Hinsa.
             apply (@in_history_in_observations index index_listing Hfinite) in Hinsa.
             apply in_cobs_messages'.
             apply cobs_single.
             exists inter.
             split;[apply in_listing|].
             intuition.
          }
          
          rewrite H3.
          unfold set_eq.
          split;[apply Hexisting; intuition| apply Hexisting'; intuition].
    Qed.
   
    Definition get_candidates 
      (s : vstate X) :
      list state 
      :=
    component_list s (GH s).
    
    Existing Instance state_lt'_dec.
    Existing Instance state_lt_ext_dec.
    
    Definition get_topmost_candidates
      (s : vstate X)
      (target : index) :
      list state 
      :=
      get_maximal_elements (fun s s' => bool_decide (state_lt_ext target (project s target) (project s' target))) (get_candidates s).
    
    Lemma honest_self_projections_maximal1
      (s : vstate X)
      (Hpr : protocol_state_prop X s)
      (i j : index)
      (Hhonest : In i (GH s)) :
      state_lt_ext i (project (s j) i) (s i).
    Proof.
      assert (Hsnb : forall (i : index), (s i) <> Bottom). {
        intros.
        apply protocol_state_component_no_bottom.
        intuition.
      }
    unfold state_lt_ext.
    destruct (s i) eqn : eq_si;[specialize (Hsnb i);congruence|].
    destruct (project (s j) i) eqn : eq_pji;[left; intuition congruence|].
    destruct (decide (state_lt' i (project (s j) i) (s i)));right; rewrite <- eq_si; rewrite <- eq_pji.
    - intuition.
    - assert (He : In i (GE s)). {
        apply GE_direct.
        unfold cequiv_evidence.
        unfold equivocation_evidence.
        setoid_rewrite hbo_cobs.
        exists (SimpObs State' i (s i)).
        unfold get_simp_event_subject_some. simpl.
        split.
        - apply in_cobs_states'.
          apply state_obs_present. apply in_listing.
        - split;[intuition|].
          exists (SimpObs Message' i (project (s j) i)). simpl.
          split.
          + apply in_cobs_messages'.
            apply cobs_single.
            exists j. split;[apply in_listing|].
            apply refold_simp_lv_observations1.
            apply Hsnb.
            rewrite eq_pji. congruence.
            intuition.
          + split;[intuition|].
            unfold simp_lv_event_lt.
            unfold comparable.
            rewrite decide_True by intuition.
            intros contra.
            destruct contra.
            * congruence.
            * rewrite decide_True in H by intuition.
              destruct H;[intuition|].
              intuition.
      }
      apply wH_wE' in Hhonest. intuition.
  Qed.
  
    Lemma honest_self_projections_maximal2
    (s : vstate X)
    (Hpr : protocol_state_prop X s)
    (i j : index)
    (Hhonest : In i (GH s)) :
    project (s j) i = project (s i) i \/ state_lt_ext i (project (s j) i) (project (s i) i).
  Proof.
    assert (Hsnb : forall (i : index), (s i) <> Bottom). {
      intros.
      apply protocol_state_component_no_bottom.
      intuition.
    } 
    unfold state_lt_ext.
    destruct (s i) eqn : eq_si;[specialize (Hsnb i);congruence|]. rewrite <- eq_si.
    
    specialize (honest_self_projections_maximal1 s Hpr i j Hhonest) as Hh.
    destruct (project (s i) i) eqn : eq_pii.
    - destruct (project (s j) i) eqn : eq_pji.
      + left. intuition.
      + rewrite <- eq_pji in *.
        unfold state_lt_ext in Hh.
        destruct Hh;[intuition congruence|].
        unfold state_lt' in H.
        rewrite unfold_history_bottom in H by intuition. 
        intuition.
    - unfold state_lt_ext in Hh.
      destruct Hh;[intuition congruence|].
      rewrite <- eq_pii in *.
      destruct (project (s j) i) eqn : eq_pji;[right;left;intuition congruence|].
      rewrite <- eq_pji in *.
      destruct (decide (project (s j) i = project (s i) i));[left;intuition|].
      right. right.
      
      unfold state_lt' in H.
      apply in_split in H as H2.
      destruct H2 as [left1 [right1 Heq1]].
      apply (@unfold_history index index_listing Hfinite) in Heq1 as Heq1'.
      rewrite Heq1' in Heq1.
      rewrite (@unfold_history_cons index index_listing Hfinite) in Heq1 by (intuition congruence).
      destruct left1.
      + simpl in Heq1. inversion Heq1. congruence.
      + inversion Heq1.
        unfold state_lt'.
        rewrite H2.
        apply in_app_iff. right. intuition.
  Qed.
    
    Lemma honest_always_candidate_for_self
      (s : vstate X)
      (Hpr : protocol_state_prop X s)
      (i : index)
      (Hhonest : In i (GH s)) :
      In (s i) (get_topmost_candidates s i).
    Proof.
     - unfold get_topmost_candidates.
      unfold get_maximal_elements.
      apply filter_In.
      split.
      + unfold get_candidates. apply in_map_iff. exists i. intuition.
      + rewrite forallb_forall. intros.
        rewrite negb_true_iff.
        rewrite bool_decide_eq_false.
        apply in_map_iff in H.
        destruct H as [j [Heqj Hinj]]. subst x.
        specialize (honest_self_projections_maximal2 s Hpr i j Hhonest) as Hh.
        intros contra.
        destruct Hh.
        * unfold state_lt_ext in contra.
          destruct contra;[intuition congruence|].
          rewrite H in H0.
          unfold state_lt' in H0.
          apply (@history_no_self_reference index index_listing Hfinite) in H0.
          intuition.
        * apply (@state_lt_ext_antisymmetric index index_listing Hfinite) in H.
          intuition.
  Qed.
  
  Lemma all_candidates_for_honest_equiv
    (s : vstate X)
    (Hpr : protocol_state_prop X s)
    (i : index)
    (Hhonest : In i (GH s)) :
    forall (s' : (@state index index_listing)), 
    In s' (get_topmost_candidates s i) -> project s' i = project (s i) i.
  Proof.
    intros.
    unfold get_topmost_candidates in H.
    unfold get_maximal_elements in H.
    apply filter_In in H.
    destruct H as [Hin H].
    rewrite forallb_forall in H.
    specialize (H (s i)).
    spec H. {
      apply in_map_iff. exists i. intuition.
    }
    rewrite negb_true_iff in H.
    rewrite bool_decide_eq_false in H.
    destruct (decide (project (s i) i = project s' i));[intuition|].
    
    apply in_map_iff in Hin.
    destruct Hin as [j [Heqj Hj]].
    subst s'.
    specialize (honest_self_projections_maximal2 s Hpr i j Hhonest) as Hh.
    destruct Hh;[intuition congruence|].
    intuition.
  Qed.
    
    Definition get_matching_state
      (s : vstate X)
      (to from : index) : state :=
      let candidates := (get_topmost_candidates s from) in
      let found := List.find (fun s' => bool_decide (state_lt_ext from (project (s to) from) s')) candidates in
      match found with
      | Some s' => s'
      | None => (s to)
      end.
      
    Remark get_matching_state_correct1
      (s : vstate X)
      (to from : index) :
      exists (inter : index), (get_matching_state s to from) = (s inter).
    Proof.
      unfold get_matching_state.
      destruct (find (fun s' : state => bool_decide (state_lt_ext from (project (s to) from) s'))
      (get_topmost_candidates s from)) eqn : eq_find.
      - apply find_some in eq_find.
        destruct eq_find as [eq_find _].
        unfold get_topmost_candidates in eq_find.
        unfold get_maximal_elements in eq_find.
        apply filter_In in eq_find.
        destruct eq_find as [eq_find _].
        unfold get_candidates in eq_find.
        unfold component_list in eq_find.
        apply in_map_iff in eq_find.
        destruct eq_find as [inter Hinter].
        exists inter. intuition.
      - exists to. intuition.
    Qed.
    
    Remark get_matching_state_correct2
      (s : vstate X)
      (to from : index)
      (Hin : In to (GH s)) :
      exists (inter : index), In inter (GH s) /\ (get_matching_state s to from) = (s inter).
    Proof.
      unfold get_matching_state.
      destruct (find (fun s' : state => bool_decide (state_lt_ext from (project (s to) from) s'))
      (get_topmost_candidates s from)) eqn : eq_find.
      - apply find_some in eq_find.
        destruct eq_find as [eq_find _].
        unfold get_topmost_candidates in eq_find.
        unfold get_maximal_elements in eq_find.
        apply filter_In in eq_find.
        destruct eq_find as [eq_find _].
        unfold get_candidates in eq_find.
        unfold component_list in eq_find.
        apply in_map_iff in eq_find.
        destruct eq_find as [inter Hinter].
        exists inter. intuition.
      - exists to. intuition.
    Qed.
    
    Definition top_history
      (s : vstate X)
      (from : index) :=
      let history_lengths := List.map (fun s' : state => length (get_history s' from)) (get_candidates s) in
      let max_length := list_max history_lengths in
      filter (fun s' : state => beq_nat (length (get_history s' from)) max_length) (get_candidates s).
    
    Lemma top_history_something 
      (s : vstate X)
      (from : index) :
      exists (s' : state), In s' (top_history s from).
    Proof.
      unfold top_history.
      specialize (list_max_exists (List.map (fun s' : state => length (get_history s' from)) (get_candidates s))) as Hmax.
      spec Hmax. admit. apply in_map_iff in Hmax.
      destruct Hmax.
      exists x. apply filter_In. split;[intuition|].
      rewrite beq_nat_true_iff. intuition.
    Admitted.
    
    Lemma topmost_candidates_nonempty 
      (s : vstate X)
      (from : index)
      (Hne : GH s <> []) :
      exists (s' : state), In s' (get_topmost_candidates s from).
    Proof.
      specialize (top_history_something s from) as Htop_hist.
      destruct Htop_hist as [s' Htop].
      exists s'.
      unfold get_topmost_candidates.
      apply filter_In.
      unfold top_history in Htop.
      apply filter_In in Htop.
      split;[intuition|].
      destruct Htop as [_ Htop].
      rewrite beq_nat_true_iff in Htop.
      rewrite forallb_forall. 
      intros.
      rewrite negb_true_iff.
      rewrite bool_decide_eq_false.
      intros contra.
      specialize (list_max_le (map (fun s'0 : state => length (get_history s'0 from)) (get_candidates s))) as Hmax.
      specialize (Hmax (length (get_history s' from))).
      rewrite Htop in Hmax. 
      destruct Hmax as [Hmax _]. spec Hmax. lia.
      rewrite Forall_forall in Hmax.
      specialize (Hmax (length (get_history x from))).
      spec Hmax. {
        apply in_map_iff.
        exists x. intuition.
      }
      rewrite <- Htop in Hmax.
      unfold state_lt_ext in contra.
      destruct contra.
      - assert (get_history s' from = []) by (apply unfold_history_bottom;intuition).
        rewrite H1 in Hmax. simpl in Hmax. 
        rewrite (@unfold_history_cons index index_listing Hfinite) in Hmax.
        simpl in Hmax. lia. intuition.
      - unfold state-lt'
    Qed.
    
    Remark get_matching_state_correct3
      (s : vstate X)
      (to from : index)
      (Hin : In to (GH s)) :
      In (get_matching_state s to from) (get_topmost_candidates s from).
    Proof.
      unfold get_matching_state.
      destruct (find (fun s' : state => bool_decide (state_lt_ext from (project (s to) from) s'))
      (get_topmost_candidates s from)) eqn : eq_find.
      - apply find_some in eq_find. intuition.
      - unfold get_topmost_candidates.
        unfold get_maximal_elements.
        apply filter_In.
        split.
        + apply in_map_iff. exists to. intuition.
        + rewrite forallb_forall. intros.
          rewrite negb_true_iff.
          rewrite bool_decide_eq_false.
          intros contra.
          specialize (find_none (fun s' : state => bool_decide (state_lt_ext from (project (s to) from) s'))) as Hnone.
          specialize (Hnone (get_topmost_candidates s from) eq_find).
          
          specialize (Hnone x). spec Hnone. admit.
          rewrite bool_decide_eq_false in Hnone.
          
    Admitted.
    
   Lemma get_matching_state_for_honest
    (s : vstate X)
    (Hpr : protocol_state_prop X s)
    (i j : index)
    (Hhonest : In i (GH s)) :
    project (get_matching_state s j i) i = project (s i) i.
  Proof.
    unfold get_matching_state.
    destruct (find (fun s' : state => bool_decide (state_lt_ext i (project (s j) i) s'))
    (get_topmost_candidates s i)) eqn : eq_find.
    - apply find_some in eq_find.
      destruct eq_find as [Hin Hcomp].
      rewrite bool_decide_eq_true in Hcomp.
      specialize (all_candidates_for_honest_equiv s Hpr i Hhonest).
      intros.
      specialize (H s0 Hin).
      intuition.
    - specialize (find_none (fun s' : state => bool_decide (state_lt_ext i (project (s j) i) s'))) as Hnone.
      specialize (Hnone (get_topmost_candidates s i) eq_find).
      specialize (Hnone (s i)).
        
      assert (In (s i) (get_topmost_candidates s i)). {
         apply honest_always_candidate_for_self.
         intuition.
         intuition.
      }
      
      specialize (Hnone H).
      simpl in Hnone.
      rewrite bool_decide_eq_false in Hnone.
      specialize (honest_self_projections_maximal1 s Hpr i j Hhonest) as Hh.
      intuition.
  Qed.
      
    Definition get_matching_plan
      (s : vstate X)
      (from to : index) : vplan X :=
      let s' := get_matching_state s to from in
      match (sync s s' to from) with
      | None => []
      | Some a => a
      end.
      
    Lemma sync_some 
      (s : vstate X)
      (from to : index) :
      sync s (get_matching_state s to from) to from <> None.
    Proof.
      intros contra.
      unfold get_matching_state in contra.
      destruct (find (fun s' : state => bool_decide (state_lt_ext from (project (s to) from) s'))
               (get_topmost_candidates s from)) eqn : eq_find.
      - apply find_some in eq_find.
        destruct eq_find as [_ eq_find].
        unfold sync in contra.
        destruct (complete_suffix (get_history s0 from) (get_history (s to) from)) eqn : eq_suf.
        discriminate contra.
        unfold state_ltb' in eq_find.
        rewrite bool_decide_eq_true in eq_find.
        unfold state_lt_ext in eq_find.
        destruct eq_find as [eq_find|eq_find].
        + destruct eq_find as [Hb _].
          apply unfold_history_bottom in Hb.
          rewrite Hb in eq_suf.
          rewrite complete_suffix_empty in eq_suf.
          congruence.
        + unfold state_lt' in eq_find.
          assert (eq_find' := eq_find).
          apply in_split in eq_find.
          destruct eq_find as [pref [suff Heq]].
          apply (@unfold_history index index_listing) in Heq as Hsufhist.
          rewrite Hsufhist in Heq.
          apply complete_suffix_correct in Heq.
          assert ((project (s to) from :: get_history (project (s to) from) from) = get_history (s to) from). {
            symmetry.
            apply (@unfold_history_cons index index_listing).
            assumption.
            apply (@no_bottom_in_history index index_listing Hfinite idec s0 _ from).
            intuition.
          }
        rewrite H in Heq.
        rewrite Heq in eq_suf.
        discriminate eq_suf.
        intuition.
       - unfold sync in contra.
         destruct (complete_suffix (get_history (s to) from) (get_history (s to) from)) eqn : eq_suf.
         + discriminate contra.
         + assert (get_history (s to) from = [] ++ (get_history (s to) from)). {
            intuition.
           }
           apply complete_suffix_correct in H.
           rewrite H in eq_suf.
           discriminate eq_suf. 
    Qed.
    
    Lemma get_matching_plan_effect 
      (s : vstate X)
      (Hprs : protocol_state_prop X s)
      (s' : state)
      (from to : index)
      (Hdif : from <> to)
      (Hmatch : get_matching_state s to from = s') :
      let res := snd (apply_plan X s (get_matching_plan s from to)) in
      finite_protocol_plan_from X s (get_matching_plan s from to) /\
      project (res to) from = project s' from.
    Proof.
      simpl.
      unfold get_matching_plan.
      rewrite Hmatch.
      destruct (sync s s' to from) eqn : eq_sync.
      - unfold sync in eq_sync.
        destruct (complete_suffix (get_history s' from) (get_history (s to) from)) eqn : eq_suf;[|congruence].
        assert (eq_suf_original := eq_suf).
        apply complete_suffix_correct in eq_suf.
        inversion eq_sync.
        specialize (one_sender_receive_protocol s s Hprs Hprs to) as Hone.
        unfold get_matching_state in Hmatch.
        destruct (find (fun s'0 : state => bool_decide (state_lt_ext from (project (s to) from) s'0))
             (get_topmost_candidates s from)) eqn : eq_find.
        + apply find_some in eq_find.
          destruct eq_find as [eq_find _].
          unfold get_topmost_candidates in eq_find.
          unfold get_maximal_elements in eq_find.
          apply filter_In in eq_find.
          destruct eq_find as [eq_find _].
          unfold get_candidates in eq_find.
          unfold component_list in eq_find.
          apply in_map_iff in eq_find.
          destruct eq_find as [inter [Hinter _]].
          
          specialize (Hone inter from eq_refl).
          spec Hone. {
            intuition.
          }
          
          specialize (Hone (sync_plan to from (rev l))).
          
          spec Hone. {
             unfold sync.
             rewrite <- Hmatch in eq_suf_original.
             rewrite <- Hinter in eq_suf_original.
             rewrite eq_suf_original.
             reflexivity.
          }
          simpl in Hone.
          rewrite <- Hmatch.
          rewrite <- Hinter.
          intuition.
        + rewrite <- Hmatch.
          rewrite <- Hmatch in eq_suf.
          assert (Hempty: l = []). {
            replace (get_history (s to) from) with ([] ++ (get_history (s to) from)) in eq_suf at 1.
            apply app_inv_tail in eq_suf.
            all : intuition.
          }
          rewrite Hempty.
          simpl.
          unfold sync_plan; simpl.
          intuition.
          apply finite_protocol_plan_empty.
          assumption.
      - rewrite <- Hmatch in eq_sync.
        apply sync_some in eq_sync.
        intuition. 
    Qed.
    
    Remark get_matching_plan_info
      (s : vstate X)
      (from to : index)
      (ai : plan_item)
      (Hin : In ai (get_matching_plan s from to)) :
      let component := projT1 (label_a ai) in
      let label := projT2 (label_a ai) in
      label = receive /\
      component = to /\
      (exists (so : state), (input_a ai = Some (from, so)) /\ In (SimpObs Message' from so) (cobs_messages s from)).
    Proof.
      unfold get_matching_plan in Hin.
      remember (get_matching_state s to from) as s0.
      destruct (sync s s0 to from) eqn : eq_sync.
        + unfold sync in eq_sync.
          destruct (complete_suffix (get_history s0 from) (get_history (s to) from)) eqn : eq_hist;[|congruence].
          inversion eq_sync.
          unfold sync_plan in H0.
          rewrite <- H0 in Hin.
          apply in_map_iff in Hin.
          destruct Hin as [x [Hlift Hinx]].
          
          apply in_map_iff in Hinx.
          destruct Hinx as [so [Hlift_rec Hinso]].
          unfold lift_to_receive_item in Hlift_rec.
          subst x.
          unfold lift_to_composite_plan_item in Hlift.
          rewrite <- Hlift. simpl.
          split;[intuition|].
          split;[intuition|].
          exists so. split;[intuition|].
          apply in_rev in Hinso.
          apply complete_suffix_correct in eq_hist.
          assert (In so (get_history s0 from)). {
            rewrite eq_hist.
            apply in_app_iff. left.
            intuition.
          }
          rewrite Heqs0 in H.
          specialize (get_matching_state_correct1 s to from) as Hinter.
          destruct Hinter as [inter Heq_inter].
          rewrite Heq_inter in H.
          apply (@in_history_in_observations index index_listing Hfinite) in H.
          apply cobs_single.
          exists inter. intuition.
          apply in_listing.
        + contradict Hin.
    Qed.
    
    Definition get_receives_for
      (s : vstate X)
      (li : list index)
      (from : index) : vplan X :=
      let matching_plans := List.map (get_matching_plan s from) li in
      List.concat matching_plans.
      
    Definition get_receives_for_info
      (s : vstate X)
      (li : list index)
      (from : index)
      (ai : vplan_item X)
      (Hin : In ai (get_receives_for s li from)) :
      let component := projT1 (label_a ai) in
      let label := projT2 (label_a ai) in
      label = receive /\
      In component li /\
      (exists (so : state), (input_a ai = Some (from, so)) /\ In (SimpObs Message' from so) (cobs_messages s from)).
    Proof.
      unfold get_receives_for in Hin.
      apply in_concat in Hin.
      destruct Hin as [smaller [Hin_smaller Hin_ai]].
      
      apply in_map_iff in Hin_smaller.
      destruct Hin_smaller as [i [Heq_matching Hini]].
      
      rewrite <- Heq_matching in Hin_ai.
      apply get_matching_plan_info in Hin_ai.
      simpl in *.
      split;[intuition|].
      split.
      - destruct Hin_ai as [_ [Hin_ai]].
        rewrite Hin_ai. intuition.
      - destruct Hin_ai as [_ [_ Hin_ai]].
        destruct Hin_ai as [so Hso].
        exists so. intuition.
    Qed.
    
    Lemma get_receives_for_correct
        (s : vstate X)
        (Hpr : protocol_state_prop X s)
        (li : list index)
        (from : index)
        (Hnodup : NoDup li)
        (Hnf : ~ In from li) :
        let res := snd (apply_plan X s (get_receives_for s li from)) in
        finite_protocol_plan_from X s (get_receives_for s li from) /\
        forall (i : index), In i li -> project (res i) from = project (get_matching_state s i from) from.
    Proof.
      induction li using rev_ind; intros.
      - unfold get_receives_for. simpl.
        split.
        apply finite_protocol_plan_empty.
        assumption.
        intuition.
      - unfold res.
        unfold get_receives_for.
        rewrite map_app.
        rewrite concat_app. simpl in *.
        rewrite app_nil_r.
        
        rewrite apply_plan_app.
       
        destruct (apply_plan X s (concat (map (get_matching_plan s from) li))) as (tr_long, res_long) eqn : eq_long.
        destruct (apply_plan X res_long (get_matching_plan s from x)) as (tr_short, res_short) eqn : eq_short.
        simpl.
        
        assert (Hres_long : res_long = snd (apply_plan X s (concat (map (get_matching_plan s from) li)))). {
          rewrite eq_long. intuition.
        }
        
        assert (Hres_short : res_short = snd ((apply_plan X res_long (get_matching_plan s from x)))). {
          rewrite eq_short. intuition.
        }
        
        assert (Hnodup_li : NoDup li). {
          apply NoDup_rev in Hnodup.
          rewrite rev_app_distr in Hnodup.
          simpl in Hnodup.
          apply NoDup_cons_iff in Hnodup.
          destruct Hnodup as [_ Hnodup].
          apply NoDup_rev in Hnodup.
          rewrite rev_involutive in Hnodup.
          intuition.
        }
        
        assert (Hnf_li : ~In from li). {
          intros contra.
          contradict Hnf.
          apply in_app_iff.
          left. intuition.
        }
        
        assert (Hnxf : x <> from). {
          intros contra.
          rewrite contra in Hnf.
          intuition.
        }
        
        assert (Hnx_li : ~In x li). {
          intros contra.
          apply in_split in contra.
          destruct contra as [lf [rt Heq]].
          rewrite Heq in Hnodup.
          apply NoDup_remove_2 in Hnodup.
          contradict Hnodup.
          rewrite app_nil_r.
          apply in_app_iff.
          right. intuition.
        }
        
        specialize (IHli Hnodup_li Hnf_li).
        
        assert (Hrem : forall (i : index), ~In i li -> res_long i = s i). {
          intros.
          rewrite Hres_long.
          apply irrelevant_components.
          intros contra.
          apply in_map_iff in contra.
          destruct contra as [some [Hproj Hinsome]].
          
          apply in_map_iff in Hinsome.
          destruct Hinsome as [pi [Hlabel Inpi]].
          apply in_concat in Inpi.
          destruct Inpi as [lpi [Hlpi Hinlpi]].
          apply in_map_iff in Hlpi.
          destruct Hlpi as [j [Hmatch Hwhat]].
          rewrite <- Hmatch in Hinlpi.
          apply get_matching_plan_info in Hinlpi.
          rewrite <- Hlabel in Hproj.
          assert (i = j). {
            rewrite <- Hproj. 
            intuition.
          }
          clear Hproj. clear Hinlpi.
          subst i.
          intuition.
        }
        
        destruct IHli as [IHli_proto IHli_proj].
        
        assert (Hpr_long : protocol_state_prop X res_long). {
          apply apply_plan_last_protocol in IHli_proto.
          subst res_long.
          all : intuition.
        }
        
        assert (Hmatch_idx : incl (map (projT1 (P:=fun n : index => vlabel (IM_index n)))
               (map label_a (get_matching_plan s from x))) [x]). {
           unfold incl.
           intros.
           apply in_map_iff in H.
           destruct H as [smth [Hproj Hinsmth]].
           apply in_map_iff in Hinsmth.
           destruct Hinsmth as [pi [Hlabel Hinpi]].
           apply get_matching_plan_info in Hinpi.
           rewrite <- Hlabel in Hproj.
           destruct Hinpi as [_ [Hinpi _]].
           subst a. subst x.
           intuition.
        }
        
        assert (Hrem2 : forall (i : index), In i li -> res_long i = res_short i). {
          intros.
          assert (~In i [x]). {
            intros contra.
            destruct contra; [|intuition]. subst i.
            intuition.
          }
          subst res_long. subst res_short.
          symmetry.
          apply irrelevant_components.
          intros contra.
          assert (In i [x]). {
            unfold incl in Hmatch_idx.
            specialize (Hmatch_idx i contra).
            intuition.
          }
          intuition.
        }
        
        specialize (get_matching_plan_effect s Hpr (get_matching_state s x from) from x) as Heff.
        spec Heff. intuition.
        specialize (Heff eq_refl).
        
        simpl in Heff.
        destruct Heff as [Heff Heff2].
        
        apply relevant_components with (s' := res_long) (li0 := [x]) in Heff.
        
        2, 4 : intuition.
        2 : {
          intros.
          simpl in H. destruct H;[|intuition].
          subst i.
          specialize (Hrem x Hnx_li). intuition.
        }
        
        rewrite Hres_long in Heff.
        destruct Heff as [Heff_proto Heff_proj].
        
        split.
        + apply finite_protocol_plan_from_app_iff.
          split. 
          * unfold get_receives_for in IHli_proto. intuition.
          * intuition.
        + intros.
          apply in_app_iff in H.
          destruct H as [H|H].
          * specialize (IHli_proj i H).
            rewrite <- IHli_proj.
            specialize (Hrem2 i H).
            rewrite <- Hrem2.
            rewrite Hres_long.
            intuition.
          * simpl in H. destruct H; [|intuition].
            subst i.
            subst res_short. subst res_long.
            specialize (Heff_proj x). 
            spec Heff_proj. intuition. simpl in Heff_proj.
            unfold free_composite_vlsm in Heff_proj.
            rewrite <- Heff2.
            unfold X. unfold X in Heff_proj.
            rewrite Heff_proj.
            intuition.
    Qed.
    
    Definition is_receive_plan
      (a : vplan X) : Prop := 
      forall (ai : vplan_item X),
        In ai a -> projT2 (label_a ai) = receive.
    
    Definition is_receive_plan_app
      (a b : vplan X) :
      is_receive_plan a /\ is_receive_plan b <-> is_receive_plan (a ++ b).
    Proof.
      unfold is_receive_plan.
      split; intros.
      - destruct H as [Hl Hr].
        apply in_app_iff in H0.
        destruct H0.
        + specialize (Hl ai). intuition.
        + specialize (Hr ai). intuition.
      - split; intros.
        + specialize (H ai).
          spec H. apply in_app_iff. left. intuition.
          intuition.
        + specialize (H ai).
          spec H. apply in_app_iff. right. intuition.
          intuition.
    Qed.
    
    Lemma message_providers_receive
      (s : vstate X)
      (i : index) :
      incl (get_message_providers_from_plan (get_receives_for s (others i s) i)) [i].
    Proof.
      unfold incl. intros.
      unfold get_message_providers_from_plan in H.
      unfold messages_a in H.
      apply in_map_iff in H.
      destruct H as [psi [Heq Hinpsi]].
      apply in_cat_option in Hinpsi.
      destruct Hinpsi as [opsi [Hinopsi Heq_opsi]].
      apply in_map_iff in Hinopsi.
      destruct Hinopsi as [ai [Heq_ai Hinai]].
      apply get_receives_for_info in Hinai.
      
      destruct Hinai as [_ [_ Hinai]].
      destruct Hinai as [so [Heq_so Hinso]].
      rewrite Heq_ai in Heq_so.
      rewrite Heq_opsi in Heq_so.
      inversion Heq_so.
      rewrite H0 in Heq.
      simpl in Heq.
      subst a.
      intuition.
    Qed.
    
    Lemma receive_for_is_receive_plan 
      (s : vstate X)
      (from : index)
      (li : list index) :
      is_receive_plan (get_receives_for s li from).
    Proof.
      unfold is_receive_plan. intros.
      apply get_receives_for_info in H.
      intuition.
    Qed.
    
    Lemma receives_neq
      (s : vstate X)
      (Hpr : protocol_state_prop X s)
      (a : vplan X) 
      (Hpra : finite_protocol_plan_from X s a)
      (i j : index)
      (providers := get_message_providers_from_plan a)
      (Hreceive : is_receive_plan a)
      (Hj : ~ In j providers) 
      (res := snd (apply_plan X s a)) :
      project (res i) j = project (s i) j.
    Proof.
      induction a using rev_ind.
      - intuition.
      - apply finite_protocol_plan_from_app_iff in Hpra.
      
        destruct Hpra as [Hpra_long Hpra_short].
        specialize (IHa Hpra_long); simpl in *.
        apply is_receive_plan_app in Hreceive.
        
        destruct Hreceive as [Hreceive_long Hreceive_short].
        specialize (IHa Hreceive_long); simpl.
        
        spec IHa. {
          clear -Hj.
          intros contra.
          contradict Hj.
          unfold providers.
          unfold get_message_providers_from_plan in *.
          unfold messages_a in *.
          rewrite map_app.
          rewrite cat_option_app.
          rewrite map_app.
          apply in_app_iff.
          left. intuition.
        }
        
        rewrite <- IHa.
        unfold res.
        rewrite apply_plan_app.
        destruct (apply_plan X s a) as [tr_long res_long].
        simpl in *.
        unfold apply_plan.
        unfold apply_plan_folder.
        destruct x. simpl.
        destruct (vtransition X label_a (res_long, input_a)) eqn : eq_trans.
        simpl.
        
        unfold finite_protocol_plan_from in Hpra_short.
        unfold apply_plan in Hpra_short.
        unfold apply_plan_folder in Hpra_short.
        simpl in Hpra_short.
        rewrite eq_trans in Hpra_short.
        simpl in Hpra_short.
        inversion Hpra_short.
        
        unfold protocol_transition in H6.
        destruct H6 as [Hprtr Htrans].
        
        unfold vtransition in eq_trans.
        unfold transition in eq_trans.
        simpl in eq_trans.
        unfold vtransition in eq_trans.
        unfold transition in eq_trans.
        simpl in eq_trans.
        remember label_a as label_a'.
        destruct label_a as [idx li].
        
        destruct li eqn : eq_li.
        + unfold is_receive_plan in Hreceive_short.
          specialize (Hreceive_short {| label_a := label_a'; input_a := input_a |}).
          move Hreceive_short at bottom.
          simpl in Hreceive_short.
          spec Hreceive_short. intuition.
          subst label_a'. simpl in Hreceive_short.
          congruence.
        + destruct input_a eqn : eq_input.
          * rewrite Heqlabel_a' in eq_trans.
            inversion eq_trans.
            destruct (decide (i = idx)).
            -- rewrite e. rewrite state_update_eq.
              rewrite (@project_different index index_listing).
              reflexivity.
              intuition.
              intros contra. {
                clear -Hj contra.
                unfold providers in Hj.
                unfold get_message_providers_from_plan in Hj.
                rewrite contra in Hj.
                contradict Hj.
                apply in_map_iff.
                exists m. intuition.
                unfold messages_a.
                rewrite map_app.
                rewrite cat_option_app.
                rewrite in_app_iff.
                right; simpl; intuition.
              }
              clear -Hprtr.
              apply protocol_state_component_no_bottom.
              unfold protocol_valid in Hprtr.
              intuition.
          -- rewrite state_update_neq.
             reflexivity.
             assumption.
         * unfold protocol_valid in Hprtr.
           unfold valid in Hprtr.
           rewrite Heqlabel_a' in Hprtr.
           simpl in Hprtr.
           unfold constrained_composite_valid in Hprtr.
           unfold free_constraint in Hprtr.
           unfold free_composite_valid in Hprtr.
           unfold vvalid in Hprtr.
           unfold valid in Hprtr.
           simpl in Hprtr.
           intuition.
    Qed.
    
    Lemma relevant_component_transition_lv
      (s s' : vstate X)
      (Hprs : protocol_state_prop X s)
      (Hprs' : protocol_state_prop X s') 
      (l : vlabel X)
      (input : message)
      (i := projT1 l)
      (Hsame : project (s i) (fst input) = project (s' i) (fst input))
      (Hvalid: protocol_valid X l (s, Some input)) :
      protocol_valid X l (s', Some input).
    Proof.
      unfold protocol_valid in *.
      intuition.
      clear X0 X1.
      unfold valid in *.
      simpl in *.
      unfold constrained_composite_valid in *.
      unfold free_composite_valid in *.
      unfold vvalid in *.
      intuition.
      unfold valid in *.
      unfold machine in *.
      simpl in *.
      destruct l as [j lj].
      destruct lj eqn : eq_lj.
      - destruct H0 as [_ Hd].
        discriminate Hd.
      - intuition.
        simpl in i.
        subst i.
        rewrite <- Hsame.
        assumption.
    Qed.
    
    Lemma relevant_components_lv
      (s s' : vstate X)
      (Hprs : protocol_state_prop X s)
      (Hprs' : protocol_state_prop X s')
      (a : vplan X)
      (Hrec : is_receive_plan a)
      (Hpr : finite_protocol_plan_from X s a)
      (f : index)
      (Hli : incl (get_message_providers_from_plan a) [f])
      (Hsame : forall (i : index), project (s i) f = project (s' i) f) :
      let res' := snd (apply_plan X s' a) in
      let res := snd (apply_plan X s a) in 
      finite_protocol_plan_from X s' a /\ 
      forall (i : index), project (res' i) f = project (res i) f.
    Proof.
      induction a using rev_ind.
      - simpl. 
        split. apply finite_protocol_plan_empty.
        assumption.
        intros.
        specialize (Hsame i).
        intuition.
      - simpl.
        
        apply is_receive_plan_app in Hrec.
        destruct Hrec as [Hrec_long Hrec_short].
        apply finite_protocol_plan_from_app_iff in Hpr.
        destruct Hpr as [Hpr_long Hpr_short].
        
        rewrite apply_plan_app.
        destruct (apply_plan X s' a) as (tr_long', res_long') eqn : eq_long'.
        destruct (apply_plan X res_long' [x]) as (tr_short', res_short') eqn : eq_short'.
        simpl.
        
        spec IHa. intuition.
        spec IHa. intuition.
        
        spec IHa. {
          clear -Hli.
          unfold get_message_providers_from_plan in *.
          unfold messages_a in *.
          unfold incl in *.
          rewrite map_app in Hli.
          rewrite cat_option_app in Hli.
          rewrite map_app in Hli.
          intros.
          specialize (Hli a0).
          apply Hli.
          apply in_app_iff; left; intuition.
        }
        
        simpl in IHa.
        destruct IHa as [Iha_pr Iha_proj].
        
        rewrite apply_plan_app.
        destruct (apply_plan X s a) as (tr_long, res_long) eqn : eq_long.
        destruct (apply_plan X res_long [x]) as (tr_short, res_short) eqn : eq_short.
        simpl in *.
        
        assert (res_long = snd (apply_plan X s a)). {
          rewrite eq_long.
          intuition.
        }
        
        assert (res_short = snd (apply_plan X res_long [x])). {
          rewrite eq_short.
          intuition.
        }
        
        assert (res_long' = snd (apply_plan X s' a)). {
          rewrite eq_long'.
          intuition.
        }
        
        assert (res_short' = snd (apply_plan X res_long' [x])). {
          rewrite eq_short'.
          intuition.
        }
          
        replace res_short' with (snd (apply_plan X res_long' [x])).
        replace res_short with (snd (apply_plan X res_long [x])).
        
        unfold apply_plan.
        unfold apply_plan_folder.
        specialize (Hrec_short x).
        destruct x as [label_x input_x].
        simpl.
        
        assert (Hprs_long : protocol_state_prop X res_long). {
          rewrite H.
          apply apply_plan_last_protocol.
          assumption.
          assumption.
        }
        
        assert (Hprs'_long : protocol_state_prop X res_long'). {
          rewrite H1.
          apply apply_plan_last_protocol.
          assumption.
          assumption.
        } 
        
        destruct (vtransition X label_x (res_long', input_x)) eqn : trans'.
        destruct (vtransition X label_x (res_long, input_x)) eqn : trans.
        simpl.
        
        unfold finite_protocol_plan_from in Hpr_short.
        unfold apply_plan in Hpr_short.
        unfold apply_plan_folder in Hpr_short.
        simpl in Hpr_short.
        rewrite trans in Hpr_short.
          
        inversion Hpr_short.
        remember H10 as Hprotocol_trans.
        unfold protocol_transition in H10.
        destruct H10 as [Hprotocol_valid Htrans].
        
        unfold vtransition in trans, trans'.
        unfold transition in trans, trans'.
        simpl in *.
        unfold vtransition in trans, trans'.
        destruct label_x as [j label_x].
        simpl in trans, trans'.
        
        destruct label_x eqn : eq_label.
        { 
          clear -Hrec_short eq_label.
          unfold is_receive_plan in Hrec_short.
          simpl in Hrec_short.
          spec Hrec_short. intuition.
          congruence.
       }
       
        destruct input_x eqn : eq_input.
        2 : {
          unfold protocol_valid in Hprotocol_valid.
          unfold constrained_composite_valid in Hprotocol_valid.
          unfold free_composite_valid in Hprotocol_valid. 
          unfold vvalid in Hprotocol_valid.
          unfold valid in Hprotocol_valid.
          simpl in Hprotocol_valid.
          destruct Hprotocol_valid as [e [b [c d]]].
          intuition. 
        }
       
       assert (Hm : fst m = f). {
          clear -Hli eq_input.
          unfold incl in Hli.
          unfold get_message_providers_from_plan in Hli.
          unfold messages_a in Hli.
          rewrite map_app in Hli.
          rewrite cat_option_app in Hli.
          rewrite map_app in Hli.
          specialize (Hli (fst m)).
          spec Hli. {
            simpl.
            apply in_app_iff.
            right.
            intuition.
          }
          simpl in Hli.
          intuition.
       }
       
        split.
        + apply finite_protocol_plan_from_app_iff.
          split.
          * assumption.
          * unfold finite_protocol_plan_from.
            assert (protocol_transition X (existT (fun n : index => vlabel (IM_index n)) j receive)
                    (snd (apply_plan X s' a), Some m)
                    (state_update IM_index (snd (apply_plan X s' a)) j
                    (update_state (snd (apply_plan X s' a) j) (snd m) (fst m)), None)). {
             split.
             - destruct Hprotocol_trans as [Hprotocol_trans tmp].
               specialize (relevant_component_transition_lv res_long res_long') as Hrel.
               specialize (Hrel Hprs_long Hprs'_long (existT (fun n : index => vlabel (IM_index n)) j receive)).
               specialize (Hrel m).
               rewrite H1 in Hrel.
               apply Hrel.
               simpl.
               specialize (Iha_proj j).
               move Iha_proj at bottom.
               rewrite Hm.
               symmetry.
               rewrite <- H1.
               assumption.
               assumption.
            - unfold transition.
              unfold vlabel.
              unfold machine.
              simpl.
              reflexivity.
            }
            
            apply finite_ptrace_extend.
            apply finite_ptrace_empty.
            apply protocol_transition_destination in H10.
            assumption.
            assumption.
        + intros.
          specialize (Iha_proj i).
         * inversion trans.
           inversion trans'.
           destruct (decide (i = j)).
           -- rewrite e.
              rewrite state_update_eq.
              rewrite state_update_eq.
              rewrite e in Iha_proj.
              clear -Iha_proj Hprs_long Hprs'_long.
              destruct (decide ((fst m) = f)).
              ** rewrite e.
                 rewrite (@project_same index index_listing Hfinite).
                 rewrite (@project_same index index_listing Hfinite).
                 reflexivity.
                 all : (apply protocol_state_component_no_bottom; assumption).
              ** rewrite (@project_different index index_listing Hfinite).
                 rewrite (@project_different index index_listing Hfinite).
                 assumption.
                 intuition.
                 (apply protocol_state_component_no_bottom; assumption).
                 intuition.
                 (apply protocol_state_component_no_bottom; assumption).
          -- rewrite state_update_neq.
             rewrite state_update_neq.
             all : intuition.
    Qed.
    
    Definition get_receives_all
      (s : vstate X)
      (lfrom : set index) : vplan X :=
      let receive_fors := List.map (fun (i : index) => get_receives_for s (others i s) i) lfrom in
      List.concat receive_fors.
      
    Remark get_receives_all_info
      (s : vstate X)
      (lfrom : list index)
      (ai : vplan_item X)
      (Hin : In ai (get_receives_all s lfrom)) :
      let label := projT2 (label_a ai) in
      label = receive /\
      (exists (so : state) (from : index), (input_a ai = Some (from, so)) /\ In from lfrom /\ In (SimpObs Message' from so) (cobs_messages s from)).
    Proof.
      unfold get_receives_all in Hin.
      apply in_concat in Hin.
      destruct Hin as [smaller [Hin_smaller Hin_ai]].
      
      apply in_map_iff in Hin_smaller. 
      destruct Hin_smaller as [from [Hrec Hinfrom]].
      rewrite <- Hrec in Hin_ai.
      apply get_receives_for_info in Hin_ai.
      simpl in *.
      split;[intuition|].
      destruct Hin_ai as [_ [_ Hin_ai]].
      destruct Hin_ai as [so Hso].
      exists so. exists from.
      intuition.
    Qed.
   
    Lemma get_receives_all_protocol
      (s : vstate X)
      (lfrom : set index)
      (Hnodup : NoDup lfrom)
      (Hprs : protocol_state_prop X s) :
      let res := snd (apply_plan X s (get_receives_all s lfrom)) in 
      finite_protocol_plan_from X s (get_receives_all s lfrom) /\
      forall (f i : index), 
      In f lfrom -> 
      i <> f -> 
      In i (GH s) -> 
      project (res i) f = project (get_matching_state s i f) f. 
    Proof.
      induction lfrom using rev_ind; unfold get_receives_all.
      - split; simpl. 
        + apply finite_protocol_plan_empty. assumption.
        + intuition.
      - simpl.
        apply NoDup_rev in Hnodup.
        rewrite rev_unit in Hnodup.
        apply NoDup_cons_iff in Hnodup.
        destruct Hnodup as [notX Hnodup].
        apply NoDup_rev in Hnodup.
        rewrite rev_involutive in Hnodup.
        
        specialize (IHlfrom Hnodup).
        simpl in IHlfrom.
        
        destruct IHlfrom as [IHprotocol IHproject].
        rewrite map_app.
        rewrite concat_app.
        rewrite apply_plan_app; simpl.
        
        match goal with
        |- context[apply_plan X s ?a] => 
           destruct (apply_plan X s a) as [tr_long res_long] eqn : eq_long 
        end.
        
        match goal with
        |- context [apply_plan X res_long ?a] =>
           destruct (apply_plan X res_long a) as [tr_short res_short] eqn : eq_short
        end.
        
        rewrite app_nil_r in *.
        simpl.
        
        assert (res_short = snd (apply_plan X res_long (get_receives_for s (others x s) x))). {
          rewrite eq_short.
          intuition.
        }
        
        assert (res_long = snd (apply_plan X s (concat (map (fun i : index => get_receives_for s (others i s) i) lfrom)))). {
          match goal with
          |- context[apply_plan X s ?a] =>
             replace (apply_plan X s a) with (tr_long, res_long)
          end.
          intuition.
        }
        
        assert (Hrec_long':  is_receive_plan (get_receives_all s lfrom)). {
          unfold is_receive_plan. intros.
          apply get_receives_all_info in H1.
          intuition.
        }
        
        assert (Hrec_short : is_receive_plan (get_receives_for s (others x s) x)). {
          apply receive_for_is_receive_plan.
        }
        
        assert (Hprs_long : protocol_state_prop X res_long). {
          rewrite H0.
          apply apply_plan_last_protocol.
          assumption.
          assumption.
        }
        
        assert (Hx_after_long : forall (i : index), project (res_long i) x = project (s i) x). {
          intros.
          replace res_long with 
            (snd (apply_plan X s (concat (map (fun i : index => get_receives_for s (others i s) i) lfrom)))).
          apply receives_neq.
          assumption.
          assumption.
          assumption.
          
          intros contra.
          
          unfold get_message_providers_from_plan in contra.
          rewrite in_map_iff in contra.
          destruct contra as [m [Hfs Hinm]].
          unfold messages_a in Hinm.
          apply in_cat_option in Hinm.
          destruct Hinm as [Hom [Hinom Hsome]].
          rewrite in_map_iff in Hinom.
          destruct Hinom as [ai [Hinput Hinconcat]].
          rewrite in_concat in Hinconcat.
          destruct Hinconcat as [a [Hina Hina2]].
          apply in_map_iff in Hina.
          destruct Hina as [j [Heq_rec Heqfrom]].
          rewrite <- Heq_rec in Hina2.
          apply get_receives_for_info in Hina2.
          destruct Hina2 as [_ [Hina2 Hina2']].
          destruct Hina2' as [so [Hm Hso]].
          rewrite Hinput in Hm.
          rewrite Hsome in Hm.
          inversion Hm.
          rewrite H2 in Hfs. simpl in Hfs.
          subst j. 
          apply in_rev in Heqfrom.
          intuition.
        }
        
        assert (Hsource: finite_protocol_plan_from X s (get_receives_for s (others x s) x)). {
          apply get_receives_for_correct.
          assumption.
          apply NoDup_others.
          apply others_correct.
        }
        
        specialize (relevant_components_lv s res_long Hprs Hprs_long (get_receives_for s (others x s) x)) as Hrel.
        specialize (Hrel Hrec_short Hsource x).
        
        spec Hrel. apply message_providers_receive.
        
        spec Hrel. {
          intros.
          specialize (Hx_after_long i).
          symmetry.
          assumption.
        }
        
        simpl in Hrel.
        
        assert (Hfinite_short : finite_protocol_plan_from X res_long (get_receives_for s (others x s) x)). {
          intuition.
        }
        
        split.
        + apply finite_protocol_plan_from_app_iff.
          split.
          * unfold finite_protocol_plan_from in IHprotocol.
            replace tr_long with (fst (apply_plan X s (get_receives_all s lfrom))).
            assumption.
            unfold get_receives_all.
            replace (apply_plan X s (concat (map (fun i : index => get_receives_for s (others i s) i) lfrom))) with
            (tr_long, res_long). 
            intuition.
          * rewrite H0 in Hfinite_short.
            apply Hfinite_short.
        +
             intros.
             destruct (decide (f = x)).
              -- rewrite H.
                destruct Hrel as [_ Hrel].
                specialize (Hrel i).
                rewrite e.
                rewrite Hrel.
                apply get_receives_for_correct.
                assumption.
                apply NoDup_others.
                apply others_correct.
                unfold others.
                apply set_remove_3.
                intuition.
                subst f. intuition.
              -- apply in_app_iff in H1.
                simpl in H1.
                destruct H1.
                specialize (IHproject f i H1).
                spec IHproject. {
                  intuition.
                }
                spec IHproject. {
                  intuition.
                }
                rewrite <- IHproject.
                unfold get_receives_all.
                replace (snd (apply_plan X s (concat (map (fun i1 : index => get_receives_for s (others i1 s) i1) lfrom)))) with res_long.
                rewrite H.
                apply receives_neq.
                assumption.
                assumption.
                assumption.
                rewrite message_providers_receive.
                intros contra.
                simpl in contra.
                all : intuition.
    Qed.
    
    Definition receive_phase_plan (s : vstate X) := (get_receives_all s index_listing).
    Definition receive_phase (s : vstate X) := apply_plan X s (receive_phase_plan s).
    Definition receive_phase_result (s : vstate X) := snd (receive_phase s).
    Definition receive_phase_transitions (s : vstate X) := fst (receive_phase s).
    
    Lemma receive_phase_protocol
      (s : vstate X)
      (Hprs : protocol_state_prop X s):
      finite_protocol_plan_from X s (receive_phase_plan s).
    Proof.
      unfold receive_phase_plan.
      apply get_receives_all_protocol.
      apply (proj1 Hfinite).
      intuition.
    Qed.
    
    Remark receive_phase_result_protocol
      (s : vstate X)
      (Hprs : protocol_state_prop X s)
      (res_receive := receive_phase_result s) :
      protocol_state_prop X res_receive.
    Proof. 
      apply apply_plan_last_protocol.
      intuition.
      apply receive_phase_protocol.
      all : intuition.
    Qed.
  
    Lemma receive_phase_GE
      (s : vstate X)
      (Hprs : protocol_state_prop X s)
      (res_receive := receive_phase_result s) :
      set_eq (GE res_receive) (GE s).
    Proof.
      specialize (ep_plan s Hprs (receive_phase_plan s)) as Hep.
      spec Hep. apply receive_phase_protocol. intuition. 
      spec Hep. {
        intros.
        unfold receive_phase_plan in H.
        apply get_receives_all_info in H.
        split;[intuition|].
        destruct H as [_ H].
        destruct H as [so [from H]].
        exists so. exists from. intuition.
      }
      simpl in Hep.
      apply set_eq_comm.
      intuition.
    Qed.
  
    Remark receive_phase_future 
      (s : vstate X)
      (Hspr : protocol_state_prop _ s) :
      in_futures _ s (receive_phase_result s).
    Proof.
      unfold in_futures.
      exists (receive_phase_transitions s).
      split.
      apply receive_phase_protocol.
      assumption.
      unfold receive_phase_transitions.
      unfold receive_phase_result.
      apply apply_plan_last.
    Qed.
    
    Remark self_projections_same_after_receive_phase
      (s : vstate X)
      (Hpr : protocol_state_prop X s)
      (res_receive := receive_phase_result s) :
      forall (i : index), project (res_receive i) i = project (s i) i.
    Proof.
      intros.
      specialize (self_projections_same_after_receives s Hpr) as Hsame.
      specialize (Hsame (receive_phase_plan s)).
      spec Hsame. apply receive_phase_protocol. intuition.
  
      spec Hsame. {
        intros.
        unfold receive_phase_plan in H.
        apply get_receives_all_info in H.
        intuition.
      }
      specialize (Hsame i).
      intuition.
    Qed.
    
    Definition common_future (s : vstate X) := receive_phase_result (send_phase_result s).
    
    Lemma common_future_in_futures
      (s : vstate X)
      (Hpr : protocol_state_prop X s)
      (Hnf : no_component_fully_equivocating s (GH s)) :
      in_futures X s (common_future s).
    Proof.
      specialize (@in_futures_trans message X s (send_phase_result s) (common_future s)) as Htrans.
      apply Htrans.
      apply send_phase_future.
      intuition.
      intuition.
      unfold common_future.
      apply receive_phase_future.
      apply send_phase_result_protocol.
      all : intuition.
    Qed.
    
    Lemma common_future_no_extra_equivocation
      (s : vstate X)
      (Hpr : protocol_state_prop X s)
      (Hnf : no_component_fully_equivocating s (GH s)) :
      set_eq (GE (common_future s)) (GE s).
    Proof.
      apply set_eq_tran with (s2 := GE (send_phase_result s)).
      apply receive_phase_GE.
      apply send_phase_result_protocol.
      intuition. intuition.
      apply send_phase_GE.
      intuition. intuition.
    Qed.
    
    Remark common_future_result_protocol
      (s : vstate X)
      (Hpr : protocol_state_prop X s)
      (Hnf : no_component_fully_equivocating s (GH s))
      (res := common_future s) :
      protocol_state_prop X res.
    Proof.
      unfold res.
      unfold common_future.
      apply receive_phase_result_protocol.
      apply send_phase_result_protocol.
      all : intuition.
    Qed. 
    
    Corollary GH_eq1
      (s : vstate X)
      (Hpr : protocol_state_prop X s)
      (Hnf : no_component_fully_equivocating s (GH s))
      (res_send := send_phase_result s)
      (res := common_future s) :
      (GH s) = (GH res_send).
    Proof.
    Admitted.
    
    Corollary GH_eq2
      (s : vstate X)
      (Hpr : protocol_state_prop X s)
      (Hnf : no_component_fully_equivocating s (GH s))
      (res_send := send_phase_result s)
      (res := common_future s) :
      (GH s) = (GH res).
    Proof.
    Admitted.
    
    Corollary GH_eq3
      (s : vstate X)
      (Hpr : protocol_state_prop X s)
      (Hnf : no_component_fully_equivocating s (GH s))
      (res_send := send_phase_result s)
      (res := common_future s) :
      (GH res_send) = (GH res).
    Proof.
    Admitted.
   
  Lemma honest_receive_honest
    (s : vstate X)
    (Hpr : protocol_state_prop X s)
    (Hnf : no_component_fully_equivocating s (GH s))
    (res_send := send_phase_result s)
    (res := common_future s) :
    forall (i j : index), In i (GH res) -> In j (GH res) -> project (res i) j = project (res j) j.
  Proof.
    intros.
    destruct (decide (i = j));[subst i;intuition|].
      
    assert (Hsend_pr : protocol_state_prop X res_send). {
      apply send_phase_result_protocol.
      all : intuition.
    }
    
    assert (In i (GH s) /\ In j (GH s)) by (setoid_rewrite GH_eq2;intuition).
    assert (HiGH : In i (GH (send_phase_result s))) by (setoid_rewrite <- GH_eq1;intuition).
    
    specialize (get_receives_all_protocol (send_phase_result s) index_listing (proj1 Hfinite) Hsend_pr) as Hrec.
    simpl in Hrec. destruct Hrec as [Hrec_pr Hrec].
    specialize (Hrec j i). 
    spec Hrec. apply in_listing.
    specialize (Hrec n).
    unfold res in H.

    specialize (Hrec HiGH).
    unfold res at 1.
    unfold common_future.
    unfold receive_phase_result.
    unfold receive_phase.
    unfold receive_phase_plan.
    rewrite Hrec. 
    rewrite get_matching_state_for_honest.
    rewrite <- self_projections_same_after_receive_phase.
    intuition.
    1, 2 : intuition.
    setoid_rewrite <- GH_eq1; intuition.
  Qed.
  
  Definition hcobs (s : vstate X) := @wcobs (GH s) s.
  Definition hcobs_messages (s : vstate X) := @wcobs_messages (GH s) s.
  Definition hcobs_states (s : vstate X) := @wcobs_states (GH s) s.
  
  Definition HE (s : vstate X) := @wE (GH s) s.
  Definition HH (s : vstate X) := @wH (GH s) s.
  
  Definition LE (i : index) := (@wE [i]).
  Definition LH (i : index) := (@wH [i]).
  
  Lemma all_projections_old1
    (s : vstate X)
    (Hpr : protocol_state_prop X s)
    (Hnf : no_component_fully_equivocating s (GH s))
    (res_send := send_phase_result s)
    (res := common_future s) 
    (i j : index)
    (Hdif : i <> j)
    (Hi : In i (GH res)) :
    (project (res i) j = (s j) /\ (In j (GH res))) \/
    (exists (inter : index), In inter (GH res) /\
    project (s inter) j = project (res i) j).
  Proof.
    assert (Hspr: protocol_state_prop X res_send) by (apply send_phase_result_protocol;intuition).
    assert (In i (GH res_send)). {
      unfold res_send.
      rewrite GH_eq3; intuition.
    }
    
    assert (project (res i) j = project (get_matching_state (res_send) i j) j). {
      unfold res.
      unfold common_future.
      specialize (get_receives_all_protocol res_send index_listing (proj1 Hfinite) Hspr) as Hrec.
      destruct Hrec as [_ Hrec].
      specialize (Hrec j i (in_listing j)).
      spec Hrec. intuition.
      specialize (Hrec H).
      apply Hrec.
    }
    specialize (get_matching_state_correct2 res_send i j H) as Hinter.
    destruct Hinter as [inter [HinterGH Hmatch]].
    
    destruct (decide (inter = j)).
    - subst inter.
      left.
      rewrite Hmatch in H0.
      unfold res_send in H0.
      rewrite send_phase_result_projections in H0.
      2 , 3 : intuition.
      2 : {
        rewrite GH_eq1; intuition.
      }
      split.
      + intuition.
      + unfold res. rewrite <- GH_eq3; intuition.
    - right. 
      exists inter.
      split.
      + unfold res. rewrite <- GH_eq3; intuition.
      + assert (project (s inter) j = project (res_send inter) j). {
          specialize (non_self_projections_same_after_send_phase s Hpr Hnf inter j n).
          intuition.
        }
        rewrite Hmatch in H0.
        rewrite H0.
        intuition.
  Qed.
  
  Lemma all_projections_old2
    (s : vstate X)
    (Hpr : protocol_state_prop X s)
    (Hnf : no_component_fully_equivocating s (GH s))
    (res_send := send_phase_result s)
    (res := common_future s) 
    (i j : index)
    (Hi : In i (GH res))
    (Hk : ~ In j (GH res)) :
    exists (inter : index), In inter (GH res) /\
    project (s inter) j = project (res i) j.
  Proof.
    
    assert (Hdif : i <> j). {
      destruct (decide (i = j));[subst i;intuition|intuition].
    }
  
    assert (Hspr: protocol_state_prop X res_send) by (apply send_phase_result_protocol;intuition).
    assert (In i (GH res_send)). {
      unfold res_send.
      rewrite GH_eq3; intuition.
    }
    
    assert (project (res i) j = project (get_matching_state (res_send) i j) j). {
      unfold res.
      unfold common_future.
      specialize (get_receives_all_protocol res_send index_listing (proj1 Hfinite) Hspr) as Hrec.
      destruct Hrec as [_ Hrec].
      specialize (Hrec j i (in_listing j)).
      spec Hrec. intuition.
      specialize (Hrec H).
      apply Hrec.
    }
    specialize (get_matching_state_correct2 res_send i j H) as Hinter.
    destruct Hinter as [inter [HinterGH Hmatch]].
    
    assert (inter <> j). {
      destruct (decide (inter = j)).
      - subst inter.
        unfold res_send in HinterGH. 
        rewrite GH_eq3 in HinterGH; intuition.
      - intuition.
    } 
    
    exists inter.
    split.
    + unfold res. rewrite <- GH_eq3; intuition.
    + assert (project (s inter) j = project (res_send inter) j). {
        specialize (non_self_projections_same_after_send_phase s Hpr Hnf inter j H1).
        intuition.
      }
      rewrite Hmatch in H0.
      rewrite H0.
      intuition.
  Qed.
  
  Lemma all_message_observations_old
    (s : vstate X)
    (Hpr : protocol_state_prop X s)
    (Hnf : no_component_fully_equivocating s (GH s))
    (res_send := send_phase_result s)
    (res := common_future s) 
    (target : index)
    (Htarget : ~In target (GH res))
    (e : simp_lv_event) :
    In e (hcobs_messages res target) -> 
    In e (hcobs_messages s target).
  Proof.
    intros.
    assert (H' := H).
    apply cobs_single in H.
    destruct H as [k [Hink Hine]].
    
    assert (Hspr : protocol_state_prop X res_send). {
      apply send_phase_result_protocol; intuition.
    }
    
    assert (In k (GH res_send)). {
      unfold res_send.
      rewrite GH_eq3; intuition.
    }
    
    assert (Hdif : target <> k). {
      destruct (decide (k = target)).
      - subst k. intuition.
      - intuition.
    }
  
    apply (@unfold_simp_lv_observations index index_listing Hfinite) in Hine.
    2 : {
      apply protocol_state_component_no_bottom.
      apply common_future_result_protocol; intuition.
    }
    apply cobs_single.
    
    destruct Hine as [Hine|Hine].
    - specialize (all_projections_old2 s Hpr Hnf k target Hink Htarget) as Hinter.
      destruct Hinter as [inter [HinterGH Hproject]].
      exists inter.
      split.
      + rewrite GH_eq2; intuition.
      + unfold res in Hine.
        rewrite <- Hproject in Hine.
        apply refold_simp_lv_observations1.
        apply protocol_state_component_no_bottom; intuition.
        apply cobs_single in H'.
        destruct H' as [inter2 Hrest].
        destruct Hrest as [_ Hrest].
        apply (@in_message_observations_nb index index_listing Hfinite) in Hrest.
        rewrite Hine in Hrest. simpl in Hrest.
        intuition.
        intuition.
    - destruct Hine as [l Hinel].
      destruct (decide (k = l)).
      + subst l.
        unfold res in Hinel.
        unfold common_future in Hinel.
        rewrite self_projections_same_after_receive_phase in Hinel by intuition.
        rewrite send_phase_result_projections in Hinel.
        2, 3 : intuition.
        2 : (rewrite GH_eq2; intuition).
        exists k. 
        split. 
        * rewrite GH_eq1; intuition.
        * intuition.
      + specialize (all_projections_old1 s Hpr Hnf k l n Hink) as Hinter.
        destruct Hinter.
        * unfold res in Hinel. 
          destruct H0 as [H0 HlGH].
          rewrite H0 in Hinel.
          exists l.
          rewrite GH_eq2; intuition.
        * destruct H0 as [inter2 [Hinter2GH Hproj]].
          unfold res in Hinel.
          rewrite <- Hproj in Hinel.
          exists inter2.
          split.
          -- rewrite GH_eq2; intuition.
          -- apply (@refold_simp_lv_observations2 index index_listing Hfinite).
             apply protocol_state_component_no_bottom.
             intuition.
             exists l. intuition.
  Qed.
  
  Lemma all_message_observations_in_new_projections
    (s : vstate X)
    (Hpr : protocol_state_prop X s)
    (Hnf : no_component_fully_equivocating s (GH s))
    (res_send := send_phase_result s)
    (res := common_future s) 
    (i target : index)
    (Hi : In i (GH res))
    (Htarget : ~In target (GH res))
    (e : simp_lv_event) :
    In e (hcobs_messages s target) -> 
    In e (simp_lv_message_observations (res i) target).
  Proof.
    intros.
    apply cobs_single in H.
    destruct H as [j [HjGH Hine]].
    apply (@refold_simp_lv_observations2 index index_listing Hfinite).
    apply protocol_state_component_no_bottom; apply common_future_result_protocol; intuition.
    exists j.
    specialize (honest_receive_honest s Hpr Hnf i j Hi) as Hhonest.
    spec Hhonest. rewrite <- GH_eq2; intuition.
    unfold res. rewrite Hhonest.
    unfold common_future.
    rewrite self_projections_same_after_receive_phase by (apply send_phase_result_protocol;intuition).
    rewrite send_phase_result_projections; intuition.
  Qed.
  
  Lemma local_and_honest
    (s : vstate X)
    (Hpr : protocol_state_prop X s)
    (Hnf : no_component_fully_equivocating s (GH s))
    (res_send := send_phase_result s)
    (res := common_future s) 
    (i : index)
    (Hi : In i (GH res)) : 
    set_eq (HE res) (LE i res).
  Proof.
    apply set_eq_extract_forall.
    intros v.
    split; intros.
    - assert (Hdif : ~ In v (GH res)). {
        admit.
      }
      unfold HE in H.
      unfold LE.
      apply GE_direct in H.
      unfold cequiv_evidence in H.
      unfold equivocation_evidence in H.
      setoid_rewrite hbo_cobs in H.
      
      destruct H as [e1 [He1 [He1' [e2 [He2 [He2']]]]]].
      setoid_rewrite cobs_messages_states in He1.
      setoid_rewrite cobs_messages_states in He2.
      
      apply set_union_iff in He1.
      apply set_union_iff in He2.
      
      destruct He1 as [He1|He1].
      + unfold wcobs_states in He1.
        apply set_union_in_iterated in He1.
        rewrite Exists_exists in He1.
        destruct He1 as [le [Heq_le Hin_e1]].
        apply in_map_iff in Heq_le.
        destruct Heq_le as [j [Heqj Hinj]].
        unfold simp_lv_state_observations in Heqj.
        inversion He1'.
        rewrite H1 in Heqj.
        destruct (decide (v = j));[subst v;intuition|].
        subst le. intuition.
     + destruct He2 as [He2|He2].
       * unfold wcobs_states in He2.
         apply set_union_in_iterated in He2.
         rewrite Exists_exists in He2.
         destruct He2 as [le [Heq_le Hin_e2]].
         apply in_map_iff in Heq_le.
         destruct Heq_le as [j [Heqj Hinj]].
         unfold simp_lv_state_observations in Heqj.
         inversion He2'.
         rewrite H1 in Heqj.
         destruct (decide (v = j));[subst v;intuition|].
         subst le. intuition.
       * apply GE_direct.
         unfold cequiv_evidence.
         unfold equivocation_evidence.
         setoid_rewrite hbo_cobs.
         inversion He1'.
         inversion He2'.
         exists e1.
         split.
         -- apply all_message_observations_old in He1.
            apply all_message_observations_in_new_projections with (i := i) in He1.
            unfold wcobs. unfold composite_state_events_fn. simpl. unfold Hstate_events_fn.
            unfold res. apply in_simp_lv_message_observations'. intuition.
            intuition. intuition. intuition. rewrite H1.
            intuition. intuition. intuition. rewrite H1. intuition.
         -- split;[intuition|].
            exists e2.
            split.
            ++ apply all_message_observations_old in He2.
               apply all_message_observations_in_new_projections with (i := i) in He2.
               unfold wcobs. unfold composite_state_events_fn. simpl. unfold Hstate_events_fn.
               unfold res. apply in_simp_lv_message_observations'. intuition.
               intuition. intuition. intuition. rewrite H2.
               intuition. intuition. intuition. rewrite H2. intuition.
            ++ rewrite He2'. rewrite H1. intuition.
    - assert (Hdif : i <> v). {
        admit.
      }
      unfold LE in H. apply GE_direct in H.
      unfold cequiv_evidence in H.
      unfold equivocation_evidence in H.
      setoid_rewrite hbo_cobs in H.
      destruct H as [e1 [He1 [He1' [e2 [He2 [He2']]]]]].
      unfold HE.
      apply GE_direct.
      unfold cequiv_evidence.
      unfold equivocation_evidence.
      setoid_rewrite hbo_cobs.
      
      exists e1.
      split. 
      + apply in_cobs_messages'.
        apply cobs_single. exists i. split;[intuition|].
        unfold wcobs in He1. unfold composite_state_events_fn in He1. simpl in He1.
        unfold Hstate_events_fn in He1.
        unfold simp_lv_observations in He1.
        apply set_union_iff in He1.
        destruct He1;[intuition|].
        unfold simp_lv_state_observations in H0.
        inversion He1'.
        rewrite H2 in H0.
        rewrite decide_False in H0 by intuition.
        intuition.
      + split;[intuition|].
        exists e2.
        split.
        * apply in_cobs_messages'.
          apply cobs_single. exists i. split;[intuition|].
          unfold wcobs in He2. unfold composite_state_events_fn in He2. simpl in He2.
          unfold Hstate_events_fn in He2.
          unfold simp_lv_observations in He2.
          apply set_union_iff in He2.
          destruct He2;[intuition|].
          unfold simp_lv_state_observations in H0.
          inversion He2'.
          rewrite H2 in H0.
          rewrite decide_False in H0 by intuition.
          intuition.
        * split;[intuition|].
          intuition.
  Admitted.
 
  Lemma honest_hh_projections_comparable
    (s : vstate X)
    (Hpr : protocol_state_prop X s)
    (h1 h2 hh : index)
    (Hgh : In h1 (GH s) /\ In h2 (GH s))
    (Hhh : In hh (HH s)) :
    comparable (state_lt_ext hh) (project (s h1) hh) (project (s h2) hh).
  Proof.
    unfold comparable.
    destruct (decide (project (s h1) hh = project (s h2) hh));[left;intuition|].
    right.
    
    destruct (project (s h1) hh) eqn : eq1.
    - left. unfold state_lt_ext. intuition.
    - destruct (project (s h2) hh) eqn : eq2.
      + right. unfold state_lt_ext. intuition.
      + rewrite <- eq1. rewrite <- eq2.
        
        assert (Hcomp : comparable (state_lt' hh) (project (s h1) hh) (project (s h2) hh)). {
          destruct (decide (comparable (state_lt' hh) (project (s h1) hh) (project (s h2) hh)));[intuition|].
          assert (In hh (HE s)). {
            unfold HE.
            apply GE_direct.
            unfold cequiv_evidence.
            unfold equivocation_evidence.
            setoid_rewrite hbo_cobs.
            
            exists (SimpObs Message' hh (project (s h1) hh)).
            simpl. split.
            - apply in_cobs_messages'.
              apply cobs_single. 
              exists h1. split;[intuition|].
              apply refold_simp_lv_observations1. 
              apply protocol_state_component_no_bottom; intuition.
              intuition congruence. intuition.
            - split;[simpl;intuition|].
              exists (SimpObs Message' hh (project (s h2) hh)).
              simpl. split.
              + apply in_cobs_messages'.
                apply cobs_single. 
                exists h2. split;[intuition|].
                apply refold_simp_lv_observations1. 
                apply protocol_state_component_no_bottom; intuition.
                intuition congruence. intuition.
              + split;[simpl;intuition|].
                intros contra.
                unfold comparable in contra.
                unfold simp_lv_event_lt in contra.
                rewrite decide_True in contra by intuition.
                rewrite decide_True in contra by intuition.
                destruct contra.
                * inversion H. intuition congruence.
                * unfold comparable in n0.
                  contradict n0.
                  right. intuition.
          }
          unfold HH in Hhh.
          apply wH_wE' in Hhh.
          unfold HE in H. intuition.
        }
        
        unfold comparable in Hcomp.
        destruct Hcomp;[intuition congruence|].
        destruct H.
        * left. unfold state_lt_ext. intuition.
        * right. unfold state_lt_ext. intuition.
  Qed.
 
  Lemma comparable_projections_match
    (s : vstate X)
    (Hpr : protocol_state_prop X s)
    (h1 h2 hh : index)
    (Hgh : In h1 (GH s) /\ In h2 (GH s))
    (Hhh : In hh (HH s)) 
    (projh1 := project (get_matching_state s h1 hh) hh)
    (projh2 := project (get_matching_state s h2 hh) hh) :
    projh1 = projh2.
  Proof.
    
    specialize (get_matching_state_correct2 s h1 hh) as Hmatch1.
    specialize (get_matching_state_correct2 s h2 hh) as Hmatch2.
    spec Hmatch1. intuition. spec Hmatch2. intuition.
    destruct Hmatch1 as [i [GHi Hmatch1]].
    destruct Hmatch2 as [j [GHj Hmatch2]].
    
    assert (Hcomp': comparable (state_lt_ext hh) projh1 projh2). {
      unfold projh1, projh2.
      rewrite Hmatch1. rewrite Hmatch2.
      apply honest_hh_projections_comparable; intuition.
    }
    
    unfold projh1 in *.
    unfold projh2 in *.
    specialize (get_matching_state_correct3 s h1 hh) as Htop1.
    specialize (get_matching_state_correct3 s h2 hh) as Htop2.
    spec Htop1. intuition. spec Htop2. intuition.
    
    unfold comparable in Hcomp'.
    destruct Hcomp' as [|Hcomp'];[intuition|].
    destruct Hcomp'.
    - unfold get_topmost_candidates in Htop1.
      unfold get_maximal_elements in Htop1.
      apply filter_In in Htop1.
      destruct Htop1 as [_ Htop1].
      rewrite forallb_forall in Htop1.
      specialize (Htop1 (s j)).
      spec Htop1.
      apply in_map_iff. exists j. intuition.
      rewrite negb_true_iff in Htop1.
      rewrite bool_decide_eq_false in Htop1.
      rewrite Hmatch2 in H.
      intuition.
    - unfold get_topmost_candidates in Htop2.
      unfold get_maximal_elements in Htop2.
      apply filter_In in Htop2.
      destruct Htop2 as [_ Htop2].
      rewrite forallb_forall in Htop2.
      specialize (Htop2 (s i)).
      spec Htop2.
      apply in_map_iff. exists i. intuition.
      rewrite negb_true_iff in Htop2.
      rewrite bool_decide_eq_false in Htop2.
      rewrite Hmatch1 in H.
      intuition.
   Qed.
  
  Lemma honest_equiv_proj_same
    (s : vstate X)
    (Hpr : protocol_state_prop X s)
    (Hnf : no_component_fully_equivocating s (GH s))
    (res_send := send_phase_result s)
    (res := common_future s) :
    forall (h1 h2 hh : index), 
    In h1 (GH res) ->
    In h2 (GH res) -> 
    In hh (HH res) ->
    project (res h1) hh = project (res h2) hh.
  Proof.
    intros.
    
    destruct (decide (h1 = hh)).
    subst hh.
    specialize (honest_receive_honest s Hpr Hnf h2 h1).
    intuition.
    destruct (decide (h2 = hh)).
    subst hh.
    specialize (honest_receive_honest s Hpr Hnf h1 h2).
    intuition.
    
    destruct (decide (project (res h1) hh = project (res h2) hh));[intuition|]. 
    exfalso.
    
    specialize (get_receives_all_protocol res_send index_listing (proj1 Hfinite)) as Hmatch.
    spec Hmatch. apply send_phase_result_protocol. intuition. intuition.
    destruct Hmatch as [_ Hmatch].
    
    specialize (Hmatch hh h1) as Hmatch1. 
    spec Hmatch1. apply in_listing. spec Hmatch1. intuition.
    spec Hmatch1. unfold res_send. rewrite GH_eq3 by intuition. intuition.
    specialize (Hmatch hh h2) as Hmatch2. 
    spec Hmatch2. apply in_listing. spec Hmatch2. intuition.
    spec Hmatch2. unfold res_send. rewrite GH_eq3 by intuition. intuition.
    
    unfold res in n1. unfold common_future in n1. unfold receive_phase_result in n1.
    unfold res_send in Hmatch1, Hmatch2.
    unfold receive_phase in n1.
    unfold receive_phase_plan in n1.
    rewrite Hmatch1 in n1.
    rewrite Hmatch2 in n1.
    
    specialize (comparable_projections_match res_send) as Hcomp.
    spec Hcomp. apply send_phase_result_protocol; intuition.
    specialize (Hcomp h1 h2 hh).
    spec Hcomp. {
      unfold res_send.
      rewrite GH_eq3 by intuition.
      unfold res in H, H0. intuition.
    }
    spec Hcomp. {
      admit.
    }
    intuition.
  Admitted.
    
     
End Composition.
