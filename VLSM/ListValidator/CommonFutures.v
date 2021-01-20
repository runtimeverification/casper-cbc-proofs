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
  (Hstate_validators := fun (i : index) => (fun (s : vstate (IM_index i)) => index_listing))
  (Hbasic := fun (i : index) => @simp_lv_basic_equivocation index i index_listing Hfinite idec Mindex Rindex).
  
  Definition get_message_providers_from_plan
   (a : vplan X) : list index :=
    List.map fst (messages_a X a).
  
  Definition component_list (s : vstate X) (li : list index) :=
    List.map s li.
  
  Program Instance lv_composed_observable_events :
     observable_events (vstate X) simp_lv_event := 
     composite_state_observable_events_instance
     index_listing
     IM_index
     Hstate_events_fn
     Hstate_validators.
  
  Check @composite_observable_events_equivocation_evidence.
  
  Definition ce := 
  @composite_observable_events_equivocation_evidence
    message index simp_lv_event
    decide_eq
    index index_listing IM_index
    Hstate_events_fn
    Hstate_validators
    decide_eq
    simp_lv_event_lt
    simp_lv_event_lt_dec
    get_simp_event_subject_some.
    
  Check @composite_observable_events_equivocation_evidence_dec.
  
  Definition GH (s : vstate X) : set index := 
    List.filter (fun i : index => negb (
    @bool_decide _ (@composite_observable_events_equivocation_evidence_dec
      message index simp_lv_event
      decide_eq
      index index_listing IM_index
      Hstate_events_fn
      Hstate_validators
      decide_eq
      simp_lv_event_lt
      simp_lv_event_lt_dec
      get_simp_event_subject_some s i))) index_listing.
    
  Definition GE (s : vstate X) : set index := 
    List.filter (fun i : index => 
    @bool_decide _ (@composite_observable_events_equivocation_evidence_dec
      message index simp_lv_event
      decide_eq
      index index_listing IM_index
      Hstate_events_fn
      Hstate_validators
      decide_eq
      simp_lv_event_lt
      simp_lv_event_lt_dec
      get_simp_event_subject_some s i)) index_listing.
  
  (*
  Definition ce' (s : vstate X) := @composed_witness_observation_based_equivocation_evidence
    message index lv_event
    decide_eq 
    lv_event_lt
    lv_event_lt_dec
    get_event_subject_some
    index IM_index _ (GH s).
 
  Definition LH (s : vstate X) : set index :=
    List.filter (fun i : index => negb (
    @bool_decide _ (
      @observable_events_equivocation_evidence_dec 
      (vstate X) index lv_event _ 
      (composed_complete_observations_witness_set (GH s)) 
      _ lv_event_lt lv_event_lt_dec 
      get_event_subject_some 
      s i))) index_listing.
  
  Definition LE (s : vstate X) : set index :=
    List.filter (fun i : index => 
    @bool_decide _ (
      @observable_events_equivocation_evidence_dec 
      (vstate X) index lv_event _ 
      (composed_complete_observations_witness_set (GH s)) 
      _ lv_event_lt lv_event_lt_dec 
      get_event_subject_some 
      s i)) index_listing. *)
  
  Check @composite_state_events_fn.
  
  Definition cobs := (composite_state_events_fn index_listing IM_index Hstate_events_fn).
  
  Definition cobs_messages 
    (s : vstate X)
    (target : index) :=
  fold_right (set_union decide_eq) [] (List.map (fun (i : index) => (simp_lv_message_observations (s i) target)) index_listing).
  
  Lemma in_cobs_messages
    (s : vstate X)
    (target : index)
    (e : simp_lv_event)
    (Hin : In e (cobs_messages s target)) :
    get_simp_event_type e = Message'.
  Proof.
    unfold cobs_messages in Hin.
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
  
  Definition cobs_states 
    (s : vstate X)
    (target : index) : set simp_lv_event :=
    fold_right (set_union decide_eq) [] (List.map (fun (i : index) => (@simp_lv_state_observations index i index_listing _) (s i) target) index_listing).
  
  Lemma in_cobs_states
    (s : vstate X)
    (target : index)
    (e : simp_lv_event)
    (Hin : In e (cobs_states s target)) :
    get_simp_event_type e = State'.
  Proof.
    unfold cobs_messages in Hin.
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
  
  Lemma cobs_messages_states
    (s : vstate X)
    (target : index) :
    set_eq (cobs s target) (set_union decide_eq (cobs_states s target) (cobs_messages s target)).
  Proof.
    unfold cobs.
    unfold composite_state_events_fn.
    unfold cobs_states.
    unfold cobs_messages.
    remember (map (fun i : index => Hstate_events_fn i (s i) target) index_listing) as ss.
    specialize (@set_union_iterated_part (@simp_lv_event index index_listing) _ ss) as Hpart.
  Admitted.
  
  Lemma in_cobs_and_message
    (s : vstate X)
    (target : index)
    (e : simp_lv_event)
    (Hm : get_simp_event_type e = Message')
    (Hin : In e (cobs s target)) :
    In e (cobs_messages s target).
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
    (Hin : In e (cobs_states s target)) :
    In e (cobs s target).
  Proof.
    setoid_rewrite cobs_messages_states.
    apply set_union_iff.
    left. intuition.
  Qed.
  
  Lemma in_cobs_messages'
    (s : vstate X)
    (target : index)
    (e : simp_lv_event)
    (Hin : In e (cobs_messages s target)) :
    In e (cobs s target).
  Proof.
    setoid_rewrite cobs_messages_states.
    apply set_union_iff.
    right. intuition.
  Qed.
  
  Definition obs 
    (i : index) 
    := (@lv_observations index i index_listing _).
  
  Definition cequiv_evidence
    := (@equivocation_evidence 
    (vstate X) index simp_lv_event 
    _ decide_eq 
    simp_lv_event_lt simp_lv_event_lt_dec 
    get_simp_event_subject_some ce).
    
  Check cequiv_evidence.
  
  Lemma unique_state_observation 
    (s : vstate X)
    (i : index)
    (e : simp_lv_event)
    (Hin : In e (cobs_states s i)) : 
    e = SimpObs State' i (s i).
  Proof.
    unfold cobs in Hin.
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
    (i : index) :
    In (SimpObs State' i (s i)) (cobs_states s i).
  Proof.
    unfold cobs_states.
    apply set_union_in_iterated.
    rewrite Exists_exists.
    exists (@simp_lv_state_observations index i index_listing _ (s i) i).
    split.
    - apply in_map_iff.
      exists i.
      split;[intuition|apply ((proj2 Hfinite) i)].
    - unfold simp_lv_state_observations.
      rewrite decide_True.
      all : intuition.
  Qed.
    
  
  Lemma GE_direct 
    (s : vstate X)
    (i : index) :
    In i (GE s) <-> (cequiv_evidence s i).
  Proof.
    split; intros.
    - unfold GE in H.
      unfold GH in H.
      apply filter_In in H.
      destruct H as [_ H].
      apply bool_decide_eq_true in H.
      intuition.
    - unfold GE.
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
    In e (cobs s (get_simp_event_subject e)).
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
      unfold cobs.
      unfold composite_state_events_fn.
      rewrite <- Heqle in Hine.
      intuition.
    - apply set_union_in_iterated.
      rewrite Exists_exists.
      exists (cobs s (get_simp_event_subject e)).
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
             split;[intuition|apply ((proj2 Hfinite) i0)].
          -- apply ((proj2 Hfinite) (get_simp_event_subject e)).
     + intuition.
  Qed.
  
  Lemma cobs_single
    (s : vstate X)
    (target : index)
    (e : simp_lv_event) :
    In e (cobs_messages s target) <->
    exists (i : index), (In e (simp_lv_message_observations (s i) target)).
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
      + apply in_map_iff. exists i. split;[intuition|apply ((proj2 Hfinite) i)].
      + intuition.
  Qed.
  
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
        apply (@in_message_observations_nb index index_listing Hfinite) in Hhave.
        all : intuition.
    }
    unfold incl.
    intros e.
    intros H.
    apply cobs_single in H.
    destruct H as [k Hink].
    destruct (decide (k = i)).
    - subst k.
      unfold s' in Hink.
      rewrite state_update_eq in Hink.
      destruct (decide (j = target)).
      + subst target.
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
          -- apply in_cobs_and_message in Hhave.
             apply cobs_single in Hhave. 
             destruct Hhave as [l Hhave].
             apply cobs_single.
             exists l.
             apply (@message_cross_observations index index_listing Hfinite) with (e1 := (SimpObs Message' j so)) (i := j).
             all : intuition.
       * destruct Hink;[|intuition].
         rewrite <- H.
         apply in_cobs_and_message in Hhave.
         all : intuition.
   
      + apply (@new_incl_rest_diff index index_listing Hfinite) in Hink.
        2 : {
          split. apply Hsnb; intuition. intuition.
        }
        2 : intuition. 
        
        apply set_union_iff in Hink.
        destruct Hink as [Hink|Hink]. 
        apply cobs_single.
        exists i.
        intuition.
        apply in_cobs_and_message in Hhave.
        2 : intuition.  
        apply cobs_single in Hhave.
        destruct Hhave as [l Hhave].
        apply cobs_single.
        exists l.
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
        apply (@new_incl_rest_diff index index_listing Hfinite) in H.
        apply set_union_iff in H.
        destruct H; (apply cobs_single; exists i; intuition).
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
        apply (@old_incl_new index index_listing Hfinite) with (so := (s i)) (i := i) in H. 
        apply cobs_single.
        exists i.
        unfold s'.
        rewrite state_update_eq.
        rewrite cons_clean_message_obs with (b0 := b) in H.
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
        apply (@new_incl_rest_same index index_listing Hfinite) in H.
        apply set_union_iff in H.
        destruct H as [H|H];[|right;intuition].
        apply set_union_iff in H.
        destruct H; left; apply cobs_single; exists i; intuition.
        split; apply Hsnb.
        intuition.
      + left.
        unfold s' in H.
        rewrite state_update_neq in H by intuition.
        apply cobs_single. exists k. intuition.
    - apply set_union_iff in H.
      destruct H as [H | H].
      + apply cobs_single in H.
        destruct H as [k H].
        destruct (decide (i = k)).
        * subst k. 
          apply (@old_incl_new index index_listing Hfinite) with (so := (s i)) (i := i) in H.
          apply cobs_single.
          exists i.
          unfold s'.
          rewrite state_update_eq.
          rewrite cons_clean_message_obs with (b0 := b) in H.
          intuition.
          split; apply Hsnb.
          intuition.
        * apply cobs_single.
          exists k.
          unfold s'.
          rewrite state_update_neq.
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
        destruct Hhave as [k Hhave].
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
        destruct Hhave as [k Hhave].
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

  Lemma GH_GE'
    (s : vstate X)
    (i : index) :
    In i (GH s) <-> ~ In i (GE s).
  Proof.
    unfold GH.
    unfold GE.
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
  
  Lemma GH_GE
    (s : vstate X) :
    set_eq (GH s) (set_diff decide_eq index_listing (GE s)).
  Proof.
    apply set_eq_extract_forall.
    intros i.
    split; intros H.
    - apply set_diff_intro.
      apply (proj2 Hfinite i).
      apply GH_GE' in H.
      intuition.
    - apply set_diff_iff in H.
      destruct H as [_ H].
      apply GH_GE'.
      intuition. 
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
  
  Definition phase_one_plan (s : vstate X) : vplan X :=
    chain_updates (GH s) s.
 
  Definition phase_one (s : vstate X) : list (vtransition_item X) * vstate X :=
    apply_plan X s (phase_one_plan s).
  
  Definition phase_one_res 
    (s : vstate X) :=
    snd (phase_one s).
 
  Definition phase_one_transitions
    (s : vstate X) :=
    fst (phase_one s).
  
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
          rewrite <- GH_GE'.
          apply Hhonest. intuition.
      }
      
      spec IHli. {
        unfold incl in *.
        intros idx Hidx.
        apply GH_GE'.
        specialize (Hhonest idx).
        setoid_rewrite HGEs'.
        apply GH_GE'.
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
              apply GH_GE'.
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
  
  Lemma phase_one_protocol
    (s : vstate X)
    (Hprs : protocol_state_prop X s)
    (Hnf : no_component_fully_equivocating s (GH s)) :
    finite_protocol_plan_from X s (phase_one_plan s).
  Proof.
    unfold phase_one_plan.
    apply chain_updates_protocol.
    assumption.
    apply GH_NoDup.
    intuition.
    intuition.
  Qed.
  
  Lemma phase_one_future 
    (s : vstate X)
    (Hnf : no_component_fully_equivocating s (GH s))
    (Hspr : protocol_state_prop _ s) :
    in_futures _ s (phase_one_res s).
  Proof.
    unfold in_futures.
    exists (phase_one_transitions s).
    split.
    apply phase_one_protocol.
    assumption.
    assumption.
    unfold phase_one_transitions.
    unfold phase_one_res.
    apply apply_plan_last.
  Qed.
  
  Lemma phase_one_projections 
    (s : vstate X)
    (Hprss : protocol_state_prop _ s)
    (Hnf : no_component_fully_equivocating s (GH s))
    (i : index)
    (Hin : In i (GH s))
    (s' := phase_one_res s) :
    project (s' i) i = (s i).
  Proof.
    apply chain_updates_protocol.
    intuition.
    apply GH_NoDup.
    all : intuition.
  Qed. 
  
  (*
  Lemma everything_in_projections 
    (s : vstate X)
    (Hprs : protocol_state_prop _ s)
    (Hnf : no_component_fully_equivocating s index_listing)
    (li : list index)
    (s' := phase_one_res s) :
    set_eq 
    (unite_observations (component_list s li))
    (unite_observations (zip_apply (List.map project (component_list s' li)) li)).
  Proof.
    split.
    - unfold incl.
      intros.
      unfold unite_observations in H.
      apply set_union_in_iterated in H.
      apply set_union_in_iterated.
      rewrite Exists_exists in *.
      destruct H as [x [Hinx Hinax]].
      rewrite in_map_iff in Hinx.
      destruct Hinx as [si [Heq Hinsi]].
      unfold component_list in Hinsi.
      rewrite in_map_iff in Hinsi.
      destruct Hinsi as [i [Heqi Hini]].
      exists (complete_observations (project (s' i) i)).
      split.
      rewrite in_map_iff.
      exists (project (s' i) i).
      split.
      reflexivity.
      apply In_nth_error in Hini.
      destruct Hini as [n Hn].
      apply in_zip_apply_if with (n0 := n).
      remember (component_list s' li) as f.
      rewrite nth_error_map.
      rewrite Heqf.
      unfold component_list.
      rewrite nth_error_map.
      rewrite Hn.
      simpl.
      reflexivity.
      assumption.
      unfold s'.
      rewrite phase_one_projections.
      rewrite Heqi.
      rewrite Heq.
      all : assumption.
    - unfold incl.
      intros.
      unfold unite_observations in *.
      apply set_union_in_iterated in H.
      apply set_union_in_iterated.
      rewrite Exists_exists in H.
      destruct H as [x [Hinx Hina]].
      rewrite in_map_iff in Hinx.
      destruct Hinx as [x0 [Heqx Hinx]].
      rewrite Exists_exists.
      apply in_zip_apply_if2 in Hinx.
      destruct Hinx as [pr [i [n H]]].
      exists (complete_observations (s i)).
      split.
      rewrite in_map_iff.
      exists (s i).
      intuition.
      unfold component_list.
      rewrite in_map_iff.
      exists i.
      intuition.
      apply nth_error_In in H.
      assumption.
      rewrite <- Heqx in Hina.
      assert (x0 = (s i)). {
        destruct H as [alfa [beta caroten]].
        rewrite nth_error_map in alfa.
        unfold component_list in alfa.
        rewrite nth_error_map in alfa.
        rewrite beta in alfa.
        simpl in alfa.
        inversion alfa.
        rewrite <- H0 in caroten.
        rewrite <- caroten.
        apply phase_one_projections.
        assumption.
        assumption.
      }
      rewrite H0 in Hina.
      assumption.
  Qed. *)
  
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
    (project (res to) from = project (s' inter) from) /\ incl (GE res) (GE s).
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
    
      repeat split.
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
      + destruct IHa as [_ IHa].
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
      + destruct IHa as [Iha1 [Iha2 Iha3]].
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
        
        apply incl_tran with (m := GE res_short).
        * rewrite <- H1 in Iha3 at 2.
          rewrite H2 in Iha3.
          intuition.
        * rewrite H1.
          specialize (GE_existing_different s Hpr sa to from Hdif Hecs) as Hexisting.
          
          
          assert (s0 = (state_update IM_index s to (update_state (s to) sa from))). {
            destruct H as [_ H].
            unfold transition in H.
            simpl in H. unfold vtransition in H. unfold transition in H. simpl in H.
            inversion Hh.
            rewrite <- H4 in H.
            inversion H.
            intuition.
          }
          
          rewrite H3.
          apply Hexisting.
          rewrite <- Hhist in Hinsa.
          apply (@in_history_in_observations index index_listing Hfinite) in Hinsa.
          apply in_cobs_messages'.
          apply cobs_single.
          exists inter.
          intuition.
    Qed.
   
    Definition get_candidates 
      (s : vstate X) :
      list state 
      :=
    component_list s (GH s).
    
    Definition get_topmost_candidates
      (s : vstate X)
      (target : index) :
      list state 
      :=
      get_maximal_elements (fun s s' => state_ltb' target (project s target) (project s' target)) (get_candidates s).
      
    Definition get_matching_state
      (s : vstate X)
      (to from : index) : state :=
      let candidates := (get_topmost_candidates s from) in
      let found := List.find (fun s' => state_ltb' from (project (s to) from) s') candidates in
      match found with
      | Some s' => s'
      | None => (s to)
      end.
      
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
      destruct (find (fun s' : state => state_ltb' from (project (s to) from) s')
               (get_topmost_candidates s from)) eqn : eq_find.
      - apply find_some in eq_find.
        destruct eq_find as [_ eq_find].
        unfold sync in contra.
        destruct (complete_suffix (get_history s0 from) (get_history (s to) from)) eqn : eq_suf.
        discriminate contra.
        unfold state_ltb' in eq_find.
        apply in_correct in eq_find.
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
      project (res to) from = project s' from /\ incl (GE res) (GE s).
    Proof.
      simpl.
      unfold get_matching_plan.
      rewrite Hmatch.
      destruct (sync s s' to from) eqn : eq_sync.
      - unfold sync in eq_sync.
        destruct (complete_suffix (get_history s' from) (get_history (s to) from)) eqn : eq_suf.
        2 : discriminate eq_sync.
        assert (eq_suf_original := eq_suf).
        apply complete_suffix_correct in eq_suf.
        inversion eq_sync.
        specialize (one_sender_receive_protocol s s Hprs Hprs to) as Hone.
        unfold get_matching_state in Hmatch.
        destruct (find (fun s' : state => state_ltb' from (project (s to) from) s')
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
    
    Lemma get_matching_plan_index
      (s : vstate X)
      (from to : index)
      (ai : plan_item)
      (Hin : In ai (get_matching_plan s from to)) :
      (projT1 (label_a ai) = to).
    Proof.
      unfold get_matching_plan in Hin.
      remember (get_matching_state s to from) as s0.
      destruct (sync s s0 to from) eqn : eq_sync.
        + unfold sync in eq_sync.
          destruct (complete_suffix (get_history s0 from) (get_history (s to) from)).
          inversion eq_sync.
          unfold sync_plan in H0.
          rewrite <- H0 in Hin.
          apply in_map_iff in Hin.
          destruct Hin as [x [Hlift Hinx]].
          unfold lift_to_composite_plan_item in Hlift.
          rewrite <- Hlift.
          destruct x. simpl. reflexivity.
          discriminate eq_sync.
        + contradict Hin.
    Qed.
    
    Definition get_receives_for
      (s : vstate X)
      (li : list index)
      (from : index) : vplan X :=
      let matching_plans := List.map (get_matching_plan s from) li in
      List.concat matching_plans.
      
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
      induction li; intros.
      - unfold get_receives_for. simpl.
        split.
        apply finite_protocol_plan_empty.
        assumption.
        intuition.
      - unfold get_receives_for.
        rewrite map_cons. simpl.
        unfold get_receives_for in IHli.
        apply not_in_cons in Hnf.
        destruct Hnf as [Hnfa Hnfli].
        apply NoDup_cons_iff in Hnodup as Hnodup'.
        
        specialize (@plan_independence _ X (get_matching_plan s from a) (concat (map (get_matching_plan s from) li))) as Hind.
        
        remember (fun s' => forall (i : index), In i li -> (s' i) = (s i)) as Pb.
        
        specialize (Hind Pb s).
        
        spec Hind. {
          assumption.
        }
        
        assert (Hfrs : finite_protocol_plan_from X s (get_matching_plan s from a)). {
          apply get_matching_plan_effect with (s' := (get_matching_state s a from)).
          all : intuition.
        }
        
        spec Hind. { 
          auto.
        }
        
        spec Hind. {
          rewrite HeqPb. intros.
          reflexivity.
        }
        
        specialize (@relevant_components (@message index index_listing) index idec IM_index) as Hrel.
        specialize (Hrel i0 s).
        
        assert (Hincl: incl
               (map (projT1 (P:=fun n : index => vlabel (IM_index n)))
               (map label_a (concat (map (get_matching_plan s from) li)))) li). {
          unfold incl. intros.
          rewrite in_map_iff in H.
          destruct H as [x [Hproj Hinx]].
          apply in_map_iff in Hinx.
          destruct Hinx as [x0 [H_label Hincon]].
          apply in_concat in Hincon.
          destruct Hincon as [y [Hiny Hinx0]].
          rewrite in_map_iff in Hiny.
          destruct Hiny as [z [Hmatching Hindex]].
          rewrite <- H_label in Hproj.
          unfold free_composite_vlsm.
          assert (a0 = z). {
            rewrite <- Hproj.
            apply get_matching_plan_index with (s := s) (from := from).
            rewrite <- Hmatching in Hinx0.
            assumption.
          }
          rewrite H.
          assumption.
       }
        
        (* ensures *)
        
        spec_save Hind. {
          unfold ensures. intros.
          rewrite HeqPb in H0.
          apply Hrel with (li := li).
          assumption.
          assumption.
          unfold incl. intros.
          rewrite in_map_iff in H1.
          destruct H1 as [x [Hproj Hinx]].
          rewrite in_map_iff in Hinx.
          destruct Hinx as [x0 [H_label Hincon]].
          apply in_concat in Hincon.
          destruct Hincon as [y [Hiny Hinx0]].
          rewrite in_map_iff in Hiny.
          destruct Hiny as [z [Hmatching Hindex]].
          rewrite <- H_label in Hproj.
          unfold free_composite_vlsm.
          assert (a0 = z). {
            rewrite <- Hproj.
            apply get_matching_plan_index with (s := s) (from := from).
            rewrite <- Hmatching in Hinx0.
            assumption.
          }
          rewrite H1.
          assumption.
          apply IHli.
          all : intuition.
        }
        
        (* preserves *)
        
        spec_save Hind. {
          rewrite HeqPb.
          unfold preserves.
          intros.
          specialize (Hrel s0).
          specialize (H0 i H3).
          rewrite <- H0.
          apply irrelevant_components.
          intros contra.
          rewrite in_map_iff in contra.
          destruct contra as [x [Hproj Hinx]].
          rewrite in_map_iff in Hinx.
          destruct Hinx as [x0 [Hlabel Hinx0]].
          apply get_matching_plan_index in Hinx0.
          rewrite <- Hlabel in Hproj.
          assert (a = i). {
            rewrite <- Hproj.
            rewrite <- Hinx0.
            intuition.
          }
          rewrite <- H4 in H3.
          intuition.
        }
        split. 
        + intuition.
        + intros.
          unfold res.
          unfold get_receives_for.
          simpl.
          rewrite apply_plan_app.
          destruct (apply_plan X s (get_matching_plan s from a)) as (tr0, res0) eqn : eq_first.
          destruct (apply_plan X res0 (concat (map (get_matching_plan s from) li))) as (tr, res') eqn : eq_second.
          simpl.
          destruct H1.
          rewrite <- H1.
          * assert (project (res0 a) from = project (get_matching_state s a from) from). {
              specialize (get_matching_plan_effect s Hpr (get_matching_state s a from) from a) as Heff.
              spec Heff. {
                intuition.
              }
              spec Heff. {
                intuition.
              }
              simpl in Heff.
              replace res0 with (snd (apply_plan X s (get_matching_plan s from a))).
              apply Heff.
              rewrite eq_first; intuition.
            }
            rewrite <- H2.
            
            assert ((res' a) = (res0 a)). {
              replace res' with (snd (apply_plan X res0 (concat (map (get_matching_plan s from) li)))).
              apply irrelevant_components.
              intros contra.
              rewrite in_map_iff in contra.
              destruct contra as [x [Hproj Hinx]].
              rewrite in_map_iff in Hinx.
              destruct Hinx as [x0 [Hl Hinx0]].
              apply in_concat in Hinx0.
              destruct Hinx0 as [x' [Hinx' Hinx0']].
              rewrite in_map_iff in Hinx'.
              destruct Hinx' as [j [Hmatch Hli]].
              rewrite <- Hl in Hproj.
              rewrite <- Hmatch in Hinx0'.
              apply get_matching_plan_index in Hinx0'.
              replace (@projT1 index (fun n : index => @vlabel (@message index index_listing) (IM_index n))
              (@label_a (@message index index_listing) (@type (@message index index_listing) X)
                 x0)) with a in Hinx0'.
              rewrite <- Hinx0' in Hli.
              intuition.
              rewrite eq_second.
              intuition.
            }
            rewrite H3; intuition.
         * clear Hind.
           replace res' with (snd (apply_plan X res0 (concat (map (get_matching_plan s from) li)))).
           spec IHli. { intuition. }
           spec IHli. { intuition. }
           destruct IHli as [left IHli].
           specialize (IHli i H1).
           rewrite <- IHli.
           assert (forall (i : index), In i li -> res0 i = s i). {
            intros.
            replace res0 with (snd (apply_plan X s (get_matching_plan s from a))).
            apply irrelevant_components.
            intros contra. 
            apply in_map_iff in contra.
            destruct contra as [x [y contra]].
            apply in_map_iff in contra.
            destruct contra as [x0 [Hl Hinx0]].
            apply get_matching_plan_index in Hinx0.
            rewrite <- Hl in y.
            replace (@projT1 index (fun n : index => @vlabel (@message index index_listing) (IM_index n))
             (@label_a (@message index index_listing) (@type (@message index index_listing) X) x0))
             with i1 in Hinx0.
             rewrite Hinx0 in H2.
             intuition.
             rewrite eq_first; intuition.
           }
           
           f_equal.
           specialize (Hrel res0).
           spec Hrel. {
             replace res0 with (snd (apply_plan X s (get_matching_plan s from a))).
             apply apply_plan_last_protocol.
             assumption.
             assumption.
             rewrite eq_first; intuition.
           }
           
           specialize (Hrel (concat (map (get_matching_plan s from) li))).
           simpl in Hrel.
           specialize (Hrel li).
           spec Hrel. {
             assumption.
           }
           
           spec Hrel. {
            assumption.
           }
           
           spec Hrel. {
            assumption.
           }
           
           simpl in Hrel.
           destruct Hrel as [_ Hrel].
           specialize (Hrel i).
           spec Hrel. {
            intuition.
           }
           apply Hrel.
           rewrite eq_second; intuition.
    Qed.
    
    
    Lemma get_receives_for_correct_GE
        (s : vstate X)
        (Hpr : protocol_state_prop X s)
        (li : list index)
        (from : index)
        (Hnodup : NoDup li)
        (Hnf : ~ In from li) :
        let res := snd (apply_plan X s (get_receives_for s li from)) in
        incl (GE res) (GE s).
    Proof.
      induction li using rev_ind; intros.
      - simpl in res.
        unfold res.
        apply incl_refl.
      - simpl in Hnf.
        (*
        apply NoDup_cons_iff in Hnodup.
        destruct Hnodup as [Hna Hnodup].
        specialize (IHli Hnodup). *)
        
        assert (NoDup li). {
          admit.
        }
        
        assert (~ In from li). {
          admit.
        }
        
        spec IHli. intuition.
        
        unfold get_receives_for in res. simpl in res.
        (* remember (get_matching_plan s from a) as short_plan.
        remember (concat (map (get_matching_plan s from) li)) as long_plan. *)
        unfold res.
        rewrite map_app.
        rewrite concat_app.
        rewrite apply_plan_app.
        
        destruct (apply_plan X s (concat (map (get_matching_plan s from) li))) as (tr_long, res_long) eqn : eq_long.
        destruct (apply_plan X res_long (concat (map (get_matching_plan s from) [x]))) as (tr_short, res_short) eqn : eq_short.
        
        simpl.
        
        spec IHli. {
          intuition.
        }
        simpl in IHli.
        apply incl_tran with (m := GE res_long). 
        2 : {
          replace res_long with (snd (apply_plan X s (concat (map (get_matching_plan s from) li)))) by (rewrite eq_long;intuition).
          unfold get_receives_for in IHli.
          intuition.
        }
        
        simpl in eq_short.
        rewrite app_nil_r in eq_short.
        replace res_short with (snd (apply_plan X res_long (get_matching_plan s from x))) by (rewrite eq_short; intuition).
        admit.
    Admitted.
    
    Definition is_receive_plan
      (a : vplan X) : Prop := 
      let labels_a := List.map label_a a in
      let label_types := List.map (fun (l : vlabel X) => let (i, li) := l in li) labels_a in
      forall (l : label_list), In l label_types -> l = receive.
    
    Definition is_receive_plan_app
      (a b : vplan X) :
      is_receive_plan (a ++ b) <-> is_receive_plan a /\ is_receive_plan b.
    Proof.
    Admitted.
    
    Lemma message_providers_receive
      (s : vstate X)
      (i : index) :
      get_message_providers_from_plan (get_receives_for s (others i s) i) = [i].
    Proof.
    Admitted.
    
    Lemma get_matching_plan_is_receive_plan
      (s : vstate X)
      (from to : index) :
      is_receive_plan (get_matching_plan s from to).
    Proof.
      unfold is_receive_plan; intros.
      apply in_map_iff in H.
      destruct H as [x [Hlabel Hinx]].
      destruct x as [i x].
      apply in_map_iff in Hinx.
      destruct Hinx as [x0 [Hlabel_a Hinx0]].
      destruct x0 as [lable_x0 input_x0] eqn : eq_x0.
      
      unfold get_matching_plan in Hinx0.
      destruct (sync s (get_matching_state s to from) to from) eqn : eq_sync.
      - unfold sync in eq_sync.
        destruct (complete_suffix (get_history (get_matching_state s to from) from) (get_history (s to) from)) eqn : eq_c.
        + inversion eq_sync.
          admit.
       + discriminate eq_sync.
    - simpl in Hinx0.
      intuition.
    Admitted.
    
    Lemma receive_for_is_receive_plan 
      (s : vstate X)
      (from : index)
      (li : list index) :
      is_receive_plan (get_receives_for s li from).
    Proof.
      unfold is_receive_plan.
      unfold get_receives_for.
      intros.
      rewrite in_map_iff in H.
      destruct H as [x [Hlabel Hinx]].
      rewrite in_map_iff in Hinx.
      destruct Hinx as [x0 [Heqlabel Hinx0]].
      destruct x0.
      destruct x.
      apply in_concat in Hinx0.
      destruct Hinx0 as [x1 [Hinx1 Hinx1']].
      rewrite in_map_iff in Hinx1.
      destruct Hinx1 as [x2 [Heqmatch Hinx2]].
      
      unfold get_matching_plan in Heqmatch.
    Admitted.
    
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
          specialize (Hreceive_short li).
          spec Hreceive_short. {
            apply in_map_iff.
            exists label_a'. simpl. intuition.
            rewrite Heqlabel_a'.
            intuition.
          }
          rewrite eq_li in Hreceive_short.
          discriminate Hreceive_short.
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
        
        spec IHa. {
          assumption.
        }
        
        spec IHa. {
          assumption.
        }
        
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
            specialize (Hrec_short label_x).
            spec Hrec_short. {
              intuition.
            }
          rewrite eq_label in Hrec_short.
          discriminate Hrec_short.
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
    
    Lemma get_receives_all_protocol
      (s : vstate X)
      (lfrom : set index)
      (Hnodup : NoDup lfrom)
      (Hprs : protocol_state_prop X s) :
      let res := snd (apply_plan X s (get_receives_all s lfrom)) in 
      finite_protocol_plan_from X s (get_receives_all s lfrom) /\
      forall (f i : index), In f lfrom -> i <> f -> project (res i) f = project (get_matching_state s i f) f /\
      incl (GE res) (GE s).
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
        
        assert (Hrec_long : is_receive_plan (concat (map (fun i : index => get_receives_for s (others i s) i) lfrom))). {
          admit.
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
          clear -contra.
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
          destruct Hina as [i [Heq_rec Heqfrom]].
          admit.
        }
        
        assert (Hsource: finite_protocol_plan_from X s (get_receives_for s (others x s) x)). {
          apply get_receives_for_correct.
          assumption.
          apply NoDup_others.
          apply others_correct.
        }
        
        specialize (relevant_components_lv s res_long Hprs Hprs_long (get_receives_for s (others x s) x)) as Hrel.
        specialize (Hrel Hrec_short Hsource x).
        
        spec Hrel. {
          rewrite message_providers_receive.
          intuition.
        }
        
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
        + split.
          *  intros.
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
                apply others_correct2.
                rewrite e in H2.
                assumption.
              -- apply in_app_iff in H1.
                simpl in H1.
                destruct H1.
                specialize (IHproject f i H1).
                spec IHproject. {
                  intuition.
                }
                destruct IHproject as [IHproject _].
                rewrite <- IHproject.
                unfold get_receives_all.
                replace (snd (apply_plan X s (concat (map (fun i : index => get_receives_for s (others i) i) lfrom)))) with res_long.
                rewrite H.
                apply receives_neq.
                assumption.
                assumption.
                assumption.
                rewrite message_providers_receive.
                intros contra.
                simpl in contra.
                all : intuition.
          * admit. 
    Admitted.
    
    Definition phase_two (s : vstate X) := snd (apply_plan X s (get_receives_all s index_listing)).
    Definition common_future (s : vstate X) := phase_two (phase_one_res s).
    
    Lemma common_future_in_futures
      (s : vstate X)
      (Hpr : protocol_state_prop X s)
      (Hnf : no_component_fully_equivocating s index_listing) :
      in_futures X s (common_future s).
    Proof.
      specialize (@in_futures_trans message X s (phase_one_res s) (common_future s)) as Htrans.
      apply Htrans.
      apply phase_one_future.
      assumption.
      assumption.
      unfold common_future.
      unfold phase_two.
      unfold in_futures.
      remember (phase_one_res s) as s'.
      exists (fst (apply_plan X (phase_one_res s) (get_receives_all s' index_listing))).
      split.
      - specialize (get_receives_all_protocol s' index_listing (proj1 Hfinite)) as Hrec.
        spec Hrec. {
          rewrite Heqs'.
          unfold phase_one_res.
          unfold phase_one.
          apply apply_plan_last_protocol.
          assumption.
          apply phase_one_protocol.
          assumption.
          assumption.
        }
        simpl in Hrec.
        destruct Hrec as [Hrec _].
        unfold finite_protocol_plan_from in Hrec.
        rewrite Heqs' in *.
        assumption.
      - rewrite Heqs'.
        apply apply_plan_last.
    Qed.
    
    Lemma common_future_no_extra_equivocation
      (s : vstate X)
      (Hpr : protocol_state_prop X s)
      (Hnf : no_component_fully_equivocating s index_listing) :
      incl (GE (common_future s)) (GE s).
    Proof.
      intros.
    Admitted.
End Composition.
