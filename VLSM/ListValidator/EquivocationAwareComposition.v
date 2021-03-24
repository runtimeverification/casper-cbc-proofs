From Coq Require Import Bool List ListSet Reals FinFun RelationClasses Relations Relations_1 Sorting Basics Lia.
Import ListNotations.

From CasperCBC
Require Import
  Lib.Preamble
  Lib.ListExtras
  Lib.ListSetExtras
  Lib.SortedLists
  Lib.Measurable
  VLSM.Common
  VLSM.Plans
  VLSM.ProjectionTraces
  VLSM.Composition
  VLSM.Equivocation
  VLSM.ListValidator.ListValidator
  VLSM.ListValidator.Equivocation
  VLSM.ListValidator.Observations
  VLSM.ListValidator.EquivocationAwareListValidator
  VLSM.ObservableEquivocation
  .

(** * VLSM Free Composition of List Validators *)

(**   This file describes a free composition <X> of List Validator nodes, each using
   an [equivocation_aware_estimator]. Also see:

   - [Observations.v] for the observation model used here
   - [EquivocationAwareListValidator.v] for the used estimators
   - [Equivocation.v] and [ListValidator.v] for some general
     facts about List Validators.
*)

Section Composition.
Context
  {index : Type}
  {i0 : Inhabited index}
  {index_listing : list index}
  {Hfinite : Listing index_listing}
  {idec : EqDecision index}
  {Mindex : Measurable index}
  {Rindex : ReachableThreshold index}
  (est' := fun (i : index) => (@EquivocationAwareListValidator.equivocation_aware_estimator _ i _ Hfinite _ _ _ ))
  (IM_index := fun (i : index) => @VLSM_list index i index_listing idec (est' i))
  (has_been_sent_capabilities := fun i : index => @lv_sent_capability index i index_listing Hfinite idec (est' i))
  (has_been_received_capabilities := fun i : index => @lv_received_capability index i index_listing Hfinite idec (est' i))
  (X := composite_vlsm IM_index (free_constraint IM_index))
  (preX := pre_loaded_with_all_messages_vlsm X)
  (Hevents_set' := fun (i : index) => @simp_lv_observable_events index i index_listing _)
  (Hstate_events_set := fun (i : index) => @simp_lv_state_observations index i index_listing _)
  (Hevidence := fun (i : index) => @simp_observable_full index i index_listing idec)
  (Hstate_events_fn := fun (i : index) => (@simp_lv_observations index i index_listing _))
  (Hbasic := fun (i : index) => @simp_lv_basic_equivocation index i index_listing Hfinite idec Mindex Rindex).

  Local Notation in_listing := (proj2 Hfinite).

  (**  We begin with some basic facts about the given composition. *)

  (**  Protocol states are never bottom *)

  Lemma protocol_state_component_no_bottom
    (s : vstate X)
    (i : index)
    (Hprs : protocol_state_prop X s) :
    (s i) <> Bottom.
  Proof.
    apply (@protocol_prop_no_bottom index i _ _ (est' i)).
    apply protocol_state_projection with (j := i) in Hprs.
    unfold protocol_state_prop in Hprs.
    destruct Hprs as [om Hprs] in Hprs.
    apply proj_pre_loaded_with_all_messages_protocol_prop in Hprs.
    unfold protocol_state_prop.
    exists om.
    assumption.
  Qed.

  Proposition Hsnb
    (s : vstate X)
    (Hpr : protocol_state_prop X s) :
    forall (i : index), (s i) <> Bottom.
  Proof.
    intros i.
    apply protocol_state_component_no_bottom. intuition.
  Qed.

  (**  Applying a protocol plan of receive transitions do not alter the nodes'
     self-projections (i.e, <<project (s i) i >> *)

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
    unfold composite_valid in Hprotocol.
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
    (a : plan X)
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
     rewrite Hres_short.
     rewrite Hres_long.
     intuition.
  Qed.

  (**  Applying a plan of send/update transitions does not alter
     non-self projections. *)

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
    unfold composite_valid in Hprotocol.
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
    (a : plan X)
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
     rewrite Hres_short.
     rewrite Hres_long.
     intuition.
     intuition.
  Qed.

  Local Notation component_list s li := (List.map s li).

  Section EquivObsUtils.

  (** Here we instantiate the observation-based equivocation model for our composition.
     The implicit <<ws>> stands for "witness set" and it means, in short, that we only
     take into account validators in <<ws>> when gathering observations for the composite state.
     Note that these observations can concern anyone, but they can only be taken from local
     observations of validators in <<ws>>. *)

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

  (** The honest set: Validators for which there is no evidence of equivocation.
     Note that some of these may actually be equivocating if we were to
     take into account observations originating outside of <<ws>> *)

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

  (** The equivocating set : Validators for which there is evidence of equivocation. *)

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

  (** Shorthands for the union of observations. *)

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

  Remark cobs_single
    (s : vstate X)
    (target : index)
    (e : simp_lv_event) :
    In e (wcobs s target) <->
    exists (i : index), (In i ws) /\ (In e (@simp_lv_observations index i index_listing _ (s i) target)).
  Proof.
    split; intros.
    - apply set_union_in_iterated in H. rewrite Exists_exists in H.
      destruct H as [le [Hinle Hine]].
      apply in_map_iff in Hinle.
      destruct Hinle as [ii [Heqle Hini]].
      exists ii. rewrite <- Heqle in Hine. intuition.
    - apply set_union_in_iterated. rewrite Exists_exists.
      destruct H as [i Hi].
      exists (@simp_lv_observations index i index_listing _ (s i) target).
      split.
      + apply in_map_iff. exists i. split;intuition.
      + intuition.
  Qed.

  Remark cobs_single_s
    (s : vstate X)
    (target : index)
    (e : simp_lv_event) :
    In e (wcobs_states s target) <->
    exists (i : index), (In i ws) /\ (In e (@simp_lv_state_observations index i index_listing _ (s i) target)).
  Proof.
    split; intros.
    - apply set_union_in_iterated in H. rewrite Exists_exists in H.
      destruct H as [le [Hinle Hine]].
      apply in_map_iff in Hinle.
      destruct Hinle as [ii [Heqle Hini]].
      exists ii. rewrite <- Heqle in Hine. intuition.
    - apply set_union_in_iterated. rewrite Exists_exists.
      destruct H as [i Hi].
      exists (@simp_lv_state_observations index i index_listing _ (s i) target).
      split.
      + apply in_map_iff. exists i. split;intuition.
      + intuition.
  Qed.

  Remark cobs_single_m
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

  Remark in_cobs_messages
    (s : vstate X)
    (target : index)
    (e : simp_lv_event)
    (Hin : In e (wcobs_messages s target)) :
    get_simp_event_type e = Message'.
  Proof.
    apply cobs_single_m in Hin.
    destruct Hin as [i [Hini Hine]].
    apply in_simp_lv_message_observations in Hine.
    intuition.
  Qed.

  Remark in_cobs_states
    (s : vstate X)
    (target : index)
    (e : simp_lv_event)
    (Hin : In e (wcobs_states s target)) :
    get_simp_event_type e = State'.
  Proof.
    apply cobs_single_s in Hin.
    destruct Hin as [i [Hini Hine]].
    apply in_simp_lv_state_observations in Hine.
    intuition.
  Qed.

  Remark cobs_messages_states
    (s : vstate X)
    (target : index) :
    set_eq (wcobs s target) (set_union decide_eq (wcobs_states s target) (wcobs_messages s target)).
  Proof.
    apply set_eq_extract_forall. intros.
    split; intros.
    - apply cobs_single in H.
      destruct H as [i [Hini Hobsi]].
      unfold simp_lv_observations in Hobsi.
      apply set_union_iff in Hobsi.
      apply set_union_iff.
      destruct Hobsi.
      + right. apply cobs_single_m.
        exists i. intuition.
      + left. apply cobs_single_s.
        exists i. intuition.
     - apply set_union_iff in H.
       destruct H.
       + apply cobs_single_s in H.
         destruct H as [i [Hini Hobsi]].
         apply cobs_single.
         exists i. split;[intuition|].
         apply in_simp_lv_state_observations'.
         intuition.
       + apply cobs_single_m in H.
         destruct H as [i [Hini Hobsi]].
         apply cobs_single.
         exists i. split;[intuition|].
         apply in_simp_lv_message_observations'.
         intuition.
  Qed.

  Remark in_cobs_and_message
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

  Remark in_cobs_states'
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

  Remark in_cobs_messages'
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

  (** There's at most one state observation
     regarding a fixed validator. *)

  Lemma unique_state_observation
    (s : vstate X)
    (i : index)
    (e : simp_lv_event)
    (Hin : In e (wcobs_states s i)) :
    e = SimpObs State' i (s i).
  Proof.
    unfold wcobs in Hin.
    unfold composite_state_events_fn in Hin; simpl in Hin.
    apply cobs_single_s in Hin.
    destruct Hin as [j [Hinj Hine]].
    unfold simp_lv_state_observations in Hine.
    destruct (decide (i = j)).
    - subst j.
      destruct Hine; intuition.
    - intuition.
  Qed.

  (** And if said validator is in <<ws>>,
     it's always there. *)

  Lemma state_obs_present
    (s : vstate X)
    (i : index)
    (Hin : In i ws) :
    In (SimpObs State' i (s i)) (wcobs_states s i).
  Proof.
    apply cobs_single_s.
    exists i.
    split;[intuition|].
    unfold simp_lv_state_observations.
    rewrite decide_True by intuition.
    intuition.
  Qed.

  Remark GE_direct
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

  (** Shortcircuiting the lengthy translation
     between the observation typeclass and
     the above definitions. *)

  Remark hbo_cobs
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
             exists inhabitant.
             split;[intuition|]. apply (proj2 Hfinite).
          -- apply ((proj2 Hfinite) (get_simp_event_subject e)).
     + intuition.
  Qed.

  (** We have actual equality due to these
     sets being the results of [filter]s. *)

  Remark wE_eq_equality
    (s s' : vstate X) :
    set_eq (wE s) (wE s') -> (wE s) = (wE s').
  Proof.
    intros.
    apply filter_set_eq.
    unfold wE in H.
    intuition.
  Qed.

  Remark wH_eq_equality
    (s s' : vstate X)
    (i : index) :
    set_eq (wH s) (wH s') -> (wH s) = (wH s').
  Proof.
    intros.
    apply filter_set_eq.
    unfold wH in H.
    intuition.
  Qed.

  Remark wH_wE'
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

  Remark wE_wH'
    (s : vstate X)
    (i : index) :
    In i (wE s) <-> ~ In i (wH s).
  Proof.
    unfold wH.
    unfold wE.
    split; intros.
    - apply filter_In in H.
      intros contra.
      apply filter_In in contra.
      destruct H as [_ H].
      destruct contra as [_ contra].
      rewrite bool_decide_eq_true in H.
      rewrite negb_true_iff in contra.
      rewrite bool_decide_eq_false in contra.
      intuition.
    - apply filter_In.
      split; [apply (proj2 Hfinite)|].
      match goal with
      |- ?e = _ =>
        destruct e eqn : eq_d end.
      + intuition.
      + contradict H.
        apply filter_In.
        split;[apply in_listing|].
        rewrite negb_true_iff.
        intuition.
  Qed.

  Remark wH_wE
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

  Remark HE_eq_equiv
    (s s' : vstate X) :
    (wH s) = (wH s') <-> (wE s) = (wE s').
  Proof.
    unfold wH. unfold wE.
    symmetry. apply filter_complement.
  Qed.

  (** We start to describe what happens to observations
     when doing composite updates (similarly to results in [Observations.v]). Some results
     that don't hold for arbitrary <<ws>> live outside
     this section. *)

  Lemma cobs_message_existing_other_lf
    (s : vstate X)
    (Hpr : protocol_state_prop X s)
    (so : state)
    (i j target : index)
    (Hdif : i <> j)
    (s' := state_update IM_index s i (update_state (s i) so j))
    (Hfull : project (s i) j = project so j)
    (Hhave : In (SimpObs Message' j so) (wcobs s j)) :
    incl (wcobs_messages s' target) (wcobs_messages s target).
  Proof.
    assert (Hsnb : forall (k : index), (s k) <> Bottom). {
      intros k.
      apply protocol_state_component_no_bottom. intuition.
    }

    assert (Hsonb : so <> Bottom). {
        apply in_cobs_and_message in Hhave.
        apply cobs_single_m in Hhave.
        destruct Hhave as [k Hhave].
        destruct Hhave as [_ Hhave].
        apply (@in_message_observations_nb index index_listing Hfinite) in Hhave.
        all : intuition.
    }
    unfold incl.
    intros e.
    intros H.
    unfold wcobs_messages in H.
    apply cobs_single_m in H.
    destruct H as [k Hink].
    destruct (decide (k = i)).
    - subst k.
      unfold s' in Hink.
      rewrite state_update_eq in Hink.
      destruct (decide (j = target)).
      + subst target.
        destruct Hink as [Hink' Hink].
        apply (@new_incl_rest_same index index_listing Hfinite) in Hink.
        2 : {
          split. apply Hsnb; intuition. intuition.
        }
        2 : intuition.

        apply set_union_iff in Hink.
        destruct Hink as [Hink|Hink].
        * apply set_union_iff in Hink.
          destruct Hink as [Hink|Hink].
          -- apply cobs_single_m.
             exists i. intuition.
          -- apply in_cobs_and_message in Hhave.
             apply cobs_single_m in Hhave.
             destruct Hhave as [l Hhave].
             apply cobs_single_m.
             exists l.
             split;[intuition|].
             apply (@message_cross_observations index index_listing Hfinite) with (e1 := (SimpObs Message' j so)) (i := j).
             all : intuition.
       * destruct Hink;[|intuition].
         rewrite <- H.
         apply in_cobs_and_message in Hhave.
         all : intuition.

      + destruct Hink as [Hink' Hink].
        apply (@new_incl_rest_diff index index_listing Hfinite) in Hink.
        2 : {
          split. apply Hsnb; intuition. intuition.
        }
        2 : intuition.

        apply set_union_iff in Hink.
        destruct Hink as [Hink|Hink].
        apply cobs_single_m.
        exists i.
        split;[intuition|].
        intuition.
        apply in_cobs_and_message in Hhave.
        2 : intuition.
        apply cobs_single_m in Hhave.
        destruct Hhave as [l Hhave].
        apply cobs_single_m.
        exists l.
        split;[intuition|].
        apply (@message_cross_observations index index_listing Hfinite) with (e1 := (SimpObs Message' j so)) (i := j).
        intuition.
        simpl.
        intuition.
        intuition.
    - unfold s' in Hink.
      rewrite state_update_neq in Hink by intuition.
      apply cobs_single_m.
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
    (Hhave : In (SimpObs Message' j so) (wcobs s j)) :
    incl (wcobs_messages s target) (wcobs_messages s' target).
  Proof.
    assert (Hsnb : forall (k : index), (s k) <> Bottom). {
      intros k.
      apply protocol_state_component_no_bottom. intuition.
    }

    assert (Hsonb : so <> Bottom). {
        apply in_cobs_and_message in Hhave.
        apply cobs_single_m in Hhave.
        destruct Hhave as [k Hhave].
        destruct Hhave as [_ Hhave].
        apply (@in_message_observations_nb index index_listing Hfinite) in Hhave.
        all : intuition.
    }

    unfold incl.
    intros.
    apply cobs_single_m in H.
    destruct H as [k H].
    destruct (decide (i = k)).
    - subst k.
      apply cobs_single_m.
      exists i.
      split;[intuition|].
      destruct H as [_ H].
      apply (@old_incl_new index index_listing Hfinite) with (so := so) (i := j) in H.
      unfold s'.
      rewrite state_update_eq.
      intuition.
      split. apply Hsnb. intuition.
      intuition.
   - apply cobs_single_m.
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
    incl (wcobs_messages s target) (wcobs_messages s' target).
  Proof.
    assert (Hsnb : forall (k : index), (s k) <> Bottom). {
      intros k.
      apply protocol_state_component_no_bottom. intuition.
    }

    unfold incl.
    intros.
    apply cobs_single_m in H.
    destruct H as [k H].
    destruct (decide (i = k)).
    - subst k.
      apply cobs_single_m.
      exists i.
      split;[intuition|].
      destruct H as [_ H].
      apply (@old_incl_new index index_listing Hfinite) with (so := so) (i := j) in H.
      unfold s'.
      rewrite state_update_eq.
      intuition.
      split. apply Hsnb. intuition.
      intuition.
   - apply cobs_single_m.
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
    (Hhave : In (SimpObs Message' j so) (wcobs s j)) :
    set_eq (wcobs_messages s target) (wcobs_messages s' target).
  Proof.
    unfold set_eq.
    split.
    - apply cobs_message_existing_other_rt.
      all : intuition.
    - apply cobs_message_existing_other_lf.
      all : intuition.
  Qed.

  Lemma wcobs_message_existing_same1
    (s : vstate X)
    (Hpr : protocol_state_prop X s)
    (b : bool)
    (i target : index)
    (Hdif : i <> target)
    (s' := state_update IM_index s i (update_consensus (update_state (s i) (s i) i) b)) :
    incl (wcobs_messages s target) (wcobs_messages s' target).
  Proof.
    assert (Hsnb : forall (k : index), (s k) <> Bottom). {
      intros k.
      apply protocol_state_component_no_bottom. intuition.
    }

    intros e.
    intros H.
    - apply cobs_single_m in H.
      destruct H as [k H].
      destruct (decide (k = i)).
      + subst k.
        destruct H as [H' H].
        apply (@old_incl_new index index_listing Hfinite) with (so := (s i)) (i := i) in H.
        apply cobs_single_m.
        exists i.
        unfold s'.
        rewrite state_update_eq.
        rewrite cons_clean_message_obs with (b0 := b) in H.
        split;[intuition|].
        intuition.
        split; apply Hsnb.
        intuition.
      + apply cobs_single_m.
        exists k.
        unfold s'.
        rewrite state_update_neq.
        all : intuition.
  Qed.

  Lemma wcobs_message_existing_same2
    (s : vstate X)
    (Hpr : protocol_state_prop X s)
    (b : bool)
    (i : index)
    (s' := state_update IM_index s i (update_consensus (update_state (s i) (s i) i) b)) :
    incl (wcobs_messages s i) (wcobs_messages s' i).
  Proof.
    assert (Hsnb : forall (k : index), (s k) <> Bottom). {
      intros k.
      apply protocol_state_component_no_bottom. intuition.
    }
    intros e.
    intros H.
    -
      + apply cobs_single_m in H.
        destruct H as [k [H' H]].
        destruct (decide (i = k)).
        * subst k.
          apply (@old_incl_new index index_listing Hfinite) with (so := (s i)) (i := i) in H.
          apply cobs_single_m.
          exists i.
          unfold s'.
          rewrite state_update_eq.
          rewrite cons_clean_message_obs with (b0 := b) in H.
          split;[intuition|].
          intuition.
          split; apply Hsnb.
          intuition.
        * apply cobs_single_m.
          exists k.
          unfold s'.
          rewrite state_update_neq.
          split;[intuition|].
          all : intuition.
  Qed.

  Lemma in_future_message_obs
    (s s' : vstate X)
    (Hprs : protocol_state_prop X s)
    (target : index)
    (Hf : in_futures X s s')
    (e : simp_lv_event)
    (Hin : In e (wcobs_messages s target)) :
    In e (wcobs_messages s' target).
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
      unfold composite_valid in Hproto.
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
          apply wcobs_message_existing_same2. intuition. intuition.
        * apply wcobs_message_existing_same1; intuition.
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

  End EquivObsUtils.

  Lemma ws_incl_cobs
    (s : vstate X)
    (i : index)
    (ws ws' : set index)
    (Hincl : incl ws' ws)
    (e : simp_lv_event) :
    In e (@wcobs ws' s i) -> In e (@wcobs ws s i).
  Proof.
    intros.
    unfold wcobs in *.
    unfold composite_state_events_fn in *.
    apply set_union_in_iterated in H; rewrite Exists_exists in H.
    apply set_union_in_iterated. apply Exists_exists.
    destruct H as [le [H1 H2]].
    exists le.
    apply in_map_iff in H1. destruct H1 as [j [Hj Hinj]].
    split.
    - apply in_map_iff.
      exists j. intuition.
    - intuition.
  Qed.

  Lemma ws_incl_wE
    (s : vstate X)
    (ws ws' : set index)
    (Hincl : incl ws' ws) :
    incl (@wE ws' s) (@wE ws s).
  Proof.
    unfold incl. intros.
    apply GE_direct in H.
    apply GE_direct.
    unfold cequiv_evidence in *.
    unfold equivocation_evidence in *.
    setoid_rewrite hbo_cobs.
    setoid_rewrite hbo_cobs in H.
    destruct H as [e1 [He1 [He1' [e2 [He2 [He2' Hcomp]]]]]].
    exists e1.
    apply ws_incl_cobs with (ws := ws) in He1. 2 : intuition.
    split;[intuition|].
    split;[intuition|].
    exists e2.
    apply ws_incl_cobs with (ws := ws) in He2. 2 : intuition.
    intuition.
  Qed.

  (** GH := the set of globally honest validators: no evidence of equiv. exists at all.
     HH := the set of honest-looking-for-the-honest validators: members of GH have
     no evidence of equiv. regarding these validators.
     LH i := the set of locally honest validators (<<ws>> is a singleton). *)

  Definition GE := @wE index_listing.
  Definition GH := @wH index_listing.
  Definition cobs (s : vstate X) := @wcobs index_listing s.
  Definition cobs_messages (s : vstate X) := @wcobs_messages index_listing s.
  Definition cobs_states (s : vstate X) := @wcobs_states index_listing s.

  Definition HE (s : vstate X) := @wE (GH s) s.
  Definition HH (s : vstate X) := @wH (GH s) s.

  Definition hcobs (s : vstate X) := @wcobs (GH s) s.
  Definition hcobs_messages (s : vstate X) := @wcobs_messages (GH s) s.
  Definition hcobs_states (s : vstate X) := @wcobs_states (GH s) s.

  Definition LE (i : index) := (@wE [i]).
  Definition LH (i : index) := (@wH [i]).

  Remark GH_NoDup
    (s : vstate X) :
    NoDup (GH s).
  Proof.
    unfold GH.
    apply NoDup_filter.
    apply (proj1 Hfinite).
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
    apply set_eq_extract_forall.
    intros e.
    split; intros H.
    - apply cobs_single_m in H.
      destruct H as [k H].
      destruct (decide (k = i)).
      + subst k.
        unfold s' in H.
        rewrite state_update_eq in H.
        rewrite <- cons_clean_message_obs in H.
        destruct H as [_ H].
        apply (@new_incl_rest_diff index index_listing Hfinite) in H.
        apply set_union_iff in H.
        destruct H; (apply cobs_single_m; exists i; split;[apply in_listing|intuition]).
        split; apply Hsnb.
        all :intuition.
      + unfold s' in H.
        rewrite state_update_neq in H.
        apply cobs_single_m.
        exists k. all : intuition.
    - apply wcobs_message_existing_same1; intuition.
  Qed.

  Lemma cobs_message_existing_same2
    (s : vstate X)
    (Hpr : protocol_state_prop X s)
    (b : bool)
    (i : index)
    (s' := state_update IM_index s i (update_consensus (update_state (s i) (s i) i) b)) :
    set_eq (cobs_messages s' i) (set_union decide_eq (cobs_messages s i) [SimpObs Message' i (s i)]).
  Proof.
    apply set_eq_extract_forall.
    intros e.
    split; intros H.
    - apply cobs_single_m in H.
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
        destruct H; left; apply cobs_single_m; exists i; (split;[apply in_listing|intuition]).
        split; apply Hsnb; intuition.
        intuition.
      + left.
        unfold s' in H.
        rewrite state_update_neq in H by intuition.
        apply cobs_single_m. exists k. intuition.
    -  apply set_union_iff in H.
      destruct H as [H | H].
      + apply wcobs_message_existing_same2; intuition.
      + apply cobs_single_m.
        exists i.
        unfold s'.
        rewrite state_update_eq by intuition.
        destruct H;[|intuition].
        rewrite <- cons_clean_message_obs with (b0 := b).
        assert (project (update_state (s i) (s i) i) i = s i). {
          rewrite (@project_same index index_listing).
          intuition.
          intuition.
          apply Hsnb; intuition.
        }
        split;[apply in_listing|].
        apply refold_simp_lv_observations1.
        unfold update_state.
        destruct (s i) eqn : eq_si.
        specialize (Hsnb s Hpr i). congruence.
        congruence.
        rewrite H0.
        apply Hsnb; intuition.
        rewrite H0.
        intuition.
  Qed.

  (** The following set of results allow us to conclude that our
     common future-finding procedure maintains the same set of globally
     honest validators. *)

  Lemma GE_existing_same_state_message
    (s : vstate X)
    (es2 : state)
    (Hprs : protocol_state_prop X s)
    (b : bool)
    (i v : index)
    (s' := state_update IM_index s i (update_consensus (update_state (s i) (s i) i) b))
    (Hine2 : In (SimpObs Message' v es2) (cobs_messages s' v))
    (Hcomp : ~ comparable simp_lv_event_lt (SimpObs State' v (s' v)) (SimpObs Message' v es2)) :
    @cequiv_evidence index_listing s v.
  Proof.
    unfold cequiv_evidence.
    unfold equivocation_evidence.
    setoid_rewrite hbo_cobs.
    destruct (decide (i = v)).
    - subst i.
      unfold s' in Hine2.
      setoid_rewrite cobs_message_existing_same2 in Hine2.
      2 : intuition.
      apply set_union_iff in Hine2.
      destruct Hine2 as [Hine2|Hine2].
      + exists (SimpObs State' v (s v)).
        split.
            * simpl.
              apply in_cobs_states'.
              apply state_obs_present.
              apply in_listing.
            * split; [simpl;intuition|].
                exists (SimpObs Message' v es2).
                split.
                -- simpl. apply in_cobs_messages'. intuition.
                -- split;[simpl;intuition|].
                   intros contra.
                   apply comparable_commutative in contra.
                   apply (@state_obs_stuff_cons index v index_listing Hfinite) with (so := (s v)) (i := v) (b := b) in contra.
                   unfold s' in Hcomp.
                   apply comparable_commutative in contra.
                   rewrite state_update_eq in Hcomp.
                   intuition.
                   split;apply Hsnb; intuition.
                   intuition.
                   simpl. congruence.
                   simpl. congruence.
          +  destruct Hine2; [|intuition].
             inversion H.
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
             apply Hsnb; intuition.
             rewrite (@project_same index index_listing Hfinite).
             apply Hsnb; intuition.
             apply Hsnb; intuition.
         - unfold s' in Hine2.
           setoid_rewrite cobs_message_existing_same1 in Hine2.
           2, 3 : intuition.
           exists (SimpObs State' v (s v)).
             split.
             * simpl.
                apply in_cobs_states'.
                apply state_obs_present.
                apply in_listing.
             * split; [simpl;intuition|].
                exists (SimpObs Message' v es2).
                split.
                -- simpl. apply in_cobs_messages'. intuition.
                -- split;[simpl;intuition|].
                   intros contra.
                   apply comparable_commutative in contra.
                   unfold s' in Hcomp.
                   rewrite state_update_neq in Hcomp.
                   apply comparable_commutative in contra.
                   all : intuition.
  Qed.

  Lemma GE_existing_same
    (s : vstate X)
    (Hprs : protocol_state_prop X s)
    (b : bool)
    (i : index)
    (s' := state_update IM_index s i (update_consensus (update_state (s i) (s i) i) b)) :
    incl (GE s') (GE s).
  Proof.
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
    simpl in *.
    destruct Hine1 as [Hine1|Hine1].
    - apply in_cobs_states in Hine1 as Het1.
      simpl in Het1.
      subst et1.
      apply unique_state_observation in Hine1.
      simpl in Hine1.
      inversion Hine1.
      subst es1.
      destruct Hine2 as [Hine2|Hine2].
      + (** State and state : immediate contradiction *)
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
      + (*State and message *)
        apply in_cobs_messages in Hine2 as Het2.
        simpl in Het2. subst et2.
        specialize (GE_existing_same_state_message s es2 Hprs b i v Hine2 Hcomp) as Hev.
        unfold cequiv_evidence in Hev. unfold equivocation_evidence in Hev.
        setoid_rewrite hbo_cobs in Hev. intuition.
     - apply in_cobs_messages in Hine1 as Het1.
       simpl in Het1. subst et1.
       destruct Hine2 as [Hine2|Hine2].
       + apply in_cobs_states in Hine2 as Het2.
         simpl in Het2. subst et2.
         apply unique_state_observation in Hine2.
         inversion Hine2. subst es2.
         rewrite comparable_commutative in Hcomp.
         specialize (GE_existing_same_state_message s es1 Hprs b i v Hine1 Hcomp) as Hev.
         unfold cequiv_evidence in Hev. unfold equivocation_evidence in Hev.
         setoid_rewrite hbo_cobs in Hev. intuition.
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

  Lemma GE_existing_different_state_message
    (s : vstate X)
    (Hprs : protocol_state_prop X s)
    (i j v : index)
    (Hdif : i <> j)
    (es2 so : state)
    (s' := state_update IM_index s i (update_state (s i) so j))
    (Hfull : project (s i) j = project so j)
    (Hhave : In (SimpObs Message' j so) (cobs s j))
    (Hine2 : In (SimpObs Message' v es2) (cobs_messages s' v))
    (Hcomp : ~ comparable simp_lv_event_lt (SimpObs State' v (s' v)) (SimpObs Message' v es2)) :
    @cequiv_evidence index_listing s v.
  Proof.
    assert (Hsnb : forall (k : index), (s k) <> Bottom). {
      intros k.
      apply protocol_state_component_no_bottom. intuition.
    }

    assert (Hsonb : so <> Bottom). {
        apply in_cobs_and_message in Hhave.
        apply cobs_single_m in Hhave.
        destruct Hhave as [k [_ Hhave]].
        apply (@in_message_observations_nb index index_listing Hfinite) in Hhave.
        all : intuition.
    }

    unfold cequiv_evidence.
    unfold equivocation_evidence. setoid_rewrite hbo_cobs.
    unfold s' in Hine2.
        setoid_rewrite <- cobs_message_existing_other in Hine2.
        2, 3, 4, 5: intuition.
        exists (SimpObs Message' v es2). simpl.
        split;[apply in_cobs_messages';intuition|].
        split;[intuition|].
        destruct (decide (i = v)).
        * exists (SimpObs State' v (s v)). simpl.
          subst v.
          split;[apply in_cobs_states'; apply state_obs_present|].
          apply in_listing.
          split;[intuition|].
          intros contra.
          apply (@state_obs_stuff index i index_listing Hfinite) with (so := so) (i0 := j) in contra.
          unfold s' in Hcomp.
          apply comparable_commutative in contra.
          rewrite state_update_eq in Hcomp by intuition.
          intuition.
          split;[apply Hsnb|intuition].
          intuition.
          simpl. congruence.
          simpl. intuition.
        * unfold s' in *.
          rewrite state_update_neq in Hcomp.
          exists (SimpObs State' v (s v)).
          simpl.
          split;[apply in_cobs_states';apply state_obs_present|].
          apply in_listing.
          split;[simpl;intuition|].
          intros contra.
          apply comparable_commutative in contra.
          all : intuition.
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
        specialize (GE_existing_different_state_message s Hpr i j v Hdif es2 so Hfull Hhave Hine2 Hcomp) as Hev.
        setoid_rewrite <- hbo_cobs. intuition.
    - apply in_cobs_messages in Hine1 as Het1.
      simpl in Het1. subst et1. simpl in Hine1.
      destruct Hine2 as [Hine2|Hine2].
      + apply in_cobs_states in Hine2 as Het2.
        simpl in Het2. subst et2.
        apply unique_state_observation in Hine2. simpl in Hine2.
        inversion Hine2. subst es2.
        rewrite comparable_commutative in Hcomp.
        specialize (GE_existing_different_state_message s Hpr i j v Hdif es1 so Hfull Hhave Hine1 Hcomp) as Hev.
        setoid_rewrite <- hbo_cobs. intuition.
      + apply in_cobs_messages in Hine2 as Het2.
        simpl in Het2. subst et2. simpl in Hine2.
        unfold s' in Hine2. unfold s' in Hine1.
        setoid_rewrite <- cobs_message_existing_other in Hine2.
        setoid_rewrite <- cobs_message_existing_other in Hine1.
        2, 3, 4, 5: intuition.
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
      + apply in_cobs_states in Hine2 as Het2.
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
    assert (Hsonb : so <> Bottom). {
        apply in_cobs_and_message in Hhave.
        apply cobs_single_m in Hhave.
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
              apply Hsnb; intuition.
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
              apply Hsnb; intuition.
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

  Lemma receive_plan_preserves_equivocation
    (s : vstate X)
    (Hpr : protocol_state_prop X s)
    (a : plan X)
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
      + spec IHa. {
          intros ai Hai.
          specialize (Hgood ai).
          spec Hgood. apply in_app_iff. left. intuition.
          intuition.
        }
        simpl in IHa.
        intuition.
      + rewrite H0.
        unfold apply_plan, _apply_plan. simpl.

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
        unfold composite_valid in Hpr_a.
        unfold vvalid in Hpr_a.
        unfold valid in Hpr_a. simpl in Hpr_a.
        subst v.
        destruct input_a eqn : eq_input
        ; [| intuition].
        destruct Hgood as [so [from [Heqm Hinso]]].
        inversion Heqm.
        subst m. simpl in *.
        unfold set_eq.
        inversion eq_trans. clear H3.
        assert (In (SimpObs Message' from so) (cobs res_long from)). {
          specialize (@in_future_message_obs index_listing s res_long Hpr from) as Hf.
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
  Qed.

End Composition.
