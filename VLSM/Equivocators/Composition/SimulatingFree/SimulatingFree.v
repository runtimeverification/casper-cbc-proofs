Require Import
  List Coq.Vectors.Fin FinFun
  Arith.Compare_dec Lia
  Program
  Coq.Logic.JMeq
  .
Import ListNotations.
From CasperCBC
  Require Import
    Preamble ListExtras FinExtras FinFunExtras
    VLSM.Common VLSM.Composition VLSM.Equivocation VLSM.ProjectionTraces
    VLSM.Equivocators.Common VLSM.Equivocators.Projections
    VLSM.Equivocators.MessageProperties
    VLSM.Equivocators.Composition.Common
    VLSM.Equivocators.Composition.Projections
    VLSM.Equivocators.Composition.SimulatingFree.FullReplayTraces
    VLSM.Plans
    .

Section all_equivocating.

Context {message : Type}
  {equiv_index : Type}
  (index := equiv_index)
  {IndEqDec : EqDecision index}
  (IM : index -> VLSM message)
  (Hbs : forall i : index, has_been_sent_capability (IM i))
  {i0 : Inhabited index}
  (X := free_composite_vlsm IM)
  (equivocator_descriptors := equivocator_descriptors IM)
  (index_listing : list index)
  (finite_index : Listing index_listing)
  (equivocators_no_equivocations_vlsm := equivocators_no_equivocations_vlsm IM Hbs finite_index)
  (equivocators_state_project := equivocators_state_project IM)
  (equivocator_IM := equivocator_IM IM)
  (equivocator_descriptors_update := equivocator_descriptors_update IM)
  (proper_equivocator_descriptors := proper_equivocator_descriptors IM)
  (not_equivocating_equivocator_descriptors := not_equivocating_equivocator_descriptors IM)
  (equivocators_trace_project := equivocators_trace_project IM)
  (seed : message -> Prop)
  (SeededXE := seeded_equivocators_no_equivocation_vlsm IM Hbs finite_index seed)
  (SeededX := pre_loaded_vlsm X seed)
  (PreFree := pre_loaded_with_all_messages_vlsm (free_composite_vlsm equivocator_IM))
  .

Local Ltac unfold_transition  Ht :=
  ( unfold transition, equivocator_IM, Common.equivocator_IM, equivocator_vlsm
  , mk_vlsm, machine, projT2, equivocator_vlsm_machine, equivocator_transition
  in Ht).

Local Ltac unfold_equivocators_transition_item_project :=
(
  simpl;
  unfold equivocators_transition_item_project; simpl;
  unfold composite_transition_item_projection; simpl;
  unfold composite_transition_item_projection_from_eq; simpl;
  unfold eq_rect_r; simpl
).


Lemma equivocators_trace_project_skip_full_replay_trace_init'
  (full_replay_state : composite_state equivocator_IM)
  (eqv_descriptors: equivocator_descriptors)
  (Heqv_descriptors: not_equivocating_equivocator_descriptors eqv_descriptors full_replay_state)
  (is : composite_state equivocator_IM)
  (eqvs : list equiv_index)
  : let app_tr :=
     composite_apply_plan equivocator_IM
        full_replay_state
        (map (initial_new_machine_transition_item IM is) eqvs)
  in fold_right
    (equivocators_trace_project_folder IM)
      (Some ([], eqv_descriptors)) (fst app_tr) = Some ([], eqv_descriptors)
    /\ (forall eqv,
      projT1 (snd (app_tr) (eqv)) >= projT1 (full_replay_state (eqv))
      /\ (In eqv eqvs -> projT1 (snd (app_tr) (eqv)) > projT1 (full_replay_state (eqv)))
    ).
Proof.
  induction eqvs using rev_ind
  ; [repeat split; [simpl;lia|intro contra; inversion contra]|].
  rewrite map_app. rewrite (composite_apply_plan_app equivocator_IM).
  match type of IHeqvs with
  | context[let _ := ?a in _] => remember a as tr_app
  end.
  match goal with
  |- context[let _ := let (_, _) := ?a in _ in _] => replace a with tr_app
  end.
  destruct tr_app as (tr_items, tr_final).
  simpl in IHeqvs.
  match goal with
  |- context[let _ := let (_, _) := ?a in _ in _] => remember a as a_app
  end.
  destruct a_app as (a_items, a_final).
  simpl.
  rewrite fold_right_app.
  match goal with
  |- context[fold_right _ ?f _ = _] => remember f as a_fold
  end.
  destruct IHeqvs as [Hproject Hsize].
  simpl in Heqa_app.
  inversion Heqa_app. subst. clear Heqa_app.
  unfold_equivocators_transition_item_project.
  rewrite state_update_eq.
  specialize (Heqv_descriptors x) as Heqv_descriptors_eqv.
  specialize (Hsize x) as Hsize_eqv.
  destruct Hsize_eqv as [Hsize_eqv _].
  destruct (eqv_descriptors x) as [|eqv_i eqv_f] eqn:Heq_eqv
  ; [contradict Heqv_descriptors_eqv|].
  destruct eqv_f; [contradict Heqv_descriptors_eqv|].
  unfold equivocator_vlsm_transition_item_project.
  destruct (tr_final (x)) as (n_tr_final_eqv, s_tr_final_eqv) eqn:Htr_final_eqv.
  unfold equivocator_state_extend at 1.
  simpl in Hsize_eqv.
  simpl in Heqv_descriptors_eqv.
  destruct (le_lt_dec (S (S n_tr_final_eqv)) eqv_i); [lia|].
  destruct (nat_eq_dec (S eqv_i) (S (S n_tr_final_eqv))); [lia|].
  rewrite equivocator_descriptors_update_id; [|assumption].
  split; [assumption|].
  intros eqv'.
  destruct (decide (eqv' = x)).
  - subst eqv'. rewrite state_update_eq. simpl.
    split; [lia|].
    intro. lia.
  - rewrite state_update_neq by assumption.
    specialize (Hsize eqv'). destruct Hsize as [Hsize_all Hsize_eqvs].
    split; [assumption|].
    intro Heqv'.
    apply in_app_iff in Heqv'. destruct Heqv' as [Heqv'| [Heqv' | contra]];
    [..|inversion contra].
    + apply Hsize_eqvs. assumption.
    + subst. elim n0. reflexivity.
Qed.

Lemma equivocators_trace_project_skip_full_replay_trace_init
  (full_replay_state : composite_state equivocator_IM)
  (eqv_descriptors: equivocator_descriptors)
  (Heqv_descriptors: not_equivocating_equivocator_descriptors eqv_descriptors full_replay_state)
  (is : composite_state equivocator_IM)
  : let app_tr :=
     composite_apply_plan equivocator_IM
        full_replay_state
        (spawn_initial_state IM index_listing is)
  in fold_right
    (equivocators_trace_project_folder IM)
      (Some ([], eqv_descriptors)) (fst app_tr) = Some ([], eqv_descriptors)
    /\ forall eqv, projT1 (snd (app_tr) (eqv)) > projT1 (full_replay_state (eqv)).
Proof.
  specialize
    (equivocators_trace_project_skip_full_replay_trace_init'
      _ _ Heqv_descriptors is index_listing
    ) as Hinit.
  match type of Hinit with
  | let _ := ?a in _ => remember a as app
  end.
  match goal with
  |- let _ := ?a in _ => replace a with app
  end.
  destruct Hinit as [Hproject Hsize].
  split; [assumption|].
  intro eqv. spec Hsize eqv. destruct Hsize as [_ Hsize].
  apply Hsize.
  apply (proj2 finite_index).
Qed.

Lemma equivocators_trace_project_skip_full_replay_trace
  (full_replay_state : composite_state equivocator_IM)
  (eqv_descriptors: equivocator_descriptors)
  (Heqv_descriptors: not_equivocating_equivocator_descriptors eqv_descriptors full_replay_state)
  (tr : list (composite_transition_item equivocator_IM))
  (is_final : composite_state equivocator_IM)
  (His_final_size : forall eqv, projT1 (is_final (eqv)) > projT1 (full_replay_state (eqv)))
  : let app_tr :=
    composite_apply_plan equivocator_IM is_final
      (map
         (update_equivocators_transition_item_descriptor IM full_replay_state)
         tr)
  in fold_right
    (equivocators_trace_project_folder IM)
      (Some ([], eqv_descriptors)) (fst app_tr) = Some ([], eqv_descriptors)
    /\ forall eqv, projT1 (snd (app_tr) (eqv)) > projT1 (full_replay_state (eqv)).
Proof.
  induction tr using rev_ind
  ; [split; [reflexivity|]; assumption|].
  rewrite map_app. rewrite (composite_apply_plan_app equivocator_IM).
  match type of IHtr with
  | context[let _ := ?a in _] => remember a as tr_app
  end.
  match goal with
  |- context[let _ := let (_, _) := ?a in _ in _] => replace a with tr_app
  end.
  destruct tr_app as (tr_items, tr_final).
  simpl in IHtr.
  match goal with
  |- context[let _ := let (_, _) := ?a in _ in _] => remember a as a_app
  end.
  destruct a_app as (a_items, a_final).
  simpl.
  rewrite fold_right_app.
  match goal with
  |- context[fold_right _ ?f _ = _] => remember f as a_fold
  end.
  destruct IHtr as [Hproject Hsize].
  simpl in Heqa_app.
  unfold composite_apply_plan, _apply_plan in Heqa_app.
  simpl in Heqa_app.
  unfold update_equivocators_transition_item_descriptor in Heqa_app.
  destruct x. destruct l as (eqv, li).
  destruct li as (li, di).
  specialize (Heqv_descriptors eqv) as Heqv_descriptors_eqv.
  destruct (eqv_descriptors eqv) as [|eqv_i eqv_f] eqn:Heq_eqv
  ; [contradict Heqv_descriptors_eqv|].
  destruct eqv_f; [contradict Heqv_descriptors_eqv|].
  simpl in Heqv_descriptors_eqv.
  specialize (Hsize eqv) as Hsize_eqv.
  destruct di as [s_di|j_di f_di].
  + simpl in Heqa_app. inversion Heqa_app. subst. clear Heqa_app.
    unfold_equivocators_transition_item_project.
    rewrite Heq_eqv. unfold equivocator_vlsm_transition_item_project.
    rewrite state_update_eq.
    destruct (tr_final (eqv)) as (n_tr_final_eqv, s_tr_final_eqv) eqn:Htr_final_eqv.
    simpl in Hsize_eqv.
    unfold equivocator_state_extend at 1.
    destruct (le_lt_dec (S (S n_tr_final_eqv)) eqv_i); [lia|].
    destruct (nat_eq_dec (S eqv_i) (S (S n_tr_final_eqv))); [lia|].
    rewrite equivocator_descriptors_update_id; [|assumption].
    split; [assumption|].
    intros eqv'.
    destruct (decide (eqv' = eqv)).
    * subst eqv'. rewrite state_update_eq. simpl. lia.
    * rewrite state_update_neq; [|assumption]. apply Hsize.
  + destruct
    (vtransition (equivocator_IM eqv)
      (li, Existing (IM eqv) (j_di + S (projT1 (full_replay_state eqv))) f_di)
      (tr_final eqv, input)
    ) as (str_final_eqv', omtr_final_eqv') eqn:Ht_tr_final_eqv.
    simpl in Heqa_app. inversion Heqa_app. subst a_items a_final. clear Heqa_app.
    simpl in Heqa_fold.
    subst.
    unfold_equivocators_transition_item_project.
    rewrite Heq_eqv. unfold equivocator_vlsm_transition_item_project.
    rewrite state_update_eq.
    destruct str_final_eqv' as (nstr_final_eqv', bstr_final_eqv').
    unfold vtransition in Ht_tr_final_eqv.
    unfold_transition Ht_tr_final_eqv. unfold snd in Ht_tr_final_eqv.
    destruct
      (le_lt_dec (S (projT1 (tr_final eqv))) (j_di + S (projT1 (full_replay_state eqv)))).
    * inversion Ht_tr_final_eqv. subst. clear Ht_tr_final_eqv.
      rewrite H0 in *. simpl in l, Hsize_eqv.
      destruct (le_lt_dec (S nstr_final_eqv') eqv_i); [lia|].
      rewrite! eq_dec_if_false by lia.
      match goal with
      |- context [if f_di then ?x else ?x] =>
        replace (if f_di then x else x) with x
          by (destruct f_di; reflexivity)
      end.
      rewrite! equivocator_descriptors_update_id by assumption.
      split; [assumption|].
      intros eqv'.
      destruct (decide (eqv' = eqv)).
      ++ subst eqv'. rewrite state_update_eq. simpl. lia.
      ++ rewrite state_update_neq by assumption. apply Hsize.
    * destruct (tr_final eqv) as (ntr_final_eqv, btr_final_eqv) eqn:Heqtr_final_eqv.
      unfold projT2, fst in Ht_tr_final_eqv.
      destruct
        (vtransition (IM eqv) li (btr_final_eqv (of_nat_lt l), input))
        as (btr_final_eqv_l', ombtr_final_eqv_l') eqn:Ht_tr_final_eqv_l.
      simpl in Hsize_eqv.
      destruct f_di
      ; inversion Ht_tr_final_eqv; subst; simpl_existT; subst; clear Ht_tr_final_eqv
      ; match goal with
        |- context [le_lt_dec ?a ?b] => destruct (le_lt_dec a b); [lia|]
        end
      ; rewrite eq_dec_if_false by lia
      ; rewrite equivocator_descriptors_update_id by assumption
      ; split; [assumption| |assumption|]
      ; intros eqv'
      ; destruct (decide (eqv' = eqv)).
      -- subst eqv'. rewrite state_update_eq. simpl. lia.
      -- rewrite state_update_neq by assumption. apply Hsize.
      -- subst eqv'. rewrite state_update_eq. simpl. lia.
      -- rewrite state_update_neq by assumption. apply Hsize.
Qed.

Lemma equivocators_trace_project_skip_full_replay_trace_full
  (full_replay_state : composite_state equivocator_IM)
  (is : composite_state equivocator_IM)
  (tr : list (composite_transition_item equivocator_IM))
  (eqv_descriptors: equivocator_descriptors)
  (Heqv_descriptors: not_equivocating_equivocator_descriptors eqv_descriptors full_replay_state)
  : equivocators_trace_project eqv_descriptors
      (replayed_trace_from IM index_listing full_replay_state is tr) =
    Some ([], eqv_descriptors).
Proof.
  unfold replayed_trace_from, applied_replay_plan_from, replay_plan_from.
  rewrite (composite_apply_plan_app equivocator_IM).
  destruct
    (composite_apply_plan equivocator_IM
      full_replay_state
      (spawn_initial_state IM index_listing is))
    as (is_items, is_final) eqn:His.
  destruct
    (composite_apply_plan equivocator_IM
      is_final
      (map
          (update_equivocators_transition_item_descriptor IM full_replay_state) tr)
    ) as (tr_items, tr_final) eqn:Htr.
  simpl.
  unfold equivocators_trace_project.
  unfold Projections.equivocators_trace_project.
  rewrite fold_right_app.
  specialize
    (equivocators_trace_project_skip_full_replay_trace_init
      _ _ Heqv_descriptors is
    )
  as Hinit.
  simpl in Hinit, His. rewrite! His in Hinit.
  simpl in Hinit.
  destruct Hinit as [Hproject Hsize].
 specialize
  (equivocators_trace_project_skip_full_replay_trace
    _ _ Heqv_descriptors tr is_final Hsize
  )
  as Htrace.
  simpl in Htrace.
  rewrite! Htr in Htrace.
  simpl in Htrace.
  destruct Htrace as [Htrace _].
  match goal with
  |- fold_right _ ?f _ = _ => replace f with (Some (@nil (composite_transition_item IM), eqv_descriptors))
  end.
  assumption.
Qed.

Lemma equivocators_protocol_vlsm_run_project
  (runX : vproto_run SeededX)
  (HrunX : vlsm_run_prop SeededX runX)
  : exists
    (run : vproto_run SeededXE)
    (Hrun : vlsm_run_prop SeededXE run)
    (eqv_descriptors : equivocator_descriptors)
    (Heqv : not_equivocating_equivocator_descriptors eqv_descriptors (fst (final run)))
    (Hproject : equivocators_trace_project eqv_descriptors (transitions run)
      = Some (transitions runX, zero_descriptor _))
    (Hdestination : equivocators_state_project eqv_descriptors (fst (final run)) = fst (final runX))
    (Houtput : snd (final run) = snd (final runX)),
    equivocators_state_project (zero_descriptor _) (start run) = start runX.
Proof.
  induction HrunX.
  - specialize (lift_initial_to_equivocators_state IM Hbs finite_index is His) as Hs.
    remember (lift_to_equivocators_state IM is) as s.
    exists (@mk_proto_run _ (type SeededXE) s [] (s, None)).
    split; [constructor; assumption|].
    exists (zero_descriptor _).
    split; [apply zero_descriptor_not_equivocating|].
    exists eq_refl.
    subst.
    simpl.
    assert
      (Hproject : equivocators_state_project (zero_descriptor IM)
        (lift_to_equivocators_state IM is) = is)
    ; [|exists Hproject; exists eq_refl; assumption].
    apply functional_extensionality_dep_good.
    reflexivity.
  - rename s into is, Hs into His.
    simpl.
    pose ((exist _ is His) : vinitial_state SeededX) as v.
    pose ((fun i => mk_singleton_state _ (is i)) :
          vstate SeededXE) as is'.
    assert (vinitial_state_prop _ is') as His'.
    {
      intro i. apply mk_singleton_initial_state. apply His.
    }
    pose ((exist _ is' His') : vinitial_state SeededXE) as vsz.
    exists (@mk_proto_run _ (type SeededXE) (proj1_sig vsz) [] ((proj1_sig vsz), Some im)).
    assert (Him' : vinitial_message_prop SeededXE im).
    { unfold vinitial_message_prop. simpl.
      destruct Him as [(eqv, ((imi, Himi), Himeq)) | Hseedim].
      - subst im. simpl in *. left.
        exists eqv. simpl in *.
        exists (exist _ imi Himi). reflexivity.
      - right. assumption.
    }
    split; [apply (empty_run_initial_message SeededXE im Him'); apply proj2_sig|].
    exists (zero_descriptor _).
    split; [apply zero_descriptor_not_equivocating|].
    exists eq_refl. unfold final. unfold start. unfold fst. unfold snd.
    assert
      (Hproject : equivocators_state_project (zero_descriptor IM) (` vsz) = is)
    ; [| exists Hproject; exists eq_refl; assumption].
    unfold vsz, is'; simpl.
    apply functional_extensionality_dep_good.
    reflexivity.
  - destruct IHHrunX1 as [eqv_state_run [Heqv_state_run [eqv_state_descriptors [Heqv_state_descriptors [Hstate_project [Hstate_final_project [_ Hstate_start_project]]]]]]].
    destruct IHHrunX2 as [eqv_msg_run [Heqv_msg_run [eqv_msg_descriptors [Heqv_msg_descriptors [Hmsg_project [_ [Hom Hmsg_start_project]]]]]]].
    specialize (run_is_trace SeededXE (exist _ _ Heqv_state_run))
      as Hstate_trace.
    simpl in Hstate_trace.
    specialize
      (vlsm_run_last_state SeededX
        (exist _ _ HrunX1)
      ) as Hstate_final.
    simpl in Hstate_final.
    simpl in Hstate_final_project.
    rewrite <- Hstate_final in Hstate_final_project.
    specialize (run_is_trace SeededXE (exist _ _ Heqv_msg_run))
      as Hmsg_trace.
    specialize
      (finite_ptrace_last_pstate SeededXE _ _ (proj1 Hstate_trace))
      as Hstate_protocol.
    simpl in Hmsg_trace.
    specialize
      (replayed_trace_from_protocol_equivocating
        IM Hbs index_listing finite_index
        _ _ Hstate_protocol _ _ Hmsg_trace
      )
      as Hmsg_trace_full_replay.
    simpl in Hmsg_trace_full_replay.
    match type of Hmsg_trace_full_replay with
    | finite_protocol_trace_from _ _ ?EMsgTr =>
      remember EMsgTr as emsg_tr
    end.
    specialize
      (finite_protocol_trace_from_app_iff SeededXE
        (start eqv_state_run) (transitions eqv_state_run)
        emsg_tr
      ) as Happ.
    apply proj1 in Happ.
    specialize (Happ (conj (proj1 Hstate_trace) Hmsg_trace_full_replay)).
    simpl.
    specialize
      (extend_right_finite_trace_from SeededXE _ _ Happ) as Happ_extend.
    destruct l as (eqv, li).
    specialize (Heqv_state_descriptors eqv) as Heqv_state_descriptors_i.
    destruct (eqv_state_descriptors eqv) as [| eqv_state_descriptors_i eqv_state_descriptors_f]
    eqn:Heqv_state_descriptors_eqv
    ; [contradict Heqv_state_descriptors_i|].
    destruct eqv_state_descriptors_f; [contradict Heqv_state_descriptors_i|].
    pose
      (existT (fun i : index => vlabel (equivocator_IM i)) (eqv) (li, Existing (IM (eqv)) eqv_state_descriptors_i false))
      as el.
    pose (last (map destination (transitions eqv_state_run ++ emsg_tr))
      (start eqv_state_run))
      as es.

    destruct (vtransition SeededXE el (es, om))
      as (es', om') eqn:Hesom'.
    specialize
      (Happ_extend  el om es' om').
    unfold protocol_transition in Happ_extend.
    match type of Happ_extend with
    | context [?t = _] =>
      replace t with (es', om')
    end.
    simpl in Heqv_state_descriptors_i.
    assert (Heqv_t := Hesom').
    unfold vtransition in Hesom'. simpl in Hesom'.
    unfold vtransition in Hesom'.
    match type of Hesom' with
    | (let (_, _) := ?t in _) = _ => remember t as tesom'
    end.
    unfold_transition Heqtesom'. unfold snd in Heqtesom'.
    subst tesom'.
    destruct
      (replayed_trace_from_state_correspondence
        IM Hbs index_listing finite_index seed
        (last (map destination (transitions eqv_state_run)) (start eqv_state_run))
        _  _ Hmsg_trace
      )
      as [Houtput Hstate].
    specialize (Hstate eqv) as Hstate_eqv.
    destruct Hstate_eqv as [Hstate_size [Hstate_msg Hstate_state]].
    spec Hstate_state eqv_state_descriptors_i.

    remember (last (map destination (transitions eqv_state_run ++ emsg_tr)) (start eqv_state_run))
      as ess.
    rewrite map_app in Heqess. rewrite last_app in Heqess.
    specialize
      (vlsm_run_last_state SeededXE
        (exist _ _ Heqv_state_run)
      ) as Heqv_state_final.
    simpl in Heqv_state_final.
    simpl in Heqess, Hstate_state, Heqemsg_tr.
    rewrite Heqv_state_final in Heqess, Heqemsg_tr, Hstate_state.
    specialize (Hstate_state Heqv_state_descriptors_i) as Hstate_state_i.
    destruct Hstate_state_i as [Heqv_merged_descriptors_i Hstate_state_i].
    rewrite Heqemsg_tr in Heqess.
    change ess with es in Happ_extend.
    subst ess. unfold es in Hesom'.

    match type of Hesom' with
    | context [le_lt_dec ?X ?Y] =>
       destruct (le_lt_dec X Y)
    end
    ; [lia|].
    replace (of_nat_lt l) with (of_nat_lt Heqv_merged_descriptors_i) in Hesom' by apply of_nat_ext. clear l.
    rewrite Hstate_state_i in Hesom'.
    unfold fst in Hesom' at 1.
    specialize (equal_f_dep Hstate_final_project (eqv)) as Hstate_final_project_eqv.
    unfold equivocators_state_project in Hstate_final_project_eqv.
    unfold Common.equivocators_state_project in Hstate_final_project_eqv.
    unfold equivocator_state_descriptor_project in Hstate_final_project_eqv.
    unfold equivocator_state_project in Hstate_final_project_eqv.
    rewrite Heqv_state_descriptors_eqv in Hstate_final_project_eqv.
    match type of Heqv_state_descriptors_i with
    | context [projT1 ?s] => destruct s as (n_eqv_state_run_eqv, s_eqv_state_run_eqv) eqn:Heqeqv_state_run_eqv
    end.
    simpl in Heqv_state_descriptors_i.
    destruct (le_lt_dec (S n_eqv_state_run_eqv) eqv_state_descriptors_i); [lia|].
    replace (of_nat_lt l) with (of_nat_lt Heqv_state_descriptors_i) in Hstate_final_project_eqv by apply of_nat_ext. clear l.
    simpl in Hesom', Hstate_final_project_eqv.
    rewrite Hstate_final_project_eqv in Hesom'.
    rewrite Hstate_final in Hesom'.
    simpl in som'.
    remember som' as som''. unfold som' in *. clear som'.
    unfold s in Heqsom''. simpl in Heqsom''.
    match type of Heqsom'' with
    | _ = (let (_,_) := ?t in _)  => destruct t as (si', om'') eqn:Ht
    end.
    subst som''. simpl.
    inversion Hesom'. clear Hesom'. subst om''.

    spec Happ_extend.
    {
      split; [|assumption].
      specialize (finite_ptrace_last_pstate SeededXE _ _ Happ) as Hps.
      rewrite map_app in Hps.
      rewrite last_app in Hps. simpl in Hps.
      rewrite Heqv_state_final in Hps.
      split; [subst; assumption|].
      assert (Hpom : option_protocol_message_prop SeededXE om).
      { exists (fst (final eqv_msg_run)).
        unfold om. rewrite <- Hom.
        specialize
          (run_is_protocol SeededXE
            (exist _ _ Heqv_msg_run)
          ) as Hpom.
        simpl in Hpom.
        destruct (final eqv_msg_run) eqn:Hfin. simpl.
        simpl in *. rewrite Hfin in Hpom.
        assumption.
      }
      split; [assumption|].
      split.
      - simpl. unfold vvalid. simpl.
        exists Heqv_merged_descriptors_i.
        unfold es.
        rewrite Hstate_state_i. simpl.
        rewrite Hstate_final_project_eqv.
        rewrite Hstate_final. clear -Hv.
        simpl in Hv. destruct Hv as [Hv _].
        assumption.
      - split; [|exact I].
        unfold om in *. destruct (snd (final msg_run)) eqn:Hm; [|exact I].
        destruct (null_dec (transitions eqv_msg_run)).
        + right.
          apply (vlsm_run_no_transitions_output SeededXE)
            with (run := eqv_msg_run); assumption.
        + left. apply proper_sent.
          {
            specialize (finite_ptrace_last_pstate SeededXE _ _ Happ)
              as Hlst.
            rewrite map_app, last_app in Hlst. simpl in Hlst.
            rewrite Heqv_state_final in Hlst.
            subst. subst es.
            revert Hlst.
            apply VLSM_incl_protocol_state.
            apply seeded_equivocators_incl_preloaded.
          }
          specialize
            (vlsm_run_last_final SeededXE (exist _ _ Heqv_msg_run))
            as Hfinal.
          simpl in Hfinal.
          spec Hfinal n.
          assert
            (Happ_pre :
              finite_protocol_trace PreFree
                (start eqv_state_run) (transitions eqv_state_run ++ emsg_tr)).
          {
            apply VLSM_incl_finite_protocol_trace; [apply seeded_equivocators_incl_preloaded|].
            split; [assumption|].
            apply vlsm_run_initial_state. assumption.
          }
          assert
            (Hbs_free : has_been_sent_capability (free_composite_vlsm equivocator_IM)).
          { exact (composite_has_been_sent_capability equivocator_IM (free_constraint equivocator_IM) finite_index (equivocator_Hbs IM Hbs)).
          }
          assert
            (Hlst :
              last (map destination (transitions eqv_state_run ++ emsg_tr))
                (start eqv_state_run) = es
            ).
          { rewrite map_app, last_app.
            simpl.
            unfold es.
            rewrite !Heqv_state_final. subst. reflexivity.
          }
          assert
            (Hes_pre : protocol_state_prop
              (pre_loaded_with_all_messages_vlsm
                (free_composite_vlsm (Common.equivocator_IM IM))) es).
          { rewrite <- Hlst. apply (finite_ptrace_last_pstate PreFree). apply Happ_pre.
          }
          apply has_been_sent_consistency; [assumption| assumption| ].
          eexists _. eexists _. exists Happ_pre, Hlst.

          apply Exists_app. right. subst.
          spec Houtput n.
          clear - Hfinal Houtput Hom n Heqv_state_final.
          simpl in Heqv_state_final, Houtput.
          rewrite Heqv_state_final in Houtput.
          destruct Hfinal as [_ Hfinal].
          simpl in *.
          rewrite Hom in Hfinal.
          match type of Houtput with
          | ?A = ?B => replace A with (Some (Some m)) in Houtput
          end.
          simpl in *.
          match goal with
          |- Exists _ ?new => remember new as newtr
          end.
          clear Heqnewtr.
          destruct (null_dec newtr)
           ; [subst; discriminate Houtput|].
          apply exists_last in n0.
          destruct n0 as [newtr' [lst Hnewtr]].
          subst newtr.
          apply Exists_exists. exists lst.
          rewrite last_error_is_last in Houtput. simpl in Houtput.
          inversion Houtput. symmetry in H0.
          split; [|assumption].
          apply in_app_iff. right. left. reflexivity.
    }
    destruct
      (trace_is_run SeededXE _ _
        (conj Happ_extend (proj2 Hstate_trace))
      )
      as [eqv_merged_run [Heqv_merged_run [Heqv_merged_run_start Heqv_merged_run_transitions]]].
    exists eqv_merged_run.
    exists Heqv_merged_run.
    exists eqv_state_descriptors.
    specialize
      (vlsm_run_last_final SeededXE (exist _ _ Heqv_merged_run))
      as Hmerged_final.
    simpl in Hmerged_final. simpl in Heqv_merged_run_transitions.
    rewrite Heqv_merged_run_transitions in Hmerged_final.
    spec Hmerged_final; [apply last_not_null|].
    rewrite last_error_is_last in Hmerged_final. simpl in Hmerged_final.
    destruct Hmerged_final as [Hfinal_es Hfinal_om].
    inversion Hfinal_es as [Hfinal_es']. rewrite <- Hfinal_es'.
    inversion Hfinal_om as [Hfinal_om']. rewrite <- Hfinal_om'.
    assert (Hnext_state_descriptors : not_equivocating_equivocator_descriptors eqv_state_descriptors es').
    { intro eqv'. spec Heqv_state_descriptors eqv'.
      specialize (Hstate eqv').
      destruct Hstate as [Hstate_size' _].
      destruct (eqv_state_descriptors eqv') as [| eqv_state_descriptors_i' eqv_state_descriptors_f']
      eqn:Heqv_state_descriptors_eqv'
      ; [contradict Heqv_state_descriptors|].
      destruct eqv_state_descriptors_f'; [contradict Heqv_state_descriptors|].
      simpl in Heqv_state_descriptors. simpl.
      subst es'.
      simpl in Hstate_size'.
      rewrite Heqv_state_final in Hstate_size'.
      destruct (decide (eqv' = eqv)).
      - inversion e. subst. rewrite state_update_eq.
        rewrite equivocator_state_update_size.
        lia.
      - rewrite state_update_neq; [|assumption].
        lia.
    }
    exists Hnext_state_descriptors.
    match type of H0 with
    | state_update _ _ _ ?e = _ => remember e as esu
    end.
    match type of Heqesu with
    | context [equivocator_state_update _ ?l _ _] => remember l as lst
    end.
    assert (Hesu_size : projT1 esu = projT1 lst)
      by (subst; apply equivocator_state_update_size).
    assert
      (Hproject :
        equivocators_state_project eqv_state_descriptors es' =
        state_update IM (fst (final state_run)) (eqv) si'
      ).
    {
      subst es'.
      apply functional_extensionality_dep_good.
      intro i.
      unfold equivocators_state_project.
      rewrite equivocators_state_project_state_update_eqv.
      rewrite Heqv_state_descriptors_eqv.
      destruct (le_lt_dec (S (projT1 esu)) eqv_state_descriptors_i)
      ; [subst; rewrite equivocator_state_update_size in l; lia|].
      f_equal.
      - specialize
        (replayed_trace_from_full_replay_state_project IM Hbs _ finite_index seed
          (fst (final eqv_state_run)) (start eqv_msg_run)
          _ Hmsg_trace eqv_state_descriptors
        ) as Hproject.
        spec Hproject
        ; [apply not_equivocating_equivocator_descriptors_proper; assumption|].
        destruct Hproject as [_ Hproject].
        simpl in Hproject.
        rewrite Hproject.
        simpl.
        rewrite <- Hstate_final.
        assumption.
      - clear - Heqesu.
        subst.
        simpl.
        rewrite eq_dec_if_true; [reflexivity|].
        apply of_nat_ext.
    }
    repeat split
    ; [
      | apply Hproject
      | simpl in *; rewrite Heqv_merged_run_start; rewrite Hstate_start_project; reflexivity].
    rewrite Heqv_merged_run_transitions.
    rewrite <- app_assoc.
    unfold equivocators_trace_project.
    unfold Projections.equivocators_trace_project.
    rewrite fold_right_app.
    rewrite fold_right_app.
    unfold fold_right at 3.
    match goal with
    |- fold_right _ (fold_right _ ?l1 _) _ = _ => remember l1 as last_prj
    end.
    match goal with
    |- context [ts ++ ?l] => remember l as last_item
    end.
    assert (last_prj = Some (last_item, eqv_state_descriptors)).
    { subst last_prj. subst last_item.
      unfold equivocators_trace_project_folder.
      subst el.
      unfold_equivocators_transition_item_project.
      simpl in Hproject.
      rewrite <- Hproject.
      rewrite Heqv_state_descriptors_eqv.
      unfold equivocator_vlsm_transition_item_project.
      rewrite <- H0.
      rewrite state_update_eq.
      destruct esu as (n_esu, s_esu) eqn:Hesu.
      destruct (le_lt_dec (S n_esu) eqv_state_descriptors_i)
      ; [simpl in *; subst; lia|].
      rewrite eq_dec_if_true by reflexivity.
      simpl.
      repeat f_equal.
      apply equivocator_descriptors_update_id.
      assumption.
    }
    rewrite H.
    assert (equivocators_trace_project eqv_state_descriptors emsg_tr = Some ([], eqv_state_descriptors)).
    {
      subst emsg_tr.
      apply equivocators_trace_project_skip_full_replay_trace_full. assumption.
    }
    specialize
      (equivocators_trace_project_folder_additive IM
        _ last_item _ _ _ H1
      ) as Hmsg_tr.
    simpl in Hmsg_tr.
    match goal with
    |- fold_right _ ?r _ = _ => replace r with (Some (last_item, eqv_state_descriptors))
    end.
    clear Hmsg_tr.
    specialize
      (equivocators_trace_project_folder_additive IM
        _ last_item _ _ _ Hstate_project
      ) as Heqv_state.
    assumption.
Qed.

Lemma seeded_equivocators_protocol_trace_project_rev
  (isX : composite_state IM)
  (trX : list (composite_transition_item IM))
  (HtrX : finite_protocol_trace SeededX isX trX)
  : exists
    (is : composite_state equivocator_IM)
    (tr : list (composite_transition_item equivocator_IM))
    (Htr : finite_protocol_trace SeededXE is tr)
    (eqv_descriptors : equivocator_descriptors)
    (Hproject : equivocators_trace_project eqv_descriptors tr = Some (trX, zero_descriptor _)),
    equivocators_state_project (zero_descriptor _) is = isX.
Proof.
  destruct (trace_is_run SeededX _ _ HtrX) as [runX [HrunX [_HstartX _HtrX]]].
  subst.
  destruct
    (equivocators_protocol_vlsm_run_project
      _ HrunX
    )
    as [run [Hrun [descriptors [Hproper [Hproject [Hfinal_state [Hfinal_msg Hstart]]]]]]].
  exists (start run).
  exists (transitions run).
  specialize (run_is_trace SeededXE (exist _ _ Hrun)) as Htr.
  simpl in Htr.
  exists Htr.
  exists descriptors.
  exists Hproject.
  exact Hstart.
Qed.

End all_equivocating.

Lemma equivocators_protocol_trace_project_rev
  {message : Type}
  {index : Type}
  {IndEqDec : EqDecision index}
  {i0 : Inhabited index}
  (IM : index -> VLSM message)
  (X := free_composite_vlsm IM)
  (isX : vstate X)
  (trX : list (vtransition_item X))
  (HtrX : finite_protocol_trace X isX trX)
  {index_listing : list index}
  (finite_index : Listing index_listing)
  (Hbs : forall i : index, has_been_sent_capability (IM i))
  (equivocators_no_equivocations_vlsm := equivocators_no_equivocations_vlsm IM Hbs finite_index)
  : exists
    (is : vstate equivocators_no_equivocations_vlsm)
    (tr : list (composite_transition_item (equivocator_IM IM)))
    (Htr : finite_protocol_trace equivocators_no_equivocations_vlsm is tr)
    (eqv_descriptors : equivocator_descriptors IM)
    (Hproject : equivocators_trace_project IM eqv_descriptors tr = Some (trX, zero_descriptor _)),
    equivocators_state_project IM (zero_descriptor _) is = isX.
Proof.
  specialize (vlsm_is_pre_loaded_with_False X) as Hincl.
  apply VLSM_eq_incl_iff in Hincl. apply proj1 in Hincl.
  assert (HtrX' : finite_protocol_trace (pre_loaded_vlsm X (fun _ => False)) isX trX).
  {
    revert HtrX.
    apply VLSM_incl_finite_protocol_trace. apply Hincl.
  }
  destruct
    (seeded_equivocators_protocol_trace_project_rev IM Hbs _ finite_index
       _ _ _ HtrX'
    )
    as [is [tr [Htr [descriptors [Hpr_tr Hpr_is]]]]].
  exists is, tr.
  split; [|exists descriptors, Hpr_tr; assumption].
  revert Htr.
  apply VLSM_incl_finite_protocol_trace.
  match goal with
  |- context [projT2 (projT2 ?M)] => apply VLSM_incl_trans with (machine M)
    ; [specialize (vlsm_is_pre_loaded_with_False M) |]
  end.
  - intro Heq. apply VLSM_eq_incl_iff in Heq. apply proj2 in Heq.
    apply Heq.
  - apply basic_VLSM_incl.
    + intros. assumption.
    + intros. apply initial_message_is_protocol. assumption.
    + intros l s om [Hs [Hom [Hv [Hc _]]]].
      repeat split; [assumption|].
      destruct om; [|exact I]. simpl in *.
      apply or_assoc in Hc.
      destruct Hc as [Hc | Hfalse]; [|contradiction].
      assumption.
    + intros; reflexivity.
Qed.
