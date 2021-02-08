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
  (equivocators_choice := equivocators_choice IM)
  (index_listing : list index)
  (finite_index : Listing index_listing)
  (equivocators_no_equivocations_vlsm := equivocators_no_equivocations_vlsm IM Hbs index_listing finite_index)
  (equivocators_state_project := equivocators_state_project IM)
  (equivocator_IM := equivocator_IM IM)
  (equivocators_choice_update := equivocators_choice_update IM)
  (proper_equivocators_choice := proper_equivocators_choice IM)
  (equivocators_trace_project := equivocators_trace_project IM Hbs)
  .

Local Tactic Notation "unfold_transition"  hyp(Ht) :=
  ( unfold transition in Ht; unfold Common.equivocator_IM in Ht;
  unfold equivocator_vlsm in Ht; unfold mk_vlsm in Ht;
  unfold machine in Ht; unfold projT2 in Ht;
  unfold equivocator_vlsm_machine in Ht; unfold equivocator_transition in Ht).

Definition update_euivocators_transition_item_descriptor
  (s : vstate equivocators_no_equivocations_vlsm)
  (item : vtransition_item equivocators_no_equivocations_vlsm)
  : vplan_item equivocators_no_equivocations_vlsm
  :=
  match item with
  | {| l := l; input := input; destination := destination; output := output |} =>
    let (e, l) := l in
    let (l, d) := l in
    match d with
    | NewMachine _ sn =>
      @Build_plan_item message (type equivocators_no_equivocations_vlsm)
        (@existT index (fun n : index => vlabel (equivocator_IM n)) (e) (l, d)) input
    | Existing _ i fi =>
      @Build_plan_item message (type equivocators_no_equivocations_vlsm)
        (@existT index (fun n : index => vlabel (equivocator_IM n)) (e)
          (l, Existing _ (i + S (projT1 (s (e)))) fi)
        )
        input
    end
  end.

Definition initial_new_machine_transition_item
  (is : vstate equivocators_no_equivocations_vlsm)
  (eqv : equiv_index)
  : vplan_item equivocators_no_equivocations_vlsm
  :=
  let seqv := is (eqv) in
  let new_l :=
    (@existT index (fun n : index => vlabel (equivocator_IM n)) (eqv)
      (vl0 (IM (eqv)), NewMachine _ (projT2 seqv (of_nat_lt (Hzero _ seqv))))
    )
    in
  @Build_plan_item message (type equivocators_no_equivocations_vlsm) new_l None.

Lemma equivocators_no_equivocations_vlsm_newmachine_always_valid
  (s : vstate equivocators_no_equivocations_vlsm)
  (a : vplan equivocators_no_equivocations_vlsm)
  (eqv : equiv_index)
  (sn : vstate (IM (eqv)))
  (Hsn : vinitial_state_prop (IM (eqv)) sn)
  (constraint :  composite_label equivocator_IM -> composite_state equivocator_IM * option message -> Prop)
  (Hconstraint_subsumption :
    constraint_subsumption equivocator_IM
      (equivocators_no_equivocations_constraint IM Hbs _ finite_index)
      constraint
  )
  : vvalid (equivocators_constrained_vlsm IM constraint)
      (@existT index (fun n : index => vlabel (equivocator_IM n)) (eqv)
        (vl0 (IM (eqv)), NewMachine _ sn))
      (snd (apply_plan equivocators_no_equivocations_vlsm s a), None).
Proof.
  split.
  - split; [assumption|reflexivity].
  - apply Hconstraint_subsumption. exact I.
Qed.

Definition spawn_initial_state
  (is : vstate equivocators_no_equivocations_vlsm)
  : vplan equivocators_no_equivocations_vlsm
  := map (initial_new_machine_transition_item is) index_listing.

Definition replay_trace_from
  (full_replay_state : vstate equivocators_no_equivocations_vlsm)
  (is : vstate equivocators_no_equivocations_vlsm)
  (tr : list (vtransition_item equivocators_no_equivocations_vlsm))
  : list (vtransition_item equivocators_no_equivocations_vlsm)
  :=
  let initial := spawn_initial_state is in
  let reindex := map (update_euivocators_transition_item_descriptor full_replay_state) tr in
  fst (apply_plan equivocators_no_equivocations_vlsm full_replay_state (initial ++ reindex)).

Lemma replay_trace_from_app
  (full_replay_state : vstate equivocators_no_equivocations_vlsm)
  (is : vstate equivocators_no_equivocations_vlsm)
  (tra trb : list (vtransition_item equivocators_no_equivocations_vlsm))
  (eqva := replay_trace_from full_replay_state is tra)
  (lsta := last (map destination eqva) full_replay_state)
  : replay_trace_from full_replay_state is (tra ++ trb) =
    eqva ++
    fst
      (apply_plan equivocators_no_equivocations_vlsm lsta
        (map (update_euivocators_transition_item_descriptor full_replay_state) trb)
      ).
Proof.
  unfold lsta, eqva. clear lsta eqva.
  unfold replay_trace_from in *.
  rewrite map_app at 1.
  rewrite app_assoc.
  rewrite apply_plan_app at 1.
  destruct
    (apply_plan equivocators_no_equivocations_vlsm full_replay_state
      (spawn_initial_state is ++ map (update_euivocators_transition_item_descriptor full_replay_state) tra)
    ) as (tra_items, tra_final) eqn:Htra.
  unfold fst at 2. unfold fst at 3.
  specialize
    (apply_plan_last equivocators_no_equivocations_vlsm full_replay_state
      (spawn_initial_state is ++
        map (update_euivocators_transition_item_descriptor full_replay_state) tra)
    ) as Hlst.
  rewrite Htra in Hlst. simpl in Hlst.
  simpl. rewrite Hlst. simpl.
  destruct
    (apply_plan equivocators_no_equivocations_vlsm tra_final
      (map (update_euivocators_transition_item_descriptor full_replay_state) trb))
    as (trb_items, trb_final).
  reflexivity.
Qed.

Lemma apply_plan_full_replay_state_initial_state
  (full_replay_state : vstate equivocators_no_equivocations_vlsm)
  (is : vstate equivocators_no_equivocations_vlsm)
  (tr_full_replay_is :=
    apply_plan equivocators_no_equivocations_vlsm full_replay_state
      (spawn_initial_state is)
  )
  (eqv : equiv_index)
  : snd tr_full_replay_is (eqv)
  = equivocator_state_extend (IM (eqv))
    (full_replay_state (eqv))
    (projT2 (is (eqv)) (of_nat_lt (Hzero (IM (eqv)) (is (eqv))))).
Proof.
  unfold spawn_initial_state in tr_full_replay_is.
  assert
    (Heq_state_not_in :
      forall
        (l : list equiv_index)
        (Heqv : ~In eqv l)
        (s : vstate equivocators_no_equivocations_vlsm),
        snd
          (apply_plan equivocators_no_equivocations_vlsm s
            (map (initial_new_machine_transition_item is) l))
          (eqv)
        = s (eqv)
    ).
  { induction l; intros; [reflexivity|].
    spec IHl.
    { intro contra. elim Heqv. right. assumption. }
    change (a :: l) with ([a] ++ l).
    rewrite map_app. rewrite apply_plan_app.
    destruct
      (apply_plan equivocators_no_equivocations_vlsm s
        (map (initial_new_machine_transition_item is) [a]))
      as (aitems, afinal) eqn:Happlya.
    spec IHl afinal.
    destruct
      (apply_plan equivocators_no_equivocations_vlsm afinal
        (map (initial_new_machine_transition_item is) l))
      as (litems, lfinal)
      eqn:Happlyl.
    simpl in *. rewrite IHl.
    unfold apply_plan in Happlya. simpl in Happlya.
    inversion Happlya.
    rewrite state_update_neq; [reflexivity|].
    intro contra. elim Heqv. left. congruence.
  }
  assert
    (Heq_state_in :
      forall
        (l : list equiv_index)
        (Hnodup : NoDup l)
        (Heqv : In eqv l),
        snd
          (apply_plan equivocators_no_equivocations_vlsm full_replay_state
            (map (initial_new_machine_transition_item is) l))
          (eqv)
        = equivocator_state_extend (IM (eqv))
          (full_replay_state (eqv))
          (projT2 (is (eqv)) (of_nat_lt (Hzero (IM (eqv)) (is (eqv)))))
    ).
  { intros. apply in_split in Heqv as Heqv.
    destruct Heqv as [pref [suf Heqv]].
    subst. apply NoDup_remove in Hnodup.
    destruct Hnodup as [Hnodup Heqv].
    rewrite map_app. rewrite apply_plan_app.
    change (eqv :: suf) with ([eqv] ++ suf).
    rewrite map_app.
    specialize (Heq_state_not_in pref) as Hpref.
    spec Hpref.
    { intro contra. elim Heqv. apply in_app_iff. left. assumption. }
    spec Hpref full_replay_state.
    destruct
      (apply_plan equivocators_no_equivocations_vlsm full_replay_state
        (map (initial_new_machine_transition_item is) pref))
      as (pref_items, pref_final).
    simpl in Hpref.
    rewrite apply_plan_app.
    destruct
      (apply_plan equivocators_no_equivocations_vlsm pref_final
        (map (initial_new_machine_transition_item is) [eqv]))
      as (eqv_items, eqv_final) eqn:Happly_eqv.
    specialize (Heq_state_not_in suf) as Hsuf.
    spec Hsuf.
    { intro contra. elim Heqv. apply in_app_iff. right. assumption. }
    spec Hsuf eqv_final.
    destruct
      (apply_plan equivocators_no_equivocations_vlsm eqv_final
        (map (initial_new_machine_transition_item is) suf))
      as (suf_items, suf_final).
    simpl in Hsuf. simpl.
    rewrite Hsuf.
    unfold apply_plan in Happly_eqv.
    simpl in Happly_eqv. inversion Happly_eqv.
    rewrite state_update_eq. congruence.
  }
  apply Heq_state_in. apply (proj1 finite_index). apply (proj2 finite_index).
Qed.

Lemma replay_trace_from_state_correspondence'
  (full_replay_state : vstate equivocators_no_equivocations_vlsm)
  (is : vstate equivocators_no_equivocations_vlsm)
  (His : vinitial_state_prop equivocators_no_equivocations_vlsm is)
  (epref : list (vtransition_item equivocators_no_equivocations_vlsm))
  (tr_is_epref :=
    apply_plan equivocators_no_equivocations_vlsm is
      (trace_to_plan equivocators_no_equivocations_vlsm epref)
  )
  (tr_full_replay_is_epref :=
    apply_plan equivocators_no_equivocations_vlsm full_replay_state
      (spawn_initial_state is
      ++ map (update_euivocators_transition_item_descriptor full_replay_state) epref)
  )
  (eqv : equiv_index)
  : S (projT1 (snd tr_is_epref (eqv))) + S (projT1 (full_replay_state (eqv))) = S (projT1 (snd tr_full_replay_is_epref (eqv)))
  /\ (epref <> [] -> option_map output (last_error (fst tr_is_epref)) = option_map output (last_error (fst tr_full_replay_is_epref)))
  /\ (forall
    (id : nat)
    (Hid: id < S (projT1 (snd tr_is_epref (eqv)))),
    exists
    (Hi : id + S (projT1 (full_replay_state (eqv))) < S (projT1 (snd tr_full_replay_is_epref (eqv)))),
    projT2 (snd tr_is_epref (eqv)) (of_nat_lt Hid) =
    projT2 (snd tr_full_replay_is_epref (eqv)) (of_nat_lt Hi))
  /\ forall
    (id : nat)
    (Hid: id < S (projT1 (full_replay_state (eqv)))),
    exists
    (Hi : id < S (projT1 (snd tr_full_replay_is_epref (eqv)))),
    projT2 (snd tr_full_replay_is_epref (eqv)) (of_nat_lt Hi) =
    projT2 (full_replay_state (eqv)) (of_nat_lt Hid) .
Proof.
  generalize dependent eqv.
  induction epref using rev_ind; intros.
  - simpl in *. clear tr_is_epref. unfold tr_full_replay_is_epref. clear tr_full_replay_is_epref.
    rewrite app_nil_r.
    rewrite apply_plan_full_replay_state_initial_state.
    destruct (full_replay_state (eqv)) as (neqv, seqv).
    unfold equivocator_state_extend. simpl.
    specialize (equivocators_initial_state_size IM Hbs _ _ is His eqv) as His_size.
    split; [rewrite His_size; reflexivity|].
    split; [congruence|].
    split.
    + intros.
      assert (Hid_zero : id = 0) by lia.
      subst id. unfold plus.
      assert (Hi : S neqv < S (S neqv)) by lia.
      exists Hi. rewrite to_nat_of_nat.
      destruct (nat_eq_dec (S neqv) (S neqv)); [|congruence].
      reflexivity.
    + intros. assert (Hi : id < S (S neqv)) by lia.
      exists Hi. rewrite to_nat_of_nat.
      destruct (nat_eq_dec id (S neqv)); [lia|].
      f_equal. apply of_nat_ext.
  - remember
      (apply_plan equivocators_no_equivocations_vlsm is
      (trace_to_plan equivocators_no_equivocations_vlsm
         (epref ++ [x])))
      as tr_is_epref'.
    unfold tr_is_epref. clear tr_is_epref.
    unfold trace_to_plan in Heqtr_is_epref'.
    rewrite map_app in Heqtr_is_epref'.
    rewrite apply_plan_app in Heqtr_is_epref'.
    simpl in IHepref.
    unfold trace_to_plan in IHepref.
    remember
      (apply_plan equivocators_no_equivocations_vlsm is
      (map
         (transition_item_to_plan_item
            equivocators_no_equivocations_vlsm) epref))
      as tr_is_epref.
    destruct tr_is_epref as (epref_items, epref_final).
    simpl in IHepref.
    remember
      (apply_plan equivocators_no_equivocations_vlsm
      full_replay_state
      (spawn_initial_state is ++
       map
         (update_euivocators_transition_item_descriptor
            full_replay_state) (epref ++ [x])))
      as tr_full_replay_is_epref'.
    unfold tr_full_replay_is_epref in *. clear tr_full_replay_is_epref.
    rewrite map_app in Heqtr_full_replay_is_epref'.
    rewrite app_assoc in Heqtr_full_replay_is_epref'.
    rewrite apply_plan_app in Heqtr_full_replay_is_epref'.
    remember
      (apply_plan equivocators_no_equivocations_vlsm
      full_replay_state
      (spawn_initial_state is ++
       map
         (update_euivocators_transition_item_descriptor
            full_replay_state) epref))
      as tr_full_replay_is_epref.
    destruct tr_full_replay_is_epref as (full_replay_is_epref_items, full_replay_is_epref_final).
    unfold apply_plan in Heqtr_is_epref'. simpl in Heqtr_is_epref'.
    unfold apply_plan in Heqtr_full_replay_is_epref'. simpl in Heqtr_full_replay_is_epref'.
    destruct x. simpl in Heqtr_full_replay_is_epref'. simpl in Heqtr_is_epref'.
    destruct l as (eqv', l).
    destruct l as (l, d).
    destruct d as [sd | id' fd'].
    + simpl in Heqtr_full_replay_is_epref'. simpl in Heqtr_is_epref'.
      subst. simpl in *.
      destruct (decide (eqv = eqv')).
      * subst eqv'.
        spec IHepref eqv.
        remember (state_update (Common.equivocator_IM IM) epref_final
        (eqv)
        (equivocator_state_extend (IM (eqv))
           (epref_final (eqv)) sd) (eqv)) as stat.
        rewrite state_update_eq in Heqstat.
        rewrite state_update_eq.
        unfold equivocator_state_extend in Heqstat.
        destruct (epref_final (eqv)) as (nepref_eqv, sepref_eqv) eqn:Hepref_final_eqv.
        simpl in IHepref. subst stat. simpl.
        unfold equivocator_state_extend.
        destruct (full_replay_is_epref_final (eqv)) as (nfull_replay_is_epref_eqv, sfull_replay_is_epref_eqv).
        unfold projT1. unfold projT2.
        simpl in IHepref.
        destruct (full_replay_state (eqv)) as (nfull_replay_state_eqv, sfull_replay_state_eqv) eqn:Hfull_replay_state_eqv.
        simpl in IHepref.
        destruct IHepref as [Hsize Hstate].
        split; [congruence|].
        repeat split.
        -- intros. repeat rewrite last_error_is_last. reflexivity.
        -- intros.
          assert (Hi : id + S nfull_replay_state_eqv < S (S nfull_replay_is_epref_eqv)) by lia.
          exists Hi.
          repeat rewrite to_nat_of_nat.
          destruct (nat_eq_dec id (S nepref_eqv)).
          ++ subst id.
            destruct (nat_eq_dec (S nepref_eqv + S nfull_replay_state_eqv) (S nfull_replay_is_epref_eqv))
            ; [reflexivity|lia].
          ++ destruct (nat_eq_dec (id + S nfull_replay_state_eqv) (S nfull_replay_is_epref_eqv) ) ; [lia|].
            assert (Hid' : id < S nepref_eqv) by lia.
            destruct Hstate as [_ [Hstate _]].
            spec Hstate  id Hid'.
            replace
              (of_nat_lt (Common.equivocator_state_extend_obligation_1 nepref_eqv id Hid n))
              with (of_nat_lt Hid') in *
              by apply of_nat_ext.
            destruct Hstate as [Hi' Hstate].
            rewrite Hstate. f_equal. apply of_nat_ext.
        -- intros.
          assert (Hi : id < S (S nfull_replay_is_epref_eqv)) by lia.
          exists Hi. rewrite to_nat_of_nat.
          destruct (nat_eq_dec id (S nfull_replay_is_epref_eqv)); [lia|].
          destruct Hstate as [_ [_ Hstate]].
          spec Hstate id Hid.
          destruct Hstate as [Hi' Hstate].
          rewrite <- Hstate. f_equal. apply of_nat_ext.
      * remember
          (state_update (Common.equivocator_IM IM) full_replay_is_epref_final
          (eqv')
          (equivocator_state_extend (IM (eqv'))
             (full_replay_is_epref_final (eqv')) sd) (eqv))
          as stat.
        spec IHepref eqv.
        rewrite state_update_neq in Heqstat by assumption.
        rewrite state_update_neq by assumption.
        destruct (epref_final (eqv)) as (nepref_eqv, sepref_eqv) eqn:Hepref_final_eqv.
        simpl in IHepref. subst stat. simpl.
        destruct (full_replay_is_epref_final (eqv)) as (nfull_replay_is_epref_eqv, sfull_replay_is_epref_eqv).
        unfold projT1. unfold projT2.
        simpl in IHepref.
        destruct (full_replay_state (eqv)) as (nfull_replay_state_eqv, sfull_replay_state_eqv) eqn:Hfull_replay_state_eqv.
        simpl in IHepref.
        destruct IHepref as [Hsize [_ Hstate]].
        split; [congruence|].
        split; [|assumption].
        intros. repeat rewrite last_error_is_last. reflexivity.
    + unfold vtransition in Heqtr_full_replay_is_epref'. simpl in Heqtr_full_replay_is_epref'.
      unfold vtransition in Heqtr_full_replay_is_epref'.
      match type of Heqtr_full_replay_is_epref' with
      | _ = let (_, _) := let (_, _) := let (_, _) := let (_, _) := ?t
            in _ in _ in _ in _ => remember t as t_full_replay_is_epref'
      end.
      unfold_transition Heqt_full_replay_is_epref'.
      unfold snd in Heqt_full_replay_is_epref'.
      unfold vtransition in Heqtr_is_epref'.
      simpl in Heqtr_is_epref'.
      match type of Heqtr_is_epref' with
      | _ = let (_, _) := let (_, _) := let (_, _) := let (_, _) := ?t
            in _ in _ in _  in _ => remember t as t_is_epref'
      end.
      unfold vtransition in Heqt_is_epref'.
      unfold_transition Heqt_is_epref'.
      unfold snd in Heqt_is_epref'.
      simpl in IHepref.
      specialize (IHepref eqv') as IHepref'.
      specialize (IHepref eqv).
      destruct (epref_final (eqv')) as (nepref_eqv', sepref_eqv') eqn:Hepref_final_eqv'.
      destruct (full_replay_is_epref_final (eqv')) as (nfull_replay_is_epref_eqv', sfull_replay_is_epref_eqv') eqn:Hfull_replay_is_epref_eqv'.
      destruct (full_replay_state (eqv')) as (nfull_replay_state_eqv', sfull_replay_state_eqv') eqn:Hfull_replay_state_eqv'.
      unfold projT1 in Heqt_is_epref'. unfold projT2 in Heqt_is_epref'.
      unfold projT1 in Heqt_full_replay_is_epref'. unfold projT2 in Heqt_full_replay_is_epref'.
      unfold projT1 in Heqtr_full_replay_is_epref'.
      simpl in IHepref'.
      destruct IHepref' as [Hsize' Hstate'].
      destruct (le_lt_dec (S nepref_eqv') id').
      * destruct (le_lt_dec (S nfull_replay_is_epref_eqv') (id' + S nfull_replay_state_eqv'))
        ; [|lia].
        subst. simpl.
        destruct (decide (eqv = eqv')).
        -- subst eqv'.
          rewrite <- Hepref_final_eqv'.
          remember (state_update (Common.equivocator_IM IM) epref_final
          (eqv) (epref_final (eqv)) (eqv)) as stat.
          rewrite state_update_eq in Heqstat.
          rewrite state_update_eq.
          subst.
          rewrite Hfull_replay_is_epref_eqv' in *.
          rewrite Hepref_final_eqv' in *.
          rewrite Hfull_replay_state_eqv' in *.
          simpl in IHepref.
          unfold projT1. unfold projT2.
          destruct Hstate' as [_ Hstate'].
          split; [assumption|]. split; [|assumption].
          intros. repeat rewrite last_error_is_last. reflexivity.
        -- rewrite <- Hepref_final_eqv'.
          remember
            (state_update (Common.equivocator_IM IM) epref_final
            (eqv') (epref_final (eqv')) (eqv))
            as stat.
          rewrite state_update_neq in Heqstat by assumption.
          rewrite state_update_neq by assumption.
          destruct (epref_final (eqv)) as (nepref_eqv, sepref_eqv) eqn:Hepref_final_eqv.
          simpl in IHepref. subst stat. simpl.
          destruct (full_replay_is_epref_final (eqv)) as (nfull_replay_is_epref_eqv, sfull_replay_is_epref_eqv).
          destruct (full_replay_state (eqv)) as (nfull_replay_state_eqv, sfull_replay_state_eqv) eqn:Hfull_replay_state_eqv.
          unfold projT1. unfold projT2.
          simpl in IHepref. destruct IHepref as [Hsize [_ Heq]].
          split; [assumption|]. split; [|assumption].
          intros. repeat rewrite last_error_is_last. reflexivity.
      * destruct (le_lt_dec (S nfull_replay_is_epref_eqv') (id' + S nfull_replay_state_eqv')); [lia|].
        destruct
          (vtransition (IM (eqv'))
          (fst (l, Existing (IM (eqv')) id' fd'))
          (sepref_eqv' (Fin2Restrict.n2f l0), input))
          as (seqv', omeqv') eqn:Hteqv'.
        destruct
          (vtransition (IM (eqv'))
          (fst
             (l,
             Existing (IM (eqv'))
               (id' + S nfull_replay_state_eqv') fd'))
          (sfull_replay_is_epref_eqv'
             (Fin2Restrict.n2f l1), input))
          as (seqv'', omeqv'') eqn:Hteqv''.
        destruct fd' eqn:Hfd'.
        -- subst. simpl.
          destruct (decide (eqv = eqv')).
          ++ subst eqv'.
            remember
              (state_update (Common.equivocator_IM IM) epref_final
              (eqv)
              (existT (fun n : nat => t (S n) -> vstate (IM (eqv)))
                 (S nepref_eqv')
                 (fun j : t (S (S nepref_eqv')) =>
                  let (nj, Hnj) := to_nat j in
                  match nat_eq_dec nj (S nepref_eqv') with
                  | in_left => seqv'
                  | right H =>
                      sepref_eqv'
                        (Fin2Restrict.n2f
                           (Common.equivocator_state_extend_obligation_1
                              nepref_eqv' nj Hnj H))
                  end)) (eqv))
              as stat.
            rewrite state_update_eq in Heqstat.
            rewrite state_update_eq.
            subst.
            rewrite Hfull_replay_is_epref_eqv' in *.
            rewrite Hepref_final_eqv' in *.
            rewrite Hfull_replay_state_eqv' in *.
            simpl in IHepref.
            simpl.
            destruct IHepref as [Hsize Hstate].
            split; [congruence|].
            destruct Hstate' as [_ [Hstate' Hstate_pre]].
            unfold fst in Hteqv'. unfold fst in Hteqv''.
            specialize (Hstate' id' l0) as Hstate''.
            destruct Hstate'' as [Hi' Hstate''].
            replace (of_nat_lt l1) with (of_nat_lt Hi') in * by apply of_nat_ext.
            clear l1.
            rewrite Hstate'' in Hteqv'.
            rewrite Hteqv' in Hteqv''. inversion Hteqv''. subst seqv'' omeqv''.
            split ; [intros; repeat rewrite last_error_is_last; reflexivity|].
            split; intros.
            ** assert (Hi : id + S nfull_replay_state_eqv' < S (S nfull_replay_is_epref_eqv')) by lia.
              exists Hi.
              repeat rewrite to_nat_of_nat.
              destruct (nat_eq_dec id (S nepref_eqv')).
              --- subst.
                destruct (nat_eq_dec (S nepref_eqv' + S nfull_replay_state_eqv') (S nfull_replay_is_epref_eqv'))
                ; [reflexivity | elim n; assumption].
              --- destruct (nat_eq_dec (id + S nfull_replay_state_eqv') (S nfull_replay_is_epref_eqv'))
                ; [lia|].
                specialize (Hstate' _ (Common.equivocator_state_extend_obligation_1 nepref_eqv' id Hid n)).
                destruct Hstate' as [Hi'' Hstate'].
                rewrite Hstate'. f_equal. apply of_nat_ext.
            ** assert (Hi : id < S (S nfull_replay_is_epref_eqv')) by lia.
              exists Hi. rewrite to_nat_of_nat.
              destruct (nat_eq_dec id (S nfull_replay_is_epref_eqv')); [lia|].
              spec Hstate_pre id Hid.
              destruct Hstate_pre as [Hi'' Hstate_pre].
              rewrite <- Hstate_pre. f_equal. apply of_nat_ext.
          ++ remember
              (state_update (Common.equivocator_IM IM) epref_final (eqv')
              (existT (fun n0 : nat => t (S n0) -> vstate (IM (eqv'))) (S nepref_eqv')
                 (fun j : t (S (S nepref_eqv')) =>
                  let (nj, Hnj) := to_nat j in
                  match nat_eq_dec nj (S nepref_eqv') with
                  | in_left => seqv'
                  | right H =>
                      sepref_eqv'
                        (Fin2Restrict.n2f
                           (Common.equivocator_state_extend_obligation_1 nepref_eqv' nj Hnj H))
                  end)) (eqv))
              as stat.
            rewrite state_update_neq in Heqstat by assumption.
            rewrite state_update_neq by assumption.
            destruct (epref_final (eqv)) as (nepref_eqv, sepref_eqv) eqn:Hepref_final_eqv.
            simpl in IHepref. subst stat. simpl.
            destruct (full_replay_is_epref_final (eqv)) as (nfull_replay_is_epref_eqv, sfull_replay_is_epref_eqv).
            destruct (full_replay_state (eqv)) as (nfull_replay_state_eqv, sfull_replay_state_eqv) eqn:Hfull_replay_state_eqv.
            unfold projT1. unfold projT2.
            simpl in IHepref. destruct IHepref as [Hsize [_ Heq]].
            destruct Hstate' as [_ [Hstate' Hstate_pre]].
            unfold fst in Hteqv'. unfold fst in Hteqv''.
            specialize (Hstate' id' l0) as Hstate''.
            destruct Hstate'' as [Hi' Hstate''].
            replace (of_nat_lt l1) with (of_nat_lt Hi') in * by apply of_nat_ext.
            clear l1.
            rewrite Hstate'' in Hteqv'.
            rewrite Hteqv' in Hteqv''. inversion Hteqv''. subst seqv'' omeqv''.
            split; [assumption|].
            split; [|assumption].
            intros. repeat rewrite last_error_is_last. reflexivity.
        -- subst. simpl.
          destruct (decide (eqv = eqv')).
          ++ inversion e. subst eqv'.
            remember
              (state_update (Common.equivocator_IM IM) epref_final
              (eqv)
              (equivocator_state_update (IM (eqv))
                 (existT (fun n : nat => t (S n) -> vstate (IM (eqv)))
                    nepref_eqv' sepref_eqv') (Fin2Restrict.n2f l0) seqv')
              (eqv))
              as stat.
            rewrite state_update_eq in Heqstat.
            rewrite state_update_eq.
            subst.
            simpl.
            rewrite Hfull_replay_is_epref_eqv' in *.
            rewrite Hepref_final_eqv' in *.
            rewrite Hfull_replay_state_eqv' in *.
            simpl in IHepref.
            simpl.
            destruct IHepref as [Hsize Hstate].
            split; [congruence|].
            destruct Hstate' as [_ [Hstate' Hstate_pre]].
            unfold fst in Hteqv'. unfold fst in Hteqv''.
            specialize (Hstate' id' l0) as Hstate''.
            destruct Hstate'' as [Hi' Hstate''].
            replace (of_nat_lt l1) with (of_nat_lt Hi') in * by apply of_nat_ext.
            clear l1.
            rewrite Hstate'' in Hteqv'.
            rewrite Hteqv' in Hteqv''. inversion Hteqv''. subst seqv'' omeqv''.
            split; [intros; repeat rewrite last_error_is_last; reflexivity|].
            split; intros.
            ** assert (Hi : id + S nfull_replay_state_eqv' < S nfull_replay_is_epref_eqv') by lia.
              exists Hi.
              destruct (nat_eq_dec id id').
              --- subst id'.
                destruct (eq_dec (Fin2Restrict.n2f l0) (Fin2Restrict.n2f Hid))
                ; [|elim n; apply of_nat_ext].
                destruct (eq_dec (Fin2Restrict.n2f Hi') (Fin2Restrict.n2f Hi))
                ; [|elim n; apply of_nat_ext].
                replace (of_nat_lt l0) with (of_nat_lt Hid) in *.
                clear l0 e0.
                replace (of_nat_lt Hi') with (of_nat_lt Hi) in * by apply of_nat_ext.
                reflexivity.
              --- assert (Hneq : of_nat_lt l0 <> of_nat_lt Hid).
                { intro contra. elim n. apply (f_equal to_nat) in contra.
                  repeat rewrite to_nat_of_nat in contra.
                  inversion contra. reflexivity.
                }
                destruct (eq_dec (of_nat_lt l0) (of_nat_lt Hid))
                ; [congruence|].
                clear Hneq.
                assert (Hneq : of_nat_lt Hi' <> of_nat_lt Hi).
                { intro contra. elim n. apply (f_equal to_nat) in contra.
                  repeat rewrite to_nat_of_nat in contra.
                  inversion contra. lia.
                }
                destruct (eq_dec (of_nat_lt Hi') (of_nat_lt Hi))
                ; [congruence|].
                clear Hneq.
                clear Hi' Hteqv' Hstate'' n1.
                spec Hstate' id Hid.
                destruct Hstate' as [Hi' Hstate'].
                rewrite Hstate'. f_equal. apply of_nat_ext.
            ** assert (Hi : id < S nfull_replay_is_epref_eqv') by lia.
              exists Hi.
              specialize (Hstate_pre id Hid).
              destruct Hstate_pre as [Hi'' Hstate_pre].
              replace (of_nat_lt Hi'') with (of_nat_lt Hi) in Hstate_pre by apply of_nat_ext.
              destruct (eq_dec (Fin2Restrict.n2f Hi') (Fin2Restrict.n2f Hi)); [|assumption].
              apply (f_equal to_nat) in e.
              repeat rewrite to_nat_of_nat in e. inversion e. lia.
          ++ remember
              (state_update (Common.equivocator_IM IM) epref_final
              (eqv')
              (equivocator_state_update (IM (eqv'))
                 (existT (fun n0 : nat => t (S n0) -> vstate (IM (eqv')))
                    nepref_eqv' sepref_eqv') (Fin2Restrict.n2f l0) seqv')
              (eqv))
              as stat.
            rewrite state_update_neq in Heqstat by assumption.
            rewrite state_update_neq by assumption.
            destruct (epref_final (eqv)) as (nepref_eqv, sepref_eqv) eqn:Hepref_final_eqv.
            simpl in IHepref. subst stat. simpl.
            destruct (full_replay_is_epref_final (eqv)) as (nfull_replay_is_epref_eqv, sfull_replay_is_epref_eqv).
            destruct (full_replay_state (eqv)) as (nfull_replay_state_eqv, sfull_replay_state_eqv) eqn:Hfull_replay_state_eqv.
            unfold projT1. unfold projT2.
            unfold fst in Hteqv'. unfold fst in Hteqv''.
            destruct Hstate' as [_ [Hstate' Hstate_pre]].
            specialize (Hstate' id' l0) as Hstate''.
            destruct Hstate'' as [Hi' Hstate''].
            replace (of_nat_lt l1) with (of_nat_lt Hi') in * by apply of_nat_ext.
            clear l1.
            rewrite Hstate'' in Hteqv'.
            rewrite Hteqv' in Hteqv''. inversion Hteqv''. subst seqv'' omeqv''.
            simpl in IHepref. destruct IHepref as [Hsize [_ Heq]].
            split; [assumption|].
            split; [|assumption].
            intros. repeat rewrite last_error_is_last. reflexivity.
Qed.

Lemma replay_trace_from_state_correspondence
  (full_replay_state : vstate equivocators_no_equivocations_vlsm)
  (is : vstate equivocators_no_equivocations_vlsm)
  (His : vinitial_state_prop equivocators_no_equivocations_vlsm is)
  (tr : list (vtransition_item equivocators_no_equivocations_vlsm))
  (Htr : finite_protocol_trace_from equivocators_no_equivocations_vlsm is tr)
  (last_is_tr := last (map destination tr) is)
  (tr_full_replay_is_tr := replay_trace_from full_replay_state is tr)
  (last_full_replay_is_tr := last (map destination tr_full_replay_is_tr) full_replay_state)
  : (tr <> [] -> option_map output (last_error tr) = option_map output (last_error tr_full_replay_is_tr))
  /\ forall
    (eqv : equiv_index),
  S (projT1 (last_is_tr (eqv))) + S (projT1 (full_replay_state (eqv))) = S (projT1 (last_full_replay_is_tr (eqv)))
  /\ (forall
    (id : nat)
    (Hid: id < S (projT1 (last_is_tr (eqv)))),
    exists
    (Hi : id + S (projT1 (full_replay_state (eqv))) < S (projT1 (last_full_replay_is_tr (eqv)))),
    projT2 (last_is_tr (eqv)) (of_nat_lt Hid) =
    projT2 (last_full_replay_is_tr (eqv)) (of_nat_lt Hi))
  /\ forall
    (id : nat)
    (Hid: id < S (projT1 (full_replay_state (eqv)))),
    exists
    (Hi : id < S (projT1 (last_full_replay_is_tr (eqv)))),
    projT2 (last_full_replay_is_tr (eqv)) (of_nat_lt Hi) =
    projT2 (full_replay_state (eqv)) (of_nat_lt Hid) .
Proof.
  split.
  - set (eqv0 := @inhabitant index _).
    destruct
      (replay_trace_from_state_correspondence'
        full_replay_state _ His tr eqv0
      ) as [_ [Houtput _]].
    rewrite trace_to_plan_to_trace in Houtput; assumption.
  - intro eqv.
    specialize
      (replay_trace_from_state_correspondence'
        full_replay_state _ His tr eqv
      ) as Hcorrespondence.
    repeat rewrite <- apply_plan_last in Hcorrespondence.
    rewrite trace_to_plan_to_trace in Hcorrespondence by assumption.
    destruct Hcorrespondence as [Hsize [_ Hstate]].
    split; assumption.
Qed.

Lemma replay_trace_from_full_replay_state_project
  (full_replay_state : vstate equivocators_no_equivocations_vlsm)
  (is : vstate equivocators_no_equivocations_vlsm)
  (His : vinitial_state_prop equivocators_no_equivocations_vlsm is)
  (tr : list (vtransition_item equivocators_no_equivocations_vlsm))
  (Htr : finite_protocol_trace_from equivocators_no_equivocations_vlsm is tr)
  (tr_full_replay_is_tr := replay_trace_from full_replay_state is tr)
  (last_full_replay_is_tr := last (map destination tr_full_replay_is_tr) full_replay_state)
  (eqv_choice : equivocators_choice)
  (Heqv_choice : proper_equivocators_choice eqv_choice full_replay_state)
  : proper_equivocators_choice eqv_choice last_full_replay_is_tr /\
    equivocators_state_project eqv_choice last_full_replay_is_tr =
    equivocators_state_project eqv_choice  full_replay_state.
Proof.
  assert (Heqv_choice' : proper_equivocators_choice eqv_choice last_full_replay_is_tr); [|split;[assumption|]].
  - intro eqv. specialize (Heqv_choice eqv). unfold proper_descriptor in *.
    destruct (eqv_choice eqv); [assumption|].
    destruct (proj2 (replay_trace_from_state_correspondence full_replay_state _ His _ Htr) eqv)
      as [Hsize _]. unfold last_full_replay_is_tr. unfold tr_full_replay_is_tr.
    lia.
  - apply functional_extensionality_dep_good.
    intros eqv.
    unfold equivocators_state_project. unfold Common.equivocators_state_project.
    spec Heqv_choice eqv.
    spec Heqv_choice' eqv.
    unfold proper_descriptor in *.
    destruct (eqv_choice eqv); [reflexivity|].
    destruct (last_full_replay_is_tr (eqv)) as (last_full_replay_is_tr_size, last_full_replay_is_tr_s)
      eqn:Hlast_full_replay_is_tr_eqv.
    destruct (full_replay_state (eqv)) as (full_replay_state_size, full_replay_state_s)
      eqn:Hfull_replay_state_eqv.
    simpl in Heqv_choice, Heqv_choice'.
    destruct (le_lt_dec (S last_full_replay_is_tr_size) n); [lia|].
    destruct (le_lt_dec (S full_replay_state_size) n); [lia|].
    destruct (proj2 (replay_trace_from_state_correspondence full_replay_state _ His _ Htr) eqv)
      as [_ [_ Hstate_pre]].
    rewrite Hfull_replay_state_eqv in Hstate_pre.
    specialize (Hstate_pre n Heqv_choice).
    unfold last_full_replay_is_tr in *. unfold tr_full_replay_is_tr in *.
    rewrite Hlast_full_replay_is_tr_eqv in Hstate_pre.
    unfold projT1,projT2 in Hstate_pre.
    destruct Hstate_pre as [Hi Hstate_pre].
    replace (of_nat_lt Hi) with (of_nat_lt Heqv_choice') in * by apply of_nat_ext.
    replace (of_nat_lt l) with (of_nat_lt Heqv_choice') in * by apply of_nat_ext.
    replace (of_nat_lt l0) with (of_nat_lt Heqv_choice) in * by apply of_nat_ext.
    assumption.
Qed.

Lemma replay_trace_from_protocol
  (full_replay_state : vstate equivocators_no_equivocations_vlsm)
  (Hfull_replay_state : protocol_state_prop equivocators_no_equivocations_vlsm full_replay_state)
  (is : vstate equivocators_no_equivocations_vlsm)
  (tr : list (vtransition_item equivocators_no_equivocations_vlsm))
  (Htr : finite_protocol_trace equivocators_no_equivocations_vlsm is tr)
  (constraint :  composite_label equivocator_IM -> composite_state equivocator_IM * option message -> Prop)
  (Hconstraint_subsumption :
    constraint_subsumption equivocator_IM
      (equivocators_no_equivocations_constraint IM Hbs _ finite_index)
      constraint
  )
  (Hconstraint :
    forall
      (epref esuf : list (vtransition_item equivocators_no_equivocations_vlsm))
      (eitem : vtransition_item equivocators_no_equivocations_vlsm)
      (Htr_eq : tr = epref ++ [eitem] ++ esuf)
      (id : nat)
      (fd : bool)
      (eqv : equiv_index)
      (l0 : vlabel (IM (eqv)))
      (Hleitem : l eitem = existT
                       (fun n : index =>
                        vlabel (Common.equivocator_IM IM n))
                       (eqv) (l0, Existing (IM (eqv)) id fd)),
      constraint
        (existT (fun n : index => vlabel (equivocator_IM n))
           (eqv)
           (l0,
           Existing (IM (eqv)) (id + S (projT1 (full_replay_state (eqv)))) fd))
        (last
           (map Common.destination
              (fst
                 (apply_plan (equivocators_constrained_vlsm IM constraint)
                    full_replay_state
                    (spawn_initial_state is ++
                     map
                       (update_euivocators_transition_item_descriptor full_replay_state)
                       epref)))) full_replay_state, input eitem)
  )
  : finite_protocol_trace_from (equivocators_constrained_vlsm IM constraint)
      full_replay_state (replay_trace_from full_replay_state is tr).
Proof.
  assert (Hfull_replay_state' : protocol_state_prop (equivocators_constrained_vlsm IM constraint) full_replay_state).
  { destruct Hfull_replay_state as [om Hfull_replay_state]. exists om.
    apply (constraint_subsumption_protocol_prop equivocator_IM _ _ Hconstraint_subsumption).
    assumption.
  }
  apply (finite_protocol_plan_iff  (equivocators_constrained_vlsm IM constraint)).
  split; [assumption|].
  specialize
    (finite_protocol_trace_from_to_plan equivocators_no_equivocations_vlsm _ _ (proj1 Htr))
    as Htr'.
  apply finite_protocol_plan_iff in Htr'.
  split.
  - apply Forall_forall. intros a Ha.
    apply in_app_iff in Ha.
    destruct Ha as [Ha | Ha].
    + apply in_map_iff in Ha.
      destruct Ha as [eqv [Ha _]].
      subst. simpl. apply option_protocol_message_None.
    + apply in_map_iff in Ha.
      destruct Ha as [item [Ha Hitem]].
      destruct Htr' as [_ [Hinputs _]].
      rewrite Forall_forall in Hinputs.
      unfold update_euivocators_transition_item_descriptor in Ha.
      destruct item. destruct l eqn:Hl.
      specialize (Hinputs {| label_a := l; input_a := input|}).
      spec Hinputs.
      { apply in_map_iff. eexists _. split; [|apply Hitem].
        subst l. reflexivity.
      }
      simpl in Hinputs. subst a.
      assert (Hinputs' : option_protocol_message_prop (equivocators_constrained_vlsm IM constraint) input).
      { destruct Hinputs as [_s Hinputs]. exists _s.
        apply (constraint_subsumption_protocol_prop equivocator_IM _ _ Hconstraint_subsumption).
        assumption.
      }
      destruct v. destruct m; assumption.
  - intros.
    rewrite app_assoc in Heqa. apply order_decompositions in Heqa as Hprefa.
    rewrite <- or_assoc in Hprefa.
    destruct Hprefa as [Hprefa | [suf Hprefa]].
    + assert (Hai: In ai (spawn_initial_state is)).
      { destruct Hprefa as [Hprefa | Hprefa].
        - rewrite Hprefa; apply in_app_iff; right; left; reflexivity.
        - destruct Hprefa as [suf1 Hprefa].
          rewrite Hprefa.
          apply in_app_iff. left.
          apply in_app_iff. right.
          left. reflexivity.
      }
      apply in_map_iff in Hai. destruct Hai as [eqv [Hai _]].
      subst ai.
      apply equivocators_no_equivocations_vlsm_newmachine_always_valid; [|assumption].
      destruct Htr as [Htr His]. specialize (His (eqv)).
      destruct His as [Hzero His]. assumption.
    + rewrite Hprefa in Heqa.
      rewrite <- app_assoc in Heqa.
      apply app_inv_head in Heqa.
      assert (Hsuf: suf = [] \/ suf <> [])
        by (destruct suf; [left; congruence | right; congruence]).
      destruct Hsuf as [Hsuf|Hsuf].
      * subst.
        assert (Hai: In ai (spawn_initial_state is)).
        { rewrite app_nil_r in Hprefa. rewrite <- Hprefa; apply in_app_iff; right; left; reflexivity.
        }
        apply in_map_iff in Hai. destruct Hai as [eqv [Hai _]].
        subst ai.
        apply equivocators_no_equivocations_vlsm_newmachine_always_valid; [|assumption].
        destruct Htr as [Htr His]. specialize (His (eqv)).
        destruct His as [Hzero His]. assumption.
      * apply exists_last in Hsuf. destruct Hsuf as (pref, (ai', Hpref)).
        subst suf. rewrite app_assoc in Hprefa.
        apply app_inj_tail in Hprefa.
        destruct Hprefa. subst ai' prefa.
        apply  map_eq_app in Heqa.
        destruct Heqa as [eprefai [esuf [Heq_tr [Heprefai Hesuf]]]].
        apply map_eq_app in Heprefai.
        destruct Heprefai as [epref [eai [Heq_prefai [Hepref Heai]]]].
        apply map_eq_cons in Heai.
        destruct Heai as [ea [enil [Heq_eai [Heai Henil]]]].
        apply map_eq_nil in Henil. subst enil. subst eai. subst eprefai.
        rewrite <- app_assoc in Heq_tr.
        destruct Htr' as [His [Hinputs Hvalids]].
        specialize
          (Hvalids
            (trace_to_plan equivocators_no_equivocations_vlsm epref)
            (trace_to_plan equivocators_no_equivocations_vlsm esuf)
            (transition_item_to_plan_item equivocators_no_equivocations_vlsm ea)
          ).
        spec Hvalids.
        { subst tr. unfold trace_to_plan. repeat rewrite map_app. reflexivity. }
        destruct ea. simpl in *.
        destruct l as (eqv, l).
        destruct l as (l,d).
        destruct Hvalids as [Hvalids Hnoequiv].
        unfold vvalid in Hvalids. simpl in Hvalids.
        unfold vvalid in Hvalids. simpl in Hvalids.
        unfold equivocators_no_equivocations_constraint in Hnoequiv.
        simpl in Hnoequiv.
        destruct d as [sd | id fd].
        -- subst ai. simpl. destruct Hvalids as [Hsd Hinput]. subst input.
          repeat split; [assumption|].
          apply Hconstraint_subsumption.
          assumption.
        -- subst. simpl. destruct Hvalids as [Hid Hvalids].
          unfold lst. clear lst.
          split.
          ++ simpl. unfold vvalid. simpl.
            specialize
              (replay_trace_from_state_correspondence' full_replay_state _ (proj2 Htr)
              epref eqv
              )
              as Hstate.
            destruct Hstate as [Hsize [Houtput [Hstate Hstate_pre]]].
            spec Hstate id Hid.
            destruct Hstate as [Hi Hstate].
            exists Hi.
            match goal with
            |- vvalid _ _ (?s,_) =>
              replace s with
              (projT2
              (snd
                 (apply_plan equivocators_no_equivocations_vlsm full_replay_state
                    (spawn_initial_state is ++
                     map
                       (update_euivocators_transition_item_descriptor
                          full_replay_state) epref)) (eqv))
              (Fin2Restrict.n2f Hi))
            end
            ; [rewrite <- Hstate; assumption|].
            reflexivity.
          ++ simpl. rewrite <- apply_plan_last in *.
            specialize (Hconstraint _ _ _ eq_refl _ _ _ _ eq_refl).
            assumption.
Qed.

Lemma replay_trace_from_protocol_free
  (full_replay_state : vstate equivocators_no_equivocations_vlsm)
  (Hfull_replay_state : protocol_state_prop equivocators_no_equivocations_vlsm full_replay_state)
  (is : vstate equivocators_no_equivocations_vlsm)
  (tr : list (vtransition_item equivocators_no_equivocations_vlsm))
  (Htr : finite_protocol_trace equivocators_no_equivocations_vlsm is tr)
  : finite_protocol_trace_from (free_composite_vlsm equivocator_IM)
      full_replay_state (replay_trace_from full_replay_state is tr).
Proof.
  apply replay_trace_from_protocol.
  - assumption.
  - assumption.
  - intro; intros. exact I.
  - intros. exact I.
Qed.

Lemma replay_trace_from_protocol_equivocating
  (full_replay_state : vstate equivocators_no_equivocations_vlsm)
  (Hfull_replay_state : protocol_state_prop equivocators_no_equivocations_vlsm full_replay_state)
  (is : vstate equivocators_no_equivocations_vlsm)
  (tr : list (vtransition_item equivocators_no_equivocations_vlsm))
  (Htr : finite_protocol_trace equivocators_no_equivocations_vlsm is tr)
  : finite_protocol_trace_from equivocators_no_equivocations_vlsm
      full_replay_state (replay_trace_from full_replay_state is tr).
Proof.
  apply replay_trace_from_protocol
  ;[assumption|assumption|intro; intros; assumption|].
  intros.
  subst tr.
  destruct Htr as [Htr His].
  apply finite_protocol_trace_from_app_iff in Htr.
  destruct Htr as [Hepref Hesuf].
  specialize (replay_trace_from_protocol_free _ Hfull_replay_state _ _ (conj Hepref His))
    as Hepref_free.
  specialize (finite_ptrace_last_pstate _ _ _ Hepref_free) as Hlast_free.
  destruct (input eitem) as [m|] eqn:Hinput; [|exact I].
  apply finite_ptrace_first_valid_transition in Hesuf as Hitem.
  destruct Hitem as [[Hs [Hinp [_ Heqv] ]] _].
  rewrite Hleitem in Heqv. clear Hleitem.
  unfold equivocators_no_equivocations_constraint in Heqv.
  unfold equivocators_no_equivocations_constraint at 1.
  unfold no_equivocations in Heqv.
  rewrite Hinput in Heqv.
  destruct Heqv as [Heqv | Hinitial]; [| right; assumption].
  left. apply specialized_proper_sent; [assumption|].
  apply specialized_proper_sent_rev in Heqv
  ; [|
     destruct Hs as [_om Hs]; apply constraint_free_protocol_prop in Hs; exists _om; assumption
  ].
  spec Heqv is epref.
  spec Heqv.
  {
    split;[|assumption].
    apply (VLSM_incl_finite_trace); [|assumption].
    apply constraint_subsumption_incl.
    intro. intros. exact I.
  }
  specialize (Heqv eq_refl).
  apply
    (specialized_selected_message_exists_in_some_traces_from (free_composite_vlsm equivocator_IM)
      (field_selector output)
    ) with full_replay_state (replay_trace_from full_replay_state is epref)
  ; [assumption|reflexivity|].
  apply Exists_exists in Heqv.
  destruct Heqv as [mitem [Hmitem Houtput]].
  apply in_split in Hmitem.
  destruct Hmitem as [pref [suf Heqepref]].
  change (mitem :: suf) with ([mitem] ++ suf) in Heqepref.
  subst epref.
  rewrite app_assoc.
  rewrite replay_trace_from_app.
  apply Exists_app. left.
  destruct
    (replay_trace_from_state_correspondence' full_replay_state is His (pref ++ [mitem]) eqv)
    as [_ [Houtput' _]].
  spec Houtput'.
  { intro contra; destruct pref; discriminate contra. }
  rewrite app_assoc in Hepref.
  apply (finite_protocol_trace_from_app_iff equivocators_no_equivocations_vlsm) in Hepref.
  apply proj1 in Hepref.
  rewrite trace_to_plan_to_trace in Houtput'; [|assumption].
  change
    (fst (apply_plan equivocators_no_equivocations_vlsm
    full_replay_state
    (spawn_initial_state is ++
     map
       (update_euivocators_transition_item_descriptor
          full_replay_state) (pref ++ [mitem]))))
    with (replay_trace_from full_replay_state is (pref ++ [mitem]))
    in Houtput'.
  rewrite replay_trace_from_app.
  rewrite replay_trace_from_app in Houtput'.
  apply Exists_app. right. simpl.
  rewrite last_error_is_last in Houtput'.
  simpl in Houtput'.
  unfold apply_plan. unfold apply_plan in Houtput'. simpl in *.
  destruct (update_euivocators_transition_item_descriptor full_replay_state mitem) eqn:Hupdated_item.
  simpl in *.
  match goal with
  |- context [vtransition ?V ?l ?som] =>
    destruct (vtransition V l som) eqn:Ht
  end.
  simpl in *.
  rewrite last_error_is_last in Houtput'.
  simpl in Houtput'. inversion Houtput'.
  left. simpl. congruence.
Qed.

End all_equivocating.
