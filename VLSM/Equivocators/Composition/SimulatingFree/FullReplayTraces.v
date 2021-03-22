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
  (equivocator_descriptors := equivocator_descriptors IM)
  (index_listing : list index)
  (finite_index : Listing index_listing)
  (equivocators_no_equivocations_vlsm := equivocators_no_equivocations_vlsm IM Hbs finite_index)
  (equivocators_state_project := equivocators_state_project IM)
  (equivocator_IM := equivocator_IM IM)
  (equivocator_descriptors_update := equivocator_descriptors_update IM)
  (proper_equivocator_descriptors := proper_equivocator_descriptors IM)
  (equivocators_trace_project := equivocators_trace_project IM)
  (seed : message -> Prop)
  (SeededXE := seeded_equivocators_no_equivocation_vlsm IM Hbs finite_index seed)
  (SeededFree := pre_loaded_vlsm (free_composite_vlsm equivocator_IM) seed)
  (PreFree := pre_loaded_with_all_messages_vlsm (free_composite_vlsm equivocator_IM))
  .

Local Ltac unfold_transition Ht :=
  ( unfold transition, equivocator_IM, Common.equivocator_IM, equivocator_vlsm,
        mk_vlsm, machine, projT2, equivocator_vlsm_machine, equivocator_transition,
        snd in Ht
   ).

  (**
  Transforms a [composite_transition_item] of the [equivocator_IM] into
  a [plan_item] for the [equivocators_no_equivocations_vlsm] which is supposed
  to be executed as fully equivocating from the given state.
  *)

Definition update_equivocators_transition_item_descriptor
  (s : composite_state equivocator_IM)
  (item : composite_transition_item equivocator_IM)
  : composite_plan_item equivocator_IM
  :=
  match item with
  | {| l := l; input := input; destination := destination; output := output |} =>
    let (e, l) := l in
    let (l, d) := l in
    match d with
    | NewMachine _ sn =>
      @Build_plan_item message (composite_type equivocator_IM)
        (@existT index (fun n : index => vlabel (equivocator_IM n)) (e) (l, d)) input
    | Existing _ i fi =>
      @Build_plan_item message (composite_type equivocator_IM)
        (@existT index (fun n : index => vlabel (equivocator_IM n)) (e)
          (l, Existing _ (i + S (projT1 (s (e)))) fi)
        )
        input
    end
  end.

(** The plan item correspondint to an initial state equivocation *)
Definition initial_new_machine_transition_item
  (is : composite_state equivocator_IM)
  (eqv : equiv_index)
  : composite_plan_item equivocator_IM
  :=
  let seqv := is (eqv) in
  let new_l :=
    (@existT index (fun n : index => vlabel (equivocator_IM n)) (eqv)
      (vl0 (IM (eqv)), NewMachine _ (projT2 seqv (of_nat_lt (Hzero _ seqv))))
    )
    in
  @Build_plan_item message (composite_type equivocator_IM) new_l None.

(** The transition corresponding to the initial state equivocation above is valid. *)
Lemma equivocators_no_equivocations_vlsm_newmachine_always_valid
  (s : composite_state equivocator_IM)
  (a : composite_plan equivocator_IM)
  (eqv : equiv_index)
  (sn : vstate (IM (eqv)))
  (Hsn : vinitial_state_prop (IM (eqv)) sn)
  (constraint :  composite_label equivocator_IM -> composite_state equivocator_IM * option message -> Prop)
  (Hconstraint_subsumption :
    constraint_subsumption equivocator_IM
      (no_equivocations_additional_constraint_with_pre_loaded equivocator_IM
        (free_constraint equivocator_IM) (equivocator_Hbs IM Hbs) finite_index
        seed)
      constraint)
  : vvalid (pre_loaded_vlsm (composite_vlsm equivocator_IM constraint) seed)
      (@existT index (fun n : index => vlabel (equivocator_IM n)) (eqv)
        (vl0 (IM (eqv)), NewMachine _ sn))
      (snd (composite_apply_plan equivocator_IM s a), None).
Proof.
  split.
  - split; [assumption|reflexivity].
  - apply Hconstraint_subsumption.
    split; exact I.
Qed.

(** Command for equivocating all states of an initial composite state. *)
Definition spawn_initial_state
  (is : composite_state equivocator_IM)
  : composite_plan equivocator_IM
  := map (initial_new_machine_transition_item is) index_listing.

(** The replay plan of a trace on top of a given state, fully equivocating. *)
Definition replay_plan_from
  (full_replay_state : composite_state equivocator_IM)
  (is : composite_state equivocator_IM)
  (tr : list (composite_transition_item equivocator_IM))
  : composite_plan equivocator_IM
  :=
  spawn_initial_state is ++
  map (update_equivocators_transition_item_descriptor full_replay_state) tr.


(** The replaying of a trace on top of a given state, fully equivocating. *)
Definition applied_replay_plan_from
  (full_replay_state : composite_state equivocator_IM)
  (is : composite_state equivocator_IM)
  (tr : list (composite_transition_item equivocator_IM))
  : (list (composite_transition_item equivocator_IM) * composite_state equivocator_IM)
  :=
  composite_apply_plan equivocator_IM full_replay_state
      (replay_plan_from full_replay_state is tr).

(** The trace component of the above applied plan. *)
Definition replayed_trace_from
  (full_replay_state : composite_state equivocator_IM)
  (is : composite_state equivocator_IM)
  (tr : list (composite_transition_item equivocator_IM))
  : list (composite_transition_item equivocator_IM)
  :=
  fst (applied_replay_plan_from full_replay_state is tr).

(** Append property for replayed_trace_from. *)
Lemma replayed_trace_from_app
  (full_replay_state : composite_state equivocator_IM)
  (is : composite_state equivocator_IM)
  (tra trb : list (composite_transition_item equivocator_IM))
  (eqva := replayed_trace_from full_replay_state is tra)
  (lsta := last (map destination eqva) full_replay_state)
  : replayed_trace_from full_replay_state is (tra ++ trb) =
    eqva ++
    fst
      (composite_apply_plan equivocator_IM lsta
        (map (update_equivocators_transition_item_descriptor full_replay_state) trb)
      ).
Proof.
  unfold lsta, eqva. clear lsta eqva.
  unfold replayed_trace_from, applied_replay_plan_from, replay_plan_from in *.
  rewrite !map_app.
  rewrite app_assoc.
  rewrite (composite_apply_plan_app _) at 1.
  destruct
    (composite_apply_plan equivocator_IM full_replay_state
      (spawn_initial_state is ++ map (update_equivocators_transition_item_descriptor full_replay_state) tra)
    ) as (tra_items, tra_final) eqn:Htra.
  unfold fst at 2. unfold fst at 3.
  specialize
    (composite_apply_plan_last _ full_replay_state
      (spawn_initial_state is ++
        map (update_equivocators_transition_item_descriptor full_replay_state) tra)
    ) as Hlst.
  rewrite Htra in Hlst. simpl in Hlst.
  simpl.
  match goal with
  |- context [fst (composite_apply_plan _ ?l _)] => replace l with tra_final
  end.
  destruct
    (composite_apply_plan equivocator_IM tra_final
      (map (update_equivocators_transition_item_descriptor full_replay_state) trb))
    as (trb_items, trb_final).
  reflexivity.
Qed.

Lemma apply_plan_full_replay_state_initial_state
  (full_replay_state : composite_state equivocator_IM)
  (is : composite_state equivocator_IM)
  (tr_full_replay_is :=
    composite_apply_plan equivocator_IM full_replay_state
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
        (s : composite_state equivocator_IM),
        snd
          (composite_apply_plan equivocator_IM s
            (map (initial_new_machine_transition_item is) l))
          (eqv)
        = s (eqv)
    ).
  { induction l; intros; [reflexivity|].
    spec IHl.
    { intro contra. elim Heqv. right. assumption. }
    change (a :: l) with ([a] ++ l).
    rewrite map_app. rewrite (composite_apply_plan_app equivocator_IM).
    destruct
      (composite_apply_plan equivocator_IM s
        (map (initial_new_machine_transition_item is) [a]))
      as (aitems, afinal) eqn:Happlya.
    spec IHl afinal.
    destruct
      (composite_apply_plan equivocator_IM afinal
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
          (composite_apply_plan equivocator_IM full_replay_state
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
    rewrite map_app. rewrite (composite_apply_plan_app equivocator_IM).
    change (eqv :: suf) with ([eqv] ++ suf).
    rewrite map_app.
    specialize (Heq_state_not_in pref) as Hpref.
    spec Hpref.
    { intro contra. elim Heqv. apply in_app_iff. left. assumption. }
    spec Hpref full_replay_state.
    destruct
      (composite_apply_plan equivocator_IM full_replay_state
        (map (initial_new_machine_transition_item is) pref))
      as (pref_items, pref_final).
    simpl in Hpref.
    rewrite (composite_apply_plan_app equivocator_IM).
    destruct
      (composite_apply_plan equivocator_IM pref_final
        (map (initial_new_machine_transition_item is) [eqv]))
      as (eqv_items, eqv_final) eqn:Happly_eqv.
    specialize (Heq_state_not_in suf) as Hsuf.
    spec Hsuf.
    { intro contra. elim Heqv. apply in_app_iff. right. assumption. }
    spec Hsuf eqv_final.
    destruct
      (composite_apply_plan equivocator_IM eqv_final
        (map (initial_new_machine_transition_item is) suf))
      as (suf_items, suf_final).
    simpl in Hsuf. simpl.
    rewrite Hsuf. inversion Happly_eqv.
    rewrite state_update_eq. congruence.
  }
  apply Heq_state_in. apply (proj1 finite_index). apply (proj2 finite_index).
Qed.

(**
This lemma matches states in the replay with the state in the original trace.
This lengthy proof covers all cases, and might be good to split up in the future.
*)

Lemma replayed_trace_from_state_correspondence'
  (full_replay_state : composite_state equivocator_IM)
  (is : composite_state equivocator_IM)
  (His : composite_initial_state_prop equivocator_IM is)
  (epref : list (composite_transition_item equivocator_IM))
  (tr_is_epref :=
    composite_apply_plan equivocator_IM is
      (composite_trace_to_plan equivocator_IM epref)
  )
  (tr_full_replay_is_epref := applied_replay_plan_from full_replay_state is epref)
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
  unfold applied_replay_plan_from, replay_plan_from in tr_full_replay_is_epref.
  generalize dependent eqv.
  induction epref using rev_ind; intros.
  - simpl in *. clear tr_is_epref. unfold tr_full_replay_is_epref. clear tr_full_replay_is_epref.
    rewrite app_nil_r.
    rewrite apply_plan_full_replay_state_initial_state.
    destruct (full_replay_state (eqv)) as (neqv, seqv).
    unfold equivocator_state_extend. simpl.
    specialize (equivocators_initial_state_size IM Hbs finite_index is His eqv) as His_size.
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
  - destruct
      (composite_apply_plan equivocator_IM is (composite_trace_to_plan equivocator_IM (epref ++ [x])))
      as (tr_eprefx, s_eprefx) eqn:Hplan_eprefx.
    subst tr_is_epref.
    setoid_rewrite map_app in Hplan_eprefx.
    rewrite composite_apply_plan_app in Hplan_eprefx.
    simpl in *.
    unfold composite_trace_to_plan,_trace_to_plan in IHepref.
    destruct
      (composite_apply_plan equivocator_IM is  (map _transition_item_to_plan_item epref))
      as (tr_epref, s_epref) eqn:Hplan_epref.
    simpl in *.
    destruct
      (composite_apply_plan equivocator_IM s_epref [_transition_item_to_plan_item x] )
      as (tr_x, s_x) eqn:Hplan_x.
    inversion Hplan_eprefx. subst tr_eprefx s_eprefx. clear Hplan_eprefx.
    destruct
      (composite_apply_plan equivocator_IM
        full_replay_state
        (spawn_initial_state is ++
         map
           (update_equivocators_transition_item_descriptor
              full_replay_state) (epref ++ [x])))
      as (tr_replay_eprefx, s_replay_eprefx) eqn:Hplan_replay_eprefx.
    subst tr_full_replay_is_epref.
    simpl in *.
    rewrite map_app,app_assoc,(composite_apply_plan_app equivocator_IM)  in Hplan_replay_eprefx.
    destruct
      (composite_apply_plan equivocator_IM
        full_replay_state
        (spawn_initial_state is ++
         map
           (update_equivocators_transition_item_descriptor
              full_replay_state) epref))
      as (tr_replay_epref, s_replay_epref) eqn:Hplan_replay_epref.
    simpl in *.
    destruct
      (composite_apply_plan equivocator_IM
        s_replay_epref [update_equivocators_transition_item_descriptor full_replay_state x]
      ) as (tr_replay_x, s_replay_x) eqn:Hplan_replay_x.
    inversion Hplan_replay_eprefx.
    subst tr_replay_eprefx s_replay_eprefx. clear Hplan_replay_eprefx.

    destruct x. simpl in *.
    unfold _transition_item_to_plan_item, composite_apply_plan, _apply_plan in Hplan_x. simpl in Hplan_x.
    destruct l as (i, li).
    destruct (vtransition (equivocator_IM i) li (s_epref i, input))
      as (s_epref_i', om_epref_i') eqn:Ht_s_epref_i.
    simpl in Hplan_x. inversion Hplan_x. subst tr_x s_x. clear Hplan_x.
    rewrite last_error_is_last. simpl.
    destruct li as (li, [sd | id' fd']); [destruct (decide (eqv = i))|].
    + subst i.
      inversion Hplan_replay_x. subst tr_replay_x s_replay_x. clear Hplan_replay_x.
      rewrite last_error_is_last.
      inversion Ht_s_epref_i.  subst. clear Ht_s_epref_i.
      rewrite! state_update_eq. simpl.
      spec IHepref eqv.
      destruct IHepref as [Hsize Hstate].
      destruct (s_replay_epref eqv) as (ns_replay_epref_eqv, bs_replay_epref_eqv).
      destruct (s_epref eqv) as (ns_epref_eqv, bs_epref_eqv).
      unfold equivocator_state_extend. simpl in *.
      subst.
      split; [lia|].
      split; [intro; reflexivity|].
      destruct (full_replay_state eqv) as (nfull_replay_state_eqv, bfull_replay_state_eqv).
      simpl in *.
      split; intros.
      * assert (Hi : id + S nfull_replay_state_eqv < S (S ns_replay_epref_eqv)) by lia.
        exists Hi.
        rewrite! to_nat_of_nat.
        destruct (nat_eq_dec id (S ns_epref_eqv)).
        -- subst id.
          destruct (nat_eq_dec (S ns_epref_eqv + S nfull_replay_state_eqv) (S ns_replay_epref_eqv))
          ; [reflexivity|lia].
        -- destruct (nat_eq_dec (id + S nfull_replay_state_eqv) (S ns_replay_epref_eqv) ) ; [lia|].
          assert (Hid' : id < S ns_epref_eqv) by lia.
          destruct Hstate as [_ [Hstate _]].
          spec Hstate  id Hid'.
          replace
            (of_nat_lt (Common.equivocator_state_extend_obligation_1 ns_epref_eqv id Hid n))
            with (of_nat_lt Hid') in *
            by apply of_nat_ext.
          destruct Hstate as [Hi' Hstate].
          rewrite Hstate. f_equal. apply of_nat_ext.
      * assert (Hi : id < S (S ns_replay_epref_eqv)) by lia.
        exists Hi. rewrite to_nat_of_nat.
        destruct (nat_eq_dec id (S ns_replay_epref_eqv)); [lia|].
        destruct Hstate as [_ [_ Hstate]].
        spec Hstate id Hid.
        destruct Hstate as [Hi' Hstate].
        rewrite <- Hstate. f_equal. apply of_nat_ext.
    + inversion Hplan_replay_x. subst tr_replay_x s_replay_x. clear Hplan_replay_x.
      rewrite last_error_is_last.
      inversion Ht_s_epref_i.  subst. clear Ht_s_epref_i.
      rewrite! state_update_neq by assumption.
      spec IHepref eqv.
      destruct IHepref as [Hsize [_ Hstate]].
      split; [assumption|].
      split; [intros; reflexivity|].
      assumption.
    + unfold composite_apply_plan, _apply_plan in Hplan_replay_x. simpl in Hplan_replay_x.
      destruct
        (vtransition (equivocator_IM i)
          (li, Existing (IM i) (id' + S (projT1 (full_replay_state i))) fd')
          (s_replay_epref i, input)
        ) as (s_replay_epref_i', om_replay_epref_i')
        eqn:Ht_s_replay_epref_i.
      simpl in Hplan_replay_x.
      inversion Hplan_replay_x. subst. clear Hplan_replay_x. simpl in *.
      rewrite last_error_is_last. simpl.
      unfold vtransition in Ht_s_epref_i, Ht_s_replay_epref_i.
      unfold_transition Ht_s_epref_i.
      unfold_transition Ht_s_replay_epref_i.
      destruct (IHepref i) as [Hsizei [_ Hstatei]].
      specialize (IHepref eqv). destruct IHepref as [Hsize [_ Hstate]].
      destruct (s_replay_epref i) as (ns_replay_epref_i, bs_replay_epref_i)
        eqn:Heqs_replay_epref_i.
      destruct (full_replay_state i) as (nfull_replay_state_i, bfull_replay_state_i)
        eqn:Heqfull_replay_state_i.
      destruct (s_epref i) as (ns_epref_i, bs_epref_i)
        eqn:Heqs_epref_i.
      simpl in Hsizei, Hstatei.
      unfold projT1 in Ht_s_replay_epref_i, Ht_s_epref_i.
      destruct (le_lt_dec (S ns_epref_i) id').
      * destruct (le_lt_dec (S ns_replay_epref_i) (id' + S nfull_replay_state_i)); [|lia].
        inversion Ht_s_epref_i. subst om_epref_i' s_epref_i'. clear Ht_s_epref_i.
        inversion Ht_s_replay_epref_i. subst om_replay_epref_i' s_replay_epref_i'. clear Ht_s_replay_epref_i.
        destruct (decide (eqv = i)).
        -- subst i. rewrite! state_update_eq. simpl.
          rewrite Heqfull_replay_state_i. simpl.
          split; [assumption|]. split; [reflexivity|].
          assumption.
        -- rewrite! state_update_neq by assumption. simpl.
          split; [assumption|]. split; [reflexivity|]. assumption.
      * destruct (le_lt_dec (S ns_replay_epref_i) (id' + S nfull_replay_state_i)); [lia|].
        simpl in Ht_s_replay_epref_i, Ht_s_epref_i.
        destruct Hstatei as [Hstatei_1 Hstatei_2].
        destruct (Hstatei_1 id' l) as [_l0 Hstateil].
        replace (of_nat_lt _l0) with (of_nat_lt l0) in Hstateil by apply of_nat_ext.
        clear _l0.
        rewrite <- Hstateil in Ht_s_replay_epref_i. clear Hstateil.
        destruct
          (vtransition (IM i) li (bs_epref_i (Fin2Restrict.n2f l), input))
          as (bs_epref_i', om_bs_epref_i') eqn:Ht_bs_eprefi.
        destruct fd' eqn:Hfd'
        ; inversion Ht_s_epref_i; subst s_epref_i' om_epref_i'; clear Ht_s_epref_i
        ; inversion Ht_s_replay_epref_i; subst s_replay_epref_i' om_replay_epref_i'; clear Ht_s_replay_epref_i
        ; destruct (decide (eqv = i)).
        -- subst i. rewrite! state_update_eq. simpl.
          rewrite! Heqfull_replay_state_i in *. simpl in *.
          split; [lia|]. split; [reflexivity|].
          split; intros.
          ++ assert (Hi : id + S nfull_replay_state_i < S (S ns_replay_epref_i)) by lia.
            exists Hi.
            rewrite! to_nat_of_nat.
            destruct (nat_eq_dec id (S ns_epref_i)).
            ** subst.
              destruct (nat_eq_dec (S ns_epref_i + S nfull_replay_state_i) (S ns_replay_epref_i))
              ; [reflexivity | elim n; assumption].
            ** destruct (nat_eq_dec (id + S nfull_replay_state_i) (S ns_replay_epref_i))
              ; [lia|].
              specialize (Hstatei_1 _ (Common.equivocator_state_extend_obligation_1 ns_epref_i id Hid n)).
              destruct Hstatei_1 as [Hi'' Hstate'].
              rewrite Hstate'. f_equal. apply of_nat_ext.
          ++ assert (Hi : id < S (S ns_replay_epref_i)) by lia.
            exists Hi. rewrite to_nat_of_nat.
            destruct (nat_eq_dec id (S ns_replay_epref_i)); [lia|].
            spec Hstatei_2 id Hid.
            destruct Hstatei_2 as [Hi'' Hstate_pre].
            rewrite <- Hstate_pre. f_equal. apply of_nat_ext.
        -- rewrite! state_update_neq by assumption.
          split; [assumption|]. split; [reflexivity|].
          assumption.
        -- subst i.
          rewrite! state_update_eq.
          simpl.
          rewrite! Heqfull_replay_state_i in *.
          split; [assumption|]. split; [reflexivity|].
          simpl in *.
          split; intros.
          ++ assert (Hi : id + S nfull_replay_state_i < S ns_replay_epref_i) by lia.
            exists Hi.
            destruct (nat_eq_dec id id').
            ** subst id'.
              destruct (eq_dec (of_nat_lt l) (of_nat_lt Hid))
              ; [|elim n; apply of_nat_ext].
              destruct (eq_dec (of_nat_lt l0) (of_nat_lt Hi))
              ; [|elim n; apply of_nat_ext].
              reflexivity.
            ** rewrite! eq_dec_if_false.
              {
                spec Hstatei_1 id Hid.
                destruct Hstatei_1 as [Hi' Hstate'].
                rewrite Hstate'. f_equal. apply of_nat_ext.
              }
              { intro contra. elim n. apply (f_equal to_nat) in contra.
                repeat rewrite to_nat_of_nat in contra.
                inversion contra. lia.
              }
              { intro contra. elim n. apply (f_equal to_nat) in contra.
                repeat rewrite to_nat_of_nat in contra.
                inversion contra. lia.
              }
          ++ assert (Hi : id < S ns_replay_epref_i) by lia.
            exists Hi.
            specialize (Hstatei_2 id Hid).
            destruct Hstatei_2 as [Hi'' Hstate_pre].
            replace (of_nat_lt Hi'') with (of_nat_lt Hi) in Hstate_pre by apply of_nat_ext.
            rewrite eq_dec_if_false; [assumption|].
            intro e.
            apply (f_equal to_nat) in e.
            repeat rewrite to_nat_of_nat in e. inversion e. lia.
        -- rewrite! state_update_neq by assumption.
          split; [assumption|].
          split; [reflexivity|].
          assumption.
Qed.

(** A specialization of the above lemma for the case when the trace is protocol. *)
Lemma replayed_trace_from_state_correspondence
  (full_replay_state : composite_state equivocator_IM)
  (is : composite_state equivocator_IM)
  (tr : list (composite_transition_item equivocator_IM))
  (Htr : finite_protocol_trace SeededXE is tr)
  (last_is_tr := last (map destination tr) is)
  (tr_full_replay_is_tr := replayed_trace_from full_replay_state is tr)
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
  unfold replayed_trace_from, applied_replay_plan_from, replay_plan_from in tr_full_replay_is_tr.
  destruct Htr as [Htr His]. split.
  - set (eqv0 := @inhabitant index _).
    destruct
      (replayed_trace_from_state_correspondence'
        full_replay_state _ His tr eqv0
      ) as [_ [Houtput _]].
    specialize (trace_to_plan_to_trace SeededXE _ _ Htr) as Heq.
    intro Htrne. specialize (Houtput Htrne).
    subst last_is_tr tr_full_replay_is_tr last_full_replay_is_tr.
    replace
      (fst
        (composite_apply_plan equivocator_IM is
           (composite_trace_to_plan equivocator_IM tr)))
      with tr in Houtput. assumption.
  - intro eqv.
    specialize
      (replayed_trace_from_state_correspondence'
        full_replay_state _ His tr eqv
      ) as Hcorrespondence.
    unfold applied_replay_plan_from, replay_plan_from in Hcorrespondence.
    repeat rewrite <- (composite_apply_plan_last equivocator_IM) in Hcorrespondence.
    specialize (trace_to_plan_to_trace SeededXE _ _ Htr) as Heq.
    replace
      (fst
        (composite_apply_plan equivocator_IM is
           (composite_trace_to_plan equivocator_IM tr)))
      with tr in Hcorrespondence.
    destruct Hcorrespondence as [Hsize [_ Hstate]].
    split; assumption.
Qed.

(**
All the states from the original state on top of which we replay are kept
unchanged in the final state after the replay.
*)
Lemma replayed_trace_from_full_replay_state_project
  (full_replay_state : vstate equivocators_no_equivocations_vlsm)
  (is : vstate equivocators_no_equivocations_vlsm)
  (tr : list (composite_transition_item equivocator_IM))
  (Htr : finite_protocol_trace SeededXE is tr)
  (tr_full_replay_is_tr := replayed_trace_from full_replay_state is tr)
  (last_full_replay_is_tr := last (map destination tr_full_replay_is_tr) full_replay_state)
  (eqv_descriptors : equivocator_descriptors)
  (Heqv_descriptors : proper_equivocator_descriptors eqv_descriptors full_replay_state)
  : proper_equivocator_descriptors eqv_descriptors last_full_replay_is_tr /\
    equivocators_state_project eqv_descriptors last_full_replay_is_tr =
    equivocators_state_project eqv_descriptors  full_replay_state.
Proof.
  assert (Heqv_descriptors' : proper_equivocator_descriptors eqv_descriptors last_full_replay_is_tr); [|split;[assumption|]].
  - intro eqv. specialize (Heqv_descriptors eqv). unfold proper_descriptor in *.
    destruct (eqv_descriptors eqv); [assumption|].
    destruct (proj2 (replayed_trace_from_state_correspondence full_replay_state _ _ Htr) eqv)
      as [Hsize _]. unfold last_full_replay_is_tr. unfold tr_full_replay_is_tr.
    lia.
  - apply functional_extensionality_dep_good.
    intros eqv.
    unfold equivocators_state_project. unfold Common.equivocators_state_project.
    unfold equivocator_state_descriptor_project.
    unfold equivocator_state_project.
    spec Heqv_descriptors eqv.
    spec Heqv_descriptors' eqv.
    unfold proper_descriptor in *.
    destruct (eqv_descriptors eqv); [reflexivity|].
    destruct (last_full_replay_is_tr (eqv)) as (last_full_replay_is_tr_size, last_full_replay_is_tr_s)
      eqn:Hlast_full_replay_is_tr_eqv.
    destruct (full_replay_state (eqv)) as (full_replay_state_size, full_replay_state_s)
      eqn:Hfull_replay_state_eqv.
    simpl in Heqv_descriptors, Heqv_descriptors'.
    destruct (le_lt_dec (S last_full_replay_is_tr_size) n); [lia|].
    destruct (le_lt_dec (S full_replay_state_size) n); [lia|].
    destruct (proj2 (replayed_trace_from_state_correspondence full_replay_state _  _ Htr) eqv)
      as [_ [_ Hstate_pre]].
    rewrite Hfull_replay_state_eqv in Hstate_pre.
    specialize (Hstate_pre n Heqv_descriptors).
    unfold last_full_replay_is_tr in *. unfold tr_full_replay_is_tr in *.
    rewrite Hlast_full_replay_is_tr_eqv in Hstate_pre.
    unfold projT1,projT2 in Hstate_pre.
    destruct Hstate_pre as [Hi Hstate_pre].
    replace (of_nat_lt Hi) with (of_nat_lt Heqv_descriptors') in * by apply of_nat_ext.
    replace (of_nat_lt l) with (of_nat_lt Heqv_descriptors') in * by apply of_nat_ext.
    replace (of_nat_lt l0) with (of_nat_lt Heqv_descriptors) in * by apply of_nat_ext.
    assumption.
Qed.

Lemma parametric_constrained_incl
  (constraint: composite_label equivocator_IM ->
               composite_state equivocator_IM * option message -> Prop)
  (Hconstraint_subsumption: constraint_subsumption equivocator_IM
                              (no_equivocations_additional_constraint_with_pre_loaded
                                 equivocator_IM
                                 (free_constraint equivocator_IM)
                                 (equivocator_Hbs IM Hbs) finite_index seed)
                              constraint)
  : VLSM_incl SeededXE (pre_loaded_vlsm (composite_vlsm equivocator_IM constraint) seed).
Proof.
  apply basic_VLSM_incl.
  - intros. assumption.
  - intros.
    apply initial_message_is_protocol.
    assumption.
  - intros l s om [Hs [Hom Hv]]. simpl in Hv. unfold vvalid. simpl.
    unfold constrained_composite_valid in *.
    destruct Hv as [Hv Hc].
    split; [assumption|].
    apply Hconstraint_subsumption. assumption.
  - intros. reflexivity.
Qed.

(**
By replaying a [protocol_trace] on top of a [protocol_state] we obtain
a [protocol_trace]. The proof is parameterized in a constraint having "good"
properties, to allow deriving the [protocol_trace] property both for
the free composition of equivocators and for the no message equivocation
composition of equivocators (the latter proof uses the first result,
and both use the one below)
*)
Lemma replayed_trace_from_protocol
  (full_replay_state : composite_state equivocator_IM)
  (Hfull_replay_state : protocol_state_prop SeededXE full_replay_state)
  (is : composite_state equivocator_IM)
  (tr : list (composite_transition_item equivocator_IM))
  (Htr : finite_protocol_trace SeededXE is tr)
  (constraint :  composite_label equivocator_IM -> composite_state equivocator_IM * option message -> Prop)
  (Hconstraint_subsumption :
    constraint_subsumption equivocator_IM
      (no_equivocations_additional_constraint_with_pre_loaded equivocator_IM
        (free_constraint equivocator_IM) (equivocator_Hbs IM Hbs) finite_index
        seed)
      constraint)
  (Hconstraint :
    forall
      [epref esuf
      eitem
      id fd eqv l0]
      (Htr_eq : tr = epref ++ [eitem] ++ esuf)
      (Hleitem : l eitem = existT _ eqv (l0, Existing (IM (eqv)) id fd)),
      constraint
        (existT _ eqv (l0, Existing (IM eqv) (id + S (projT1 (full_replay_state eqv))) fd))
        (last (map destination (replayed_trace_from full_replay_state is epref)) full_replay_state
        , input eitem)
  )
  : finite_protocol_trace_from (pre_loaded_vlsm (composite_vlsm equivocator_IM constraint) seed)
      full_replay_state (replayed_trace_from full_replay_state is tr).
Proof.
  assert (Hfull_replay_state' : protocol_state_prop (pre_loaded_vlsm (composite_vlsm equivocator_IM constraint) seed) full_replay_state).
  { revert Hfull_replay_state.
    apply VLSM_incl_protocol_state.
    apply parametric_constrained_incl.
    assumption.
  }
  apply (finite_protocol_plan_iff  (pre_loaded_vlsm  (composite_vlsm equivocator_IM constraint) seed)).
  split; [assumption|].
  specialize
    (finite_protocol_trace_from_to_plan SeededXE _ _ (proj1 Htr))
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
      unfold update_equivocators_transition_item_descriptor in Ha.
      destruct item. destruct l eqn:Hl.
      specialize (Hinputs {| label_a := l; input_a := input|}).
      spec Hinputs.
      { apply in_map_iff. eexists _. split; [|apply Hitem].
        subst l. reflexivity.
      }
      simpl in Hinputs. subst a.
      assert (Hinputs' : option_protocol_message_prop (pre_loaded_vlsm (composite_vlsm equivocator_IM constraint) seed) input).
      { destruct input; [|apply option_protocol_message_None].
        apply can_emit_protocol_iff. apply can_emit_protocol_iff in Hinputs.
        destruct Hinputs as [Hinit | Hemit]; [left; assumption|].
        right. revert Hemit. apply VLSM_incl_can_emit.
        apply (parametric_constrained_incl constraint). assumption.
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
            (trace_to_plan SeededXE epref)
            (trace_to_plan SeededXE esuf)
            (_transition_item_to_plan_item ea)
          ).
        spec Hvalids.
        { subst tr. unfold trace_to_plan, _trace_to_plan. repeat rewrite map_app. reflexivity. }
        destruct ea. simpl in *.
        destruct l as (eqv, l).
        destruct l as (l,d).
        destruct Hvalids as [Hvalids Hnoequiv].
        unfold vvalid in Hvalids. simpl in Hvalids.
        unfold vvalid in Hvalids. simpl in Hvalids.
        unfold no_equivocations_additional_constraint_with_pre_loaded in Hnoequiv.
        unfold no_equivocations_except_from in Hnoequiv.
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
              (replayed_trace_from_state_correspondence' full_replay_state _ (proj2 Htr)
              epref eqv
              )
              as Hstate.
            destruct Hstate as [Hsize [Houtput [Hstate Hstate_pre]]].
            spec Hstate id Hid.
            destruct Hstate as [Hi Hstate].
            exists Hi.
            clear -Hstate Hvalids.
            match goal with
            |- vvalid _ _ (?s1,_) =>
              match type of Hvalids with
              | vvalid _ _ (?s2,_) =>
                replace s1 with s2
              end
            end.
            assumption.
          ++ simpl. rewrite <- (apply_plan_last SeededXE) in *.
            rewrite <- (apply_plan_last (pre_loaded_vlsm (composite_vlsm equivocator_IM constraint) seed)).
            apply (Hconstraint _ _ _  _ _ _ _ eq_refl eq_refl).
Qed.

Lemma replayed_trace_from_protocol_free
  (full_replay_state : vstate equivocators_no_equivocations_vlsm)
  (Hfull_replay_state : protocol_state_prop SeededXE full_replay_state)
  (is : vstate equivocators_no_equivocations_vlsm)
  (tr : list (composite_transition_item equivocator_IM))
  (Htr : finite_protocol_trace SeededXE is tr)
  : finite_protocol_trace_from SeededFree
      full_replay_state (replayed_trace_from full_replay_state is tr).
Proof.
  specialize
    (replayed_trace_from_protocol _ Hfull_replay_state _ _ Htr (free_constraint equivocator_IM))
    as Hreplay.
  spec Hreplay. { intro; intros. exact I. }
  spec Hreplay. { intros. exact I. }
  assumption.
Qed.

Lemma replayed_trace_from_protocol_equivocating
  (full_replay_state : composite_state equivocator_IM)
  (Hfull_replay_state : protocol_state_prop SeededXE full_replay_state)
  (is : vstate SeededXE)
  (tr : list (composite_transition_item equivocator_IM))
  (Htr : finite_protocol_trace SeededXE is tr)
  : finite_protocol_trace_from SeededXE
      full_replay_state (replayed_trace_from full_replay_state is tr).
Proof.
  apply replayed_trace_from_protocol
  ;[assumption|assumption|intro; intros; assumption|].
  intros.
  split; [|exact I].
  subst tr.
  destruct Htr as [Htr His].
  apply finite_protocol_trace_from_app_iff in Htr.
  destruct Htr as [Hepref Hesuf].
  specialize (replayed_trace_from_protocol_free _ Hfull_replay_state _ _ (conj Hepref His))
    as Hreplay_epref_free.
  assert
    (Hreplay_epref_pre :
      finite_protocol_trace_from PreFree full_replay_state (replayed_trace_from full_replay_state is epref)
    ).
  { revert Hreplay_epref_free. apply VLSM_incl_finite_protocol_trace_from.
    apply pre_loaded_vlsm_incl_pre_loaded_with_all_messages.
  }
  specialize (finite_ptrace_last_pstate _ _ _ Hreplay_epref_pre) as Hlast_replay_pre.
  destruct (input eitem) as [m|] eqn:Hinput; [|exact I].
  apply finite_ptrace_first_valid_transition in Hesuf as Hitem.
  destruct Hitem as [[Hs [Hinp [_ Heqv] ]] _].
  destruct eitem. simpl in Hinput, Hleitem. subst l.
  subst input.
  destruct Heqv as [[Heqv | Hinitial] _]; [| right; assumption].
  left. apply proper_sent; [assumption|].
  assert
    (Hepref_pre :
      finite_protocol_trace_from PreFree is epref
    ).
  { revert Hepref. apply VLSM_incl_finite_protocol_trace_from.
    apply seeded_equivocators_incl_preloaded.
  }
  specialize (finite_ptrace_last_pstate _ _ _ Hepref_pre) as Hlast_pre.

  apply proper_sent in Heqv; [|assumption].
  specialize (Heqv is epref (conj Hepref_pre His) eq_refl).
  apply has_been_sent_consistency; [|assumption|].
  { apply (composite_has_been_sent_capability equivocator_IM (free_constraint equivocator_IM) finite_index (equivocator_Hbs IM Hbs)).
  }
  apply finite_protocol_trace_from_complete_left in Hreplay_epref_pre as Hpre_replay.
  destruct Hpre_replay as [is_replay [trs_replay [Htrs_replay Hfull_replay_state_lst]]].
  eexists _. eexists _. exists Htrs_replay.
  split.
  - rewrite map_app, last_app. simpl.
    subst.
    reflexivity.
  - apply Exists_exists in Heqv.
    destruct Heqv as [mitem [Hmitem Houtput]].
    apply in_split in Hmitem.
    destruct Hmitem as [pref [suf Heqepref]].
    change (mitem :: suf) with ([mitem] ++ suf) in Heqepref.
    subst epref.
    rewrite app_assoc.
    rewrite replayed_trace_from_app.
    apply Exists_app. right. apply Exists_app. left.
    destruct
      (replayed_trace_from_state_correspondence' full_replay_state is His (pref ++ [mitem]) eqv)
      as [_ [Houtput' _]].
    spec Houtput'.
    { intro contra; destruct pref; discriminate contra. }
    rewrite app_assoc in Hepref.
    apply (finite_protocol_trace_from_app_iff SeededXE) in Hepref.
    apply proj1 in Hepref.
    specialize (trace_to_plan_to_trace SeededXE _ _ Hepref) as Hfst.

    replace (fst(composite_apply_plan equivocator_IM is
      (composite_trace_to_plan equivocator_IM
        (pref ++ [mitem])))) with (pref ++ [mitem])
      in Houtput'.
    change
      (fst (applied_replay_plan_from full_replay_state is (pref ++ [mitem])))
      with (replayed_trace_from full_replay_state is (pref ++ [mitem]))
      in Houtput'.
    rewrite! replayed_trace_from_app in Houtput'.
    simpl in Houtput'.
    rewrite last_error_is_last in Houtput'.
    rewrite replayed_trace_from_app.
    apply Exists_app. right. simpl.
    unfold composite_apply_plan,_apply_plan in Houtput'.
    unfold composite_apply_plan,_apply_plan. simpl in *.
    destruct (update_equivocators_transition_item_descriptor full_replay_state mitem) eqn:Hupdated_item.
    simpl in *.
    destruct label_a as (i, li).
    match goal with
    |- context [vtransition ?V ?l ?som] =>
      destruct (vtransition V l som) eqn:Ht
    end.
    simpl in *.
    rewrite last_error_is_last in Houtput'.
    simpl in Houtput'. inversion Houtput'.
    left. simpl. assumption.
Qed.

End all_equivocating.
