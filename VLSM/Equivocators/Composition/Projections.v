Require Import
  List Coq.Vectors.Fin FinFun
  Arith.Compare_dec Lia
  Program
  Coq.Logic.JMeq
  .
Import ListNotations.
From CasperCBC
  Require Import
    Preamble ListExtras FinExtras
    VLSM.Common VLSM.Composition VLSM.Equivocation
    VLSM.Equivocators.Common VLSM.Equivocators.Projections
    VLSM.Equivocators.MessageProperties
    VLSM.Equivocators.Composition.Common
    .

Section equivocators_composition_projections.

Context {message : Type}
  {equiv_index : Type}
  (index := equiv_index)
  {IndEqDec : EqDecision index}
  (IM : index -> VLSM message)
  (Hbs : forall i : index, has_been_sent_capability (IM i))
  (i0 : index)
  (X := free_composite_vlsm IM i0)
  (index_listing : list index)
  (finite_index : Listing index_listing)
  (equivocators_choice := equivocators_choice IM)
  (equivocators_no_equivocations_vlsm := equivocators_no_equivocations_vlsm IM Hbs i0 index_listing finite_index)
  (equivocators_state_project := equivocators_state_project IM i0)
  (equivocator_IM := equivocator_IM IM)
  (equivocators_choice_update := equivocators_choice_update IM)
  (proper_equivocators_choice := proper_equivocators_choice IM i0)
  .

Definition equivocators_transition_item_project
  (eqv_choice : equivocators_choice)
  (item : vtransition_item equivocators_no_equivocations_vlsm)
  : option (option (vtransition_item X) * equivocators_choice)
  :=
  match item with {| l := el; input := iom; output := oom; destination := s |} =>
    let sx := equivocators_state_project eqv_choice s in
    let (eqv, li) := el in
    let deqv := eqv_choice eqv in
    match
      equivocator_vlsm_transition_item_project
        (IM eqv)
        {| l := li; input := iom; output := oom; destination := s eqv |}
        deqv
        with
    | Some (Some item', deqv') =>
      Some
        (Some (@Build_transition_item message (@type message X)
          (existT (fun n : index => vlabel (IM n)) eqv (l item'))
          iom sx oom)
        , equivocators_choice_update eqv_choice eqv deqv')
    | Some (None, deqv') => Some (None, equivocators_choice_update eqv_choice eqv deqv')
    | None => None
    end
  end.

Lemma equivocators_transition_item_project_proper
  (eqv_choice : equivocators_choice)
  (item : vtransition_item equivocators_no_equivocations_vlsm)
  (Hproper : proper_equivocators_choice eqv_choice (destination item))
  : equivocators_transition_item_project eqv_choice item <> None.
Proof.
  destruct item. simpl.
  destruct l as [e v].
  intro contra.
  spec Hproper e. simpl in Hproper.
  elim
    (equivocator_transition_item_project_proper (IM e)
      (@Build_transition_item message (@equivocator_type message (IM e))
        v input (destination e) output)
      (eqv_choice e) Hproper).
  simpl in contra. simpl.
  destruct
    (equivocator_vlsm_transition_item_project (IM e)
      (@Build_transition_item message (@equivocator_type message (IM e))
        v input (destination e) output)
      (eqv_choice e))
  ; [|reflexivity].
  destruct p. destruct o; congruence.
Qed.

Definition equivocators_trace_project_folder
  (item : vtransition_item equivocators_no_equivocations_vlsm)
  (result: option (list (vtransition_item X) * equivocators_choice))
  : option (list (vtransition_item X) * equivocators_choice)
  :=
  match result with
  | None => None
  | Some (r, idescriptor) =>
    match equivocators_transition_item_project idescriptor item with
    | None => None
    | Some (None, odescriptor) => Some (r, odescriptor)
    | Some (Some item', odescriptor) => Some (item' :: r, odescriptor)
    end
  end.

Lemma equivocators_trace_project_fold_None
  (tr : list (vtransition_item equivocators_no_equivocations_vlsm))
  : fold_right equivocators_trace_project_folder None tr = None.
Proof.
  induction tr; [reflexivity|]. simpl. rewrite IHtr. reflexivity.
Qed.

Lemma equivocators_trace_project_folder_additive
  (tr : list (vtransition_item equivocators_no_equivocations_vlsm))
  (itrX trX : list (vtransition_item X))
  (ieqv_choice eqv_choice : equivocators_choice)
  (Htr : fold_right equivocators_trace_project_folder (Some ([], ieqv_choice)) tr
    = Some (trX, eqv_choice))
  : fold_right equivocators_trace_project_folder (Some (itrX, ieqv_choice)) tr
    = Some (trX ++ itrX, eqv_choice).
Proof.
  generalize dependent trX. revert eqv_choice ieqv_choice.
  induction tr; intros.
  - simpl in Htr. inversion Htr. reflexivity.
  - simpl in Htr.
    simpl.
    destruct
      (fold_right equivocators_trace_project_folder (Some ([], ieqv_choice)) tr)
      as [(trX', eqv_choice')|] eqn:Hfld; [|discriminate Htr].
    simpl in Htr.
    destruct (equivocators_transition_item_project eqv_choice' a)
      as [(oitem, eqv_choice'')|] eqn:Ha; [|congruence].
    destruct oitem as [item'|]; inversion Htr; subst
    ; specialize (IHtr _ _ _ Hfld)
    ; rewrite IHtr
    ; simpl
    ; rewrite Ha
    ; reflexivity.
Qed.

(**
The projection of an [equivocators] trace is obtained by traversing the
trace from right to left guided by the descriptors produced by
[equivocators_transition_item_project] and gathering all non-empty
[transition_item]s it produces.
*)
Definition equivocators_trace_project
  (eqv_choice : equivocators_choice)
  (tr : list (vtransition_item equivocators_no_equivocations_vlsm))
  : option (list (vtransition_item X) * equivocators_choice)
  :=
  fold_right
    equivocators_trace_project_folder
    (Some ([], eqv_choice))
    tr.

Local Tactic Notation "unfold_transition"  hyp(Ht) :=
  ( unfold transition in Ht; unfold equivocator_IM in Ht;
  unfold equivocator_vlsm in Ht; unfold mk_vlsm in Ht;
  unfold machine in Ht; unfold projT2 in Ht;
  unfold equivocator_vlsm_machine in Ht; unfold equivocator_transition in Ht). 

Lemma equivocators_protocol_trace_project
  (final_choice : equivocators_choice)
  (is : vstate equivocators_no_equivocations_vlsm)
  (tr : list (vtransition_item equivocators_no_equivocations_vlsm))
  (final_state := last (map destination tr) is)
  (Hproper : proper_equivocators_choice final_choice final_state)
  (Htr : finite_protocol_trace_from equivocators_no_equivocations_vlsm is tr)
  : exists
    (trX : list (vtransition_item X))
    (initial_choice : equivocators_choice)
    (isX := equivocators_state_project initial_choice is)
    (Hproject: equivocators_trace_project final_choice tr = Some (trX, initial_choice))
    (final_stateX := last (map destination trX) isX)
    (Hfinal : equivocators_state_project final_choice final_state = final_stateX)
    (Hproper : proper_equivocators_choice initial_choice is),
    finite_protocol_trace_from X isX trX.
Proof.
  generalize dependent final_choice.
  generalize dependent is.
  induction tr; intros.
  - exists []. simpl. exists final_choice.
    exists eq_refl. exists eq_refl. exists Hproper.
    constructor.
    inversion Htr. subst. destruct H as [_om His].
    apply (proj2 (equivocators_protocol_state_project IM Hbs i0 _ _ _ _ His) final_choice Hproper).
  - unfold equivocators_trace_project. simpl.
    inversion Htr. subst s' tl.
    specialize (IHtr _ H2).
    unfold final_state in Hproper.
    rewrite map_cons in Hproper.
    rewrite unroll_last in Hproper.
    rewrite <- H in Hproper. simpl in Hproper.
    specialize (IHtr _ Hproper).
    destruct IHtr as [trX' [initial_choice' [Hproject [Hfinal [Hproper' HtrX']]]]].
    unfold equivocators_trace_project in Hproject.
    rewrite Hproject.
    unfold equivocators_trace_project_folder.
    destruct H3 as [[His [Hiom [Hv _]]] Ht].
    simpl in Hv. simpl in Ht.
    destruct l as (eqv, li).
    destruct (vtransition (Common.equivocator_IM IM eqv) li (is eqv, iom)) as (si', om')
      eqn:Ht'.
    inversion Ht. subst s oom. clear Ht.
    unfold final_state. rewrite map_cons. rewrite unroll_last. subst a.
    clear final_state.
    destruct His as [_omis His]. apply equivocators_protocol_state_project in His. destruct His as [_ His].
    destruct Hiom as [_siom Hiom]. apply equivocators_protocol_state_project in Hiom.
    destruct Hiom as [Hiom _].
    simpl in *.
    destruct (initial_choice' eqv) as [seqv | ieqv feqv] eqn:Heqv.
    * eexists _. eexists _. exists eq_refl.
      repeat split.
      -- replace
          (equivocators_state_project
          (equivocators_choice_update initial_choice' eqv
             (NewMachine (IM (eqv)) seqv)) is)
          with
            (equivocators_state_project initial_choice'
            (state_update (Common.equivocator_IM IM) is (eqv) si'))
          ;[assumption|].
        assert
          (Hinitial_choice' : equivocators_choice_update initial_choice' eqv
          (NewMachine (IM (eqv)) seqv) = initial_choice').
        { apply functional_extensionality_dep_good.
          intro eqv'.  unfold equivocators_choice_update.
          destruct (decide (eqv' = eqv)).
          - subst eqv'.
            rewrite equivocators_choice_update_eq. symmetry. assumption.
          - rewrite equivocators_choice_update_neq by assumption. reflexivity.
        }
        rewrite Hinitial_choice'.
        unfold equivocators_state_project.
        rewrite equivocators_state_project_state_update_eqv.
        rewrite Heqv.
        apply functional_extensionality_dep_good.
        intros eqv'.
        destruct (decide (eqv = eqv')).
        ** subst eqv'. rewrite state_update_eq. simpl.
          unfold Common.equivocators_state_project.
          rewrite Heqv. reflexivity.
        ** rewrite state_update_neq; congruence.
      -- intro eqv'.
        destruct (decide (eqv' = eqv)).
        ++ subst. unfold equivocators_choice_update. rewrite equivocators_choice_update_eq.
          spec Hproper' eqv. rewrite Heqv in Hproper'. assumption.
        ++ unfold equivocators_choice_update.
          rewrite equivocators_choice_update_neq by assumption.
          spec Hproper' eqv'.
          rewrite state_update_neq in Hproper'; [assumption|]. congruence.
      -- replace
          (equivocators_state_project
          (equivocators_choice_update initial_choice' eqv
             (NewMachine (IM (eqv)) seqv)) is)
          with
            (equivocators_state_project initial_choice'
            (state_update (Common.equivocator_IM IM) is (eqv) si'))
        ; [assumption|].
        rewrite (equivocators_state_project_state_update_eqv IM i0).
        apply functional_extensionality_dep_good.
        intro i'. destruct (decide (i' = (eqv))).
        ++ subst. rewrite state_update_eq. rewrite Heqv.
          unfold equivocators_state_project.
          unfold Common.equivocators_state_project.
          unfold equivocators_choice_update.
          rewrite equivocators_choice_update_eq. reflexivity.
        ++ rewrite state_update_neq by assumption.
          unfold equivocators_state_project.
          unfold Common.equivocators_state_project.
          unfold equivocators_choice_update.
          rewrite equivocators_choice_update_neq; congruence.
    * rewrite state_update_eq.
      destruct li as (li, di).
      destruct si' as (nsi', bsi').
      specialize (Hproper' eqv) as Hproper_eqv.
      rewrite state_update_eq in Hproper_eqv.
      rewrite Heqv in Hproper_eqv.
      simpl in Hproper_eqv.
      unfold equivocator_vlsm_transition_item_project.
      destruct (le_lt_dec (S nsi') ieqv); [lia|].
      unfold vvalid in Hv. simpl in Hv.
      unfold vtransition in Ht'. 
      unfold transition in Ht'. unfold Common.equivocator_IM in Ht'.
      unfold equivocator_vlsm in Ht'. unfold mk_vlsm in Ht'.
      unfold machine in Ht'. unfold projT2 in Ht'.
      unfold equivocator_vlsm_machine in Ht'.
      unfold equivocator_transition in Ht'.
      unfold snd in Ht'.
      destruct di as [sdi|idi fdi].
      -- destruct Hv as [Hsdi _Hiom]. subst iom.
        inversion Ht'. subst om'. clear Ht'.
        unfold equivocator_state_extend in H0.
        destruct (is (eqv)) as (is_eqv_n, is_eqv_s) eqn:His_eqv.
        inversion H0. subst nsi'.
        simpl_existT.
        destruct (nat_eq_dec (S is_eqv_n) (S is_eqv_n)); [|lia].
        destruct (nat_eq_dec (S ieqv) (S (S is_eqv_n))).
        ++ inversion e0. subst ieqv. clear e e0.
          eexists _. eexists _. exists eq_refl.
          assert
            (Hfinal' :
            equivocators_state_project final_choice
            (last (map destination tr)
               (state_update (Common.equivocator_IM IM) is (eqv)
                  (equivocator_state_extend (IM (eqv)) (existT (fun n : nat => t (S n) -> vstate (IM (eqv)))
                  is_eqv_n is_eqv_s) sdi))) =
            last (map destination trX')
              (equivocators_state_project
                 (equivocators_choice_update initial_choice' eqv
                    (NewMachine (IM (eqv)) sdi)) is)
            ).
          { subst bsi'. simpl in *. rewrite Hfinal.
            rewrite (equivocators_state_project_state_update_eqv IM i0).
            rewrite Heqv.
            unfold projT1. unfold projT2.
            destruct (le_lt_dec (S (S is_eqv_n)) (S is_eqv_n)); [lia|].
            f_equal.
            apply functional_extensionality_dep_good.
            rewrite to_nat_of_nat.
            destruct (nat_eq_dec (S is_eqv_n) (S is_eqv_n)); [|lia].
            intro i'. destruct (decide (i' = (eqv))).
            - subst. rewrite state_update_eq.
              unfold equivocators_state_project.
              unfold Common.equivocators_state_project.
              unfold equivocators_choice_update.
              rewrite equivocators_choice_update_eq.
              reflexivity.
            - rewrite state_update_neq by assumption.
              unfold equivocators_state_project.
              unfold Common.equivocators_state_project.
              unfold equivocators_choice_update.
              rewrite equivocators_choice_update_neq; congruence.
          }
          exists Hfinal'.
          assert
            (Hproper'' :
              proper_equivocators_choice
                (equivocators_choice_update initial_choice' eqv
                  (NewMachine (IM (eqv)) sdi)) is).
          {
          intro eqv'. spec Hproper' eqv'.  unfold equivocators_choice_update.
          destruct (decide (eqv' = eqv)).
          - subst. rewrite equivocators_choice_update_eq. assumption.
          - rewrite equivocators_choice_update_neq by assumption.
            rewrite state_update_neq in Hproper'; congruence.
          }
          exists Hproper''.
          replace
            (equivocators_state_project
            (equivocators_choice_update initial_choice' eqv
               (NewMachine (IM (eqv)) sdi)) is)
            with
              (equivocators_state_project initial_choice'
              (state_update (Common.equivocator_IM IM) is
                 (eqv)
                 (existT (fun n : nat => t (S n) -> vstate (IM (eqv)))
                  (S is_eqv_n) bsi')))
          ; [assumption|].
          subst bsi'.
          unfold equivocators_state_project.
          rewrite equivocators_state_project_state_update_eqv.
          rewrite Heqv. unfold projT1. unfold projT2.
          destruct (le_lt_dec (S (S is_eqv_n)) (S is_eqv_n)); [lia |].
          rewrite to_nat_of_nat.
          destruct ( nat_eq_dec (S is_eqv_n) (S is_eqv_n) ); [|congruence].
          replace (of_nat_lt l0) with (of_nat_lt Hproper_eqv) in * by apply of_nat_ext.
          clear l0.
          replace (of_nat_lt l) with (of_nat_lt Hproper_eqv) in * by apply of_nat_ext.
          clear l.
          apply functional_extensionality_dep_good.
          intro i.
          unfold Common.equivocators_state_project at 2.
          unfold equivocators_choice_update.
          destruct (decide (i = (eqv))).
          ** subst. rewrite state_update_eq.
            rewrite equivocators_choice_update_eq.
            reflexivity.
          ** repeat rewrite state_update_neq by assumption.
            unfold Common.equivocators_state_project.
            rewrite equivocators_choice_update_neq; congruence.
        ++ eexists _. eexists _. exists eq_refl.
          assert
            (Hfinal' :
              equivocators_state_project final_choice
                (last (map destination tr)
                   (state_update (Common.equivocator_IM IM) is
                      (eqv)
                      (equivocator_state_extend (IM (eqv))
                         (existT (fun n0 : nat => t (S n0) -> vstate (IM (eqv)))
                            is_eqv_n is_eqv_s) sdi))) =
              last (map destination trX')
                (equivocators_state_project
                   (equivocators_choice_update initial_choice' eqv
                      (Existing (IM (eqv)) ieqv false)) is)
            ).
          { subst bsi'. simpl in *. rewrite Hfinal.
            rewrite (equivocators_state_project_state_update_eqv IM i0).
            rewrite Heqv.
            unfold projT1. unfold projT2.
            destruct (le_lt_dec (S (S is_eqv_n)) ieqv); [lia|].
            f_equal.
            apply functional_extensionality_dep_good.
            rewrite to_nat_of_nat.
            destruct (nat_eq_dec ieqv (S is_eqv_n)); [lia|].
            intro i'. destruct (decide (i' = (eqv))).
            - subst. rewrite state_update_eq.
              unfold equivocators_state_project.
              unfold Common.equivocators_state_project.
              unfold equivocators_choice_update.
              rewrite equivocators_choice_update_eq.
              rewrite His_eqv.
              destruct (le_lt_dec (S is_eqv_n) ieqv); [lia|].
              f_equal. apply of_nat_ext.
            - rewrite state_update_neq by assumption.
              unfold equivocators_state_project.
              unfold Common.equivocators_state_project.
              unfold equivocators_choice_update.
              rewrite equivocators_choice_update_neq; congruence.
          }
          exists Hfinal'.
          assert
            (Hproper'' :
            proper_equivocators_choice
            (equivocators_choice_update initial_choice' eqv
               (Existing (IM (eqv)) ieqv false)) is).
          {
          intro eqv'. spec Hproper' eqv'.  unfold equivocators_choice_update.
          destruct (decide (eqv' = eqv)).
          - subst. rewrite equivocators_choice_update_eq.
            simpl. rewrite His_eqv. simpl. lia.
          - rewrite equivocators_choice_update_neq by assumption.
            rewrite state_update_neq in Hproper'; congruence.
          }
          exists Hproper''.
          replace
            ((equivocators_state_project
            (equivocators_choice_update initial_choice' eqv
               (Existing (IM (eqv)) ieqv false)) is))
            with
              (equivocators_state_project initial_choice'
              (state_update (Common.equivocator_IM IM) is
                 (eqv)
                 (existT (fun n : nat => t (S n) -> vstate (IM (eqv)))
                  (S is_eqv_n) bsi')))
          ; [assumption|].
          unfold equivocators_state_project.
          rewrite equivocators_state_project_state_update_eqv.
          rewrite Heqv. unfold projT1. unfold projT2.
          destruct (le_lt_dec (S (S is_eqv_n)) ieqv); [lia |].
          replace (of_nat_lt l0) with (of_nat_lt Hproper_eqv) in * by apply of_nat_ext.
          clear l0.
          replace (of_nat_lt l) with (of_nat_lt Hproper_eqv) in * by apply of_nat_ext.
          clear l.
          apply functional_extensionality_dep_good.
          intro i.
          destruct (decide (i = (eqv))).
          --- subst. rewrite state_update_eq.
            unfold Common.equivocators_state_project.
            unfold equivocators_choice_update.
            rewrite equivocators_choice_update_eq.
            rewrite to_nat_of_nat. rewrite His_eqv.
            destruct (le_lt_dec (S is_eqv_n) ieqv); [lia|].
            destruct (nat_eq_dec ieqv (S is_eqv_n)); [congruence|].
            f_equal. apply of_nat_ext.
          --- rewrite state_update_neq by assumption.
            unfold Common.equivocators_state_project.
            unfold equivocators_choice_update.
            rewrite equivocators_choice_update_neq; congruence.
    -- destruct Hv as [Hidi Hv].
      destruct (le_lt_dec (S (projT1 (is (eqv)))) idi); [lia|].
      replace (of_nat_lt l0) with (of_nat_lt Hidi) in * by apply of_nat_ext.
      clear l0.
      unfold fst in Ht'.
      destruct (is (eqv)) as (neqv, bseqv) eqn:Hiseqv.
      unfold projT2 in Ht'.
      destruct (vtransition (IM (eqv)) li (bseqv (of_nat_lt Hidi), iom))
        as (si', siom') eqn:Ht''.
      destruct fdi.
      ++ inversion Ht'. subst.
        simpl_existT.
        destruct (nat_eq_dec (S ieqv) (S (S neqv))).
        ** eexists _. eexists _. exists eq_refl.
          inversion e. subst ieqv. clear e.
          unfold Common.l.
          rewrite map_cons. unfold destination at 5.
          assert
            (Hfinal' :
              equivocators_state_project final_choice
                (last (map destination tr)
                   (state_update (Common.equivocator_IM IM) is
                      (eqv)
                      (existT (fun n : nat => t (S n) -> vstate (IM (eqv)))
                         (S neqv) bsi'))) =
              last
                (equivocators_state_project initial_choice'
                   (state_update (Common.equivocator_IM IM) is
                      (eqv)
                      (existT (fun n : nat => t (S n) -> vstate (IM (eqv)))
                         (S neqv) bsi')) :: map destination trX')
                (equivocators_state_project
                   (equivocators_choice_update initial_choice' eqv
                      (Existing (IM (eqv)) idi true)) is)
            ).
          { rewrite unroll_last. subst bsi'. simpl in *. rewrite Hfinal.
            rewrite (equivocators_state_project_state_update_eqv IM i0).
            rewrite Heqv.
            unfold projT1. unfold projT2.
            reflexivity.
          }
          exists Hfinal'.
          assert
            (Hproper'' :
            proper_equivocators_choice
            (equivocators_choice_update initial_choice' eqv
               (Existing (IM (eqv)) idi true)) is).
          { intro eqv'. spec Hproper' eqv'.
            unfold equivocators_choice_update.
            destruct (decide (eqv' = eqv)).
            - subst. rewrite state_update_eq in Hproper'.
              rewrite equivocators_choice_update_eq.
              rewrite Heqv in Hproper'.
              simpl in *.
              rewrite Hiseqv. simpl. lia.
            - rewrite state_update_neq in Hproper' by congruence.
              rewrite equivocators_choice_update_neq; assumption.
          }
          exists Hproper''.
          constructor; [assumption|].
          repeat split; [apply His; assumption|assumption|..].
          --- remember equivocators_state_project as esp. simpl.
            simpl in Hv. subst esp. unfold equivocators_state_project.
            unfold Common.equivocators_state_project.
            unfold equivocators_choice_update.
            rewrite equivocators_choice_update_eq.
            rewrite Hiseqv.
            simpl in Hidi.
            destruct (le_lt_dec (S neqv) idi); [lia|].
            replace (of_nat_lt l0) with (of_nat_lt Hidi) in * by apply of_nat_ext.
            clear l0.
            assumption.
          --- unfold equivocators_state_project.
            rewrite equivocators_state_project_state_update_eqv.
            rewrite Heqv. unfold projT1. unfold projT2.
            destruct (le_lt_dec (S (S neqv)) (S neqv)); [lia|].
            replace (of_nat_lt l) with (of_nat_lt Hproper_eqv) in * by apply of_nat_ext.
            clear l.
            replace (of_nat_lt l0) with (of_nat_lt Hproper_eqv) in * by apply of_nat_ext.
            clear l0.
            remember Common.equivocators_state_project as esp.
            remember (of_nat_lt Hproper_eqv) as onl.
            simpl.
            rewrite  Heqesp.
            unfold Common.equivocators_state_project at 1.
            unfold equivocators_choice_update.
            rewrite equivocators_choice_update_eq.
            rewrite Hiseqv.
            simpl in Hidi.
            destruct (le_lt_dec (S neqv) idi); [lia|].
            replace (of_nat_lt l) with (of_nat_lt Hidi) in * by apply of_nat_ext.
            clear l. clear Hproject. subst. rewrite to_nat_of_nat.
            destruct (nat_eq_dec (S neqv) (S neqv)); [|congruence].
            simpl in *. rewrite Ht''.
            f_equal.
            apply functional_extensionality_dep_good.
            intro eqvi.
            destruct (decide (eqvi = eqv)).
            +++ subst. repeat rewrite state_update_eq. reflexivity.
            +++ repeat rewrite state_update_neq by assumption.
              unfold  Common.equivocators_state_project.
              destruct (decide (eqvi = eqv)); [congruence|].
              rewrite equivocators_choice_update_neq; congruence.
        ** eexists _. eexists _. exists eq_refl.
          assert
            (Hfinal' :
              equivocators_state_project final_choice
                (last (map destination tr)
                   (state_update (Common.equivocator_IM IM) is
                      (eqv)
                      (existT (fun n0 : nat => t (S n0) -> vstate (IM (eqv)))
                         (S neqv) bsi'))) =
              last (map destination trX')
                (equivocators_state_project
                   (equivocators_choice_update initial_choice' eqv
                      (Existing (IM (eqv)) ieqv false)) is)
            ).
          { subst bsi'. simpl in *. rewrite Hfinal.
            rewrite (equivocators_state_project_state_update_eqv IM i0).
            rewrite Heqv.
            unfold projT1. unfold projT2.
            f_equal.
            apply functional_extensionality_dep_good.
            destruct (le_lt_dec (S (S neqv)) ieqv); [lia|].
            rewrite to_nat_of_nat.
            destruct (nat_eq_dec ieqv (S neqv) ); [lia|].
            intro i'. destruct (decide (i' = (eqv))).
            - subst. rewrite state_update_eq.
              unfold equivocators_state_project.
              unfold Common.equivocators_state_project.
              unfold equivocators_choice_update.
              rewrite equivocators_choice_update_eq.
              rewrite Hiseqv.
              destruct (le_lt_dec (S neqv) ieqv); [lia|].
              f_equal. apply of_nat_ext.
            - rewrite state_update_neq by assumption.
              unfold equivocators_state_project.
              unfold Common.equivocators_state_project.
              unfold equivocators_choice_update.
              rewrite equivocators_choice_update_neq; congruence.
          }
          exists Hfinal'.
          assert
            (Hproper'' :
            proper_equivocators_choice
              (equivocators_choice_update initial_choice' eqv
                 (Existing (IM (eqv)) ieqv false)) is).
          { intro eqv'. spec Hproper' eqv'.
            unfold equivocators_choice_update.
            destruct (decide (eqv' = eqv)).
            - subst. rewrite state_update_eq in Hproper'.
              rewrite equivocators_choice_update_eq.
              rewrite Heqv in Hproper'.
              simpl in *.
              rewrite Hiseqv. simpl. lia.
            - rewrite state_update_neq in Hproper' by congruence.
              rewrite equivocators_choice_update_neq; assumption.
          }
          exists Hproper''.
          replace
            (equivocators_state_project
            (equivocators_choice_update initial_choice' eqv
               (Existing (IM (eqv)) ieqv false)) is)
            with
            (equivocators_state_project initial_choice'
            (state_update (Common.equivocator_IM IM) is
               (eqv)
               (existT (fun n : nat => t (S n) -> vstate (IM (eqv)))
                  (S neqv) bsi')))
          ; [assumption|].
          unfold equivocators_state_project.
          rewrite equivocators_state_project_state_update_eqv.
          rewrite Heqv. unfold projT1. unfold projT2.
          destruct (le_lt_dec (S (S neqv)) ieqv); [lia|].
          replace (of_nat_lt l) with (of_nat_lt Hproper_eqv) in * by apply of_nat_ext.
          clear l.
          replace (of_nat_lt l0) with (of_nat_lt Hproper_eqv) in * by apply of_nat_ext.
          clear l0.
          apply functional_extensionality_dep_good.
          intro i.
          destruct (decide (i = eqv)).
          --- subst. rewrite state_update_eq.
            rewrite to_nat_of_nat.
            destruct (nat_eq_dec ieqv (S neqv)); [congruence|].
            unfold Common.equivocators_state_project.
            unfold equivocators_choice_update.
            rewrite equivocators_choice_update_eq.
            rewrite Hiseqv.
            destruct (le_lt_dec (S neqv) ieqv); [lia|].
            f_equal. apply of_nat_ext.
          --- rewrite state_update_neq by assumption.
            unfold  Common.equivocators_state_project.
            unfold equivocators_choice_update.
            rewrite equivocators_choice_update_neq; congruence.
      ++ inversion Ht'. subst. simpl_existT.
        destruct (nat_eq_dec idi ieqv).
        --- subst. simpl in Hidi.
          replace (of_nat_lt l) with (of_nat_lt Hidi) in * by apply of_nat_ext.
          clear l.
          replace (of_nat_lt Hproper_eqv) with (of_nat_lt Hidi) in * by apply of_nat_ext.
          clear Hproper_eqv.
          rewrite eq_dec_if_true in * by reflexivity.
          eexists _. eexists _. exists eq_refl.
          rewrite map_cons. unfold destination at 5.
          assert
            (Hfinal' :
              equivocators_state_project final_choice
                (last (map destination tr)
                   (state_update (Common.equivocator_IM IM) is
                      (eqv)
                      (existT (fun n : nat => t (S n) -> vstate (IM (eqv))) nsi'
                         (fun j : t (S nsi') =>
                          if eq_dec (of_nat_lt Hidi) j then si' else bseqv j)))) =
              last
                (equivocators_state_project initial_choice'
                   (state_update (Common.equivocator_IM IM) is
                      (eqv)
                      (existT (fun n : nat => t (S n) -> vstate (IM (eqv))) nsi'
                         (fun j : t (S nsi') =>
                          if eq_dec (of_nat_lt Hidi) j then si' else bseqv j)))
                 :: map destination trX')
                (equivocators_state_project
                   (equivocators_choice_update initial_choice' eqv
                      (Existing (IM (eqv)) ieqv false)) is)
            ).
          { rewrite unroll_last. simpl in *. rewrite Hfinal.
            rewrite (equivocators_state_project_state_update_eqv IM i0).
            rewrite Heqv.
            unfold projT1. unfold projT2.
            reflexivity.
          }
          exists Hfinal'.
          assert
            (Hproper'' : proper_equivocators_choice
            (equivocators_choice_update initial_choice' eqv
               (Existing (IM (eqv)) ieqv false)) is).
          { intro eqv'. spec Hproper' eqv'.
            unfold equivocators_choice_update.
            destruct (decide (eqv' = eqv)).
            - subst. rewrite state_update_eq in Hproper'.
              rewrite equivocators_choice_update_eq.
              rewrite Heqv in Hproper'.
              simpl in *.
              rewrite Hiseqv. simpl. lia.
            - rewrite state_update_neq in Hproper' by congruence.
              rewrite equivocators_choice_update_neq; assumption.
          }
          exists Hproper''.
          constructor; [assumption|].
          repeat split; [apply His; assumption| assumption| |].
          +++ remember equivocators_state_project as esp. simpl.
            simpl in Hv. subst esp. unfold equivocators_state_project.
            unfold Common.equivocators_state_project.
            unfold equivocators_choice_update.
            rewrite equivocators_choice_update_eq.
            rewrite Hiseqv.
            simpl in Hidi.
            destruct (le_lt_dec (S nsi') ieqv); [lia|].
            replace (of_nat_lt l) with (of_nat_lt Hidi) in * by apply of_nat_ext.
            clear l.
            assumption.
          +++ unfold equivocators_state_project.
            rewrite equivocators_state_project_state_update_eqv.
            rewrite Heqv. unfold projT1. unfold projT2.
            destruct (le_lt_dec (S nsi') ieqv); [lia|].
            replace (of_nat_lt l) with (of_nat_lt Hidi) in * by apply of_nat_ext.
            clear l.
            remember Common.equivocators_state_project as esp.
            remember (of_nat_lt Hidi) as onl.
            simpl.
            rewrite  Heqesp.
            unfold Common.equivocators_state_project at 1.
            unfold equivocators_choice_update.
            rewrite equivocators_choice_update_eq.
            rewrite Hiseqv.
            destruct (le_lt_dec (S nsi') ieqv); [lia|].
            replace (of_nat_lt l) with (of_nat_lt Hidi) in * by apply of_nat_ext.
            clear l. clear Hproject. subst. rewrite eq_dec_if_true by reflexivity.
            simpl in *. rewrite Ht''.
            f_equal.
            apply functional_extensionality_dep_good.
            intro eqvi.
            destruct (decide (eqvi = eqv)).
            *** subst. repeat rewrite state_update_eq. reflexivity.
            *** repeat rewrite state_update_neq by  assumption.
              unfold  Common.equivocators_state_project.
              destruct (decide (eqvi = eqv)); [congruence|].
              rewrite equivocators_choice_update_neq; congruence.
        --- eexists _. eexists _. exists eq_refl.
          assert
            (Hfinal' :
              equivocators_state_project final_choice
                (last (map destination tr)
                   (state_update (Common.equivocator_IM IM) is
                      (eqv)
                      (existT (fun n0 : nat => t (S n0) -> vstate (IM (eqv)))
                         nsi' bsi'))) =
              last (map destination trX')
                (equivocators_state_project
                   (equivocators_choice_update initial_choice' eqv
                      (Existing (IM (eqv)) ieqv false)) is)
            ).
          { subst bsi'. simpl in *. rewrite Hfinal.
            rewrite (equivocators_state_project_state_update_eqv IM i0).
            rewrite Heqv.
            unfold projT1. unfold projT2.
            f_equal.
            apply functional_extensionality_dep_good.
            destruct (le_lt_dec (S nsi') ieqv); [lia|].
            destruct (eq_dec (of_nat_lt Hidi) (of_nat_lt l0))
            ; [apply (f_equal to_nat) in e; repeat rewrite to_nat_of_nat in e; congruence|].
            intro i'. destruct (decide (i' = (eqv))).
            - subst. rewrite state_update_eq.
              unfold equivocators_state_project.
              unfold Common.equivocators_state_project.
              unfold equivocators_choice_update.
              rewrite equivocators_choice_update_eq.
              rewrite Hiseqv.
              destruct (le_lt_dec (S nsi') ieqv); [lia|].
              f_equal. apply of_nat_ext.
            - rewrite state_update_neq by assumption.
              unfold equivocators_state_project.
              unfold Common.equivocators_state_project.
              unfold equivocators_choice_update.
              rewrite equivocators_choice_update_neq; congruence.
          }
          exists Hfinal'.
          assert
            (Hproper'' :
            proper_equivocators_choice
              (equivocators_choice_update initial_choice' eqv
                 (Existing (IM (eqv)) ieqv false)) is).
          { intro eqv'. spec Hproper' eqv'.
            unfold equivocators_choice_update.
            destruct (decide (eqv' = eqv)).
            - subst. rewrite state_update_eq in Hproper'.
              rewrite equivocators_choice_update_eq.
              rewrite Heqv in Hproper'.
              simpl in *.
              rewrite Hiseqv. simpl. lia.
            - rewrite state_update_neq in Hproper' by congruence.
              rewrite equivocators_choice_update_neq; assumption.
          }
          exists Hproper''.
          replace
            (equivocators_state_project
            (equivocators_choice_update initial_choice' eqv
               (Existing (IM (eqv)) ieqv false)) is)
            with
            (equivocators_state_project initial_choice'
            (state_update (Common.equivocator_IM IM) is
               (eqv)
               (existT (fun n : nat => t (S n) -> vstate (IM (eqv)))
                  nsi' bsi')))
          ; [assumption|].
          unfold equivocators_state_project.
          rewrite equivocators_state_project_state_update_eqv.
          rewrite Heqv. unfold projT1. unfold projT2.
          destruct (le_lt_dec (S nsi') ieqv); [lia|].
          replace (of_nat_lt l0) with (of_nat_lt Hproper_eqv) in * by apply of_nat_ext.
          clear l0.
          apply functional_extensionality_dep_good.
          intro i.
          destruct (decide (i = eqv)).
          +++ subst. rewrite state_update_eq.
            rewrite eq_dec_if_false.
            *** unfold Common.equivocators_state_project.
              unfold equivocators_choice_update.
              rewrite equivocators_choice_update_eq.
              rewrite Hiseqv.
              destruct (le_lt_dec (S nsi') ieqv); [lia|].
              f_equal. apply of_nat_ext.
            *** intro contra. elim n. apply (f_equal to_nat) in contra.
              repeat rewrite to_nat_of_nat in contra. inversion contra. reflexivity.
          +++ rewrite state_update_neq by assumption.
            unfold  Common.equivocators_state_project.
            unfold equivocators_choice_update.
            rewrite equivocators_choice_update_neq; congruence.
Qed.

End equivocators_composition_projections.
