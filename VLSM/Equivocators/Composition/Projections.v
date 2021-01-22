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
    VLSM.Common VLSM.Composition VLSM.ProjectionTraces VLSM.Equivocation
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
  {i0 : Inhabited index}
  (X := free_composite_vlsm IM)
  {index_listing : list index}
  (finite_index : Listing index_listing)
  (equivocators_choice := equivocators_choice IM)
  (equivocators_no_equivocations_vlsm := equivocators_no_equivocations_vlsm IM Hbs finite_index)
  (equivocators_state_project := equivocators_state_project IM)
  (equivocator_IM := equivocator_IM IM)
  (equivocators_choice_update := equivocators_choice_update IM)
  (proper_equivocators_choice := proper_equivocators_choice IM)
  .

Definition equivocators_transition_item_project
  (eqv_choice : equivocators_choice)
  (item : composite_transition_item equivocator_IM)
  : option (option (composite_transition_item IM) * equivocators_choice)
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
  (item : composite_transition_item equivocator_IM)
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

Local Tactic Notation "unfold_transition"  hyp(Ht) :=
  ( unfold transition in Ht; unfold equivocator_IM in Ht; unfold Common.equivocator_IM in Ht;
  unfold equivocator_vlsm in Ht; unfold mk_vlsm in Ht;
  unfold machine in Ht; unfold projT2 in Ht;
  unfold equivocator_vlsm_machine in Ht; unfold equivocator_transition in Ht).

Lemma equivocators_transition_item_project_proper_characterization
  (eqv_choice : equivocators_choice)
  (item : composite_transition_item equivocator_IM)
  (Hproper : proper_equivocators_choice eqv_choice (destination item))
  : exists oitem eqv_choice',
    equivocators_transition_item_project eqv_choice item = Some (oitem, eqv_choice')
    /\ forall
      (s : composite_state equivocator_IM)
      (Hv : free_composite_valid equivocator_IM (l item) (s, input item))
      (Ht : composite_transition equivocator_IM (l item) (s, input item) = (destination item, output item)),
      proper_equivocators_choice eqv_choice' s /\
      match oitem with
      | Some itemx =>
        existT _ (projT1 (l item)) (fst (projT2 (l item))) = l itemx /\  input item = input itemx /\ output item = output itemx /\
        (equivocators_state_project eqv_choice (destination item) = destination itemx) /\
        forall (sx : composite_state IM)
          (Hsx : sx = equivocators_state_project eqv_choice' s),
          free_composite_valid IM (l itemx) (sx, input itemx) /\
          composite_transition IM (l itemx) (sx, input itemx) = (destination itemx, output itemx)
      | None => 
        equivocators_state_project eqv_choice (destination item) = equivocators_state_project eqv_choice' s
      end.
Proof.
  destruct item. simpl.
  destruct l as [i v].
  specialize (Hproper i) as Hi. simpl in Hi.
  unfold equivocator_vlsm_transition_item_project.
  destruct (eqv_choice i) eqn:Heqvi.
  - exists None. eexists _. split; [reflexivity|].
    intros.
    apply and_comm. split.
    { unfold equivocators_choice_update.
      rewrite equivocators_choice_update_id; [|assumption].
      apply
        (new_machine_reflects_equivocators_state_project IM (existT _ i v) s input destination output Ht _ _ Heqvi).
    }
    intro eqv.
    unfold equivocators_choice_update.
    destruct (decide (eqv = i)).
    + subst i. 
      rewrite equivocators_choice_update_eq. assumption.
    + rewrite equivocators_choice_update_neq; [|assumption].
      specialize (Hproper eqv). simpl in Hproper.
      destruct (vtransition (equivocator_IM i) v (s i, input)) as (si', om').
      inversion Ht. subst. clear Ht.
      rewrite state_update_neq in Hproper; assumption.
  - destruct v as (li, eqvi).
    simpl in Hproper.
    destruct (destination i) as (ni, bsi) eqn:Hdesti.
    simpl in Hi.
    destruct (le_lt_dec (S ni) n); [lia|].
    destruct eqvi as [nsi | ieqvi feqvi].
    + destruct (nat_eq_dec (S n) (S ni)).
      * exists None. eexists _. split; [reflexivity|].
        intros.
        apply and_comm.
        split.
        { specialize
          (new_machine_label_equivocators_state_project_last IM  (existT _ i ((li, NewMachine (IM i) nsi))) s input destination output Ht nsi eq_refl eqv_choice b)
          as Hnew.
          spec Hnew.
          { simpl. rewrite Hdesti, Heqvi. simpl. inversion e. reflexivity. }
          assumption.
        }
        intro eqv.
        destruct Hv as [Heqv Hv].
        unfold equivocators_choice_update.
        destruct (decide (eqv = i)).
        -- subst i. 
          rewrite equivocators_choice_update_eq. assumption.
        -- rewrite equivocators_choice_update_neq; [|assumption].
          specialize (Hproper eqv). simpl in Hproper.
          simpl in Ht. inversion Ht. subst. clear Ht.
          rewrite state_update_neq in Hproper; assumption.
      * exists None. eexists _. split; [reflexivity|]. 
        intros.
        apply and_comm.
        split.
        { specialize
          (new_machine_label_equivocators_state_project_not_last IM  (existT _ i ((li, NewMachine (IM i) nsi))) s input destination output Ht nsi eq_refl
            eqv_choice _ _ Heqvi)
          as Hnew.
          spec Hnew.
          { simpl. rewrite Hdesti. simpl. lia. }
          apply Hnew.
        }
        intro eqv.
        destruct Hv as [Heqv Hv].
        unfold equivocators_choice_update.
        destruct (decide (eqv = i)).
        -- subst i. 
          rewrite equivocators_choice_update_eq. simpl.
          simpl in Ht. inversion Ht. subst. clear Ht.
          rewrite state_update_eq in Hdesti.
          destruct (s eqv) as (neqv, seqv). simpl in *.
          inversion Hdesti. subst ni. lia.
        -- rewrite equivocators_choice_update_neq; [|assumption].
          specialize (Hproper eqv). simpl in Hproper.
          simpl in Ht. inversion Ht. subst. clear Ht.
          rewrite state_update_neq in Hproper; assumption.
    + destruct feqvi; [destruct (nat_eq_dec (S n) (S ni))|destruct (nat_eq_dec ieqvi n)].
      * inversion e. subst ni. clear e.
        simpl. eexists _. eexists _. split; [reflexivity|].
        intros.
        destruct Hv as [Heqv Hv].
        unfold equivocators_choice_update.
        split.
        -- intros eqv.
          destruct (decide (eqv = i)).
          ++ subst i. 
            rewrite equivocators_choice_update_eq. simpl. assumption.
          ++ rewrite equivocators_choice_update_neq; [|assumption].
            specialize (Hproper eqv). simpl in Hproper.
            destruct (vtransition (equivocator_IM i) (li, Existing (IM i) ieqvi true) (s i, input))
              as (si', om').
            inversion Ht. subst. clear Ht.
            rewrite state_update_neq in Hproper; assumption.
        -- intros.
          simpl. repeat (split; [reflexivity|]).
          intros.
          unfold equivocators_state_project in Hsx.
          destruct (vtransition (equivocator_IM i) (li, Existing (IM i) ieqvi true) (s i, input))
            as (si', om') eqn:Ht'.
          inversion Ht. subst om' destination. clear Ht.
          rewrite state_update_eq in Hdesti.
          unfold fst in Hv.
          unfold vvalid in Hv.
          unfold vtransition in Ht'.
          unfold_transition Ht'. unfold snd in Ht'.
          destruct (le_lt_dec (S (projT1 (s i))) ieqvi); [lia|].
          replace (of_nat_lt l0) with (of_nat_lt Heqv) in * by apply of_nat_ext.
          clear l0.
          assert (Hsxi : sx i = projT2 (s i) (Fin2Restrict.n2f Heqv)).
          { subst. unfold Common.equivocators_state_project.
            rewrite equivocators_choice_update_eq.
            destruct (s i) as (nsi, si). unfold projT2.
            simpl in Heqv.
            destruct (le_lt_dec (S nsi) ieqvi); [lia|].
            f_equal. apply of_nat_ext.
          }
          rewrite Hsxi. split; [assumption|].
          simpl in *.
          destruct (vtransition (IM i) li (projT2 (s i) (Fin2Restrict.n2f Heqv), input))
            as (si'', om') eqn:Ht''.
          inversion Ht'.
          f_equal.
          unfold equivocators_state_project.
          unfold equivocator_IM.
          rewrite equivocators_state_project_state_update_eqv.
          rewrite Heqvi.
          apply functional_extensionality_dep.
          intro eqv.
          destruct (decide (eqv = i)).
          ++ subst eqv. repeat rewrite state_update_eq.
            rewrite H0. clear Ht'.
            specialize (Hproper i). rewrite Heqvi in Hproper.
            simpl in Hproper. rewrite state_update_eq in Hproper.
            destruct (le_lt_dec (S (projT1 si')) n); [lia|].
            revert l0.
            rewrite <- H0. intro l0.
            assert (Hn : n  = S (projT1 (s i))).
            {
              rewrite Hdesti in H0.
              destruct (s i) as (nsi, si) eqn:Hsi.
              simpl.
              unfold equivocator_state_extend in H0.
              inversion H0. reflexivity.
            }
            subst n.
            specialize
              (equivocator_state_extend_project_last (IM i) (s i) si'').
            revert l0.
            rewrite H0. clear H0. subst si'. simpl. intros.
            symmetry. apply H.
          ++ repeat (rewrite state_update_neq; [|assumption]).
            subst sx.
            unfold Common.equivocators_state_project at 1.
            rewrite equivocators_choice_update_neq; [|assumption].
            reflexivity.
      * simpl. eexists _. eexists _. split; [reflexivity|].
        intros.
        apply and_comm.
        split.
        { specialize
            (existing_true_label_equivocators_state_project_not_last IM  (existT _ i ((li, Existing (IM i) ieqvi true))) s input destination output Ht _ eq_refl )
            as Hex.
          destruct Hv as [Hieqvi Hv].
          specialize (Hex Hieqvi eqv_choice _ _ Heqvi).
          spec Hex.
          { simpl. rewrite Hdesti. simpl. lia. }
          apply Hex.
        }
        intro eqv.
        destruct Hv as [Heqv Hv].
        unfold equivocators_choice_update.
        destruct (decide (eqv = i)).
        -- subst i. 
          rewrite equivocators_choice_update_eq. simpl.
          destruct (vtransition (equivocator_IM eqv) (li, Existing (IM eqv) ieqvi true) (s eqv, input))
            as (si', om') eqn:Ht'.
          inversion Ht. subst. clear Ht.
          rewrite state_update_eq in Hdesti.
          subst si'.
          simpl in Ht'. unfold vtransition in Ht'.
          unfold transition in Ht'. unfold equivocator_IM in Ht'.  unfold Common.equivocator_IM in Ht'.
          unfold equivocator_vlsm in Ht'. unfold mk_vlsm in Ht'.
          unfold machine in Ht'. unfold projT2 in Ht'.
          unfold equivocator_vlsm_machine in Ht'. unfold equivocator_transition in Ht'.
          unfold snd in Ht'.
          destruct (le_lt_dec (S (projT1 (s eqv))) ieqvi); [lia|].
          destruct (vtransition (IM eqv) (fst (li, Existing (IM eqv) ieqvi true))
          (projT2 (s eqv) (Fin2Restrict.n2f l0), input))
            as (si', om').
          inversion Ht'. subst.
          destruct (s eqv) as (neqv, seqv). simpl in *.
          inversion H0. subst ni. lia.
        -- rewrite equivocators_choice_update_neq; [|assumption].
          specialize (Hproper eqv). simpl in Hproper.
          destruct (vtransition (equivocator_IM i) (li, Existing (IM i) ieqvi true) (s i, input))
            as (si', om').
          inversion Ht. subst. clear Ht.
          rewrite state_update_neq in Hproper; assumption.
      * subst ieqvi.
        simpl. eexists _. eexists _. split; [reflexivity|].
        intros.
        destruct Hv as [Heqv Hv].
        unfold equivocators_choice_update.
        split.
        -- intro eqv. destruct (decide (eqv = i)).
          ++ subst i. 
            rewrite equivocators_choice_update_eq. simpl. assumption.
          ++ rewrite equivocators_choice_update_neq; [|assumption].
            specialize (Hproper eqv). simpl in Hproper.
            destruct (vtransition (equivocator_IM i) (li, Existing (IM i) n false) (s i, input))
              as (si', om').
            inversion Ht. subst. clear Ht.
            rewrite state_update_neq in Hproper; assumption.
        -- intros.
          simpl. repeat (split; [reflexivity|]).
          intros.
          unfold equivocators_state_project in Hsx.
          destruct (vtransition (equivocator_IM i) (li, Existing (IM i) n false)
          (s i, input))
            as (si', om') eqn:Ht'.
          inversion Ht. subst om' destination. clear Ht.
          rewrite state_update_eq in Hdesti.
          subst si'.
          unfold fst in Hv.
          unfold vvalid in Hv.
          unfold vtransition in Ht'.
          unfold_transition Ht'. unfold snd in Ht'.
          destruct (le_lt_dec (S (projT1 (s i))) n); [lia|].
          replace (of_nat_lt l0) with (of_nat_lt Heqv) in * by apply of_nat_ext.
          clear l0.
          assert (Hsxi : sx i = projT2 (s i) (Fin2Restrict.n2f Heqv)).
          { subst. unfold Common.equivocators_state_project.
            rewrite equivocators_choice_update_eq.
            destruct (s i) as (nsi, si). unfold projT2.
            simpl in Heqv.
            destruct (le_lt_dec (S nsi) n); [lia|].
            f_equal. apply of_nat_ext.
          }
          rewrite Hsxi. split; [assumption|].
          simpl in *.
          destruct (vtransition (IM i) li (projT2 (s i) (Fin2Restrict.n2f Heqv), input))
            as (si'', om') eqn:Ht''.
          inversion Ht'. clear Ht'. subst ni.
          simpl_existT. subst bsi.
          f_equal.
          unfold equivocators_state_project.
          unfold equivocator_IM.
          rewrite equivocators_state_project_state_update_eqv.
          rewrite Heqvi.
          unfold projT1 at 1. unfold projT2.
          destruct (le_lt_dec (S (projT1 (s i))) n); [lia|].
          apply functional_extensionality_dep.
          intro eqv.
          destruct (decide (eqv = i)).
          ++  subst eqv. repeat rewrite state_update_eq.
            rewrite eq_dec_if_true; [reflexivity|].
            apply of_nat_ext.
          ++ repeat (rewrite state_update_neq; [|assumption]).
            subst sx.
            unfold Common.equivocators_state_project at 1.
            rewrite equivocators_choice_update_neq; [|assumption].
            reflexivity.
      * simpl. eexists _. eexists _. split; [reflexivity|].
        intros.
        apply and_comm.
        split.
        { specialize
            (existing_false_label_equivocators_state_project_not_same IM  (existT _ i ((li, Existing (IM i) ieqvi false))) s input destination output Ht _ eq_refl )
            as Hex.
          destruct Hv as [Hieqvi Hv].
          specialize (Hex Hieqvi eqv_choice _ _ Heqvi).
          spec Hex.
          { simpl. rewrite Hdesti. simpl. lia. }
          apply Hex. assumption.
        }
        intro eqv.
        destruct Hv as [Heqv Hv].
        unfold equivocators_choice_update.
        destruct (decide (eqv = i)).
        -- subst i. 
          rewrite equivocators_choice_update_eq. simpl.
          destruct (vtransition (equivocator_IM eqv) (li, Existing (IM eqv) ieqvi false)
          (s eqv, input))
            as (si', om') eqn:Ht'.
          inversion Ht. subst. clear Ht.
          rewrite state_update_eq in Hdesti.
          subst si'.
          simpl in Ht'. unfold vtransition in Ht'.
          unfold transition in Ht'. unfold equivocator_IM in Ht'.  unfold Common.equivocator_IM in Ht'.
          unfold equivocator_vlsm in Ht'. unfold mk_vlsm in Ht'.
          unfold machine in Ht'. unfold projT2 in Ht'.
          unfold equivocator_vlsm_machine in Ht'. unfold equivocator_transition in Ht'.
          unfold snd in Ht'.
          destruct (le_lt_dec (S (projT1 (s eqv))) ieqvi); [lia|].
          destruct (vtransition (IM eqv) (fst (li, Existing (IM eqv) ieqvi false))
          (projT2 (s eqv) (Fin2Restrict.n2f l0), input))
            as (si', om').
          apply pair_equal_spec in Ht'. destruct Ht' as [Hseqv Hom'].
          unfold equivocator_state_update in Hseqv.
          inversion Hseqv.
          lia.
        -- rewrite equivocators_choice_update_neq; [|assumption].
          specialize (Hproper eqv). simpl in Hproper.
          destruct (vtransition (equivocator_IM i) (li, Existing (IM i) ieqvi false)
          (s i, input))
            as (si', om').
          inversion Ht. subst. clear Ht.
          rewrite state_update_neq in Hproper; assumption.
Qed.

Definition equivocators_trace_project_folder
  (item : composite_transition_item equivocator_IM)
  (result: option (list (composite_transition_item IM) * equivocators_choice))
  : option (list (composite_transition_item IM) * equivocators_choice)
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
  (tr : list (composite_transition_item equivocator_IM))
  : fold_right equivocators_trace_project_folder None tr = None.
Proof.
  induction tr; [reflexivity|]. simpl. rewrite IHtr. reflexivity.
Qed.

Lemma equivocators_trace_project_folder_additive
  (tr : list (composite_transition_item equivocator_IM))
  (itrX trX : list (composite_transition_item IM))
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
  (tr : list (composite_transition_item equivocator_IM))
  : option (list (composite_transition_item IM) * equivocators_choice)
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
  (tr : list (composite_transition_item equivocator_IM))
  (final_state := last (map destination tr) is)
  (Hproper : proper_equivocators_choice final_choice final_state)
  (Htr : finite_protocol_trace_from equivocators_no_equivocations_vlsm is tr)
  : exists
    (trX : list (composite_transition_item IM))
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
  induction tr using rev_ind; intros.
  - exists []. simpl. exists final_choice.
    exists eq_refl. exists eq_refl. exists Hproper.
    constructor.
    inversion Htr. subst. destruct H as [_om His].
    apply (proj2 (equivocators_protocol_state_project IM Hbs _ _ _ His) final_choice Hproper).
  - apply finite_protocol_trace_from_app_iff in Htr.
    destruct Htr as [Htr Hinit].
    specialize (IHtr _ Htr).
    specialize (equivocators_transition_item_project_proper_characterization final_choice x) as Hproperx.
    unfold final_state in Hproper.
    rewrite map_app in Hproper. simpl in Hproper. rewrite last_is_last in Hproper.
    spec Hproperx Hproper.
    destruct Hproperx as [oitem [final_choice' [Hprojectx Hproperx]]].
    specialize (Hproperx (last (map destination tr) is)).
    unfold equivocators_trace_project.
    rewrite fold_right_app.
    match goal with
    |- context [fold_right _ ?fld _] => remember fld as foldx
    end.
    simpl in Heqfoldx.
    rewrite Hprojectx in Heqfoldx.
    inversion Hinit. subst tl s' x.
    destruct H3 as [[Hs [Hiom [Hv _]]] Ht].
    specialize (Hproperx Hv Ht). clear Hv Ht.
    destruct Hproperx as [Hproper' Hx].
    specialize (IHtr _ Hproper').
    destruct IHtr as [trX' [initial_choice [Htr_project [Hstate_project [Hproper_initial HtrX']]]]].
    destruct oitem as [item|].
    + destruct Hx as [Hl [Hinput [Houtput [Hdestination Hx]]]].
      simpl in Hl, Hinput, Houtput, Hdestination.
      specialize (Hx _ eq_refl).
      destruct Hx as [Hvx Htx].
      exists (trX' ++ [item]), initial_choice. subst foldx.
      rewrite equivocators_trace_project_folder_additive with (trX := trX') (eqv_choice := initial_choice)
      ; [|assumption].
      exists eq_refl.
      rewrite map_app. simpl. rewrite last_is_last.
      unfold final_state. rewrite map_app. simpl. rewrite last_is_last.
      exists Hdestination.
      exists Hproper_initial.
      apply finite_protocol_trace_from_app_iff.
      split; [assumption|].
      change [item] with ([] ++ [item]).
      match goal with
      |- finite_protocol_trace_from _ ?l _ => remember l as lst
      end.
      destruct item.
      assert (Hlst : protocol_state_prop X lst).
      { apply finite_ptrace_last_pstate in HtrX'. subst. assumption. }
      apply (extend_right_finite_trace_from X lst []); [constructor; assumption|].
      simpl in Hl. subst. 
      split.
      * split; [assumption|].
        unfold Common.input in Hiom.
        destruct Hiom as [_s Hiom].
        apply equivocators_protocol_state_project in Hiom.
        destruct Hiom as [Hiom _].
        split; [assumption|].
        split; [|exact I].
        clear -Hvx Hstate_project. simpl in Hvx. simpl in Hstate_project.
        rewrite Hstate_project in Hvx.
        simpl. assumption.
      * simpl. simpl in Htx, Hstate_project.
        rewrite Hstate_project in Htx.
        assumption. 
    + exists trX'. exists initial_choice. subst foldx. exists Htr_project.
      repeat split; [| assumption | assumption].
      clear -Hstate_project Hx. rewrite Hstate_project in Hx.
      rewrite <- Hx. f_equal. unfold final_state.
      rewrite map_app. simpl. rewrite last_is_last. reflexivity.
Qed.

Lemma equivocators_trace_project_finite_trace_projection_list_commute
  (i : index)
  (final_choice initial_choice : equivocators_choice)
  (eqv_final eqv_initial : MachineDescriptor (IM i))
  (tr : list (composite_transition_item equivocator_IM))
  (trX : list (composite_transition_item IM))
  (trXi : list (vtransition_item (IM i)))
  (Hfinali : final_choice i = eqv_final)
  (Hproject_tr : equivocators_trace_project final_choice tr = Some (trX, initial_choice))
  (Hproject_tri :
    equivocator_vlsm_trace_project (IM i)
      (finite_trace_projection_list equivocator_IM i tr) eqv_final
    = Some (trXi, eqv_initial))
  : initial_choice i = eqv_initial /\
    finite_trace_projection_list IM i trX = trXi.
Proof.
  revert Hfinali.
  generalize dependent trXi. generalize dependent trX.
  generalize dependent final_choice. revert eqv_final.
  induction tr using rev_ind; intros.
  - simpl in Hproject_tr. inversion Hproject_tr. subst.
    clear Hproject_tr.
    simpl in Hproject_tri.
    inversion Hproject_tri. subst. split; reflexivity.
  - unfold equivocators_trace_project in Hproject_tr.
    rewrite fold_right_app in Hproject_tr.
    match type of Hproject_tr with
    | fold_right _ ?i _ = _ => remember i as project_x
    end.
    destruct project_x as [(projectx,final_choice')|]
    ; [|rewrite equivocators_trace_project_fold_None in Hproject_tr; inversion Hproject_tr].
    simpl in Heqproject_x.
    destruct (equivocators_transition_item_project final_choice x)
      as [(o, descriptor)|] eqn:Hproject_x
    ; [| inversion Heqproject_x].
    rewrite finite_trace_projection_list_app in Hproject_tri.
    apply equivocator_vlsm_trace_project_app in Hproject_tri.
    destruct Hproject_tri as [eqv_final' [trXi' [trXi_x [HtrXi' [HtrXi_x HeqtrXi]]]]].
    specialize (IHtr eqv_final' final_choice').
    unfold equivocator_vlsm_trace_project in Hproject_tri.
    simpl in Hproject_tri.
    specialize (equivocators_trace_project_folder_additive .
    rewrite equivocators_trace_project_folder_additive in Hproject_tr.

Lemma equivocators_trace_project_output_reflecting_inv
  (is: composite_state equivocator_IM)
  (tr: list (composite_transition_item equivocator_IM))
  (Htr: finite_protocol_trace_from (pre_loaded_with_all_messages_vlsm (free_composite_vlsm equivocator_IM)) is tr)
  (m : message)
  (Hbbs : Exists (field_selector output m) tr)
  : exists
    (final_choice initial_choice : equivocators_choice)
    (trX: list (composite_transition_item IM)),
    equivocators_trace_project final_choice tr = Some (trX, initial_choice) /\
    Exists (field_selector output m) trX.
Proof.
  apply Exists_exists in Hbbs.
  destruct Hbbs as [item [Hitem Hm]]. simpl in Hm.
  apply (finite_trace_projection_list_in  equivocator_IM (free_constraint equivocator_IM)) in Hitem.
  destruct item. simpl in *. destruct l as (i, li). simpl in *.
  specialize
    (preloaded_finite_ptrace_projection equivocator_IM (free_constraint equivocator_IM) i _ _ Htr)
    as Htri.
  specialize
    (equivocator_vlsm_trace_project_output_reflecting_inv (IM i) _ _ Htri m) as Hex.
  spec Hex.
  { apply Exists_exists. eexists _. split;[exact Hitem|].
    subst. reflexivity.
  }
  destruct Hex as [eqv_final [eqv_init [trXi [Hprojecti Hex]]]].
Admitted.

End equivocators_composition_projections.
