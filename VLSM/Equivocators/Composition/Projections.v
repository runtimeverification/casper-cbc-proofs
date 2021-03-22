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
    VLSM.Common VLSM.Composition VLSM.ProjectionTraces VLSM.SubProjectionTraces
    VLSM.Equivocation
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
  (equivocator_descriptors := equivocator_descriptors IM)
  (equivocators_no_equivocations_vlsm := equivocators_no_equivocations_vlsm IM Hbs finite_index)
  (equivocators_state_project := equivocators_state_project IM)
  (equivocator_IM := equivocator_IM IM)
  (equivocator_descriptors_update := equivocator_descriptors_update IM)
  (proper_equivocator_descriptors := proper_equivocator_descriptors IM)
  (equivocators_free_vlsm := free_composite_vlsm equivocator_IM)
  (pre_loaded_equivocators := pre_loaded_with_all_messages_vlsm equivocators_free_vlsm)
  (equivocators_free_Hbs : has_been_sent_capability equivocators_free_vlsm := composite_has_been_sent_capability equivocator_IM (free_constraint equivocator_IM) finite_index (equivocator_Hbs IM Hbs))
  .

Existing Instance equivocators_free_Hbs.

Definition equivocators_transition_item_project
  (eqv_descriptors : equivocator_descriptors)
  (item : composite_transition_item equivocator_IM)
  : option (option (composite_transition_item IM) * equivocator_descriptors)
  :=
  let sx := equivocators_state_project eqv_descriptors (destination item) in
  let eqv := projT1 (l item) in
  let deqv := eqv_descriptors eqv in
  match
    equivocator_vlsm_transition_item_project
      (IM eqv)
      (composite_transition_item_projection equivocator_IM item)
      deqv
      with
  | Some (Some item', deqv') =>
    Some
      (Some (@Build_transition_item message (@type message X)
        (existT (fun n : index => vlabel (IM n)) eqv (l item'))
        (input item) sx (output item))
      , equivocator_descriptors_update eqv_descriptors eqv deqv')
  | Some (None, deqv') => Some (None, equivocator_descriptors_update eqv_descriptors eqv deqv')
  | None => None
  end.

(**
[zero_descriptor]s are preserved when projecting [transition_item]s of the
composition of equivocators.
*)
Lemma equivocators_transition_item_project_preserves_zero_descriptors
  (descriptors : equivocator_descriptors)
  (item : composite_transition_item equivocator_IM)
  oitem idescriptors
  s
  (Ht : composite_transition equivocator_IM (l item) (s, input item) = (destination item, output item))
  (Hv : composite_valid equivocator_IM (l item) (s, input item))
  (Hpr : equivocators_transition_item_project descriptors item = Some (oitem, idescriptors))
  : forall i, descriptors i = Existing _ 0 false -> idescriptors i = Existing _ 0 false.
Proof.
  intros i Hi.
  unfold equivocators_transition_item_project in Hpr.
  destruct (decide (i = projT1 (l item))).
  -  subst i. rewrite Hi in Hpr.
    specialize
      (equivocators_vlsm_transition_item_project_zero_descriptor (IM (projT1 (l item)))
        (composite_transition_item_projection equivocator_IM item)
        (s (projT1 (l item)))
      ) as Hpr_item.
    remember (composite_transition_item_projection equivocator_IM item) as pr_item.
    spec Hpr_item.
    {
      clear -Ht Heqpr_item.
      destruct item. simpl in *.
      destruct l as (i, li).
      unfold projT1 .
      match type of Ht with
      | (let (_, _) := ?t in _) = _ => destruct t as (si', om') eqn:Hti
      end.
      inversion Ht. subst. simpl.
      unfold eq_rect_r. simpl.
      rewrite state_update_eq. assumption.
    }
    spec Hpr_item.
    {
      clear -Hv Heqpr_item.
      destruct item. simpl in *.
      destruct l as (i, li).
      unfold projT1 .
      subst. simpl.
      unfold eq_rect_r. simpl. assumption.
    }
    destruct Hpr_item as [oitem' Hpr_item].
    rewrite Hpr_item in Hpr.
    destruct oitem'; inversion Hpr
    ; unfold equivocator_descriptors_update; rewrite equivocator_descriptors_update_eq; reflexivity.
  -
  destruct
    (equivocator_vlsm_transition_item_project (IM (projT1 (l item)))
      (composite_transition_item_projection equivocator_IM item)
      (descriptors (projT1 (l item))))
    eqn: Hpr'; [|congruence].
  destruct p.
  destruct o; inversion Hpr
  ; unfold equivocator_descriptors_update; rewrite equivocator_descriptors_update_neq; assumption.
Qed.

Lemma equivocators_transition_item_project_proper_descriptor
  (eqv_descriptors : equivocator_descriptors)
  (item : composite_transition_item equivocator_IM)
  (i := projT1 (l item))
  (Hproper : proper_descriptor (IM i) (eqv_descriptors i) (destination item i))
  : equivocators_transition_item_project eqv_descriptors item <> None.
Proof.
  unfold equivocators_transition_item_project.
  intro contra.
  elim
    (equivocator_transition_item_project_proper (IM (projT1 (l item)))
      (composite_transition_item_projection equivocator_IM item)
      (eqv_descriptors (projT1 (l item))) Hproper).
  destruct
    (equivocator_vlsm_transition_item_project (IM (projT1 (l item)))
    (composite_transition_item_projection equivocator_IM item)
    (eqv_descriptors (projT1 (l item))))
  ; [|reflexivity].
  destruct p. destruct o; congruence.
Qed.

Lemma equivocators_transition_item_project_proper
  (eqv_descriptors : equivocator_descriptors)
  (item : composite_transition_item equivocator_IM)
  (Hproper : proper_equivocator_descriptors eqv_descriptors (destination item))
  : equivocators_transition_item_project eqv_descriptors item <> None.
Proof.
  apply equivocators_transition_item_project_proper_descriptor.
  apply Hproper.
Qed.

(**
A generalization of [no_equivocating_equivocator_transition_item_project] to
the composition of equivocators.
*)
Lemma no_equivocating_equivocators_transition_item_project
  (eqv_descriptors : equivocator_descriptors)
  (item : composite_transition_item equivocator_IM)
  (i := projT1 (l item))
  (Hzero : (eqv_descriptors i) = Existing _ 0 false)
  (Hdest_i : is_singleton_state (IM i) (destination item i))
  (s : composite_state equivocator_IM)
  (Hv : composite_valid equivocator_IM (l item) (s, input item))
  (Ht : composite_transition equivocator_IM (l item) (s, input item) = (destination item, output item))
  (lx : composite_label IM :=  existT (fun i => vlabel (IM i)) i (fst (projT2 (l item))))
  : equivocators_transition_item_project eqv_descriptors item =
    Some (Some
      {| l := lx; input := input item; output := output item;
        destination := equivocators_state_project eqv_descriptors (destination item) |},
      eqv_descriptors).
Proof.
  specialize
    (no_equivocating_equivocator_transition_item_project (IM i)
      (composite_transition_item_projection equivocator_IM item)
      Hdest_i
      (s i)
    ) as Heqv_pr.
  destruct item, l. simpl in Ht, Hv. simpl in i. subst i.
  specialize (Heqv_pr Hv).
  spec Heqv_pr.
  { simpl. unfold eq_rect_r. simpl.
    destruct (vtransition (equivocator_IM x) v (s x, input)) eqn:Hti.
    clear -Ht Hti.
    inversion Ht. rewrite state_update_eq. subst. assumption.
  }
  unfold equivocators_transition_item_project.
  unfold l. unfold projT1.
  rewrite Hzero.
  rewrite Heqv_pr.
  repeat f_equal.
  apply equivocator_descriptors_update_id.
  assumption.
Qed.

Lemma equivocators_transition_item_project_proper_descriptor_characterization
  (eqv_descriptors : equivocator_descriptors)
  (item : composite_transition_item equivocator_IM)
  (i := projT1 (l item))
  (Hproper : proper_descriptor (IM i) (eqv_descriptors i) (destination item i))
  : exists oitem eqv_descriptors',
    equivocators_transition_item_project eqv_descriptors item = Some (oitem, eqv_descriptors')
    /\ match oitem with
      | Some itemx =>
        existT _ i (fst (projT2 (l item))) = l itemx /\  input item = input itemx /\ output item = output itemx /\
        (equivocators_state_project eqv_descriptors (destination item) = destination itemx)
      | None => True
      end
    /\ forall
      (s : composite_state equivocator_IM)
      (Hv : composite_valid equivocator_IM (l item) (s, input item))
      (Ht : composite_transition equivocator_IM (l item) (s, input item) = (destination item, output item)),
      proper_descriptor (IM i) (eqv_descriptors' i) (s i) /\
      eqv_descriptors' = equivocator_descriptors_update eqv_descriptors i (eqv_descriptors' i) /\
      s = state_update equivocator_IM (destination item) i (s i) /\
      match oitem with
      | Some itemx =>
        forall (sx : composite_state IM)
          (Hsx : sx = equivocators_state_project eqv_descriptors' s),
          composite_valid IM (l itemx) (sx, input itemx) /\
          composite_transition IM (l itemx) (sx, input itemx) = (destination itemx, output itemx)
      | None =>
        equivocators_state_project eqv_descriptors (destination item) = equivocators_state_project eqv_descriptors' s
      end.
Proof.
  destruct
    (equivocator_transition_item_project_proper_characterization (IM i)
      (composite_transition_item_projection equivocator_IM item)
      (eqv_descriptors i) Hproper)
    as [oitemi [eqv_descriptorsi' [Hoitemi [Hitemx H]]]].
  unfold i in *. clear i.
  unfold equivocators_transition_item_project.
  rewrite Hoitemi. clear Hoitemi.
  destruct item. simpl in *. destruct l as (i, li). simpl in *.
  destruct oitemi as [itemi'|]; eexists _; eexists _; (split; [reflexivity|])
  ; destruct li as (li, di); simpl in *;
  [ destruct Hitemx as [Hli [Hinputi [Houtputi Hdestinationi]]]
  ; rewrite Hli; subst; split; [repeat split|]
  | split; [exact I|]]
  ; intros
  ; match type of Ht with
    | (let (_, _) := ?t in _ ) = _ =>
      destruct t as (si', om') eqn:Ht'
    end
  ; inversion Ht; subst; clear Ht
  ; rewrite state_update_eq in H
  ; specialize (H _ Hv Ht')
  ; simpl in *
  ; destruct H as [Hproper' H]
  .
  - repeat split.
    + unfold equivocator_descriptors_update. rewrite equivocator_descriptors_update_eq. assumption.
    + unfold equivocator_descriptors_update. rewrite equivocator_descriptors_update_eq. reflexivity.
    + apply functional_extensionality_dep. intro j.
      destruct (decide (j = i)).
      * subst. rewrite state_update_eq. reflexivity.
      * repeat (rewrite state_update_neq; [| assumption]). reflexivity.
    + subst. specialize (H _ eq_refl). destruct H as [Hvx Htx].
      unfold equivocators_state_project. unfold Common.equivocators_state_project.
      unfold equivocator_descriptors_update.
      rewrite equivocator_descriptors_update_eq.
      assumption.
    + subst. specialize (H _ eq_refl). destruct H as [Hvx Htx].
      unfold equivocators_state_project. unfold Common.equivocators_state_project.
      unfold equivocator_descriptors_update.
      rewrite equivocator_descriptors_update_eq.
      simpl in *. rewrite Htx. f_equal.
      apply functional_extensionality_dep.
      intro eqv.
      destruct (decide (eqv = i)).
      * subst. repeat rewrite state_update_eq.
        rewrite state_update_eq in Hdestinationi. symmetry. assumption.
      * repeat (rewrite state_update_neq; [|assumption]).
        rewrite equivocator_descriptors_update_neq; [|assumption].
        reflexivity.
  - repeat split.
    + unfold equivocator_descriptors_update. rewrite equivocator_descriptors_update_eq. assumption.
    + unfold equivocator_descriptors_update. rewrite equivocator_descriptors_update_eq. reflexivity.
    + apply functional_extensionality_dep. intro j.
      destruct (decide (j = i)).
      * subst. rewrite state_update_eq. reflexivity.
      * repeat (rewrite state_update_neq; [| assumption]). reflexivity.
    + apply functional_extensionality_dep.
      intro eqv.
      unfold equivocators_state_project. unfold Common.equivocators_state_project.
      unfold equivocator_descriptors_update.
      destruct (decide (eqv = i)).
      * subst. rewrite state_update_eq. rewrite equivocator_descriptors_update_eq. assumption.
      * rewrite state_update_neq; [|assumption].
        rewrite equivocator_descriptors_update_neq; [|assumption].
        reflexivity.
Qed.

Lemma equivocators_transition_item_project_proper_characterization
  (eqv_descriptors : equivocator_descriptors)
  (item : composite_transition_item equivocator_IM)
  (Hproper : proper_equivocator_descriptors eqv_descriptors (destination item))
  : exists oitem eqv_descriptors',
    equivocators_transition_item_project eqv_descriptors item = Some (oitem, eqv_descriptors')
    /\ match oitem with
      | Some itemx =>
        existT _ (projT1 (l item)) (fst (projT2 (l item))) = l itemx /\  input item = input itemx /\ output item = output itemx /\
        (equivocators_state_project eqv_descriptors (destination item) = destination itemx)
      | None => True
      end
    /\ forall
      (s : composite_state equivocator_IM)
      (Hv : composite_valid equivocator_IM (l item) (s, input item))
      (Ht : composite_transition equivocator_IM (l item) (s, input item) = (destination item, output item)),
      proper_equivocator_descriptors eqv_descriptors' s /\
      match oitem with
      | Some itemx =>
        forall (sx : composite_state IM)
          (Hsx : sx = equivocators_state_project eqv_descriptors' s),
          composite_valid IM (l itemx) (sx, input itemx) /\
          composite_transition IM (l itemx) (sx, input itemx) = (destination itemx, output itemx)
      | None =>
        equivocators_state_project eqv_descriptors (destination item) = equivocators_state_project eqv_descriptors' s
      end.
Proof.
  destruct
    (equivocators_transition_item_project_proper_descriptor_characterization eqv_descriptors item (Hproper (projT1 (l item))))
    as [oitem [eqv_descriptors' [Hoitem [Hitemx H]]]].
  exists oitem, eqv_descriptors'. split; [assumption|].
  split; [assumption|].
  intros.
  specialize (H s Hv Ht). clear Hv Ht Hoitem.
  destruct H as [Hproperi' [Heqv' [Hs H]]].
  split; [|assumption]. clear H.
  intro eqv.
  destruct (decide (eqv = (projT1 (l item)))).
  - subst. assumption.
  - rewrite Heqv'. rewrite Hs.
    rewrite state_update_neq; [|assumption].
    unfold proper_descriptor. unfold equivocator_descriptors_update.
    rewrite equivocator_descriptors_update_neq; [|assumption].
    apply Hproper.
Qed.

Lemma equivocators_transition_item_project_inv_characterization
  (eqv_descriptors eqv_descriptors': equivocator_descriptors)
  (item : composite_transition_item equivocator_IM)
  (itemx : composite_transition_item IM)
  (Hpr_item : equivocators_transition_item_project eqv_descriptors item = Some (Some itemx, eqv_descriptors'))
  : existT _ (projT1 (l item)) (fst (projT2 (l item))) = l itemx /\
    input item = input itemx /\ output item = output itemx /\
    equivocators_state_project eqv_descriptors (destination item) = destination itemx.
Proof.
  unfold equivocators_transition_item_project in Hpr_item.
  destruct
    (equivocator_vlsm_transition_item_project
      (IM (projT1 (l item)))
      (composite_transition_item_projection equivocator_IM item)
      (eqv_descriptors (projT1 (l item))))
    as [([itemi|], descriptori)|] eqn:Hpr_itemi
  ; [|congruence|congruence].
  inversion Hpr_item. subst. clear Hpr_item. simpl.
  repeat split.
  apply equivocator_transition_item_project_inv_characterization in Hpr_itemi.
  destruct Hpr_itemi as [Hl _].
  rewrite Hl. reflexivity.
Qed.

Definition equivocators_trace_project_folder
  (item : composite_transition_item equivocator_IM)
  (result: option (list (composite_transition_item IM) * equivocator_descriptors))
  : option (list (composite_transition_item IM) * equivocator_descriptors)
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

Lemma equivocators_trace_project_folder_additive_iff
  (tr : list (composite_transition_item equivocator_IM))
  (itrX : list (composite_transition_item IM))
  (ieqv_descriptors eqv_descriptors : equivocator_descriptors)
  (trX' : list (composite_transition_item IM))
  : fold_right equivocators_trace_project_folder (Some (itrX, ieqv_descriptors)) tr
    = Some (trX', eqv_descriptors)
  <-> exists trX : list (composite_transition_item IM),
    fold_right equivocators_trace_project_folder (Some ([], ieqv_descriptors)) tr
      = Some (trX, eqv_descriptors)
    /\ trX' = trX ++ itrX.
Proof.
  revert trX' eqv_descriptors.
  induction tr; intros.
  - simpl. split; intro Htr.
    + inversion Htr. subst. exists []. split; reflexivity.
    + destruct Htr as [trX [HtrX HtrX']]. subst. inversion HtrX. reflexivity.
  - simpl.
    remember (fold_right equivocators_trace_project_folder (Some (itrX, ieqv_descriptors)) tr)
      as pr_itrX_tr.
    remember (fold_right equivocators_trace_project_folder (Some ([], ieqv_descriptors)) tr)
      as pr_tr.
    split.
    + intro Htr.
      destruct pr_itrX_tr as [(tr1,e1)|] ; [|inversion Htr].
      specialize (IHtr tr1 e1). apply proj1 in IHtr. specialize (IHtr eq_refl).
      destruct IHtr as [trX [Hpr_tr Htr1]].
      rewrite Hpr_tr in *. rewrite Htr1 in *.
      simpl in Htr. simpl.
      destruct (equivocators_transition_item_project e1 a)
        as [(oitem, eqv_descriptors'')|] eqn:Ha; [|congruence].
      destruct oitem; inversion Htr; eexists _; split; reflexivity.
    + intros [trX [Htr HtrX']].
      subst trX'.
      destruct pr_tr as [(tr1, e1)|]; [|inversion Htr].
      specialize (IHtr (tr1 ++ itrX) e1). apply proj2 in IHtr.
      spec IHtr. { eexists _.  split; reflexivity. }
      rewrite IHtr.
      simpl in *.
      destruct (equivocators_transition_item_project e1 a)
        as [(oitem, odescriptor)|] eqn:Ha
      ; [|discriminate Htr].
      destruct oitem as [item'|]; inversion Htr; reflexivity.
Qed.

Lemma equivocators_trace_project_folder_additive
  (tr : list (composite_transition_item equivocator_IM))
  (itrX trX : list (composite_transition_item IM))
  (ieqv_descriptors eqv_descriptors : equivocator_descriptors)
  (Htr : fold_right equivocators_trace_project_folder (Some ([], ieqv_descriptors)) tr
    = Some (trX, eqv_descriptors))
  : fold_right equivocators_trace_project_folder (Some (itrX, ieqv_descriptors)) tr
    = Some (trX ++ itrX, eqv_descriptors).
Proof.
  apply equivocators_trace_project_folder_additive_iff.
  exists trX. split; [assumption|reflexivity].
Qed.

(**
The projection of an [equivocators] trace is obtained by traversing the
trace from right to left guided by the descriptors produced by
[equivocators_transition_item_project] and gathering all non-empty
[transition_item]s it produces.
*)
Definition equivocators_trace_project
  (eqv_descriptors : equivocator_descriptors)
  (tr : list (composite_transition_item equivocator_IM))
  : option (list (composite_transition_item IM) * equivocator_descriptors)
  :=
  fold_right
    equivocators_trace_project_folder
    (Some ([], eqv_descriptors))
    tr.

Lemma equivocators_trace_project_app_iff
  (pre suf : list (composite_transition_item equivocator_IM))
  (ieqv_descriptors eqv_descriptors : equivocator_descriptors)
  (trX : list (composite_transition_item IM))
  : equivocators_trace_project eqv_descriptors (pre ++ suf)
    = Some (trX, ieqv_descriptors)
  <-> exists
    (preX sufX : list (composite_transition_item IM))
    (eqv_descriptors' : equivocator_descriptors),
    equivocators_trace_project eqv_descriptors suf = Some (sufX, eqv_descriptors') /\
    equivocators_trace_project eqv_descriptors' pre = Some (preX, ieqv_descriptors) /\
    trX = preX ++ sufX.
Proof.
  unfold equivocators_trace_project.
  rewrite fold_right_app.
  simpl.
  match goal with
  |- fold_right _ ?r _ = _ <-> _ => remember r as r_sufX
  end.
  destruct r_sufX as [(sufX, eqv_descriptors')|]
  ; [
    | rewrite equivocators_trace_project_fold_None; split;
      [intro contra; congruence| intros [preX [sufX [eqv_descriptors' [contra _]]]]; congruence]
    ].
  specialize (equivocators_trace_project_folder_additive_iff pre sufX eqv_descriptors' ieqv_descriptors trX)
    as Hadd.
  rewrite Hadd.
  split.
  - intros [preX [HpreX HtrX]]. exists preX, sufX, eqv_descriptors'. split; [reflexivity|].
    split; assumption.
  - intros [preX [_sufX [_eqv_descriptors' [Heq [Hpre HtrX]]]]].
    exists preX. inversion Heq. subst _sufX _eqv_descriptors'.
    split; assumption.
Qed.

(**
For every [transition_item] of the projection of a trace over the composition
of equivocators, there exists a corresponding item in the original trace
which projects to it.

*)
Lemma equivocators_trace_project_app_inv_item
  (tr : list (composite_transition_item equivocator_IM))
  (ieqv_descriptors eqv_descriptors : equivocator_descriptors)
  (preX sufX : list (composite_transition_item IM))
  (itemX : composite_transition_item IM)
  : equivocators_trace_project eqv_descriptors tr
    = Some (preX ++ [itemX] ++ sufX, ieqv_descriptors) ->
  exists
    (pre suf : list (composite_transition_item equivocator_IM))
    (item : (composite_transition_item equivocator_IM))
    (item_descriptors pre_descriptors : equivocator_descriptors),
    equivocators_trace_project eqv_descriptors suf = Some (sufX, item_descriptors) /\
    equivocators_transition_item_project item_descriptors item = Some (Some itemX, pre_descriptors) /\
    equivocators_trace_project pre_descriptors pre = Some (preX, ieqv_descriptors) /\
    tr = pre ++ [item] ++ suf.
Proof.
  generalize dependent sufX. generalize dependent eqv_descriptors.
  induction tr using rev_ind; intros eqv_descriptors sufX.
  - simpl. intro H. inversion H as [[Hnil Heq]]. destruct preX; inversion Hnil.
  - intro H. apply equivocators_trace_project_app_iff in H.
    destruct H as [trX' [xX [eqv_descriptors' [Hpr_x [Hpr_tr Heq]]]]].
    simpl in Hpr_x.
    destruct (equivocators_transition_item_project eqv_descriptors x)
      as [(ox, descriptorx)|] eqn:Hpr_x_item
    ; [|congruence].
    destruct xX as [|xX _empty].
    + destruct ox; [congruence|].
      inversion Hpr_x. subst. clear Hpr_x.
      rewrite app_nil_r in  Heq. subst trX'.
      specialize (IHtr eqv_descriptors' sufX Hpr_tr).
      destruct IHtr as [pre [suf [item [item_descriptors [pre_descriptors [Hpr_suf [Hpr_item [Hpr_pre Heqtr]]]]]]]].
      exists pre, (suf ++ [x]), item, item_descriptors, pre_descriptors.
      subst tr. rewrite !app_assoc.
      repeat split; [|assumption|assumption].
      apply equivocators_trace_project_app_iff.
      exists sufX, [], eqv_descriptors'. rewrite app_nil_r.
      repeat split; [|assumption].
      simpl. rewrite Hpr_x_item. reflexivity.
    + destruct ox; [|congruence].
      inversion Hpr_x. subst. clear Hpr_x.
      destruct_list_last sufX sufX' _xX Heq_sufX.
      * subst. rewrite app_nil_r in Heq. apply app_inj_tail in Heq.
        destruct Heq. subst.
        exists tr, [], x, eqv_descriptors, eqv_descriptors'.
        rewrite app_nil_r.
        repeat split; assumption.
      * subst. rewrite! app_assoc in Heq. apply app_inj_tail in Heq.
        rewrite <- app_assoc in Heq. destruct Heq. subst.
        specialize (IHtr eqv_descriptors' sufX' Hpr_tr).
        destruct IHtr as [pre [suf [item [item_descriptors [pre_descriptors [Hpr_suf [Hpr_item [Hpr_pre Heqtr]]]]]]]].
        exists pre, (suf ++ [x]), item, item_descriptors, pre_descriptors.
        subst tr. rewrite !app_assoc.
        repeat split; [|assumption|assumption].
        apply equivocators_trace_project_app_iff.
        exists sufX', [xX], eqv_descriptors'.
        repeat split; [|assumption].
        simpl. rewrite Hpr_x_item. reflexivity.
Qed.

(**
A corrollary of the above, reflecting a split in the projection to the original trace.
*)
Lemma equivocators_trace_project_app_inv
  (tr : list (composite_transition_item equivocator_IM))
  (ieqv_descriptors eqv_descriptors : equivocator_descriptors)
  (preX sufX : list (composite_transition_item IM))
  : equivocators_trace_project eqv_descriptors tr
    = Some (preX ++ sufX, ieqv_descriptors) ->
  exists
    (pre suf : list (composite_transition_item equivocator_IM))
    (eqv_descriptors' : equivocator_descriptors),
    equivocators_trace_project eqv_descriptors suf = Some (sufX, eqv_descriptors') /\
    equivocators_trace_project eqv_descriptors' pre = Some (preX, ieqv_descriptors) /\
    tr = pre ++ suf.
Proof.
  intro Hpr_tr.
  destruct sufX as [|itemX sufX].
  - rewrite app_nil_r in Hpr_tr.
    exists tr, [], eqv_descriptors. rewrite app_nil_r. repeat split. assumption.
  - change (itemX :: sufX) with ([itemX] ++ sufX) in Hpr_tr.
    apply equivocators_trace_project_app_inv_item in Hpr_tr.
    destruct Hpr_tr as [pre [suf [item [item_descriptors [pre_descriptors [Hpr_suf [Hpr_item [Hpr_pre Heqtr]]]]]]]].
    exists pre, ([item] ++ suf), pre_descriptors.
    subst. repeat split; [|assumption].
    apply equivocators_trace_project_app_iff.
    exists [itemX], sufX, item_descriptors.
    repeat split; [assumption|].
    simpl. rewrite Hpr_item. reflexivity.
Qed.

(**
We can project a trace over the composition of equivocators in two ways:
(1) first project on a equivocator component, then project the equivocator to the original component
(2) first projects to the composition of original components, then project to one of them

The result below says that the two ways lead to the same result.
*)
Lemma equivocators_trace_project_finite_trace_projection_list_commute
  (i : index)
  (final_descriptors initial_descriptors : equivocator_descriptors)
  (eqv_initial : MachineDescriptor (IM i))
  (tr : list (composite_transition_item equivocator_IM))
  (trX : list (composite_transition_item IM))
  (trXi : list (vtransition_item (IM i)))
  (eqv_final := final_descriptors i)
  (Hproject_tr : equivocators_trace_project final_descriptors tr = Some (trX, initial_descriptors))
  (Hproject_tri :
    equivocator_vlsm_trace_project (IM i)
      (finite_trace_projection_list equivocator_IM i tr) eqv_final
    = Some (trXi, eqv_initial))
  : initial_descriptors i = eqv_initial /\
    finite_trace_projection_list IM i trX = trXi.
Proof.
  generalize dependent trXi. generalize dependent trX.
  generalize dependent final_descriptors.
  induction tr using rev_ind; intros.
  - simpl in Hproject_tr. inversion Hproject_tr. subst.
    clear Hproject_tr.
    simpl in Hproject_tri.
    inversion Hproject_tri. subst. split; reflexivity.
  - unfold equivocators_trace_project in Hproject_tr.
    rewrite fold_right_app in Hproject_tr.
    match type of Hproject_tr with
    | fold_right _ ?i _ = _ => destruct i as [(projectx,final_descriptors')|] eqn:Hproject_x
    end
    ; [|rewrite equivocators_trace_project_fold_None in Hproject_tr; inversion Hproject_tr].
    apply equivocators_trace_project_folder_additive_iff in Hproject_tr.
    destruct Hproject_tr as [trX0 [HtrX0 HtrX]].
    specialize (IHtr _ _ HtrX0).
    rewrite finite_trace_projection_list_app in Hproject_tri.
    apply equivocator_vlsm_trace_project_app in Hproject_tri.
    destruct Hproject_tri as [eqv_final' [trXi' [project_xi [HtrXi' [Hproject_xi HeqtrXi]]]]].
    assert (Hfinal'i : final_descriptors' i = eqv_final' /\ finite_trace_projection_list IM i projectx = project_xi).
    { clear - Hproject_x Hproject_xi.
      simpl in *.
      destruct (equivocators_transition_item_project final_descriptors x)
        as [(ox, final')|] eqn:Hpr_item_x
      ; [|congruence].
      unfold equivocators_transition_item_project in Hpr_item_x.
      unfold composite_transition_item_projection in Hpr_item_x.
      destruct (decide (i = projT1 (l x))).
      - subst i. simpl in Hproject_xi.
        unfold eqv_final in *.
        remember
          (equivocator_vlsm_transition_item_project (IM (projT1 (l x))) (composite_transition_item_projection_from_eq equivocator_IM x (projT1 (l x)) eq_refl) (final_descriptors (projT1 (l x))))
          as pr_item_x.
        destruct pr_item_x as [(oitem', descriptor')|]; [|discriminate Hproject_xi].
        destruct oitem' as [item'|]
        ; inversion Hproject_xi; subst descriptor' project_xi; clear Hproject_xi
        ; inversion Hpr_item_x; subst; clear Hpr_item_x
        ; inversion Hproject_x; subst; clear Hproject_x
        ; unfold equivocator_descriptors_update; rewrite equivocator_descriptors_update_eq
        ; [|split; reflexivity].
        split; [reflexivity|].
        symmetry in Heqpr_item_x.
        simpl. destruct x. simpl in *. destruct l as (i, li). simpl in *.
        destruct (decide (i = i)); [|congruence].
        f_equal.
        replace e with (@eq_refl _ i) by apply UIP. clear e.
        unfold composite_transition_item_projection_from_eq in *.
        simpl in *.
        destruct item'.
        apply equivocator_transition_item_project_inv_characterization in Heqpr_item_x.
        simpl in *.
        destruct Heqpr_item_x as [Hl [Hinput [Houtput Hdestination]]].
        subst. reflexivity.
      - simpl in Hproject_xi.
        unfold eqv_final in *.
        inversion Hproject_xi. subst. clear Hproject_xi.
        remember
          (equivocator_vlsm_transition_item_project (IM (projT1 (l x))) (composite_transition_item_projection_from_eq equivocator_IM x (projT1 (l x)) eq_refl) (final_descriptors (projT1 (l x))))
          as pr_item_x.
        destruct pr_item_x as [(oitem', descriptor')|]; [|discriminate Hpr_item_x].
        destruct oitem' as [item'|]
        ; inversion Hpr_item_x; subst; clear Hpr_item_x
        ; inversion Hproject_x; subst; clear Hproject_x
        ; unfold equivocator_descriptors_update; (rewrite equivocator_descriptors_update_neq ; [|assumption])
        ; [|split; reflexivity].
        split; [reflexivity|].
        simpl.
        destruct (decide (i = projT1 (l x))); congruence.
    }
    destruct Hfinal'i as [Hfinal'i Hpr_xi].
    rewrite <- Hfinal'i in HtrXi'.
    specialize (IHtr _ HtrXi').
    destruct IHtr as [Heqv_initial Hpr_trXi'].
    split; [assumption|].
    subst.
    rewrite finite_trace_projection_list_app.
    reflexivity.
Qed.

Section seeded_equivocators_protocol_trace_project.

Context
  (seed : message -> Prop)
  (FreeE := free_composite_vlsm equivocator_IM)
  (PreFreeE := pre_loaded_with_all_messages_vlsm FreeE)
  (SeededXE := seeded_equivocators_no_equivocation_vlsm IM Hbs finite_index seed)
  (SeededX := pre_loaded_vlsm X seed)
  .

Lemma seeded_equivocators_initial_message
  (m : message)
  (Hem : vinitial_message_prop SeededXE m)
  : vinitial_message_prop SeededX m.
Proof.
  destruct Hem as [[eqv [emi Hem]]|Hseed].
  - left. exists eqv. exists emi. assumption.
  - right. assumption.
Qed.

Lemma seeded_equivocators_incl_preloaded
  : VLSM_incl SeededXE PreFreeE.
Proof.
  apply seeded_equivocators_incl_preloaded.
Qed.

(**
A generalization of [equivocators_transition_item_project_preserves_zero_descriptors]
to full (valid) traces
*)
Lemma equivocators_trace_project_preserves_zero_descriptors
  (is : composite_state equivocator_IM)
  (tr : list (composite_transition_item equivocator_IM))
  (Htr : finite_protocol_trace_from PreFreeE is tr)
  (s := last (map destination tr) is)
  (descriptors : equivocator_descriptors)
  (idescriptors : equivocator_descriptors)
  (trX : list (composite_transition_item IM))
  (HtrX : equivocators_trace_project descriptors tr = Some (trX, idescriptors))
  : forall i, descriptors i = Existing _ 0 false -> idescriptors i = Existing _ 0 false.
Proof.
  generalize dependent trX. generalize dependent descriptors.
  induction tr using rev_ind; intros
  ; [inversion HtrX; subst; apply H; assumption|].
  apply finite_protocol_trace_from_app_iff in Htr. destruct Htr as [Htr Hx].
  spec IHtr Htr.
  apply equivocators_trace_project_app_iff in HtrX.
  destruct HtrX as [trX' [xX [eqv_descriptors' [HxX [HtrX' HtrX]]]]].
  subst trX.
  subst s.
  simpl in HxX.
  destruct (equivocators_transition_item_project descriptors x) as [(o, descriptor)|] eqn:Hpr; [|congruence].

  inversion Hx. subst. clear Hx H3.
  destruct H4 as [[_ [_ [Hv _]]] Ht].
  match type of Hv with
  | composite_valid _ _ (?l, _) => remember l as lst
  end.

  spec IHtr eqv_descriptors' trX' HtrX'.
  apply IHtr.

  specialize
    (equivocators_transition_item_project_preserves_zero_descriptors descriptors
      {| l := l; input := iom; destination := s; output := oom |}
      o descriptor
    )
    as Hzero.
  simpl in Hzero.
  specialize (Hzero _ Ht Hv Hpr).
  spec Hzero i H.
  destruct o; inversion HxX; subst; assumption.
Qed.

Lemma preloaded_equivocators_protocol_trace_from_project
  (final_descriptors : equivocator_descriptors)
  (is : composite_state equivocator_IM)
  (tr : list (composite_transition_item equivocator_IM))
  (final_state := last (map destination tr) is)
  (Hproper : proper_equivocator_descriptors final_descriptors final_state)
  (Htr : finite_protocol_trace_from pre_loaded_equivocators is tr)
  : exists
    (trX : list (composite_transition_item IM))
    (initial_descriptors : equivocator_descriptors),
    equivocators_trace_project final_descriptors tr = Some (trX, initial_descriptors)
    /\ proper_equivocator_descriptors initial_descriptors is
    /\ equivocators_state_project final_descriptors (last (map destination tr) is)
     = last (map destination trX) (equivocators_state_project initial_descriptors is).
Proof.
  generalize dependent final_descriptors.
  generalize dependent is.
  induction tr using rev_ind; intros.
  - exists []. simpl. exists final_descriptors. repeat split; assumption.
  - apply finite_protocol_trace_from_app_iff in Htr.
    destruct Htr as [Htr Hx].
    specialize (IHtr _ Htr).
    specialize (equivocators_transition_item_project_proper_characterization final_descriptors x) as Hproperx.
    unfold final_state in Hproper.
    rewrite map_app in Hproper. simpl in Hproper. rewrite last_is_last in Hproper.
    spec Hproperx Hproper.
    destruct Hproperx as [oitem [final_descriptors' [Hprojectx [Hitemx Hproperx]]]].
    specialize (Hproperx (last (map destination tr) is)).
    unfold equivocators_trace_project.
    rewrite fold_right_app.
    match goal with
    |- context [fold_right _ ?fld _] => remember fld as foldx
    end.
    simpl in Heqfoldx.
    rewrite Hprojectx in Heqfoldx.
    inversion Hx. subst tl s' x. clear Hx.
    destruct H3 as [[_ [_ [Hv _]]] Ht].
    specialize (Hproperx Hv Ht).
    destruct Hproperx as [Hproper' Hx].
    specialize (IHtr _ Hproper').
    destruct IHtr as [trX' [initial_descriptors [Htr_project [Hproper_initial Hlst]]]].
    destruct oitem as [item|].
    + simpl in Hitemx. destruct Hitemx as [Hl [Hinput [Houtput Hdestination]]].
      specialize (Hx _ eq_refl).
      destruct Hx as [Hvx Htx].
      exists (trX' ++ [item]), initial_descriptors. subst foldx.
      rewrite equivocators_trace_project_folder_additive with (trX := trX') (eqv_descriptors := initial_descriptors)
      ; [|assumption].
      repeat split; [assumption|].
      rewrite! map_app. simpl. rewrite! last_is_last. assumption.
    + exists trX', initial_descriptors. subst foldx. repeat split; [assumption|assumption|].
      rewrite! map_app. simpl. rewrite! last_is_last.
      simpl in Hx. simpl in Hlst. congruence.
Qed.

Lemma preloaded_equivocators_protocol_trace_project_inv
  (final_descriptors : equivocator_descriptors)
  (is : composite_state equivocator_IM)
  (tr : list (composite_transition_item equivocator_IM))
  (final_state := last (map destination tr) is)
  (Htr : finite_protocol_trace pre_loaded_equivocators is tr)
  (trX : list (composite_transition_item IM))
  (initial_descriptors : equivocator_descriptors)
  (Hproject: equivocators_trace_project final_descriptors tr = Some (trX, initial_descriptors))
  (Hproper : proper_equivocator_descriptors initial_descriptors is)
  : proper_equivocator_descriptors final_descriptors final_state.
Proof.
  revert Hproject. revert trX Htr final_descriptors.
  induction tr using rev_ind; intros; [inversion Hproject; assumption|].
  destruct Htr as [Htr Hinit].
  apply finite_protocol_trace_from_app_iff in Htr.
  destruct Htr as [Htr Hx].
  unfold equivocators_trace_project in Hproject.
  rewrite fold_right_app in Hproject.
  match type of Hproject with
  | fold_right _ ?f _ = _ => remember f as project_x
  end.
  simpl in Heqproject_x.
  destruct project_x as [(x', x_descriptors)|]
  ; [|rewrite equivocators_trace_project_fold_None in Hproject; congruence].
  destruct (equivocators_transition_item_project final_descriptors x) as [(oitem', ditem')|]
    eqn:Hproject_x
  ; [|congruence].
  apply (equivocators_trace_project_folder_additive_iff tr x' x_descriptors initial_descriptors trX)
  in Hproject.
  destruct Hproject as [trX' [Hproject_x' HeqtrX]].
  specialize (IHtr trX' (conj Htr Hinit) _ Hproject_x').
  inversion Hx. subst. clear Hx.
  unfold equivocators_transition_item_project in Hproject_x.
  simpl in Hproject_x.
  unfold composite_transition_item_projection in Hproject_x. simpl in Hproject_x.
  unfold composite_transition_item_projection_from_eq in Hproject_x. simpl in Hproject_x.
  unfold eq_rect_r in Hproject_x. simpl in Hproject_x.
  match type of Hproject_x with
  | context [equivocator_vlsm_transition_item_project ?X ?i ?c] => remember (equivocator_vlsm_transition_item_project X i c)  as projecti
  end.
  destruct projecti as [(oitem'', ditem'')|]; [|congruence].
  unfold equivocator_vlsm_transition_item_project in Heqprojecti.
  unfold final_state in *. clear final_state.
  rewrite map_app. simpl. rewrite last_is_last.
  destruct (final_descriptors (projT1 l)) as [sn| j fj] eqn:Hfinali.
  - inversion Heqprojecti. subst. clear Heqprojecti.
    inversion Hproject_x. subst; clear Hproject_x.
    inversion Heqproject_x. subst. clear Heqproject_x.
    intro e. specialize (IHtr e).
    destruct (decide (e = projT1 l)).
    + subst.
      unfold equivocator_descriptors_update in IHtr. rewrite equivocator_descriptors_update_eq in IHtr.
      rewrite Hfinali. assumption.
    + unfold equivocator_descriptors_update in IHtr.
      rewrite equivocator_descriptors_update_neq in IHtr
      ; [|assumption].
      destruct H3 as [Hv Ht].
      simpl in Ht. unfold vtransition in Ht. simpl in Ht.
      destruct l as (i, li).
      match type of Ht with
      | (let (_,_) := ?t in _) = _ => destruct t as (si', om')
      end.
      inversion Ht. subst. simpl in n.
      rewrite state_update_neq; [|assumption]. assumption.
  - destruct l as (i, (li, di)).
    unfold projT2 in Heqprojecti.
    unfold projT1 in Heqprojecti.
    destruct (s i) as (nsi, bsi) eqn:Hsi.
    destruct (le_lt_dec (S nsi) j); [congruence|].
    destruct H3 as [Hv Ht].
    simpl in Ht. unfold vtransition in Ht. simpl in Ht.
    match type of Ht with
    | (let (_,_) := ?t in _) = _ => destruct t as (si', om') eqn:Ht'
    end.
    inversion Ht. subst. clear Ht.
    destruct di as [ndi | idi ifi]
    ; [destruct (nat_eq_dec (S j) (S nsi))
      | destruct ifi; [destruct (nat_eq_dec (S j) (S nsi))| destruct (nat_eq_dec idi j)]]
    ; inversion Heqprojecti; subst; clear Heqprojecti
    ; inversion Hproject_x; subst; clear Hproject_x
    ; inversion Heqproject_x; subst; clear Heqproject_x
    ; intro eqv; specialize (IHtr eqv)
    ; (destruct (decide (eqv = i))
      ; [subst eqv
        ; unfold equivocator_descriptors_update in IHtr; rewrite equivocator_descriptors_update_eq in IHtr
        ; simpl in *; rewrite Hfinali; rewrite Hsi; simpl; assumption
        |
        unfold equivocator_descriptors_update in IHtr
        ; rewrite equivocator_descriptors_update_neq in IHtr
        ; [|assumption]
        ; rewrite state_update_neq; [|assumption]
        ; assumption
        ]
      ).
Qed.

(**
A corrollary of [preloaded_equivocators_protocol_trace_from_project] selecting
only the [proper_equivocator_descriptors] property.
*)
Lemma preloaded_equivocators_protocol_trace_project_proper_initial
  (is : composite_state equivocator_IM)
  (tr : list (composite_transition_item equivocator_IM))
  (final_state := last (map destination tr) is)
  (Htr : finite_protocol_trace_from pre_loaded_equivocators is tr)
  (final_descriptors : equivocator_descriptors)
  (trX : list (composite_transition_item IM))
  (initial_descriptors : equivocator_descriptors)
  (Hproject: equivocators_trace_project final_descriptors tr = Some (trX, initial_descriptors))
  (Hproper : proper_equivocator_descriptors final_descriptors final_state)
  : proper_equivocator_descriptors initial_descriptors is.
Proof.
  destruct
    (preloaded_equivocators_protocol_trace_from_project
      final_descriptors is tr Hproper Htr
    )
    as [_trX [_initial_descriptors [_Hproject [Hiproper _]]]].
  rewrite Hproject in _Hproject.
  inversion _Hproject. subst _trX _initial_descriptors.
  assumption.
Qed.

Lemma equivocators_trace_project_output_reflecting_inv
  (is: composite_state equivocator_IM)
  (tr: list (composite_transition_item equivocator_IM))
  (Htr: finite_protocol_trace_from (pre_loaded_with_all_messages_vlsm (free_composite_vlsm equivocator_IM)) is tr)
  (m : message)
  (Hbbs : Exists (field_selector output m) tr)
  : exists
    (final_descriptors initial_descriptors : equivocator_descriptors)
    (trX: list (composite_transition_item IM)),
    not_equivocating_equivocator_descriptors IM final_descriptors (last (map destination tr) is) /\
    equivocators_trace_project final_descriptors tr = Some (trX, initial_descriptors) /\
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
  destruct Hex as [eqv_final [eqv_init [Heqv_init [Heqv_final [trXi [Hprojecti Hex]]]]]].
  specialize
    (preloaded_finite_trace_projection_last_state equivocator_IM (free_constraint equivocator_IM) i _ _ Htr)
    as Hlst.
  simpl in Hlst,Heqv_final. rewrite Hlst in Heqv_final. clear Hlst.
  match type of Heqv_final with
  | not_equivocating_descriptor _ _ (?l i) => remember l as final
  end.
  remember (equivocator_descriptors_update (zero_descriptor IM) i eqv_final) as final_descriptors.
  assert (Hfinal_descriptors : not_equivocating_equivocator_descriptors IM final_descriptors final).
  { intro eqv. subst final_descriptors.
    destruct (decide (eqv = i)).
    - subst i.
      unfold equivocator_descriptors_update.  rewrite equivocator_descriptors_update_eq.
      assumption.
    - unfold equivocator_descriptors_update.
      rewrite equivocator_descriptors_update_neq
      ; [|assumption].
      apply zero_descriptor_proper. assumption.
  }
  exists final_descriptors.
  subst final.
  assert (Hfinal_descriptors_proper : proper_equivocator_descriptors final_descriptors (last (map Common.destination tr) is)).
  { apply not_equivocating_equivocator_descriptors_proper. assumption. }
  destruct (preloaded_equivocators_protocol_trace_from_project  _ _ _ Hfinal_descriptors_proper Htr)
    as [trX [initial_descriptors [Hproject_tr _]]].
  exists initial_descriptors, trX. split; [assumption|]. split; [assumption|].
  specialize
    (equivocators_trace_project_finite_trace_projection_list_commute i final_descriptors initial_descriptors
      eqv_init tr trX trXi Hproject_tr)
    as Hcommute.
  assert (Hfinali : final_descriptors i = eqv_final).
  { subst. apply equivocator_descriptors_update_eq. }
  rewrite Hfinali in Hcommute.
  spec Hcommute Hprojecti.
  destruct Hcommute as [Hiniti Hcommute].
  clear -Hex Hcommute. subst.
  apply Exists_exists in Hex. destruct Hex as [x [Hx Hm]].
  apply (finite_trace_projection_list_in_rev IM) in Hx.
  destruct Hx as [itemX [Houtput [_ [_ [_ [_ HitemX]]]]]].
  apply Exists_exists. exists itemX. split; [assumption|].
  simpl in *. rewrite Houtput. assumption.
Qed.

Lemma equivocators_trace_project_output_reflecting_iff
  (is: composite_state equivocator_IM)
  (tr: list (composite_transition_item equivocator_IM))
  (Htr: finite_protocol_trace_from (pre_loaded_with_all_messages_vlsm (free_composite_vlsm equivocator_IM)) is tr)
  (m : message)
  : Exists (field_selector output m) tr
  <-> exists
    (final_descriptors initial_descriptors : equivocator_descriptors)
    (trX: list (composite_transition_item IM)),
    not_equivocating_equivocator_descriptors IM final_descriptors (last (map destination tr) is) /\
    equivocators_trace_project final_descriptors tr = Some (trX, initial_descriptors) /\
    Exists (field_selector output m) trX.
Proof.
  split; [apply equivocators_trace_project_output_reflecting_inv; assumption|].
  intros [final_descriptors [initial_descriptors [trX [Hfinal_descriptors [Hpr_tr Hex]]]]].
  apply Exists_exists in Hex.
  destruct Hex as [itemX [HitemX Hm]].
  apply in_split in HitemX.
  destruct HitemX as [preX [sufX Heq_trX]].
  subst.
  apply equivocators_trace_project_app_inv_item in Hpr_tr.
  destruct Hpr_tr as [pre [suf [item [item_descriptors [pre_descriptors [_ [Hpr_item [_ Heqtr]]]]]]]].
  subst.
  rewrite !Exists_app. right. left. constructor.
  apply equivocators_transition_item_project_inv_characterization in Hpr_item.
  destruct Hpr_item as [_ [_ [Heqoutput _]]].
  simpl in *. congruence.
Qed.

Lemma seeded_equivocators_protocol_trace_project
  (final_descriptors : equivocator_descriptors)
  (is : vstate equivocators_no_equivocations_vlsm)
  (tr : list (composite_transition_item equivocator_IM))
  (final_state := last (map destination tr) is)
  (Hproper : proper_equivocator_descriptors final_descriptors final_state)
  (Htr : finite_protocol_trace SeededXE is tr)
  : exists
    (trX : list (composite_transition_item IM))
    (initial_descriptors : equivocator_descriptors)
    (isX := equivocators_state_project initial_descriptors is)
    (final_stateX := last (map destination trX) isX),
    proper_equivocator_descriptors initial_descriptors is /\
    equivocators_trace_project final_descriptors tr = Some (trX, initial_descriptors) /\
    equivocators_state_project final_descriptors final_state = final_stateX /\
    finite_protocol_trace SeededX isX trX.
Proof.
  remember (length tr) as len_tr.
  generalize dependent final_descriptors. generalize dependent tr.
  induction len_tr using (well_founded_induction Wf_nat.lt_wf); intros.
  subst len_tr.
  destruct_list_last tr tr' lst Htr_lst.
  - clear H. subst. unfold final_state in *. exists [], final_descriptors.
    split; [assumption|]. split; [reflexivity|]. split; [reflexivity|].
    remember (equivocators_state_project final_descriptors is) as isx.
    cut (vinitial_state_prop X isx).
    { intro. split; [|assumption]. constructor.
      apply protocol_state_prop_iff. left.
      exists (exist _ _ H). reflexivity.
    }
    subst.
    apply equivocators_initial_state_project; [|assumption].
    apply Htr.
  - specialize (H (length tr')) as H'.
    spec H'. { rewrite app_length. simpl. lia. }
    destruct Htr as [Htr Hinit].
    apply finite_protocol_trace_from_app_iff in Htr.
    destruct Htr as [Htr Hlst].
    specialize (H' tr' (conj Htr Hinit) eq_refl).
    specialize (equivocators_transition_item_project_proper_characterization final_descriptors lst) as Hproperx.
    unfold final_state in Hproper. rewrite Htr_lst in Hproper.
    rewrite map_app in Hproper. simpl in Hproper. rewrite last_is_last in Hproper.
    spec Hproperx Hproper.
    destruct Hproperx as [oitem [final_descriptors' [Hprojectx [Hitemx Hproperx]]]].
    specialize (Hproperx (last (map destination tr') is)).
    unfold equivocators_trace_project.
    rewrite fold_right_app.
    match goal with
    |- context [fold_right _ ?fld _] => remember fld as foldx
    end.
    simpl in Heqfoldx.
    rewrite Hprojectx in Heqfoldx.
    inversion Hlst. subst tl s' lst.
    destruct H4 as [[Hs [Hiom [Hv Hc]]] Ht].
    specialize (Hproperx Hv Ht). clear Hv Ht.
    destruct Hproperx as [Hproper' Hx].
    specialize (H' _ Hproper').
    destruct H' as [trX' [initial_descriptors [Hproper_initial [Htr_project [Hstate_project HtrX']]]]].
    destruct oitem as [item|].
    +  simpl in Hitemx. destruct Hitemx as [Hl [Hinput [Houtput Hdestination]]].
      specialize (Hx _ eq_refl).
      destruct Hx as [Hvx Htx].
      exists (trX' ++ [item]), initial_descriptors. subst foldx.
      rewrite equivocators_trace_project_folder_additive with (trX := trX') (eqv_descriptors := initial_descriptors)
      ; [|assumption].
      split; [assumption|].
      split; [reflexivity|].
      rewrite map_app. simpl. rewrite last_is_last.
      unfold final_state. subst tr. rewrite map_app. simpl. rewrite last_is_last.
      split; [assumption|].
      destruct HtrX' as [HtrX' His].
      split; [|assumption].
      apply finite_protocol_trace_from_app_iff.
      split; [assumption|].
      change [item] with ([] ++ [item]).
      match goal with
      |- finite_protocol_trace_from _ ?l _ => remember l as lst
      end.
      destruct item.
      assert (Hplst : protocol_state_prop SeededX lst).
      { apply finite_ptrace_last_pstate in HtrX'. subst. assumption. }
      apply (extend_right_finite_trace_from SeededX lst []); [constructor; assumption|].
      simpl in Hl. subst.
      simpl in Htx,Hvx,Hstate_project.
      rewrite Hstate_project in Hvx, Htx.
      destruct input as [input|]
      ; [|repeat split; [assumption| apply option_protocol_message_None |assumption| assumption]].
      simpl in Hc.
      specialize (seeded_equivocators_initial_message input) as Hinput.
      unfold vinitial_message_prop in Hinput at 1. simpl in Hinput.
      destruct Hc as [Hc _]. apply or_comm in Hc.
      destruct Hc as [Hinit_input | Hno_equiv]
      ; [apply Hinput in Hinit_input|]
      ; [repeat split; [assumption| |assumption|assumption]|].
      { apply initial_message_is_protocol. assumption. }
      clear Hinput.
      assert
        (Hs_free : protocol_state_prop PreFreeE (last (map Common.destination tr') is)).
      { clear -Hs.
        apply VLSM_incl_protocol_state with (machine SeededXE)
        ; [|assumption].
        apply seeded_equivocators_incl_preloaded.
      }

      specialize
        (proper_sent _  _ Hs_free input) as Hall.
      apply Hall in Hno_equiv.
      specialize (Hno_equiv is tr').
      assert
        (Htr'pre : finite_protocol_trace PreFreeE is tr').
      {  split; [|assumption].
        apply (VLSM_incl_finite_protocol_trace_from _ _ seeded_equivocators_incl_preloaded).
        assumption.
      }
      specialize (Hno_equiv Htr'pre eq_refl).
      destruct (equivocators_trace_project_output_reflecting_inv _ _ (proj1 Htr'pre) _ Hno_equiv)
        as [final_descriptors_m [initial_descriptors_m [trXm [Hfinal_descriptors_m [Hproject_trXm Hex]]]]].
      specialize (H (length tr')).
      spec H. { rewrite app_length. simpl. lia. }
      assert (Hfinal_descriptors_m_proper : proper_equivocator_descriptors final_descriptors_m (last (map Common.destination tr') is))
        by (apply not_equivocating_equivocator_descriptors_proper; assumption).
      specialize (H tr' (conj Htr Hinit) eq_refl final_descriptors_m Hfinal_descriptors_m_proper).
      destruct H as [trXm' [initial_descriptors_m' [Hproper_initial_m [Hproject_trXm' [Hpr_fin_tr' HtrXm]]]]].
      simpl in *. rewrite Hproject_trXm in Hproject_trXm'.
      inversion Hproject_trXm'. subst trXm' initial_descriptors_m'. clear Hproject_trXm'.
      repeat split; [assumption| |assumption| assumption].
      apply option_protocol_message_Some.
      apply (protocol_trace_output_is_protocol _ _ _ (proj1 HtrXm) _ Hex).
    + exists trX'. exists initial_descriptors. subst foldx. split; [assumption|].
      split; [apply Htr_project|]. split; [|assumption].
      subst tr. clear -Hstate_project Hx.
      rewrite Hstate_project in Hx.
      rewrite <- Hx. f_equal. unfold final_state.
      rewrite map_app. simpl. rewrite last_is_last. reflexivity.
Qed.

Lemma seeded_equivocators_protocol_trace_from_project
  (final_descriptors : equivocator_descriptors)
  (is : vstate equivocators_no_equivocations_vlsm)
  (tr : list (composite_transition_item equivocator_IM))
  (final_state := last (map destination tr) is)
  (Hproper : proper_equivocator_descriptors final_descriptors final_state)
  (Htr : finite_protocol_trace_from SeededXE is tr)
  : exists
    (trX : list (composite_transition_item IM))
    (initial_descriptors : equivocator_descriptors)
    (isX := equivocators_state_project initial_descriptors is)
    (final_stateX := last (map destination trX) isX),
    proper_equivocator_descriptors initial_descriptors is /\
    equivocators_trace_project final_descriptors tr = Some (trX, initial_descriptors) /\
    equivocators_state_project final_descriptors final_state = final_stateX /\
    finite_protocol_trace_from SeededX isX trX.
Proof.
  apply finite_protocol_trace_from_complete_left in Htr as Htr'.
  destruct Htr' as [is0 [pre [Htr' His]]].
  apply (seeded_equivocators_protocol_trace_project final_descriptors) in Htr' as HtrX'
  ; [| rewrite map_app; rewrite last_app; subst; assumption].
  destruct HtrX' as [trX' [initial_descriptors' [Hinitial_descriptors' [Hproject' [Hstate_project HtrX']]]]].
  apply equivocators_trace_project_app_iff in Hproject'.
  destruct Hproject' as [preX [trX [initial_descriptors [Hproject_tr [Hproject_pre HeqtrX']]]]].
  subst trX'.
  destruct HtrX' as [HtrX' HinitX].
  apply finite_protocol_trace_from_app_iff in HtrX'.
  destruct HtrX' as [HpreX HtrX].
  exists trX. exists initial_descriptors.
  rewrite! map_app in Hstate_project.
  rewrite! last_app in Hstate_project.
  destruct Htr' as [Htr' Hinit].
  apply finite_protocol_trace_from_app_iff in Htr'.
  destruct Htr' as [Hpre _].
  assert (HprePre : finite_protocol_trace pre_loaded_equivocators is0 pre).
  { split; [|assumption].
    apply (VLSM_incl_finite_protocol_trace_from _ _ seeded_equivocators_incl_preloaded).
    assumption.
  }
  specialize
    (preloaded_equivocators_protocol_trace_project_inv initial_descriptors _ _ HprePre _ _ Hproject_pre Hinitial_descriptors')
    as Hinitial_descriptors.
  destruct
    (seeded_equivocators_protocol_trace_project _ _ _ Hinitial_descriptors (conj Hpre Hinit))
    as [_preX [_initial_descriptors' [_ [_Hproject_pre [Hpr_last_pre _]]]]].
  rewrite Hproject_pre in _Hproject_pre.
  inversion _Hproject_pre. subst _preX _initial_descriptors'. clear _Hproject_pre.
  subst is. unfold final_state in *. simpl in *. rewrite <- Hpr_last_pre in *.
  repeat (split; [assumption|]). split; [|assumption].
  match goal with
  |- ?p = _ =>
    match type of Hstate_project with
    | _ = ?l => replace p with l
    end
  end.
  f_equal. symmetry. assumption.
Qed.

End seeded_equivocators_protocol_trace_project.

Lemma equivocators_protocol_trace_from_project
  (final_descriptors : equivocator_descriptors)
  (is : vstate equivocators_no_equivocations_vlsm)
  (tr : list (composite_transition_item equivocator_IM))
  (final_state := last (map destination tr) is)
  (Hproper : proper_equivocator_descriptors final_descriptors final_state)
  (Htr : finite_protocol_trace_from equivocators_no_equivocations_vlsm is tr)
  : exists
    (trX : list (composite_transition_item IM))
    (initial_descriptors : equivocator_descriptors)
    (isX := equivocators_state_project initial_descriptors is)
    (final_stateX := last (map destination trX) isX),
    proper_equivocator_descriptors initial_descriptors is /\
    equivocators_trace_project final_descriptors tr = Some (trX, initial_descriptors) /\
    equivocators_state_project final_descriptors final_state = final_stateX /\
    finite_protocol_trace_from X isX trX.
Proof.
  specialize
    (seeded_equivocators_protocol_trace_from_project (fun m => False)
      final_descriptors is tr Hproper
    ) as Hproject.
  spec Hproject.
  { apply VLSM_incl_finite_protocol_trace_from; [|assumption].
    specialize (false_composite_no_equivocation_vlsm_with_pre_loaded equivocator_IM (free_constraint equivocator_IM) (equivocator_Hbs IM Hbs) finite_index)
      as Heq.
    match goal with
    |- VLSM_incl_part ?m1 ?m2 =>
      cut (VLSM_eq (mk_vlsm m2) (mk_vlsm m1))
    end
    ; [intro H; apply VLSM_eq_incl_iff in H; exact (proj2 H)|].
    assumption.
  }
  destruct Hproject as [trX [initial_descriptors [Hinitial_descriptors [Hproject_tr [Hproject_lst HtrX]]]]].
  exists trX, initial_descriptors.
  specialize (vlsm_is_pre_loaded_with_False X) as Heq.
  apply VLSM_eq_incl_iff in Heq.
  destruct Heq as [_ Hincl].
  apply (VLSM_incl_finite_protocol_trace_from _ _ Hincl) in HtrX.
  repeat split; assumption.
Qed.

End equivocators_composition_projections.

Section equivocators_composition_sub_projections.

Context
  {message : Type}
  {index : Type}
  {IndEqDec : EqDecision index}
  (IM : index -> VLSM message)
  (Hbs : forall i : index, has_been_sent_capability (IM i))
  {index_listing : list index}
  (finite_index : Listing index_listing)
  (selection : list index)
  (Hsub_i0 : selection <> [])
  (i0 : Inhabited index := @SubProjectionTraces.i0 index selection Hsub_i0)
  (sub_index_eq_dec : EqDecision (sub_index selection) := sub_index_eq_dec selection)
  (sub_i0 : Inhabited (sub_index selection) := sub_index_i0 selection Hsub_i0)
  .

Existing Instance i0.
Existing Instance sub_i0.
Existing Instance sub_index_eq_dec.


(**
A generalization of [equivocators_trace_project_finite_trace_projection_list_commute]
to projections over a set of indices.

We can project a trace over the composition of equivocators in two ways:
(1) first project to a subset of equivocator components, then project that to the corresponding subset of the composition of the original components
(2) first project to the composition of original components, then project to a subset of them

The results below (fist for a single item, then for the full trace saythat the
two ways lead to the same result.
*)
Lemma equivocators_trace_project_finite_trace_sub_projection_item_commute
  (item: composite_transition_item (equivocator_IM IM))
  (final_descriptors' final_descriptors: equivocator_descriptors IM)
  (final_sub_descriptors := fun i : sub_index selection => final_descriptors (` i))
  (pr_item: list (composite_transition_item IM))
  (Hpr_item: equivocators_trace_project IM final_descriptors [item] = Some (pr_item, final_descriptors'))
  (pr_sub_item: list (composite_transition_item (sub_IM IM selection)))
  (final_sub_descriptors': equivocator_descriptors (sub_IM IM selection))
  (Hpr_sub_item: equivocators_trace_project (sub_IM IM selection) final_sub_descriptors (finite_trace_sub_projection (equivocator_IM IM) selection [item]) = Some (pr_sub_item, final_sub_descriptors'))
  : final_sub_descriptors' = (fun i : sub_index selection => final_descriptors' (` i))
  /\ finite_trace_sub_projection IM selection pr_item = pr_sub_item.
Proof.
  unfold equivocators_trace_project in Hpr_item. unfold sub_IM in *.
  simpl in *.
  destruct (equivocators_transition_item_project IM final_descriptors item)
    as [(ox, final')|] eqn:Hpr_item_x
  ; [|congruence].
  unfold equivocators_transition_item_project in Hpr_item_x.
  unfold composite_transition_item_projection in Hpr_item_x.
  remember (equivocator_vlsm_transition_item_project (IM (projT1 (l item))) (composite_transition_item_projection_from_eq (equivocator_IM IM) item (projT1 (l item)) eq_refl) (final_descriptors (projT1 (l item))))
    as pr_item_x.
  destruct pr_item_x as [(oitem', descriptor')|]; [|congruence].

  unfold composite_transition_item_projection_from_eq in Heqpr_item_x.
  unfold eq_rect_r in Heqpr_item_x.
  simpl in Heqpr_item_x.
  destruct (decide (from_sub_projection (equivocator_IM IM) selection item)).
  - simpl in Hpr_sub_item.
    unfold final_sub_descriptors in *.
    unfold equivocators_transition_item_project in Hpr_sub_item.
    match type of Hpr_sub_item with
    | context [equivocator_vlsm_transition_item_project ?X ?i ?c]
      => remember (equivocator_vlsm_transition_item_project X i c) as project
    end.
    simpl in Heqproject.
    unfold
      composite_transition_item_sub_projection,
      composite_transition_item_projection,
      composite_transition_item_projection_from_eq,
      eq_rect_r,
      composite_state_sub_projection in Heqproject.
    simpl in Heqproject.
    rewrite <-  Heqpr_item_x in Heqproject. clear Heqpr_item_x.
    subst project.
    simpl in Hpr_sub_item.
    split.
    + apply functional_extensionality_dep.
      destruct oitem' as [item'|]
      ; inversion Hpr_sub_item; subst; clear Hpr_sub_item
      ; inversion Hpr_item_x; subst; clear Hpr_item_x
      ; inversion Hpr_item; subst; clear Hpr_item
      ; simpl
      ; intros i
      ; destruct (decide ((proj1_sig i) = projT1 (l item))).
      * rewrite equivocator_descriptors_update_eq_rew with (Heq := e).
        assert (e1 : i = (dec_exist (sub_index_prop selection) (projT1 (l item)) f)).
        { apply dec_sig_eq_iff. assumption. }
        subst i.
        rewrite equivocator_descriptors_update_eq_rew with (Heq := eq_refl).
        simpl in e. replace e with (eq_refl (projT1 (l item))); [reflexivity|].
        apply Eqdep_dec.UIP_dec. assumption.
      * rewrite! equivocator_descriptors_update_neq; [reflexivity | assumption |].
        intro H. elim n. apply dec_sig_eq_iff in H. assumption.
      * rewrite equivocator_descriptors_update_eq_rew with (Heq := e).
        assert (e1 : i = (dec_exist (sub_index_prop selection) (projT1 (l item)) f)).
        { apply dec_sig_eq_iff. assumption. }
        subst i.
        rewrite equivocator_descriptors_update_eq_rew with (Heq := eq_refl).
        simpl in e. replace e with (eq_refl (projT1 (l item))); [reflexivity|].
        apply Eqdep_dec.UIP_dec. assumption.
      * rewrite! equivocator_descriptors_update_neq; [reflexivity | assumption |].
        intro H. elim n. apply dec_sig_eq_iff in H. assumption.
    + destruct oitem' as [item'|]
      ; inversion Hpr_sub_item; subst; clear Hpr_sub_item
      ; inversion Hpr_item_x; subst; clear Hpr_item_x
      ; inversion Hpr_item; subst; clear Hpr_item
      ; simpl; [|reflexivity].
      unfold from_sub_projection. simpl.
      destruct (decide (sub_index_prop selection (projT1 (l item)))); [|contradiction].
      f_equal.
      unfold composite_transition_item_sub_projection. simpl.
      f_equal.
      unfold sub_index.
      apply
        (@dec_sig_sigT_eq _
          (sub_index_prop selection)
          (sub_index_prop_dec selection)
          (fun n => vlabel (IM n))
          (projT1 (l item)) (l item') (l item') s f
        ).
      reflexivity.
  - simpl in Hpr_sub_item. unfold final_sub_descriptors in *.
    inversion Hpr_sub_item. subst. clear Hpr_sub_item.
    split.
    + apply functional_extensionality_dep. intros i.
      assert (Hnot : proj1_sig i <> projT1 (l item)).
      { intro Hnot. elim n. destruct i. simpl in Hnot. subst.
        apply bool_decide_eq_true in e. assumption.
      }
      destruct oitem' as [item'|]
      ; inversion Hpr_item_x; subst; clear Hpr_item_x
      ; inversion Hpr_item; subst; clear Hpr_item
      ; simpl
      ; rewrite equivocator_descriptors_update_neq; [reflexivity| assumption | reflexivity| assumption].
    + destruct oitem' as [item'|]
      ; inversion Hpr_item_x; subst; clear Hpr_item_x
      ; inversion Hpr_item; subst; clear Hpr_item
      ; simpl; [|reflexivity].
      unfold from_sub_projection. simpl.
      destruct (decide (sub_index_prop selection (projT1 (l item)))); [contradiction|].
      reflexivity.
Qed.

Lemma equivocators_trace_project_finite_trace_sub_projection_commute
  (final_descriptors initial_descriptors : equivocator_descriptors IM)
  (initial_sub_descriptors : equivocator_descriptors (sub_IM IM selection))
  (tr : list (composite_transition_item (equivocator_IM IM)))
  (trX : list (composite_transition_item IM))
  (tr_subX : list (composite_transition_item (sub_IM IM selection)))
  (final_sub_descriptors := fun i : sub_index selection => final_descriptors (proj1_sig i))
  (Hproject_tr : equivocators_trace_project IM final_descriptors tr = Some (trX, initial_descriptors))
  (Hproject_sub_tr :
    equivocators_trace_project (sub_IM IM selection) final_sub_descriptors
      (finite_trace_sub_projection (equivocator_IM IM) selection tr)
    = Some (tr_subX, initial_sub_descriptors))
  : initial_sub_descriptors = (fun i => initial_descriptors (proj1_sig i)) /\
    finite_trace_sub_projection IM selection trX = tr_subX.
Proof.
  generalize dependent tr_subX. generalize dependent trX.
  generalize dependent final_descriptors.
  induction tr using rev_ind; intros.
  - simpl in Hproject_tr. inversion Hproject_tr. subst.
    clear Hproject_tr.
    simpl in Hproject_sub_tr.
    inversion Hproject_sub_tr. subst. split; reflexivity.
  - unfold equivocators_trace_project in Hproject_tr.
    rewrite fold_right_app in Hproject_tr.
    match type of Hproject_tr with
    | fold_right _ ?i _ = _ => destruct i as [(projectx,final_descriptors')|] eqn:Hproject_x
    end
    ; [|rewrite equivocators_trace_project_fold_None in Hproject_tr; inversion Hproject_tr].
    apply equivocators_trace_project_folder_additive_iff in Hproject_tr.
    destruct Hproject_tr as [trX0 [HtrX0 HtrX]].
    specialize (IHtr _ _ HtrX0).
    rewrite finite_trace_sub_projection_app in Hproject_sub_tr.
    apply equivocators_trace_project_app_iff in Hproject_sub_tr.
    destruct Hproject_sub_tr as [tr_subX' [project_sub_x [final_sub_descriptors' [Hproject_sub_x [Htr_subX' Heqtr_subX]]]]].
    specialize
      (equivocators_trace_project_finite_trace_sub_projection_item_commute
        x _ _ _ Hproject_x _ _ Hproject_sub_x
      )
      as Hfinal_sub'.

    destruct Hfinal_sub' as [Hfinal_sub' Hpr_sub_x].
    subst final_sub_descriptors'.
    specialize (IHtr _ Htr_subX').
    destruct IHtr as [Heqv_initial Hpr_trXi'].
    split; [assumption|].
    subst.
    apply finite_trace_sub_projection_app.
Qed.

End equivocators_composition_sub_projections.
