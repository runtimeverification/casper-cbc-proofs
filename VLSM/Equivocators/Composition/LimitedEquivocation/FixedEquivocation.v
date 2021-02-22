Require Import
  List Coq.Vectors.Fin FinFun ListSet
  Arith.Compare_dec Lia
  Program Program.Equality
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
    VLSM.Equivocators.Composition.Projections
    .

Section equivocators_fixed_equivocations_vlsm.

Context
  {message : Type}
  {index : Type}
  {IndEqDec : EqDecision index}
  (IM : index -> VLSM message)
  (Hbs : forall i : index, has_been_sent_capability (IM i))
  {i0 : Inhabited index}
  (equivocator_IM := equivocator_IM IM)
  {index_listing : list index}
  (finite_index : Listing index_listing)
  (equivocating : set index)
  .

Definition equivocators_fixed_equivocations_constraint
  (l : composite_label equivocator_IM)
  (som : composite_state equivocator_IM * option message)
  (som' := composite_transition equivocator_IM l som)
  : Prop
  := equivocators_no_equivocations_constraint IM Hbs finite_index l som
  /\ incl (equivocating_indices IM index_listing (fst som')) equivocating.

Definition equivocators_fixed_equivocations_vlsm
  : VLSM message
  :=
  composite_vlsm equivocator_IM equivocators_fixed_equivocations_constraint.

Lemma equivocators_fixed_equivocations_vlsm_incl_free
  : VLSM_incl equivocators_fixed_equivocations_vlsm (free_composite_vlsm equivocator_IM).
Proof.
  apply constraint_subsumption_incl.
  intros l som H. exact I.
Qed.

Lemma equivocators_fixed_equivocations_vlsm_incl_no_equivocations
  : VLSM_incl equivocators_fixed_equivocations_vlsm (equivocators_no_equivocations_vlsm IM Hbs finite_index).
Proof.
  apply constraint_subsumption_incl.
  intros l som H. apply H.
Qed.

End equivocators_fixed_equivocations_vlsm.

Section fixed_equivocation_without_fullnode.

Context
  {message : Type}
  {index : Type}
  {IndEqDec : EqDecision index}
  (IM : index -> VLSM message)
  (Hbs : forall i : index, has_been_sent_capability (IM i))
  (Hbr : forall i : index, has_been_received_capability (IM i))
  {i0 : Inhabited index}
  (X := free_composite_vlsm IM)
  {index_listing : list index}
  (finite_index : Listing index_listing)
  (X_has_been_sent_capability : has_been_sent_capability X := composite_has_been_sent_capability IM (free_constraint IM) finite_index Hbs)
  (X_has_been_received_capability : has_been_received_capability X := composite_has_been_received_capability IM (free_constraint IM) finite_index Hbr)
  (X_has_been_observed_capability : has_been_observed_capability X := has_been_observed_capability_from_sent_received X)
  (equivocator_descriptors := equivocator_descriptors IM)
  (equivocators_state_project := equivocators_state_project IM)
  (equivocator_IM := equivocator_IM IM)
  (equivocator_descriptors_update := equivocator_descriptors_update IM)
  (proper_equivocator_descriptors := proper_equivocator_descriptors IM)
  (equivocating : set index)
  (Hi0_equiv : equivocating <> [])
  .

Existing Instance X_has_been_observed_capability.

Definition index_equivocating_prop (i : index) : Prop := In i equivocating.

Local Instance index_equivocating_prop_dec
  (i : index)
  : Decision (index_equivocating_prop i).
Proof.
  apply in_dec. assumption.
Qed.

Definition equivocating_index : Type
  := dec_sig index_equivocating_prop.

Local Instance equivocating_i0 : Inhabited equivocating_index.
Proof.
  split.
  destruct (destruct_list equivocating) as [[x [tl Hequivocating]]| n]
  ; [|elim Hi0_equiv; assumption].
  exists x. apply bool_decide_eq_true.
  unfold index_equivocating_prop. subst equivocating. left. reflexivity.
Qed.

Local Instance equivocating_index_eq_dec : EqDecision equivocating_index.
Proof.
  apply dec_sig_eq_dec. assumption.
Qed.

Definition equivocating_IM
  (ei : equivocating_index)
  : VLSM message
  := IM (proj1_sig ei).

Definition free_equivocating_vlsm_composition : VLSM message
  := free_composite_vlsm equivocating_IM.

Definition seeded_free_equivocators_composition
  (messageSet : message -> Prop)
  := vlsm_add_initial_messages free_equivocating_vlsm_composition
      (fun m => messageSet m \/ vinitial_message_prop X m).

Context
  {validator : Type}
  .

Definition fixed_equivocation_constraint
  (l : composite_label IM)
  (som : composite_state IM * option message)
  : Prop
  :=
  no_additional_equivocations_constraint X l som \/
  let (s, om) := som in
  exists m : message, om = Some m /\
  can_emit (seeded_free_equivocators_composition (no_additional_equivocations X s)) m.

Definition fixed_equivocation_vlsm_composition : VLSM message
  := composite_vlsm IM fixed_equivocation_constraint.

End fixed_equivocation_without_fullnode.

Section fixed_equivocation_with_fullnode.
  Context
    {message : Type}
    (index : Type)
    {IndEqDec : EqDecision index}
    (IM : index -> VLSM message)
    (Hbs : forall i : index, has_been_sent_capability (IM i))
    (Hbr : forall i : index, has_been_received_capability (IM i))
    {i0 : Inhabited index}
    (equivocator_IM := equivocator_IM IM)
    (index_listing : list index)
    (finite_index : Listing index_listing)
    (equivocating : set index)
    (admissible_index := fun s i => In i equivocating)
    (Hno_resend : forall i : index, cannot_resend_message_stepwise_prop (IM i))
    (full_node_constraint
      := full_node_condition_for_admissible_equivocators IM Hbs Hbr finite_index admissible_index)
    (full_node_constraint_alt
      := full_node_condition_for_admissible_equivocators_alt IM Hbs Hbr finite_index admissible_index)
    .

  Section fixed_equivocation_constraint_comparison.

  Context
    `{EqDecision message}
    (Hi0_equiv : equivocating <> [])
    (equivocating_inhabited : Inhabited (equivocating_index equivocating) := equivocating_i0 _ Hi0_equiv)
    {validator : Type}
    (A : validator -> index)
    (sender : message -> option validator)
    (fixed_equivocation_constraint : composite_label IM  -> composite_state IM * option message -> Prop
      := fixed_equivocation_constraint IM Hbs Hbr finite_index equivocating Hi0_equiv)
    (Hsender_safety : Prop := sender_safety_prop IM (free_constraint IM) A sender)
    (X := free_composite_vlsm IM)
    (X_has_been_sent_capability : has_been_sent_capability X := composite_has_been_sent_capability IM (free_constraint IM) finite_index Hbs)
    (X_has_been_received_capability : has_been_received_capability X := composite_has_been_received_capability IM (free_constraint IM) finite_index Hbr)
    (X_has_been_observed_capability : has_been_observed_capability X := has_been_observed_capability_from_sent_received X)
    .

  Local Instance index_equivocating_dec
    (i : index)
    : Decision (index_equivocating_prop equivocating i).
  Proof.
    apply index_equivocating_prop_dec.
  Qed.

  Existing Instance  equivocating_inhabited.
  Existing Instance  equivocating_index_eq_dec.

  Existing Instance X_has_been_observed_capability.
  Lemma fixed_equivocation_constraint_subsumption :
    preloaded_constraint_subsumption IM full_node_constraint fixed_equivocation_constraint.
  Proof.
    cut (preloaded_constraint_subsumption IM full_node_constraint_alt fixed_equivocation_constraint).
    {
      intros H s Hs l om Hfull.
      apply H; [assumption|].
      apply
        (@full_node_condition_for_admissible_equivocators_subsumption
          _ _ _ _ IM _ Hbs Hbr _ finite_index
          admissible_index
          Hno_resend
        ); [assumption|].
      assumption.
    }
    intros s Hs l om [Hno_equiv | Hfull]; [left; assumption|].
    destruct Hfull as [m [Hom [i [Hi Hm]]]].
    subst om.
    right. exists m. split; [reflexivity|].
    remember (no_additional_equivocations (free_composite_vlsm IM) s) as P.
    unfold seeded_free_equivocators_composition.
    remember (fun m => P m \/ vinitial_message_prop (free_composite_vlsm IM) m) as Q.
    unfold free_equivocating_vlsm_composition.
    specialize (can_emit_composite_free_lift (equivocating_IM IM equivocating) P Q) as Hemit.
    spec Hemit. { intros. subst Q. left. assumption. }
    assert
      (Hi_dec :
        @bool_decide
          (@index_equivocating_prop index equivocating i)
          (@index_equivocating_prop_dec index IndEqDec equivocating i) = true).
    { apply bool_decide_eq_true. assumption. }
    specialize (Hemit (exist _  i Hi_dec)).
    apply Hemit.
    unfold equivocating_IM. simpl. assumption.
  Qed.

  End fixed_equivocation_constraint_comparison.
End fixed_equivocation_with_fullnode.

Section from_equivocators_to_nodes.

(** ** From composition of equivocators to composition of simple nodes

In this section we show that the projection of [protocol_trace]s of a
composition of equivocators with a fixed equivocation constraint are
[protocol_trace]s for the composition of nodes with a similar fixed
equivocation constraint.
*)

Context
  {message : Type}
  `{EqDecision message}
  (index : Type)
  {IndEqDec : EqDecision index}
  (IM : index -> VLSM message)
  (Hbs : forall i : index, has_been_sent_capability (IM i))
  (Hbr : forall i : index, has_been_received_capability (IM i))
  {i0 : Inhabited index}
  {index_listing : list index}
  (finite_index : Listing index_listing)
  (equivocating : set index)
  (XE : VLSM message := equivocators_fixed_equivocations_vlsm IM Hbs finite_index equivocating)
  (Hi0_equiv : equivocating <> [])
  (X : VLSM message := fixed_equivocation_vlsm_composition IM Hbs Hbr finite_index equivocating Hi0_equiv)
  (equivocators_free_Hbs := composite_has_been_sent_capability (equivocator_IM IM) (free_constraint (equivocator_IM IM)) finite_index (equivocator_Hbs IM Hbs))
  (FreeE : VLSM message := free_composite_vlsm (equivocator_IM IM))
  (Hdec_init : forall i, vdecidable_initial_messages_prop (IM i))
  (comopsite_initial_decidable := composite_decidable_initial_message IM finite_index Hdec_init)
  (Free := free_composite_vlsm IM)
  (Free_has_been_sent_capability : has_been_sent_capability Free := composite_has_been_sent_capability IM (free_constraint IM) finite_index Hbs)
  (Free_has_been_received_capability : has_been_received_capability Free := composite_has_been_received_capability IM (free_constraint IM) finite_index Hbr)
  (Free_has_been_observed_capability : has_been_observed_capability Free := has_been_observed_capability_from_sent_received Free)
  (Free_no_additional_equivocation_decidable := no_additional_equivocations_dec Free comopsite_initial_decidable)
  .

Existing Instance equivocators_free_Hbs.

Lemma fixed_equivocators_initial_state_project
  (es : vstate XE)
  (Hes : vinitial_state_prop XE es)
  (eqv_descriptors : equivocator_descriptors IM)
  (Heqv : proper_equivocator_descriptors IM eqv_descriptors es)
  : vinitial_state_prop X (equivocators_state_project IM eqv_descriptors es).
Proof.
  intro eqv. specialize (Hes eqv).
  unfold equivocator_IM in Hes.
  unfold equivocators_state_project.
  specialize (Heqv eqv).
  destruct (eqv_descriptors eqv) as [sn | i fi]; [assumption|].
  destruct Hes as [Hzero Hes].
  destruct (es eqv) as (n, bs). simpl in Heqv.
  destruct (le_lt_dec (S n) i); [lia|].
  simpl in *.
  subst. assert (Hi: i = 0) by lia. subst.
  assumption.
Qed.

Lemma fixed_equivocators_initial_message
  (m : message)
  (Hem : vinitial_message_prop XE m)
  : vinitial_message_prop X m.
Proof.
  destruct Hem as [eqv [emi Hem]].
  exists eqv.
  unfold equivocator_IM in emi.
  exists emi. assumption.
Qed.

Lemma equivocators_protocol_trace_project
  (final_choice : equivocator_descriptors IM)
  (is : vstate XE)
  (tr : list (vtransition_item XE))
  (final_state := last (map destination tr) is)
  (Hproper : proper_equivocator_descriptors IM final_choice final_state)
  (Htr : finite_protocol_trace XE is tr)
  : exists
    (trX : list (vtransition_item X))
    (initial_choice : equivocator_descriptors IM)
    (isX := equivocators_state_project IM initial_choice is)
    (final_stateX := last (map destination trX) isX),
    proper_equivocator_descriptors IM initial_choice is /\
    equivocators_trace_project IM final_choice tr = Some (trX, initial_choice) /\
    equivocators_state_project IM final_choice final_state = final_stateX /\
    finite_protocol_trace X isX trX.
Proof.
  remember (length tr) as len_tr.
  generalize dependent final_choice. generalize dependent tr.
  induction len_tr using (well_founded_induction Wf_nat.lt_wf); intros.
  subst len_tr.
  destruct_list_last tr tr' lst Htr_lst.
  - clear H. subst. unfold final_state in *. exists [], final_choice.
    split; [assumption|]. split; [reflexivity|]. split; [reflexivity|].
    remember (equivocators_state_project IM final_choice is) as isx.
    cut (vinitial_state_prop X isx).
    { intro. split; [|assumption]. constructor.
      apply protocol_state_prop_iff. left.
      exists (exist _ _ H). reflexivity.
    }
    subst.
    apply fixed_equivocators_initial_state_project; [|assumption].
    apply Htr.
  - specialize (H (length tr')) as H'.
    spec H'. { rewrite app_length. simpl. lia. }
    destruct Htr as [Htr Hinit].
    apply finite_protocol_trace_from_app_iff in Htr.
    destruct Htr as [Htr Hlst].
    specialize (H' tr' (conj Htr Hinit) eq_refl).
    specialize (equivocators_transition_item_project_proper_characterization IM final_choice lst) as Hproperx.
    unfold final_state in Hproper. rewrite Htr_lst in Hproper.
    rewrite map_app in Hproper. simpl in Hproper. rewrite last_is_last in Hproper.
    spec Hproperx Hproper.
    destruct Hproperx as [oitem [final_choice' [Hprojectx [Hitemx Hproperx]]]].
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
    destruct H' as [trX' [initial_choice [Hproper_initial [Htr_project [Hstate_project HtrX']]]]].
    destruct oitem as [item|].
    +  simpl in Hitemx. destruct Hitemx as [Hl [Hinput [Houtput Hdestination]]].
      specialize (Hx _ eq_refl).
      destruct Hx as [Hvx Htx].
      exists (trX' ++ [item]), initial_choice. subst foldx.
      rewrite equivocators_trace_project_folder_additive with (trX := trX') (eqv_descriptors := initial_choice)
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
      assert (Hplst : protocol_state_prop X lst).
      { apply finite_ptrace_last_pstate in HtrX'. subst. assumption. }
      apply (extend_right_finite_trace_from X lst []); [constructor; assumption|].
      simpl in Hl. subst.
      simpl in Hc.
      destruct Hc as [[Hno_equiv _] Hfixed].
      simpl in Htx,Hvx,Hstate_project.
      rewrite Hstate_project in Hvx, Htx.
      destruct input as [input|]
      ; [|repeat split; [assumption| apply option_protocol_message_None |assumption| left; exact I |assumption]].

      simpl in Hno_equiv.
      apply or_comm in Hno_equiv.
      destruct Hno_equiv as [Hinit_input | Hno_equiv]
      ; [apply fixed_equivocators_initial_message in Hinit_input|]
      ; [repeat split; [assumption| |assumption| left; right;assumption |assumption]|].
      { apply protocol_message_prop_iff. left. exists (exist _ _ Hinit_input).
        reflexivity.
      }
      assert
        (Hs_free : protocol_state_prop FreeE (last (map Common.destination tr') is)).
      { destruct Hs as [_om Hs].
        apply (constraint_subsumption_protocol_prop (equivocator_IM IM))
          with (constraint2 := free_constraint (equivocator_IM IM))
          in Hs as Hs_free
          ; [|intro x; intros; exact I].
        exists _om. assumption.
      }
      specialize
        (specialized_proper_sent_rev FreeE _ Hs_free _ Hno_equiv) as Hall.
      specialize (Hall is tr').
      assert
        (Htr' : finite_protocol_trace FreeE is tr').
      {  split; [|assumption].
        apply VLSM_incl_finite_protocol_trace_from; [apply equivocators_fixed_equivocations_vlsm_incl_free|].
        assumption.
      }
      spec Hall Htr'.
      specialize (Hall eq_refl).
      assert
        (Htr'pre : finite_protocol_trace (pre_loaded_with_all_messages_vlsm FreeE) is tr').
      { split; [|assumption].
        specialize (vlsm_incl_pre_loaded_with_all_messages_vlsm FreeE) as Hincl.
        apply (VLSM_incl_finite_protocol_trace_from _ _ Hincl). apply Htr'.
      }
      destruct (equivocators_trace_project_output_reflecting_inv IM _ _ (proj1 Htr'pre) _ Hall)
        as [final_choice_m [initial_choice_m [trXm [Hfinal_choice_m [Hproject_trXm Hex]]]]].
      specialize (H (length tr')).
      spec H. { rewrite app_length. simpl. lia. }
      specialize (H tr' (conj Htr Hinit) eq_refl final_choice_m Hfinal_choice_m).
      destruct H as [trXm' [initial_choice_m' [Hproper_initial_m [Hproject_trXm' [Hpr_fin_tr' HtrXm]]]]].
      simpl in *. rewrite Hproject_trXm in Hproject_trXm'.
      inversion Hproject_trXm'. subst trXm' initial_choice_m'. clear Hproject_trXm'.
      repeat split; [assumption| |assumption| |assumption]
      ; [ apply option_protocol_message_Some
        ; apply (protocol_trace_output_is_protocol X _ _ (proj1 HtrXm) _ Hex)
        |].
      match goal with
      |- fixed_equivocation_constraint _ _ _ _ _ _ _ (?s, Some ?m) =>
        destruct (Free_no_additional_equivocation_decidable s m)
      end
      ; [left; assumption|right].
      exists input. split; [reflexivity|].
      unfold no_additional_equivocations in n.
      match type of n with
      | ~ (?o \/ ?i) => assert (Hn : ~ o /\ ~ i) by intuition
      end.
      clear n; destruct Hn as [Hno Hni].
      match type of Hno with
      | ~ has_been_observed _ ?s _ => remember s as lst_trX'
      end.
      admit.
    + exists trX'. exists initial_choice. subst foldx. split; [assumption|].
      split; [apply Htr_project|]. split; [|assumption].
      subst tr. clear -Hstate_project Hx.
      rewrite Hstate_project in Hx.
      rewrite <- Hx. f_equal. unfold final_state.
      rewrite map_app. simpl. rewrite last_is_last. reflexivity.
Admitted.

End from_equivocators_to_nodes.
