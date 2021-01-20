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
  := equivocators_no_equivocations_constraint IM Hbs index_listing finite_index l som
  /\ incl (equivocating_indices IM index_listing (fst som')) equivocating.

Definition equivocators_fixed_equivocations_vlsm
  : VLSM message
  :=
  equivocators_constrained_vlsm IM equivocators_fixed_equivocations_constraint.

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
  (equivocators_choice := equivocators_choice IM)
  (equivocators_state_project := equivocators_state_project IM)
  (equivocator_IM := equivocator_IM IM)
  (equivocators_choice_update := equivocators_choice_update IM)
  (proper_equivocators_choice := proper_equivocators_choice IM)
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
    {index_listing : list index}
    (finite_index : Listing index_listing)
    (equivocating : set index)
    (admissible_index := fun s i => In i equivocating)
    (Hno_resend : forall i : index, cannot_resend_message_stepwise_props (IM i))
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

Context
  {message : Type}
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
  .

Lemma fixed_equivocators_initial_state_project
  (es : vstate XE)
  (Hes : vinitial_state_prop XE es)
  (eqv_choice : equivocators_choice IM)
  (Heqv : proper_equivocators_choice IM eqv_choice es)
  : vinitial_state_prop X (equivocators_state_project IM eqv_choice es).
Proof.
  intro eqv. specialize (Hes eqv).
  unfold equivocator_IM in Hes.
  unfold equivocators_state_project.
  specialize (Heqv eqv). 
  destruct (eqv_choice eqv) as [sn | i fi]; [assumption|].
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

Local Tactic Notation "unfold_transition"  hyp(Ht) :=
  ( unfold transition in Ht; unfold equivocator_IM in Ht;
  unfold equivocator_vlsm in Ht; unfold mk_vlsm in Ht;
  unfold machine in Ht; unfold projT2 in Ht;
  unfold equivocator_vlsm_machine in Ht; unfold equivocator_transition in Ht).

Lemma equivocators_protocol_trace_project
  (final_choice : equivocators_choice IM)
  (is : vstate XE)
  (tr : list (vtransition_item XE))
  (final_state := last (map destination tr) is)
  (Hproper : proper_equivocators_choice IM final_choice final_state)
  (Htr : finite_protocol_trace XE is tr)
  : exists
    (trX : list (vtransition_item X))
    (initial_choice : equivocators_choice IM)
    (isX := equivocators_state_project IM initial_choice is)
    (final_stateX := last (map destination trX) isX),
    proper_equivocators_choice IM initial_choice is /\
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
    
Admitted.  

End from_equivocators_to_nodes.