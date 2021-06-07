Require Import
  List Coq.Vectors.Fin FinFun ListSet
  Arith.Compare_dec Lia Reals
  Program
  Coq.Logic.JMeq
  .
Import ListNotations.
From CasperCBC
  Require Import
    Preamble ListExtras ListSetExtras FinExtras
    Lib.Measurable
    VLSM.Common VLSM.Composition VLSM.Equivocation
    VLSM.Equivocators.Common VLSM.Equivocators.Projections
    VLSM.Equivocators.MessageProperties
    VLSM.Equivocators.Composition.Common
    VLSM.Equivocators.Composition.Projections
    VLSM.DependentMessages
    .

(** * VLSM Limited Equivocation *)

Section limited_state_equivocation.

Context {message : Type}
  {index : Type}
  {IndEqDec : EqDecision index}
  (IM : index -> VLSM message)
  (Hbs : forall i : index, has_been_sent_capability (IM i))
  {i0 : Inhabited index}
  (X := free_composite_vlsm IM)
  {index_listing : list index}
  (finite_index : Listing index_listing)
  (equivocator_descriptors := equivocator_descriptors IM)
  (equivocators_state_project := equivocators_state_project IM)
  (equivocator_IM := equivocator_IM IM)
  (equivocator_descriptors_update := equivocator_descriptors_update IM)
  (proper_equivocator_descriptors := proper_equivocator_descriptors IM)
  (sender : message -> option index)
  {Hmeasurable : Measurable index}
  (equivocating : set index)
  {reachable_threshold : ReachableThreshold index}
  .

Definition equivocators_limited_equivocations_constraint
  (l : composite_label equivocator_IM)
  (som : composite_state equivocator_IM * option message)
  (som' := composite_transition equivocator_IM l som)
  : Prop
  := equivocators_no_equivocations_constraint IM Hbs finite_index l som
  /\ (sum_weights (equivocating_indices IM index_listing (fst som'))
      <= proj1_sig threshold)%R.

Definition equivocators_limited_equivocations_vlsm
  : VLSM message
  :=
  composite_vlsm equivocator_IM equivocators_limited_equivocations_constraint.

End limited_state_equivocation.

Section limited_state_equivocation_with_full_node.

Context {message : Type}
  {index : Type}
  {IndEqDec : EqDecision index}
  (IM : index -> VLSM message)
  (Hbs : forall i : index, has_been_sent_capability (IM i))
  {i0 : Inhabited index}
  (X := free_composite_vlsm IM)
  {index_listing : list index}
  (finite_index : Listing index_listing)
  (equivocator_descriptors := equivocator_descriptors IM)
  (equivocators_state_project := equivocators_state_project IM)
  (equivocator_IM := equivocator_IM IM)
  (equivocator_descriptors_update := equivocator_descriptors_update IM)
  (proper_equivocator_descriptors := proper_equivocator_descriptors IM)
  (equivocating : set index)
  (sender : message -> option index)
  (Hbr : forall i, has_been_received_capability (IM i))
  {Hdm : DependentMessages sender (fun i => i) IM Hbs Hbr}
  {Hmeasurable : Measurable index}
  {reachable_threshold : ReachableThreshold index}
  .

Existing Instance Hdm.

Definition full_node_equivocators_constraint
  (l : composite_label equivocator_IM)
  (som : composite_state equivocator_IM * option message)
  :=
  let (i, ldi) := l in
  let (li, desc) := ldi in
  let (s, om) := som in
  match om with
  | None => True
  | Some m =>
    dependent_messages_local_full_node_condition
      (equivocator_state_descriptor_project (IM i) (s i) desc) m
  end.

Definition full_node_equivocators_limited_equivocation_constraint
  (l : composite_label equivocator_IM)
  (som : composite_state equivocator_IM * option message)
  :=
  full_node_equivocators_constraint l som /\
  equivocators_limited_equivocations_constraint IM Hbs finite_index l som.

Definition full_node_equivocators_limited_equivocation_vlsm : VLSM message :=
  composite_vlsm equivocator_IM full_node_equivocators_limited_equivocation_constraint.

End limited_state_equivocation_with_full_node.

Section limited_message_equivocation.

Context
  {message : Type}
  {index : Type}
  {IndEqDec : EqDecision index}
  {index_listing : list index}
  (finite_index : Listing index_listing)
  {ValMeasurable : Measurable index}
  (IM : index -> VLSM message)
  (Hbs : forall i, has_been_sent_capability (IM i))
  (Hbr : forall i, has_been_received_capability (IM i))
  (Hbo := fun i => has_been_observed_capability_from_sent_received (IM i))
  (i0 : Inhabited index)
  (X := free_composite_vlsm IM)
  (X_has_been_sent_capability : has_been_sent_capability X := composite_has_been_sent_capability IM (free_constraint IM) finite_index Hbs)
  (X_has_been_received_capability : has_been_received_capability X := composite_has_been_received_capability IM (free_constraint IM) finite_index Hbr)
  (X_has_been_observed_capability : has_been_observed_capability X := has_been_observed_capability_from_sent_received X)
  (sender : message -> option index)
  (globally_known_equivocators : composite_state IM -> set index)
  {Hdm : DependentMessages sender (fun i => i) IM Hbs Hbr}
  {reachable_threshold : ReachableThreshold index}
  .

Existing Instance X_has_been_observed_capability.

Lemma additional_equivocations_guarantees_sender
  l s im
  (Hequiv : ~ no_additional_equivocations_constraint X l (s, Some im))
  (Him : protocol_message_prop X im)
  : exists i, sender im = Some i.
Proof.
  destruct (sender im) as [i|] eqn:Hsender; [exists i; reflexivity|].
  specialize (sender_safety sender (fun i => i) IM Hbs Hbr)
    as Hsafety.
  apply can_emit_protocol_iff in Him.
  unfold no_additional_equivocations_constraint, no_additional_equivocations in Hequiv.
  destruct Him as [Him | Him]; [elim Hequiv; right; assumption|].
  apply pre_loaded_with_all_messages_can_emit, can_emit_composite_free_project in Him.
  destruct Him as [i Himi].
  specialize (Hsafety i im Himi).
  congruence.
Qed.

Lemma no_additional_equivocations_constraint_dec
  (Hdec_init : forall i, vdecidable_initial_messages_prop (IM i))
  : RelDecision (no_additional_equivocations_constraint X).
Proof.
  intros l (s, om).
  destruct om; [|left; exact I].
  apply no_additional_equivocations_dec.
  apply (composite_decidable_initial_message IM finite_index).
  assumption.
Qed.

Class known_equivocators_capability :=
  { known_equivocators_nodup :
    forall s, NoDup (globally_known_equivocators s)
  ; known_equivocators_initial_state :
    forall s,
      composite_initial_state_prop IM s ->
      globally_known_equivocators s = []
  ; known_equivocators_transition_no_equiv :
    forall
      l s iom s' oom,
      composite_transition IM l (s, iom) = (s', oom) ->
      no_additional_equivocations_constraint X l (s, iom) ->
      set_eq (globally_known_equivocators s') (globally_known_equivocators s)
  ; known_equivocators_transition_equiv :
    forall
      l s im s' oom v,
      composite_transition IM l (s, Some im) = (s', oom) ->
      ~ no_additional_equivocations_constraint X l (s, Some im) ->
      dependent_messages_global_full_node_condition finite_index s im ->
      sender im = Some v ->
      set_eq
        (globally_known_equivocators s')
        (set_add decide_eq v (globally_known_equivocators s))
  }.

Context
  {Hknown_equivocators : known_equivocators_capability}
  .

Lemma composite_transition_None_known_equivocators
  l s s' oom
  (Ht: composite_transition IM l (s, None) = (s', oom))
  : set_eq (globally_known_equivocators s') (globally_known_equivocators s).
Proof.
  specialize (known_equivocators_transition_no_equiv _ _ _ _ _ Ht) as Heqv.
  spec Heqv. { exact I. }
  assumption.
Qed.

Definition globally_known_equivocators_weight
  (s : composite_state IM)
  : R
  :=
  sum_weights (globally_known_equivocators s).

Lemma initial_state_equivocators_weight
  (s : composite_state IM)
  (Hs : composite_initial_state_prop IM s)
  : globally_known_equivocators_weight s = 0%R.
Proof.
  apply known_equivocators_initial_state in Hs.
  unfold globally_known_equivocators_weight.
  rewrite Hs. reflexivity.
Qed.

Lemma composite_transition_None_equivocators_weight
  l s s' oom
  : composite_transition IM l (s, None) = (s', oom) ->
    globally_known_equivocators_weight s' = globally_known_equivocators_weight s.
Proof.
  intro Ht.
  specialize (composite_transition_None_known_equivocators _ _ _ _ Ht) as Heqv.
  apply
    (set_eq_nodup_sum_weight_eq
      (globally_known_equivocators s')
      (globally_known_equivocators s)
    )
  ; [..|assumption]
  ; apply known_equivocators_nodup.
Qed.

Definition full_node_limited_equivocation_constraint
  (l : composite_label IM)
  (som : composite_state IM * option message)
  :=
  dependent_messages_local_full_node_constraint l som /\
  let s' := fst (composite_transition IM l som) in
  (globally_known_equivocators_weight s' <= proj1_sig threshold)%R.


Definition full_node_limited_equivocation_vlsm_composition
  :=
  composite_vlsm IM full_node_limited_equivocation_constraint.

Lemma full_node_limited_equivocation_protocol_state_weight s
  : protocol_state_prop full_node_limited_equivocation_vlsm_composition s ->
    (globally_known_equivocators_weight s <= proj1_sig threshold)%R.
Proof.
  intro Hs.
  induction Hs using protocol_state_prop_ind.
  - rewrite (initial_state_equivocators_weight s Hs).
    destruct threshold. intuition.
  - destruct Ht as [[Hs [Hom [Hv [Hc Hw]]]] Ht].
    unfold transition in Ht. simpl in Ht.
    simpl in Hw.
    rewrite Ht in Hw.
    assumption.
Qed.

End limited_message_equivocation.

Section limited_equivocation_state_to_message.

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
  (Hbo : forall i : index, has_been_observed_capability (IM i) := fun i => has_been_observed_capability_from_sent_received (IM i))
  (i0 : Inhabited index)
  {index_listing : list index}
  (finite_index : Listing index_listing)
  {ValMeasurable : Measurable index}
  (sender : message -> option index)
  (globally_known_equivocators : composite_state IM -> set index)
  {Hdm : DependentMessages sender (fun i => i) IM Hbs Hbr}
  {Hknown_equivocators : known_equivocators_capability finite_index IM Hbs Hbr i0 sender globally_known_equivocators}
  {reachable_threshold : ReachableThreshold index}
  (XE : VLSM message := full_node_equivocators_limited_equivocation_vlsm IM Hbs finite_index sender Hbr)
  (X : VLSM message := full_node_limited_equivocation_vlsm_composition IM Hbs Hbr i0 sender globally_known_equivocators)
  (equivocators_free_Hbs := composite_has_been_sent_capability (equivocator_IM IM) (free_constraint (equivocator_IM IM)) finite_index (equivocator_Hbs IM Hbs))
  (FreeE : VLSM message := free_composite_vlsm (equivocator_IM IM))
  (FreeE_has_been_sent_capability : has_been_sent_capability FreeE := composite_has_been_sent_capability (equivocator_IM IM) (free_constraint (equivocator_IM IM)) finite_index (equivocator_Hbs IM Hbs))
  (Hdec_init : forall i, vdecidable_initial_messages_prop (IM i))
  (comopsite_initial_decidable := composite_decidable_initial_message IM finite_index Hdec_init)
  (Free := free_composite_vlsm IM)
  (Free_has_been_sent_capability : has_been_sent_capability Free := composite_has_been_sent_capability IM (free_constraint IM) finite_index Hbs)
  (Free_has_been_received_capability : has_been_received_capability Free := composite_has_been_received_capability IM (free_constraint IM) finite_index Hbr)
  (Free_has_been_observed_capability : has_been_observed_capability Free := has_been_observed_capability_from_sent_received Free)
  (Free_no_additional_equivocation_decidable := no_additional_equivocations_dec Free comopsite_initial_decidable)
  (Free_no_additional_equivocation_constraint_dec : RelDecision (no_additional_equivocations_constraint Free):= no_additional_equivocations_constraint_dec finite_index IM Hbs Hbr i0 Hdec_init)
  .


(**
Inclusion in the free composition
*)
Lemma equivocators_limited_equivocations_vlsm_incl_free
  : VLSM_incl XE (free_composite_vlsm (equivocator_IM IM)).
Proof.
  apply constraint_subsumption_incl.
  intros l som H. exact I.
Qed.

(**
Inclusion in the free composition
*)
Lemma equivocators_limited_equivocations_vlsm_incl_preloaded_free
  : VLSM_incl XE (pre_loaded_with_all_messages_vlsm (free_composite_vlsm (equivocator_IM IM))).
Proof.
  specialize equivocators_limited_equivocations_vlsm_incl_free as Hincl1.
  specialize (vlsm_incl_pre_loaded_with_all_messages_vlsm (free_composite_vlsm (equivocator_IM IM)))
    as Hincl2.
  revert Hincl1 Hincl2.
  apply VLSM_incl_trans.
Qed.


(**
Inclusion in the composition of equivocators with no message equivocation
(no restriction on state equivocation).
*)
Lemma equivocators_limited_equivocations_vlsm_incl_no_equivocations
  : VLSM_incl XE (equivocators_no_equivocations_vlsm IM Hbs finite_index).
Proof.
  apply constraint_subsumption_incl.
  intros l som H. apply H.
Qed.


Existing Instance i0.


Lemma limited_equivocators_initial_state_project
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

(* A protocol state for a VLSM satisfying the limited equivocation assumption
has limited equivocation.
*)
Lemma protocol_state_limited_equivocation
  (s : composite_state (equivocator_IM IM))
  (Hs : protocol_state_prop XE s)
  : (sum_weights (equivocating_indices IM index_listing s) <= (proj1_sig threshold))%R
  .
Proof.
  apply protocol_state_prop_iff in Hs.
  destruct Hs as [[(is, His) Heq_s] | [l [(s0, oim) [oom' [[_ [_ [_ [_ [_ Hlimited]]]]] Ht]]]]].
  - subst s. simpl.
    replace (equivocating_indices IM index_listing is) with (@nil index).
    + destruct threshold as [t Ht]. simpl. apply Rge_le. assumption.
    + symmetry. apply filter_nil. apply Forall_forall. intros.
      apply bool_decide_eq_false. spec His x.
      destruct His as [Hzero His].
      intro. contradiction.
  - replace s with
    (fst (composite_transition (equivocator_IM IM) l (s0, oim))); [assumption|].
    simpl in *. rewrite Ht. reflexivity.
Qed.

End limited_equivocation_state_to_message.
