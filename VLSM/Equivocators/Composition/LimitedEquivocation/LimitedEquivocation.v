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
    VLSM.MessageDependencies
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
  {Hdm : MessageDependencies sender (fun i => i) IM Hbs Hbr}
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
    message_dependencies_local_full_node_condition
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
  {Hdm : MessageDependencies sender (fun i => i) IM Hbs Hbr}
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
      message_dependencies_global_full_node_condition finite_index s im ->
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
  message_dependencies_local_full_node_constraint l som /\
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
  {Hdm : MessageDependencies sender (fun i => i) IM Hbs Hbr}
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

Existing Instance equivocators_free_Hbs.
Existing Instance Free_has_been_observed_capability.
Existing Instance Free_has_been_sent_capability.

(**
This is a property of the [full_node_limited_equivocation_constraint] which also
trivially holds for the free constraint.  This property is sufficient for
proving the [_equivocators_protocol_trace_project] lemma,
which lets that lemma be used for both the composition of equivocators with
full-node limited state-equivocation and the free composition.

It basically says that if a message can be received by a state in the
composition of equivocators with no-message equivocations, satisfying the
full-node condition, and limited state-equivocations, then it can also be
received by any of its projections which are consistent with some meaningful
continuation of the trace upon receiving the message.
*)
Definition full_node_limited_equivocation_constraint_sufficient_condition_prop
  (constraint : composite_label IM -> composite_state IM * option message -> Prop)
  : Prop :=
  forall
    (s : composite_state (equivocator_IM IM))

    (l: composite_label (equivocator_IM IM))
    (input: message)

    (s1: composite_state (equivocator_IM IM))
    (output: option message)
    (item := @Build_transition_item _ (composite_type (equivocator_IM IM)) l (Some input) s1 output)

    (tr: list transition_item)
    (original_state: vstate (free_composite_vlsm (equivocator_IM IM)))
    (Htr: finite_protocol_trace_from_to XE s original_state (item :: tr))

    (original_descriptors: equivocator_descriptors IM)
    (Hnot_equivocating: not_equivocating_equivocator_descriptors IM original_descriptors original_state)

    (s1_descriptors : equivocator_descriptors IM)
    (trX: list (composite_transition_item IM))
    (Htr_project: equivocators_trace_project IM original_descriptors tr = Some (trX, s1_descriptors))

    (s_descriptors: equivocator_descriptors IM)

    (itemX : composite_transition_item IM)
    (Hitem_project: equivocators_transition_item_project IM s1_descriptors item = Some (Some itemX, s_descriptors)),

    constraint
      (Common.l itemX)
      (equivocators_state_project IM s_descriptors s, Some input).

(**
Generic proof that the projection of a trace of the composition of equivocators
with no message equivocation and fixed state equivocation is protocol w.r.t.
the composition of the regular nodes constrained by any constraint satisfying
several properties, including the [constraint_has_been_sent_prop]erty.

The proof proceeds by well founded induction on the length of the trace,
performing an analysis on the final transition item of the trace.

It uses the fact that the trace hase no message equivocation to extract a
subtrace producing the message being received at the last transition and
proves that it's a protocol message for the destination machine by using
the induction hypothesis (that is why well-founded induction is used rather
than a simpler induction principle).

The constraint satisfaction for the projection of the final transition is
for now assumes as hypothesis @Hconstraint_hbs@.
*)
Lemma _equivocators_protocol_trace_project
  (final_descriptors : equivocator_descriptors IM)
  (is : composite_state (equivocator_IM IM))
  (tr : list (composite_transition_item (equivocator_IM IM)))
  (final_state := finite_trace_last is tr)
  original_descriptors
  original_state
  (Hnot_equivocating : not_equivocating_equivocator_descriptors IM original_descriptors original_state)
  original_tr_suf
  (Horiginal_tr_suf : finite_protocol_trace_from_to XE final_state original_state original_tr_suf)
  original_tr_sufX
  (Horiginal_project : equivocators_trace_project IM original_descriptors original_tr_suf = Some (original_tr_sufX, final_descriptors))
  (Htr : finite_protocol_trace XE is tr)
  (constraint : composite_label IM -> composite_state IM * option message -> Prop)
  (X' := composite_vlsm IM constraint)
  (HconstraintNone : forall l s, protocol_state_prop X' s -> constraint l (s, None))
  (Hconstraintinitial : forall l s m, protocol_state_prop X' s -> vinitial_message_prop FreeE m -> constraint l (s, Some m))
  (Hconstraint_hbs :  full_node_limited_equivocation_constraint_sufficient_condition_prop constraint)
  : exists
    (trX : list (composite_transition_item IM))
    (initial_descriptors : equivocator_descriptors IM)
    (isX := equivocators_state_project IM initial_descriptors is)
    (final_stateX := finite_trace_last isX trX),
    proper_equivocator_descriptors IM initial_descriptors is /\
    equivocators_trace_project IM final_descriptors tr = Some (trX, initial_descriptors) /\
    equivocators_state_project IM final_descriptors final_state = final_stateX /\
    finite_protocol_trace X' isX trX.
Proof.
  remember (length tr) as len_tr.
  generalize dependent  original_tr_sufX .
  generalize dependent original_descriptors.
  generalize dependent original_state.
  generalize dependent original_tr_suf.
  generalize dependent final_descriptors. generalize dependent tr.
  induction len_tr using (well_founded_induction Wf_nat.lt_wf); intros.
  subst len_tr.
  apply not_equivocating_equivocator_descriptors_proper in Hnot_equivocating as Horiginal_proper.
  specialize
    (preloaded_equivocators_protocol_trace_project_proper_initial IM final_state original_tr_suf)
    as Hproper.
  simpl in Hproper.
  spec Hproper.
  { apply finite_protocol_trace_from_to_forget_last in Horiginal_tr_suf.
    revert Horiginal_tr_suf.
    apply VLSM_incl_finite_protocol_trace_from.
    apply equivocators_limited_equivocations_vlsm_incl_preloaded_free.
  }
  specialize (Hproper _ _ _ Horiginal_project).
  spec Hproper.
  { apply finite_protocol_trace_from_to_last in Horiginal_tr_suf as Heq_original_state.
    simpl in Heq_original_state. simpl.
    rewrite Heq_original_state. assumption.
  }
  destruct_list_last tr tr' lst Htr_lst.
  - clear H. subst. unfold final_state in *. exists [], final_descriptors.
    split; [assumption|]. split; [reflexivity|]. split; [reflexivity|].
    remember (equivocators_state_project IM final_descriptors is) as isx.
    cut (vinitial_state_prop X' isx).
    { intro. split; [|assumption]. constructor.
      apply protocol_state_prop_iff. left.
      exists (exist _ _ H). reflexivity.
    }
    subst.
    apply limited_equivocators_initial_state_project; [|apply Hproper].
    apply Htr.
  - specialize (H (length tr')) as H'.
    spec H'. { rewrite app_length. simpl. lia. }
    destruct Htr as [Htr Hinit].
    apply finite_protocol_trace_from_app_iff in Htr.
    destruct Htr as [Htr Hlst].
    specialize (H' tr' (conj Htr Hinit) eq_refl).
    specialize (equivocators_transition_item_project_proper_descriptor_characterization IM final_descriptors lst) as Hproperx.
    specialize
      (equivocators_transition_item_project_preserves_zero_descriptors IM final_descriptors lst)
      as Hzero.
    unfold final_state in Hproper.
    rewrite Htr_lst, finite_trace_last_is_last in Hproper.
    spec Hproperx (Hproper (projT1 (l lst))).
    destruct Hproperx as [oitem [final_descriptors' [Hprojectx [Hitemx Hproperx]]]].
    assert (Horiginal_project' : exists original_tr_sufX', equivocators_trace_project IM original_descriptors (lst :: original_tr_suf) = Some (original_tr_sufX', final_descriptors')).
    { change (lst :: original_tr_suf) with ([lst] ++ original_tr_suf).
      destruct oitem as [item|].
      - exists (item :: original_tr_sufX).
        apply equivocators_trace_project_app_iff.
        exists [item], original_tr_sufX, final_descriptors.
        split; [assumption|]. split; [|reflexivity].
        simpl. rewrite Hprojectx. reflexivity.
      - exists original_tr_sufX.
        apply equivocators_trace_project_app_iff.
        exists [], original_tr_sufX, final_descriptors.
        split; [assumption|]. split; [|reflexivity].
        simpl. rewrite Hprojectx. reflexivity.
    }
    destruct Horiginal_project' as [original_tr_sufX' Horiginal_project'].
    specialize (Hproperx (finite_trace_last is tr')).
    unfold equivocators_trace_project.
    rewrite fold_right_app.
    match goal with
    |- context [fold_right _ ?fld _] => remember fld as foldx
    end.
    simpl in Heqfoldx.
    rewrite Hprojectx in Heqfoldx.
    assert
      (Horiginal_tr_suf' : finite_protocol_trace_from_to XE  (finite_trace_last is tr') original_state ([lst] ++ original_tr_suf)).
    { apply finite_protocol_trace_from_to_app with (destination lst).
      - destruct lst. simpl.  apply finite_ptrace_from_to_singleton. inversion Hlst. assumption.
      - subst tr final_state. clear -Horiginal_tr_suf.
        rewrite finite_trace_last_is_last in Horiginal_tr_suf. assumption.
    }
    apply first_transition_valid in Hlst. destruct lst as (l, iom, s, oom). simpl in *.
    destruct Hlst as [Hpv Ht].
    assert (Hpv' := Hpv).
    destruct Hpv' as [Hs [Hiom [Hv Hc]]].
    specialize (Hzero oitem final_descriptors' _ Ht Hv Hprojectx).
    specialize (Hproperx Hv Ht).
    destruct Hproperx as [Hproperi' [Hdescriptors' [Hlst' Hx]]].

    specialize (H' final_descriptors' _ _ Horiginal_tr_suf' _ Hnot_equivocating  _ Horiginal_project').
    destruct H' as [trX' [initial_descriptors [Hproper_initial [Htr_project [Hstate_project HtrX']]]]].
    assert
      (Htr' : finite_protocol_trace FreeE is tr').
    {  split; [|assumption].
      apply VLSM_incl_finite_protocol_trace_from with (machine XE); [apply equivocators_limited_equivocations_vlsm_incl_free|].
      assumption.
    }
    assert
      (Htr'pre : finite_protocol_trace (pre_loaded_with_all_messages_vlsm FreeE) is tr').
    { split; [|assumption].
      specialize (vlsm_incl_pre_loaded_with_all_messages_vlsm FreeE) as Hincl.
      apply (VLSM_incl_finite_protocol_trace_from _ _ Hincl). apply Htr'.
    }
    assert (Hproper' : proper_equivocator_descriptors IM final_descriptors'  (finite_trace_last is tr')).
    { clear -Hproperi' Hdescriptors' Hlst' Hproper.
      intro i. destruct (decide (i = projT1 l)).
      - subst. assumption.
      - rewrite Hdescriptors'. rewrite equivocator_descriptors_update_neq by apply n.
        rewrite Hlst'. rewrite state_update_neq by apply n.
        apply Hproper.
    }
    destruct oitem as [item|].
    +  simpl in Hitemx. destruct Hitemx as [Hl [Hinput [Houtput [Hdestination Hdescriptorsi']]]].
      specialize (Hx _ eq_refl).
      destruct Hx as [Hvx Htx].
      exists (trX' ++ [item]), initial_descriptors. subst foldx.
      rewrite equivocators_trace_project_folder_additive with (trX := trX') (eqv_descriptors := initial_descriptors)
      ; [|assumption].
      split; [assumption|].
      split; [reflexivity|].
      rewrite finite_trace_last_is_last.
      unfold final_state. subst tr.
      rewrite finite_trace_last_is_last.
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
      assert (Hplst : protocol_state_prop X' lst).
      { apply finite_ptrace_last_pstate in HtrX'. subst. assumption. }
      apply (extend_right_finite_trace_from X'); [constructor; assumption|].
      simpl in Hl. subst.
      simpl in Hc.
      destruct Hc as [Hfull [[Hno_equiv _] _]].
      simpl in Htx,Hvx,Hstate_project.
      rewrite Hstate_project in Hvx, Htx.
      destruct input as [input|]
      ; [|repeat split; [assumption| apply option_protocol_message_None |assumption| apply HconstraintNone; assumption |assumption]].
      simpl in Hno_equiv.
      apply or_comm in Hno_equiv.
      destruct Hno_equiv as [Hinit_input | Hno_equiv].
      { repeat split; [assumption | | assumption| | assumption].
        - apply protocol_message_prop_iff. left. exists (exist _ _ Hinit_input).
          reflexivity.
        - apply Hconstraintinitial; [assumption|].
          destruct Hinit_input as [eqv [emi Hem]].
          exists eqv, emi. assumption.
      }
      assert
        (Hs_free : protocol_state_prop FreeE (finite_trace_last is tr')).
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
      spec Hall (ptrace_add_default_last Htr').
      destruct (equivocators_trace_project_output_reflecting_inv IM _ _ (proj1 Htr'pre) _ Hall)
        as [final_descriptors_m [initial_descriptors_m [trXm [_Hfinal_descriptors_m [Hproject_trXm Hex]]]]].
      assert (Hfinal_descriptors_m : proper_equivocator_descriptors IM final_descriptors_m (last (map Common.destination tr') is)).
      { apply not_equivocating_equivocator_descriptors_proper. assumption. }
      specialize (H (length tr')).
      spec H. { rewrite app_length. simpl. lia. }
      specialize (H tr' (conj Htr Hinit) eq_refl final_descriptors_m [] (finite_trace_last is tr')).
      spec H.  { constructor. assumption.  }
      specialize (H _ _Hfinal_descriptors_m [] eq_refl).
      destruct H as [trXm' [initial_descriptors_m' [Hproper_initial_m [Hproject_trXm' [Hpr_fin_tr' HtrXm]]]]].
      simpl in *. rewrite Hproject_trXm in Hproject_trXm'.
      inversion Hproject_trXm'. subst trXm' initial_descriptors_m'. clear Hproject_trXm'.
      repeat split; [assumption| |assumption| |assumption]
      ; [ apply option_protocol_message_Some
        ; apply (protocol_trace_output_is_protocol X' _ _ (proj1 HtrXm) _ Hex)
        |].
      rewrite <- Hstate_project.
      unfold finite_trace_last at 1. simpl.
      apply
        (Hconstraint_hbs _ _ _ _ _ _ _ Horiginal_tr_suf'
          _ Hnot_equivocating _ _ Horiginal_project _ _ Hprojectx).
    + exists trX'. exists initial_descriptors. subst foldx. split; [assumption|].
      split; [apply Htr_project|]. split; [|assumption].
      subst tr. clear -Hstate_project Hx.
      rewrite Hstate_project in Hx.
      rewrite <- Hx. f_equal. unfold final_state.
      rewrite finite_trace_last_is_last.
      reflexivity.
Qed.

(** Instantiating the lemma above with the free constraint.
*)
Lemma free_equivocators_protocol_trace_project
  (final_descriptors : equivocator_descriptors IM)
  (is : composite_state (equivocator_IM IM))
  (tr : list (composite_transition_item (equivocator_IM IM)))
  (final_state := @finite_trace_last _ (@type _ XE) is tr)
  (Hproper : not_equivocating_equivocator_descriptors IM final_descriptors final_state)
  (Htr : finite_protocol_trace XE is tr)
  : exists
    (trX : list (composite_transition_item IM))
    (initial_descriptors : equivocator_descriptors IM)
    (isX := equivocators_state_project IM initial_descriptors is)
    (final_stateX := finite_trace_last isX trX),
    proper_equivocator_descriptors IM initial_descriptors is /\
    equivocators_trace_project IM final_descriptors tr = Some (trX, initial_descriptors) /\
    equivocators_state_project IM final_descriptors final_state = final_stateX /\
    finite_protocol_trace (free_composite_vlsm IM) isX trX.
Proof.
  specialize (_equivocators_protocol_trace_project final_descriptors is tr _ _ Hproper [])
    as Hproject.
  spec Hproject.  { constructor. apply finite_ptrace_last_pstate. apply Htr. }
  specialize (Hproject [] eq_refl Htr).
  apply Hproject; intro; intros; exact I.
Qed.

Lemma free_equivocators_protocol_message_project
  : forall m : message,
    protocol_message_prop XE m -> protocol_message_prop (free_composite_vlsm IM) m.
Proof.
  intros m Hm.
  apply can_emit_protocol_iff in Hm.
  destruct Hm as [Hinit | Hm]; [apply initial_message_is_protocol; assumption|].
  apply can_emit_iff in Hm. destruct Hm as [s2 [(s1, iom) [l Ht]]].
  apply exists_right_finite_trace_from in Ht as Hts.
  destruct Hts as [s0 [ts [[Hs0 Hts] Hs1]]].
  specialize
    (exists_equivocators_transition_item_project IM
      {| l := l; input := iom; destination := s2; output := Some m |}
      s1
    ) as Hexists.
  destruct Ht as [[_ [_ [Hv _]]] Ht].
  spec Hexists.
  { simpl. clear -Ht Hv.
    unfold transition in Ht. simpl in Ht.
    destruct l as (i, (li, di)). simpl in *.
    unfold vvalid in Hv. simpl in Hv.
    destruct (vtransition (equivocator_IM IM i) (li, di) (s1 i, iom)) as (si', om') eqn:Hti.
    inversion Ht. subst om'. clear Ht.
    unfold vtransition in Hti. simpl in Hti.
    destruct di as [sn| j fj]; [congruence|].
    destruct Hv as [Hj Hv].
    assumption.
  }
  specialize (Hexists Hv Ht).
  simpl in Hexists.
  destruct Hexists
    as [final_descriptors [Hfinal_descriptors [final_descriptors' [Hfinal_descriptors' Hpr_item]]]].
  specialize
    (free_equivocators_protocol_trace_project
      final_descriptors
      s0
      (ts ++ [{| l := l; input := iom; destination := s2; output := Some m |}])
    ) as Hpr.
  rewrite finite_trace_last_is_last in Hpr.
  simpl in Hpr.
  spec Hpr Hfinal_descriptors.
  spec Hpr.
  { split ; [|assumption].
    revert Hs0. apply finite_protocol_trace_from_to_forget_last.
  }
  destruct Hpr as [trX [initial_descriptors [Hinitial_descriptors [Hpr [Hpr_s2 HtrX]]]]].
  apply equivocators_trace_project_app_iff in Hpr.
  destruct Hpr as [preX [sufX [_final_descriptors' [_Hpr_item [Hpr_tr Heq_trX]]]]].
  simpl in _Hpr_item.
  rewrite Hpr_item in _Hpr_item.
  inversion _Hpr_item.
  subst _final_descriptors'. clear _Hpr_item.
  subst trX sufX.
  clear -HtrX.
  apply proj1,finite_protocol_trace_from_app_iff, proj2 in HtrX.
  inversion HtrX.
  apply can_emit_protocol.
  apply can_emit_iff.
  unfold protocol_generated_prop.
  eexists _, _, _. apply H6.
Qed.

Lemma full_node_limited_equivocation_constraint_hbo
  s
  l input
  (Hv: protocol_valid XE l (s, Some input))
  :
  let (i, l') := l in
  let (li, di) := l' in
  forall
    descriptors
    (Hdescriptorsi: descriptors i = di)
    ,
    let sX' := equivocators_state_project IM descriptors s in
  message_dependencies_local_full_node_constraint (existT _ i li) (sX', Some input).
Proof.
  destruct l as (i, (li, di)). destruct Hv as [_ [_ [_ [Hfull _]]]].
  simpl in *.
  intros.
  intros m Hm.
  unfold equivocators_state_project.
  rewrite Hdescriptorsi in *.
  apply Hfull.
  assumption.
Qed.


(**
The set of equivocator indices can only grow through a transition.

If the transition label is a NewMachine, then the corresponding resulting state
component is sure to be equivocating.
*)
Lemma equivocators_transition_preserves_equivocating_indices_and_newmachines
  s iom oom l s0
  (Ht: composite_transition (equivocator_IM IM) l (s0, iom) = (s, oom))
  descriptors eqv_descriptors'
  (Heq_eqv_descriptors' : eqv_descriptors' = equivocator_descriptors_update IM descriptors (projT1 l) (snd (projT2 l)))
  : incl (set_union IndEqDec (equivocating_indices IM index_listing s0) (newmachine_descriptors_list IM index_listing eqv_descriptors')) (set_union IndEqDec (equivocating_indices IM index_listing s) (newmachine_descriptors_list IM index_listing descriptors)).
Proof.
  intros i Hi.
  apply set_union_iff. apply set_union_iff in Hi.
  subst eqv_descriptors'.
  destruct Hi as [Hi | Hi].
  - left. revert i Hi.
    apply
      (equivocators_transition_preserves_equivocating_indices IM index_listing
            _ _ _ _ _ Ht).
  - apply filter_In in Hi. destruct Hi as [_ Hi].
    apply bool_decide_eq_true in Hi.
    destruct (decide (i = projT1 l)).
    + subst i. rewrite equivocator_descriptors_update_eq in Hi.
      destruct l as (i, (li, [sn | ii fi])); [|inversion Hi].
      simpl in *. inversion Ht. subst. left. apply filter_In.
      split; [apply finite_index|].
      apply bool_decide_eq_true. unfold is_equivocating_state.
      rewrite state_update_eq. unfold is_singleton_state.
      destruct (s0 i). simpl. congruence.
    + right. rewrite equivocator_descriptors_update_neq in Hi by assumption.
      apply filter_In. split; [apply finite_index|].
      apply bool_decide_eq_true. assumption.
Qed.

(**
The message-based known equivocators of a projection of a protocol state are
either state-equivocating in the original state or are [NewMachine]s in the
projection descriptors.
*)
Lemma full_node_limited_equivocation_constraint_known_equivocators
  s
  (Hs : protocol_state_prop XE s)
  : forall
     descriptors
     (Hdescriptors : proper_equivocator_descriptors IM descriptors s)
     (sX := equivocators_state_project IM descriptors s),
     incl (globally_known_equivocators sX) (set_union IndEqDec (equivocating_indices IM index_listing s) (newmachine_descriptors_list IM index_listing descriptors)).
Proof.
  induction Hs using protocol_state_prop_ind; intros; intros eqv Heqv.
  - rewrite
      (known_equivocators_initial_state finite_index IM Hbs Hbr i0 sender globally_known_equivocators
        sX
      )
      in Heqv; [inversion Heqv|].
    intro i. specialize (Hs i). destruct Hs as [Hns Hs].
    subst sX.
    specialize (Hdescriptors i).
    unfold equivocators_state_project.
    destruct (descriptors i) as [sn | j fj]; simpl in Hdescriptors
    ; [assumption|].
    assert (Hj : j = 0) by lia. subst j. simpl.
    unfold equivocator_state_project.
    destruct (s i). assumption.
  - destruct Ht as [[Hs [Hom [Hv Hc]]] Ht].
    destruct
      (equivocators_transition_item_project_proper_descriptor_characterization IM
        descriptors (Build_transition_item l om s' om') (Hdescriptors (projT1 l))
      ) as [oitem [eqv_descriptors' [Hoitem [Hitem Hchar]]]].
    simpl in Hitem, Hchar.
    specialize (Hchar s Hv Ht).
    specialize (IHHs eqv_descriptors').
    destruct Hchar as [Hdescriptorsi' [Heq_descriptors' [Heq_s Hoitem']]].
    assert (Hdescriptors' : proper_equivocator_descriptors IM eqv_descriptors' s).
    { rewrite Heq_s, Heq_descriptors'.
      intro i.
      destruct (decide (i = projT1 l)).
      - subst. rewrite state_update_eq, equivocator_descriptors_update_eq.
        assumption.
      - rewrite state_update_neq, equivocator_descriptors_update_neq by assumption.
        apply Hdescriptors.
    }
    spec IHHs Hdescriptors'.
    destruct oitem as [itemx|].
    + specialize (Hoitem' (equivocators_state_project IM eqv_descriptors' s) eq_refl).
      destruct Hitem as [Heq_lx [Heq_om [Heq_om' [Hdestinationx Heq_descriptorsi']]]].
      destruct itemx as (lx, omx, sx', omx').
      simpl in *.
      subst omx omx' lx. rewrite Heq_descriptorsi' in *. clear Heq_descriptorsi'.
      destruct Hoitem' as [Hvx Htx].
      apply
        (equivocators_transition_preserves_equivocating_indices_and_newmachines
          _ _ _ _ _ Ht descriptors eqv_descriptors' Heq_descriptors'
        ).
      destruct om as [im|]
      ; [destruct
        (Free_no_additional_equivocation_constraint_dec
          (existT (fun n : index => vlabel (IM n)) (projT1 l) (fst (projT2 l)))
          (equivocators_state_project IM eqv_descriptors' s, Some im)
        )|].
      * specialize
          (known_equivocators_transition_no_equiv finite_index IM Hbs Hbr i0
            sender globally_known_equivocators
            (existT (fun n : index => vlabel (IM n)) (projT1 l) (fst (projT2 l)))
            _ _ _ _ Htx n
          ) as Heq.
        apply IHHs.
        apply Heq.
        subst.  assumption.
      * specialize
          (additional_equivocations_guarantees_sender finite_index IM Hbs Hbr i0 sender
            _ _ _ n
          ) as Hsender.
        spec Hsender.
        { apply free_equivocators_protocol_message_project.
          assumption.
        }
        destruct Hsender as [i Hsender].

        specialize
          (known_equivocators_transition_equiv finite_index IM Hbs Hbr i0
            sender globally_known_equivocators
            (existT (fun n : index => vlabel (IM n)) (projT1 l) (fst (projT2 l)))
            _ _ _ _ i Htx n
          ) as Heq.
        spec Heq.
        { destruct Hc as [Hfull Hlimited].
          unfold full_node_equivocators_constraint in Hfull.
          clear i Hsender Heq.
          destruct l as (i, (li, desc)).
          simpl in *.
          revert Hfull.
          apply
            (message_dependencies_global_full_node_condition_from_local sender (fun i => i) IM Hbs Hbr finite_index).
          subst eqv_descriptors'.
          unfold equivocators_state_project.
          rewrite equivocator_descriptors_update_eq.
          reflexivity.
        }
        spec Heq Hsender.
        subst sx' sX.
        apply Heq in Heqv.
        apply set_add_iff in Heqv.
        apply or_comm in Heqv.
        destruct Heqv as [Heqv | Heq_eqv]; [apply IHHs; assumption|].
        subst i.
        unfold no_additional_equivocations_constraint, no_additional_equivocations in n.
        assert (Hno : ~ has_been_observed Free (equivocators_state_project IM eqv_descriptors' s) im)
          by (clear -n; intuition).
        assert (Hni : ~vinitial_message_prop Free im)
          by (clear -n; intuition).
        destruct Hc as [Hfull [[[Hbs_im | Hinit_im] _] Hlimited]]
        ; [|contradiction].
        destruct Hbs_im as [i Hbsi_im].
        unfold has_been_sent, equivocator_Hbs in Hbsi_im.
        simpl in Hbsi_im.
        unfold equivocator_has_been_sent in Hbsi_im.
        destruct (s i) as (nsi, ssi) eqn:Heq_si.
        destruct Hbsi_im as [ji Hbsi_im].
        specialize (proper_sent (IM i) (ssi ji)) as Hproper_sent.
        assert (Hssiji : protocol_state_prop (pre_loaded_with_all_messages_vlsm (IM i)) (ssi ji)).
        { clear -Hs Heq_si.
          apply protocol_state_project_preloaded with (i := i) in Hs.
          specialize (preloaded_equivocator_state_project_protocol_state (IM i) (s i) Hs)
            as Hps.
          rewrite Heq_si in Hps. simpl in Hps.
          apply Hps.
        }
        unfold has_been_sent_prop, all_traces_have_message_prop in Hproper_sent.
        specialize (Hproper_sent Hssiji im).
        apply proj1 in Hproper_sent.
        specialize (Hproper_sent Hbsi_im).
        apply (has_been_sent_consistency) in Hproper_sent; [|apply (Hbs i)|assumption].
        destruct Hproper_sent as [s0 [tr [[Htr Hs0] Hhm_im]]].
        apply finite_protocol_trace_from_to_forget_last in Htr.
        specialize (can_emit_from_protocol_trace (pre_loaded_with_all_messages_vlsm (IM i)) _ _ _ (conj Htr Hs0) Hhm_im)
          as Hemit_im.
        specialize (sender_safety sender (fun i => i) IM Hbs Hbr i im Hemit_im)
          as _Hsender.
        rewrite Hsender in _Hsender.
        inversion _Hsender. subst i. clear _Hsender.
        assert (Hns : ~has_been_sent  Free (equivocators_state_project IM eqv_descriptors' s) im)
          by (intro Hbs_im; elim Hno; left; assumption).
        assert (Hnsi : ~has_been_sent  (IM eqv) (equivocators_state_project IM eqv_descriptors' s eqv) im).
        {
          intro Hbsi. elim Hns. exists eqv. assumption.
        }
        clear Hns.
        unfold equivocators_state_project in Hnsi.
        apply set_union_iff.
        specialize (Hdescriptors' eqv).
        destruct (eqv_descriptors' eqv) as [sn | eqvi eqvf] eqn:Heq_descriptors'_eqv.
        -- right. apply filter_In. split; [apply finite_index|].
          apply bool_decide_eq_true. rewrite Heq_descriptors'_eqv.
          exact I.
        -- left.
          apply filter_In.
          split; [apply finite_index|].
          apply bool_decide_eq_true.
          rewrite Heq_si in Hnsi. unfold equivocator_state_descriptor_project in Hnsi.
          unfold equivocator_state_project in Hnsi.
          simpl in Hdescriptors'.
          rewrite Heq_si in Hdescriptors'. simpl in Hdescriptors'.
          rewrite Heq_si. unfold is_equivocating_state, is_singleton_state.
          simpl.
          destruct (le_lt_dec (S nsi) eqvi); [lia|].
          intro contra.
          elim Hnsi. subst nsi.
          clear - Hbsi_im.
          assert (eqvi = 0) by lia.
          subst eqvi.
          assert (Heq_ji : ji = (Fin2Restrict.n2f l0)).
          { clear. dependent destruction ji; [|inversion ji].
            remember (Fin2Restrict.n2f l0) as x. clear.
            dependent destruction x; [|inversion x].
            reflexivity.
          }
          subst ji. assumption.
      * specialize
          (known_equivocators_transition_no_equiv finite_index IM Hbs Hbr i0
            sender globally_known_equivocators
            (existT (fun n : index => vlabel (IM n)) (projT1 l) (fst (projT2 l)))
            _ _ _ _ Htx I
          ) as Heq.
        subst sx' sX.
        apply IHHs.
        apply Heq.
        assumption.
    + rewrite <- Hoitem' in *.
      specialize (IHHs _ Heqv).
      apply set_union_iff. apply set_union_iff in IHHs.

      destruct IHHs as [Heqv_s | Heqv_newmachine]
      ; [ left;
          apply
            (equivocators_transition_preserves_equivocating_indices IM index_listing
              _ _ _ _ _ Ht
            )
          ; assumption
        |].

      unfold newmachine_descriptors_list. rewrite filter_In. apply filter_In in Heqv_newmachine.
      apply proj2 in Heqv_newmachine.
      apply bool_decide_eq_true in Heqv_newmachine.
      destruct (eqv_descriptors' eqv) as [seqv | ieqv feqv] eqn:Heq_eqv_descriptors'_eqv
      ; [|contradiction].
      clear Heqv_newmachine.
      rewrite Heq_descriptors' in Heq_eqv_descriptors'_eqv.
      rewrite bool_decide_eq_true.
      destruct (decide (eqv = projT1 l))
      ; [ | rewrite equivocator_descriptors_update_neq in Heq_eqv_descriptors'_eqv by assumption
            ; rewrite Heq_eqv_descriptors'_eqv
            ; right; split; [apply finite_index|]; exact I
        ].
      subst eqv. rewrite equivocator_descriptors_update_eq in Heq_eqv_descriptors'_eqv.

      unfold equivocators_transition_item_project
        , ProjectionTraces.composite_transition_item_projection
        , ProjectionTraces.composite_transition_item_projection_from_eq in Hoitem; simpl in Hoitem.
      unfold eq_rect_r, eq_rect in Hoitem; simpl in Hoitem.
      destruct
        (@equivocator_vlsm_transition_item_project message
        (IM
           (@projT1 index
              (fun n : index =>
               @vlabel message (@equivocator_IM message index IM n)) l))
        (@Build_transition_item message
           (@equivocator_type message
              (IM
                 (@projT1 index
                    (fun n : index =>
                     @vlabel message
                       (@equivocator_IM message index IM n)) l)))
           (@projT2 index
              (fun n : index =>
               @vlabel message (@equivocator_IM message index IM n)) l)
           om
           (s'
              (@projT1 index
                 (fun n : index =>
                  @vlabel message (@equivocator_IM message index IM n))
                 l)) om')
        (descriptors
           (@projT1 index
              (fun n : index =>
               @vlabel message (@equivocator_IM message index IM n)) l))
        ) as [(oitemx, eqv')|] eqn:Heq_proj
        ; [|congruence].
      destruct oitemx as [itemx |]; [congruence|].
      inversion Hoitem. subst. clear Hoitem.
      rewrite equivocator_descriptors_update_eq in Heq_eqv_descriptors'_eqv.
      subst eqv'.
      unfold equivocator_vlsm_transition_item_project in Heq_proj.
      destruct (descriptors (projT1 l))
      ; [ right; split; [apply finite_index|]; assumption
        | left].
      simpl.
      destruct l as (i, (li, di)).
      unfold projT1, projT2 in Heq_proj.
      destruct (s' i) as (ns'i, bs'i) eqn:Heq_s'i.
      destruct (le_lt_dec (S ns'i) n); [congruence|].
      destruct di as [sdi | jdi fdi]
      ; [destruct (nat_eq_dec (S n) (S ns'i));[|congruence]|]
      ; [
        | destruct fdi; [destruct (nat_eq_dec (S n) (S ns'i)); congruence|]
          ; destruct (nat_eq_dec jdi n); congruence
        ].
      inversion e. subst. clear e. inversion Heq_proj.
      simpl in *. subst. clear Heq_proj.

      apply filter_In. split; [apply finite_index|].
      apply bool_decide_eq_true.
      unfold is_equivocating_state, is_singleton_state.
      rewrite Heq_s'i. simpl.
      inversion Ht.
      subst s'. rewrite state_update_eq in Heq_s'i.
      unfold equivocator_state_extend in Heq_s'i.
      destruct (s i) as (nsi, bsi) eqn:Heq_si.
      inversion Heq_s'i.
      lia.
Qed.

(**
We here prove that the [full_node_limited_equivocation_constraint] verifies
the [full_node_limited_equivocation_constraint_sufficient_condition_prop]
stated above.
*)
Lemma full_node_limited_equivocation_constraint_sufficient_condition
  : full_node_limited_equivocation_constraint_sufficient_condition_prop
    (full_node_limited_equivocation_constraint IM Hbs Hbr sender globally_known_equivocators).
Proof.
  intro. intros.
  inversion Htr. subst s' f l0 iom s0 oom tl.
  assert (Hss : protocol_state_prop XE s1).
  { revert H7. apply protocol_transition_destination. }
  destruct H7 as [Hpv Ht].
  assert
    (Htr_pre : finite_protocol_trace_from_to
      (pre_loaded_with_all_messages_vlsm
        (free_composite_vlsm (equivocator_IM IM))) s1 original_state tr).
  { revert H3.
    apply VLSM_incl_finite_protocol_trace_from_to.
    apply equivocators_limited_equivocations_vlsm_incl_preloaded_free.
  }
  assert (Hproper: proper_equivocator_descriptors IM s1_descriptors s1).
  { apply preloaded_equivocators_protocol_trace_project_proper_initial with tr original_descriptors trX.
    - apply finite_protocol_trace_from_to_forget_last in H3.
      revert H3.
      apply VLSM_incl_finite_protocol_trace_from.
      apply equivocators_limited_equivocations_vlsm_incl_preloaded_free.
    - assumption.
    - apply not_equivocating_equivocator_descriptors_proper.
      apply finite_protocol_trace_from_to_last in H3.
      subst. assumption.
  }
  clear H3.
  destruct
    (equivocators_transition_item_project_proper_characterization IM s1_descriptors item Hproper)
    as [oitemX [_s_descriptors [_Hitem_project [Hchar1 Hchar2]]]].
  rewrite Hitem_project in _Hitem_project.
  inversion _Hitem_project. subst oitemX _s_descriptors. clear _Hitem_project.
  subst item. destruct itemX. simpl in *.
  destruct Hchar1 as [Heq_l0 [Heq_input0 [Heq_output0 [Heq_destination Hdescriptorsi']]]].
  subst input0 output0 l0.
  apply proj2 in Hpv as Hv. apply proj2,proj1 in Hv.
  specialize (Hchar2 s Hv Ht).
  destruct Hchar2 as [Hproper' Hchar2].
  specialize (Hchar2 _ eq_refl).
  destruct Hchar2 as [Hvx Htx].
  split.
  - clear -Hdescriptorsi' Hpv Ht.
    specialize
      (full_node_limited_equivocation_constraint_hbo s l input Hpv) as Hhbo.
    destruct l as (i, (li, dl)).
    specialize (Hhbo s_descriptors Hdescriptorsi').
    assumption.
  -     specialize
      (full_node_limited_equivocation_constraint_known_equivocators
        s1 Hss s1_descriptors Hproper
      ) as Hincl.
    assert (Heq_proj :  fst
    (composite_transition IM
       (existT (fun n : index => vlabel (IM n)) (projT1 l) (fst (projT2 l)))
       (equivocators_state_project IM s_descriptors s, Some input))
      =  destination).
    { apply f_equal with (f := fst) in Htx .
      simpl in Htx.
      assumption.
    }
    rewrite Heq_proj.
    unfold globally_known_equivocators_weight.
    apply Rle_trans with (sum_weights (set_union IndEqDec (equivocating_indices IM index_listing s1)
    (newmachine_descriptors_list IM index_listing s1_descriptors))).
    { revert Hincl. rewrite Heq_destination. apply sum_weights_incl.
      - apply known_equivocators_nodup with finite_index Hbs Hbr i0 sender Hdm.
        assumption.
      - apply set_union_nodup; apply NoDup_filter; apply finite_index.
    }
    clear Hincl.
    specialize
      (equivocators_trace_project_preserves_equivocating_indices_final IM finite_index
        _ _ _ _ _ _ Htr_pre Hnot_equivocating Htr_project
      ) as Hincl.
    apply sum_weights_incl in Hincl; [| apply set_union_nodup|]
      ; repeat (apply NoDup_filter; apply finite_index).
    apply Rle_trans with (sum_weights (equivocating_indices IM index_listing original_state))
    ; [assumption|].
    apply protocol_state_limited_equivocation.
    apply finite_protocol_trace_from_to_last_pstate in Htr.
    assumption.
Qed.

(**
Main result of this section, stating that traces which are protocol for the
equivocator-based definition of full-node-like limited equivocation project to
traces which are protocol for the simple-nodes definition of
full-node-like limited equivocation.
*)
Theorem limited_equivocators_protocol_trace_project
  (final_descriptors : equivocator_descriptors IM)
  (is : composite_state (equivocator_IM IM))
  (tr : list (composite_transition_item (equivocator_IM IM)))
  (final_state := finite_trace_last is tr)
  (Hproper: not_equivocating_equivocator_descriptors IM final_descriptors final_state)
  (Htr : finite_protocol_trace XE is tr)
  : exists
    (trX : list (composite_transition_item IM))
    (initial_descriptors : equivocator_descriptors IM)
    (isX := equivocators_state_project IM initial_descriptors is)
    (final_stateX := finite_trace_last isX trX),
    proper_equivocator_descriptors IM initial_descriptors is /\
    equivocators_trace_project IM final_descriptors tr = Some (trX, initial_descriptors) /\
    equivocators_state_project IM final_descriptors final_state = final_stateX /\
    finite_protocol_trace X isX trX.
Proof.
  specialize (_equivocators_protocol_trace_project final_descriptors is tr _ _ Hproper [])
    as Hproject.
  spec Hproject.  { constructor. apply finite_ptrace_last_pstate. apply Htr. }
  specialize (Hproject [] eq_refl Htr).
  apply Hproject
  ; clear is tr Hproper Htr final_state final_descriptors Hproject; intro; intros.
  - split; [exact I|].
    destruct (composite_transition IM l (s, None)) as (s', om') eqn:Ht.
    simpl.
    rewrite
      (@composite_transition_None_equivocators_weight
        _ _ _ _ finite_index _ IM Hbs Hbr i0 sender globally_known_equivocators
        Hdm Hknown_equivocators _ _ _ _ Ht
      ).
    apply
      (full_node_limited_equivocation_protocol_state_weight
        finite_index IM Hbs Hbr i0 sender globally_known_equivocators
        _ H
      ).
  - split.
    + destruct l. simpl.
      intros dm Hdmm.
      rewrite
        (initial_message_not_dependent sender (fun x => x) IM Hbs Hbr m H0)
        in Hdmm.
      inversion Hdmm.
    + destruct (composite_transition IM l (s, Some m)) as (s', oom) eqn:Ht.
      specialize
        (known_equivocators_transition_no_equiv
          finite_index IM Hbs Hbr i0 sender globally_known_equivocators
          l s (Some m) s' oom Ht
        ) as Hs'.
      spec Hs'. { simpl. right. assumption. }
      unfold globally_known_equivocators_weight.
      specialize
        (full_node_limited_equivocation_protocol_state_weight
          finite_index IM Hbs Hbr i0 sender globally_known_equivocators
          _ H
        ) as Hs.
      rewrite
        (set_eq_nodup_sum_weight_eq
          (globally_known_equivocators s')
          (globally_known_equivocators s)
        )
      ; [assumption| .. | assumption]
      ; apply
          (known_equivocators_nodup
            finite_index IM Hbs Hbr i0 sender globally_known_equivocators
          ).
  - apply
      (full_node_limited_equivocation_constraint_sufficient_condition
        _ _ _ _ _ _ _ Htr
        _ Hnot_equivocating _ _ Htr_project _ _ Hitem_project
      ).
Qed.



End limited_equivocation_state_to_message.
