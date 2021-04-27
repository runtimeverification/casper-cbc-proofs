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
  (*equivocating : set index)
  (Hi0_equiv : equivocating <> []*)
  (* i0 : Inhabited index := @SubProjectionTraces.i0 index equivocating Hi0_equiv *)
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
  (* index_equivocating_prop : index -> Prop := sub_index_prop equivocating *)
  (* equivocating_index : Type := sub_index equivocating *)
  (* equivocating_i0 : Inhabited equivocating_index := sub_index_i0 equivocating Hi0_equiv *)
  (* equivocating_IM := sub_IM IM equivocating *)
  (* equivocating_index_eq_dec : EqDecision equivocating_index := sub_index_eq_dec equivocating *)
  (* free_equivocating_vlsm_composition : VLSM message := free_composite_vlsm equivocating_IM *)
  (* sub_equivocator_IM := sub_IM (equivocator_IM IM) equivocating *)
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


(*

(**
[proper_equivocator_descriptors] strengthen for fixed-equivocation.
We require that if the index is not equivocating, than the corresponding
descriptor is a [zero_descriptor].
*)
Definition proper_fixed_equivocator_descriptors
  (eqv_descriptors : equivocator_descriptors IM)
  (s : state)
  : Prop
  := proper_equivocator_descriptors IM eqv_descriptors s /\
    forall i, ~In i equivocating -> eqv_descriptors i = Existing _ 0 false.

*)

(**
[not_equivocating_equivocator_descriptors] satisfy the
[proper_equivocator_descriptors] property.
*)
Lemma not_equivocating_equivocatos_descriptors_proper
  (s : composite_state (equivocator_IM IM))
  (Hs : protocol_state_prop XE s)
  (eqv_descriptors : equivocator_descriptors IM)
  (Heqv_descriptors : not_equivocating_equivocator_descriptors IM eqv_descriptors s)
  : proper_equivocator_descriptors IM eqv_descriptors s.
Proof.
  apply not_equivocating_equivocator_descriptors_proper. assumption.
Qed.

(**
Projections of (valid) traces of the composition of equivocators preserve
[proper_equivocator_descriptors].
*)
Lemma equivocators_trace_project_preserves_proper_equivocator_descriptors
  (is : composite_state (equivocator_IM IM))
  (tr : list (composite_transition_item (equivocator_IM IM)))
  (Htr : finite_protocol_trace_from (pre_loaded_with_all_messages_vlsm FreeE) is tr)
  (s := last (map destination tr) is)
  (descriptors : equivocator_descriptors IM)
  (idescriptors : equivocator_descriptors IM)
  (trX : list (composite_transition_item IM))
  (HtrX : equivocators_trace_project IM descriptors tr = Some (trX, idescriptors))
  : proper_equivocator_descriptors IM descriptors s -> proper_equivocator_descriptors IM idescriptors is.
Proof.
  apply (preloaded_equivocators_protocol_trace_project_proper_initial IM
    _ _ Htr _ _ _ HtrX).
Qed.

Existing Instance equivocators_free_Hbs.
Existing Instance Free_has_been_observed_capability.
Existing Instance Free_has_been_sent_capability.

(**
This is a property of the [fixed_equivocation_constraint] which also
trivially holds for the free constraint.  This property is sufficient for
proving the [_equivocators_protocol_trace_project] lemma,
which lets that lemma be used for both the composition of equivocators with
fixed state-equivocation and the free composition.

It basically says that if a message has_been_sent for a state of the
composition of equivocators with no-message equivocations and fixed
state-equivocations, then any of its projections should be allowed to receive it.
*)
Definition constraint_has_been_sent_prop
  (constraint : composite_label IM -> composite_state IM * option message -> Prop)
  : Prop :=
  forall
    (s : composite_state (equivocator_IM IM))
    (Hs : protocol_state_prop XE s)
    (descriptors : equivocator_descriptors IM)
    (Hdescriptors : proper_equivocator_descriptors IM descriptors s)
    (sX := @equivocators_state_project _ _ IndEqDec IM i0 descriptors s)
    (m: message)
    (Hm : has_been_sent FreeE s m)
    l,
  constraint l (sX, Some m).


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
  (Hproper : proper_equivocator_descriptors IM final_descriptors final_state)
  (Htr : finite_protocol_trace XE is tr)
  (constraint : composite_label IM -> composite_state IM * option message -> Prop)
  (X' := composite_vlsm IM constraint)
  (HconstraintNone : forall l s, protocol_state_prop X' s -> constraint l (s, None))
  (Hconstraintinitial : forall l s m, protocol_state_prop X' s -> vinitial_message_prop FreeE m -> constraint l (s, Some m))
  (Hconstraint_hbs :  constraint_has_been_sent_prop constraint)
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
  generalize dependent final_descriptors. generalize dependent tr.
  induction len_tr using (well_founded_induction Wf_nat.lt_wf); intros.
  subst len_tr.
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
    specialize (Hproperx (finite_trace_last is tr')).
    unfold equivocators_trace_project.
    rewrite fold_right_app.
    match goal with
    |- context [fold_right _ ?fld _] => remember fld as foldx
    end.
    simpl in Heqfoldx.
    rewrite Hprojectx in Heqfoldx.
    apply first_transition_valid in Hlst. destruct lst as (l, iom, s, oom). simpl in *.
    destruct Hlst as [Hpv Ht].
    assert (Hpv' := Hpv).
    destruct Hpv' as [Hs [Hiom [Hv Hc]]].
    specialize (Hzero oitem final_descriptors' _ Ht Hv Hprojectx).
    specialize (Hproperx Hv Ht).
    destruct Hproperx as [Hproperi' [Hdescriptors' [Hlst' Hx]]].
    assert (Hproper' : proper_equivocator_descriptors IM final_descriptors' ( finite_trace_last is tr')).
    {  rewrite Hdescriptors'. intro i.
      destruct (decide (i = projT1 l)).
      - subst. rewrite equivocator_descriptors_update_eq. assumption.
      - rewrite equivocator_descriptors_update_neq by assumption.
        rewrite Hlst'. rewrite state_update_neq by assumption.
        apply Hproper.
    }
    specialize (H' _ Hproper').
    destruct H' as [trX' [initial_descriptors [_ [Htr_project [Hstate_project HtrX']]]]].
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
    specialize
      (equivocators_trace_project_preserves_proper_equivocator_descriptors _ _ (proj1 Htr'pre) _ _ _ Htr_project Hproper')
      as Hproper_initial.
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
      destruct Hno_equiv as [Hinit_input | Hno_equiv]
      ; [apply fixed_equivocators_initial_message in Hinit_input|]
      ; [repeat split; [assumption| |assumption| apply Hconstraintinitial; assumption |assumption]|].
      { apply protocol_message_prop_iff. left. exists (exist _ _ Hinit_input).
        reflexivity.
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
      { apply not_equivocating_equivocatos_descriptors_proper; [|assumption].
        apply finite_ptrace_last_pstate. assumption.
      }
      specialize (H (length tr')).
      spec H. { rewrite app_length. simpl. lia. }
      specialize (H tr' (conj Htr Hinit) eq_refl final_descriptors_m Hfinal_descriptors_m).
      destruct H as [trXm' [initial_descriptors_m' [Hproper_initial_m [Hproject_trXm' [Hpr_fin_tr' HtrXm]]]]].
      simpl in *. rewrite Hproject_trXm in Hproject_trXm'.
      inversion Hproject_trXm'. subst trXm' initial_descriptors_m'. clear Hproject_trXm'.
      repeat split; [assumption| |assumption| |assumption]
      ; [ apply option_protocol_message_Some
        ; apply (protocol_trace_output_is_protocol X' _ _ (proj1 HtrXm) _ Hex)
        |].
      rewrite <- Hstate_project.
      apply Hconstraint_hbs; [assumption| apply Hproper'|].
      assert (Hlst'pre : protocol_state_prop (pre_loaded_with_all_messages_vlsm FreeE) (last (map Common.destination tr') is)).
      { apply finite_ptrace_last_pstate. apply Htr'pre. }
      apply proper_sent; [assumption|].
      apply has_been_sent_consistency; [assumption| assumption| ].
      exists is, tr', (ptrace_add_default_last Htr'pre). assumption.
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
  (Hproper : proper_equivocator_descriptors IM final_descriptors final_state)
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
  apply _equivocators_protocol_trace_project; [assumption | assumption| ..]
  ; unfold constraint_has_been_sent_prop; intros; exact I.
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
  dependent_messages_local_full_node_constraint (existT _ i li) (sX', Some input).
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

Lemma full_node_limited_equivocation_constraint_known_equivocators
  s
  (Hs : protocol_state_prop XE s)
  : forall
     descriptors
     (Hdescriptors : proper_equivocator_descriptors IM descriptors s)
     (sX := equivocators_state_project IM descriptors s),
     incl (globally_known_equivocators sX) (equivocating_indices IM index_listing s).
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
    specialize
      (equivocators_transition_item_project_proper_descriptor_characterization IM
        descriptors (Build_transition_item l om s' om') (Hdescriptors (projT1 l))
      ).


Lemma full_node_limited_equivocation_constraint_limited
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
  incl
    (globally_known_equivocators
      (fst (composite_transition IM
        (existT (fun n : index => vlabel (IM n)) (projT1 l) (fst (projT2 l)))
        (sX', Some input))))
    (equivocating_indices IM index_listing
      (fst (composite_transition (equivocator_IM IM) l (s, Some input)))).
Proof.
  apply proj1 in Hv as Hs.
  revert l input Hv.
Admitted.

Lemma full_node_limited_equivocation_constraint_hbs
  (is: composite_state (equivocator_IM IM))
  (constraint := full_node_limited_equivocation_constraint IM Hbs Hbr i0 sender globally_known_equivocators)
  (X':= composite_vlsm IM constraint : VLSM message)
  (HconstraintNone: forall (l : composite_label IM) (s : _composite_state IM), protocol_state_prop X' s -> constraint l (s, None))
  (Hconstraintinitial: forall (l : composite_label IM) (s : _composite_state IM) (m : message), protocol_state_prop X' s -> vinitial_message_prop FreeE m -> constraint l (s, Some m))
  (tr': list (composite_transition_item (equivocator_IM IM)))
  (l: _composite_label (equivocator_IM IM))
  (s: _composite_state (equivocator_IM IM))
  (input: message)
  (destination: _composite_state IM)
  (output: option message)
  (final_descriptors : equivocator_descriptors IM)
  (final_descriptors': equivocator_descriptors IM)
  (Hdescriptors': final_descriptors' =  equivocator_descriptors_update IM final_descriptors (projT1 l) (final_descriptors' (projT1 l)))
  (Hdescriptorsi': final_descriptors' (projT1 l) = snd (projT2 l))
  (final_state:= s)
  (Hprojectx: equivocators_transition_item_project IM final_descriptors 
    (@Build_transition_item message (@type message XE) l (Some input) s output)
     = Some (Some (@Build_transition_item message (@type message X) (existT (fun n : index => vlabel (IM n)) (projT1 l) (fst (projT2 l))) (Some input) destination output), final_descriptors'))
  (Htr: finite_protocol_trace_from XE is tr')
  (Hpv: protocol_valid XE l (finite_trace_last is tr', Some input))
  (Hs: protocol_state_prop XE (finite_trace_last is tr'))
  (Ht: (let (i, li) := l in let (si', om') := vtransition (equivocator_IM IM i) li (finite_trace_last is tr' i, Some input) in (state_update (equivocator_IM IM) (finite_trace_last is tr') i si', om')) = (s, output))
  (Hfull: full_node_equivocators_constraint IM Hbs sender Hbr l (finite_trace_last is tr', Some input))
  (Hno_equiv: composite_has_been_sent (equivocator_IM IM) (free_constraint (equivocator_IM IM)) (equivocator_Hbs IM Hbs) (finite_trace_last is tr') input)
  (Hv: let (i, li) := l in vvalid (equivocator_IM IM i) li (finite_trace_last is tr' i, Some input))
  (Hiom: option_protocol_message_prop XE (Some input))
  (Hinit: composite_initial_state_prop (equivocator_IM IM) is)
  (Hproper: proper_equivocator_descriptors IM final_descriptors s)
  (trX': list (composite_transition_item IM))
  (initial_descriptors: equivocator_descriptors IM)
  (Htr_project: equivocators_trace_project IM final_descriptors' tr' = Some (trX', initial_descriptors))
  (Hstate_project: equivocators_state_project IM final_descriptors' (finite_trace_last is tr') = finite_trace_last (equivocators_state_project IM initial_descriptors is) trX')
  (HtrX': finite_protocol_trace_from X' (equivocators_state_project IM initial_descriptors is) trX')
  (His: composite_initial_state_prop IM (equivocators_state_project IM initial_descriptors is))
  (Hzero: forall i : index, final_descriptors i = Existing (IM i) 0 false -> final_descriptors' i = Existing (IM i) 0 false)
  (Hdestination: equivocators_state_project IM final_descriptors s = destination)
  (Hproper': proper_equivocator_descriptors IM final_descriptors' (finite_trace_last is tr'))
  (Htx: (let (si', om') := vtransition (IM (projT1 l)) (fst (projT2 l)) (finite_trace_last (equivocators_state_project IM initial_descriptors is) trX' (projT1 l), Some input) in (state_update IM (finite_trace_last (equivocators_state_project IM initial_descriptors is) trX') (projT1 l) si', om')) = (destination, output))
  (Hvx: vvalid (IM (projT1 l)) (fst (projT2 l)) (finite_trace_last (equivocators_state_project IM initial_descriptors is) trX' (projT1 l), Some input))
  (Htr': finite_protocol_trace FreeE is tr')
  (Htr'pre: finite_protocol_trace (pre_loaded_with_all_messages_vlsm FreeE) is tr')
  (Hproper_initial: proper_equivocator_descriptors IM initial_descriptors is)
  (Hplst: protocol_state_prop X' (finite_trace_last (equivocators_state_project IM initial_descriptors is) trX'))
  (Hs_free: protocol_state_prop FreeE (finite_trace_last is tr'))
  (Hall: trace_has_message (field_selector Common.output) input tr')
  (final_descriptors_m : equivocator_descriptors IM)
  (initial_descriptors_m : equivocator_descriptors IM)
  (trXm: list (composite_transition_item IM))
  (_Hfinal_descriptors_m: not_equivocating_equivocator_descriptors IM final_descriptors_m (finite_trace_last is tr'))
  (Hproject_trXm: equivocators_trace_project IM final_descriptors_m tr' = Some (trXm, initial_descriptors_m))
  (Hex: Exists (field_selector Common.output input) trXm)
  (Hfinal_descriptors_m: proper_equivocator_descriptors IM final_descriptors_m (last (map Common.destination tr') is))
  (Hpr_fin_tr': equivocators_state_project IM final_descriptors_m (finite_trace_last is tr') = finite_trace_last (equivocators_state_project IM initial_descriptors_m is) trXm)
  (HtrXm: finite_protocol_trace X' (equivocators_state_project IM initial_descriptors_m is) trXm)
  (Hproper_initial_m: proper_equivocator_descriptors IM initial_descriptors_m is)
  : constraint
    (existT (fun n : index => vlabel (IM n)) (projT1 l) (fst (projT2 l)))
    (equivocators_state_project IM final_descriptors'
      (finite_trace_last is tr'), Some input)
  .
Proof.
  remember (finite_trace_last is tr') as lst_tr'.
  split.
  - clear -Hdescriptorsi' Hpv.
    specialize
      (full_node_limited_equivocation_constraint_hbo lst_tr' l input Hpv) as Hhbo.
    destruct l as (i, (li, dl)).
    specialize (Hhbo final_descriptors' Hdescriptorsi').
    assumption.
  - unfold globally_known_equivocators_weight.
    specialize
      (full_node_limited_equivocation_constraint_limited lst_tr' l input Hpv)
      as Hlimited.
    destruct l as (i, (li, di)).
    specialize (Hlimited final_descriptors' Hdescriptorsi').
    unfold projT1, projT2 in Hlimited.
    unfold projT1, projT2.
    destruct Hpv as [Hlst [Hinput [_ [_ [_ Hlimit]]]]].
    revert Hlimit.
    apply Rle_trans.
    apply sum_weights_incl; [.. |assumption].
    + apply (known_equivocators_nodup finite_index IM Hbs Hbr i0 sender globally_known_equivocators).
    + apply equivocating_indices_nodup. apply finite_index.
Qed.

(**
Main result of this section, stating that traces which are protocol for the
equivocator-based definition of limited equivocation project to traces which are
protocol for the simple-nodes definition of limited equivocation.
*)
Theorem limited_equivocators_protocol_trace_project
  (final_descriptors : equivocator_descriptors IM)
  (is : composite_state (equivocator_IM IM))
  (tr : list (composite_transition_item (equivocator_IM IM)))
  (final_state := finite_trace_last is tr)
  (Hproper: proper_equivocator_descriptors IM final_descriptors final_state)
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
  apply _equivocators_protocol_trace_project; [assumption | assumption| ..]
  ; intros.
  - split; [exact I|].
    destruct (composite_transition IM l (s, None)) as (s', om') eqn:Ht.
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
  - intros s Hs descriptors Hdescriptors sX m Hmbs l.
Admitted.




End limited_equivocation_state_to_message.