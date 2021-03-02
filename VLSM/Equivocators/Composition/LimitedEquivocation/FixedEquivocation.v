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
    VLSM.Common VLSM.Composition VLSM.Equivocation VLSM.SubProjectionTraces
    VLSM.ProjectionTraces
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
  (equivocator_IM := equivocator_IM IM)
  {index_listing : list index}
  (finite_index : Listing index_listing)
  (equivocating : set index)
  (Hi0_equiv : equivocating <> [])
  (i0 : Inhabited index := @SubProjectionTraces.i0 index equivocating Hi0_equiv)
  .

Existing Instance i0.

(** Definition of fixed-equivocation for states of the composition of equivocators.
*)
Definition state_has_fixed_equivocation
  (s : composite_state equivocator_IM)
  : Prop
  :=
  incl (equivocating_indices IM index_listing s) equivocating.

Definition equivocators_fixed_equivocations_constraint
  (l : composite_label equivocator_IM)
  (som : composite_state equivocator_IM * option message)
  (som' := composite_transition equivocator_IM l som)
  : Prop
  := equivocators_no_equivocations_constraint IM Hbs finite_index l som
  /\ state_has_fixed_equivocation (fst som').


(**
If a future state has fixed equivocation, then so must the current state.
*)
Lemma in_futures_reflects_fixed_equivocation
  (s1 s2 : composite_state equivocator_IM)
  (Hfutures : in_futures (pre_loaded_with_all_messages_vlsm (free_composite_vlsm equivocator_IM)) s1 s2)
  : state_has_fixed_equivocation s2 -> state_has_fixed_equivocation s1.
Proof.
  destruct Hfutures as [tr [Htr Hs2]].
  generalize dependent s2.
  generalize dependent tr. induction tr using rev_ind; intros
  ; [subst s2; assumption|].
  rewrite map_app in Hs2. simpl in Hs2. rewrite last_is_last in Hs2.
  apply finite_protocol_trace_from_app_iff in Htr.
  destruct Htr as [Htr Hx].
  specialize (IHtr Htr _ eq_refl).
  apply IHtr. clear IHtr.
  inversion Hx. subst. clear Hx. simpl in *. clear H3.
  match type of H4 with
  | protocol_transition _ _ (?l, _) _ => remember l as s0
  end.
  clear -H4 H.
  destruct H4 as [_ Ht]. simpl in Ht.
  apply incl_tran with (equivocating_indices IM index_listing s); [|assumption].
  apply equivocators_transition_preserves_equivocating_indices with iom oom l.
  assumption.
Qed.

(** Composition of equivocators with no message equivocation and a
fixed set of machines allowed to state-equivocate.
*)
Definition equivocators_fixed_equivocations_vlsm
  : VLSM message
  :=
  composite_vlsm equivocator_IM equivocators_fixed_equivocations_constraint.

(**
Inclusion in the free composition
*)
Lemma equivocators_fixed_equivocations_vlsm_incl_free
  : VLSM_incl equivocators_fixed_equivocations_vlsm (free_composite_vlsm equivocator_IM).
Proof.
  apply constraint_subsumption_incl.
  intros l som H. exact I.
Qed.

(**
Inclusion in the composition of equivocators with no message equivocation
(no restriction on state equivocation).
*)
Lemma equivocators_fixed_equivocations_vlsm_incl_no_equivocations
  : VLSM_incl equivocators_fixed_equivocations_vlsm (equivocators_no_equivocations_vlsm IM Hbs finite_index).
Proof.
  apply constraint_subsumption_incl.
  intros l som H. apply H.
Qed.

End equivocators_fixed_equivocations_vlsm.

Section fixed_equivocation_without_fullnode.

(**
In this section we define fixed equivocation for the regular composition.
*)

Context
  {message : Type}
  {index : Type}
  {IndEqDec : EqDecision index}
  (IM : index -> VLSM message)
  (Hbs : forall i : index, has_been_sent_capability (IM i))
  (Hbr : forall i : index, has_been_received_capability (IM i))
  (equivocating : set index)
  (Hi0_equiv : equivocating <> [])
  (i0 : Inhabited index := @SubProjectionTraces.i0 index equivocating Hi0_equiv)
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
  (index_equivocating_prop : index -> Prop := sub_index_prop equivocating)
  (equivocating_index : Type := sub_index equivocating)
  (equivocating_i0 : Inhabited equivocating_index := sub_index_i0 equivocating Hi0_equiv)
  (equivocating_IM := sub_IM IM equivocating)
  (equivocating_index_eq_dec : EqDecision equivocating_index := sub_index_eq_dec equivocating)
  (free_equivocating_vlsm_composition : VLSM message := free_composite_vlsm equivocating_IM)
  (sub_equivocator_IM := sub_IM equivocator_IM equivocating)
  .

Existing Instance X_has_been_observed_capability.

(**
[free_equivocating_vlsm_composition] is the free composition of the subset of
nodes which are allowed to equivocate.

[pre_loaded_free_equivocating_vlsm_composition] adds to that composition as initial
messages all initial messages of the full composition, along with those given by
the predicate argument @messageSet@.
*)
Definition pre_loaded_free_equivocating_vlsm_composition
  (messageSet : message -> Prop)
  := pre_loaded_vlsm free_equivocating_vlsm_composition
      (fun m => messageSet m \/ vinitial_message_prop X m).

Context
  {validator : Type}
  .

(**
The fixed equivocation constraint for the regular composition of nodes
stipulates that a message can be received either if receiving it satisfies
the [no_additional_equivocations_constraint] (message [has_been_observed],
or it has the [initial_message_prop]erty), or it can be emited by the
free composition of equivocators pre=loaded with with messages producing
[no_additional_equivocations] for the current state.
*)
Definition fixed_equivocation_constraint
  (l : composite_label IM)
  (som : composite_state IM * option message)
  : Prop
  :=
  no_additional_equivocations_constraint X l som \/
  let (s, om) := som in
  exists m : message, om = Some m /\
  can_emit (pre_loaded_free_equivocating_vlsm_composition (no_additional_equivocations X s)) m.

Existing Instance i0.

(** Composition of regular VLSMs under the [fixed_equivocation_constraint].
*)
Definition fixed_equivocation_vlsm_composition : VLSM message
  := composite_vlsm IM fixed_equivocation_constraint.

End fixed_equivocation_without_fullnode.

Section fixed_equivocation_with_fullnode.

(**
This section instantiates the [full_node_condition_for_admissible_equivocators]
by choosing the admissible indices to be the fixed set of nodes allowed to
equivocate, and then shows that this constraint is stronger than the
[fixed_equivocation_constraint].
*)


(**
Context setting the stage for, and instantiating the
[full_node_condition_for_admissible_equivocators].
It requires that the nodes have [has_been_sent] and [has_been_received]
capabilities, that the number of nodes is finite
*)
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
    (full_node_constraint
      := full_node_condition_for_admissible_equivocators IM Hbs Hbr finite_index admissible_index)
    (full_node_constraint_alt
      := full_node_condition_for_admissible_equivocators_alt IM Hbs Hbr finite_index admissible_index)
    .


(**
Context for the [fixed_equivocation_constraint]. Additionally to the above it
requires that equality on messages is decidable and that the set of VLSMs
allowed to equivocate is non-empty.
*)

  Context
    `{EqDecision message}
    (Hi0_equiv : equivocating <> [])
    (equivocating_index : Type := sub_index equivocating)
    (equivocating_IM := sub_IM IM equivocating)
    (equivocating_index_eq_dec : EqDecision equivocating_index := sub_index_eq_dec equivocating)
    (equivocating_inhabited : Inhabited equivocating_index := sub_index_i0 _ Hi0_equiv)
    (fixed_equivocation_constraint : composite_label IM  -> composite_state IM * option message -> Prop
      := fixed_equivocation_constraint IM Hbs Hbr equivocating Hi0_equiv finite_index)
    (X := free_composite_vlsm IM)
    (X_has_been_sent_capability : has_been_sent_capability X := composite_has_been_sent_capability IM (free_constraint IM) finite_index Hbs)
    (X_has_been_received_capability : has_been_received_capability X := composite_has_been_received_capability IM (free_constraint IM) finite_index Hbr)
    (X_has_been_observed_capability : has_been_observed_capability X := has_been_observed_capability_from_sent_received X)
    .

  Existing Instance  equivocating_inhabited.
  Existing Instance  equivocating_index_eq_dec.
  Existing Instance X_has_been_observed_capability.

  (**
  The [full_node_constraint_alt] is stronger than the [fixed_equivocation_constraint].
  *)
  Lemma fixed_equivocation_constraint_subsumption_alt
    : preloaded_constraint_subsumption IM full_node_constraint_alt fixed_equivocation_constraint.
  Proof.
    intros s Hs l om [Hno_equiv | Hfull]; [left; assumption|].
    destruct Hfull as [m [Hom [i [Hi Hm]]]].
    subst om.
    right. exists m. split; [reflexivity|].
    remember (no_additional_equivocations (free_composite_vlsm IM) s) as P.
    unfold pre_loaded_free_equivocating_vlsm_composition.
    remember (fun m => P m \/ vinitial_message_prop (free_composite_vlsm IM) m) as Q.
    specialize (can_emit_composite_free_lift equivocating_IM P Q) as Hemit.
    spec Hemit. { intros. subst Q. left. assumption. }
    specialize (Hemit (dec_exist _  i Hi)).
    apply Hemit.
    assumption.
  Qed.

  (** If all nodes have the [cannot_resend_message_stepwise_prop]erty, then the
  full node constraint is stronger than the [fixed_equivocation_constraint].

  (by reduction to the result above)
  *)
  Lemma fixed_equivocation_constraint_subsumption
    (Hno_resend : forall i : index, cannot_resend_message_stepwise_prop (IM i))
    : preloaded_constraint_subsumption IM full_node_constraint fixed_equivocation_constraint.
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
    apply fixed_equivocation_constraint_subsumption_alt.
  Qed.

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
  (equivocating : set index)
  (Hi0_equiv : equivocating <> [])
  (i0 : Inhabited index := @SubProjectionTraces.i0 index equivocating Hi0_equiv)
  {index_listing : list index}
  (finite_index : Listing index_listing)
  (XE : VLSM message := equivocators_fixed_equivocations_vlsm IM Hbs finite_index equivocating Hi0_equiv)
  (X : VLSM message := fixed_equivocation_vlsm_composition IM Hbs Hbr equivocating Hi0_equiv finite_index)
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
  (index_equivocating_prop : index -> Prop := sub_index_prop equivocating)
  (equivocating_index : Type := sub_index equivocating)
  (equivocating_i0 : Inhabited equivocating_index := sub_index_i0 equivocating Hi0_equiv)
  (equivocating_IM := sub_IM IM equivocating)
  (equivocating_index_eq_dec : EqDecision equivocating_index := sub_index_eq_dec equivocating)
  (free_equivocating_vlsm_composition : VLSM message := free_composite_vlsm equivocating_IM)
  (sub_equivocator_IM := sub_IM (equivocator_IM IM) equivocating)
  .

Lemma not_equivocating_index_has_singleton_state
  (s : composite_state (equivocator_IM IM))
  (Hs : protocol_state_prop XE s)
  (i : index)
  (Hi : ~In i equivocating)
  : is_singleton_state (IM i) (s i).
Proof.
  apply protocol_state_has_trace in Hs.
  destruct Hs as [is [tr [Htr Hlst]]].
  destruct_list_last tr tr' x Htr'; subst tr.
  - simpl in Hlst. subst s. destruct Htr as [_ His].
    specialize (His i).
    destruct His as [His _]. assumption.
  - destruct Htr as [Htr _].
    apply finite_protocol_trace_from_app_iff in Htr.
    destruct Htr as [_ Hx].
    inversion Hx. subst. clear Hx H2.
    destruct H3 as [[_ [_ [_ Hc]]] Ht].
    destruct Hc as [_ Hfixed].
    simpl in *. rewrite Ht in Hfixed. clear Ht. simpl in Hfixed.
    rewrite! map_app. simpl. rewrite! last_is_last.
    specialize (Hfixed i).
    destruct (decide (projT1 (s0 i) = 0)); [assumption|].
    elim Hi. apply Hfixed.
    apply filter_In. split; [apply finite_index|].
    apply bool_decide_eq_true. assumption.
Qed.

Existing Instance i0.

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

(**
[not_equivocating_equivocator_descriptors] satisfy the
[proper_fixed_equivocator_descriptors] property.
*)
Lemma not_equivocating_equivocatos_descriptors_proper_fixed
  (s : composite_state (equivocator_IM IM))
  (Hs : protocol_state_prop XE s)
  (eqv_descriptors : equivocator_descriptors IM)
  (Heqv_descriptors : not_equivocating_equivocator_descriptors IM eqv_descriptors s)
  : proper_fixed_equivocator_descriptors eqv_descriptors s.
Proof.
  apply not_equivocating_equivocator_descriptors_proper in Heqv_descriptors as Hproper.
  split; [assumption|].
  intros i Hi.
  specialize (not_equivocating_index_has_singleton_state _ Hs _ Hi)
    as Hzero.
  unfold is_singleton_state in Hzero.
  specialize (Heqv_descriptors i). unfold not_equivocating_descriptor in Heqv_descriptors.
  destruct (eqv_descriptors i); [contradiction|].
  destruct b; [contradiction|].
  replace n with 0; [reflexivity|]. lia.
Qed.

(**
Projections of (valid) traces of the composition of equivocators preserve
[proper_fixed_equivocator_descriptors].
*)
Lemma equivocators_trace_project_preserves_proper_fixed_equivocator_descriptors
  (is : composite_state (equivocator_IM IM))
  (tr : list (composite_transition_item (equivocator_IM IM)))
  (Htr : finite_protocol_trace_from (pre_loaded_with_all_messages_vlsm FreeE) is tr)
  (s := last (map destination tr) is)
  (descriptors : equivocator_descriptors IM)
  (idescriptors : equivocator_descriptors IM)
  (trX : list (composite_transition_item IM))
  (HtrX : equivocators_trace_project IM descriptors tr = Some (trX, idescriptors))
  : proper_fixed_equivocator_descriptors descriptors s -> proper_fixed_equivocator_descriptors idescriptors is.
Proof.
  intros [Hproper Hfixed].
  specialize
    (preloaded_equivocators_protocol_trace_project_proper_initial IM
      _ _ Htr _ _ _ HtrX Hproper
    )
    as Hiproper.
  split; [assumption|].
  intros i Hi. specialize (Hfixed i Hi).
  revert Hfixed. clear Hi. revert i.
  apply (equivocators_trace_project_preserves_zero_descriptors IM) with is tr trX
  ; assumption.
Qed.

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

Existing Instance Free_has_been_observed_capability.
Existing Instance Free_has_been_sent_capability.
Existing Instance equivocating_i0.

(**
This is a property of the [fixed_equivocation_constraint] which is being
used to parameterize the [_equivocators_protocol_trace_project] lemma below
allowing it to also be instantiated for the free composition.

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
    (Hdescriptors : proper_fixed_equivocator_descriptors descriptors s)
    (sX := @equivocators_state_project _ _ IndEqDec IM i0 descriptors s)
    (m: message)
    (Hinput : has_been_sent FreeE s m)
    l,
  constraint l (sX, Some m).

(**
Generic proof that the projection of a trace of the composition of equivocators
with no message equivocation and fixed state equivocation is protocol w.r.t.
the composition of the regular nodes constrained by a constraint satisfying
several properties, including the [constraint_has_been_sent_prop]erty.
*)
Lemma _equivocators_protocol_trace_project
  (final_descriptors : equivocator_descriptors IM)
  (is : composite_state (equivocator_IM IM))
  (tr : list (composite_transition_item (equivocator_IM IM)))
  (final_state := last (map destination tr) is)
  (Hproper : proper_fixed_equivocator_descriptors final_descriptors final_state)
  (Htr : finite_protocol_trace XE is tr)
  (constraint : composite_label IM -> composite_state IM * option message -> Prop)
  (HconstraintNone : forall l s, constraint l (s, None))
  (Hconstraintinitial : forall l s m, vinitial_message_prop FreeE m -> constraint l (s, Some m))
  (Hconstraint_hbs :  constraint_has_been_sent_prop constraint)
  (X' := composite_vlsm IM constraint)
  : exists
    (trX : list (composite_transition_item IM))
    (initial_descriptors : equivocator_descriptors IM)
    (isX := equivocators_state_project IM initial_descriptors is)
    (final_stateX := last (map destination trX) isX),
    proper_fixed_equivocator_descriptors initial_descriptors is /\
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
    apply fixed_equivocators_initial_state_project; [|apply Hproper].
    apply Htr.
  - specialize (H (length tr')) as H'.
    spec H'. { rewrite app_length. simpl. lia. }
    destruct Htr as [Htr Hinit].
    apply finite_protocol_trace_from_app_iff in Htr.
    destruct Htr as [Htr Hlst].
    specialize (H' tr' (conj Htr Hinit) eq_refl).
    specialize (equivocators_transition_item_project_proper_characterization IM final_descriptors lst) as Hproperx.
    specialize
      (equivocators_transition_item_project_preserves_zero_descriptors IM final_descriptors lst)
      as Hzero.
    unfold final_state in Hproper. rewrite Htr_lst in Hproper.
    rewrite map_app in Hproper. simpl in Hproper. rewrite last_is_last in Hproper.
    spec Hproperx (proj1 Hproper).
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
    specialize (Hzero oitem final_descriptors' _ Ht Hv Hprojectx).
    specialize (Hproperx Hv Ht).
    destruct Hproperx as [_Hproper' Hx].
    assert (Hproper' : proper_fixed_equivocator_descriptors final_descriptors' (last (map destination tr') is)).
    { split; [assumption|].
      intros i Hi. apply Hzero. clear Hzero. destruct Hproper as [_ Hzero].
      apply Hzero. assumption.
    }
    clear _Hproper' Hzero.
    specialize (H' _ Hproper').
    destruct H' as [trX' [initial_descriptors [_ [Htr_project [Hstate_project HtrX']]]]].
    assert
      (Htr' : finite_protocol_trace FreeE is tr').
    {  split; [|assumption].
      apply VLSM_incl_finite_protocol_trace_from with (machine XE); [apply equivocators_fixed_equivocations_vlsm_incl_free|].
      assumption.
    }
    assert
      (Htr'pre : finite_protocol_trace (pre_loaded_with_all_messages_vlsm FreeE) is tr').
    { split; [|assumption].
      specialize (vlsm_incl_pre_loaded_with_all_messages_vlsm FreeE) as Hincl.
      apply (VLSM_incl_finite_protocol_trace_from _ _ Hincl). apply Htr'.
    }
    specialize
      (equivocators_trace_project_preserves_proper_fixed_equivocator_descriptors _ _ (proj1 Htr'pre) _ _ _ Htr_project Hproper')
      as Hproper_initial.
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
      assert (Hplst : protocol_state_prop X' lst).
      { apply finite_ptrace_last_pstate in HtrX'. subst. assumption. }
      apply (extend_right_finite_trace_from X' lst []); [constructor; assumption|].
      simpl in Hl. subst.
      simpl in Hc.
      destruct Hc as [[Hno_equiv _] Hfixed].
      simpl in Htx,Hvx,Hstate_project.
      rewrite Hstate_project in Hvx, Htx.
      destruct input as [input|]
      ; [|repeat split; [assumption| apply option_protocol_message_None |assumption| apply HconstraintNone |assumption]].
      simpl in Hno_equiv.
      apply or_comm in Hno_equiv.
      destruct Hno_equiv as [Hinit_input | Hno_equiv]
      ; [apply fixed_equivocators_initial_message in Hinit_input|]
      ; [repeat split; [assumption| |assumption| apply Hconstraintinitial; assumption |assumption]|].
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
      spec Hall Htr'.
      specialize (Hall eq_refl).
      destruct (equivocators_trace_project_output_reflecting_inv IM _ _ (proj1 Htr'pre) _ Hall)
        as [final_descriptors_m [initial_descriptors_m [trXm [_Hfinal_descriptors_m [Hproject_trXm Hex]]]]].
      assert (Hfinal_descriptors_m : proper_fixed_equivocator_descriptors final_descriptors_m (last (map Common.destination tr') is)).
      { apply not_equivocating_equivocatos_descriptors_proper_fixed; [|assumption].
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
      exists is, tr', Htr'pre, eq_refl. assumption.
    + exists trX'. exists initial_descriptors. subst foldx. split; [assumption|].
      split; [apply Htr_project|]. split; [|assumption].
      subst tr. clear -Hstate_project Hx.
      rewrite Hstate_project in Hx.
      rewrite <- Hx. f_equal. unfold final_state.
      rewrite map_app. simpl. rewrite last_is_last. reflexivity.
Qed.

(** Instantiating the lemma above with the free constraint.
*)
Lemma free_equivocators_protocol_trace_project
  (final_descriptors : equivocator_descriptors IM)
  (is : composite_state (equivocator_IM IM))
  (tr : list (composite_transition_item (equivocator_IM IM)))
  (final_state := last (map destination tr) is)
  (Hproper : proper_fixed_equivocator_descriptors final_descriptors final_state)
  (Htr : finite_protocol_trace XE is tr)
  : exists
    (trX : list (composite_transition_item IM))
    (initial_descriptors : equivocator_descriptors IM)
    (isX := equivocators_state_project IM initial_descriptors is)
    (final_stateX := last (map destination trX) isX),
    proper_fixed_equivocator_descriptors initial_descriptors is /\
    equivocators_trace_project IM final_descriptors tr = Some (trX, initial_descriptors) /\
    equivocators_state_project IM final_descriptors final_state = final_stateX /\
    finite_protocol_trace (free_composite_vlsm IM) isX trX.
Proof.
  apply _equivocators_protocol_trace_project; [assumption | assumption| ..]
  ; unfold constraint_has_been_sent_prop; intros; exact I.
Qed.

Lemma equivocators_trace_sub_item_input_is_seeded_or_sub_previously_sent
  (is : vstate XE)
  (tr : list (vtransition_item XE))
  (s := last (map destination tr) is)
  (Htr : finite_protocol_trace XE is tr)
  (initial_descriptors final_descriptors: equivocator_descriptors IM)
  (Hproper: proper_fixed_equivocator_descriptors final_descriptors s)
  (trX: list (composite_transition_item IM))
  (Htr_project: equivocators_trace_project IM final_descriptors tr = Some (trX, initial_descriptors))
  (lst_trX := last (map Common.destination trX) (equivocators_state_project IM initial_descriptors is))
  : trace_sub_item_input_is_seeded_or_sub_previously_sent
    (equivocator_IM IM) equivocating
    (no_additional_equivocations (free_composite_vlsm IM) lst_trX) tr.
Proof.
  intros pre item suf m Heq Hm Hitem.
  destruct (free_equivocators_protocol_trace_project final_descriptors is tr Hproper Htr)
    as [_trX [_initial_descriptors [Hinitial_descriptors [_Htr_project [Hfinal_state HtrXFree]]]]].
  rewrite Htr_project in _Htr_project.
  inversion _Htr_project. subst _trX _initial_descriptors. clear _Htr_project.
  assert (HtrXPre : finite_protocol_trace (pre_loaded_with_all_messages_vlsm (free_composite_vlsm IM)) (equivocators_state_project IM initial_descriptors is) trX).
  { apply VLSM_incl_finite_protocol_trace with (machine (free_composite_vlsm IM)); [|apply HtrXFree].
    apply vlsm_incl_pre_loaded_with_all_messages_vlsm.
  }
  assert (Htr_free : finite_protocol_trace  (pre_loaded_with_all_messages_vlsm FreeE) is tr).
  {
    apply VLSM_incl_finite_protocol_trace with (machine XE); [|assumption].
    apply VLSM_incl_trans with (machine FreeE)
    ; [apply equivocators_fixed_equivocations_vlsm_incl_free|].
    apply vlsm_incl_pre_loaded_with_all_messages_vlsm.
  }
  subst tr.
  destruct Htr as [Htr His].
  apply finite_protocol_trace_from_app_iff in Htr as Hsuf. destruct Hsuf as [_ Hsuf].
  rewrite app_assoc in Htr.
  apply finite_protocol_trace_from_app_iff in Htr as Hpre. destruct Hpre as [Hpre _].
  apply finite_protocol_trace_from_app_iff in Hpre. destruct Hpre as [Hpre Hpt].
  destruct (Free_no_additional_equivocation_decidable lst_trX m)
  ; [left; assumption|right].
  unfold no_additional_equivocations in n.
  match type of n with
  | ~ (?o \/ ?i) => assert (Hn : ~ o /\ ~ i) by intuition
  end.
  clear n; destruct Hn as [Hno Hni].
  assert (Hsuf_free : finite_protocol_trace_from (pre_loaded_with_all_messages_vlsm FreeE) (last (map destination pre) is) ([item] ++ suf)).
  { apply VLSM_incl_finite_protocol_trace_from with (machine XE); [|assumption].
    apply VLSM_incl_trans with (machine FreeE)
    ; [apply equivocators_fixed_equivocations_vlsm_incl_free|].
    apply vlsm_incl_pre_loaded_with_all_messages_vlsm.
  }
  assert (Hs_free : protocol_state_prop  (pre_loaded_with_all_messages_vlsm FreeE) s).
  { apply finite_ptrace_last_pstate in Hsuf_free. subst s.
    rewrite map_app. rewrite last_app. assumption.
  }
  inversion Hpt. subst. clear Hpt.
  simpl in Hm. subst iom.
  clear H2.
  destruct H3 as [[_ [_ [_ [[Hc _] Hfixed]]]] Ht].
  simpl in Ht, Hfixed. rewrite Ht in Hfixed. simpl in Hfixed.
  clear Ht.
  destruct Hc as [Hc | Hinit]; [|contradiction].
  assert (Hpre_free : finite_protocol_trace FreeE is pre).
  { apply VLSM_incl_finite_protocol_trace; [|split; assumption].
    apply equivocators_fixed_equivocations_vlsm_incl_free.
  }
  assert (Hpre_lst_free : protocol_state_prop FreeE (last (map destination pre) is)).
  { apply finite_ptrace_last_pstate. apply Hpre_free. }
  apply specialized_proper_sent_rev in Hc; [|assumption].
  specialize (Hc  is pre Hpre_free eq_refl).
  apply Exists_exists in Hc.
  destruct Hc as [pre_item [Hpre_item Hpre_m]].
  exists pre_item. split; [assumption|]. split; [assumption|].
  destruct (in_dec IndEqDec (projT1 (Common.l pre_item)) equivocating)
  ; [assumption|].
  elim Hno.
  assert (Hlst_trX : protocol_state_prop (pre_loaded_with_all_messages_vlsm Free) lst_trX).
  { destruct HtrXPre as [HtrXPre _]. apply finite_ptrace_last_pstate in HtrXPre. assumption. }
  rewrite has_been_observed_sent_received_iff; [|assumption].
  right. apply proper_sent; [assumption|].
  apply has_been_sent_consistency; [assumption| assumption |].
  exists (equivocators_state_project IM initial_descriptors is), trX, HtrXPre, eq_refl.
  apply equivocators_trace_project_app_iff in Htr_project.
  destruct Htr_project as [preX [sufX [final_descriptors' [Hsuf_project [Htr_project Heq]]]]].

  subst trX.
  apply Exists_app. left.

  assert
    (Hfutures : in_futures (pre_loaded_with_all_messages_vlsm FreeE)
      (destination pre_item) s0).
  { apply in_split in  Hpre_item.
    destruct Hpre_item as [pre_pre [pre_suf Hpre_item]].
    change (pre_item :: pre_suf) with ([pre_item] ++ pre_suf) in Hpre_item.
    rewrite app_assoc in Hpre_item.
    rewrite app_assoc in Htr_free.
    destruct Htr_free as [Htr_free _].
    apply finite_protocol_trace_from_app_iff in Htr_free.
    destruct Htr_free as [Htr_s0 _].
    subst pre. clear -Htr_s0.
    rewrite <- app_assoc in Htr_s0.
    apply (finite_protocol_trace_from_app_iff (pre_loaded_with_all_messages_vlsm FreeE)) in Htr_s0.
    destruct Htr_s0 as [_ Hfuture].
    rewrite map_app in Hfuture. simpl in Hfuture. rewrite last_is_last in Hfuture.
    eexists.
    split; [apply Hfuture|].
    rewrite map_app. simpl. rewrite last_is_last. reflexivity.
  }
  apply (@in_futures_reflects_fixed_equivocation _ _ _ IM index_listing equivocating Hi0_equiv)
    in Hfutures
  ; [|assumption].
  clear Hsuf_free Hpre_free.
  destruct Htr_free as [Hpre_free _]. apply finite_protocol_trace_from_app_iff in Hpre_free.
  destruct Hpre_free as [Hpre_free Hsuf_free].
  assert (Hfinal' : forall i, ~In i equivocating -> final_descriptors' i = Existing _ 0 false).
  { specialize (equivocators_trace_project_preserves_zero_descriptors IM _ _ Hsuf_free final_descriptors) as Hpr.
    specialize (Hpr _ _ Hsuf_project).
    intros i Hi.
    apply Hpr. apply (proj2 Hproper). assumption.
  }

  destruct HtrXPre as [HpreX_Pre _].
  apply finite_protocol_trace_from_app_iff in HpreX_Pre.
  destruct HpreX_Pre as [HpreX_Pre _].
  clear Hfixed.
  apply in_split in Hpre_item.
  destruct Hpre_item as [pre' [suf' Hpre_item]].
  change (pre_item :: suf') with ([pre_item] ++ suf') in Hpre_item.
  subst pre.

  apply equivocators_trace_project_app_iff in Htr_project.
  destruct Htr_project as [preX' [sufX' [eqv_descriptors' [Hpr_suf [Hpr_pre HpreX]]]]].
  subst preX. apply Exists_app. right.

  apply (finite_protocol_trace_from_app_iff (pre_loaded_with_all_messages_vlsm FreeE)) in Hpre_free.
  destruct Hpre_free as [Hpre'_free Hsuf'_free].

  apply equivocators_trace_project_app_iff in Hpr_suf.
  destruct Hpr_suf as [pre_itemX [sufX'' [eqv_descriptors'' [Hpr_suf' [Hpr_pre_item HsufX']]]]].
  subst sufX'. apply Exists_app. left.

  apply (finite_protocol_trace_from_app_iff (pre_loaded_with_all_messages_vlsm FreeE)) in Hsuf'_free.
  destruct Hsuf'_free as [Hpre_item_free Hsuf'_free].
  assert (Heqv_descriptors'' : forall i, ~In i equivocating -> eqv_descriptors'' i = Existing _ 0 false).
  { specialize (equivocators_trace_project_preserves_zero_descriptors IM _ _ Hsuf'_free final_descriptors') as Hpr.
    specialize (Hpr _ _ Hpr_suf').
    intros i Hi.
    apply Hpr. apply Hfinal'. assumption.
  }

  assert (Hsingleton_d_pre_item : is_singleton_state (IM (projT1 (Common.l pre_item))) (destination pre_item (projT1 (Common.l pre_item)))).
  { apply not_equivocating_index_has_singleton_state; [|assumption].
    clear -Htr.
    apply finite_protocol_trace_from_app_iff in Htr.
    destruct Htr as [Htr _].
    apply finite_protocol_trace_from_app_iff in Htr.
    destruct Htr as [Htr _].
    apply (finite_protocol_trace_from_app_iff XE) in Htr.
    destruct Htr as [_ Htr].
    apply (finite_protocol_trace_from_app_iff XE) in Htr.
    destruct Htr as [Htr _].
    apply finite_ptrace_last_pstate in Htr. simpl in Htr. assumption.
  }


  clear -Hpr_pre_item Heqv_descriptors'' Hpre_m n Hpre_item_free Hsingleton_d_pre_item.
  specialize (Heqv_descriptors'' _ n).
  simpl in *.
  destruct (equivocators_transition_item_project IM eqv_descriptors'' pre_item)
    as [(o, odescriptor)|] eqn:Hpr
  ; [|congruence].
  destruct pre_item. simpl in *.
  inversion Hpre_item_free. subst. clear Hpre_item_free H2.
  destruct H6 as [[_ [_ [Hv _]]] Ht].
  destruct l. simpl in *. unfold vtransition in Ht. simpl in Ht.
  match type of Ht with
  | (let (_, _) := ?t in _) = _ => destruct t as (si', om') eqn:Hti
  end.
  inversion Ht. subst. rewrite state_update_eq in Hsingleton_d_pre_item. clear Ht.
  specialize (equivocator_transition_no_equivocation_zero_descriptor (IM x) _ _ _ _ _ Hv Hti Hsingleton_d_pre_item)
    as Hsndv.
  unfold equivocators_transition_item_project in Hpr.
  simpl in Hpr.
  destruct v. simpl in Hsndv. subst m0.
  unfold ProjectionTraces.composite_transition_item_projection in Hpr.
  unfold ProjectionTraces.composite_transition_item_projection_from_eq in Hpr.
  simpl in Hpr.
  unfold eq_rect_r in Hpr. simpl in Hpr.
  rewrite Heqv_descriptors'' in Hpr.
  unfold equivocator_vlsm_transition_item_project in Hpr.
  rewrite state_update_eq in Hpr.
  destruct si' as (nsi', bsi').
  destruct (le_lt_dec (S nsi') 0); [lia|].
  destruct (nat_eq_dec 0 0); [|congruence].
  inversion Hpr. subst.
  inversion Hpr_pre_item.
  constructor. reflexivity.
  Unshelve.
  - assumption.
  - assumption.
Qed.

Existing Instance equivocating_i0.
Existing Instance equivocating_index_eq_dec.

Lemma equivocator_vlsm_trace_project_reflect_non_equivocating
  (is: _composite_state (equivocator_IM IM))
  (tr': list (composite_transition_item (equivocator_IM IM)))
  (Htr': finite_protocol_trace XE is tr')
  (input: message)
  (final_descriptors': equivocator_descriptors IM)
  (Hproper': proper_fixed_equivocator_descriptors final_descriptors' (last (map destination tr') is))
  (trX': list (composite_transition_item IM))
  (initial_descriptors: equivocator_descriptors IM)
  (Htr_project: equivocators_trace_project IM final_descriptors' tr' = Some (trX', initial_descriptors))
  (item: composite_transition_item (equivocator_IM IM))
  (Hitem: In item tr')
  (Houtput: output item = Some input)
  (Hno_equiv_item: ~ In (projT1 (l item)) equivocating)
  : trace_has_message (field_selector output) input trX'.
Proof.
  apply in_split in Hitem.
  destruct Hitem as [pre [suf Heq_tr']].
  replace (item :: suf) with ([item] ++ suf) in Heq_tr' by reflexivity.
  subst tr'.
  apply equivocators_trace_project_app_iff in Htr_project.
  destruct Htr_project as [preX [item_sufX [eqv_pre [Hpr_item_suf [Hpr_pre Heq_trX]]]]].
  subst trX'.
  apply Exists_app. right.
  apply equivocators_trace_project_app_iff in Hpr_item_suf.
  destruct Hpr_item_suf as [itemXs [sufX [eqv_item [Hpr_suf [Hpr_item Heq_item_sufX]]]]].
  subst item_sufX.
  apply Exists_app. left.
  destruct Htr' as [Htr' _].
  rewrite app_assoc in Htr'.
  apply finite_protocol_trace_from_app_iff in Htr'.
  destruct Htr' as [Hpre Hsuf].
  apply finite_protocol_trace_from_app_iff in Hpre.
  destruct Hpre as [_ Hitem].
  rewrite app_assoc in Hproper'. rewrite map_app in Hproper'. rewrite last_app in Hproper'.
  rewrite map_app in Hsuf, Hproper'. simpl in Hsuf, Hproper'. rewrite last_is_last in Hsuf, Hproper'.
  assert (Hsufpre : finite_protocol_trace_from (pre_loaded_with_all_messages_vlsm FreeE) (destination item) suf).
  {
    revert Hsuf. apply VLSM_incl_finite_protocol_trace_from.
    apply VLSM_incl_trans with (machine FreeE).
    - apply equivocators_fixed_equivocations_vlsm_incl_free.
    - apply vlsm_incl_pre_loaded_with_all_messages_vlsm.
  }
  specialize
    (equivocators_trace_project_preserves_proper_fixed_equivocator_descriptors _ _ Hsufpre
      final_descriptors' eqv_item _ Hpr_suf Hproper'
    ) as Hproper_item.
  destruct Hproper_item as [Hproper_item Hproper_fixed_item].
  specialize (Hproper_fixed_item _ Hno_equiv_item).
  specialize
    (no_equivocating_equivocators_transition_item_project IM eqv_item item
      Hproper_fixed_item
    ) as Hex.
  spec Hex.
  {
    apply not_equivocating_index_has_singleton_state; [|assumption].
    apply finite_ptrace_last_pstate in Hitem. assumption.
  }
  inversion Hitem; subst. destruct H3 as [[Hs [Hiom [Hv Hc]]] Ht].
  specialize (Hex _ Hv Ht). simpl in Hex.
  simpl in Hpr_item. rewrite Hex in Hpr_item.
  inversion_clear Hpr_item.
  constructor. assumption.
Qed.

Lemma has_not_been_observed_piecewise
  (is: _composite_state (equivocator_IM IM))
  (tr': list (composite_transition_item (equivocator_IM IM)))
  (Htr': finite_protocol_trace XE is tr')
  (final_descriptors': equivocator_descriptors IM)
  (Hproper': proper_fixed_equivocator_descriptors final_descriptors' (last (map destination tr') is))
  (trX': list (composite_transition_item IM))
  (initial_descriptors: equivocator_descriptors IM)
  (Htr_project: equivocators_trace_project IM final_descriptors' tr' = Some (trX', initial_descriptors))
  (input: message)
  (Hno: ~ has_been_observed Free (last (map destination trX') (equivocators_state_project IM initial_descriptors is)) input)
  : forall item : composite_transition_item (equivocator_IM IM),
      In item tr' -> output item = Some input -> In (projT1 (l item)) equivocating.
Proof.
  destruct (free_equivocators_protocol_trace_project final_descriptors' is tr' Hproper' Htr')
    as [_trX' [_initial_descriptors [_ [_Htr_project [_ HtrX']]]]].
  rewrite Htr_project in _Htr_project.
  inversion _Htr_project. subst _trX' _initial_descriptors. clear _Htr_project.
  intros item Hitem Houtput.
  destruct (in_dec IndEqDec (projT1 (l item)) equivocating); [assumption|].
  elim Hno. clear Hno.
  specialize
    (@has_been_observed_sent_received_iff _
      Free Free_has_been_received_capability
      Free_has_been_sent_capability
      Free_has_been_observed_capability
    ) as Hsent_received.
  assert (HtrX'_free : finite_protocol_trace (pre_loaded_with_all_messages_vlsm Free) (equivocators_state_project IM initial_descriptors is) trX').
  {
    revert HtrX'. clear. apply VLSM_incl_finite_protocol_trace.
    apply vlsm_incl_pre_loaded_with_all_messages_vlsm.
  }
  specialize (finite_ptrace_last_pstate _ _ _ (proj1 HtrX'_free)) as Hfree_lst.
  specialize (Hsent_received _ Hfree_lst input).
  apply Hsent_received. clear Hsent_received. right.
  apply proper_sent; [assumption|].
  apply has_been_sent_consistency; [assumption| assumption |].
  exists (equivocators_state_project IM initial_descriptors is), trX', HtrX'_free, eq_refl.
  clear HtrX' HtrX'_free Hfree_lst.
  apply equivocator_vlsm_trace_project_reflect_non_equivocating with is tr' final_descriptors' initial_descriptors item
  ; assumption.
Qed.

Lemma fixed_equivocation_constraint_has_constraint_has_been_sent_prop
  : constraint_has_been_sent_prop
    (fixed_equivocation_constraint IM Hbs Hbr equivocating Hi0_equiv finite_index).
Proof.
  unfold constraint_has_been_sent_prop. intros.
  match goal with
  |- fixed_equivocation_constraint _ _ _ _ _ _ _ (?l, _) => remember l as sX
  end.
  destruct (Free_no_additional_equivocation_decidable sX m)
  ; [left; assumption|right].
  exists m. split; [reflexivity|].
  unfold no_additional_equivocations in n.
  match type of n with
  | ~ (?o \/ ?i) => assert (Hn : ~ o /\ ~ i) by intuition
  end.
  clear n; destruct Hn as [Hno Hni].
  apply protocol_state_has_trace in Hs.
  destruct Hs as [is [tr [Htr Heqs]]]. subst s.

  assert (Htr'pre : finite_protocol_trace (pre_loaded_with_all_messages_vlsm FreeE) is tr).
  { revert Htr. apply VLSM_incl_finite_protocol_trace.
    apply VLSM_incl_trans with (machine FreeE).
    - apply
      (constraint_free_incl (equivocator_IM IM) (equivocators_fixed_equivocations_constraint IM Hbs
        finite_index equivocating Hi0_equiv)).
    - apply vlsm_incl_pre_loaded_with_all_messages_vlsm.
  }

  destruct
    (preloaded_equivocators_protocol_trace_from_project IM
      descriptors is tr (proj1 Hdescriptors) (proj1 Htr'pre)
    )
    as [trX [initial_descriptors [Htr_project [_ Hlst]]]].
  simpl in Hlst, HeqsX.
  rewrite Hlst in  HeqsX.
  specialize
    (equivocators_trace_sub_item_input_is_seeded_or_sub_previously_sent
      _ _ Htr initial_descriptors descriptors Hdescriptors _ Htr_project
    ) as Hsub.
  specialize
    (finite_protocol_trace_sub_projection (equivocator_IM IM) equivocating Hi0_equiv
      (equivocators_fixed_equivocations_constraint IM Hbs finite_index equivocating Hi0_equiv)
      (equivocator_Hbs IM Hbs)
      finite_index
      (no_additional_equivocations (free_composite_vlsm IM) sX)
    ) as Hproject.
  spec Hproject.
  { intros l' (s', om').
    unfold equivocators_fixed_equivocations_constraint.
    unfold equivocators_no_equivocations_constraint.
    unfold no_equivocations_additional_constraint.
    clear. intuition.
  }
  spec Hproject is tr.
  spec Hproject. { subst sX. assumption. }
  spec Hproject Htr.
  clear Hsub.
  subst sX.
  unfold pre_loaded_free_equivocating_vlsm_composition.
  assert (Hplst : protocol_state_prop (pre_loaded_with_all_messages_vlsm FreeE) (last (map destination tr) is)).
  { apply (finite_ptrace_last_pstate (pre_loaded_with_all_messages_vlsm FreeE)).
    apply Htr'pre.
  }
  apply proper_sent in Hinput; [|assumption].
  specialize (Hinput is tr Htr'pre eq_refl).
  apply (equivocators_trace_project_output_reflecting_iff _ _ _ (proj1 Htr'pre)) in Hinput.
  destruct Hinput as [final_descriptors_m [initial_descriptors_m [trXm [Hfinal_descriptors_m [Hproject_trXm Hex]]]]].
  specialize
    (seeded_equivocators_protocol_trace_project (sub_IM IM equivocating)
      (sub_has_been_sent_capabilities IM equivocating Hbs)
      (finite_sub_index equivocating finite_index)
      (fun m : message =>
        no_additional_equivocations (free_composite_vlsm IM)
          (last (map Common.destination trX)
             (equivocators_state_project IM initial_descriptors is)) m \/
        vinitial_message_prop (free_composite_vlsm IM) m)
      (fun i => final_descriptors_m (proj1_sig i))
      (composite_state_sub_projection (equivocator_IM IM) equivocating is)
      (finite_trace_sub_projection (equivocator_IM IM) equivocating tr)
    ) as Hsub_project.
  simpl in Hsub_project.
  spec Hsub_project.
  { specialize (preloaded_finite_trace_sub_projection_last_state (equivocator_IM IM) equivocating Hi0_equiv _ _ (proj1 Htr'pre))
      as Heq_lst.
    simpl in Heq_lst.
    match goal with
    |- proper_equivocator_descriptors _ _ ?l =>
      match type of Heq_lst with
      | _ = ?l' =>
        replace l with l'
      end
    end.
    intros e.
    destruct e. simpl.
    unfold sub_IM. unfold composite_state_sub_projection. simpl.
    apply not_equivocating_equivocator_descriptors_proper in Hfinal_descriptors_m.
    apply Hfinal_descriptors_m.
  }
  spec Hsub_project.
  { clear -Hproject.
    unfold seeded_equivocators_no_equivocation_vlsm.
    destruct Hproject as [Hproject Hinit].
    split; [|assumption].
    eapply VLSM_incl_finite_protocol_trace_from; [|apply Hproject].
    unfold composite_vlsm.
    unfold mk_vlsm. unfold projT2.
    match goal with
    |- VLSM_incl_part ?MX ?MY =>
      apply (basic_VLSM_incl MX MY)
    end
    ; intros; [assumption | .. | reflexivity].
    - apply initial_message_is_protocol.
      simpl.
      destruct H0; [|right; left; assumption].
      simpl in H0. left. assumption.
    - destruct H as [Hs [_ [Hv Hc]]].
      split; [assumption|].
      destruct Hc as [Hc _].
      split; [|exact I].
      destruct om; [| exact I].
      simpl in Hc. simpl.
      destruct Hc as [Hc | [Hc | Hc]]
      ; [| right; left; assumption| right; right; left; assumption].
      left.
      destruct Hc as [subi Hibs].
      exists subi. revert Hibs.
      apply has_been_sent_irrelevance.

      match type of Hs with
      | context [composite_vlsm_machine ?IM ?constraint] =>
        apply (preloaded_protocol_state_projection IM constraint)
      end.
      revert Hs.
      apply VLSM_incl_protocol_state.
      apply pre_loaded_vlsm_incl_pre_loaded_with_all_messages.
  }
  destruct Hsub_project
    as [trX' [initial_descriptors' [Hinitial_descriptors' [Hpr_tr' [Hpr_lst_tr' HtrX]]]]].
  specialize
    (has_not_been_observed_piecewise _ _ Htr
      _ Hdescriptors
      _ _ Htr_project
      _ Hno
    ) as Hno'.
  destruct
    (equivocators_trace_project_finite_trace_sub_projection_commute IM equivocating Hi0_equiv
      final_descriptors_m initial_descriptors_m initial_descriptors' tr trXm trX'
      Hproject_trXm Hpr_tr'
    )
    as [_ HeqtrX].
  remember
    (equivocators_state_project (sub_IM IM equivocating) initial_descriptors'
      (composite_state_sub_projection (equivocator_IM IM) equivocating is)
    ) as isX.
  clear - HeqtrX HtrX Hno' Hex Hproject_trXm (* Htr'pre Hfinal_descriptors_m *).
  apply can_emit_from_protocol_trace with isX trX'; [assumption|].

  apply Exists_exists in Hex.
  destruct Hex as [output_itemX [Hin Houtput_select]].
  apply in_split in Hin.
  destruct Hin as [preX [sufX Heq_trXm]].
  change (output_itemX :: sufX) with ([output_itemX] ++ sufX) in Heq_trXm.
  subst trXm.
  apply equivocators_trace_project_app_inv_item in Hproject_trXm.
  destruct Hproject_trXm as [pre [suf [item [item_descriptors [pre_descriptors [Hpr_suf [Hpr_item [Hpr_pre Heqtr]]]]]]]].
  subst.

  specialize (Hno' item).
  spec Hno'.
  { rewrite !in_app_iff. right. left. left. reflexivity. }
  rewrite! (finite_trace_sub_projection_app IM).
  unfold trace_has_message.
  rewrite! Exists_app. right. left. simpl.

  unfold equivocators_transition_item_project in Hpr_item.
  destruct
    (equivocator_vlsm_transition_item_project (IM (projT1 (l item)))
      (composite_transition_item_projection (equivocator_IM IM) item)
      (item_descriptors (projT1 (l item)))
    ) as [(o, deqv')|] eqn:Hpr_itemi
    ; [|congruence].
  destruct o as [item'|]; [|congruence].
  inversion Hpr_item. subst. spec Hno' Houtput_select.
  unfold from_sub_projection. simpl.
  destruct (decide (sub_index_prop equivocating (projT1 (l item))))
  ; [|contradiction].
  constructor. simpl. assumption.
Qed.

Theorem fixed_equivocators_protocol_trace_project
  (final_descriptors : equivocator_descriptors IM)
  (is : composite_state (equivocator_IM IM))
  (tr : list (composite_transition_item (equivocator_IM IM)))
  (final_state := last (map destination tr) is)
  (Hproper: proper_fixed_equivocator_descriptors final_descriptors final_state)
  (Htr : finite_protocol_trace XE is tr)
  : exists
    (trX : list (composite_transition_item IM))
    (initial_descriptors : equivocator_descriptors IM)
    (isX := equivocators_state_project IM initial_descriptors is)
    (final_stateX := last (map destination trX) isX),
    proper_fixed_equivocator_descriptors initial_descriptors is /\
    equivocators_trace_project IM final_descriptors tr = Some (trX, initial_descriptors) /\
    equivocators_state_project IM final_descriptors final_state = final_stateX /\
    finite_protocol_trace X isX trX.
Proof.
  apply _equivocators_protocol_trace_project; [assumption | assumption| ..]
  ; intros.
  - left. exact I.
  - left. right. assumption.
  - apply fixed_equivocation_constraint_has_constraint_has_been_sent_prop.
Qed.

End from_equivocators_to_nodes.
