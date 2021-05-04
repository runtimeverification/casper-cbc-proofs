From Coq Require Import FinFun List.

From CasperCBC Require Import Lib.Preamble VLSM.Common VLSM.Composition VLSM.ProjectionTraces.

(** * VLSM Validating Projections

In the sequel we fix a composite VLSM <<X>> obtained from an indexed family
of VLSMs <<IM>> and a <<constraint>>, and an index <<i>>, corresponding to
component <<IM i>>.
*)

Section validating_projection.

Context
    {message : Type}
    {index : Type}
    {IndEqDec : EqDecision index}
    (IM : index -> VLSM message)
    {i0 : Inhabited index}
    (constraint : composite_label IM -> composite_state IM * option message -> Prop)
    (X := composite_vlsm IM constraint)
    (i : index)
    (Xi := composite_vlsm_constrained_projection IM constraint i)
    .

(**
We say that the component <<i>> of X is validating received messages if
non-[projection_valid]itiy implied non-component-[valid]ity.
*)

Definition validating_projection_received_messages_prop
    :=
    forall (li : vlabel (IM i)) (si : vstate (IM i)) (mi : message),
        ~ vvalid Xi li (si, Some mi)
        -> ~ protocol_valid (pre_loaded_with_all_messages_vlsm (IM i)) li (si, Some mi).

(**
We can slightly generalize the definition above to also include empty messages
and state it in a positive manner as the [validating_projection_prop]erty below,
requiring that [valid]ity in the component implies [projection_valid]ity.
*)

Definition validating_projection_prop :=
    forall (li : vlabel (IM i)) (siomi : vstate (IM i) * option message),
        protocol_valid (pre_loaded_with_all_messages_vlsm (IM i)) li siomi ->
        vvalid Xi li siomi.

Definition lifted_state_satisfying_constraint
  (li : vlabel (IM i)) (si : vstate (IM i)) (om : option message) (s : vstate X) : Prop
  := protocol_state_prop X s /\ s i = si /\  constraint (existT _ i li) (s, om).

Definition valid_subsumes_constraint_prop : Prop :=
  forall (li : vlabel (IM i)) (si : vstate (IM i)) (om : option message),
    protocol_valid (pre_loaded_with_all_messages_vlsm (IM i)) li (si, om) ->
    exists (s : vstate X), lifted_state_satisfying_constraint li si om s.

Lemma validating_projection_prop_impl_valid_subsumes_constraint_prop :
  validating_projection_prop -> valid_subsumes_constraint_prop.
Proof.
  intros Hvalidating.
  intros li si om Hv.
  apply Hvalidating in Hv.
  destruct Hv as [s [Heq [Hs [_ [_ Hc]]]]].
  exists s. repeat split; assumption.
Qed.

Definition valid_message_is_protocol_in_composition_prop : Prop :=
  forall
  (om : option message)
  (li : vlabel (IM i))
  (si : vstate (IM i)),
  protocol_valid (pre_loaded_with_all_messages_vlsm (IM i)) li (si, om) ->
  option_protocol_message_prop X om.


Lemma validating_projection_prop_impl_valid_message_is_protocol_in_composition_prop:
  validating_projection_prop -> valid_message_is_protocol_in_composition_prop.
Proof.
  intros Hvalidating mi li si Hpv.
  unfold validating_projection_prop in Hvalidating.
  specialize (Hvalidating li (si, mi) Hpv).
  clear Hpv.
  unfold vvalid in Hvalidating. simpl in Hvalidating.
  destruct Hvalidating as [s [Hsi [Hpsp [Hopmp Hccv]]]].
  inversion Hopmp.
  unfold protocol_message_prop.
  exists x. apply H.
Qed.


Lemma lift_reachability_to_protocol :
  valid_subsumes_constraint_prop ->
  valid_message_is_protocol_in_composition_prop ->
  forall si,
  protocol_state_prop (pre_loaded_with_all_messages_vlsm (IM i)) si ->
  exists s, s i = si /\ protocol_state_prop (composite_vlsm IM constraint) s.
Proof.
      intros Hcp Hpcp si Hsi.
      apply protocol_state_prop_iff in  Hsi.
      destruct Hsi as [[[s Hs] Heq] | [l [(s, om) [om' Ht]]]]. 
      - simpl in Heq. subst si. exists (lift_to_composite_state IM i s).
        unfold lift_to_composite_state. rewrite state_update_eq.
        split; [reflexivity|].
        apply initial_is_protocol.
        intro n.
        destruct (decide (n = i)).
        + subst n. rewrite state_update_eq. assumption.
        + rewrite state_update_neq by assumption.  apply (proj2_sig (vs0 (IM n))).
      - destruct Ht as [Hv Ht].
        apply Hcp in Hv as Hcpv.
        apply Hpcp in Hv as Hpcpv.
        destruct Hcpv as [s0 [Hs0 [Heq Hc]]].
        destruct (composite_transition IM (existT _ i l) (s0, om)) as (s', _om') eqn:Hct.
        exists s'.
        split.
        + simpl in Hct. rewrite Heq in Hct.
          match type of Hct with
          | (let (_,_) := ?t in _) = _ => replace t with (si, om') in Hct
          end.
          inversion Hct.
          subst _om' s'. clear Hct.
          rewrite state_update_eq.
          reflexivity.
        + apply protocol_state_prop_iff. right.
          exists (existT _ i l), (s0, om), _om'.
          split; [|assumption].
          destruct Hv as [_ [_ Hv]].
          repeat split; try assumption.
          simpl. rewrite Heq. assumption.
Qed.


Lemma alt_impl_validating_projection_prop:
  valid_subsumes_constraint_prop ->
  valid_message_is_protocol_in_composition_prop ->
  validating_projection_prop.
Proof.
  intros Hcp Hpcp li [si omi] Hpv.
  pose proof (Hcp' := Hcp li si omi Hpv).
  pose proof (Hpcp' := Hpcp omi li si Hpv).
  destruct Hcp' as [s [Hs [Hsi Hconstraint]]].
  (*clear Hpv.*)
  unfold vvalid. unfold valid. unfold machine. simpl.
  (*exists (lift_to_composite_state IM i si).*)
  exists s.
  split.
  { apply Hsi. }
  unfold protocol_message_prop in Hpcp'.
  destruct Hpcp' as [s' Hpp].
  split; [assumption|].
  
  split.
  { unfold option_protocol_message_prop.
    exists s'.
    apply Hpp.
  }
  unfold constrained_composite_valid.
  split.
  { unfold composite_valid. rewrite Hsi.
    unfold protocol_valid in Hpv. destruct Hpv as [_ [_ Hvalid]]. apply Hvalid.
  }
  apply Hconstraint.
Qed.

(**
It is easy to see that the [validating_projection_prop]erty includes the
[validating_projection_received_messages_prop]erty.
*)
Lemma validating_projection_messages_received
    : validating_projection_prop -> validating_projection_received_messages_prop.
Proof.
    unfold validating_projection_prop. unfold validating_projection_received_messages_prop. intros.
    intro Hvalid. elim H0. clear H0.
    specialize (H li (si, Some mi) Hvalid). assumption.
Qed.

(**
We say that component <<i>> is [validating_transitions] if any [valid]
transition in component <<i>> can be "lifted" to a [protocol_transition] in <<X>>.

*)

Definition validating_transitions :=
    forall
        (si : vstate (IM i))
        (omi : option message)
        (li : vlabel (IM i))
        ,
        protocol_valid (pre_loaded_with_all_messages_vlsm (IM i)) li (si, omi)
        ->
        (exists
            (s s' : vstate X)
            (om' : option message),
            si = s i
            /\
            protocol_transition X (existT _ i li) (s, omi) (s', om')
        ).

(**
Next two results show that the (simpler) [validating_projection_prop]erty
is equivalent with the [validating_transitions] property.
*)

Lemma validating_projection_messages_transitions
    : validating_projection_prop -> validating_transitions.
Proof.
    unfold validating_projection_prop. unfold validating_transitions.
    unfold projection_valid. unfold protocol_transition.
    simpl. intros.
    specialize (H li (si, omi) H0). clear H0. simpl in H.
    destruct H as [s [Hsi [Hps [Hopm [Hvalid Hctr]]]]].
    remember (vtransition X (existT _ i li) (s, omi)) as t.
    destruct t as [s' om'].
    exists s. exists s'. exists om'.
    symmetry in Hsi. subst si; simpl.
    repeat split; try assumption.
    unfold vtransition in Heqt.
    simpl in Heqt.
    remember (vtransition (IM i) li (s i, omi)) as t.
    destruct t as [si' om''].
    inversion Heqt; subst.
    reflexivity.
Qed.

Lemma validating_transitions_messages
    : validating_transitions -> validating_projection_prop.
Proof.
    unfold validating_projection_prop. unfold validating_transitions. intros.
    destruct siomi as [si omi].
    specialize (H si omi li H0); clear H0.
    destruct H as [s [s' [om' [Hsi [Hvalid Htransition]]]]].
    symmetry in Hsi.
    exists s. split; assumption.
Qed.

(** ** Validating projections and Byzantine behavior

In the sequel we assume that <<X>> has the [validating_projection_prop]erty for
component <<i>>.  Let <<Xi>> be the projection of <<X>> to component <<i>>
and <<Preloaded>> be the [pre_loaded_with_all_messages_vlsm] associated to component <<i>>.
*)

Section pre_loaded_with_all_messages_validating_proj.
    Context
        (Hvalidating : validating_projection_prop)
        (PreLoaded := pre_loaded_with_all_messages_vlsm (IM i))
        .

(**
We can show that <<Preloaded>> is included in <<Xi>> by applying the
meta-lemma [basic_VLSM_incl], using the [validating_projection_prop]erty and
Lemma [protocol_message_projection] to show that its conditions are fulfilled.
*)

    Lemma pre_loaded_with_all_messages_validating_proj_incl
        : VLSM_incl PreLoaded Xi.
    Proof.
        apply VLSM_incl_finite_traces_characterization.
        intros.
        split; [|apply H].
        induction H using finite_protocol_trace_rev_ind.
        - apply (finite_ptrace_empty Xi). apply initial_is_protocol. assumption.
        - apply (extend_right_finite_trace_from Xi);[assumption|].
          destruct Hx as [Hvx Htx].
          split; [|assumption].
          apply projection_valid_protocol.
          apply Hvalidating.
          assumption.
    Qed.

(**
Given that any projection is included in the [pre_loaded_with_all_messages_vlsm] of its component
(Lemma [proj_pre_loaded_with_all_messages_incl]), we conclude that <<Preloaded>> and <<Xi>> are
trace-equal.  This means that all the byzantine behavior of a
validating component is exhibited by its corresponding projection.
*)
    Lemma pre_loaded_with_all_messages_validating_proj_eq
        : VLSM_eq PreLoaded Xi.
    Proof.
        split.
        - apply pre_loaded_with_all_messages_validating_proj_incl.
        - apply proj_pre_loaded_with_all_messages_incl.
    Qed.

End pre_loaded_with_all_messages_validating_proj.

End validating_projection.

(** ** VLSM self-validation *)

Section validating_vlsm.

Context
    {message : Type}
    (X : VLSM message)
    .

(**
Let us fix a (regular) VLSM <<X>>. <<X>> is (self-)validating if every [valid]
[state] and <<message>> are [protocol_state] and [protocol_message] for that
VLSM, respectively.
*)

Definition validating_vlsm_prop
    :=
    forall (l : label) (s : state) (om : option message),
        protocol_valid (pre_loaded_with_all_messages_vlsm X) l (s, om) ->
        protocol_valid X l (s, om).

(**
In the sequel we will show that a VLSM with the [validating_vlsm_prop]erty
is trace-equal to its associated [pre_loaded_with_all_messages_vlsm], basically meaning that
(due to Lemma [byzantine_pre_loaded_with_all_messages]) all traces with
the [byzantine_trace_prop]erty associated to a validating VLSMs are also
[protocol_trace]s for that VLSM, meaning that the VLSM cannot exhibit
byzantine behavior.
*)

Context
    (Hvalidating : validating_vlsm_prop)
    (PreLoaded := pre_loaded_with_all_messages_vlsm X)
    .

(**
Let <<PreLoaded>> be the [pre_loaded_with_all_messages_vlsm] associated to X.
From Lemma [vlsm_incl_pre_loaded_with_all_messages_vlsm] we know that <<X>> is included
in <<PreLoaded>>.

To prove the converse we use the [validating_vlsm_prop]erty to
verify the conditions of meta-lemma [basic_VLSM_incl].
*)

    Lemma pre_loaded_with_all_messages_validating_vlsm_incl
        : VLSM_incl PreLoaded X.
    Proof.
        unfold validating_vlsm_prop  in Hvalidating.
        destruct X as [T [S M]]. simpl in *.
        apply VLSM_incl_finite_traces_characterization.
        intros.
        split; [|apply H].
        destruct H as [Htr Hs].
        induction tr using rev_ind.
        - constructor. apply initial_is_protocol. assumption.
        - apply finite_protocol_trace_from_app_iff in Htr.
          destruct Htr as [Htr Hx].
          specialize (IHtr Htr).
          apply (finite_protocol_trace_from_app_iff (mk_vlsm M)).
          split; [assumption|].
          apply (first_transition_valid (mk_vlsm M)).
          apply first_transition_valid in Hx.
          destruct Hx as [Hvx Htx].
          split; [|assumption].
          revert Hvx.
          apply Hvalidating.
    Qed.

(**
We conclude that <<X>> and <<Preloaded>> are trace-equal.
*)

    Lemma pre_loaded_with_all_messages_validating_vlsm_eq
        : VLSM_eq PreLoaded X.
    Proof.
        split.
        - apply pre_loaded_with_all_messages_validating_vlsm_incl.
        - pose (vlsm_incl_pre_loaded_with_all_messages_vlsm X) as Hincl.
          destruct X as (T, (S, M)).
          apply Hincl.
    Qed.

End validating_vlsm.
