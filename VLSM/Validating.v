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
