From Coq Require Import FinFun FunctionalExtensionality.

Require Import Coq.Program.Tactics.

From CasperCBC Require Import
    Lib.Classes
    VLSM.Common
    VLSM.Composition
    VLSM.Equivocation
    .

Section no_equivocations.

Context
  {message : Type}
  (vlsm : VLSM message)
  .

  (** It is now straightforward to define a [no_equivocations] composition constraint.
      An equivocating transition can be detected by calling the [has_been_sent]
      oracle on its arguments and we simply forbid them.

      However, since we might allow certain other messages, such as initial
      messages, we give a slightly more general definition, that of
      [no_equivocation_except_from] those specified by a given predicate.
  **)

    Definition no_equivocations_except_from
      {Hbs : has_been_sent_capability vlsm}
      (exception : message -> Prop)
      (l : vlabel vlsm)
      (som : state * option message)
      :=
      let (s, om) := som in
      match om with
      | None => True
      | Some m => has_been_sent vlsm s m \/ exception m
      end.

    (** The [no_equivocations] constraint does not allow any exceptions
    (messages being received must have been previously sent).
    *)
    Definition no_equivocations
      {Hbs : has_been_sent_capability vlsm}
      (l : vlabel vlsm)
      (som : state * option message)
      : Prop
      :=
      no_equivocations_except_from (fun m => False) l som.

End no_equivocations.

(**
*** No-Equivocation Invariants

A VLSM that enforces the [no_equivocations] constraint and also
supports [has_been_recevied] (or [has_been_observed]) obeys an
invariant that any message that tests as [has_been_received]
(resp. [has_been_observed]) in a state also tests as [has_been_sent]
in the same state.
 *)
Section NoEquivocationInvariants.
  Context
    message
    (X: VLSM message)
    (Hhbs: has_been_sent_capability X)
    (Hhbo: has_been_observed_capability X)
    (Henforced: forall l s om, vvalid X l (s,om) -> no_equivocations X l (s,om))
  .

  Definition observed_were_sent (s: state) : Prop :=
    forall msg, has_been_observed X s msg -> has_been_sent X s msg.

  Lemma observed_were_sent_initial s:
    vinitial_state_prop X s ->
    observed_were_sent s.
  Proof.
    intros Hinitial msg Hsend.
    contradict Hsend.
    apply (oracle_no_inits has_been_observed_stepwise_props).
    assumption.
  Qed.

  Lemma observed_were_sent_preserved l s im s' om:
    protocol_transition X l (s,im) (s',om) ->
    observed_were_sent s ->
    observed_were_sent s'.
  Proof.
    intros Hptrans Hprev msg Hobs.
    specialize (Hprev msg).
    apply preloaded_weaken_protocol_transition in Hptrans.
    apply (oracle_step_update has_been_observed_stepwise_props _ _ _ _ _ Hptrans) in Hobs.
    simpl in Hobs.
    specialize (Henforced l s (Some msg)).
    rewrite (oracle_step_update (has_been_sent_stepwise_from_trace Hhbs) _ _ _ _ _ Hptrans).
    destruct Hptrans as [[_ [_  Hv]] _].
    destruct Hobs as [[|]|].
    - (* by [no_equivocations], the incoming message [im] was previously sent *)
      rewrite H in Hv.
      specialize (Henforced Hv).
      destruct Henforced; [|contradiction].
      right. assumption.
    - left. assumption.
    - specialize (Hprev H).
      right. assumption.
  Qed.

  Lemma observed_were_sent_invariant s:
    protocol_state_prop X s ->
    observed_were_sent s.
  Proof.
    intro Hproto.
    induction Hproto using protocol_state_prop_ind.
    - intros msg Hsend.
      contradict Hsend.
      apply (oracle_no_inits has_been_observed_stepwise_props).
      assumption.
    - intros msg Hobs.
      specialize (IHHproto msg).
      apply preloaded_weaken_protocol_transition in Ht.
      apply (oracle_step_update has_been_observed_stepwise_props _ _ _ _ _ Ht) in Hobs.
      specialize (Henforced l s (Some msg)).
      rewrite (oracle_step_update (has_been_sent_stepwise_from_trace Hhbs) _ _ _ _ _ Ht).
      destruct Ht as [[_ [_  Hv]] _].
      simpl in Hobs |- *.
      destruct Hobs as [[|]|].
      + (* by [no_equivocations], the incoming message [im] was previously sent *)
        rewrite H in Hv.
        specialize (Henforced Hv).
        destruct Henforced as [Hbs | Hinitial]; [|contradiction].
        right. assumption.
      + left. assumption.
      + specialize (IHHproto H).
        right. assumption.
  Qed.

  Lemma no_equivocations_preloaded_traces
    (is : state)
    (tr : list transition_item)
    : finite_protocol_trace (pre_loaded_with_all_messages_vlsm X) is tr -> finite_protocol_trace X is tr.
  Proof.
    intro Htr.
    induction Htr using finite_protocol_trace_rev_ind.
    - split;[|assumption].
      rapply @finite_ptrace_empty.
      apply initial_is_protocol.
      assumption.
    - destruct IHHtr as [IHtr His].
      split; [|assumption].
      rapply extend_right_finite_trace_from;[assumption|].
      apply protocol_transition_origin in Hx as Hlst'.
      destruct Hx as [Hvalid Htrans].
      split;[|exact Htrans].
      apply finite_ptrace_last_pstate in IHtr as Hstate.
      split;[assumption|]. clear Hstate.
      split;[|apply Hvalid].
      destruct Hvalid as [_ [_ Hv]].
      apply Henforced in Hv.
      destruct iom as [m|]; [|apply option_protocol_message_None].
      apply option_protocol_message_Some.
      destruct Hv as [Hbsm | Him]
      ; [|contradiction].
      apply proper_sent in Hbsm; [|assumption].
      specialize (Hbsm _ tr (ptrace_add_default_last Htr)).
      apply can_emit_protocol.
      apply (can_emit_from_protocol_trace X _ _ _ (conj IHtr His) Hbsm).
  Qed.

  Lemma preloaded_incl_no_equivocations
    : VLSM_incl (pre_loaded_with_all_messages_vlsm X) X.
  Proof.
    specialize no_equivocations_preloaded_traces.
    clear -X. destruct X as [T [S M]].
    apply VLSM_incl_finite_traces_characterization.
  Qed.

  Lemma preloaded_eq_no_equivocations
    : VLSM_eq (pre_loaded_with_all_messages_vlsm X) X.
  Proof.
    specialize preloaded_incl_no_equivocations.
    specialize (vlsm_incl_pre_loaded_with_all_messages_vlsm X).
    clear -X. destruct X as [T [S M]].
    intros Hincl Hincl'.
    apply VLSM_eq_incl_iff. split; assumption.
  Qed.

End NoEquivocationInvariants.

Section CompositeNoEquivocation.

Context
  {message : Type}
  `{IndEqDec : EqDecision index}
  (IM : index -> VLSM message)
  {i0 : Inhabited index}
  (Hbs : forall i, has_been_sent_capability (IM i))
  .

Definition composite_no_equivocations_except_from
  (exception : message -> Prop)
  (l : composite_label IM)
  (som : composite_state IM * option message)
  :=
  let (s, om) := som in
  match om with
  | None => True
  | Some m => composite_has_been_sent IM Hbs s m \/ exception m
  end.

(** The [composite_no_equivocations] constraint requires that
messages being received must have been previously sent by a
machine in the composition.
*)
Definition composite_no_equivocations
  (l : composite_label IM)
  (som : composite_state IM * option message)
  : Prop
  :=
  composite_no_equivocations_except_from (fun m => False) l som.


(**
*** Composite No-Equivocation Invariants

A VLSM composition whose constraint substumes the [no_equivocations] constraint
and also supports [has_been_recevied] (or [has_been_observed]) obeys an
invariant that any message that tests as [has_been_received]
(resp. [has_been_observed]) in a state also tests as [has_been_sent]
in the same state.
 *)
Section CompositeNoEquivocationInvariants.
  Context
    (Hbo : forall i, has_been_observed_capability (IM i))
    {index_listing : list index}
    (finite_index : Listing index_listing)
    (Free := free_composite_vlsm IM)
    (Free_hbo : has_been_observed_capability Free := free_composite_has_been_observed_capability IM finite_index Hbo)
    (constraint : composite_label IM -> composite_state IM * option message -> Prop)
    (X := composite_vlsm IM constraint)
    (Hsubsumed: constraint_subsumption IM constraint composite_no_equivocations)
    .

Existing Instance Free_hbo.

  Definition composite_observed_were_sent (s: state) : Prop :=
    forall msg, composite_has_been_observed IM Hbo s msg -> composite_has_been_sent IM Hbs s msg.

  Lemma composite_observed_were_sent_initial s:
    composite_initial_state_prop IM s ->
    composite_observed_were_sent s.
  Proof.
    intros Hinitial msg Hsend.
    elim (oracle_no_inits (vlsm := Free) has_been_observed_stepwise_props s Hinitial msg).
    assumption.
  Qed.

  Lemma composite_observed_were_sent_preserved l s im s' om:
    protocol_transition X l (s,im) (s',om) ->
    composite_observed_were_sent s ->
    composite_observed_were_sent s'.
  Proof.
    intros Hptrans Hprev msg Hobs.
    specialize (Hprev msg).
    assert (Hpre_trans : protocol_transition (pre_loaded_with_all_messages_vlsm Free) l (s, im) (s', om)).
    { revert Hptrans.
      apply VLSM_incl_protocol_transition.
      apply VLSM_incl_trans with (composite_vlsm_machine IM (free_constraint IM)).
      - apply constraint_free_incl.
      - apply vlsm_incl_pre_loaded_with_all_messages_vlsm.
    }
    specialize (oracle_step_update has_been_observed_stepwise_props _ _ _ _ _ Hpre_trans msg) as Hstep.
    apply Hstep in Hobs.
    simpl in Hobs.
    specialize (oracle_step_update (has_been_sent_stepwise_from_trace (free_composite_has_been_sent_capability IM finite_index Hbs)) _ _ _ _ _ Hpre_trans msg) as Hrew.
    rewrite Hrew.
    destruct Hptrans as [[_ [_ [_ Hctr]]] _].
    apply Hsubsumed in Hctr.
    destruct Hobs as [[|]|].
    - (* by [no_equivocations], the incoming message [im] was previously sent *)
      rewrite H in Hctr.
      destruct Hctr; [|contradiction].
      right. assumption.
    - left. assumption.
    - specialize (Hprev H).
      right. assumption.
  Qed.

  Lemma composite_observed_were_sent_invariant s:
    protocol_state_prop X s ->
    composite_observed_were_sent s.
  Proof.
    intro Hproto.
    induction Hproto using protocol_state_prop_ind.
    - intros msg Hsend.
      elim (oracle_no_inits (vlsm := Free) has_been_observed_stepwise_props s Hs msg).
      assumption.
    - apply (composite_observed_were_sent_preserved _ _ _ _ _ Ht). assumption.
  Qed.

End CompositeNoEquivocationInvariants.

Section seeded_composite_vlsm_no_equivocation.

(** ** Pre-loading a VLSM composition with no equivocations constraint

When adding initial messages to a VLSM composition with a no equivocation
constraint, we cannot simply use the [pre_loaded_vlsm] construct
because the no-equivocation constraint must also be altered to reflect that
the newly added initial messages are safe to be received at all times.
*)

  Context
    (X := free_composite_vlsm IM)
    {index_listing : list index}
    (finite_index : Listing index_listing)
    (X_has_been_sent_capability : has_been_sent_capability X := free_composite_has_been_sent_capability IM finite_index Hbs)
    (constraint : composite_label IM -> composite_state IM * option message -> Prop)
    .

Section seeded_composite_vlsm_no_equivocation_definition.

  Context
    (seed : message -> Prop)
    .

  (** Constraint is updated to also allow seeded messages. *)

  Definition no_equivocations_additional_constraint_with_pre_loaded
    (l : composite_label IM)
    (som : composite_state IM * option message)
    :=
    composite_no_equivocations_except_from seed l som
    /\ constraint l som.

  Definition composite_no_equivocation_vlsm_with_pre_loaded
    : VLSM message
    :=
    pre_loaded_vlsm (composite_vlsm IM no_equivocations_additional_constraint_with_pre_loaded) seed.

  Lemma seeded_no_equivocation_incl_preloaded
    : VLSM_incl composite_no_equivocation_vlsm_with_pre_loaded (pre_loaded_with_all_messages_vlsm (free_composite_vlsm IM)).
  Proof.
    unfold composite_no_equivocation_vlsm_with_pre_loaded.
    match goal with
    |- VLSM_incl (pre_loaded_vlsm ?v _) _ =>
      specialize (pre_loaded_with_all_messages_vlsm_is_pre_loaded_with_True v) as Hprev
    end.
    apply VLSM_eq_incl_iff in Hprev. apply proj2 in Hprev.
    match type of Hprev with
    | VLSM_incl (mk_vlsm ?m) _ => apply VLSM_incl_trans with m
    end
    ; [apply pre_loaded_vlsm_incl; intros; exact I|].
    match type of Hprev with
    | VLSM_incl _ (mk_vlsm ?m) => apply VLSM_incl_trans with m
    end
    ; [assumption| ].
    unfold free_composite_vlsm.
    simpl.
    apply preloaded_constraint_subsumption_pre_loaded_with_all_messages_incl.
    intro. intros. exact I.
  Qed.

End seeded_composite_vlsm_no_equivocation_definition.

  (** Adds a no-equivocations condition on top of an existing constraint. *)
  Definition no_equivocations_additional_constraint
    (l : composite_label IM)
    (som : composite_state IM * option message)
    :=
    composite_no_equivocations l som
    /\ constraint l som.

  Context
    (SeededNoeqvFalse := composite_no_equivocation_vlsm_with_pre_loaded (fun m => False))
    (Noeqv := composite_vlsm IM no_equivocations_additional_constraint)
    (SeededNoeqvTrue := composite_no_equivocation_vlsm_with_pre_loaded (fun m => True))
    (PreFree := pre_loaded_with_all_messages_vlsm (free_composite_vlsm IM))
    .

  Lemma false_composite_no_equivocation_vlsm_with_pre_loaded
    : VLSM_eq SeededNoeqvFalse Noeqv.
  Proof.
    unfold SeededNoeqvFalse.
    unfold composite_no_equivocation_vlsm_with_pre_loaded.
    match goal with
    |- VLSM_eq (pre_loaded_vlsm ?m _) _ => specialize (vlsm_is_pre_loaded_with_False m) as Heq
    end.
    apply VLSM_eq_sym in Heq.
    match type of Heq with
    | VLSM_eq _ ?v => apply VLSM_eq_trans with (machine v)
    end
    ; [assumption|].
    apply VLSM_eq_incl_iff.
    specialize (constraint_subsumption_incl IM) as Hincl.
    split.
    - specialize
        (Hincl
          (no_equivocations_additional_constraint_with_pre_loaded (fun _ : message => False))
          no_equivocations_additional_constraint
        ).
      apply Hincl.
      intros l som. unfold no_equivocations_additional_constraint_with_pre_loaded.
      clear -l.
      destruct som as (s, [m|]); [|exact id].
      intros [[H|contra] Hc]; [|contradiction].
      split; [left|]; assumption.
    - specialize
        (Hincl
          no_equivocations_additional_constraint
          (no_equivocations_additional_constraint_with_pre_loaded (fun _ : message => False))
        ).
      apply Hincl.
      intros l som. unfold no_equivocations_additional_constraint_with_pre_loaded.
      clear -l.
      destruct som as (s, [m|]); [|exact id].
      intros [H Hc].
      split; [|assumption].
      assumption.
  Qed.

End seeded_composite_vlsm_no_equivocation.
End CompositeNoEquivocation.
