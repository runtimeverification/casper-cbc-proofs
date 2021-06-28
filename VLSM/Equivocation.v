From Coq Require Import List ListSet Streams ProofIrrelevance Arith.Plus Arith.Minus FinFun Rdefinitions.
Import ListNotations.

From CasperCBC Require Import Lib.Preamble Lib.ListExtras Lib.Measurable VLSM.Decisions VLSM.Common VLSM.Composition VLSM.ProjectionTraces.

Require Import Coq.Program.Tactics.

(** * VLSM Equivocation Definitions **)

(**
 This module is dedicated to building the language for discussing equivocation.
 Equivocation occurs on the receipt of a message which has not been previously sent.
 The designated sender (validator) of the message is then said to be equivocating.
 Our main purpose is to keep track of equivocating senders in a composite context
 and limit equivocation by means of a composition constraint.
**)

Lemma exists_proj1_sig {A:Type} (P:A -> Prop) (a:A):
  (exists xP:{x | P x}, proj1_sig xP = a) <-> P a.
Proof.
  split.
  - intros [[x Hx] Heq];simpl in Heq;subst x.
    assumption.
  - intro Ha.
    exists (exist _ a Ha).
    reflexivity.
Qed.

(** ** Basic equivocation **)

Class ReachableThreshold V `{Hm : Measurable V} :=
  { threshold : {r | (r >= 0)%R}
  ; reachable_threshold : exists (vs:list V), NoDup vs /\ (sum_weights vs > proj1_sig threshold)%R
  }.

(** Assuming a set of <<state>>s, and a set of <<validator>>s,
which is [Measurable] and has a [ReachableThreshold], we can define
[basic_equivocation] starting from a computable [is_equivocating_fn]
deciding whether a validator is equivocating in a state.

To avoid a [Finite] constraint on the entire set of validators, we will
assume that there is a finite set of validators for each state, which
can be retrieved through the [state_validators] function.
This can be taken to be entire set of validators when that is finite,
or the set of senders for all messages in the state for
[state_encapsulating_messages].

This allows us to determine the [equivocating_validators] for a given
state as those equivocating in that state.

The [equivocation_fault] is determined the as the sum of weights of the
[equivocating_validators].

We call a state [not_heavy] if its corresponding [equivocation_fault]
is lower than the [threshold] set for the <<validator>>s type.
**)

Class basic_equivocation
  (state validator : Type)
  {measurable_V : Measurable validator}
  {reachable_threshold : ReachableThreshold validator}
  :=
  { is_equivocating (s : state) (v : validator) : Prop
  ; is_equivocating_dec : RelDecision is_equivocating

    (** retrieves a set containing all possible validators for a state. **)

  ; state_validators (s : state) : set validator

  ; state_validators_nodup : forall (s : state), NoDup (state_validators s)

    (** All validators which are equivocating in a given composite state **)

  ; equivocating_validators
      (s : state)
      : list validator
      := List.filter (fun v => bool_decide (is_equivocating s v)) (state_validators s)

     (** The equivocation fault sum: the sum of the weights of equivocating
     validators **)

  ; equivocation_fault
      (s : state)
      : R
      :=
      sum_weights (equivocating_validators s)

  ; not_heavy
      (s : state)
      := (equivocation_fault s <= proj1_sig threshold)%R
 }.


(**
*** State-message oracles. Endowing states with history.

    Our first step is to define some useful concepts in the context of a single VLSM.

    Apart from basic definitions of equivocation, we introduce the concept of a
    [state_message_oracle]. Such an oracle can, given a state and a message,
    decide whether the message has been sent (or received) in the history leading
    to the current state. Formally, we say that a [message] <m> [has_been_sent]
    if we're in  [state] <s> iff every protocol trace which produces <s> contains <m>
    as a sent message somewhere along the way.

    The existence of such oracles, which practically imply endowing states with history,
    is necessary if we are to detect equivocation using a composition constaint, as these
    constraints act upon states, not traces.
 **)

Section Simple.
    Context
      {message : Type}
      (vlsm : VLSM message)
      (pre_vlsm := pre_loaded_with_all_messages_vlsm vlsm)
      .

(** The following property detects equivocation in a given trace for a given message. **)

    Definition equivocation_in_trace
      (msg : message)
      (tr : list (vtransition_item vlsm))
      : Prop
      :=
      exists
        (prefix suffix : list transition_item)
        (item : transition_item),
        tr = prefix ++ item :: suffix
        /\ input item = Some msg
        /\ ~ In (Some msg) (List.map output prefix).

(** We intend to give define several message oracles: [has_been_sent], [has_not_been_sent],
    [has_been_received] and [has_not_been_received]. To avoid repetition, we give
    build some generic definitions first. **)

(** General signature of a message oracle **)

    Definition state_message_oracle
      := vstate vlsm -> message -> Prop.

    Definition specialized_selected_message_exists_in_all_traces
      (X : VLSM message)
      (message_selector : message -> transition_item -> Prop)
      (s : state)
      (m : message)
      : Prop
      :=
      forall
      (start : state)
      (tr : list transition_item)
      (Htr : finite_protocol_trace_init_to X start s tr),
      trace_has_message message_selector m tr.

    Definition selected_message_exists_in_all_preloaded_traces
      := specialized_selected_message_exists_in_all_traces pre_vlsm.

    Definition specialized_selected_message_exists_in_some_traces
      (X : VLSM message)
      (message_selector : message -> transition_item -> Prop)
      (s : state)
      (m : message)
      : Prop
      :=
      exists
      (start : state)
      (tr : list transition_item)
      (Htr : finite_protocol_trace_init_to X start s tr),
      trace_has_message message_selector m tr.

    Definition selected_message_exists_in_some_preloaded_traces: forall
      (message_selector : message -> transition_item -> Prop)
      (s : state)
      (m : message),
        Prop
      := specialized_selected_message_exists_in_some_traces pre_vlsm.

    Definition specialized_selected_message_exists_in_no_trace
      (X : VLSM message)
      (message_selector : message -> transition_item -> Prop)
      (s : state)
      (m : message)
      : Prop
      :=
      forall
      (start : state)
      (tr : list transition_item)
      (Htr : finite_protocol_trace_init_to X start s tr),
      ~trace_has_message message_selector m tr.

    Definition selected_message_exists_in_no_preloaded_trace :=
      specialized_selected_message_exists_in_no_trace pre_vlsm.

    Lemma selected_message_exists_not_some_iff_no
      (X : VLSM message)
      (message_selector : message -> transition_item -> Prop)
      (s : state)
      (m : message)
      : ~ specialized_selected_message_exists_in_some_traces X message_selector s m
        <-> specialized_selected_message_exists_in_no_trace X message_selector s m.
    Proof.
      split.
      - intro Hnot.
        intros is tr Htr Hsend.
        apply Hnot.
        exists is, tr, Htr. exact Hsend.
      - intros Hno [is [tr [Htr Hsend]]].
        exact (Hno is tr Htr Hsend).
    Qed.

    Lemma selected_message_exists_preloaded_not_some_iff_no
      (message_selector : message -> transition_item -> Prop)
      (s : state)
      (m : message)
      : ~ selected_message_exists_in_some_preloaded_traces message_selector s m
        <-> selected_message_exists_in_no_preloaded_trace message_selector s m.
    Proof.
      apply selected_message_exists_not_some_iff_no.
    Qed.

    (** Sufficient condition for 'specialized_selected_message_exists_in_some_traces'
    *)
    Lemma specialized_selected_message_exists_in_some_traces_from
      (X : VLSM message)
      (message_selector : message -> transition_item -> Prop)
      (s : state)
      (m : message)
      (start : state)
      (tr : list transition_item)
      (Htr : finite_protocol_trace_from_to X start s tr)
      (Hsome : trace_has_message message_selector m tr)
      : specialized_selected_message_exists_in_some_traces X message_selector s m.
    Proof.
      assert (protocol_state_prop X start) as Hstart
        by (apply ptrace_first_pstate in Htr; assumption).
      apply protocol_state_has_trace in Hstart.
      destruct Hstart as [is [tr' Htr']].
      assert (finite_protocol_trace_init_to X is s (tr'++tr)).
      {
        destruct Htr'.
        split;
        [apply finite_protocol_trace_from_to_app with start|];
        assumption.
      }
      exists _, _, H.
      apply Exists_app.
      right;assumption.
    Qed.

    Definition selected_messages_consistency_prop
      (message_selector : message -> transition_item -> Prop)
      (s : vstate vlsm)
      (m : message)
      : Prop
      :=
      selected_message_exists_in_some_preloaded_traces message_selector s m
      <-> selected_message_exists_in_all_preloaded_traces message_selector s m.

    Lemma selected_message_exists_in_all_traces_initial_state
      (s : vstate vlsm)
      (Hs : vinitial_state_prop vlsm s)
      (message_selector : message -> transition_item -> Prop)
      (m : message)
      : ~ selected_message_exists_in_all_preloaded_traces message_selector s m.
    Proof.
      intro Hselected.
      assert (Hps : protocol_state_prop pre_vlsm s)
        by (apply initial_is_protocol;assumption).
      assert (Htr : finite_protocol_trace_init_to pre_vlsm s s []).
      { split; try assumption. constructor. assumption. }
      specialize (Hselected s [] Htr).
      unfold trace_has_message in Hselected.
      rewrite Exists_nil in Hselected.
      assumption.
      Qed.

(** Checks if all [protocol_trace]s leading to a certain state contain a certain message.
    The [message_selector] argument specifices whether we're looking for received or sent
    messages.

    Notably, the [protocol_trace]s over which we are iterating belong to the preloaded
    version of the target VLSM. This is because we want VLSMs to have oracles which
    are valid irrespective of the composition they take part in. As we know,
    the behaviour preloaded VLSMs includes behaviours of its projections in any
    composition. **)

    Definition all_traces_have_message_prop
      (message_selector : message -> transition_item -> Prop)
      (oracle : state_message_oracle)
      (s : state)
      (m : message)
      : Prop
      :=
      oracle s m <-> selected_message_exists_in_all_preloaded_traces message_selector s m.

    Definition no_traces_have_message_prop
      (message_selector : message -> transition_item -> Prop)
      (oracle : state_message_oracle)
      (s : state)
      (m : message)
      : Prop
      :=
      oracle s m <-> selected_message_exists_in_no_preloaded_trace message_selector s m.

    Definition has_been_sent_prop : state_message_oracle -> state -> message -> Prop
      := (all_traces_have_message_prop (field_selector output)).

    Definition has_not_been_sent_prop : state_message_oracle -> state -> message -> Prop
      := (no_traces_have_message_prop (field_selector output)).

    Definition has_been_received_prop : state_message_oracle -> state -> message -> Prop
      := (all_traces_have_message_prop (field_selector input)).

    Definition has_not_been_received_prop : state_message_oracle -> state -> message -> Prop
      := (no_traces_have_message_prop (field_selector input)).

(** Per the vocabulary of the official VLSM document, we say that VLSMs endowed
    with a [state_message_oracle] for sent messages have the [has_been_sent] capability.
    Capabilities for receiving messages are treated analogously, so we omit mentioning
    them explicitly.

    Notably, we also define the [has_not_been_sent] oracle, which decides if a message
    has definitely not been sent, on any of the traces producing a current state.

    Furthermore, we require a [sent_excluded_middle] property, which stipulates
    that any argument to the oracle should return true in exactly one of
    [has_been_sent] and [has_not_been_sent]. **)

    Class has_been_sent_capability := {
      has_been_sent: state_message_oracle;
      has_been_sent_dec :> RelDecision has_been_sent;

      proper_sent:
        forall (s : state)
               (Hs : protocol_state_prop pre_vlsm s)
               (m : message),
               (has_been_sent_prop has_been_sent s m);

      has_not_been_sent: state_message_oracle
        := fun (s : state) (m : message) => ~ has_been_sent s m;

      proper_not_sent:
        forall (s : state)
               (Hs : protocol_state_prop pre_vlsm s)
               (m : message),
               has_not_been_sent_prop has_not_been_sent s m;
    }.

    (** Reverse implication for 'selected_messages_consistency_prop'
    always holds. *)
    Lemma consistency_from_protocol_proj2
      (s : state)
      (Hs: protocol_state_prop pre_vlsm s)
      (m : message)
      (selector : message -> transition_item -> Prop)
      (Hall : selected_message_exists_in_all_preloaded_traces selector s m)
      : selected_message_exists_in_some_preloaded_traces selector s m.
    Proof.
      apply protocol_state_has_trace in Hs.
      destruct Hs as [is [tr Htr]].
      exists _, _, Htr.
      apply (Hall _ _ Htr).
    Qed.

    Lemma has_been_sent_consistency
      {Hbs : has_been_sent_capability}
      (s : state)
      (Hs : protocol_state_prop pre_vlsm s)
      (m : message)
      : selected_messages_consistency_prop (field_selector output) s m.
    Proof.
      split.
      - intro Hsome.
        destruct (decide (has_been_sent s m)) as [Hsm|Hsm].
        apply proper_sent in Hsm;assumption.
        apply proper_not_sent in Hsm;[|assumption].
        exfalso.
        destruct Hsome as [is [tr [Htr Hmsg]]].
        elim (Hsm _ _ Htr).
        assumption.
      - apply consistency_from_protocol_proj2.
        assumption.
    Qed.

    (** Sufficent condition for 'proper_sent' avoiding the
    'pre_loaded_with_all_messages_vlsm'
    *)
    Lemma specialized_proper_sent
      {Hbs : has_been_sent_capability}
      (s : state)
      (Hs : protocol_state_prop vlsm s)
      (m : message)
      (Hsome : specialized_selected_message_exists_in_some_traces vlsm (field_selector output) s m)
      : has_been_sent s m.
    Proof.
      destruct Hs as [_om Hs].
      assert (Hpres : protocol_state_prop pre_vlsm s).
      { exists _om. apply (pre_loaded_with_all_messages_protocol_prop vlsm). assumption. }
      apply proper_sent; [assumption|].
      specialize (has_been_sent_consistency s Hpres m) as Hcons.
      apply Hcons.
      destruct Hsome as [is [tr [Htr Hsome]]].
      exists is, tr.
      split; [|assumption].
      revert Htr.
      unfold pre_vlsm;clear.
      destruct vlsm as (T,(S,M)).
      apply VLSM_incl_finite_protocol_trace_init_to.
      apply vlsm_incl_pre_loaded_with_all_messages_vlsm.
    Qed.

    (** 'proper_sent' condition specialized to regular vlsm traces
    (avoiding 'pre_loaded_with_all_messages_vlsm')
    *)
    Lemma specialized_proper_sent_rev
      {Hbs : has_been_sent_capability}
      (s : state)
      (Hs : protocol_state_prop vlsm s)
      (m : message)
      (Hsm : has_been_sent s m)
      : specialized_selected_message_exists_in_all_traces vlsm (field_selector output) s m.
    Proof.
      destruct Hs as [_om Hs].
      assert (Hpres : protocol_state_prop pre_vlsm s).
      { exists _om. apply (pre_loaded_with_all_messages_protocol_prop vlsm). assumption. }
      apply proper_sent in Hsm; [|assumption].
      intros is tr Htr.
      specialize (Hsm is tr).
      spec Hsm;[|assumption].
      revert Htr.
      unfold pre_vlsm;clear.
      destruct vlsm as (T,(S,M)).
      apply VLSM_incl_finite_protocol_trace_init_to.
      apply vlsm_incl_pre_loaded_with_all_messages_vlsm.
    Qed.

    Lemma has_been_sent_consistency_proper_not_sent
      (has_been_sent: state_message_oracle)
      (has_been_sent_dec: RelDecision has_been_sent)
      (s : state)
      (m : message)
      (proper_sent: has_been_sent_prop has_been_sent s m)
      (has_not_been_sent
        := fun (s : state) (m : message) => ~ has_been_sent s m)
      (Hconsistency : selected_messages_consistency_prop (field_selector output) s m)
      : has_not_been_sent_prop has_not_been_sent s m.
    Proof.
      unfold has_not_been_sent_prop.
      unfold no_traces_have_message_prop.
      unfold has_not_been_sent.
      rewrite <- selected_message_exists_preloaded_not_some_iff_no.
      apply not_iff_compat.
      apply (iff_trans proper_sent).
      symmetry;exact Hconsistency.
    Qed.

  (** It is now straightforward to define a [no_equivocations] composition constraint.
      An equivocating transition can be detected by calling the [has_been_sent]
      oracle on its arguments and we simply forbid them.

      However, since we might allow certain other messages, such as initial
      messages, we give a slightly more general definition, that of
      [no_equivocation_except_from] those specified by a given predicate.
  **)

    Definition no_equivocations_except_from
      {Hbs : has_been_sent_capability}
      (exception : message -> Prop)
      (l : vlabel vlsm)
      (som : state * option message)
      :=
      let (s, om) := som in
      match om with
      | None => True
      | Some m => has_been_sent s m \/ exception m
      end.

    (** The [no_equivocations] constraint only allows initial messages
    as exceptions (messages being received without being previously sent).
    *)
    Definition no_equivocations
      {Hbs : has_been_sent_capability}
      (l : vlabel vlsm)
      (som : state * option message)
      : Prop
      :=
      no_equivocations_except_from (vinitial_message_prop vlsm) l som.


    Class has_been_received_capability := {
      has_been_received: state_message_oracle;
      has_been_received_dec :> RelDecision has_been_received;

      proper_received:
        forall (s : state)
               (Hs : protocol_state_prop pre_vlsm s)
               (m : message),
               (has_been_received_prop has_been_received s m);

      has_not_been_received: state_message_oracle
        := fun (s : state) (m : message) => ~ has_been_received s m;

      proper_not_received:
        forall (s : state)
               (Hs : protocol_state_prop pre_vlsm s)
               (m : message),
               has_not_been_received_prop has_not_been_received s m;
    }.

    Lemma has_been_received_consistency
      {Hbs : has_been_received_capability}
      (s : state)
      (Hs : protocol_state_prop pre_vlsm s)
      (m : message)
      : selected_messages_consistency_prop (field_selector input) s m.
    Proof.
      split.
      - intro Hsome.
        destruct (decide (has_been_received s m)) as [Hsm|Hsm];
          [apply proper_received in Hsm;assumption|].
        apply proper_not_received in Hsm;[|assumption].
        destruct Hsome as [is [tr [Htr Hsome]]].
        elim (Hsm _ _ Htr).
        assumption.
      - apply consistency_from_protocol_proj2.
        assumption.
    Qed.

    Lemma has_been_received_consistency_proper_not_received
      (has_been_received: state_message_oracle)
      (has_been_received_dec: RelDecision has_been_received)
      (s : state)
      (m : message)
      (proper_received: has_been_received_prop has_been_received s m)
      (has_not_been_received
        := fun (s : state) (m : message) => ~ has_been_received s m)
      (Hconsistency : selected_messages_consistency_prop (field_selector input) s m)
      : has_not_been_received_prop has_not_been_received s m.
    Proof.
      unfold has_not_been_received_prop.
      unfold no_traces_have_message_prop.
      unfold has_not_been_received.
      split.
      - intros Hsm is tr Htr Hsome.
        assert (Hsm' : selected_message_exists_in_some_preloaded_traces (field_selector input) s m)
          by (exists is; exists tr; exists Htr; assumption).
        apply Hconsistency in Hsm'.
        apply proper_received in Hsm'. contradiction.
      - intro Hnone. destruct (decide (has_been_received s m)) as [Hsm|Hsm];[|assumption].
        exfalso.
        apply proper_received in Hsm. apply Hconsistency in Hsm.
        destruct Hsm as [is [tr [Htr Hsm]]].
        elim (Hnone is tr Htr). assumption.
    Qed.

    Definition sent_messages
      (s : vstate vlsm)
      : Type
      :=
      sig (fun m => selected_message_exists_in_some_preloaded_traces (field_selector output) s m).

    Lemma sent_messages_proper
      (Hhbs : has_been_sent_capability)
      (s : vstate vlsm)
      (Hs : protocol_state_prop pre_vlsm s)
      (m : message)
      : has_been_sent s m <-> exists (m' : sent_messages s), proj1_sig m' = m.
    Proof.
      unfold sent_messages. rewrite exists_proj1_sig.
      specialize (proper_sent s Hs m) as Hbs.
      unfold has_been_sent_prop,all_traces_have_message_prop in Hbs.
      rewrite Hbs.
      symmetry.
      exact (has_been_sent_consistency s Hs m).
    Qed.

    Definition received_messages
      (s : vstate vlsm)
      : Type
      :=
      sig (fun m => selected_message_exists_in_some_preloaded_traces (field_selector input) s m).

    Lemma received_messages_proper
      (Hhbs : has_been_received_capability)
      (s : vstate vlsm)
      (Hs : protocol_state_prop pre_vlsm s)
      (m : message)
      : has_been_received s m <-> exists (m' : received_messages s), proj1_sig m' = m.
    Proof.
      unfold received_messages. rewrite exists_proj1_sig.
      specialize (proper_received s Hs m) as Hbs.
      unfold has_been_received_prop,all_traces_have_message_prop in Hbs.
      rewrite Hbs.
      symmetry.
      exact (has_been_received_consistency s Hs m).
    Qed.

    Class computable_sent_messages := {
      sent_messages_fn : vstate vlsm -> list message;

      sent_messages_full :
        forall (s : vstate vlsm) (Hs : protocol_state_prop pre_vlsm s) (m : message),
          In m (sent_messages_fn s) <-> exists (sm : sent_messages s), proj1_sig sm = m;

      sent_messages_consistency :
        forall
          (s : vstate vlsm)
          (Hs : protocol_state_prop pre_vlsm s)
          (m : message),
          selected_messages_consistency_prop (field_selector output) s m
    }.

    Lemma computable_sent_messages_initial_state_empty
      {Hrm : computable_sent_messages}
      (s : vinitial_state vlsm)
      : sent_messages_fn (proj1_sig s) = [].
    Proof.
      assert (Hps : protocol_state_prop pre_vlsm (proj1_sig s))
        by (apply initial_is_protocol; apply proj2_sig).
      destruct s as [s Hs]. simpl in *.
      destruct (sent_messages_fn s) as [|m l] eqn:Hsm; try reflexivity.
      specialize (sent_messages_full s Hps m) as Hl. apply proj1 in Hl.
      spec Hl; try (rewrite Hsm; left; reflexivity).
      destruct Hl as [[m0 Hm] Heq]. simpl in Heq. subst m0.
      apply sent_messages_consistency in Hm; try assumption.
      exfalso. revert Hm.
      apply selected_message_exists_in_all_traces_initial_state.
      assumption.
    Qed.

    Definition computable_sent_messages_has_been_sent
      {Hsm : computable_sent_messages}
      (s : vstate vlsm)
      (m : message)
      : Prop
      :=
      In m (sent_messages_fn s).

    Global Instance computable_sent_message_has_been_sent_dec
      {Hsm : computable_sent_messages}
      {eq_message: EqDecision message}
      : RelDecision computable_sent_messages_has_been_sent
      :=
        fun s m => in_dec decide_eq m (sent_messages_fn s).

    Lemma computable_sent_messages_has_been_sent_proper
      {Hsm : computable_sent_messages}
      (s : state)
      (Hs : protocol_state_prop pre_vlsm s)
      (m : message)
      : has_been_sent_prop computable_sent_messages_has_been_sent s m.
    Proof.
      unfold has_been_sent_prop. unfold all_traces_have_message_prop.
      unfold computable_sent_messages_has_been_sent.
      split.
      - intro Hin.
        apply sent_messages_full in Hin;[|assumption].
        destruct Hin as [[m0 Hm0] Hx].
        simpl in Hx. subst m0. apply (sent_messages_consistency s Hs m).
        assumption.
      - intro H.
        apply (sent_messages_consistency s Hs m) in H.
        apply sent_messages_full; try assumption.
        exists (exist _ m H). reflexivity.
    Qed.

    Definition computable_sent_messages_has_not_been_sent
      {Hsm : computable_sent_messages}
      (s : vstate vlsm)
      (m : message)
      : Prop
      :=
      ~ computable_sent_messages_has_been_sent s m.

    Lemma computable_sent_messages_has_not_been_sent_proper
      {Hsm : computable_sent_messages}
      (s : state)
      (Hs : protocol_state_prop pre_vlsm s)
      (m : message)
      : has_not_been_sent_prop computable_sent_messages_has_not_been_sent s m.
    Proof.
      unfold has_not_been_sent_prop. unfold no_traces_have_message_prop.
      unfold computable_sent_messages_has_not_been_sent.
      unfold computable_sent_messages_has_been_sent.
      split.
      - intro Hin.
        cut (~ selected_message_exists_in_some_preloaded_traces (field_selector output) s m).
        { intros Hno is tr Htr Hexists.
          contradict Hno;exists is, tr, Htr;assumption.
        }
        contradict Hin.
        apply sent_messages_full;[assumption|].
        exists (exist _ m Hin).
        reflexivity.
      - intros Htrace Hin.
        apply sent_messages_full in Hin;[|assumption].
        destruct Hin as [[m0 Hm] Heq];simpl in Heq;subst m0.
        destruct Hm as [is [tr [Htr Hex]]].
        apply (Htrace is tr Htr Hex).
    Qed.

    Definition computable_sent_messages_has_been_sent_capability
      {Hsm : computable_sent_messages}
      {eq_message : EqDecision message}
      : has_been_sent_capability
      :=
      {|
        has_been_sent := computable_sent_messages_has_been_sent;
        proper_sent := computable_sent_messages_has_been_sent_proper;
        proper_not_sent := computable_sent_messages_has_not_been_sent_proper
      |}.

    Class computable_received_messages := {
      received_messages_fn : vstate vlsm -> list message;

      received_messages_full :
        forall (s : vstate vlsm) (Hs : protocol_state_prop pre_vlsm s) (m : message),
          In m (received_messages_fn s) <-> exists (sm : received_messages s), proj1_sig sm = m;

      received_messages_consistency :
        forall
          (s : vstate vlsm)
          (Hs : protocol_state_prop pre_vlsm s)
          (m : message),
          selected_messages_consistency_prop (field_selector input) s m
    }.

    Lemma computable_received_messages_initial_state_empty
      {Hrm : computable_received_messages}
      (s : vinitial_state vlsm)
      : received_messages_fn (proj1_sig s) = [].
    Proof.
      assert (Hps : protocol_state_prop pre_vlsm (proj1_sig s))
        by (apply initial_is_protocol;apply proj2_sig).
      destruct s as [s Hs]. simpl in *.
      destruct (received_messages_fn s) as [|m l] eqn:Hrcv; try reflexivity.
      specialize (received_messages_full s Hps m) as Hl. apply proj1 in Hl.
      spec Hl; try (rewrite Hrcv; left; reflexivity).
      destruct Hl as [[m0 Hm] Heq]. simpl in Heq. subst m0.
      apply received_messages_consistency in Hm; try assumption.
      exfalso. revert Hm.
      apply selected_message_exists_in_all_traces_initial_state.
      assumption.
    Qed.

    Definition computable_received_messages_has_been_received
      {Hsm : computable_received_messages}
      (s : vstate vlsm)
      (m : message)
      : Prop
      :=
      In m (received_messages_fn s).

    Global Instance computable_received_messages_has_been_received_dec
      {Hsm : computable_received_messages}
      {eq_message : EqDecision message}
      : RelDecision computable_received_messages_has_been_received
      :=
      fun s m => in_dec decide_eq m (received_messages_fn s).

    Lemma computable_received_messages_has_been_received_proper
      {Hsm : computable_received_messages}
      (s : state)
      (Hs : protocol_state_prop pre_vlsm s)
      (m : message)
      : has_been_received_prop computable_received_messages_has_been_received s m.
    Proof.
      unfold has_been_received_prop. unfold all_traces_have_message_prop.
      unfold computable_received_messages_has_been_received.
      split.
      - intro Hin.
        apply received_messages_full in Hin;[|assumption].
        destruct Hin as [[m0 Hm] Heq];simpl in Heq;subst m0.
        apply received_messages_consistency;assumption.
      - intro H. apply received_messages_full;[assumption|].
        apply (received_messages_consistency s Hs m) in H.
        exists (exist _ m H). reflexivity.
    Qed.

    Definition computable_received_messages_has_not_been_received
      {Hsm : computable_received_messages}
      (s : vstate vlsm)
      (m : message)
      : Prop
      :=
      ~ computable_received_messages_has_been_received s m.

    Lemma computable_received_messages_has_not_been_received_proper
      {Hsm : computable_received_messages}
      (s : state)
      (Hs : protocol_state_prop pre_vlsm s)
      (m : message)
      : has_not_been_received_prop computable_received_messages_has_not_been_received s m.
    Proof.
      unfold has_not_been_received_prop. unfold no_traces_have_message_prop.
      unfold computable_received_messages_has_not_been_received.
      unfold computable_received_messages_has_been_received.
      rewrite <- selected_message_exists_preloaded_not_some_iff_no.
      apply not_iff_compat.
      rewrite received_messages_full;[|assumption].
      unfold received_messages.
      rewrite exists_proj1_sig.
      reflexivity.
    Qed.

    Definition computable_received_messages_has_been_received_capability
      {Hsm : computable_received_messages}
      {eq_message : EqDecision message}
      : has_been_received_capability
      :=
      {|
        has_been_received := computable_received_messages_has_been_received;
        proper_received := computable_received_messages_has_been_received_proper;
        proper_not_received := computable_received_messages_has_not_been_received_proper
      |}.
End Simple.

(**
 *** Stepwise consistency properties for [state_message_oracle].

 The above definitions like [all_traces_have_message_prop]
 connect a [state_message_oracle] to a predicate on
 [transition_item] by relating the oracle holding on a state
 to a satsifying transition existing in all traces.

 This is equivalent to two local properties,
 one is that the oracle cannot only for any initial state,
 the other is that the oracle judgement is appropriately
 related for the starting and [destination] states of
 any [protocol_transition].

 These conditions are defined in the record [oracle_stepwise_props]
 *)

Record oracle_stepwise_props
       [message] [vlsm: VLSM message]
       (message_selector: message -> transition_item -> Prop)
       (oracle: state_message_oracle vlsm) : Prop :=
  {oracle_no_inits: forall (s: vstate vlsm),
      initial_state_prop (VLSM_sign:=sign vlsm) s ->
      forall m, ~oracle s m;
   oracle_step_update:
       forall l s im s' om,
         protocol_transition (pre_loaded_with_all_messages_vlsm vlsm) l (s,im) (s',om) ->
         forall msg, oracle s' msg <->
                     (message_selector msg {|l:=l; input:=im; destination:=s'; output:=om|}
                      \/ oracle s msg)
  }.
Arguments oracle_no_inits {message} {vlsm} {message_selector} {oracle} _.
Arguments oracle_step_update {message} {vlsm} {message_selector} {oracle} _.

Lemma oracle_partial_trace_update
      [message] [vlsm: VLSM message]
      [selector: message -> transition_item -> Prop]
      [oracle: state_message_oracle vlsm]
      (Horacle: oracle_stepwise_props selector oracle)
      s0 s tr
         (Htr: finite_protocol_trace_from_to (pre_loaded_with_all_messages_vlsm vlsm) s0 s tr):
    forall m,
      oracle s m
      <-> (trace_has_message selector m tr \/ oracle s0 m).
Proof.
  induction Htr.
  - intro m.
    unfold trace_has_message.
    rewrite Exists_nil.
    tauto.
  - intro m. specialize (IHHtr m).
    unfold trace_has_message.
    rewrite Exists_cons.
    apply (Horacle.(oracle_step_update)) with (msg:=m) in H.
    tauto.
Qed.

(**
   Proving the trace properties from the stepwise properties
   begins with a lemma using induction along a trace to
   prove that given a [finite_protocol_trace] to a state,
   the oracle holds at that state for some message iff
   a satsifying transition item exists in the trace.

   The theorems for [all_traces_have_message_prop]
   and [no_traces_have_message_prop] are mostly rearraning
   quantifiers to use this lemma, also using [protocol_state_prop]
   to choose a trace to the state for the directions where
   one is not given.
 *)
Section TraceFromStepwise.
  Context
    (message : Type)
    (vlsm: VLSM message)
    (selector : message -> transition_item -> Prop)
    (oracle : state_message_oracle vlsm)
    (oracle_props : oracle_stepwise_props selector oracle)
    .

  Local Lemma H_protocol_trace_prop
        [s0 s tr]
        (Htr: finite_protocol_trace_init_to (pre_loaded_with_all_messages_vlsm vlsm) s0 s tr):
    forall m,
      oracle s m <-> trace_has_message selector m tr.
  Proof.
    intro m.
    destruct Htr as [Htr Hinit].
    rewrite (oracle_partial_trace_update oracle_props _ _ _ Htr).
    assert (~oracle s0 m).
    apply oracle_props, Hinit.
    tauto.
  Qed.

  Lemma prove_all_have_message_from_stepwise:
    forall (s : state)
           (Hs : protocol_state_prop (pre_loaded_with_all_messages_vlsm vlsm) s)
           (m : message),
      (all_traces_have_message_prop vlsm selector oracle s m).
  Proof.
    intros s Hproto m.
    unfold all_traces_have_message_prop.
    split.
    - intros Hsent s0 tr Htr.
      apply (H_protocol_trace_prop Htr).
      assumption.
    - intro H_all_traces.
      apply protocol_state_has_trace in Hproto.
      destruct Hproto as [s0 [tr Htr]].
      apply (H_protocol_trace_prop Htr).
      specialize (H_all_traces s0 tr Htr).
      assumption.
  Qed.

  Lemma prove_none_have_message_from_stepwise:
    forall (s : state)
           (Hs : protocol_state_prop (pre_loaded_with_all_messages_vlsm vlsm) s)
           (m : message),
      no_traces_have_message_prop vlsm selector (fun s m => ~oracle s m) s m.
  Proof.
    intros s Hproto m.
    pose proof (H_protocol_trace_prop).
    split.
    - intros H_not_sent start tr Htr.
      contradict H_not_sent.
      apply (H_protocol_trace_prop Htr).
      assumption.
    - intros H_no_traces.
      apply protocol_state_has_trace in Hproto.
      destruct Hproto as [s0 [tr Htr]].
      specialize (H_no_traces s0 tr Htr).
      contradict H_no_traces.
      apply (H_protocol_trace_prop Htr).
      assumption.
  Qed.

  Lemma in_futures_preserving_oracle_from_stepwise:
    forall (s1 s2: state)
      (Hfutures : in_futures (pre_loaded_with_all_messages_vlsm vlsm) s1 s2)
      (m : message),
      oracle s1 m -> oracle  s2 m.
  Proof.
    intros s1 s2 [tr Htr] m Hs1m.
    apply (oracle_partial_trace_update oracle_props _ _ _ Htr).
    right;assumption.
  Qed.
End TraceFromStepwise.

(**
   The stepwise properties are proven from the trace properties
   by considering the empty trace to prove the [oracle_no_inits]
   property, and by considering a trace that ends with the given
   [protocol_transition] to prove the [oracle_step_update] property.
 *)
Section StepwiseFromTrace.
  Context
    (message : Type)
    (vlsm: VLSM message)
    (selector: message -> transition_item -> Prop)
    (oracle: state_message_oracle vlsm)
    (oracle_dec: RelDecision oracle)
    (Horacle_all_have:
       forall s (Hs: protocol_state_prop (pre_loaded_with_all_messages_vlsm vlsm) s) m,
        all_traces_have_message_prop vlsm selector oracle s m)
    (Hnot_oracle_none_have:
       forall s (Hs: protocol_state_prop (pre_loaded_with_all_messages_vlsm vlsm) s) m,
         no_traces_have_message_prop vlsm selector (fun m s => ~oracle m s) s m).

  Lemma oracle_no_inits_from_trace:
    forall (s: vstate vlsm), initial_state_prop (VLSM_sign:=sign vlsm) s ->
                             forall m, ~oracle s m.
  Proof.
    intros s Hinit m Horacle.
    assert (Hproto : protocol_state_prop (pre_loaded_with_all_messages_vlsm vlsm) s)
      by (apply initial_is_protocol;assumption).
    apply Horacle_all_have in Horacle;[|assumption].
    specialize (Horacle s nil).
    eapply Exists_nil;apply Horacle;clear Horacle.
    split;[constructor|];assumption.
  Qed.

  Lemma examine_one_trace:
    forall is s tr,
      finite_protocol_trace_init_to (pre_loaded_with_all_messages_vlsm vlsm) is s tr ->
    forall m,
      oracle s m <->
      trace_has_message selector m tr.
  Proof.
    intros is s tr Htr m.
    assert (protocol_state_prop (pre_loaded_with_all_messages_vlsm vlsm) s)
      by (apply ptrace_last_pstate in Htr;assumption).
    split.
    - intros Horacle.
      apply Horacle_all_have in Horacle;[|assumption].
      specialize (Horacle is tr Htr).
      assumption.
    - intro Hexists.
      apply dec_stable.
      intro Hnot.
      apply Hnot_oracle_none_have in Hnot;[|assumption].
      rewrite <- selected_message_exists_preloaded_not_some_iff_no in Hnot.
      apply Hnot.
      exists is, tr, Htr.
      assumption.
  Qed.

  Lemma oracle_step_property_from_trace:
       forall l s im s' om,
         protocol_transition (pre_loaded_with_all_messages_vlsm vlsm) l (s,im) (s',om) ->
         forall msg, oracle s' msg
                     <-> (selector msg {| l:=l; input:=im; destination:=s'; output:=om |}
                          \/ oracle s msg).
  Proof.
    intros l s im s' om Htrans msg.
    rename Htrans into Htrans'.
    pose proof Htrans' as [[Hproto_s [Hproto_m Hvalid]] Htrans].
    set (preloaded:= pre_loaded_with_all_messages_vlsm vlsm) in * |- *.

    pose proof (protocol_state_has_trace _ _ Hproto_s)
      as [is [tr [Htr Hinit]]].

    pose proof (Htr' := extend_right_finite_trace_from_to _ Htr Htrans').

    rewrite (examine_one_trace _ _ _ (conj Htr Hinit) msg).
    rewrite (examine_one_trace _ _ _ (conj Htr' Hinit) msg).
    clear.
    progress cbn. unfold trace_has_message.
    rewrite Exists_app, Exists_cons, Exists_nil.
    tauto.
  Qed.

  Lemma stepwise_props_from_trace : oracle_stepwise_props selector oracle.
  Proof.
    constructor.
    refine oracle_no_inits_from_trace.
    refine oracle_step_property_from_trace.
  Defined.
End StepwiseFromTrace.

(**
** Stepwise view of [has_been_sent_capability]

This reduces the proof obligations in [has_been_sent_capability]
to proving the stepwise properties of [oracle_stepwise_props].
[has_been_step_stepwise_props] is a specialization of [oracle_stepwise_props]
to the right <<message_selector>>.

There are also lemmas for accessing the stepwise properties about
a [has_been_sent] predicate given an instance of [has_been_sent_capability], to allow using
[has_been_sent_capability_from_stepwise] to define a [has_been_sent_capability]
for composite VLSMs, or for proofs (e.g, about invariants) where
these are more convenient.
 **)

Definition has_been_sent_stepwise_props
       [message] [vlsm: VLSM message] (has_been_sent_pred: state_message_oracle vlsm) : Prop :=
  (oracle_stepwise_props (field_selector output) has_been_sent_pred).

Lemma has_been_sent_capability_from_stepwise
      [message : Type]
      [vlsm: VLSM message]
      [has_been_sent_pred: state_message_oracle vlsm]
      (has_been_sent_pred_dec: RelDecision has_been_sent_pred)
      (has_been_sent_alt_props: has_been_sent_stepwise_props has_been_sent_pred):
  has_been_sent_capability vlsm.
Proof.
  refine ({|has_been_sent:=has_been_sent_pred|}).
  apply prove_all_have_message_from_stepwise;assumption.
  apply prove_none_have_message_from_stepwise;assumption.
Defined.

Lemma has_been_sent_stepwise_from_trace
      [message : Type]
      [vlsm: VLSM message]
      (Hhbs: has_been_sent_capability vlsm):
  oracle_stepwise_props (field_selector output) (has_been_sent vlsm).
Proof.
  apply stepwise_props_from_trace.
  apply has_been_sent_dec.
  apply proper_sent.
  apply proper_not_sent.
Defined.

Lemma has_been_sent_step_update
      `{Hhbs: has_been_sent_capability message vlsm}:
  forall [l s im s' om],
    protocol_transition (pre_loaded_with_all_messages_vlsm vlsm) l (s,im) (s',om) ->
    forall m,
      has_been_sent vlsm s' m <-> (om = Some m \/ has_been_sent vlsm s m).
Proof.
  exact (oracle_step_update (has_been_sent_stepwise_from_trace Hhbs)).
Qed.

(**
** Stepwise view of [has_been_received_capability]
 *)

Definition has_been_received_stepwise_props
       [message] [vlsm: VLSM message] (has_been_received_pred: state_message_oracle vlsm) : Prop :=
  (oracle_stepwise_props (field_selector input) has_been_received_pred).

Lemma has_been_received_capability_from_stepwise
      [message : Type]
      [vlsm: VLSM message]
      [has_been_received_pred: state_message_oracle vlsm]
      (has_been_received_pred_dec: RelDecision has_been_received_pred)
      (has_been_sent_alt_props: has_been_received_stepwise_props has_been_received_pred):
  has_been_received_capability vlsm.
Proof.
  refine ({|has_been_received:=has_been_received_pred|}).
  apply prove_all_have_message_from_stepwise;assumption.
  apply prove_none_have_message_from_stepwise;assumption.
Defined.

Lemma has_been_received_stepwise_from_trace
      [message : Type]
      [vlsm: VLSM message]
      (Hhbr: has_been_received_capability vlsm):
  oracle_stepwise_props (field_selector input) (has_been_received vlsm).
Proof.
  apply stepwise_props_from_trace.
  apply has_been_received_dec.
  apply proper_received.
  apply proper_not_received.
Defined.

Lemma has_been_received_step_update
      `{Hhbs: has_been_received_capability message vlsm}:
  forall [l s im s' om],
    protocol_transition (pre_loaded_with_all_messages_vlsm vlsm) l (s,im) (s',om) ->
    forall m,
      has_been_received vlsm s' m <-> (im = Some m \/ has_been_received vlsm s m).
Proof.
  exact (oracle_step_update (has_been_received_stepwise_from_trace Hhbs)).
Qed.

(**
** A state message oracle for messages sent or received

In protocols like the CBC full node protocol, validators often
work with the set of all messages they have directly observed,
which includes the messages the node sent itself along with
messages that were received.
The [has_been_observed] oracle holds for a message if the
message was sent or received in any transition.
 *)

Class has_been_observed_capability {message} (vlsm: VLSM message) :=
  {
  has_been_observed: state_message_oracle vlsm;
  has_been_observed_dec :> RelDecision has_been_observed;
  has_been_observed_stepwise_props: oracle_stepwise_props item_sends_or_receives has_been_observed;
  }.
Arguments has_been_observed {message} vlsm {_}.
Arguments has_been_observed_dec {message} vlsm {_}.

Definition has_been_observed_step_update `{Hhbo: has_been_observed_capability message vlsm} :
  forall l s im s' om,
    protocol_transition (pre_loaded_with_all_messages_vlsm vlsm) l (s, im) (s', om) ->
    forall msg,
      has_been_observed vlsm s' msg <->
      ((im = Some msg \/ om = Some msg) \/ has_been_observed vlsm s msg)
  := oracle_step_update has_been_observed_stepwise_props.

Lemma proper_observed `(Hhbo: has_been_observed_capability message vlsm):
  forall (s:state),
    protocol_state_prop (pre_loaded_with_all_messages_vlsm vlsm) s ->
    forall m,
      all_traces_have_message_prop vlsm item_sends_or_receives (has_been_observed vlsm) s m.
Proof.
  intros.
  apply prove_all_have_message_from_stepwise.
  apply Hhbo.
  assumption.
Qed.

Lemma proper_not_observed `(Hhbo: has_been_observed_capability message vlsm):
  forall (s:state),
    protocol_state_prop (pre_loaded_with_all_messages_vlsm vlsm) s ->
    forall m,
      no_traces_have_message_prop vlsm item_sends_or_receives
                                  (fun s m => ~has_been_observed vlsm s m) s m.
Proof.
  intros.
  apply prove_none_have_message_from_stepwise.
  apply Hhbo.
  assumption.
Qed.

(** A received message introduces no additional equivocations to a state
    if it has already been observed in s or it is an initial message.
*)
Definition no_additional_equivocations
  {message : Type}
  (vlsm : VLSM message)
  {Hbo : has_been_observed_capability vlsm}
  (s : state)
  (m : message)
  : Prop
  :=
  has_been_observed vlsm s m \/ vinitial_message_prop vlsm m.

(** If the [initial_message_prop] is decidable, then the
    [no_additional_equivocations] is also decidable.
*)

  Lemma no_additional_equivocations_dec
  {message : Type}
  (vlsm : VLSM message)
  {Hbo : has_been_observed_capability vlsm}
  (initial_dec : vdecidable_initial_messages_prop vlsm)
  : RelDecision (no_additional_equivocations vlsm).
Proof.
  intros s m. apply Decision_or; [|apply initial_dec].
  apply has_been_observed_dec.
Qed.

Definition no_additional_equivocations_constraint
  {message : Type}
  (vlsm : VLSM message)
  {Hbo : has_been_observed_capability vlsm}
  (l : vlabel vlsm)
  (som : state * option message)
  : Prop
  :=
  let (s, om) := som in
  match om with
  | None => True
  | Some m => no_additional_equivocations vlsm s m
  end.

Section sent_received_observed_capabilities.

Context
  {message : Type}
  (vlsm : VLSM message)
  {Hbr : has_been_received_capability vlsm}
  {Hbs : has_been_sent_capability vlsm}
  .

Lemma has_been_observed_sent_received_iff
  {Hbo : has_been_observed_capability vlsm}
  (s : state)
  (Hs : protocol_state_prop (pre_loaded_with_all_messages_vlsm vlsm) s)
  (m : message)
  : has_been_observed vlsm s m <-> has_been_received vlsm s m \/ has_been_sent vlsm s m.
Proof.
  specialize
    (prove_all_have_message_from_stepwise message vlsm  item_sends_or_receives
    (has_been_observed vlsm) has_been_observed_stepwise_props _ Hs m) as Hall.
  split; [intro H | intros [H | H]].
  - apply proj1 in Hall. specialize (Hall H).
    apply consistency_from_protocol_proj2 in Hall; [|assumption].
    destruct Hall as [is [tr [Htr Hexists]]].
    apply Exists_or_inv in Hexists.
    destruct Hexists as [Hsent | Hreceived].
    + left. specialize (has_been_received_consistency vlsm _ Hs m) as Hcons.
      apply proper_received; [assumption|].
      apply Hcons. exists is, tr, Htr. assumption.
    + right. specialize (has_been_sent_consistency vlsm _ Hs m) as Hcons.
      apply proper_sent; [assumption|].
      apply Hcons. exists is, tr, Htr. assumption.
  - apply Hall.
    intro is; intros.
    apply proper_received in H; [|assumption]. specialize (H is tr Htr).
    apply Exists_or. left. assumption.
  - apply Hall.
    intro is; intros.
    apply proper_sent in H; [|assumption]. specialize (H is tr Htr).
    apply Exists_or. right. assumption.
Qed.

Definition has_been_observed_from_sent_received
  (s : vstate vlsm)
  (m : message)
  : Prop
  := has_been_sent vlsm s m \/ has_been_received vlsm s m.

Lemma has_been_observed_from_sent_received_dec
  : RelDecision has_been_observed_from_sent_received.
Proof.
  intros s m.
  apply Decision_or.
  - apply has_been_sent_dec.
  - apply has_been_received_dec.
Qed.

Lemma has_been_observed_from_sent_received_stepwise_props
  : oracle_stepwise_props item_sends_or_receives has_been_observed_from_sent_received.
Proof.
  apply stepwise_props_from_trace; [apply has_been_observed_from_sent_received_dec|..]
  ; intros; split; intros.
  - intro; intros.
    destruct H as [H | H].
    + apply proper_sent in H; [|apply Hs]. specialize (H _ _ Htr).
      apply Exists_or. right. assumption.
    + apply proper_received in H; [|apply Hs]. specialize (H _ _ Htr).
      apply Exists_or. left. assumption.
  - apply consistency_from_protocol_proj2 in H; [|assumption].
    destruct H as [is [tr [Htr Hexists]]].
    apply Exists_or_inv in Hexists.
    destruct Hexists as [Hsent | Hreceived].
    + right. apply proper_received; [assumption|].
      apply has_been_received_consistency; [assumption|assumption|].
      exists is, tr, Htr. assumption.
    + left. apply proper_sent; [assumption|].
      apply has_been_sent_consistency; [assumption|assumption|].
      exists is, tr, Htr. assumption.
  - intro; intros. intro Hexists. elim H.
    apply Exists_or_inv in Hexists.
    destruct Hexists as [Hexists| Hexists].
    + right. apply proper_received; [assumption|].
      apply has_been_received_consistency; [assumption|assumption|].
      exists start, tr, Htr. assumption.
    + left. apply proper_sent; [assumption|].
      apply has_been_sent_consistency; [assumption|assumption|].
      exists start, tr, Htr. assumption.
  - intros [Hobs | Hobs].
    + apply proper_sent in Hobs; [|assumption].
      apply has_been_sent_consistency in Hobs; [|assumption|assumption].
      destruct Hobs as [is [tr [Htr Hexists]]].
      specialize (H _ _ Htr). elim H. apply Exists_or. right. assumption.
    + apply proper_received in Hobs; [|assumption].
      apply has_been_received_consistency in Hobs; [|assumption|assumption].
      destruct Hobs as [is [tr [Htr Hexists]]].
      specialize (H _ _ Htr). elim H. apply Exists_or. left. assumption.
Qed.

Local Program Instance has_been_observed_capability_from_sent_received
  : has_been_observed_capability vlsm
  :=
  { has_been_observed := has_been_observed_from_sent_received;
    has_been_observed_dec := has_been_observed_from_sent_received_dec;

    has_been_observed_stepwise_props := has_been_observed_from_sent_received_stepwise_props
  }.

End sent_received_observed_capabilities.

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

  Definition observed_were_sent_or_initial (s: state) : Prop :=
    forall msg, has_been_observed X s msg -> has_been_sent X s msg \/ vinitial_message_prop X msg.

  Lemma observed_were_sent_initial s:
    vinitial_state_prop X s ->
    observed_were_sent_or_initial s.
  Proof.
    intros Hinitial msg Hsend.
    contradict Hsend.
    apply (oracle_no_inits has_been_observed_stepwise_props).
    assumption.
  Qed.

  Lemma observed_were_sent_preserved l s im s' om:
    protocol_transition X l (s,im) (s',om) ->
    observed_were_sent_or_initial s ->
    observed_were_sent_or_initial s'.
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
      destruct Henforced; [|right; assumption].
      left. right. assumption.
    - left. left. assumption.
    - specialize (Hprev H).
      destruct Hprev as [Hprev|Hprev]; [|right; assumption].
      left. right. assumption.
  Qed.

  Lemma observed_were_sent_invariant s:
    protocol_state_prop X s ->
    observed_were_sent_or_initial s.
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
        spec Henforced Hv.
        destruct Henforced as [Hbs | Hinitial]; [|right; assumption].
        left. right. assumption.
      + left. left. assumption.
      + spec IHHproto H. destruct IHHproto; [|right; assumption].
        left. right. assumption.
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
      ; [|apply initial_message_is_protocol; assumption].
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

(**
*** Equivocation in compositions.

 We now move on to a composite context. Each component of our composition
    will have [has_been_sent] and [has_been_received] capabilities.

    We introduce [validator]s along with their respective [Weight]s, the
    [A] function which maps validators to indices of component VLSMs and
    the [sender] function which maps messages to their (unique) designated
    sender (if any).

    For the equivocation fault sum to be computable, we also require that
    the number of [validator]s and the number of machines in the
    composition are both finite. See [finite_index], [finite_validator].
**)

Section Composite.

  Context {message : Type}
          {index : Type}
          {IndEqDec : EqDecision index}
          (IM : index -> VLSM message)
          {i0 : Inhabited index}
          (constraint : composite_label IM -> composite_state IM  * option message -> Prop)
          (X := composite_vlsm IM constraint)
          {index_listing : list index}
          (finite_index : Listing index_listing)
          (has_been_sent_capabilities : forall i : index, (has_been_sent_capability (IM i)))
          (has_been_observed_capabilities : forall i : index, (has_been_observed_capability (IM i)))
          .

  Section StepwiseProps.
    Context
      [message_selectors: forall i : index, message -> vtransition_item (IM i) -> Prop]
      [oracles: forall i, state_message_oracle (IM i)]
      (stepwise_props: forall i, oracle_stepwise_props (message_selectors i) (oracles i))
      .

      Definition composite_message_selector : message -> vtransition_item X -> Prop.
      Proof.
        intros msg [[i li] input s output].
        apply (message_selectors i msg).
        exact {|l:=li;input:=input;destination:=s i;output:=output|}.
      Defined.

      Definition composite_oracle : vstate X -> message -> Prop :=
        fun s msg => exists i, oracles i (s i) msg.

      Lemma composite_stepwise_props :
        oracle_stepwise_props composite_message_selector composite_oracle.
      Proof.
        split.
        - (* initial states not claim *)
          intros s Hs m [i H].
          revert H.
          fold (~ oracles i (s i) m).
          apply (oracle_no_inits (stepwise_props i)).
          apply Hs.
        - (* step update property *)
          intros l s im s' om Hproto msg.
          destruct l as [i li].
          simpl.
          assert (forall j, s j = s' j \/ j = i).
          {
            intro j.
            apply (protocol_transition_preloaded_project_any j) in Hproto.
            destruct Hproto;[left;assumption|right].
            destruct H as [lj [Hlj _]].
            congruence.
          }
          apply protocol_transition_preloaded_project_active in Hproto;simpl in Hproto.
          apply (oracle_step_update (stepwise_props i)) with (msg:=msg) in Hproto.
          split.
          + intros [j Hj].
            destruct (H j) as [Hunchanged|Hji].
            * right;exists j;rewrite Hunchanged;assumption.
            * subst j.
              apply Hproto in Hj.
              destruct Hj;[left;assumption|right;exists i;assumption].
          + intros [Hnow | [j Hbefore]].
            * exists i.
              apply Hproto.
              left;assumption.
            * exists j.
              destruct (H j) as [Hunchanged| ->].
              -- rewrite <- Hunchanged;assumption.
              -- apply Hproto.
                 right.
                 assumption.
      Qed.
  End StepwiseProps.

  (** A message 'has_been_sent' for a composite state if it 'has_been_sent' for any of
  its components.*)
  Definition composite_has_been_sent
    (s : vstate X)
    (m : message)
    : Prop
    := exists (i : index), has_been_sent (IM i) (s i) m.

  (** 'composite_has_been_sent' is decidable. *)
  Lemma composite_has_been_sent_dec : RelDecision composite_has_been_sent.
  Proof.
    intros s m.
    apply (Decision_iff (P:=List.Exists (fun i => has_been_sent (IM i) (s i) m) index_listing)).
    - rewrite <- exists_finite by (apply finite_index). reflexivity.
    - apply Exists_dec.
  Qed.

  Lemma composite_has_been_sent_stepwise_props :
    has_been_sent_stepwise_props composite_has_been_sent.
  Proof.
    unfold has_been_sent_stepwise_props.
    pose proof (composite_stepwise_props
                  (fun i => has_been_sent_stepwise_from_trace
                              (has_been_sent_capabilities i)))
         as [Hinits Hstep].
    split;[exact Hinits|].
    (* <<exact Hstep>> doesn't work because [composite_message_selector]
       pattern matches on the label l, so we instantiate and destruct
       to let that simplify *)
    intros l;specialize (Hstep l);destruct l.
    exact Hstep.
  Qed.

  Global Instance composite_has_been_sent_capability : has_been_sent_capability X :=
    has_been_sent_capability_from_stepwise
      composite_has_been_sent_dec
      composite_has_been_sent_stepwise_props.

  Section composite_has_been_received.

  Context
        (has_been_received_capabilities : forall i : index, (has_been_received_capability (IM i)))
        .

  (** A message 'has_been_received' for a composite state if it 'has_been_received' for any of
  its components.*)
  Definition composite_has_been_received
    (s : vstate X)
    (m : message)
    : Prop
    := exists (i : index), has_been_received (IM i) (s i) m.

  (** 'composite_has_been_received' is decidable. *)
  Lemma composite_has_been_received_dec : RelDecision composite_has_been_received.
  Proof.
    intros s m.
    apply (Decision_iff (P:=List.Exists (fun i => has_been_received (IM i) (s i) m) index_listing)).
    - rewrite <- exists_finite by (apply finite_index). reflexivity.
    - apply Exists_dec.
  Qed.

  Lemma composite_has_been_received_stepwise_props :
    has_been_received_stepwise_props composite_has_been_received.
  Proof.
    unfold has_been_received_stepwise_props.
    pose proof (composite_stepwise_props
                  (fun i => has_been_received_stepwise_from_trace
                              (has_been_received_capabilities i)))
         as [Hinits Hstep].
    split;[exact Hinits|].
    (* <<exact Hstep>> doesn't work because [composite_message_selector]
       pattern matches on the label l, so we instantiate and destruct
       to let that simplify *)
    intros l;specialize (Hstep l);destruct l.
    exact Hstep.
  Qed.

  Global Instance composite_has_been_received_capability : has_been_received_capability X :=
    has_been_received_capability_from_stepwise
      composite_has_been_received_dec
      composite_has_been_received_stepwise_props.

  End composite_has_been_received.


  (** A message 'has_been_observed' for a composite state if it 'has_been_observed' for any of
  its components.*)
  Definition composite_has_been_observed
    (s : vstate X)
    (m : message)
    : Prop
    := exists (i : index), has_been_observed (IM i) (s i) m.

  (** 'composite_has_been_observed' is decidable. *)
  Lemma composite_has_been_observed_dec : RelDecision composite_has_been_observed.
  Proof.
    intros s m.
    apply (Decision_iff (P:=List.Exists (fun i => has_been_observed (IM i) (s i) m) index_listing)).
    - rewrite <- exists_finite by (apply finite_index). reflexivity.
    - apply Exists_dec.
  Qed.

  Lemma composite_has_been_observed_stepwise_props :
    oracle_stepwise_props item_sends_or_receives composite_has_been_observed.
  Proof.
    pose proof (composite_stepwise_props
                  (fun i => has_been_observed_stepwise_props))
         as [Hinits Hstep].
    split;[exact Hinits|].
    intros l;specialize (Hstep l);destruct l.
    exact Hstep.
  Qed.

  Global Instance composite_has_been_observed_capability : has_been_observed_capability X :=
    { has_been_observed_dec := composite_has_been_observed_dec;
      has_been_observed_stepwise_props := composite_has_been_observed_stepwise_props
    }.

  Context
        {validator : Type}
        (A : validator -> index)
        (sender : message -> option validator)
        .

  (** Definitions for safety and nontriviality of the [sender] function.
      Safety means that if we designate a validator as the sender
      of a certain messsage, then it is impossible for other components
      to produce that message

      Weak/strong nontriviality say that each validator should
      be designated sender for at least one/all its protocol
      messages.
  **)

  Definition sender_safety_prop : Prop :=
    forall
    (i : index)
    (m : message)
    (v : validator)
    (Hid : A v = i)
    (Hsender : sender m = Some v),
    can_emit (composite_vlsm_constrained_projection IM constraint i) m /\
    forall (j : index)
           (Hdif : i <> j),
           ~can_emit (composite_vlsm_constrained_projection IM constraint j) m.

   (** An alternative, possibly friendlier, formulation. Note that it is
       slightly weaker, in that it does not require that the sender
       is able to send the message. **)

  Definition sender_safety_alt_prop : Prop :=
    forall
    (i : index)
    (m : message)
    (v : validator)
    (Hsender : sender m = Some v),
    can_emit (composite_vlsm_constrained_projection IM constraint i) m ->
    A v = i.

  Definition sender_weak_nontriviality_prop : Prop :=
    forall (v : validator),
    exists (m : message),
    can_emit (composite_vlsm_constrained_projection IM constraint (A v)) m /\
    sender m = Some v.

  Definition sender_strong_nontriviality_prop : Prop :=
    forall (v : validator),
    forall (m : message),
    can_emit (composite_vlsm_constrained_projection IM constraint (A v)) m ->
    sender m = Some v.

  Definition no_sender_for_initial_message_prop : Prop :=
    forall (m : message),
    vinitial_message_prop X m ->
    sender m = None.

  Context
        (has_been_received_capabilities : forall i : index, (has_been_received_capability (IM i)))
        .

   (** We say that a validator <v> (with associated component <i>) is equivocating wrt.
   to another component <j>, if there exists a message which [has_been_received] by
   <j> but [has_not_been_sent] by <i> **)

  Definition equivocating_wrt
    (v : validator)
    (j : index)
    (sv sj : state)
    (i := A v)
    : Prop
    :=
    exists (m : message),
    sender(m) = Some v /\
    has_not_been_sent  (IM i) sv m /\
    has_been_received  (IM j) sj m.

  (** We can now decide whether a validator is equivocating in a certain state. **)

  Definition is_equivocating_statewise
    (s : vstate X)
    (v : validator)
    : Prop
    :=
    exists (j : index),
    j <> (A v) /\
    equivocating_wrt v j (s (A v)) (s j).

  (** An alternative definition for detecting equivocation in a certain state,
      which checks if for every [protocol_trace] there exists equivocation
      involving the given validator

      Notably, this definition is not generally equivalent to [is_equivocating_statewise],
      which does not verify the order in which receiving and sending occurred.
  **)

  Definition is_equivocating_tracewise
    (s : vstate X)
    (v : validator)
    (j := A v)
    : Prop
    :=
    forall (tr : protocol_trace X)
    (last : transition_item)
    (prefix : list transition_item)
    (Hpr : trace_prefix X (proj1_sig tr) last prefix)
    (Hlast : destination last = s),
    exists (m : message),
    (sender m = Some v) /\
    List.Exists
    (fun (elem : vtransition_item X) =>
    input elem = Some m
    /\ ~has_been_sent (IM j) ((destination elem) j) m
    ) prefix.

  (** A possibly friendlier version using a previously defined primitive. **)
  Definition is_equivocating_tracewise_alt
    (s : vstate X)
    (v : validator)
    (j := A v)
    : Prop
    :=
    forall (tr : protocol_trace X)
    (last : transition_item)
    (prefix : list transition_item)
    (Hpr : trace_prefix X (proj1_sig tr) last prefix)
    (Hlast : destination last = s),
    exists (m : message),
    (sender m = Some v) /\
    equivocation_in_trace X m (prefix ++ [last]).

  Context
      (validator_listing : list validator)
      {finite_validator : Listing validator_listing}
      {measurable_V : Measurable validator}
      {threshold_V : ReachableThreshold validator}
      .
  (** For the equivocation sum fault to be computable, we require that
      our is_equivocating property is decidable. The current implementation
      refers to [is_equivocating_statewise], but this might change
      in the future **)

  Definition equivocation_dec_statewise
     (Hdec : RelDecision is_equivocating_statewise)
      : basic_equivocation (vstate X) (validator)
    :=
    {|
      state_validators := fun _ => validator_listing;
      state_validators_nodup := fun _ => proj1 finite_validator;
      is_equivocating := is_equivocating_statewise;
      is_equivocating_dec := Hdec
    |}.

  Definition equivocation_dec_tracewise
     (Hdec : RelDecision is_equivocating_tracewise)
      : basic_equivocation (vstate X) (validator)
    :=
    {|
      state_validators := fun _ => validator_listing;
      state_validators_nodup := fun _ => proj1 finite_validator;
      is_equivocating := is_equivocating_tracewise;
      is_equivocating_dec := Hdec
    |}.

  Definition equivocation_fault_constraint
    (Dec : basic_equivocation (vstate X) validator)
    (l : vlabel X)
    (som : vstate X * option message)
    : Prop
    :=
    let (s', om') := (vtransition X l som) in
    not_heavy s'.

    (* begin hide *)
  Lemma sent_component_protocol_composed
    (s : vstate X)
    (Hs : protocol_state_prop X s)
    (i : index)
    (m : message)
    (Hsent : (@has_been_sent _ _ (has_been_sent_capabilities i)
           (s i) m)) :
    protocol_message_prop X m.
  Proof.
    assert (Hcomp : has_been_sent X s m) by (exists i; intuition).
    assert (protocol_state_prop (pre_loaded_with_all_messages_vlsm X) s) by
      (apply pre_loaded_with_all_messages_protocol_state_prop; intuition).

    apply protocol_state_has_trace in Hs as H'.
    destruct H' as [is [tr Hpr]].
    assert (Hpr_pre : finite_protocol_trace_init_to (pre_loaded_with_all_messages_vlsm X) is s tr). {
      revert Hpr.
      apply VLSM_incl_finite_protocol_trace_init_to.
      apply vlsm_incl_pre_loaded_with_all_messages_vlsm.
    }
    apply protocol_trace_output_is_protocol with (is0:=is) (tr0:=tr).
    - apply ptrace_forget_last in Hpr; apply Hpr.
    - apply (proper_sent _ _ H) in Hcomp.
      apply (Hcomp is tr Hpr_pre).
  Qed.

  Lemma received_component_protocol_composed
    (s : vstate X)
    (Hs : protocol_state_prop X s)
    (i : index)
    (m : message)
    (Hreceived : (@has_been_received _ _ (has_been_received_capabilities i)
           (s i) m)) :
    protocol_message_prop X m.
  Proof.
    assert (Hcomp : has_been_received X s m) by (exists i; assumption).
    assert (protocol_state_prop (pre_loaded_with_all_messages_vlsm X) s) by
      (apply pre_loaded_with_all_messages_protocol_state_prop; assumption).
    
    apply protocol_state_has_trace in Hs as [is [tr Hpr]].
    assert (Hpr_pre : finite_protocol_trace_init_to (pre_loaded_with_all_messages_vlsm X) is s tr). {
      revert Hpr.
      apply VLSM_incl_finite_protocol_trace_init_to.
      apply vlsm_incl_pre_loaded_with_all_messages_vlsm.
    }

    specialize (@proper_received _ X _ s H m) as Hprop.
    unfold has_been_received_prop in Hprop.
    unfold all_traces_have_message_prop in Hprop.
    apply Hprop in Hcomp.
    specialize (Hcomp is tr Hpr_pre).
    destruct Hpr as [Hpr _].
    apply ptrace_forget_last in Hpr.
    apply protocol_trace_input_is_protocol with (is0 := is) (tr0 := tr);assumption.
  Qed.
     (* end hide *)
End Composite.

Section cannot_resend_message.
Context
  {message : Type}
  `{EqDecision message}
  (X : VLSM message)
  (PreX := pre_loaded_with_all_messages_vlsm X)
  {Hbs : has_been_sent_capability X}
  {Hbr : has_been_received_capability X}
  .

Definition state_received_not_sent (s : state) (m : message) : Prop :=
  has_been_received X s m /\ ~ has_been_sent X s m.

Lemma state_received_not_sent_trace_iff
  (m : message)
  (s : state)
  (is : state)
  (tr : list transition_item)
  (Htr : finite_protocol_trace_init_to PreX is s tr)
  : state_received_not_sent s m <-> trace_received_not_sent_before_or_after tr m.
Proof.
  assert (Hs : protocol_state_prop PreX s).
  { apply proj1 in Htr.  apply ptrace_last_pstate in Htr.
    assumption.
  }
  split; intros [Hbrm Hnbsm].
  - apply proper_received in Hbrm; [|assumption].
    specialize (Hbrm is tr Htr).
    split; [assumption|].
    intro Hbsm. elim Hnbsm.
    apply proper_sent; [assumption|].
    apply has_been_sent_consistency; [assumption| assumption|].
    exists is, tr, Htr. assumption.
  - split.
    + apply proper_received; [assumption|].
      apply has_been_received_consistency; [assumption| assumption|].
      exists is, tr, Htr. assumption.
    + intro Hbsm. elim Hnbsm.
      apply proper_sent in Hbsm; [|assumption].
      spec Hbsm is tr Htr. assumption.
Qed.

Definition state_received_not_sent_invariant
  (s : state)
  (P : message -> Prop)
  : Prop
  := forall m, state_received_not_sent s m -> P m.

Lemma state_received_not_sent_invariant_trace_iff
  (P : message -> Prop)
  (s : state)
  (is : state)
  (tr : list transition_item)
  (Htr : finite_protocol_trace_init_to PreX is s tr)
  : state_received_not_sent_invariant s P <->
    trace_received_not_sent_before_or_after_invariant tr P.
Proof.
  split; intros Hinv m Hm
  ; apply Hinv
  ; apply (state_received_not_sent_trace_iff m s is tr Htr)
  ; assumption.
Qed.

(**
A sent message cannot have been previously sent or received.
*)
Definition cannot_resend_message_stepwise_prop : Prop :=
  forall l s oim s' m,
    protocol_transition (pre_loaded_with_all_messages_vlsm X) l (s,oim) (s',Some m) ->
    ~has_been_sent X s m /\ ~has_been_received X s' m.

Lemma cannot_resend_received_message_in_future
  (Hno_resend : cannot_resend_message_stepwise_prop)
  (s1 s2 : state)
  (Hfuture : in_futures PreX s1 s2)
  : forall m : message,
    state_received_not_sent s1 m -> state_received_not_sent s2 m.
Proof.
  intros m Hm.
  destruct Hfuture as [tr2 Htr2].
  induction Htr2.
  - assumption.
  - apply IHHtr2;clear IHHtr2.
    specialize (has_been_received_step_update H m) as Hrupd.
    specialize (has_been_sent_step_update H m) as Hmupd.
    destruct Hm as [Hr Hs].
    eapply or_intror in Hr; apply Hrupd in Hr.
    split.
    + assumption.
    + intros [->|]%Hmupd;[|apply Hs;assumption].
      apply Hno_resend in H as [_ []].
      assumption.
Qed.

  Context
    (Hno_resend : cannot_resend_message_stepwise_prop).

  Lemma lift_preloaded_trace_to_seeded
    (P : message -> Prop)
    (tr: list transition_item)
    (Htrm: trace_received_not_sent_before_or_after_invariant tr P)
    (is: state)
    (Htr: finite_protocol_trace PreX is tr)
    : finite_protocol_trace (pre_loaded_vlsm X P) is tr.
  Proof.
    unfold trace_received_not_sent_before_or_after_invariant in Htrm.
    split; [|apply Htr].
    induction Htr using finite_protocol_trace_rev_ind; intros.
    - rapply @finite_ptrace_empty.
      apply initial_is_protocol. assumption.
    - assert (trace_received_not_sent_before_or_after_invariant tr P) as Htrm'.
      { intros m [Hrecv Hsend]. apply (Htrm m);clear Htrm.
        split;[apply Exists_app;left;assumption|].
        contradict Hsend.
        unfold trace_has_message in Hsend.
        rewrite Exists_app, Exists_cons, Exists_nil in Hsend.
        simpl in Hsend.
        cut (oom <> Some m);[tauto|clear Hsend].
        intros ->.
        cut (has_been_received X sf m);[apply (Hno_resend _ _ _ _ _ Hx)|].
        apply (has_been_received_step_update Hx);right.
        erewrite oracle_partial_trace_update.
        - left;exact Hrecv.
        - apply has_been_received_stepwise_from_trace.
        - apply ptrace_add_default_last. apply Htr.
      }
      specialize (IHHtr Htrm').
      apply (extend_right_finite_trace_from _ IHHtr).
      repeat split;try apply Hx;
      [apply finite_ptrace_last_pstate;assumption|].
      destruct iom as [m|];[|apply option_protocol_message_None].
      (* If m was sent during tr, it is protocol because it was
         produced in a valid (by IHHtr) trace.
         If m was not sent during tr, 
       *)
      assert (Decision (trace_has_message (field_selector output) m tr)) as [Hsent|Hnot_sent].
      apply (@Exists_dec _). intros. apply decide_eq.
      + exact (protocol_trace_output_is_protocol _ _ _ IHHtr _ Hsent).
      + apply initial_message_is_protocol.
        right. apply Htrm.
        split.
        * apply Exists_app. right;apply Exists_cons. left;reflexivity.
        * intro Hsent;destruct Hnot_sent.
          unfold trace_has_message in Hsent.
          rewrite Exists_app, Exists_cons, Exists_nil in Hsent.
          destruct Hsent as [Hsent|[[=->]|[]]];[assumption|exfalso].
          apply Hno_resend in Hx as Hx'.
          apply (proj2 Hx');clear Hx'.
          rewrite (has_been_received_step_update Hx).
          left;reflexivity.
  Qed.

  Lemma lift_preloaded_state_to_seeded
    (P : message -> Prop)
    (s: state)
    (Hequiv_s: state_received_not_sent_invariant s P)
    (Hs: protocol_state_prop PreX s)
    : protocol_state_prop (pre_loaded_vlsm X P) s.
  Proof.
    apply protocol_state_has_trace in Hs as Htr.
    destruct Htr as [is [tr Htr]].
    specialize (lift_preloaded_trace_to_seeded P tr) as Hlift.
    spec Hlift.
    { revert Hequiv_s.
      apply state_received_not_sent_invariant_trace_iff with is; assumption.
    }
    specialize (Hlift _ (ptrace_forget_last Htr)).
    apply proj1 in Hlift.
    apply finite_ptrace_last_pstate in Hlift.
    rewrite <- (ptrace_get_last Htr). assumption.
  Qed.

  Lemma lift_generated_to_seeded
    (P : message -> Prop)
    (s : state)
    (Hequiv_s: state_received_not_sent_invariant s P)
    (m : message)
    (Hgen : protocol_generated_prop PreX s m)
    : protocol_generated_prop (pre_loaded_vlsm X P) s m.
  Proof.
    apply non_empty_protocol_trace_from_protocol_generated_prop.
    apply non_empty_protocol_trace_from_protocol_generated_prop in Hgen.
    destruct Hgen as [is [tr [item [Htr Hgen]]]].
    exists is, tr, item. split; [|assumption].
    specialize (lift_preloaded_trace_to_seeded P tr) as Hlift.
    spec Hlift.
    { revert Hequiv_s.
      apply state_received_not_sent_invariant_trace_iff with is.
      apply ptrace_add_last. assumption.
      apply last_error_destination_last.
      destruct Hgen as [Hlst [Hs _]]. rewrite Hlst. subst. reflexivity.
    }
    apply Hlift. assumption.
  Qed.

End cannot_resend_message.

Section full_node_constraint.

  Context {message : Type}
          `{EqDecision message}
          {index : Type}
          {IndEqDec : EqDecision index}
          (IM : index -> VLSM message)
          {i0 : Inhabited index}
          (X := free_composite_vlsm IM)
          (has_been_sent_capabilities : forall i : index, (has_been_sent_capability (IM i)))
          (has_been_received_capabilities : forall i : index, (has_been_received_capability (IM i)))
          {index_listing : list index}
          (finite_index : Listing index_listing)
          (X_has_been_sent_capability : has_been_sent_capability X := composite_has_been_sent_capability IM (free_constraint IM) finite_index has_been_sent_capabilities)
          (X_has_been_received_capability : has_been_received_capability X := composite_has_been_received_capability IM (free_constraint IM) finite_index has_been_received_capabilities)
          (X_has_been_observed_capability : has_been_observed_capability X := has_been_observed_capability_from_sent_received X)
          (admissible_index : composite_state IM -> index -> Prop)
          (** admissible equivocator index: this index can equivocate from given state *)
          .

  Existing Instance X_has_been_observed_capability.
  Existing Instance X_has_been_sent_capability.

  (**
  Given a composite state @s@, a message @m@, and a node index @i@
  if there is a machine we say that message @m@ can be
  [node_generated_without_further_equivocation] by node @i@ if the message
  can be produced by node @i@ pre_loaded with all messages in a trace in which
  all message equivocation is done through messages causing
  [no_additional_equivocations] to state @s@
  (message [has_been_observed] in @s@ or it has the [initial_message_prop]erty).
  *)
  Definition node_generated_without_further_equivocation
    (s : composite_state IM)
    (m : message)
    (i : index)
    : Prop
    := exists (si : vstate (IM i)),
      protocol_generated_prop (pre_loaded_with_all_messages_vlsm (IM i)) si m /\
      state_received_not_sent_invariant (IM i) si (no_additional_equivocations X s).

  (**
  Similar to the condition above, but now the message is required to be
  generated by the machine pre-loaded only with messages causing
  [no_additional_equivocations] to state @s@.
  *)
  Definition node_generated_without_further_equivocation_alt
    (s : composite_state IM)
    (m : message)
    (i : index)
    : Prop
    := can_emit (pre_loaded_vlsm (IM i) (no_additional_equivocations X s)) m.

  (**
  The equivocation-based abstract definition of the full node condition
  stipulates that a message can be received in a state @s@ if either it causes
  [no_additional_equivocations] to state @s@, or it can be
  [node_generated_without_further_equivocation] by an admissible node.
  *)
  Definition full_node_condition_for_admissible_equivocators
    (l : composite_label IM)
    (som : composite_state IM * option message)
    : Prop
    :=
    no_additional_equivocations_constraint X l som \/
    let (s, om) := som in
      exists m, om = Some m /\
      exists (i : index), admissible_index s i /\
      node_generated_without_further_equivocation s m i.

  (**
  Similar to the condition above, but using the
  [node_generated_without_further_equivocation_alt] property.
  *)
  Definition full_node_condition_for_admissible_equivocators_alt
    (l : composite_label IM)
    (som : composite_state IM * option message)
    : Prop
    :=
    no_additional_equivocations_constraint X l som \/
    let (s, om) := som in
      exists m, om = Some m /\
      exists (i : index), admissible_index s i /\
      node_generated_without_further_equivocation_alt s m i.

  (**
  We here show that if a machine has the [cannot_resend_message_stepwise_prop]erty,
  then the [node_generated_without_further_equivocation] property is stronger
  than the [node_generated_without_further_equivocation_alt] property.
  *)
  Lemma node_generated_without_further_equivocation_alt_iff
    (i : index)
    (Hno_resend : cannot_resend_message_stepwise_prop (IM i))
    (s: composite_state IM)
    (Hs: protocol_state_prop
       (pre_loaded_with_all_messages_vlsm (free_composite_vlsm IM)) s)
    (m : message)
    (Hsmi : node_generated_without_further_equivocation s m i)
    : node_generated_without_further_equivocation_alt s m i.
  Proof.
    destruct Hsmi as [si [Hsim Hsi]].
    apply can_emit_iff. exists si.
    revert Hsim.
    apply lift_generated_to_seeded with (has_been_sent_capabilities i)  (has_been_received_capabilities i)
    ; assumption.
  Qed.

  (** if all machines satisty the [cannot_resend_message_stepwise_prop]erty,
  then the [full_node_condition_for_admissible_equivocators] is stronger than
  the [full_node_condition_for_admissible_equivocators_alt].
  *)
  Lemma full_node_condition_for_admissible_equivocators_subsumption
    (Hno_resend : forall i : index, cannot_resend_message_stepwise_prop (IM i))
    : preloaded_constraint_subsumption IM
        full_node_condition_for_admissible_equivocators
        full_node_condition_for_admissible_equivocators_alt.
  Proof.
    intros s Hs l om [Hno_equiv | Hfull]; [left; assumption|].
    right.
    destruct Hfull as [m [Hom [i [Hi Hfull]]]].
    subst om. exists m. split; [reflexivity|].
    exists i. split; [assumption|].
    specialize (Hno_resend i).
    apply node_generated_without_further_equivocation_alt_iff
    ; assumption.
  Qed.

End full_node_constraint.

Section seeded_composite_vlsm_no_equivocation.

(** ** Pre-loading a VLSM composition with no equivocations constraint

When adding initial messages to a VLSM composition with a no equivocation
constraint, we cannot simply use the [pre_loaded_vlsm] construct
because the no-equivocation constraint must also be altered to reflect that
the newly added initial messages are safe to be received at all times.
*)

  Context
    {message : Type}
    {index : Type}
    {IndEqDec : EqDecision index}
    (IM : index -> VLSM message)
    {i0 : Inhabited index}
    (constraint : composite_label IM -> composite_state IM  * option message -> Prop)
    (X := free_composite_vlsm IM)
    (has_been_sent_capabilities : forall i : index, (has_been_sent_capability (IM i)))
    (has_been_received_capabilities : forall i : index, (has_been_received_capability (IM i)))
    {index_listing : list index}
    (finite_index : Listing index_listing)
    (X_has_been_sent_capability : has_been_sent_capability X := composite_has_been_sent_capability IM (free_constraint IM) finite_index has_been_sent_capabilities)
    .

  Existing Instance X_has_been_sent_capability.

  Section seeded_composite_vlsm_no_equivocation_definition.

    Context
      (seed : message -> Prop)
      .

    (** Constraint is updated to also allow seeded messages. *)

    Definition no_equivocations_additional_constraint_with_pre_loaded
      (l : composite_label IM)
      (som : composite_state IM * option message)
      (initial_or_seed := fun m => vinitial_message_prop X m \/ seed m)
      :=
      no_equivocations_except_from X initial_or_seed l som
      /\ constraint l som.

    Definition composite_no_equivocation_vlsm_with_pre_loaded
      : VLSM message
      :=
      pre_loaded_vlsm (composite_vlsm IM no_equivocations_additional_constraint_with_pre_loaded) seed.

    Lemma seeded_equivocators_incl_preloaded
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
    no_equivocations X l som
    /\ constraint l som.

  Context
    (SeededNoeqvFalse := composite_no_equivocation_vlsm_with_pre_loaded (fun m => False))
    (Noeqv := composite_vlsm IM no_equivocations_additional_constraint)
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
      unfold no_equivocations_additional_constraint.
      unfold no_equivocations.
      unfold no_equivocations_except_from.
      destruct som as (s, [m|]); [|exact id].
      rewrite <- or_assoc.
      intros [[H|contra] Hc]; [|contradiction].
      split; assumption.
    - specialize
        (Hincl
          no_equivocations_additional_constraint
          (no_equivocations_additional_constraint_with_pre_loaded (fun _ : message => False))
        ).
      apply Hincl.
      intros l som. unfold no_equivocations_additional_constraint_with_pre_loaded.
      clear -l.
      unfold no_equivocations_additional_constraint.
      unfold no_equivocations.
      unfold no_equivocations_except_from.
      destruct som as (s, [m|]); [|exact id].
      rewrite <- or_assoc.
      intros [H Hc].
      split; [|assumption].
      left. assumption.
  Qed.

End seeded_composite_vlsm_no_equivocation.

Section has_been_sent_irrelevance.

(**
  As we have several ways of obtaining the 'has_been_sent' property, we need to
  sometime show that they are equivalent.
*)

  Context
    {message : Type}
    (X : VLSM message)
    (Hbs1 : has_been_sent_capability X)
    (Hbs2 : has_been_sent_capability X)
    (has_been_sent1 := @has_been_sent _ X Hbs1)
    (has_been_sent2 := @has_been_sent _ X Hbs2)
    .

  Lemma has_been_sent_irrelevance
    (s : state)
    (m : message)
    (Hs : protocol_state_prop (pre_loaded_with_all_messages_vlsm X) s)
    : has_been_sent1 s m -> has_been_sent2 s m.
  Proof.
    intro H.
    apply proper_sent in H; [|assumption].
    apply proper_sent; [assumption|].
    assumption.
  Qed.

End has_been_sent_irrelevance.
