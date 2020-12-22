Require Import List Streams ProofIrrelevance Coq.Arith.Plus Coq.Arith.Minus Coq.Logic.FinFun Coq.Reals.Reals.
Import ListNotations.

From CasperCBC
Require Import Lib.Preamble Lib.ListExtras VLSM.Common VLSM.Composition VLSM.ProjectionTraces CBC.Common CBC.Equivocation.

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

(**
*** Summary
This chapter is dedicated to building the language for discussing equivocation.
    Equivocation occurs on the receipt of a message which has not been previously sent.
    The designated sender (validator) of the message is then said to be equivocating.
    Our main purpose is to keep track of equivocating senders in a composite context
    and limit equivocation by means of a composition constraint.
**)

(** **)

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

(** We begin with a basic utility function. **)

    Definition trace_has_message
      (message_selector : message -> transition_item -> Prop)
      (msg : message)
      (tr : list (vtransition_item vlsm))
      : Prop
      := List.Exists (message_selector msg) tr.

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
      (Htr : finite_protocol_trace X start tr)
      (Hlast : last (List.map destination tr) start = s),
      List.Exists (message_selector m) tr.

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
      (Htr : finite_protocol_trace X start tr)
      (Hlast : last (List.map destination tr) start = s),
      List.Exists (message_selector m) tr.

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
      (Htr : finite_protocol_trace X start tr)
      (Hlast : last (List.map destination tr) start = s),
      ~List.Exists (message_selector m) tr.

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
        intros is tr Htr Hlast Hsend.
        apply Hnot.
        exists is, tr, Htr, Hlast. exact Hsend.
      - intros Hno [is [tr [Htr [Hlast Hsend]]]].
        exact (Hno is tr Htr Hlast Hsend).
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
      (Htr : finite_protocol_trace_from X start tr)
      (Hlast : last (List.map destination tr) start = s)
      (Hsome : List.Exists (message_selector m) tr)
      : specialized_selected_message_exists_in_some_traces X message_selector s m.
    Proof.
      apply finite_ptrace_first_pstate in Htr as Hstart.
      destruct Hstart as [_om Hstart].
      apply (protocol_is_trace X) in Hstart as Htr_start.
      destruct Htr_start as [Hinit| Htr_start].
      - exists start. exists tr. exists (conj Htr Hinit). exists Hlast. assumption.
      - destruct Htr_start as [is_start [tr_start [Htr_start [Heqstart Hout]]]].
        apply last_error_destination_last with (default := is_start) in Heqstart.
        exists is_start. exists (tr_start ++ tr).
        destruct Htr_start as [Htr_start His_start].
        split.
        + split; [|assumption]. subst s. subst start.
          apply finite_protocol_trace_from_app_iff.
          split; assumption.
        + rewrite map_app. rewrite last_app. rewrite Heqstart.
          exists Hlast.
          rewrite Exists_app. right. assumption.
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
      assert (Hps : protocol_state_prop pre_vlsm s).
      { replace s with (proj1_sig (exist _ s Hs)); try reflexivity.
        exists None. apply (protocol_initial_state pre_vlsm).
      }
      assert (Htr : finite_protocol_trace pre_vlsm s []).
      { split; try assumption. constructor. assumption. }
      specialize (Hselected s [] Htr eq_refl).
      apply Exists_exists in Hselected.
      destruct Hselected as [x [Hx _]].
      contradiction Hx.
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

    Definition field_selector [T: VLSM_type message]
               (field: transition_item (T:=T) -> option message) :
      (message -> transition_item -> Prop) :=
      fun m item => field item = Some m.

    Definition item_sends_or_receives {T: VLSM_type message}:
      message -> transition_item (T:=T) -> Prop :=
      fun m item => input item = Some m \/ output item = Some m.

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
      destruct Hs as [om Hs].
      apply protocol_is_trace in Hs.
      destruct Hs as [Hinit | [is [tr [Htr [Hlast _]]]]]
      ; [elim (selected_message_exists_in_all_traces_initial_state s Hinit selector m); assumption|].
      exists is. exists tr. exists Htr.
      assert (Hlst := last_error_destination_last _ _ Hlast is).
      exists Hlst.
      apply (Hall _ _ Htr Hlst).
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
        destruct Hsome as [is [tr [Htr [Hlast Hsome]]]].
        elim (Hsm _ _ Htr Hlast).
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
      exists is. exists tr.
      split; [|assumption].
      destruct Htr as [Htr Hinit].
      split; [|assumption].
      apply (VLSM_incl_finite_trace (machine vlsm) (machine pre_vlsm)).
      - apply vlsm_incl_pre_loaded_with_all_messages_vlsm.
      - clear -Htr.
        simpl in *. destruct vlsm. destruct s. simpl. assumption.
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
      destruct Htr as [Htr Hinit].
      split; [|assumption].
      apply (VLSM_incl_finite_trace (machine vlsm) (machine pre_vlsm)).
      - apply vlsm_incl_pre_loaded_with_all_messages_vlsm.
      - clear -Htr.
        simpl in *. destruct vlsm. destruct s. simpl. assumption.
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
      oracle on its arguments and we simply forbid them **)

      Definition equivocation
      {Hbs : has_been_sent_capability}
      (m : message)
      (s : state)
      : Prop
      :=
      has_not_been_sent s m.
   
     Definition no_equivocations
       {Hbs : has_been_sent_capability}
       (l : vlabel vlsm)
       (som : state * option message)
       : Prop
       :=
       let (s, om) := som in
       match om with
       | None => True
       | Some m => has_been_sent s m
       end.
   
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
        destruct Hsome as [is [tr [Htr [Hlast Hsome]]]].
        elim (Hsm _ _ Htr Hlast).
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
      - intros Hsm is tr Htr Hlast Hsome.
        assert (Hsm' : selected_message_exists_in_some_preloaded_traces (field_selector input) s m)
          by (exists is; exists tr; exists Htr; exists Hlast; assumption).
        apply Hconsistency in Hsm'.
        apply proper_received in Hsm'. contradiction.
      - intro Hnone. destruct (decide (has_been_received s m)) as [Hsm|Hsm];[|assumption].
        exfalso.
        apply proper_received in Hsm. apply Hconsistency in Hsm.
        destruct Hsm as [is [tr [Htr [Hlast Hsm]]]].
        elim (Hnone is tr Htr Hlast). assumption.
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
      assert (Hps : protocol_state_prop pre_vlsm (proj1_sig s)).
      { exists None. apply (@protocol_initial_state _ pre_vlsm). }
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
        { intros Hno is tr Htr Hlast Hexists.
          contradict Hno;exists is, tr, Htr,Hlast;assumption.
        }
        contradict Hin.
        apply sent_messages_full;[assumption|].
        exists (exist _ m Hin).
        reflexivity.
      - intros Htrace Hin.
        apply sent_messages_full in Hin;[|assumption].
        destruct Hin as [[m0 Hm] Heq];simpl in Heq;subst m0.
        destruct Hm as [is [tr [Htr [Hlast Hex]]]].
        apply (Htrace is tr Htr Hlast Hex).
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
      assert (Hps : protocol_state_prop pre_vlsm (proj1_sig s)).
      { exists None. apply (@protocol_initial_state _ pre_vlsm). }
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

Arguments field_selector [message] [T] field msg item /.
Arguments item_sends_or_receives {message} {T} msg item /.

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

  Local Lemma H_partial_trace_prop
        s0 s tr
        (Htr: finite_protocol_trace_from (pre_loaded_with_all_messages_vlsm vlsm) s0 tr)
        (Hlast: last (List.map Common.destination tr) s0 = s):
    forall m,
      oracle s m
      <-> (List.Exists (selector m) tr \/ oracle s0 m).
  Proof.
    induction Htr.
    - simpl in Hlast; subst s.
      intro m.
      rewrite Exists_nil.
      tauto.
    - simpl List.map in Hlast.
      rewrite unroll_last in Hlast.
      specialize (IHHtr Hlast);clear Hlast.
      intro m.
      specialize (IHHtr m).
      rewrite Exists_cons. simpl.
      apply (oracle_props.(oracle_step_update _ _)) with (msg:=m) in H.
      tauto.
  Qed.

  Local Lemma H_protocol_trace_prop
        [s0 tr]
        (Htr: finite_protocol_trace (pre_loaded_with_all_messages_vlsm vlsm) s0 tr)
        [s]
        (Hlast: last (List.map Common.destination tr) s0 = s):
    forall m,
      oracle s m <-> List.Exists (selector m) tr.
  Proof.
    intro m.
    destruct Htr as [Htr Hinit].
     rewrite (H_partial_trace_prop _ _ _ Htr Hlast).
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
    - intros Hsent s0 tr Htr Hlast.
      apply (H_protocol_trace_prop Htr Hlast).
      assumption.
    - intro H_all_traces.
      apply protocol_state_has_trace in Hproto.
      destruct Hproto as [s0 [tr [Htr Hlast]]].
      apply (H_protocol_trace_prop Htr Hlast).
      specialize (H_all_traces s0 tr Htr Hlast).
      assumption.
  Qed.

  Lemma prove_none_have_message_from_stepwise:
    forall (s : state)
           (Hs : protocol_state_prop (pre_loaded_with_all_messages_vlsm vlsm) s)
           (m : message),
      no_traces_have_message_prop vlsm selector (fun m s => ~oracle m s) s m.
  Proof.
    intros s Hproto m.
    pose proof (H_protocol_trace_prop).
    split.
    - intros H_not_sent start tr Htr Hlast.
      contradict H_not_sent.
      apply (H_protocol_trace_prop Htr Hlast).
      assumption.
    - intros H_no_traces.
      apply protocol_state_has_trace in Hproto.
      destruct Hproto as [s0 [tr [Htr Hlast]]].
      specialize (H_no_traces s0 tr Htr Hlast).
      contradict H_no_traces.
      apply (H_protocol_trace_prop Htr Hlast).
      assumption.
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
    eapply Exists_nil;refine (Horacle _ (eq_refl _));clear Horacle.
    split;[|assumption].
    constructor;assumption.
  Qed.

  Lemma examine_one_trace:
    forall is s tr,
      last (List.map destination tr) is = s ->
      finite_protocol_trace (pre_loaded_with_all_messages_vlsm vlsm) is tr ->
    forall m,
      oracle s m <->
      List.Exists (selector m) tr.
  Proof.
    intros is s tr Hlast Htr m.
    assert (protocol_state_prop (pre_loaded_with_all_messages_vlsm vlsm) s)
      by (rewrite <- Hlast; apply trace_is_protocol;assumption).
    split.
    - intros Horacle.
      apply Horacle_all_have in Horacle;[|assumption].
      specialize (Horacle is tr Htr Hlast).
      assumption.
    - intro Hexists.
      apply dec_stable.
      intro Hnot.
      apply Hnot_oracle_none_have in Hnot;[|assumption].
      rewrite <- selected_message_exists_preloaded_not_some_iff_no in Hnot.
      apply Hnot.
      exists is, tr, Htr, Hlast.
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
      as [is [tr [[Htr Hinit] Hlast]]].

    rewrite <- Hlast in Htrans'.
    pose proof (Htr' := extend_right_finite_trace_from _ _ _ Htr _ _ _ _ Htrans').

    match type of Htr' with (finite_protocol_trace_from _ _ ?tr') =>
                            assert (last (List.map destination tr') is = s') as Hlast'
    end.
    {
      rewrite map_app.
      simpl List.map.
      rewrite last_is_last.
      reflexivity.
    }

    rewrite (examine_one_trace is s tr Hlast (conj Htr Hinit) msg).
    rewrite (examine_one_trace is s' _ Hlast' (conj Htr' Hinit) msg).
    clear.
    progress cbn.
    rewrite Exists_app, Exists_cons, Exists_nil.
    simpl.
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
      `(Hhbs: has_been_sent_capability message vlsm):
  forall l s im s' om,
    protocol_transition (pre_loaded_with_all_messages_vlsm vlsm) l (s,im) (s',om) ->
    forall m,
      has_been_sent vlsm s' m <-> (om = Some m \/ has_been_sent vlsm s m).
Proof.
  exact (oracle_step_update _ _ (has_been_sent_stepwise_from_trace Hhbs)).
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
  := oracle_step_update _ _ has_been_observed_stepwise_props.

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
          (i0 : index)
          (constraint : composite_label IM -> composite_state IM  * option message -> Prop)
          (X := composite_vlsm IM i0 constraint)
          {index_listing : list index}
          (finite_index : Listing index_listing)
          (has_been_sent_capabilities : forall i : index, (has_been_sent_capability (IM i)))
          .

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

  (** 'composite_has_been_sent' has the 'proper_sent' property. *)
  Lemma composite_proper_sent
    (s : vstate X)
    (Hs : protocol_state_prop (pre_loaded_with_all_messages_vlsm X) s)
    (m : message)
    : has_been_sent_prop X composite_has_been_sent s m.
  Proof.
    split.
    - intros Hcomposite is tr Htr Hlast.
      destruct Hcomposite as [i Hbsi].
      destruct Hs as [_om Hs].
      apply constraint_subsumption_preloaded_protocol_prop
        with (constraint2 := free_constraint IM) in Hs
      ; [|firstorder].
      apply proper_sent in Hbsi
      ; [|apply (preloaded_composed_protocol_state IM i0); exists _om; assumption ].
      specialize (Hbsi (is i) (finite_trace_projection_list IM i0 constraint i tr) ).
      destruct Htr as [Htr His].
      spec Hbsi.
      {
        specialize (His i).
        split; [|assumption].
        apply
          (preloaded_finite_ptrace_projection IM i0 constraint i); [|assumption].
        apply initial_is_protocol. assumption.
      }
      spec Hbsi.
      {
        subst.
        apply (preloaded_finite_trace_projection_last_state IM i0 constraint i).
        assumption.
      }
      apply Exists_exists. apply Exists_exists in Hbsi.
      destruct Hbsi as [itemi [Hitemi Hout]].
      apply (finite_trace_projection_list_in_rev IM i0 constraint) in Hitemi.
      destruct Hitemi as [itemX [Houtput [Hinput [Hl1 [Hl2 [Hdestination HitemX]]]]]].
      exists itemX. split; [assumption|]. simpl in *. congruence.
    - intro Hall.
      destruct Hs as [_om Hs].
      apply protocol_is_trace in Hs as Htr.
      destruct Htr as [Hinit | [is [tr [Htr [Hlast _]]]]]
      ; [
        elim (selected_message_exists_in_all_traces_initial_state X s Hinit (field_selector output) m)
        ; assumption|].
      specialize (Hall is tr Htr).
      apply last_error_destination_last with (default := is) in Hlast.
      spec Hall Hlast.
      apply Exists_exists in Hall.
      destruct Hall as [itemX [HitemX Hout]].
      exists (projT1 (l itemX)).
      assert
        (Hsj : protocol_state_prop
          (pre_loaded_with_all_messages_vlsm (IM (projT1 (l itemX))))
          (s (projT1 (l itemX))))
      ; [| apply proper_sent; [assumption|]].
      + apply (preloaded_composed_protocol_state IM i0).
        exists _om.
        apply (constraint_subsumption_preloaded_protocol_prop IM i0 constraint (free_constraint IM))
        ; [intro; intros; exact I|].
        assumption.
      + apply has_been_sent_consistency
        ; [apply has_been_sent_capabilities|assumption|].
        exists (is (projT1 (l itemX))).
        exists (finite_trace_projection_list IM i0 constraint (projT1 (l itemX)) tr).
        assert
          (Hisj : protocol_state_prop
            (pre_loaded_with_all_messages_vlsm (IM (projT1 (l itemX))))
            (is (projT1 (l itemX))))
          by (apply initial_is_protocol; apply (proj2 Htr (projT1 (l itemX)))).
        specialize
          (preloaded_finite_ptrace_projection IM i0 constraint (projT1 (l itemX)) is
            Hisj tr (proj1 Htr)
          ) as Htrj.
        exists (conj Htrj (proj2 Htr (projT1 (l itemX)))).
        specialize
          (preloaded_finite_trace_projection_last_state IM i0 constraint
            (projT1 (l itemX)) is tr (proj1 Htr)) as Hlst.
        simpl in Hlst. subst s. exists Hlst.
        apply Exists_exists.
        specialize (finite_trace_projection_list_in IM i0 constraint _ _ HitemX)
          as Hitemj.
        simpl in Hitemj.
        exists ({|
        l := projT2 (l itemX);
        input := input itemX;
        destination := destination itemX (projT1 (l itemX));
        output := output itemX |}).
        split; assumption.
  Qed.

  (** 'composite_has_been_sent' has the consistency property for 'output' messages. *)
  Lemma composite_output_consistency
    (s : vstate X)
    (Hs : protocol_state_prop (pre_loaded_with_all_messages_vlsm X) s)
    (m : message)
    : selected_messages_consistency_prop X (field_selector output) s m.
  Proof.
    split.
    - intros Hsome is. intros.
      destruct Hsome as [is0 [tr0 [Htr0 [Hlst0 Hsome]]]].
      apply Exists_exists in Hsome.
      destruct Hsome as [item0 [Hitem0 Houtput0]].
      pose (projT1 (l item0)) as j.
      assert (Hsomej : selected_message_exists_in_some_preloaded_traces (IM j) (field_selector output) (s j) m).
      { exists (is0 j).
        exists (finite_trace_projection_list IM i0 constraint j tr0).
        assert
          (His0j : protocol_state_prop
            (pre_loaded_with_all_messages_vlsm (IM j))
            (is0 j))
          by (apply initial_is_protocol; apply (proj2 Htr0 j)).
        specialize
          (preloaded_finite_ptrace_projection IM i0 constraint j is0
            His0j tr0 (proj1 Htr0)
          ) as Htr0j.
        exists (conj Htr0j (proj2 Htr0 j)).
        specialize
          (preloaded_finite_trace_projection_last_state IM i0 constraint
            j is0 tr0 (proj1 Htr0)) as Hlst0'.
        simpl in Hlst0. rewrite <- Hlst0. exists Hlst0'.
        apply Exists_exists.
        specialize
          (finite_trace_projection_list_in IM i0 constraint _ _ Hitem0) as Hitem0j.
        simpl in Hitem0j.
        exists {|
        l := projT2 (l item0);
        input := input item0;
        destination := destination item0 (projT1 (l item0));
        output := output item0 |}.
        split; assumption.
      }
      assert
        (Hisj : protocol_state_prop
          (pre_loaded_with_all_messages_vlsm (IM j))
          (is j))
        by (apply initial_is_protocol; apply (proj2 Htr j)).
      specialize
        (preloaded_finite_ptrace_projection IM i0 constraint j is
          Hisj tr (proj1 Htr)
        ) as Htrj.
      specialize
          (preloaded_finite_trace_projection_last_state IM i0 constraint
            j is tr (proj1 Htr)) as Hlst.
      apply has_been_sent_consistency in Hsomej.
      + spec Hsomej (is j) (finite_trace_projection_list IM i0 constraint j tr).
        specialize (Hsomej (conj Htrj (proj2 Htr j))).
        simpl in Hlst. rewrite <- Hlast in Hsomej. specialize (Hsomej Hlst).
        apply Exists_exists in Hsomej.
        destruct Hsomej as [itemj [Hitemj Hout]].
        apply (finite_trace_projection_list_in_rev IM i0 constraint) in Hitemj.
        destruct Hitemj as [item [Houtput [_ [_ [_ [_ HitemX]]]]]].
        apply Exists_exists. exists item.
        split; [assumption|].
        simpl in *.
        congruence.
      + apply has_been_sent_capabilities.
      + apply finite_ptrace_last_pstate in Htrj as Hsj.
        simpl in *. rewrite Hlst in Hsj.
        rewrite <- Hlast.
        assumption.
    - apply consistency_from_protocol_proj2.
      assumption.
  Qed.

  (** The negation of 'composite_has_been_sent' has the 'proper_not_sent' property.*)
  Lemma composite_proper_not_sent
    (s: vstate X)
    (Hs: protocol_state_prop (pre_loaded_with_all_messages_vlsm X) s)
    (m: message)
    : has_not_been_sent_prop X
      (fun (s0 : vstate X) (m0 : message) => ~ composite_has_been_sent s0 m0) s m.
  Proof.
    apply has_been_sent_consistency_proper_not_sent.
    - apply composite_has_been_sent_dec.
    - apply composite_proper_sent. assumption.
    - apply composite_output_consistency. assumption.
  Qed.

  Global Instance composite_has_been_sent_capability : has_been_sent_capability X
    :=
    { has_been_sent := composite_has_been_sent
    ; has_been_sent_dec := composite_has_been_sent_dec
    ; proper_sent := composite_proper_sent
    ; proper_not_sent := composite_proper_not_sent
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
    can_emit (composite_vlsm_constrained_projection IM i0 constraint i) m /\
    forall (j : index)
           (Hdif : i <> j),
           ~can_emit (composite_vlsm_constrained_projection IM i0 constraint j) m.

   (** An alternative, possibly friendlier, formulation. Note that it is
       slightly weaker, in that it does not require that the sender
       is able to send the message. **)

  Definition sender_safety_alt_prop : Prop :=
    forall
    (i : index)
    (m : message)
    (v : validator)
    (Hsender : sender m = Some v),
    can_emit (composite_vlsm_constrained_projection IM i0 constraint i) m ->
    A v = i.

  Definition sender_weak_nontriviality_prop : Prop :=
    forall (v : validator),
    exists (m : message),
    can_emit (composite_vlsm_constrained_projection IM i0 constraint (A v)) m /\
    sender m = Some v.

  Definition sender_strong_nontriviality_prop : Prop :=
    forall (v : validator),
    forall (m : message),
    can_emit (composite_vlsm_constrained_projection IM i0 constraint (A v)) m ->
    sender m = Some v.

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

End Composite.
