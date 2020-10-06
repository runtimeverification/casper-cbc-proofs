Require Import List Streams ProofIrrelevance Coq.Arith.Plus Coq.Arith.Minus Coq.Logic.FinFun Coq.Reals.Reals.
Import ListNotations.

From CasperCBC
Require Import Lib.Preamble Lib.ListExtras VLSM.Common VLSM.Composition CBC.Common CBC.Equivocation.

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
      (message_selector : transition_item -> option message)
      (msg : message)
      (tr : list (vtransition_item vlsm))
      : Prop
      := List.Exists (fun item => message_selector item = Some msg) tr.

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
      := vstate vlsm -> message -> bool.

    Definition selected_message_exists_in_all_traces
      (message_selector : transition_item -> option message)
      (s : state)
      (m : message)
      : Prop
      :=
      forall
      (start : state)
      (tr : list transition_item)
      (Htr : finite_protocol_trace pre_vlsm start tr)
      (Hlast : last (List.map destination tr) start = s),
      List.Exists (fun (elem : transition_item) => message_selector elem = Some m) tr.

    Definition selected_message_exists_in_some_traces
      (message_selector : transition_item -> option message)
      (s : state)
      (m : message)
      : Prop
      :=
      exists
      (start : state)
      (tr : list transition_item)
      (Htr : finite_protocol_trace pre_vlsm start tr)
      (Hlast : last (List.map destination tr) start = s),
      List.Exists (fun (elem : transition_item) => message_selector elem = Some m) tr.

    Definition selected_message_exists_in_no_trace
      (message_selector : transition_item -> option message)
      (s : state)
      (m : message)
      : Prop
      :=
      forall
      (start : state)
      (tr : list transition_item)
      (Htr : finite_protocol_trace pre_vlsm start tr)
      (Hlast : last (List.map destination tr) start = s),
      ~List.Exists (fun (elem : transition_item) => message_selector elem = Some m) tr.

    Definition selected_messages_consistency_prop
      (message_selector : transition_item -> option message)
      (s : vstate vlsm)
      (m : message)
      : Prop
      :=
      selected_message_exists_in_some_traces message_selector s m
      <-> selected_message_exists_in_all_traces message_selector s m.

    Lemma selected_message_exists_in_all_traces_initial_state
      (s : vstate vlsm)
      (Hs : vinitial_state_prop vlsm s)
      (selector : transition_item -> option message)
      (m : message)
      : ~ selected_message_exists_in_all_traces selector s m.
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
      (message_selector : transition_item -> option message)
      (oracle : state_message_oracle)
      (s : state)
      (m : message)
      : Prop
      :=
      oracle s m = true <-> selected_message_exists_in_all_traces message_selector s m.

    Definition no_traces_have_message_prop
      (message_selector : transition_item -> option message)
      (oracle : state_message_oracle)
      (s : state)
      (m : message)
      : Prop
      :=
      oracle s m = true <-> selected_message_exists_in_no_trace message_selector s m.

    Definition has_been_sent_prop : state_message_oracle -> state -> message -> Prop
      := (all_traces_have_message_prop output).

    Definition has_not_been_sent_prop : state_message_oracle -> state -> message -> Prop
      := (no_traces_have_message_prop output).

    Definition has_been_received_prop : state_message_oracle -> state -> message -> Prop
      := (all_traces_have_message_prop input).

    Definition has_not_been_received_prop : state_message_oracle -> state -> message -> Prop
      := (no_traces_have_message_prop input).

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

      proper_sent:
        forall (s : state)
               (Hs : protocol_state_prop pre_vlsm s)
               (m : message),
               (has_been_sent_prop has_been_sent s m);

      has_not_been_sent: state_message_oracle
        := fun (s : state) (m : message) => negb (has_been_sent s m);

      proper_not_sent:
        forall (s : state)
               (Hs : protocol_state_prop pre_vlsm s)
               (m : message),
               has_not_been_sent_prop has_not_been_sent s m;
    }.

    Lemma has_been_sent_consistency
      {Hbs : has_been_sent_capability}
      (s : state)
      (Hs : protocol_state_prop pre_vlsm s)
      (m : message)
      : selected_messages_consistency_prop output s m.
    Proof.
      split.
      - intro Hsome.
        destruct (has_been_sent s m) eqn:Hsm
        ; try (apply proper_sent in Hsm; assumption).
        apply Bool.negb_true_iff in Hsm.
        apply proper_not_sent in Hsm; try assumption.
        destruct Hsome as [is [tr [Htr [Hlast Hsome]]]].
        elim (Hsm _ _ Htr Hlast).
        assumption.
      - intro Hall.
        destruct Hs as [om Hs].
        apply protocol_is_trace in Hs.
        destruct Hs as [Hinit | [is [tr [Htr [Hlast _]]]]]
        ; try
          (elim (selected_message_exists_in_all_traces_initial_state s Hinit output m)
          ; assumption).
        exists is. exists tr. exists Htr.
        assert (Hlst := last_error_destination_last _ _ Hlast is).
        exists Hlst.
        apply (Hall _ _ Htr Hlst).
    Qed.

    Lemma has_been_sent_consistency_proper_not_sent
      (has_been_sent: state_message_oracle)
      (s : state)
      (m : message)
      (proper_sent: has_been_sent_prop has_been_sent s m)
      (has_not_been_sent
        := fun (s : state) (m : message) => negb (has_been_sent s m))
      (Hconsistency : selected_messages_consistency_prop output s m)
      : has_not_been_sent_prop has_not_been_sent s m.
    Proof.
      unfold has_not_been_sent_prop.
      unfold no_traces_have_message_prop.
      unfold has_not_been_sent.
      rewrite Bool.negb_true_iff.
      split.
      - intros Hsm is tr Htr Hlast Hsome.
        assert (Hsm' : selected_message_exists_in_some_traces output s m)
          by (exists is; exists tr; exists Htr; exists Hlast; assumption).
        apply Hconsistency in Hsm'.
        apply proper_sent in Hsm'. rewrite Hsm' in Hsm. discriminate Hsm.
      - intro Hnone. destruct (has_been_sent s m) eqn:Hsm; try reflexivity.
        apply proper_sent in Hsm. apply Hconsistency in Hsm.
        destruct Hsm as [is [tr [Htr [Hlast Hsm]]]].
        elim (Hnone is tr Htr Hlast). assumption.
    Qed.

    Class has_been_received_capability := {
      has_been_received: state_message_oracle;

      proper_received:
        forall (s : state)
               (Hs : protocol_state_prop pre_vlsm s)
               (m : message),
               (has_been_received_prop has_been_received s m);

      has_not_been_received: state_message_oracle
        := fun (s : state) (m : message) => negb (has_been_received s m);

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
      : selected_messages_consistency_prop input s m.
    Proof.
      split.
      - intro Hsome.
        destruct (has_been_received s m) eqn:Hsm
        ; try (apply proper_received in Hsm; assumption).
        apply Bool.negb_true_iff in Hsm.
        apply proper_not_received in Hsm; try assumption.
        destruct Hsome as [is [tr [Htr [Hlast Hsome]]]].
        elim (Hsm _ _ Htr Hlast).
        assumption.
      - intro Hall.
        destruct Hs as [om Hs].
        apply protocol_is_trace in Hs.
        destruct Hs as [Hinit | [is [tr [Htr [Hlast _]]]]]
        ; try
          (elim (selected_message_exists_in_all_traces_initial_state s Hinit input m)
          ; assumption).
        exists is. exists tr. exists Htr.
        assert (Hlst := last_error_destination_last _ _ Hlast is).
        exists Hlst.
        apply (Hall _ _ Htr Hlst).
    Qed.

    Lemma has_been_received_consistency_proper_not_received
      (has_been_received: state_message_oracle)
      (s : state)
      (m : message)
      (proper_received: has_been_received_prop has_been_received s m)
      (has_not_been_received
        := fun (s : state) (m : message) => negb (has_been_received s m))
      (Hconsistency : selected_messages_consistency_prop input s m)
      : has_not_been_received_prop has_not_been_received s m.
    Proof.
      unfold has_not_been_received_prop.
      unfold no_traces_have_message_prop.
      unfold has_not_been_received.
      rewrite Bool.negb_true_iff.
      split.
      - intros Hsm is tr Htr Hlast Hsome.
        assert (Hsm' : selected_message_exists_in_some_traces input s m)
          by (exists is; exists tr; exists Htr; exists Hlast; assumption).
        apply Hconsistency in Hsm'.
        apply proper_received in Hsm'. rewrite Hsm' in Hsm. discriminate Hsm.
      - intro Hnone. destruct (has_been_received s m) eqn:Hsm; try reflexivity.
        apply proper_received in Hsm. apply Hconsistency in Hsm.
        destruct Hsm as [is [tr [Htr [Hlast Hsm]]]].
        elim (Hnone is tr Htr Hlast). assumption.
    Qed.

    Definition sent_messages
      (s : vstate vlsm)
      : Type
      :=
      sig (fun m => selected_message_exists_in_some_traces output s m).

    Lemma sent_messages_proper
      (Hhbs : has_been_sent_capability)
      (s : vstate vlsm)
      (Hs : protocol_state_prop pre_vlsm s)
      (m : message)
      : has_been_sent s m = true <-> exists (m' : sent_messages s), proj1_sig m' = m.
    Proof.
      split.
      - specialize (proper_sent s Hs m) as Hbs.
        unfold has_been_sent_prop in Hbs. unfold all_traces_have_message_prop in Hbs.
        intros. apply Hbs in H.
        destruct Hs as [_om Hs].
        specialize (protocol_is_trace pre_vlsm s _om Hs) as Htr.
        unfold sent_messages.
        destruct Htr as [Hinit | Htr].
        + specialize (H s []).
          spec H; repeat (try constructor; try assumption); try exists _om; try assumption.
          specialize (H eq_refl).
          apply Exists_exists in H. destruct H as [x [Hx _]]. inversion Hx.
        + destruct Htr as [is [tr [Htr [Hdest Hout]]]].
          assert (Hm : selected_message_exists_in_some_traces output s m).
          { exists is. exists tr. exists Htr.
            assert (Hlst : last (List.map destination tr) is = s).
            { destruct tr as [|i tr]; inversion Hdest.
              apply last_map.
            }
            exists Hlst.
            specialize (H is tr Htr Hlst).
            assumption.
          }
          exists (exist _ m Hm).
          reflexivity.
      - intros [[m0 Hm0] Hm']. simpl in Hm'. subst m0.
        destruct (has_been_sent s m) eqn:Hbs; try reflexivity.
        specialize (proper_not_sent s Hs m) as Hns.
        unfold has_not_been_sent_prop in Hns. unfold no_traces_have_message_prop in Hns.
        unfold has_not_been_sent in Hns. rewrite Bool.negb_true_iff in Hns.
        apply Hns in Hbs.
        destruct Hm0 as [is [tr [Htr [Hdest Hout]]]].
        specialize (Hbs is tr Htr Hdest).
        elim Hbs. assumption.
    Qed.

    Definition received_messages
      (s : vstate vlsm)
      : Type
      :=
      sig (fun m => selected_message_exists_in_some_traces input s m).

    Lemma received_messages_proper
      (Hhbs : has_been_received_capability)
      (s : vstate vlsm)
      (Hs : protocol_state_prop pre_vlsm s)
      (m : message)
      : has_been_received s m = true <-> exists (m' : received_messages s), proj1_sig m' = m.
    Proof.
      split.
      - specialize (proper_received s Hs m) as Hbs.
        unfold has_been_received_prop in Hbs. unfold all_traces_have_message_prop in Hbs.
        intros. apply Hbs in H.
        destruct Hs as [_om Hs].
        specialize (protocol_is_trace pre_vlsm s _om Hs) as Htr.
        unfold received_messages.
        destruct Htr as [Hinit | Htr].
        + specialize (H s []).
          spec H; repeat (try constructor; try assumption); try exists _om; try assumption.
          specialize (H eq_refl).
          apply Exists_exists in H. destruct H as [x [Hx _]]. inversion Hx.
        + destruct Htr as [is [tr [Htr [Hdest Hout]]]].
          assert (Hm : selected_message_exists_in_some_traces input s m).
          { exists is. exists tr. exists Htr.
            assert (Hlst : last (List.map destination tr) is = s).
            { destruct tr as [|i tr]; inversion Hdest.
              apply last_map.
            }
            exists Hlst.
            specialize (H is tr Htr Hlst).
            assumption.
          }
          exists (exist _ m Hm).
          reflexivity.
      - intros [[m0 Hm0] Hm']. simpl in Hm'. subst m0.
        destruct (has_been_received s m) eqn:Hbs; try reflexivity.
        specialize (proper_not_received s Hs m) as Hns.
        unfold has_not_been_received_prop in Hns. unfold no_traces_have_message_prop in Hns.
        unfold has_not_been_received in Hns. rewrite Bool.negb_true_iff in Hns.
        apply Hns in Hbs.
        destruct Hm0 as [is [tr [Htr [Hdest Hout]]]].
        specialize (Hbs is tr Htr Hdest).
        elim Hbs. assumption.
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
          selected_messages_consistency_prop output s m
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
      specialize (selected_message_exists_in_all_traces_initial_state s Hs output m) as H.
      elim H. assumption.
    Qed.

    Definition computable_sent_messages_has_been_sent
      {Hsm : computable_sent_messages}
      {eq_message : EqDec message}
      (s : vstate vlsm)
      (m : message)
      : bool
      :=
      if inb eq_dec m (sent_messages_fn s) then true else false.

    Lemma computable_sent_messages_has_been_sent_proper
      {Hsm : computable_sent_messages}
      {eq_message : EqDec message}
      (s : state)
      (Hs : protocol_state_prop pre_vlsm s)
      (m : message)
      : has_been_sent_prop computable_sent_messages_has_been_sent s m.
    Proof.
      unfold has_been_sent_prop. unfold all_traces_have_message_prop.
      unfold computable_sent_messages_has_been_sent.
      destruct
        (inb eq_dec m (sent_messages_fn s))
        eqn: Hin; split; intros; try discriminate; try reflexivity
        ; apply in_correct in Hin || apply in_correct' in Hin.
      - apply sent_messages_full in Hin; try assumption.
        destruct Hin as [[m0 Hm0] Hx].
        simpl in Hx. subst m0. apply (sent_messages_consistency s Hs m).
        assumption.
      - elim Hin.
        apply (sent_messages_consistency s Hs m) in H.
        apply sent_messages_full; try assumption.
        exists (exist _ m H). reflexivity.
    Qed.

    Definition computable_sent_messages_has_not_been_sent
      {Hsm : computable_sent_messages}
      {eq_message : EqDec message}
      (s : vstate vlsm)
      (m : message)
      : bool
      :=
      negb (computable_sent_messages_has_been_sent s m).

    Lemma computable_sent_messages_has_not_been_sent_proper
      {Hsm : computable_sent_messages}
      {eq_message : EqDec message}
      (s : state)
      (Hs : protocol_state_prop pre_vlsm s)
      (m : message)
      : has_not_been_sent_prop computable_sent_messages_has_not_been_sent s m.
    Proof.
      unfold has_not_been_sent_prop. unfold no_traces_have_message_prop.
      unfold computable_sent_messages_has_not_been_sent.
      rewrite Bool.negb_true_iff.
      unfold computable_sent_messages_has_been_sent.
      destruct
        (inb eq_dec m (sent_messages_fn s))
        eqn: Hin; split; intros; try discriminate; try reflexivity
        ; apply in_correct in Hin || apply in_correct' in Hin.
      - apply sent_messages_full in Hin; try assumption.
        destruct Hin as [[m0 Hm0] Hx].
        simpl in Hx. subst m0.
        destruct Hm0 as [is [tr [Htr [Hlast Hexists]]]].
        specialize (H is tr Htr Hlast).
        elim H. assumption.
      - intro is; intros. intro HExists. elim Hin. apply sent_messages_full; try assumption.
        assert (Hm : selected_message_exists_in_some_traces output s m).
        { exists is. exists tr. exists Htr. exists Hlast. assumption. }
        exists (exist _ m Hm). reflexivity.
    Qed.

    Definition computable_sent_messages_has_been_sent_capability
      {Hsm : computable_sent_messages}
      {eq_message : EqDec message}
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
          selected_messages_consistency_prop input s m
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
      specialize (selected_message_exists_in_all_traces_initial_state s Hs input m) as H.
      elim H. assumption.
    Qed.

    Definition computable_received_messages_has_been_received
      {Hsm : computable_received_messages}
      {eq_message : EqDec message}
      (s : vstate vlsm)
      (m : message)
      : bool
      :=
      if inb eq_dec m (received_messages_fn s) then true else false.

    Lemma computable_received_messages_has_been_received_proper
      {Hsm : computable_received_messages}
      {eq_message : EqDec message}
      (s : state)
      (Hs : protocol_state_prop pre_vlsm s)
      (m : message)
      : has_been_received_prop computable_received_messages_has_been_received s m.
    Proof.
      unfold has_been_received_prop. unfold all_traces_have_message_prop.
      unfold computable_received_messages_has_been_received.
      destruct
        (inb eq_dec m (received_messages_fn s))
        eqn: Hin; split; intros; try discriminate; try reflexivity
        ; apply in_correct in Hin || apply in_correct' in Hin.
      - apply received_messages_full in Hin; try assumption. destruct Hin as [[m0 Hm0] Hx].
        simpl in Hx. subst m0. apply (received_messages_consistency s Hs m).
        assumption.
      - elim Hin. apply received_messages_full; try assumption.
        apply (received_messages_consistency s Hs m) in H.
        exists (exist _ m H). reflexivity.
    Qed.

    Definition computable_received_messages_has_not_been_received
      {Hsm : computable_received_messages}
      {eq_message : EqDec message}
      (s : vstate vlsm)
      (m : message)
      : bool
      :=
      negb (computable_received_messages_has_been_received s m).

    Lemma computable_received_messages_has_not_been_received_proper
      {Hsm : computable_received_messages}
      {eq_message : EqDec message}
      (s : state)
      (Hs : protocol_state_prop pre_vlsm s)
      (m : message)
      : has_not_been_received_prop computable_received_messages_has_not_been_received s m.
    Proof.
      unfold has_not_been_received_prop. unfold no_traces_have_message_prop.
      unfold computable_received_messages_has_not_been_received.
      rewrite Bool.negb_true_iff.
      unfold computable_received_messages_has_been_received.
      destruct
        (inb eq_dec m (received_messages_fn s))
        eqn: Hin; split; intros; try discriminate; try reflexivity
        ; apply in_correct in Hin || apply in_correct' in Hin.
      - apply received_messages_full in Hin; try assumption. destruct Hin as [[m0 Hm0] Hx].
        simpl in Hx. subst m0.
        destruct Hm0 as [is [tr [Htr [Hlast Hexists]]]].
        specialize (H is tr Htr Hlast).
        elim H. assumption.
      - intro is; intros. intro HExists. elim Hin. apply received_messages_full; try assumption.
        assert (Hm : selected_message_exists_in_some_traces input s m).
        { exists is. exists tr. exists Htr. exists Hlast. assumption. }
        exists (exist _ m Hm). reflexivity.
    Qed.

    Definition computable_received_messages_has_been_received_capability
      {Hsm : computable_received_messages}
      {eq_message : EqDec message}
      : has_been_received_capability
      :=
      {|
        has_been_received := computable_received_messages_has_been_received;
        proper_received := computable_received_messages_has_been_received_proper;
        proper_not_received := computable_received_messages_has_not_been_received_proper
      |}.
End Simple.

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
            (index_listing : list index)
            {finite_index : Listing index_listing}
            {validator : Type}
            {measurable_V : Measurable validator}
            {threshold_V : ReachableThreshold validator}
            (validator_listing : list validator)
            {finite_validator : Listing validator_listing}
            {IndEqDec : EqDec index}
            (IM : index -> VLSM message)
            (i0 : index)
            (constraint : composite_label IM -> composite_state IM  * option message -> Prop)
            (has_been_sent_capabilities : forall i : index, (has_been_sent_capability (IM i)))
            (has_been_received_capabilities : forall i : index, (has_been_received_capability (IM i)))
            (sender : message -> option validator)
            (A : validator -> index)
            (T : R)
            (X := composite_vlsm IM i0 constraint)
            .

     (** It is now straightforward to define a [no_equivocations] composition constraint.
         An equivocating transition can be detected by calling the [has_been_sent]
         oracle on its arguments and we simply forbid them **)

     Definition equivocation
      (m : message)
      (s : vstate X)
      : Prop
      :=
      forall (i : index),
      has_not_been_sent (IM i) (s i) m = true.

      (* TODO: Reevaluate if this looks better in a positive form *)

      Definition no_equivocations
        (l : vlabel X)
        (som : vstate X * option message)
        : Prop
        :=
        let (s, om) := som in
        match om with
        | None => True
        | Some m => ~equivocation m s
        end.


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
        has_not_been_sent  (IM i) sv m = true /\
        has_been_received  (IM j) sj m = true.

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
          /\ has_been_sent (IM j) ((destination elem) j) m = false
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

        (** For the equivocation sum fault to be computable, we require that
            our is_equivocating property is decidable. The current implementation
            refers to [is_equivocating_statewise], but this might change
            in the future **)

        Definition equivocation_dec_statewise
           (Hdec : forall (s : vstate X) (v : validator),
             {is_equivocating_statewise s v} + {~is_equivocating_statewise s v})
            : basic_equivocation (vstate X) (validator)
          :=
          {|
            state_validators := fun _ => validator_listing;
            state_validators_nodup := fun _ => proj1 finite_validator;
            is_equivocating_fn := fun (s : vstate X) (v : validator) =>
              if Hdec s v then true else false
          |}.

        Definition equivocation_dec_tracewise
           (Hdec : forall (s : vstate X) (v : validator),
             {is_equivocating_tracewise s v} + {~is_equivocating_tracewise s v})
            : basic_equivocation (vstate X) (validator)
          :=
          {|
            state_validators := fun _ => validator_listing;
            state_validators_nodup := fun _ => proj1 finite_validator;
            is_equivocating_fn := fun (s : vstate X) (v : validator) =>
              if Hdec s v then true else false
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


