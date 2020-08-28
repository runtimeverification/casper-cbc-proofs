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
      (vlsm : VLSM message).

(** We begin with a basic utility function. **)

    Definition trace_has_message
      (message_selector : transition_item -> option message)
      (msg : message)
      (tr : protocol_trace vlsm)
      : Prop
      := exists (last : transition_item),
         exists (prefix : list transition_item),
          trace_prefix vlsm (proj1_sig tr) last prefix
          /\ message_selector last = Some msg.

(** The following property detects equivocation in a given trace for a given message. **)

    Definition equivocation_in_trace
               (msg : message)
               (tr : protocol_trace vlsm)
      : Prop
      :=
        exists (last : transition_item),
        exists (prefix : list transition_item),
          trace_prefix vlsm (proj1_sig tr) last prefix
          /\  input last = Some msg
          /\  ~ In (Some msg) (List.map output prefix).

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
      (Htr : finite_protocol_trace (pre_loaded_vlsm vlsm) start tr)
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
      (Htr : finite_protocol_trace (pre_loaded_vlsm vlsm) start tr)
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
      (Htr : finite_protocol_trace (pre_loaded_vlsm vlsm) start tr)
      (Hlast : last (List.map destination tr) start = s),
      ~List.Exists (fun (elem : transition_item) => message_selector elem = Some m) tr.

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
               (Hs : protocol_state_prop (pre_loaded_vlsm vlsm) s)
               (m : message),
               (has_been_sent_prop has_been_sent s m);

      has_not_been_sent: state_message_oracle
        := fun (s : state) (m : message) => negb (has_been_sent s m);

      proper_not_sent:
        forall (s : state)
               (Hs : protocol_state_prop (pre_loaded_vlsm vlsm) s)
               (m : message),
               has_not_been_sent_prop has_not_been_sent s m;
    }.

    Class has_been_received_capability := {
      has_been_received: state_message_oracle;

      proper_received:
        forall (s : state)
               (Hs : protocol_state_prop (pre_loaded_vlsm vlsm) s)
               (m : message),
               (has_been_received_prop has_been_received s m);

      has_not_been_received: state_message_oracle
        := fun (s : state) (m : message) => negb (has_been_received s m);

      proper_not_received:
        forall (s : state)
               (Hs : protocol_state_prop (pre_loaded_vlsm vlsm) s)
               (m : message),
               has_not_been_received_prop has_not_been_received s m;
    }.

    Definition sent_messages
      (s : vstate vlsm)
      : Type
      :=
      sig (fun m => selected_message_exists_in_some_traces output s m).

    Lemma sent_messages_proper
      (Hhbs : has_been_sent_capability)
      (ps : protocol_state (pre_loaded_vlsm vlsm))
      (m : message)
      (s := proj1_sig ps)
      : has_been_sent s m = true <-> exists (m' : sent_messages s), proj1_sig m' = m.
    Proof.
      split.
      - specialize (proper_sent s (proj2_sig ps) m) as Hbs.
        unfold has_been_sent_prop in Hbs. unfold all_traces_have_message_prop in Hbs.
        intros. apply Hbs in H.
        unfold s in *. clear s.
        destruct ps as [s [_om Hs]]. simpl in *.
        specialize (protocol_is_trace (pre_loaded_vlsm vlsm) s _om Hs) as Htr.
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
        specialize (proper_not_sent s (proj2_sig ps) m) as Hns.
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
      (ps : protocol_state (pre_loaded_vlsm vlsm))
      (m : message)
      (s := proj1_sig ps)
      : has_been_received s m = true <-> exists (m' : received_messages s), proj1_sig m' = m.
    Proof.
      split.
      - specialize (proper_received s (proj2_sig ps) m) as Hbs.
        unfold has_been_received_prop in Hbs. unfold all_traces_have_message_prop in Hbs.
        intros. apply Hbs in H.
        unfold s in *. clear s.
        destruct ps as [s [_om Hs]]. simpl in *.
        specialize (protocol_is_trace (pre_loaded_vlsm vlsm) s _om Hs) as Htr.
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
        specialize (proper_not_received s (proj2_sig ps) m) as Hns.
        unfold has_not_been_received_prop in Hns. unfold no_traces_have_message_prop in Hns.
        unfold has_not_been_received in Hns. rewrite Bool.negb_true_iff in Hns.
        apply Hns in Hbs.
        destruct Hm0 as [is [tr [Htr [Hdest Hout]]]].
        specialize (Hbs is tr Htr Hdest).
        elim Hbs. assumption.
    Qed.

    Class computable_sent_messages := {
      sent_messages_fn :
        forall (ps : protocol_state (pre_loaded_vlsm vlsm)),
          {l : list (sent_messages (proj1_sig ps)) | Listing l};

      sent_messages_consistency :
        forall
          (ps : protocol_state (pre_loaded_vlsm vlsm))
          (m : message)
          (s := proj1_sig ps),
          selected_message_exists_in_some_traces output s m <-> selected_message_exists_in_all_traces output s m
    }.

    Definition computable_sent_messages_has_been_sent
      {Hsm : computable_sent_messages}
      {eq_message : EqDec message}
      (ps : protocol_state (pre_loaded_vlsm vlsm))
      (m : message)
      : bool
      :=
      let sent_messages_list := List.map (@proj1_sig message _) (proj1_sig (sent_messages_fn ps)) in
      if in_dec eq_message m sent_messages_list then true else false.

    Class computable_received_messages := {
      received_messages_fn :
        forall (ps : protocol_state (pre_loaded_vlsm vlsm)),
          {l : list (received_messages (proj1_sig ps)) | Listing l};

      received_messages_consistency :
        forall
          (ps : protocol_state (pre_loaded_vlsm vlsm))
          (m : message)
          (s := proj1_sig ps),
          selected_message_exists_in_some_traces input s m <-> selected_message_exists_in_all_traces input s m
    }.

    Definition computable_received_messages_has_been_received
      {Hsm : computable_received_messages}
      {eq_message : EqDec message}
      (ps : protocol_state (pre_loaded_vlsm vlsm))
      (m : message)
      : bool
      :=
      let received_messages_list := List.map (@proj1_sig message _) (proj1_sig (received_messages_fn ps)) in
      if in_dec eq_dec m received_messages_list then true else false.
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
          equivocation_in_trace X m (build_trace_prefix_protocol X Hpr).

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


