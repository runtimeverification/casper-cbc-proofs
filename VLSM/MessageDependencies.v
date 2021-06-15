From Coq
Require Import
  FinFun List ListSet
  .
Import ListNotations.
From CasperCBC
Require Import
  Preamble Measurable
  VLSM.Common VLSM.Composition VLSM.Equivocation
  .

Section message_dependencies.

Context
  {message : Type}
  {validator : Type}
  {index : Type}
  (sender : message -> option validator)
  (A : validator -> index)
  (IM : index -> VLSM message)
  (Hbs : forall i, has_been_sent_capability (IM i))
  (Hbr : forall i, has_been_received_capability (IM i))
  (Hbo := fun i => has_been_observed_capability_from_sent_received (IM i))
  {i0 : Inhabited index}
  {IndEqDec : EqDecision index}
  (X := free_composite_vlsm IM)
  .

(** An abstract framework for the full-node condition.
Assumes that each message has an associated set of [message_dependencies],
which is empty for initial messages.
Furthermore, it constraints senders to satisfy the
[sender_strong_nontriviality] property.

[message_dependencies] for a message @m@m are axiomatized to be exactly those
messages which were received by the state emitting the message @m@, and are
thus responsible for @m@ being created.
*)
Class MessageDependencies
  :=
  { message_dependencies : message -> set message
  ; sender_safety :  sender_strong_nontriviality_prop IM A sender
  ; initial_message_not_dependent (m : message)
      : composite_initial_message_prop IM m -> message_dependencies m = []
  ; no_sender_for_initial_message : no_sender_for_initial_message_prop IM sender
(*
  ; message_dependencies_characterization (m : message)
      : forall
        (v : validator)
        (Hmv : sender m = Some v)
        (s : vstate (IM (A v)))
        (Hsm : protocol_generated_prop (pre_loaded_with_all_messages_vlsm (IM (A v))) s m)
        (dm : message),
        In dm (message_dependencies m) <->
        has_been_observed (has_been_observed_capability := Hbo (A v)) (IM (A v)) s dm
*)        
  }.

(** Under [MessageDependencies] assumptions, the (local) full node condition
requires that the component of the state receiving the message has previously
observed all of @m@'s [message_dependencies].
*)
Definition message_dependencies_local_full_node_condition
  {Hdm : MessageDependencies}
  (i : index)
  (s : vstate (IM i))
  (m : message)
  : Prop
  := forall dm, In dm (message_dependencies m) ->
    @has_been_observed _ (IM i) (Hbo i) s dm.

(** The constraint associated to the above condition. *)
Definition message_dependencies_local_full_node_constraint
  {Hdm : MessageDependencies}
  (l : composite_label IM)
  (som : composite_state IM * option message)
  : Prop
  :=
  let (s, om) := som in
  match om with
  | None => True
  | Some m =>
    let (i, li) := l in
    message_dependencies_local_full_node_condition i (s i) m
  end.

End message_dependencies.

Arguments message_dependencies { _ _ _ _ _ _ _ } _ .
Arguments message_dependencies_local_full_node_constraint  { _ _ _ _ _ _ _ _ _ } _ _.
Arguments message_dependencies_local_full_node_condition  { _ _ _ _ _ _ _ _ _ _} _ _.


Section message_dependencies_full_node.

Context
  {message : Type}
  {validator : Type}
  {index : Type}
  (sender : message -> option validator)
  (A : validator -> index)
  (IM : index -> VLSM message)
  (Hbs : forall i, has_been_sent_capability (IM i))
  (Hbr : forall i, has_been_received_capability (IM i))
  (Hbo := fun i => has_been_observed_capability_from_sent_received (IM i))
  {i0 : Inhabited index}
  {IndEqDec : EqDecision index}
  (X := free_composite_vlsm IM)
  {Hdm : MessageDependencies sender A IM }
  {index_listing : list index}
  (finite_index : Listing index_listing)
  (X_has_been_sent_capability : has_been_sent_capability X := free_composite_has_been_sent_capability IM finite_index Hbs)
  (X_has_been_received_capability : has_been_received_capability X := free_composite_has_been_received_capability IM finite_index Hbr)
  (X_has_been_observed_capability : has_been_observed_capability X := has_been_observed_capability_from_sent_received X)
  .

Lemma has_been_sent_sender_strong_nontriviality
  v s m
  (Hs : protocol_state_prop (pre_loaded_with_all_messages_vlsm (IM (A v))) s)
  (Hsent : has_been_sent (IM (A v)) s m)
  : sender m = Some v.
Proof.
  apply proper_sent in Hsent; [|assumption].
  apply protocol_state_has_trace in Hs.
  destruct Hs as [is [tr Htr]]. specialize (Hsent is tr Htr).
  apply finite_protocol_trace_init_to_forget_last in Htr.
  specialize (can_emit_from_protocol_trace _ is m tr Htr Hsent) as Hemit.
  apply (sender_safety sender A IM _ _ Hemit).
Qed.

Existing Instance X_has_been_observed_capability.

(** A slightly more relaxed version of the full-node condition requires that
the composite state as a whole has observed all the [message_dependencies] of
the message to be received.
*)
Definition message_dependencies_global_full_node_condition
  (s : composite_state IM)
  (m : message)
  : Prop
  :=
  forall dm, In dm (message_dependencies m) ->
    has_been_observed X s dm.

(** Proof that the [message_dependencies_global_full_node_condition] is weaker
than the [message_dependencies_local_full_node_condition]. *)
Lemma message_dependencies_global_full_node_condition_from_local
  s i si im
  (Hsi : s i = si)
  (Hlocal : message_dependencies_local_full_node_condition si im)
  : message_dependencies_global_full_node_condition s im.
Proof.
  intros m Hm.
  specialize (Hlocal m Hm).
  subst.
  destruct Hlocal as [Hsent | Hreceived].
  - left. exists i. assumption.
  - right. exists i. assumption.
Qed.

End message_dependencies_full_node.

Arguments message_dependencies_global_full_node_condition  { _ _ _ _ _ _ _ _ _ _ _ _} _ _.