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

Section dependent_messages.

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

Class DependentMessages
  :=
  { dependent_messages : message -> set message
  ; initial_message_not_dependent (m : message)
      : composite_initial_message_prop IM m -> dependent_messages m = []
  ; sender_safety :  sender_strong_nontriviality_prop IM A sender
  ; dependent_message (m : message)
      : forall
        (v : validator)
        (Hmv : sender m = Some v)
        (s : vstate (IM (A v)))
        (Hsm : protocol_generated_prop (pre_loaded_with_all_messages_vlsm (IM (A v))) s m)
        (dm : message),
        In dm (dependent_messages m) <->
        @state_received_not_sent _ (IM (A v)) (Hbs (A v)) (Hbr (A v)) s dm
  }.


Definition dependent_messages_local_full_node_condition
  {Hdm : DependentMessages}
  (i : index)
  (s : vstate (IM i))
  (m : message)
  : Prop
  := forall dm, In dm (dependent_messages m) ->
    @has_been_observed _ (IM i) (Hbo i) s dm.

Definition dependent_messages_local_full_node_constraint
  {Hdm : DependentMessages}
  (l : composite_label IM)
  (som : composite_state IM * option message)
  : Prop
  :=
  let (s, om) := som in
  match om with
  | None => True
  | Some m =>
    let (i, li) := l in
    dependent_messages_local_full_node_condition i (s i) m
  end.

End dependent_messages.

Arguments dependent_messages { _ _ _ _ _ _ _ _ _ } _ .
Arguments dependent_messages_local_full_node_constraint  { _ _ _ _ _ _ _ _ _ } _ _.
Arguments dependent_messages_local_full_node_condition  { _ _ _ _ _ _ _ _ _ _ } _ _.


Section dependent_messages_full_node.

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
  {Hdm : DependentMessages sender A IM Hbs Hbr}
  {index_listing : list index}
  (finite_index : Listing index_listing)
  (X_has_been_sent_capability : has_been_sent_capability X := composite_has_been_sent_capability IM (free_constraint IM) finite_index Hbs)
  (X_has_been_received_capability : has_been_received_capability X := composite_has_been_received_capability IM (free_constraint IM) finite_index Hbr)
  (X_has_been_observed_capability : has_been_observed_capability X := has_been_observed_capability_from_sent_received X)
  .

Existing Instance X_has_been_observed_capability.

Definition dependent_messages_global_full_node_condition
  (s : composite_state IM)
  (m : message)
  : Prop
  :=
  forall dm, In dm (dependent_messages m) ->
    has_been_observed X s dm.
  
Lemma dependent_messages_global_full_node_condition_from_local
  s i si im
  (Hsi : s i = si)
  (Hlocal : dependent_messages_local_full_node_condition si im)
  : dependent_messages_global_full_node_condition s im.
Proof.
  intros m Hm.
  specialize (Hlocal m Hm).
  subst.
  destruct Hlocal as [Hsent | Hreceived].
  - left. exists i. assumption.
  - right. exists i. assumption.
Qed.

End dependent_messages_full_node.

Arguments dependent_messages_global_full_node_condition  { _ _ _ _ _ _ _ _ _ _ _ _} _ _.