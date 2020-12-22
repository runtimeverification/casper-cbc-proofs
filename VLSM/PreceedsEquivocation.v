Require Import
  Bool Reals
  List ListSet
  Coq.Classes.RelationClasses
  .

From CasperCBC
  Require Import
    Preamble
    Lib.ListExtras
    Lib.ListSetExtras
    CBC.Common
    CBC.Equivocation
    VLSM.Common
    VLSM.Composition
    VLSM.Equivocation
    VLSM.ObservableEquivocation
    .

(** ** Message-based equivocation

This definition relates a set of <<validator>>s and one of <<messages>>,
where messages are mapped to validators through the [sender] function,
and there is a function [message_preceeds_fn] which can decide whether
two messages having the same sender were seen one before another.

This allows to define that a message is [equivocating_with] another
if they have the same [sender] and are not comparable through
the [message_preceeds_fn].

Then, we can say that a message is [equivocating_in_set]
if it is [equivocating_with] any of the messages in that set.

_Note_: Ideally [message_preceeds_fn] should determine a strict partial order;
however this might not happen for the whole set of messages, but only
for a restricted set, e.g., [protocol_messsage]s
(please see class [HasPreceedsEquivocation] for more details).
*)

Class message_equivocation_evidence
  (message validator : Type)
  `{EqDecision message}
  `{EqDecision validator}
  (message_preceeds : message -> message -> Prop)
  {message_preceeds_dec : RelDecision message_preceeds}
  :=
  { sender : message -> option validator
  ; equivocating_with (msg1 msg2 : message)  : Prop
    := (exists v, sender msg1 = Some v /\ sender msg2 = Some v) /\
    ~comparable message_preceeds msg1 msg2
  ; equivocating_in_set
      (msg : message)
      (msgs : set message)
      :=
      exists m, In m msgs /\ equivocating_with msg m
  }.

Instance equivocating_with_dec `{message_equivocation_evidence}:
  RelDecision equivocating_with.
Proof with (try (right; intros [v1 [Hv Hv0]]; congruence)).
  intros msg1 msg2.
  unfold equivocating_with.
  apply Decision_and.
  - destruct (sender msg1) eqn:Hmsg1 ...
    destruct (sender msg2) eqn:Hmsg2 ...
    destruct (decide (v = v0)) ...
    subst. left. exists v0. intuition.
  - apply Decision_not.
    typeclasses eauto.
Qed.

Instance equivocating_in_set_dec `{message_equivocation_evidence} :
  Decision (equivocating_in_set msg msgs).
Proof.
  intros msg msgs.
  apply (Decision_iff (Exists_exists _ _)).
  apply @Exists_dec.
  typeclasses eauto.
Qed.

(**
First, let us fix events to be messages, and choose the [happens_before] relation
to be the [message_preceeds] relation.
*)

(** ** Equivocation for states encapsulating messages

The definition below assumes that one can [get_messages] associated to
states, and these messages are equipped with [message_equivocation_evidence].

For the purpose of the definition, what are the messages associated to the
state can remain an abstract notion; however, one could imagine these messages
as being those the state has memory of (sent, received, or otherwise observed).

We can use this to instantiate [basic_equivocation], by saying that a
validator is equivocating in a state iff there exists at least one message
in that state with it as a sender which is [equivocating_in_set] for
the messages of the state.
*)
Class state_encapsulating_messages
  (state message : Type)
  :=
  { get_messages : state -> set message }.

Definition state_encapsulating_messages_is_equivocating
  {state validator : Type}
  `{Hstate : state_encapsulating_messages state message}
  `{Hmessage : message_equivocation_evidence message validator}
  (s : state)
  (v : validator)
  : Prop
  :=
  exists (msg : message),
    In msg (get_messages s) /\
    sender msg = Some v /\
    equivocating_in_set msg (get_messages s).

Lemma state_encapsulating_messages_is_equivocating_dec
  {state validator : Type}
  `{Hstate : state_encapsulating_messages state message}
  `{Hmessage : message_equivocation_evidence message validator}
  : RelDecision state_encapsulating_messages_is_equivocating.
Proof.
  intros s v.
  unfold state_encapsulating_messages_is_equivocating.
  apply (Decision_iff (Exists_exists _ _)).
  apply @Exists_dec.
  intro m.
  apply Decision_and; [apply option_eq_dec|].
  unfold equivocating_in_set.
  apply (Decision_iff (Exists_exists _ _)).
  apply @Exists_dec.
  intro m'.
  apply equivocating_with_dec.
Qed.

Definition state_encapsulating_messages_validators
  {state message validator : Type}
  `{Hstate : state_encapsulating_messages state message}
  `{Hmessage : message_equivocation_evidence message validator}
  (s : state)
  : set validator
  := nodup decide_eq (map_option sender (get_messages s)).

Lemma state_encapsulating_messages_validators_nodup
  {state message validator : Type}
  `{Hstate : state_encapsulating_messages state message}
  `{Hmessage : message_equivocation_evidence message validator}
  (s : state)
  : NoDup (state_encapsulating_messages_validators s).
Proof.
  apply NoDup_nodup.
Qed.

Definition state_encapsulating_messages_equivocation
  (state message validator : Type)
  `{Hstate : state_encapsulating_messages state message}
  `{Hmessage : message_equivocation_evidence message validator}
  {measurable_V : Measurable validator}
  {reachable_threshold : ReachableThreshold validator}
  : basic_equivocation state validator
  :=
  {|  state_validators := state_encapsulating_messages_validators
   ;  state_validators_nodup := state_encapsulating_messages_validators_nodup
   ;  is_equivocating := state_encapsulating_messages_is_equivocating
   ;  is_equivocating_dec := state_encapsulating_messages_is_equivocating_dec
  |}.

Section equivocation_properties.

Lemma equivocating_in_set_incl
  {message validator : Type}
  `{Heqv : message_equivocation_evidence message validator}
  (sigma sigma' : set message)
  (Hincl : incl sigma sigma')
  (msg : message)
  (Hmsg : equivocating_in_set msg sigma)
  : equivocating_in_set msg sigma'.
Proof. firstorder. Qed.

Context
  (state message validator : Type)
  `{Hstate : state_encapsulating_messages state message}
  `{Hmessage : message_equivocation_evidence message validator}
  {measurable_V : Measurable validator}
  {reachable_threshold : ReachableThreshold validator}
  (Hbasic := state_encapsulating_messages_equivocation state message validator)
  .

Existing Instance Hbasic.

Lemma state_validators_incl
  (sigma sigma' : state)
  (Hincl : incl (get_messages sigma) (get_messages sigma'))
  : incl (state_validators sigma) (state_validators sigma').
Proof.
  simpl. unfold incl. unfold state_encapsulating_messages_validators.
  intro v. repeat rewrite nodup_In. apply map_option_incl.
  assumption.
Qed.

Lemma equivocating_validators_incl
  (sigma sigma' : state)
  (Hincl : incl (get_messages sigma) (get_messages sigma'))
  : incl (equivocating_validators sigma) (equivocating_validators sigma').
Proof.
  unfold equivocating_validators.
  intro v. rewrite !filter_In.
  pose proof (state_validators_incl _ _ Hincl).
  rewrite !bool_decide_eq_true.
  firstorder.
Qed.

Lemma equivocation_fault_incl
  (sigma sigma' : state)
  (Hincl : incl (get_messages sigma) (get_messages sigma'))
  : (equivocation_fault sigma <= equivocation_fault sigma')%R.
Proof.
  intros.
  apply sum_weights_incl
  ; [solve[apply NoDup_filter; apply state_validators_nodup]..|].
  apply equivocating_validators_incl. assumption.
Qed.

(* If a state is not overweight, none of its subsets are *)
Lemma not_heavy_incl
  (sigma sigma' : state)
  (Hincl : incl (get_messages sigma) (get_messages sigma'))
  (Hsigma' : not_heavy sigma')
  : not_heavy sigma.
Proof.
  apply Rle_trans with (equivocation_fault sigma'); try assumption.
  apply equivocation_fault_incl; assumption.
Qed.

Lemma empty_not_heavy
  (s : state)
  (Hempty : get_messages s = nil)
  : not_heavy s.
Proof.
  unfold not_heavy. unfold equivocation_fault. unfold equivocating_validators.
  simpl. unfold state_encapsulating_messages_validators. rewrite Hempty. simpl.
  destruct threshold;simpl.
  apply Rge_le;assumption.
Qed.

End equivocation_properties.

(** * VLSM equivocation based-on full-node-like  [message_equivocation_evidence]

Given a [VLSM] X over a type of messages which [message_equivocation_evidence], we say
that @X@ has [vlsm_message_equivocation_evidence] if [message_preceeds_fn]
determines a [StrictOrder] on the [protocol_message]s of @X@.
*)

Section vlsm_message_equivocation_evidence.

  Context
    {message : Type}
    (validator : Type)
    `{Eqv : message_equivocation_evidence message validator}
    (X : VLSM message).

  Class vlsm_message_equivocation_evidence
    :=
    { protocol_message_preceeds
        (pm1 pm2 : byzantine_message X)
        : Prop
        := message_preceeds (proj1_sig pm1) (proj1_sig pm2)
    ; protocol_message_preceeds_strict_order
      : StrictOrder protocol_message_preceeds
    ; evidence_of_equivocation
        (pm1 pm2 : byzantine_message X)
        (m1 := proj1_sig pm1)
        (m2 := proj1_sig pm2)
        (Heqv : equivocating_with m1 m2 = true)
        (s : state)
        (tr : list transition_item)
        (Htr : finite_protocol_trace (pre_loaded_with_all_messages_vlsm X) s tr)
        (Hm1 : trace_has_message X (field_selector input) m1 tr)
        (Hm2 : trace_has_message X (field_selector input) m2 tr)
        : equivocation_in_trace X m1 tr
        \/ equivocation_in_trace X m2 tr
    }.

End vlsm_message_equivocation_evidence.

Section composite_preceeds_equivocation.

  Context
    {message validator : Type}
    `{Eqv : message_equivocation_evidence message validator}
    `{EqDecision index}
    (IM : index -> VLSM message)
    (i0 : index)
    (constraint1 : composite_label IM -> composite_state IM * option message -> Prop)
    (constraint2 : composite_label IM -> composite_state IM * option message -> Prop)
    (Hsubsumption : constraint_subsumption IM constraint1 constraint2)
    (X1 := composite_vlsm IM i0 constraint1)
    (X2 := composite_vlsm IM i0 constraint2)
    .

  Lemma preceeds_equivocation_constrained
    (Heqv : vlsm_message_equivocation_evidence validator X2)
    : vlsm_message_equivocation_evidence validator X1.
  Proof.
    destruct Heqv as
      [ protocol_message_preceeds2
        [ protocol_message_preceeds2_irreflexive
          protocol_message_preceeds2_transitive
        ]
        Heqv
      ].
    specialize
      (constraint_subsumption_byzantine_message_prop
        IM i0 constraint1 constraint2 Hsubsumption
      ); intro Hem.
    repeat split.
    - intros [m1 Hem1].
      unfold complement. simpl.
      apply Hem in Hem1.
      specialize (protocol_message_preceeds2_irreflexive (exist _ m1 Hem1)).
      unfold complement in protocol_message_preceeds2_irreflexive.
      assumption.
    - intros [m1 Hem1] [m2 Hem2] [m3 Hem3]
      ; simpl.
      intros H12 H23.
      apply Hem in Hem1.
      apply Hem in Hem2.
      apply Hem in Hem3.
      specialize
        (protocol_message_preceeds2_transitive
          (exist _ m1 Hem1)
          (exist _ m2 Hem2)
          (exist _ m3 Hem3)
          H12
          H23
        ).
      assumption.
    - intros [m1 Hm1] [m2 Hm2]. simpl. intros.
      assert (Hm1': byzantine_message_prop X2 m1)
        by (apply constraint_subsumption_byzantine_message_prop with constraint1; assumption).
      assert (Hm2': byzantine_message_prop X2 m2)
        by (apply constraint_subsumption_byzantine_message_prop with constraint1; assumption).
      specialize (constraint_subsumption_pre_loaded_with_all_messages_incl IM i0 constraint1 constraint2 Hsubsumption (@Finite _ (type X1) s tr) Htr)
        as Htrace'.
      simpl in Htrace'.
      specialize (Heqv (exist _ _ Hm1') (exist _ _ Hm2')). simpl in Heqv.
      specialize (Heqv Heqv0 s tr Htrace' Hm0 Hm3).
      assumption.
  Qed.

End composite_preceeds_equivocation.

Section message_observable_equivocation_equivalent_defnitions.

(** ** Deriving observable equivocation evidence from message-based equivocation evidence

In this section we show that given the [basic_equivocation] instance
obtained through [state_encapsulating_messages_equivocation], we can turn
it into a [basic_observable_equivocation].

*)

Context
  (state message validator : Type)
  `{Hmsgeqv : message_equivocation_evidence message validator}
  {Hstate : state_encapsulating_messages state message}
  {measurable_V : Measurable validator}
  {reachable_threshold : ReachableThreshold validator}
  (message_based_equivocation := state_encapsulating_messages_equivocation state message validator)
  .

(**
If we have a [state_encapsulating_messages], then we can use the [sender]
function to select ones having a given validator and obtain the
corresponding [observable_events].
*)

Definition has_been_observed_messages
  (s : state)
  (m : message)
  :=
  In m (get_messages s).

Lemma has_been_observed_messages_dec
  : RelDecision has_been_observed_messages.
Proof.
  intros s m.
  apply in_dec. assumption.
Qed.

Instance observable_messages
  : observable_events state message
  :=
  {| has_been_observed := has_been_observed_messages;
     has_been_observed_dec := has_been_observed_messages_dec
  |}.


Definition message_observation_based_equivocation_evidence
  : @observation_based_equivocation_evidence state validator message _ _ _ message_preceeds_dec sender.
Proof. split. Defined.  

Local Instance message_observation_based_equivocation_evidence_dec
  : RelDecision (@equivocation_evidence _ _ _ _ _ _ _ _ message_observation_based_equivocation_evidence).
Proof.
  intros s v.
  unfold equivocation_evidence.
  unfold has_been_observed. simpl. unfold has_been_observed_messages.
  apply (Decision_iff (Exists_exists _ _)).
  apply @Exists_dec.
  intro m1.
  apply Decision_and; [apply option_eq_dec|].
  apply (Decision_iff (Exists_exists _ _)).
  apply @Exists_dec.
  intro m2.
  apply Decision_and; [apply option_eq_dec|].
  apply Decision_not.
  apply comparable_dec.
  assumption.
Qed.

(**
Further, we can get all validators for a state by projecting the messages
on [sender] and thus obtain a [basic_equivocation] instance through the
[basic_observable_equivocation] definition.
*)

Definition message_basic_observable_equivocation
  (Hevidence := message_observation_based_equivocation_evidence)
  : basic_equivocation state validator
  := @basic_observable_equivocation state validator message _ _ _ _ sender Hevidence _ _ _ state_encapsulating_messages_validators state_encapsulating_messages_validators_nodup.


(**
We can now show that the [message_based_equivocation] (customly built for
messages) and the [message_basic_observable_equivocation] (derived from it
as an instance of event-based equivocation) yield the same
[is_equivocating_fn].
*)

Lemma message_basic_observable_equivocation_iff
  (s : state)
  (v : validator)
  : @is_equivocating _ _ _ _ message_basic_observable_equivocation s v
  <-> @is_equivocating _ _ _ _ message_based_equivocation s v.
Proof.
  unfold is_equivocating. simpl. unfold equivocation_evidence.
  unfold state_encapsulating_messages_is_equivocating.
  unfold has_been_observed. simpl. unfold has_been_observed_messages.
  unfold equivocating_in_set. unfold equivocating_with.
  firstorder.
  exists x. split; [assumption|].  split; [assumption|].
  exists x0.  split; [assumption|].  split; [congruence|].
  firstorder.
Qed.

End message_observable_equivocation_equivalent_defnitions.
