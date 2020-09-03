Require Import List ListSet FinFun.
Import ListNotations.
From CasperCBC
  Require Import
    Preamble ListExtras ListSetExtras
    CBC.Common CBC.Equivocation
    VLSM.Common VLSM.Composition
    .

(** * Observable equivocation

In this section we define a notion of equivocation based on observations.

This approach is based on the intuition that a participant to the protocol
stores in its state knowledge about validators, obtained either directly or
through third parties.

We will consider this items of knowledge to be abstract objects of a
type <<event>>.
The <<event>> type is equiped with a [happens_before_fn] which should tell
whether an event was generated befor another.

We assume that all events for a given validator must be comparable through
[happens_before_fn]. Under this assumption, if there are events for the same
validator which are not comparable through [happens_before_fn], this constitutes
an [equivocation_evidence].
*)

Class comparable_events
  (event : Type)
  := { happens_before_fn : event -> event -> bool }.

Class computable_observable_equivocation_evidence
  (state validator event : Type)
  (event_eq : EqDec event)
  (event_comparable : comparable_events event) :=
  {
    observable_events : state -> validator -> set event;
    equivocation_evidence (s : state) (v : validator) : bool :=
      existsb
        (fun e1 =>
          existsb
            (fun e2 =>
              negb (comparableb happens_before_fn e1 e2)
            )
            (observable_events s v)
        )
        (observable_events s v)
  }.

(** We can use this notion of [computable_observable_equivocation_evidence]
to obtain the [basic_equivocation] between states and validators.
*)
Definition basic_observable_equivocation
  (state validator event : Type)
  `{Hevidence : computable_observable_equivocation_evidence state validator event}
  {measurable_V : Measurable validator}
  {reachable_threshold : ReachableThreshold validator}
  (validators : state -> set validator)
  (validators_nodup : forall (s : state), NoDup (validators s))
  : basic_equivocation state validator
  :=
  {|
    is_equivocating_fn := equivocation_evidence;
    state_validators := validators;
    state_validators_nodup := validators_nodup
  |}.

Section observable_equivocation_in_composition.

(** ** Linking evidence of equivocation with observable equivocation

We assume a composition of [VLSM]s where each machine has a way to
produce [computable_observable_equivocation_evidence].
*)


Context
  {message validator event : Type}
  {event_eq : EqDec event}
  {event_comparable : comparable_events event}
  {index : Type}
  {IndEqDec : EqDec index}
  (index_listing : list index)
  (finite_index : Listing index_listing)
  (IM : index -> VLSM message)
  (Hevidence : forall (i : index),
    computable_observable_equivocation_evidence
        (vstate (IM i)) validator event event_eq event_comparable
  )
  (i0 : index)
  (constraint : composite_label IM -> composite_state IM * option message -> Prop)
  (A : validator -> index)
  (X := composite_vlsm IM i0 constraint)
  (PreX := pre_loaded_vlsm X)
  .

(**
It is easy to define a [computable_observable_equivocation_evidence] mechanism for
the composition, by just defining the [observable_events] for the composite state
to be the union of [observable_events] for each of the component states.
*)

Definition composed_observable_events
  (s : vstate X)
  (v : validator)
  : set event
  :=
  fold_right (set_union eq_dec) [] (map (fun i => observable_events (s i) v) index_listing).

Definition composed_computable_observable_equivocation_evidence
  : computable_observable_equivocation_evidence (vstate X) validator event event_eq event_comparable
  :=
  {| observable_events := composed_observable_events |}.

Existing Instance composed_computable_observable_equivocation_evidence.

(**
Below we're trying to define some notions of equivocation based on
observable events.

For this purpose we assume that machines communicate through messages,
and that messages can carry some of the information of their originating
states.

To formalize that, we willl assume a function [message_observable_events]
yielding the events which can be observed in a message for a validator,
and we will require that this set is a subset of the [observable_events]
corresponding to the validator in any state obtained upon sending that
message ([message_observable_consistency]).

Given a trace ending in composite state <<s>> and an event <<e>> in the
[observable_events] of <<s i>> for validator <<v>>, an
[observable_event_witness] is a decomposition of the trace in which a
message where <<e>> is observable is sent before being received in the
component <<i>>.

We say that an equivocation of validator <<v>> can be observed in the
last state <<s>> of a trace ([equivocating_trace_last]) if there is an
[observable_event] for <<v>> in <<s i>>, <<i <> v>>, for which there is
no [observable_event_witness] in the trace.

We say that <<v>> is [equivocating_in_trace] <<tr>> if there is
a prefix of <<tr>> such that v is [equivocating_trace_last] w.r.t. that
prefix.

We say that <<v>> is [equivocating_in_state] <<s>> if it is
[equivocating_in_trace_last] w.r.t. all [protocol_trace]s ending in <<s>>.

Finally, we tie the [computable_observable_equivocation_evidence] notion
to that of [composite_vlsm_observable_equivocation] by requiring that
the existence of two events observable for a validator <<v>> in a state <<s>> 
which are not [comparable] w.r.t. [happens_before] relation guarantees
that <<v>> is [equivocating_in_state] <<s>> ([evidence_implies_equivocation]).
*)
Class composite_vlsm_observable_equivocation
  :=
  {
    message_observable_events : message -> validator -> set event;
    message_observable_consistency
      (m : message)
      (v : validator)
      (som : state * option message)
      (l : label)
      (s : state)
      (Ht : protocol_transition X l som (s, Some m))
      : incl (message_observable_events m v) (observable_events (s (projT1 l)) v);

    observable_event_witness
      (is : vstate X)
      (tr : list transition_item)
      (s := last (map destination tr) is)
      (v : validator)
      (e : event)
      (i : index)
      (He : In e (observable_events (s i) v))
      : Prop
      :=
      exists
        (prefix middle suffix : list transition_item)
        (sitem ritem : transition_item)
        (Heq : tr = prefix ++ [sitem] ++ middle ++ [ritem] ++ suffix)
        (m : message)
        (Hsent : output sitem = Some m)
        (Hreceived : input ritem = Some m)
        (Hreceived_by_i : projT1 (l ritem) = i),
        In e (message_observable_events m v);

    equivocating_in_trace_last
      (is : vstate X)
      (tr : list transition_item)
      (s := last (map destination tr) is)
      (v : validator)
      : Prop
      := exists
          (e : event)
          (i : index)
          (Hvi : A v <> i)
          (He : In e (observable_events (s i) v)),
          ~ observable_event_witness is tr v e i He;
    
    equivocating_in_trace
      (tr : protocol_trace X)
      (v : validator)
      : Prop
      :=
      exists
        (prefix : list transition_item)
        (last : transition_item)
        (Hpr : trace_prefix X (proj1_sig tr) last prefix),
        equivocating_in_trace_last (trace_first (proj1_sig tr)) prefix v;

    equivocating_in_state
      (s : protocol_state X)
      (v : validator)
      : Prop
      := forall 
        (is : vstate X)
        (tr : list transition_item)
        (Htr : finite_protocol_trace X is tr)
        (Hlast : last (map destination tr) is = proj1_sig s),
        equivocating_in_trace_last is tr v;
    
    evidence_implies_equivocation
      (s : vstate X)
      (Hs : protocol_state_prop X s)
      (v : validator)
      (e1 e2 : event)
      (He1 : In e1 (observable_events s v))
      (He2 : In e2 (observable_events s v))
      (Heqv : comparableb happens_before_fn e1 e2 = false)
      : equivocating_in_state (exist _ s Hs) v
  }.

End observable_equivocation_in_composition.

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
First, let us fix events to be messages, and choose the [happens_before_fn] to be
the [message_preceeds_fn].
*)

Definition message_comparable_events
  : comparable_events message
  :=
  {| happens_before_fn := message_preceeds_fn |}.

(**
If we have a [state_encapsulating_messages], then we can use the [sender]
function to select ones having a given validator and obtain the
corresponding [observable_events].
*)

Definition observable_messages
  (s : state)
  (v : validator)
  :=
  filter (fun m => if eq_dec (sender m) v then true else false) (get_messages s).

Definition message_computable_observable_equivocation_evidence
  : @computable_observable_equivocation_evidence state validator message _ message_comparable_events
  :=
  {| observable_events := observable_messages |}.

(**
Further, we can get all validators for a state by projecting the messages
on [sender] and thus obtain a [basic_equivocation] instance through the
[basic_observable_equivocation] definition.
*)

Definition message_basic_observable_equivocation
  (Hevidence := message_computable_observable_equivocation_evidence)
  (validators := fun s => set_map eq_dec sender (get_messages s))
  (validators_nodup := fun s => set_map_nodup eq_dec sender (get_messages s))
  : basic_equivocation state validator
  := @basic_observable_equivocation state validator message _ _ Hevidence _ _ validators validators_nodup.

(**
We can now show that the [message_based_equivocation] (customly built for
messages) and the [message_basic_observable_equivocation] (derived from it
as an instance of event-based equivocation) yield the same
[is_equivocating_fn].
*)

Lemma message_basic_observable_equivocation_iff
  (s : state)
  (v : validator)
  : @is_equivocating_fn _ _ _ _ message_basic_observable_equivocation s v
  = @is_equivocating_fn _ _ _ _ message_based_equivocation s v.
Proof.
  simpl. unfold equivocation_evidence.
  destruct
    (ListExtras.inb eq_dec v
      (map sender
         (filter (fun msg : message => equivocating_in_set msg (get_messages s))
            (get_messages s)))
    ) eqn: Heqv_msg.
  - rewrite existsb_exists. apply in_correct in Heqv_msg.
    apply in_map_iff in Heqv_msg.
    destruct Heqv_msg as [m [Hm Heqv_msg]].
    apply filter_In in Heqv_msg.
    destruct Heqv_msg as [Hin Heqv_msg].
    exists m.
    split.
    + unfold observable_events. simpl. unfold observable_messages.
      apply filter_In. split; try assumption.
      destruct (eq_dec (sender m) v); try reflexivity.
      elim n. assumption.
    + unfold equivocating_in_set in Heqv_msg.
      apply existsb_exists. apply existsb_exists in Heqv_msg.
      destruct Heqv_msg as [m' [Hin' Heqv_msg]].
      unfold equivocating_with in Heqv_msg.
      destruct (eq_dec m m'); try discriminate Heqv_msg.
      destruct (eq_dec (sender m) (sender m')); try discriminate Heqv_msg.
      symmetry in e. rewrite Hm in e.
      exists m'. split.
      * unfold observable_events. simpl. unfold observable_messages.
        apply filter_In. split; try assumption.
        destruct (eq_dec (sender m') v); try reflexivity.
        elim n0. assumption.
      * unfold happens_before_fn. simpl. unfold comparableb.
        destruct (eq_dec m m'); try (elim n; assumption).
        apply Bool.andb_true_iff in Heqv_msg.
        repeat rewrite Bool.negb_true_iff in Heqv_msg.
        destruct Heqv_msg as [Hmm' Hm'm].
        rewrite Hmm'. rewrite Hm'm.
        reflexivity.
  - unfold observable_events. simpl. unfold observable_messages.
    apply in_correct' in Heqv_msg.
    apply existsb_forall. intros m1 Hin1.
    apply existsb_forall. intros m2 Hin2.
    apply filter_In in Hin1. destruct Hin1 as [Hin1 Hin1'].
    apply filter_In in Hin2. destruct Hin2 as [Hin2 Hin2'].
    destruct (eq_dec (sender m1) v); try discriminate Hin1'. clear Hin1'.
    destruct (eq_dec (sender m2) v); try discriminate Hin2'. clear Hin2'.
    apply Bool.negb_false_iff.
    destruct (comparableb message_preceeds_fn m1 m2) eqn:Hcomp; try reflexivity.
    elim Heqv_msg.
    apply in_map_iff. exists m1. split; try assumption.
    apply filter_In. split; try assumption.
    unfold equivocating_in_set. apply existsb_exists.
    exists m2. split; try assumption.
    unfold comparableb in Hcomp.
    unfold equivocating_with.
    destruct (eq_dec m1 m2); try discriminate Hcomp.
    rewrite e. rewrite e0. 
    rewrite eq_dec_if_true; try reflexivity.
    apply Bool.orb_false_iff in Hcomp.
    destruct Hcomp as [Hm12 Hm21].
    rewrite Hm12. rewrite Hm21. reflexivity.
Qed.

End message_observable_equivocation_equivalent_defnitions.