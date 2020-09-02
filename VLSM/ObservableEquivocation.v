Require Import List ListSet FinFun.
Import ListNotations.
From CasperCBC
  Require Import
    Preamble
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