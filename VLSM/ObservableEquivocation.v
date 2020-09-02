Require Import List ListSet FinFun.
Import ListNotations.
From CasperCBC
  Require Import
    Preamble
    CBC.Common CBC.Equivocation
    VLSM.Common VLSM.Composition
    .

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