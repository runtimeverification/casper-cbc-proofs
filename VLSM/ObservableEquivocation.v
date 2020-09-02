Require Import List ListSet.
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
              if eq_dec e1 e2 then false
              else negb (orb (happens_before_fn e1 e2) (happens_before_fn e2 e1))
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

    observable_happens_before_prop
      (s : vstate X)
      (Hs : protocol_state_prop X s)
      (i : index)
      (e : event)
      (v : validator)
      (Hvi : A v <> i)
      (He : In e (observable_events (s i) v))
      : Prop
      :=
      forall
        (is : vstate X)
        (tr : list transition_item)
        (Htr : finite_protocol_trace X is tr)
        (Hlast : last (map destination tr) is = s),
        exists
          (prefix middle suffix : list transition_item)
          (sitem ritem : transition_item)
          (Heq : tr = prefix ++ [sitem] ++ middle ++ [ritem] ++ suffix)
          (m : message)
          (Hsent : output sitem = Some m)
          (Hreceived : input ritem = Some m)
          (Hreceived_by_i : projT1 (l ritem) = i),
          In e (message_observable_events m v)
  }.

End observable_equivocation_in_composition.