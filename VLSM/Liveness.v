Require Import List.
Require Import Coq.Logic.FinFun.

From CasperCBC
  Require Import
    Lib.Preamble
    Lib.Traces
    Lib.Measurable
    VLSM.Common
    VLSM.Decisions
    VLSM.Composition
    VLSM.Equivocation (* for has_been_sent *)
.

(**
   This module defines liveness, and contains basic defintiions
   that will be used for proving liveness properties,
   constructing protocols designed for liveness, and
   stating the assumptions under which those protocols are live.
 *)

(** * Liveness

 A composite VLSM is live if every complete trace reaches a [decision]
 *)
Section Liveness.

  Context
    {CV : consensus_values}
    {message : Type}
    {index : Type}
    {Heqd : EqDecision index}
    (IM : index -> VLSM message)
    {Hi : Inhabited index}
    (constraint : composite_label IM -> composite_state IM * option message -> Prop)
    (X := composite_vlsm IM constraint)
    (ID : forall i : index, vdecision (IM i)).

Definition live : Prop :=
  forall
    (tr : Trace)
    (Htr: complete_trace_prop X tr),
  exists
    (n : nat)
    (i : index)
    (st : vstate X),
    trace_nth X tr n = (Some st)
    /\ (ID i) (st i) <> None.

End Liveness.

(** * Clocks

Liveness always requires some notion of time, and assumptions
that messages are not infinitely delayed.

We will use logical clocks that assign states and
messages to times in [nat], with messages carrying the
time from the sending component, and messages only
expected to be received by a node at the matching time.
 *)

Section Clocks.

  (** A clock for a VLSM assigns a time to any state, and is
      nondecreasing on transitions.
   *)
  Record ClockFor `(X:VLSM message) : Type := {
    clock : vstate X -> nat;
    clock_monotone : forall l s om s' om',
        vtransition X l (s,om) = (s',om') -> clock s <= clock s';
    }.

  (** For a composite VLSM we usually want to have a separate
      clock for each component
   *)
  Definition ClocksFor `(IM:index -> VLSM message) : Type :=
    forall i, ClockFor (IM i).

  (** A message time function is consistent with a
      set of clocks for a composite VLSM if
      the message time always agrees with the time
      of the sending component at the begining of
      the transition where the message is sent.
   *)
  Record MessageTimeProp
        `(IM: index -> VLSM message) `{EqDecision index} `{Inhabited index} constraint
        (X := composite_vlsm IM constraint)
        (clocks : ClocksFor IM)
        (message_time : message -> nat)
    : Type := {
    message_time_accurate :
      forall m t,
        message_time m = t
        <-> (forall (l:vlabel X) s om l s',
             vtransition X l (s,om) = (s', Some m) -> clock _ (clocks _) (s (projT1 l)) = t)
             }.

End Clocks.

(** * Plans

Protocols may be designed so that only a subset of validators
are expected to send messages in each phase.

Our example protocol will use a fixed that specifies the
expected set of senders for each time.
Here we define the conditions that such a fixed plan will
need to satisfy.

Later protocols will dyanmically construct plans to
react to failures, and we will need to generalize
these properties to apply to dynamic plans.
 *)
Section Plan.
  Context
    (index: Type)
    {Hweights: Measurable index}
    {index_listing: list index}
    {Hfinite: FinFun.Listing index_listing}
  .

  (** An "odd" set cannot be partitioned into
      two disjoint pieces with equal weight,
      so votes cannot have ties *)
  Definition odd_set (P: index -> Prop) : Prop :=
    forall l1 l2,
      (forall i, P i <-> (In i l1 \/ In i l2)) ->
      NoDup (l1++l2) ->
      sum_weights l1 <> sum_weights l2.

  Record Plan (plan: nat -> index -> Prop) := {
    stages_nonempty : forall n, ~forall v, ~plan n v;
    plan_has_odd_stage: exists n, odd_set (plan n);
    recurring_sends: forall n v, exists n', n' > n /\ plan n' v;
    }.
End Plan.

(** * Synchrony Constraint

Synchrony assumptions will be expresed with composition constraints.

Currently we define only a strong assumption that doesn't allow
any messages to be delayed, which will be used for example proofs of
liveness.

Definitions allowing a limited rate of "synchronization faults" will
be added before verifying more robust protocols over more realistic
assumptions.
 *)
Section StrongSynchrony.
  Context
    {message : Type}
    {index : Type}
    {index_listing : list index}
    (finite_index : Listing index_listing)
    {Heqd : EqDecision index}
    (IM : index -> VLSM message)
    {Hi : Inhabited index}
    (constraint : composite_label IM -> composite_state IM * option message -> Prop)
    {Hsents : forall i, has_been_sent_capability (IM i)}
    {Hobserveds: forall i, has_been_observed_capability (IM i)}
    (clocks : ClocksFor IM)
    (message_time : message -> nat)
  .

  (** This portion of a constraint ensures that messages are received only
      by components at the proper time.

      Perhaps this condition should be added to [MessageTimeProp] and
      required as a property of the components in [IM] rather than
      imposed as a composition constraint.
   *)
  Definition delivery_time_constraint :
    composite_label IM -> composite_state IM * option message -> Prop
    := fun l som =>
         let (i,_) := l in
         let (s,om) := som in
         match om with
         | Some m => message_time m = clock _ (clocks i) (s i)
         | None => True
         end.

  Definition all_earlier_messages_received (i:index) (s:composite_state IM) : Prop :=
    forall msg, (exists (j:index), has_been_sent (IM j) (s j) msg) ->
                message_time msg <= clock _ (clocks i) (s i) ->
                has_been_observed (IM i) (s i) msg.

  (** This portion of a constraint prevents a component from advancing its clock
      if it has not received all oustanding messages from the time
      it is leaving.

      N.B. As written, this does not prevent the possiblity that some
      other component which is still in the earlier time hasn't even
      sent a message yet. Combined with the use of [lt] in
      [all_earlier_messages_received], and the [delivery_time_constraint],
      this component would never be able to advance its clock again
      after such a "late send".
   *)
  Definition timely_reception_constraint:
    composite_label IM -> composite_state IM * option message -> Prop
    := fun l som =>
         let (i,l_i) := l in
         let (s,om) := som in
         let (s',_) := vtransition (IM i) l_i (s i,om) in
         clock _ (clocks i) (s i) < clock _ (clocks i) s'
         -> all_earlier_messages_received i s.

  Context
    (Free := free_composite_vlsm IM)
    (composite_has_been_sent_capability : has_been_sent_capability Free := composite_has_been_sent_capability IM (free_constraint IM) finite_index Hsents)
    .

  Existing Instance composite_has_been_sent_capability.

  (** This strong constraint allows no equivocations and
      no failures of synchrony.
   *)
  Definition no_synch_faults_no_equivocation_constraint :
    composite_label IM -> composite_state IM * option message -> Prop
    := fun l som =>
         no_equivocations Free l som
         /\ delivery_time_constraint l som
         /\ timely_reception_constraint l som.

End StrongSynchrony.
