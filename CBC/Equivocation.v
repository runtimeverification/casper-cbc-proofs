Require Import
  List
  Bool
  Reals
  ListSet
  RelationClasses
  .

From CasperCBC
  Require Import
    Preamble
    CBC.Common
    ListExtras
  .

(**
* An abstract definition of full-node-like equivocation

The definition below defines equivocation and fault-weight on sets
of messages equiped with a [sender], relying on a [message_preceeds_fn]
which can decide whether two messages having the same sender were seen
one before another.

This allows to define that a message is [equivocating_with] another
if they have the same [sender] and are not comparable through
the [message_preceeds_fn].

Then, we can say that a message is [equivocating_in_set] of other messages
if it is [equivocating_with] any of the messages in that set.

This allows us to determine the [equivocating_senders_set] for a given
set of messages as those [sender]s for which there is at least one
message [equivocating_in_set].

The [set_fault_weight] is determined the as the sum of weights in the
[equivocating_senders_set].

We call a message [set_not_heavy] if its corresponding [set_fault_weight]
is lower than the [threshold] set for the class.

_Note_: Ideally [message_preceeds_fn] should determine a strict partial order;
however this might not happen for the whole set of messages, but only
for a restricted set, e.g., [protocol_messsage]s
(please see class [HasPreceedsEquivocation] for more details).
*)

Class HasEquivocation (message : Type) := 
    { V : Type
    ; about_message : StrictlyComparable message
    ; about_V : StrictlyComparable V
    ; measurable_V : Measurable V
    ; reachable_threshold : ReachableThreshold V
    ; sender : message -> V
    ; message_preceeds_fn (m1 m2 : message) : bool
    ; equivocating_with
        (msg1 msg2 : message)  : bool
        :=
        if compare_eq_dec msg1 msg2
        then false
        else if compare_eq_dec (sender msg1) (sender msg2)
          then
            negb (message_preceeds_fn msg1 msg2)
            && negb (message_preceeds_fn msg2 msg1)
          else false
    ; equivocating_in_set
        (msg : message)
        (msgs : set message)
        :=
        existsb (equivocating_with msg) msgs

    ; equivocating_senders_set
        (msgs : set message)
        :=
        set_map compare_eq_dec sender
            (filter (fun msg => equivocating_in_set msg msgs) msgs)
    ; set_fault_weight
        (msgs : set message)
        := 
        sum_weights (equivocating_senders_set msgs)
    ; set_not_heavy
        (msgs : set message)
        :=  (set_fault_weight msgs <= proj1_sig threshold)%R
    }.



