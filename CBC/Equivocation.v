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
    ListSetExtras
  .

  (** * Equivocation definitions **)

  (** ** Basic equivocation **)

  (** Assuming a set of <<state>>s, and a set of <<validator>>s,
  which is [Measurable] and has a [ReachableThreshold], we can define
  [basic_equivocation] starting from a computable [is_equivocating_fn]
  deciding whether a validator is equivocating in a state.

  To avoid a [Finite] constraint on the entire set of validators, we will
  assume that there is a finite set of validators for each state, which
  can be retrieved through the [state_validators] function.
  This can be taken to be entire set of validators when that is finite,
  or the set of senders for all messages in the state for
  [state_encapsulating_messages].

  This allows us to determine the [equivocating_validators] for a given
  state as those equivocating in that state.

  The [equivocation_fault] is determined the as the sum of weights of the
  [equivocating_validators].

  We call a state [not_heavy] if its corresponding [equivocation_fault]
  is lower than the [threshold] set for the <<validator>>s type.
  **)

  Class basic_equivocation
    (state validator : Type)
    {measurable_V : Measurable validator}
    {reachable_threshold : ReachableThreshold validator}
    :=
    { is_equivocating (s : state) (v : validator) : Prop
    ; is_equivocating_dec : RelDecision is_equivocating

      (** retrieves a set containing all possible validators for a state. **)

    ; state_validators (s : state) : set validator

    ; state_validators_nodup : forall (s : state), NoDup (state_validators s)

      (** All validators which are equivocating in a given composite state **)

    ; equivocating_validators
        (s : state)
        : list validator
        := List.filter (fun v => bool_decide (is_equivocating s v)) (state_validators s)

       (** The equivocation fault sum: the sum of the weights of equivocating
       validators **)

    ; equivocation_fault
        (s : state)
        : R
        :=
        sum_weights (equivocating_validators s)

    ; not_heavy
        (s : state)
        :=  (equivocation_fault s <= proj1_sig threshold)%R
   }.

