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
    { is_equivocating_fn (s : state) (v : validator) : bool

      (** retrieves a set containing all possible validators for a state. **)

    ; state_validators (s : state) : set validator

    ; state_validators_nodup : forall (s : state), NoDup (state_validators s)

      (** All validators which are equivocating in a given composite state **)

    ; equivocating_validators
        (s : state)
        : list validator
        := List.filter (is_equivocating_fn s) (state_validators s)

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
  {about_message : StrictlyComparable message}
  {about_V : StrictlyComparable validator}
  :=
  { sender : message -> validator
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
  }.

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

Definition state_encapsulating_messages_equivocation
  (state message validator : Type)
  `{Hstate : state_encapsulating_messages state message}
  `{Hmessage : message_equivocation_evidence message validator}
  {measurable_V : Measurable validator}
  {reachable_threshold : ReachableThreshold validator}
  : basic_equivocation state validator
  :=
  {|  state_validators := fun s => set_map compare_eq_dec sender (get_messages s)
   ;  state_validators_nodup := fun s => set_map_nodup compare_eq_dec sender (get_messages s)
   ;  is_equivocating_fn := fun s v =>
        let msgs := get_messages s in
        inb compare_eq_dec v
          (map sender (filter (fun msg => equivocating_in_set msg msgs) msgs))
  |}.

Section equivocation_properties.

Lemma equivocating_in_set_incl
  {message validator : Type}
  `{Heqv : message_equivocation_evidence message validator}
  (sigma sigma' : set message)
  (Hincl : incl sigma sigma')
  (msg : message)
  (Hmsg : equivocating_in_set msg sigma = true)
  : equivocating_in_set msg sigma' = true.
Proof.
  apply existsb_exists in Hmsg.
  destruct Hmsg as [x [Hin Heq]].
  apply existsb_exists.
  exists x. split; try assumption.
  apply Hincl. assumption.
Qed.

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
  simpl. apply set_map_incl. assumption.
Qed.


Lemma equivocating_validators_incl
  (sigma sigma' : state)
  (Hincl : incl (get_messages sigma) (get_messages sigma'))
  : incl (equivocating_validators sigma) (equivocating_validators sigma').
Proof.
  intros. intros v Hv.
  apply filter_In. apply filter_In in Hv.
  destruct Hv as [Hin Heq].
  apply (state_validators_incl _ sigma') in Hin; try assumption.
  split; try assumption.
  simpl in *. apply in_correct. apply in_correct in Heq.
  apply in_map_iff.
  apply in_map_iff in Heq.
  destruct Heq as [x [Hsender Hfilter]].
  exists x. split; try assumption.
  apply filter_In. apply filter_In in Hfilter.
  destruct Hfilter as [Hx Heq].
  apply Hincl in Hx. split; try assumption.
  apply equivocating_in_set_incl with (get_messages sigma); assumption.
Qed.

Lemma equivocation_fault_incl
  (sigma sigma' : state)
  (Hincl : incl (get_messages sigma) (get_messages sigma'))
  : (equivocation_fault sigma <= equivocation_fault sigma')%R.
Proof.
  intros.
  apply sum_weights_incl
  ; try (apply NoDup_filter; apply state_validators_nodup).
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
  simpl. rewrite Hempty. simpl.
  destruct threshold.
  simpl.
  apply Rge_le in r.
  assumption.
Qed.

End equivocation_properties.
