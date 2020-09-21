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
  {about_message : EqDec message}
  {about_V : EqDec validator}
  :=
  { sender : message -> validator
  ; message_preceeds_fn (m1 m2 : message) : bool
  ; equivocating_with
      (msg1 msg2 : message)  : bool
      :=
      if eq_dec msg1 msg2
      then false
      else if eq_dec (sender msg1) (sender msg2)
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
  {|  state_validators := fun s => set_map eq_dec sender (get_messages s)
   ;  state_validators_nodup := fun s => set_map_nodup eq_dec sender (get_messages s)
   ;  is_equivocating_fn := fun s v =>
        let msgs := get_messages s in
        inb eq_dec v
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
        := message_preceeds_fn (proj1_sig pm1) (proj1_sig pm2) = true
    ; protocol_message_preceeds_strict_order
      : StrictOrder protocol_message_preceeds
    ; evidence_of_equivocation
        (pm1 pm2 : byzantine_message X)
        (m1 := proj1_sig pm1)
        (m2 := proj1_sig pm2)
        (Heqv : equivocating_with m1 m2 = true)
        (s : state)
        (tr : list transition_item)
        (Htr : finite_protocol_trace (pre_loaded_vlsm X) s tr)
        (Hm1 : trace_has_message X input m1 tr)
        (Hm2 : trace_has_message X input m2 tr)
        : equivocation_in_trace X m1 tr
        \/ equivocation_in_trace X m2 tr
    }.

End vlsm_message_equivocation_evidence.

Section composite_preceeds_equivocation.

  Context
    {message validator : Type}
    `{Eqv : message_equivocation_evidence message validator}
    {index : Type}
    {IndEqDec : EqDec index}
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
      specialize (constraint_subsumption_pre_loaded_incl IM i0 constraint1 constraint2 Hsubsumption (@Finite _ (type X1) s tr) Htr)
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
