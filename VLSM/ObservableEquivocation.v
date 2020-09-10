Require Import List ListSet FinFun Wf_nat.
Import ListNotations.
From CasperCBC
  Require Import
    Preamble ListExtras ListSetExtras
    CBC.Common CBC.Equivocation
    VLSM.Common VLSM.Composition VLSM.Equivocation
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
Let us now factor [VLSM]s into the event observability framework.

[message_observable_events] can be extracted from any message.
*)
Class composite_vlsm_observable_messages
  :=
  {
(**
To simplify the presentation, we assume that no events can be observed in
initial states.
*)
    no_events_in_initial_state
      (s : state)
      (His : vinitial_state_prop X s)
      (v : validator)
      : observable_events s v = [];

(**
We assume that machines communicate through messages,
and that messages can carry some of the information of their originating
states.

To formalize that, we willl assume a function [message_observable_events]
yielding the events which can be observed in a message for a validator,
and we will require that we cannot observe in a sent message events which
were not available in the transition that generated it
([message_observable_consistency]).
*)
    message_observable_events : message -> validator -> set event;
    message_observable_consistency
      (m : message)
      (v : validator)
      (som : state * option message)
      (l : label)
      (s : state)
      (Ht : protocol_transition X l som (s, Some m))
      : incl (message_observable_events m v) (observable_events (s (projT1 l)) v);

    option_message_observable_events
      (om : option message)
      (v : validator)
      : set event
      :=
      match om with
      | Some m => message_observable_events m v
      | None => []
      end;

(**
We'll also assume a weak form of [unforgeability]: that a machine can only
produce events for its own validator; for other validators it can only
gather information through the messages it receives.
*)
    unforgeability
      (s s' : state)
      (om om' : option message)
      (l : label)
      (Ht : protocol_transition X l (s, om) (s', om'))
      (i := projT1 l)
      (v : validator)
      (Hv : A v <> i)
      : incl
        (observable_events (s' i) v)
        (observable_events (s i) v ++ option_message_observable_events om v);
  }.

Context
  {Hcomposite : composite_vlsm_observable_messages}
  {message_eq : EqDec message}
  .

Lemma in_observable_events_first
  (is : vstate X)
  (tr : list (vtransition_item X))
  (Htr : finite_protocol_trace X is tr)
  (v : validator)
  (e : event)
  (s := last (map destination tr) is)
  (He : In e (observable_events s v))
  : exists
    (pre suf : list transition_item)
    (item : transition_item)
    (Heq : tr = pre ++ [item] ++ suf)
    (He' : In e (observable_events (destination item) v)),
    Forall (fun item => ~In e (observable_events (destination item) v)) pre.
Proof.
  assert (Htr0 : tr = [] \/ tr <> [])
    by (destruct tr; (left; reflexivity) || (right; intro contra; discriminate contra)).
  destruct Htr0 as [Htr0 | Htr0].
  - subst tr. destruct Htr as [Htr His].
    specialize (no_events_in_initial_state (last (map destination []) is) His v) as Hno.
    replace
      (observable_events (last (map destination []) is) v)
      with (@nil event) in He.
    inversion He.
  - destruct (exists_last Htr0) as [l' [a Heq]].
    specialize
      (existsb_first tr (fun item => inb eq_dec e (observable_events (destination item) v)))
      as Hfirst.
    spec Hfirst.
    + apply existsb_exists. exists a.
      split.
      * subst tr. apply in_app_iff. right. left. reflexivity.
      * apply in_correct.
        unfold s in *. clear s. rewrite Heq in He.
        rewrite map_app in He. simpl in He. rewrite last_last in He.
        assumption.
    + destruct Hfirst as [pre [suf [a' [He' [Heq' Hfirst]]]]].
      apply in_correct in He'.
      rewrite existsb_forall in Hfirst.
      exists pre. exists suf. exists a'. exists Heq'. exists He'.
      apply Forall_forall.
      intros x Hx.
      specialize (Hfirst x Hx).
      apply in_correct' in Hfirst.
      assumption.
Qed.

(**
We call [trace_generated_event] a new event for validator <<v>> which
appeared as result of a transition in a trace, that is, which it was
not in the state prior to the transition, nor in the received message,
but it is in the state resulted after the transition.
*)
  Definition trace_generated_event
    (is : vstate X)
    (tr : list (vtransition_item X))
    (v : validator)
    (e : event)
    : Prop
    :=
    exists
    (prefix suffix : list transition_item)
    (item : transition_item)
    (Heq : tr = prefix ++ [item] ++ suffix)
    (i := projT1 (l item))
    (s := last (map destination prefix) is)
    (s' := destination item),
    In e
      (set_diff eq_dec
        (observable_events (s' i) v)
        (set_union eq_dec
          (observable_events (s i) v)
          (option_message_observable_events (input item) v)
        )
      ).

(**
If a new event is [trace_generated_event] for a validator, then it must be
that it's generated by the machine corresponding to that validator.
*)
Lemma trace_generated_index
  (is : vstate X)
  (tr : list (vtransition_item X))
  (Htr : finite_protocol_trace X is tr)
  (v : validator)
  (e : event)
  (prefix suffix : list transition_item)
  (item : transition_item)
  (Heq : tr = prefix ++ [item] ++ suffix)
  (i := projT1 (l item))
  (s := last (map destination prefix) is)
  (s' := destination item)
  (He : In e
      (set_diff eq_dec
        (observable_events (s' i) v)
        (set_union eq_dec
          (observable_events (s i) v)
          (option_message_observable_events (input item) v)
        )
      )
  )
  : A v = i.
Proof.
  destruct (eq_dec (A v) i); try assumption.
  specialize (protocol_transition_to X is item tr prefix suffix Heq (proj1 Htr)).
  intro Hpt.
  specialize (unforgeability s s' (input item) (output item) (l item) Hpt v n) as Hincl.
  apply set_diff_iff in He.
  destruct He as [He Hne].
  apply Hincl in He. apply in_app_iff in He. elim Hne.
  apply set_union_iff. assumption.
Qed.

Definition trace_generated_event_fn
  (is : vstate X)
  (tr : list (vtransition_item X))
  (v : validator)
  (e : event)
  : bool
  :=
  existsb
    (fun t : list (vtransition_item X) * vtransition_item X * list (vtransition_item X) =>
      match t with (pre, item, _) =>
        let i := projT1 (l item) in
          let s := last (map destination pre) is in
          let s' := destination item in
          inb eq_dec e
            (set_diff eq_dec
              (observable_events (s' i) v)
              (set_union eq_dec
                (observable_events (s i) v)
                (option_message_observable_events (input item) v)
              )
            )
      end
    )
    (one_element_decompositions tr).

Lemma trace_generated_event_function
  (is : vstate X)
  (tr : list (vtransition_item X))
  (v : validator)
  (e : event)
  : trace_generated_event is tr v e <->
  trace_generated_event_fn is tr v e = true.
Proof.
  split.
  - intros [pre [suf [item [Heq Hin]]]]. simpl in Hin.
    unfold trace_generated_event_fn. apply existsb_exists.
    exists (pre, item, suf).
    symmetry in Heq. apply in_one_element_decompositions_iff in Heq.
    split; try assumption.
    apply in_correct. assumption.
  - intro H. apply existsb_exists in H.
    destruct H as [((pre, item), suf) [Hdec H]].
    simpl in H. apply in_correct in H.
    apply in_one_element_decompositions_iff in Hdec. symmetry in Hdec.
    exists pre. exists suf. exists item. exists Hdec. assumption.
Qed.

Lemma trace_generated_prefix
  (is : vstate X)
  (pre : list (vtransition_item X))
  (v : validator)
  (e : event)
  (Hgen : trace_generated_event is pre v e)
  (suf : list transition_item)
  : trace_generated_event is (pre ++ suf) v e.
Proof.
  destruct Hgen as [pre' [suf' [item [Heq Hgen]]]].
  exists pre'. exists (suf' ++ suf). exists item.
  subst pre. repeat rewrite <- app_assoc. exists eq_refl. assumption.
Qed.

Lemma not_trace_generated_prefix
  (is : vstate X)
  (pre : list (vtransition_item X))
  (v : validator)
  (e : event)
  (suf : list transition_item)
  (Hngen : ~trace_generated_event is (pre ++ suf) v e)
  : ~trace_generated_event is pre v e.
Proof.
  intro contra. elim Hngen. apply trace_generated_prefix. assumption.
Qed.

Lemma not_trace_generated_event
  (is : vstate X)
  (tr : list (vtransition_item X))
  (v : validator)
  (e : event)
  (Hne : ~trace_generated_event is tr v e)
  (prefix suffix : list transition_item)
  (item : transition_item)
  (Heq : tr = prefix ++ [item] ++ suffix)
  (i := projT1 (l item))
  (s := last (map destination prefix) is)
  (s' := destination item)
  (Hin : In e (observable_events (s' i) v))
  : In e (observable_events (s i) v)
  \/ In e (option_message_observable_events (input item) v).
Proof.
  destruct (trace_generated_event_fn is tr v e) eqn:Hne'.
  - apply trace_generated_event_function in Hne'. elim Hne. assumption.
  - unfold trace_generated_event_fn in Hne'. rewrite existsb_forall in Hne'.
    specialize (Hne' (prefix, item, suffix)).
    rewrite in_one_element_decompositions_iff in Hne'. symmetry in Heq.
    specialize (Hne' Heq).
    apply in_correct' in Hne'.
    rewrite set_diff_iff in Hne'.
    rewrite set_union_iff in Hne'.
    repeat rewrite in_correct in Hne'. rewrite <- in_correct in Hne'.
    rewrite <- Bool.orb_true_iff in Hne'.
    repeat rewrite in_correct.
    rewrite <- Bool.orb_true_iff.
    unfold s. unfold s'. unfold i.
    destruct
      (inb eq_dec e
        (observable_events (last (map destination prefix) is (projT1 (l item))) v)
      || inb eq_dec e (option_message_observable_events (input item) v)
      )%bool
      eqn:Hor; try reflexivity.
    elim Hne'. split; try assumption. intro contra. discriminate contra.
Qed.

(**
We say that an equivocation of validator <<v>> can be observed in the
last state <<s>> of a trace ([equivocating_trace_last]) if there is an
[observable_event] for <<v>> in s, which was no [trace_generated_event]
in the same trace.
*)
Definition equivocating_in_trace_last
  (is : vstate X)
  (tr : list transition_item)
  (s := last (map destination tr) is)
  (v : validator)
  : Prop
  :=
  exists
    (e : event)
    (He : In e (observable_events s v)),
    ~ trace_generated_event is tr v e.

Definition equivocating_in_trace_last_fn
  (is : vstate X)
  (tr : list transition_item)
  (s := last (map destination tr) is)
  (v : validator)
  : bool
  :=
  existsb
    (fun e : event =>
      negb (trace_generated_event_fn is tr v e)
    )
    (observable_events s v).

Lemma equivocating_in_trace_last_function
  (is : vstate X)
  (tr : list transition_item)
  (v : validator)
  : equivocating_in_trace_last is tr v
  <-> equivocating_in_trace_last_fn is tr v = true.
Proof.
  split.
  - intros [e [He Hnobs]].
    unfold equivocating_in_trace_last_fn.
    apply existsb_exists. exists e. split; try assumption.
    destruct (trace_generated_event_fn is tr v e) eqn:H; try reflexivity.
    elim Hnobs. apply trace_generated_event_function. assumption.
  - intro H. apply existsb_exists in H.
    destruct H as [e [Hin H]].
    exists e. exists Hin.
    intro contra. apply trace_generated_event_function in contra.
    rewrite contra in H. simpl in H. discriminate H.
Qed.

Lemma not_equivocating_in_trace_last_initial
  (s : vstate X)
  (Hs : vinitial_state_prop X s)
  (v : validator)
  : ~ equivocating_in_trace_last s [] v.
Proof.
  intro contra. destruct contra as [e [He Hne]].
  specialize (no_events_in_initial_state (last (map destination []) s) Hs v) as Hno.
  replace
    (observable_events (last (map destination []) s) v)
    with (@nil event) in He.
  inversion He.
Qed.

(**
We say that <<v>> is [equivocating_in_trace] <<tr>> if there is
a prefix of <<tr>> such that v is [equivocating_trace_last] w.r.t. that
prefix.
*)

Definition equivocating_in_trace
  (tr : protocol_trace X)
  (v : validator)
  : Prop
  :=
  exists
    (prefix : list transition_item)
    (last : transition_item)
    (Hpr : trace_prefix X (proj1_sig tr) last prefix),
    equivocating_in_trace_last (trace_first (proj1_sig tr)) prefix v.

(**
We say that <<v>> is [equivocating_in_all_traces_ending_in_state] <<s>> if it is
[equivocating_in_trace_last] w.r.t. all [protocol_trace]s ending in <<s>>.
*)

Definition equivocating_in_all_traces_ending_in_state
  (s : protocol_state X)
  (v : validator)
  : Prop
  := forall
    (is : vstate X)
    (tr : list transition_item)
    (Htr : finite_protocol_trace X is tr)
    (Hlast : last (map destination tr) is = proj1_sig s),
    equivocating_in_trace_last is tr v.

Definition not_equivocating_in_some_traces_ending_in_state
  (s : protocol_state X)
  (v : validator)
  : Prop
  := exists
    (is : vstate X)
    (tr : list transition_item)
    (Htr : finite_protocol_trace X is tr)
    (Hlast : last (map destination tr) is = proj1_sig s),
    ~equivocating_in_trace_last is tr v.

Lemma event_equivocation_implies_message_equivocation
  (is : vstate X)
  (tr : list transition_item)
  (Htr : finite_protocol_trace X is tr)
  (v : validator)
  (Heqv : equivocating_in_trace_last is tr v)
  : exists (m : message), VLSM.Equivocation.equivocation_in_trace X m tr.
Proof.
  destruct Heqv as [e [He Hne]].
  apply in_observable_events_first in He; try assumption.
  destruct He as [pre [suf [item [Heq [He Hpre]]]]].
  rewrite app_assoc in Heq.
  subst tr.
  apply not_trace_generated_prefix in Hne.
  destruct Htr as [Htr His].
  apply finite_protocol_trace_from_app_iff in Htr.
  destruct Htr as [Htr _].
  rewrite Forall_forall in Hpre.
  apply finite_protocol_trace_from_app_iff in Htr.
  destruct Htr as [Htr Ht].
  inversion Ht. subst item tl s'. clear Ht H2. simpl in He.
  apply set_union_in_iterated in He. apply Exists_exists in He.
  destruct He as [esi [Hesi He]].
  apply in_map_iff in Hesi.
  destruct Hesi as [i [Hesi Hi]]. subst esi.
  assert (Hnpre : ~In e (observable_events (last (map destination pre) is) v)).
  { assert (Hpre0: pre = [] \/ pre <> [])
      by (destruct pre; (left; reflexivity) || (right; intro contra; discriminate contra)).
    destruct Hpre0 as [Hpre0 | Hpre0].
    - subst pre. simpl.
      specialize (no_events_in_initial_state is His v) as Hno.
      replace (composed_observable_events is v) with (@nil event).
      intro contra. inversion contra. 
    - destruct (exists_last Hpre0) as [pre' [item' Heq']].
      subst pre.
      rewrite map_app. simpl. rewrite last_last.
      apply (Hpre item').
      apply in_app_iff. right. left. reflexivity.
  }
  assert (Hnei : ~In e (observable_events (last (map destination pre) is (projT1 l)) v)).
  { intro contra. elim Hnpre. simpl.
    simpl. apply set_union_in_iterated. apply Exists_exists.
    exists (observable_events (last (map destination pre) is (projT1 l)) v).
    split; try assumption.
    apply in_map_iff. exists (projT1 l). split; try reflexivity.
    apply (proj2 finite_index).
  }
  destruct (eq_dec i (projT1 l)).
  - specialize
    (not_trace_generated_event _ _ _ _ Hne
      pre [] {| l := l; input := iom; destination := s; output := oom |}
      eq_refl
    ) as Hng.
    simpl in Hng. subst i. specialize (Hng He).
    destruct Hng as [Hng | Hng]; try (elim Hnei; assumption).
    destruct iom as [m|]; try inversion Hng.
    exists m.
    exists pre. exists suf. exists {| l := l; input := Some m; destination := s; output := oom |}.
    rewrite <- app_assoc. repeat split; try reflexivity.
    intro contra.
    apply in_map_iff in contra.
    destruct contra as [item' [Hout Hitem']].
    specialize (Hpre item' Hitem').
    elim Hpre.
    apply in_split in Hitem'.
    destruct Hitem' as [pre' [suf' Hitem']].
    subst pre.
    apply finite_protocol_trace_from_app_iff in Htr.
    destruct Htr as [_ Htr]. inversion Htr.
    subst s' item' tl. simpl in Hout. subst oom0.
    simpl.
    apply (message_observable_consistency m v _ _ _ H4) in Hng.
    simpl. apply set_union_in_iterated. apply Exists_exists.
    exists (observable_events (s0 (projT1 l0)) v).
    split; try assumption.
    apply in_map_iff. exists (projT1 l0). split; try reflexivity.
    apply (proj2 finite_index).
  - replace (s i) with (last (map destination pre) is i) in He.
    + elim Hnpre.
      simpl. apply set_union_in_iterated. apply Exists_exists.
      exists (observable_events (last (map destination pre) is i) v).
      split; try assumption.
      apply in_map_iff. exists i. split; try reflexivity. assumption.
    + symmetry. apply (composite_transition_state_neq _ _ _ _ _ _ _ H3 _ n).
Qed.

Lemma event_equivocation_implies_message_equivocation_converse
  (is : vstate X)
  (tr : list transition_item)
  (Htr : finite_protocol_trace X is tr)
  (Hneqv : forall (m : message), ~VLSM.Equivocation.equivocation_in_trace X m tr)
  (v : validator)
  : ~equivocating_in_trace_last is tr v.
Proof.
  intro contra.
  apply event_equivocation_implies_message_equivocation in contra; try assumption.
  destruct contra as [m contra].
  elim (Hneqv m). assumption.
Qed.

(**
The class below links [composite_vlsm_observable_messages] with 
[computable_observable_equivocation_evidence] by requiring that all
[trace_generated_event]s for the same validator are [comparable] through
the [happens_before_fn].
*)
Class composite_vlsm_comparable_generated_events
  :=
  {
    comparable_generated_events
      (is : vstate X)
      (tr : list transition_item)
      (Htr : finite_protocol_trace X is tr)
      (v : validator)
      (e1 e2 : event)
      (He1 : trace_generated_event is tr v e1)
      (He2 : trace_generated_event is tr v e2)
      : comparableb happens_before_fn e1 e2 = true;
  }.

Context
  {Hcomparable_generated_events : composite_vlsm_comparable_generated_events}.

Lemma uncomparable_with_generated_event_equivocation
  (is : vstate X)
  (tr : list transition_item)
  (Htr : finite_protocol_trace X is tr)
  (v : validator)
  (e1 e2 : event)
  (s := last (map destination tr) is)
  (He1 : In e1 (observable_events s v))
  (He2 : In e2 (observable_events s v))
  (Hnc : comparableb happens_before_fn e1 e2 = false)
  (Hgen1 : trace_generated_event is tr v e1)
  : equivocating_in_trace_last is tr v.
Proof.
  destruct (trace_generated_event_fn is tr v e2) eqn:Hgen2.
  - apply trace_generated_event_function in Hgen2.
    specialize (comparable_generated_events is tr Htr v e1 e2 Hgen1 Hgen2) as Hc.
    rewrite Hc in Hnc. discriminate Hnc.
  - exists e2. exists He2. intro contra.
    apply trace_generated_event_function in contra.
    rewrite Hgen2 in contra. discriminate contra.
Qed.

(**
Finally, we tie the [computable_observable_equivocation_evidence] notion
to that of [composite_vlsm_observable_equivocation] by showing that
the existence of two events observable for a validator <<v>> in a state <<s>>
which are not [comparable] w.r.t. [happens_before_fn] relation guarantees
that <<v>> is [equivocating_in_all_traces_ending_in_state] <<s>>.
*)
Lemma evidence_implies_equivocation
  (s : vstate X)
  (Hs : protocol_state_prop X s)
  (v : validator)
  (e1 e2 : event)
  (He1 : In e1 (observable_events s v))
  (He2 : In e2 (observable_events s v))
  (Heqv : comparableb happens_before_fn e1 e2 = false)
  : equivocating_in_all_traces_ending_in_state (exist _ s Hs) v.
Proof.
  intro is; intros. simpl in Hlast.
  subst s.
  destruct (trace_generated_event_fn is tr v e1) eqn:Hgen1.
  - apply uncomparable_with_generated_event_equivocation with e1 e2
    ; try assumption.
    apply trace_generated_event_function. assumption.
  - exists e1. exists He1. intro contra.
    apply trace_generated_event_function in contra.
    rewrite Hgen1 in contra. discriminate contra.
Qed.

Lemma evidence_implies_equivocation_converse
  (s : vstate X)
  (Hs : protocol_state_prop X s)
  (v : validator)
  (Hneqv : not_equivocating_in_some_traces_ending_in_state (exist _ s Hs) v)
  (e1 e2 : event)
  (He1 : In e1 (observable_events s v))
  (He2 : In e2 (observable_events s v))
  : comparableb happens_before_fn e1 e2 = true.
Proof.
  destruct (comparableb happens_before_fn e1 e2) eqn:Hcmp; try reflexivity.
  specialize (evidence_implies_equivocation s Hs v e1 e2 He1 He2 Hcmp)
    as Heqv.
  destruct Hneqv as [is [tr [Htr [Hlast Hneqv]]]].
  specialize (Heqv is tr Htr Hlast). elim Hneqv. assumption.
Qed.

Lemma no_equivocation_constraint_implies_no_equivocations
  (Hbs : forall i : index, has_been_sent_capability (IM i))
  (Hno_equiv : constraint_subsumption IM constraint (no_equivocations IM i0 constraint Hbs))
  (s : vstate X)
  (Hs : protocol_state_prop X s)
  (v : validator)
  : not_equivocating_in_some_traces_ending_in_state (exist _ s Hs) v.
Proof.
  destruct Hs as [_om Hs].
  destruct (protocol_is_trace X s _om Hs) as [Hinit | [is [tr [Htr [Hlast _]]]]].
  - exists s. exists [].
    repeat split; try assumption.
    + constructor. apply initial_is_protocol. assumption.
    + apply not_equivocating_in_trace_last_initial. assumption.
  - exists is. exists tr. exists Htr.
    split.
    + simpl.
      unfold option_map in Hlast.
      destruct (last_error tr) eqn : eq; try discriminate Hlast.
      inversion Hlast.
      unfold last_error in eq.
      destruct tr; try discriminate eq.
      inversion eq.
      rewrite last_map. reflexivity.
    + intro contra.
      apply event_equivocation_implies_message_equivocation in contra; try assumption.
      destruct contra as [m [pre [suf [item [Heq [Hinput contra]]]]]].
      subst tr.
      destruct Htr as [Htr Hinit].
      apply finite_protocol_trace_from_app_iff in Htr.
      destruct Htr as [_ Htr].
      inversion Htr.
Admitted.



(**
Since an initial state has no observable events, it follows that it
cannot be equivocating for any validator.
*)
Lemma no_equivocation_in_initial_state
  (is : vstate X)
  (Hs : vinitial_state_prop X is)
  (v : validator)
  (Hps := initial_is_protocol X is Hs)
  : ~ equivocating_in_all_traces_ending_in_state (exist _ is Hps) v.
Proof.
  intro contra.
  specialize (contra is []).
  spec contra.
  { split; try assumption. constructor. assumption. }
  specialize (contra eq_refl).
  destruct contra as [e [He _]]. simpl in He.
  specialize (no_events_in_initial_state is Hs v) as Heis.
  simpl in Heis. rewrite Heis in He. inversion He.
Qed.

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

(*
Given a trace ending in composite state <<s>> and an event <<e>> in the
[observable_events] of <<s i>> for validator <<v>>, an
[observable_event_witness] is a decomposition of the trace in which a
message where <<e>> is observable is sent before being received in the
component <<i>>.

Definition observable_event_witness
  (tr : list (vtransition_item X))
  (v : validator)
  (e : event)
  (i : index)
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
    In e (message_observable_events m v).

Definition observable_event_witness_fn
  (tr : list (vtransition_item X))
  (v : validator)
  (e : event)
  (i : index)
  : bool
  :=
  inb eq_dec e
    (flat_map
      (fun t : list transition_item * vtransition_item X * list transition_item * vtransition_item X * list transition_item =>
        match t with (_,sitem,_,ritem,_) =>
          if eq_dec i (projT1 (l ritem)) then
            match output sitem, input ritem with
            | Some m, Some m' =>
              if eq_dec m m' then message_observable_events m v else []
            | _, _ => []
            end
          else []
        end
      )
      (two_element_decompositions tr)
    ).

Lemma observable_event_witness_function
  (tr : list transition_item)
  (v : validator)
  (e : event)
  (i : index)
  : observable_event_witness tr v e i
  <-> observable_event_witness_fn tr v e i = true.
Proof.
  split.
  - intros [prefix [middle [suffix [sitem [ritem
      [Heq [m [Hsent [Hreceived [Hreceived_by_i Hin]]]]]]]]]].
    unfold observable_event_witness_fn.
    apply in_correct. apply in_flat_map.
    exists (prefix, sitem, middle, ritem, suffix).
    symmetry in Heq. apply in_two_element_decompositions_iff in Heq.
    split; try assumption.
    symmetry in Hreceived_by_i.
    rewrite eq_dec_if_true; try assumption.
    rewrite Hsent. rewrite Hreceived.
    rewrite eq_dec_if_true; try reflexivity.
    assumption.
  - unfold observable_event_witness_fn. intro H.
    apply in_correct in H. apply in_flat_map in H.
    destruct H as [((((pre, x), mid), y), suf) [Heq H]].
    exists pre. exists mid. exists suf. exists x. exists y.
    apply in_two_element_decompositions_iff in Heq.
    symmetry in Heq. exists Heq.
    destruct (eq_dec i (projT1 (l y))); try inversion H.
    destruct (output x) eqn:Hout; try inversion H.
    destruct (input y) eqn:Hin; try inversion H.
    destruct (eq_dec m m0); try inversion H.
    subst m0. exists m. exists eq_refl. exists eq_refl.
    symmetry in e0. exists e0. assumption.
Qed.

Lemma observable_event_witness_generated
  (is : vstate X)
  (tr : list (vtransition_item X))
  (s := last (map destination tr) is)
  (v : validator)
  (e : event)
  (i : index)
  (He : In e (observable_events (s i) v))
  (Hwitness : observable_event_witness tr v e i)
  : trace_generated_event is tr v e.
Proof.
  destruct Hwitness as
    [prefix [middle [suffix [sitem [ritem
      [Heq [m [Hsent [Hreceived [Hreceived_by_i Hin]]]]]]]]]].
*)

End message_observable_equivocation_equivalent_defnitions.