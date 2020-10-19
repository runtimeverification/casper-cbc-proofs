Require Import List ListSet FinFun
  Reals.
Import ListNotations.
From CasperCBC
  Require Import
    Preamble ListExtras ListSetExtras
    CBC.Common CBC.Equivocation
    VLSM.Common VLSM.Composition VLSM.Equivocation
    VLSM.ProjectionTraces
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

Class observation_based_equivocation_evidence
  (state validator event : Type)
  (event_eq : EqDecision event)
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

(** We can use this notion of [observation_based_equivocation_evidence]
to obtain the [basic_equivocation] between states and validators.
*)
Definition basic_observable_equivocation
  (state validator event : Type)
  `{EqDecision event}
  {event_comparable : comparable_events event}
  {Hevidence : observation_based_equivocation_evidence state validator event decide_eq event_comparable}
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

Section not_heavy_incl.

Context
  (state validator event : Type)
  `{EqDecision event}
  (v_eq : EqDecision validator)
  {event_comparable : comparable_events event}
  {Hevidence : observation_based_equivocation_evidence state validator event decide_eq event_comparable}
  {measurable_V : Measurable validator}
  {reachable_threshold : ReachableThreshold validator}
  (validators : state -> set validator)
  (validators_nodup : forall (s : state), NoDup (validators s))
  (basic_eqv := basic_observable_equivocation state validator event validators validators_nodup)
  .

Existing Instance basic_eqv.

Lemma equivocation_fault_incl
  (sigma sigma' : state)
  (Hincl_validators : incl (validators sigma) (validators sigma'))
  (Hincl : forall v : validator, incl (observable_events sigma v) (observable_events sigma' v))
  : (equivocation_fault sigma <= equivocation_fault sigma')%R.
Proof.
  intros.
  unfold equivocation_fault.
  unfold equivocating_validators.
  apply sum_weights_incl; try (apply NoDup_filter; apply state_validators_nodup).
  apply incl_tran with (filter (is_equivocating_fn sigma') (state_validators sigma))
  ; try (apply filter_incl; assumption).
  apply filter_incl_fn.
  intro v. spec Hincl v. simpl. unfold equivocation_evidence.
  repeat rewrite existsb_exists. intros [e1 [He1 He2]]. exists e1.
  split; try (apply Hincl; assumption).
  rewrite existsb_exists in *. destruct He2 as [e2 [He2 Heqv]]. exists e2.
  split; try apply Hincl; assumption.
Qed.

(* If a state is not overweight, none of its subsets are *)
Lemma not_heavy_incl
  (sigma sigma' : state)
  (Hincl_validators : incl (validators sigma) (validators sigma'))
  (Hincl : forall v : validator, incl (observable_events sigma v) (observable_events sigma' v))
  (Hsigma' : not_heavy sigma')
  : not_heavy sigma.
Proof.
  apply Rle_trans with (equivocation_fault sigma'); try assumption.
  apply equivocation_fault_incl; assumption.
Qed.

End not_heavy_incl.

Section observable_equivocation_in_composition.

(** ** Observable messages in a VLSM composition

We assume a composition of [VLSM]s where each machine has a way to
produce [observation_based_equivocation_evidence].
*)


Context
  {message validator event : Type}
  `{EqDecision event}
  {event_comparable : comparable_events event}
  {index : Type}
  `{EqDecision index}
  (index_listing : list index)
  (finite_index : Listing index_listing)
  (IM : index -> VLSM message)
  (Hevidence : forall (i : index),
    observation_based_equivocation_evidence
        (vstate (IM i)) validator event decide_eq event_comparable
  )
  (i0 : index)
  (constraint : composite_label IM -> composite_state IM * option message -> Prop)
  (X := composite_vlsm IM i0 constraint)
  (PreX := pre_loaded_with_all_messages_vlsm X)
  .

(**
It is easy to define a [observation_based_equivocation_evidence] mechanism for
the composition, by just defining the [observable_events] for the composite state
to be the union of [observable_events] for each of the component states.
*)

Definition composed_observable_events
  (s : composite_state IM)
  (v : validator)
  : set event
  :=
  fold_right (set_union decide_eq) [] (map (fun i => observable_events (s i) v) index_listing).

Definition composed_observation_based_equivocation_evidence
  : observation_based_equivocation_evidence (composite_state IM) validator event decide_eq event_comparable
  :=
  {| observable_events := composed_observable_events |}.

Existing Instance composed_observation_based_equivocation_evidence.

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
  }.

Context
  {Hcomposite : composite_vlsm_observable_messages}
  `{EqDecision message}
  .

Definition option_message_observable_events
  (om : option message)
  (v : validator)
  : set event
  :=
  match om with
  | Some m => message_observable_events m v
  | None => []
  end.

(**
An useful result, corollary of the abstract [existsb_first] says that if
an event is observed into the final state of a trace, there must be a
prefix of the trace with the same property and no prior observation of
the event.
*)
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
      (existsb_first tr (fun item => inb decide_eq e (observable_events (destination item) v)))
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

(** ** Defining observable equivocation based on observable messages
*)

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
    (set_diff decide_eq
      (observable_events (s' i) v)
      (set_union decide_eq
        (observable_events (s i) v)
        (option_message_observable_events (input item) v)
      )
    ).

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
          inb decide_eq e
            (set_diff decide_eq
              (observable_events (s' i) v)
              (set_union decide_eq
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

(**
If an event is generated by a trace <<tr>>, then it's also generated by
any trace having <<tr>> as a prefix.
*)
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

(**
Conversely, if an event is not generated by a trace, then it's not
generated by any of its prefixes.
*)
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

(**
An event which was not generated prior to reaching a trace, but it is
observable in its final state must come from the previous state or
the incoming message.
*)
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
      (inb decide_eq e
        (observable_events (last (map destination prefix) is (projT1 (l item))) v)
      || inb decide_eq e (option_message_observable_events (input item) v)
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

(**
Since the initial state has no events, no equivocations can exist in an
empty protocol trace.
*)
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

(**
Next property holds for states <<s>> and validators <<v>> for which there
exists at least one trace ending in <<s>> and not equivocating in <<v>>.
*)
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

(**
Next property holds for states <<s>> and validators <<v>> for which
all protocol traces ending in <<s>> are not equivocating in <<v>>.
*)
Definition not_equivocating_in_all_traces_ending_in_state
  (s : protocol_state X)
  (v : validator)
  : Prop
  := forall
    (is : vstate X)
    (tr : list transition_item)
    (Htr : finite_protocol_trace X is tr)
    (Hlast : last (map destination tr) is = proj1_sig s),
    ~equivocating_in_trace_last is tr v.

(**
Given that each protocol state has a witness trace, it follow that
[not_equivocating_in_all_traces_ending_in_state] implies
[not_equivocating_in_some_traces_ending_in_state].
*)
Lemma not_equivocating_in_traces_ending_in_state
  (s : protocol_state X)
  (v : validator)
  (Hall : not_equivocating_in_all_traces_ending_in_state s v)
  : not_equivocating_in_some_traces_ending_in_state s v.
Proof.
  destruct s as [s [_om Hs]].
  destruct (protocol_is_trace X s _om Hs) as [Hinit | [is [tr [Htr [Hlast _]]]]].
  - exists s. exists [].
    repeat split; try assumption.
    + constructor. apply initial_is_protocol. assumption.
    + apply not_equivocating_in_trace_last_initial. assumption.
  - assert (Hlst := last_error_destination_last tr s Hlast is).
    exists is. exists tr. exists Htr. exists Hlst.
    specialize (Hall is tr Htr Hlst). assumption.
Qed.

(** ** Linking observable equivocation to message-based equivocation
*)

(**
This shows that if there exists an event which is observable for a
validator <<v>> in the last state of a trace but which was not generated
by <<v>> during the trace [equivocating_in_trace_last], then there exists
a message <<m>> which was received but not sent in the trace
[VLSM.Equivocation.equivocation_in_trace].

Note that this result does not guarantee that the sender of <<m>> is <<v>>.
To achieve that we would need additional [unforgeable_messages] assumptions.
*)
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
  destruct (decide (i = (projT1 l))).
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

(**
The counter-positive of the above: if there exists no message <<m>> which
was received but not sent in the trace, then, for any validator <<v>>
there exists no event which is observable for <<v>> but not generated
during the trace.
*)
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

(** ** Linking evidence of equivocation with observable equivocation
*)


(**
The class below links [composite_vlsm_observable_messages] with
[observation_based_equivocation_evidence] by requiring that all
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

(**
A helping lemma: if two events obsevable for <<v>> in the last state of
a protocol trace are uncomparable and one of them is generated, then
there exists an equivocation (the other cannot be).
*)
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
We now tie the [observation_based_equivocation_evidence] notion
to that of [composite_vlsm_comparable_generated_events] by showing that
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

(**
The counter-positive of the above says that if there exists a trace
leading to <<s>> which is not equivocating, then all events observed
for <<v>> in <<s>> must be comparable w.r.t. the [happens_before_fn].
*)
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

(** ** No-equivocation composition constraint guarantees no equivocations
*)

(**
If the composition constraint subsumes the no-equivocations constraint,
then all observable events for a validator are comparable w.r.t.
the [happens_before_fn].
*)
Lemma no_equivocation_constraint_implies_no_equivocations
  (Hbs : forall i : index, has_been_sent_capability (IM i))
  (Hno_equiv : constraint_subsumption IM constraint (no_equivocations IM i0 constraint Hbs))
  (s : vstate X)
  (Hs : protocol_state_prop X s)
  (v : validator)
  : not_equivocating_in_all_traces_ending_in_state (exist _ s Hs) v.
Proof.
  intro is; intros. simpl in Hlast.
  intro contra.
  apply event_equivocation_implies_message_equivocation in contra; try assumption.
  destruct contra as [m [pre [suf [item [Heq [Hinput contra]]]]]].
  subst tr.
  destruct Htr as [Htr Hinit].
  apply finite_protocol_trace_from_app_iff in Htr.
  destruct Htr as [Hpre Htr].
  inversion Htr.
  subst. simpl in Hinput. subst.
  destruct H3 as [[Hps [Hpm [Hv Hconstr]]] Ht].
  apply Hno_equiv in Hconstr. simpl in Hconstr.
  unfold equivocation in Hconstr.
  assert
    (Hconstr' :
      existsb (fun i : index => has_been_sent (IM i) (last (map destination pre) is i) m) index_listing = true).
  { destruct (existsb (fun i : index => has_been_sent (IM i) (last (map destination pre) is i) m) index_listing)
      eqn: Hexist; try reflexivity.
    rewrite existsb_forall in Hexist.
    elim Hconstr.
    intro i.
    specialize (Hexist i (proj2 finite_index i)).
    unfold has_not_been_sent. apply Bool.negb_true_iff. assumption.
  }
  apply existsb_exists in Hconstr'.
  destruct Hconstr' as [i [_ Hconstr']].
  elim contra.
  apply (protocol_state_projection IM i0 constraint i) in Hps.
  destruct Hps as [_oms Hps].
  apply proj_pre_loaded_with_all_messages_protocol_prop in Hps.
  apply proper_sent in Hconstr'; try (exists _oms; assumption).
  unfold selected_message_exists_in_all_traces in Hconstr'.
  simpl in Hinit. specialize (Hinit i).
  pose (composite_vlsm_constrained_projection IM i0 constraint i) as Xi.
  assert (protocol_state_prop Xi (is i)) by (apply initial_is_protocol; assumption).
  specialize (finite_trace_projection_last_state IM i0 constraint i _ _ Hpre) as Hlast.
  apply (finite_ptrace_projection IM i0 constraint i) in Hpre; try assumption.
  pose (Finite (is i) (finite_trace_projection_list IM i0 constraint i pre)) as tri.
  assert (Htri : protocol_trace_prop Xi tri) by (split; assumption).
  apply (proj_pre_loaded_with_all_messages_incl IM i0 constraint i) in Htri.
  simpl in Htri.
  spec Hconstr' (is i) (finite_trace_projection_list IM i0 constraint i pre) Htri Hlast.
  apply Exists_exists in Hconstr'.
  destruct Hconstr' as [itemi [Hitemi Houtput]].
  specialize (finite_trace_projection_list_alt_iff IM i0 constraint i pre) as Halt.
  simpl in Halt.
  specialize (Halt (filter_Forall _ (dec_from_projection IM i0 constraint i) pre)).
  rewrite <- Halt in Hitemi.
  apply in_map_iff in Hitemi.
  destruct Hitemi as [[item Hpr] [Heq Hitem]].
  simpl in Heq.
  apply in_map_iff. exists item. subst itemi. simpl in Houtput.
  split; try assumption.
  apply in_list_annotate_forget in Hitem.
  simpl in Hitem.
  apply filter_In in Hitem.
  destruct Hitem. assumption.
Qed.

(**
As a corollary, if the composition constraint subsumes the
no-equivocations constraint, then for any validator, all observable events
in a protocol state are comparable w.r.t. the [happens_before_fn].
*)
Lemma no_equivocation_constraint_implies_comparable_events
  (Hbs : forall i : index, has_been_sent_capability (IM i))
  (Hno_equiv :
    constraint_subsumption IM constraint (no_equivocations IM i0 constraint Hbs)
  )
  (s : vstate X)
  (Hs : protocol_state_prop X s)
  (e1 e2 : event)
  (v : validator)
  (He1 : In e1 (observable_events s v))
  (He2 : In e2 (observable_events s v))
  : comparableb happens_before_fn e1 e2 = true.
Proof.
  apply evidence_implies_equivocation_converse with s Hs v; try assumption.
  apply not_equivocating_in_traces_ending_in_state.
  apply no_equivocation_constraint_implies_no_equivocations with Hbs.
  assumption.
Qed.

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

Context
  {measurable_V : Measurable validator}
  {reachable_threshold : ReachableThreshold validator}
  (validators : composite_state IM -> set validator)
  (validators_nodup : forall (s : composite_state IM), NoDup (validators s))
  .

Definition composed_observable_basic_equivocation
  : basic_equivocation (composite_state IM) validator
  := @basic_observable_equivocation (composite_state IM) validator event
      decide_eq
      event_comparable
      composed_observation_based_equivocation_evidence
      measurable_V
      reachable_threshold
      validators
      validators_nodup.

Existing Instance composed_observable_basic_equivocation.

Lemma initial_state_not_heavy
  (is : vstate X)
  (Hs : vinitial_state_prop X is)
  : not_heavy is.
Proof.
  unfold not_heavy. unfold equivocation_fault. unfold equivocating_validators.
  unfold state_validators. simpl. unfold equivocation_evidence.
  destruct threshold.
  simpl.
  apply Rge_le in r.
  replace
    (filter
    (fun v : validator =>
     existsb
       (fun e1 : event =>
        existsb
          (fun e2 : event => negb (comparableb happens_before_fn e1 e2))
          (composed_observable_events is v))
       (composed_observable_events is v)) (validators is)
    )
    with (@nil validator)
  ; try assumption.
  symmetry.
  apply filter_nil. rewrite Forall_forall. intros v Hv.
  apply existsb_forall. intros e1 He1.
  rewrite no_events_in_initial_state in He1; try assumption.
  inversion He1.
Qed.

End observable_equivocation_in_composition.

Section unforgeable_messages.

(** ** Unforgeability and observations *)

Context
  {message validator event : Type}
  `{EqDecision event}
  {event_comparable : comparable_events event}
  {index : Type}
  `{EqDecision index}
  (index_listing : list index)
  (finite_index : Listing index_listing)
  (IM : index -> VLSM message)
  (Hevidence : forall (i : index),
    observation_based_equivocation_evidence
        (vstate (IM i)) validator event decide_eq event_comparable
  )
  (i0 : index)
  (constraint : composite_label IM -> composite_state IM * option message -> Prop)
  (A : validator -> index)
  (X := composite_vlsm IM i0 constraint)
  (PreX := pre_loaded_with_all_messages_vlsm X)
  {Hobservable_messages :
    @composite_vlsm_observable_messages _ _ _ decide_eq event_comparable _ decide_eq
    index_listing IM Hevidence i0 constraint}
.

Class unforgeable_messages
  :=
  {
(**
We'll also assume a weak form of [unforgeability]: that a machine can only
produce events for its own validator; for other validators it can only
gather information through the messages it receives.
*)
    sent_messages_unforgeability
      (s s' : vstate X)
      (om om' : option message)
      (l : label)
      (Ht : protocol_transition X l (s, om) (s', om'))
      (i := projT1 l)
      (v : validator)
      (Hv : A v <> i)
      : incl
        (observable_events (s' i) v)
        (set_union decide_eq
          (observable_events (s i) v)
          (option_message_observable_events index_listing IM Hevidence i0 constraint om v)
        );
  }.

(** *** On stating unforgeability for received messages

We'd like to argue here that it's not actually possible to state a similar
property for received messages. In fact, we argue that it is not possible
to require anything more from the received messages than what we already
know, i.e., that the message was produced in an alternative protocol trace.

The reason for the above affirmation is that we can assume that all the
nodes from the current protocol run which don't behave as in the protocol
run generating the message are in fact equivocating and there is a fork of
them behaving such as to guarantee the production of the message.

*)

Context
  {Hunforge : unforgeable_messages}.

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
      (set_diff decide_eq
        (observable_events (s' i) v)
        (set_union decide_eq
          (observable_events (s i) v)
          (option_message_observable_events index_listing IM Hevidence i0 constraint (input item) v)
        )
      )
  )
  : A v = i.
Proof.
  destruct (decide ((A v) = i)); try assumption.
  specialize (protocol_transition_to X is item tr prefix suffix Heq (proj1 Htr)).
  intro Hpt.
  specialize (sent_messages_unforgeability s s' (input item) (output item) (l item) Hpt v n) as Hincl.
  apply set_diff_iff in He.
  destruct He as [He Hne].
  apply Hincl in He. elim Hne. assumption.
Qed.

End unforgeable_messages.
