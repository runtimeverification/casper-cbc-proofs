Require Import Bool List ListSet FinFun
  Reals.
Import ListNotations.
From CasperCBC
  Require Import
    Preamble ListExtras ListSetExtras
    Lib.Classes
    Lib.Measurable
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
*)

Class observable_events
  (state event : Type)
  :=
  {
    has_been_observed : state -> event -> Prop;
    has_been_observed_dec : RelDecision has_been_observed;
  }.
Hint Mode observable_events ! ! : typeclass_instances.

(**
The <<event>> type is equiped with a decidable relation [happens_before] which should tell
whether an event was generated befor another.

We assume that all events for a given validator must be comparable through
[happens_before]. Under this assumption, if there are events for the same
validator which are not comparable through [happens_before], this constitutes
an [equivocation_evidence].
*)

Class observation_based_equivocation_evidence
  (state validator event : Type)
  (state_events : observable_events state event)
  (event_eq : EqDecision event)
  (happens_before : event -> event -> Prop)
  (happens_before_dec : RelDecision happens_before)
  (subject_of_observation : event -> option validator)
  :=
  {
    equivocation_evidence (s : state) (v : validator) : Prop :=
      exists e1,
        has_been_observed s e1 /\
        subject_of_observation e1 = Some v /\
        exists e2,
          has_been_observed s e2 /\
          subject_of_observation e2 = Some v /\
        ~ comparable happens_before e1 e2;
  }.

Section observable_events_fn.

Context
  (state validator event : Type)
  (event_eq : EqDecision event)
  (observable_events_fn : state -> validator -> set event)
  (validators : state -> set validator)
  .

Definition state_observable_events_fn
  (s : state)
  : set event
  :=
  fold_right (set_union decide_eq) [] (map (fun v => observable_events_fn s v) (validators s)).

Definition observable_events_has_been_observed (s : state) (e : event) : Prop :=
  In e (state_observable_events_fn s).

Lemma observable_events_has_been_observed_dec : RelDecision observable_events_has_been_observed.
Proof.
  intros s e.
  apply in_dec. assumption.
Qed.

Local Instance state_observable_events_instance
  : observable_events state event
  :=
  {| has_been_observed := observable_events_has_been_observed;
     has_been_observed_dec := observable_events_has_been_observed_dec
  |}.

Context
  (validator_eq : EqDecision validator)
  (happens_before : event -> event -> Prop)
  (happens_before_dec : RelDecision happens_before)
  (subject_of_observation : event -> option validator)
  .

Local Instance observable_events_equivocation_evidence
  : observation_based_equivocation_evidence _ validator _
    state_observable_events_instance event_eq _ happens_before_dec subject_of_observation
  := Build_observation_based_equivocation_evidence _ _ _ _ _ _ _ _.

Instance observable_events_equivocation_evidence_dec : RelDecision equivocation_evidence.
Proof.
  intros s v.
  unfold equivocation_evidence.
  unfold has_been_observed. simpl. unfold observable_events_has_been_observed.
  apply (Decision_iff (Exists_exists _ _)).
  apply @Exists_dec.
  intro m1.
  apply Decision_and; [apply option_eq_dec|].
  apply (Decision_iff (Exists_exists _ _)).
  apply @Exists_dec.
  intro m2.
  apply Decision_and; [apply option_eq_dec|].
  apply Decision_not.
  apply comparable_dec.
  assumption.
Qed.

End observable_events_fn.

(** We can use this notion of [observation_based_equivocation_evidence]
 to obtain the [basic_equivocation] between states and validators.
 *)
Definition basic_observable_equivocation
  (state validator event : Type)
  {event_eq: EqDecision event}
  (happens_before : event -> event -> Prop)
  {happens_before_dec : RelDecision happens_before}
  (state_events : observable_events state event)
  (subject_of_observation : event -> option validator)
  {Hevidence : observation_based_equivocation_evidence state validator event state_events event_eq happens_before happens_before_dec subject_of_observation}
  {equivocation_evidence_dec : RelDecision equivocation_evidence}
  {measurable_V : Measurable validator}
  {reachable_threshold : ReachableThreshold validator}
  (validators : state -> set validator)
  (validators_nodup : forall (s : state), NoDup (validators s))
  : basic_equivocation state validator
  := {|
    is_equivocating := equivocation_evidence;
    is_equivocating_dec := equivocation_evidence_dec;
    state_validators := validators;
    state_validators_nodup := validators_nodup
    |}.

Section not_heavy_incl.

Context
  (state validator event : Type)
  `{EqDecision event}
  (v_eq : EqDecision validator)
  {happens_before : event -> event -> Prop}
  {happens_before_dec : RelDecision happens_before}
  (state_events : observable_events state event)
  (subject_of_observation : event -> option validator)
  {Hevidence : observation_based_equivocation_evidence state validator event state_events decide_eq happens_before happens_before_dec subject_of_observation}
  {equivocation_evidence_dec : RelDecision equivocation_evidence}
  {measurable_V : Measurable validator}
  {reachable_threshold : ReachableThreshold validator}
  (validators : state -> set validator)
  (validators_nodup : forall (s : state), NoDup (validators s))
  (basic_eqv := basic_observable_equivocation state validator event happens_before state_events subject_of_observation validators validators_nodup)
  .

Existing Instance basic_eqv.

Lemma equivocation_fault_incl
  (sigma sigma' : state)
  (Hincl_validators : incl (validators sigma) (validators sigma'))
  (Hincl : forall e : event, has_been_observed sigma e -> has_been_observed sigma' e)
  : (equivocation_fault sigma <= equivocation_fault sigma')%R.
Proof.
  intros.
  unfold equivocation_fault.
  unfold equivocating_validators.
  apply sum_weights_incl; try (apply NoDup_filter; apply state_validators_nodup).
  apply incl_tran with (filter (fun v : validator => bool_decide (is_equivocating sigma' v))
  (state_validators sigma))
  ; [|apply filter_incl; assumption].
  apply filter_incl_fn.
  intro v.
  repeat rewrite bool_decide_eq_true.
  unfold equivocation_evidence.
  clear -Hincl;firstorder.
Qed.

(* If a state is not overweight, none of its subsets are *)
Lemma not_heavy_incl
  (sigma sigma' : state)
  (Hincl_validators : incl (validators sigma) (validators sigma'))
  (Hincl : forall e : event, has_been_observed sigma e -> has_been_observed sigma' e)
  (Hsigma' : not_heavy sigma')
  : not_heavy sigma.
Proof.
  apply Rle_trans with (equivocation_fault sigma'); try assumption.
  apply equivocation_fault_incl; assumption.
Qed.

End not_heavy_incl.

Section vlsm_observable_events.

(**
Let us now factor [VLSM]s into the event observability framework.

[message_observable_events] can be extracted from any message.
*)
Class vlsm_observable_events
  {message : Type}
  (X : VLSM message)
  {event validator : Type}
  {state_events : observable_events state event}
  {message_events : observable_events message event}
  (subject_of_observation : event -> option validator)
  :=
  {
(**
To simplify the presentation, we assume that the events which can be observed
in initial states have no subject, thus they cannot contribute to any
evidence of equivocation.
*)
    no_event_subject_in_initial_state
      (s : state)
      (His : vinitial_state_prop X s)
      (e : event)
      (He : has_been_observed s e)
      : subject_of_observation e = None;
(**
Similarly, we assume that the events which can be observed
in initial messages have no subject, thus they cannot contribute to any
evidence of equivocation.
*)
    no_event_subject_in_initial_message
      (m : message)
      (His : vinitial_message_prop X m)
      (e : event)
      (He : has_been_observed m e)
      : subject_of_observation e = None;

(**
We assume that messages can only carry some of the information
of their originating states.

To formalize that, we will require that we cannot observe in a sent
message events which were not available in the transition that generated it
([message_observable_consistency]).
*)
    message_observable_consistency
      (l : label)
      (som : state * option message)
      (s' : state)
      (m' : message)
      (Ht : vtransition X l som = (s', Some m'))
      : forall e : event, has_been_observed m' e -> has_been_observed s' e;
  }.

Context
  {message : Type}
  (X : VLSM message)
  {event validator : Type}
  {state_events : observable_events state event}
  {message_events : observable_events message event}
  (subject_of_observation : event -> option validator)
  {vlsm_events : vlsm_observable_events X subject_of_observation}
  .

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
  (e : event)
  (s := last (map destination tr) is)
  (He : has_been_observed s e)
  : s = is \/
    exists
    (pre suf : list transition_item)
    (item : transition_item),
    tr = pre ++ [item] ++ suf /\
    has_been_observed (destination item) e /\
    Forall (fun item => ~has_been_observed (destination item) e) pre.
Proof.
  destruct (null_dec tr) as [Htr0 | Htr0].
  - subst tr.
    left. reflexivity.
  - right. destruct (exists_last Htr0) as [l' [a Heq]].
    specialize
      (Exists_first tr (fun item => has_been_observed (destination item) e))
      as Hfirst.
    spec Hfirst. { intro item. apply has_been_observed_dec. }
    spec Hfirst.
    { apply Exists_exists. exists a.
      split.
      * subst tr. apply in_app_iff. right. left. reflexivity.
      * unfold s in *. clear s. rewrite Heq in He.
        rewrite map_app in He. simpl in He. rewrite last_last in He.
        assumption.
    }
    destruct Hfirst as [pre [suf [a' [He' [Heq' Hfirst]]]]].
    exists pre, suf, a'.
    repeat (split; [assumption|]).
    apply Forall_Exists_neg. assumption.
Qed.

Definition option_message_has_been_observed
  (om : option message)
  (e : event)
  : Prop
  :=
  match om with
  | Some m => has_been_observed m e
  | None => False
  end.

Lemma option_message_has_been_observed_dec
  : RelDecision option_message_has_been_observed.
Proof.
  intros om e.
  destruct om; simpl; [|right; intuition].
  apply has_been_observed_dec.
Qed.

(** ** Defining observable equivocation based on observable messages
*)

Definition transition_generated_event
  (s : vstate X)
  (om : option message)
  (s' : vstate X)
  (e : event)
  : Prop
  :=
  has_been_observed s' e /\
  ~ has_been_observed s e /\
  ~ option_message_has_been_observed om e.

Lemma transition_generated_event_dec
  (s : vstate X)
  (om : option message)
  (s' : vstate X)
  (e : event)
  : Decision (transition_generated_event s om s' e).
Proof.
  repeat apply Decision_and; repeat apply Decision_not; repeat apply has_been_observed_dec.
  apply option_message_has_been_observed_dec.
Qed.

(**
We call [trace_generated_event] an event which
appeared as result of a transition in a trace, that is, which it was
not in the state prior to the transition, nor in the received message,
but it is in the state resulted after the transition.
*)
Definition trace_generated_event
  (is : vstate X)
  (tr : list (vtransition_item X))
  (e : event)
  : Prop
  :=
  exists
  (prefix suffix : list transition_item)
  (item : vtransition_item X)
  (s := last (map destination prefix) is)
  (s' := destination item),
  tr = prefix ++ [item] ++ suffix /\
  transition_generated_event s (input item) s' e.

Lemma trace_generated_event_dec
  (is : vstate X)
  (tr : list (vtransition_item X))
  (e : event)
  : Decision (trace_generated_event is tr e).
Proof.
  unfold trace_generated_event.
  apply
    (Decision_iff
      (P := Exists
        (fun t =>
          match t with
          (prefix, item, _) =>
            transition_generated_event (last (map destination prefix) is) (input item) (destination item) e
          end)
        (one_element_decompositions tr)))
  ; [rewrite Exists_exists; split|].
  - intros [((prefix, item), suffix) H]. exists prefix, suffix, item.
    rewrite in_one_element_decompositions_iff in H.
    firstorder.
  - intros [prefix [suffix [item H]]]. exists (prefix, item, suffix).
    rewrite in_one_element_decompositions_iff.
    firstorder.
  - apply @Exists_dec. intros [(prefix, item) _].
    apply transition_generated_event_dec.
Qed.

(**
If an event is generated by a trace <<tr>>, then it's also generated by
any trace having <<tr>> as a prefix.
*)
Lemma trace_generated_prefix
  (is : vstate X)
  (pre : list (vtransition_item X))
  (e : event)
  (Hgen : trace_generated_event is pre e)
  (suf : list transition_item)
  : trace_generated_event is (pre ++ suf) e.
Proof.
  unfold trace_generated_event in *.
  destruct Hgen as [pre' [suf' [item [Heq Hgen]]]].
  exists pre'. exists (suf' ++ suf). exists item.
  subst pre. repeat rewrite <- app_assoc.
  intuition.
Qed.

(**
Conversely, if an event is not generated by a trace, then it's not
generated by any of its prefixes.
*)
Lemma not_trace_generated_prefix
  (is : vstate X)
  (pre : list (vtransition_item X))
  (e : event)
  (suf : list transition_item)
  (Hngen : ~trace_generated_event is (pre ++ suf) e)
  : ~trace_generated_event is pre e.
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
  (e : event)
  (Hne : ~trace_generated_event is tr e)
  (prefix suffix : list transition_item)
  (item : transition_item)
  (Heq : tr = prefix ++ [item] ++ suffix)
  (s := last (map destination prefix) is)
  (s' := destination item)
  (Hin : has_been_observed s' e)
  : has_been_observed s e \/ option_message_has_been_observed (input item) e.
Proof.
  destruct (has_been_observed_dec s e) as [|Hsi]; [left; assumption|].
  destruct (option_message_has_been_observed_dec (input item) e) as [|Hitem]; [right; assumption|].
  elim Hne.
  exists prefix, suffix, item.
  unfold transition_generated_event.
  intuition.
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
  exists (e : event),
    subject_of_observation e = Some v /\
    has_been_observed s e /\
    ~ trace_generated_event is tr e.

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
  intro contra. destruct contra as [e [Hv [He Hne]]].
  specialize (no_event_subject_in_initial_state (last (map destination []) s) Hs) as Hno.
  spec Hno e He. congruence.
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
    (last : transition_item),
    trace_prefix X (proj1_sig tr) last prefix /\
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
    (tr : list transition_item),
    finite_protocol_trace X is tr /\
    last (map destination tr) is = proj1_sig s /\
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
    exists is. exists tr. split; [assumption|].  split; [assumption|].
    apply (Hall is tr); assumption.
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
  : exists (m : message),
    VLSM.Equivocation.equivocation_in_trace X m tr
    /\ ~vinitial_message_prop X m.
Proof.
  destruct Heqv as [e [Hv [He Hne]]].
  unfold trace_generated_event in Hne.
  assert (Hcon : ~ has_been_observed is e).
  { intro contra. apply no_event_subject_in_initial_state in contra; [|apply (proj2 Htr)].
    congruence.
  }
  assert (He' := He).
  apply (in_observable_events_first is tr Htr e) in He.
  destruct He as [He | He]; [rewrite He in He'; intuition|].
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
  assert (Hnpre : ~has_been_observed (last (map destination pre) is) e).
  { destruct (null_dec pre) as [Hpre0 | Hpre0].
    - subst pre. assumption.
    - destruct (exists_last Hpre0) as [pre' [item' Heq']].
      subst pre.
      rewrite map_app. simpl. rewrite last_last.
      apply (Hpre item').
      apply in_app_iff. right. left. reflexivity.
  }
  specialize
    (not_trace_generated_event _ _ _ Hne
      pre [] {| l := l; input := iom; destination := s; output := oom |}
      eq_refl
    ) as Hng.
  simpl in Hng.
  specialize (Hng He).
  destruct Hng as [Hng | Hng]; [elim Hnpre; assumption|].
  destruct iom as [m|]; [|inversion Hng].
  exists m.
  split.
  - exists pre. exists suf. exists {| l := l; input := Some m; destination := s; output := oom |}.
    rewrite <- app_assoc. repeat (split; [reflexivity|]).
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
    destruct H4 as [Hvalid Ht].
    apply (message_observable_consistency  _ _ _ _ Ht) in Hng.
    assumption.
  - intro contra.
    simpl in Hng.
    specialize (no_event_subject_in_initial_message _ contra e Hng) as contra1.
    congruence.
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
  destruct contra as [m [contra Hnoinitial]].
  elim (Hneqv m). assumption.
Qed.

(** ** Linking evidence of equivocation with observable equivocation
*)

Context
  `{EqDecision event}
  {happens_before: event -> event -> Prop}
  {happens_before_dec: RelDecision happens_before}
  .


(**
The class below links [vlsm_observable_events] with
[observation_based_equivocation_evidence] by requiring that all
[trace_generated_event]s for the same validator are [comparable] through
the [happens_before].
*)
Class vlsm_comparable_generated_events
  :=
  {
    comparable_generated_events
      (is : vstate X)
      (tr : list transition_item)
      (Htr : finite_protocol_trace X is tr)
      (v : validator)
      (e1 e2 : event)
      (He1 : trace_generated_event is tr e1)
      (He2 : trace_generated_event is tr e2)
      (Hv1 : subject_of_observation e1 = Some v)
      (Hv2 : subject_of_observation e2 = Some v)
      : comparable happens_before e1 e2;
  }.

Context
  {Hcomparable_generated_events : vlsm_comparable_generated_events}.

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
  (He1 : has_been_observed s e1)
  (He2 : has_been_observed s e2)
  (Hv1 : subject_of_observation e1 = Some v)
  (Hv2 : subject_of_observation e2 = Some v)
  (Hnc : ~comparable happens_before e1 e2)
  (Hgen1 : trace_generated_event is tr e1)
  : equivocating_in_trace_last is tr v.
Proof.
  destruct (trace_generated_event_dec is tr e2) as [Hgen2|Hgen2].
  - contradict Hnc.
    exact (comparable_generated_events is tr Htr v e1 e2 Hgen1 Hgen2 Hv1 Hv2).
  - exists e2. repeat split; assumption.
Qed.

(**
We now tie the [observation_based_equivocation_evidence] notion
to that of [composite_vlsm_comparable_generated_events] by showing that
the existence of two events observable for a validator <<v>> in a state <<s>>
which are not [comparable] w.r.t. [happens_before] relation guarantees
that <<v>> is [equivocating_in_all_traces_ending_in_state] <<s>>.
*)
Lemma evidence_implies_equivocation
  (s : vstate X)
  (Hs : protocol_state_prop X s)
  (v : validator)
  (e1 e2 : event)
  (He1 : has_been_observed s e1)
  (He2 : has_been_observed s e2)
  (Hv1 : subject_of_observation e1 = Some v)
  (Hv2 : subject_of_observation e2 = Some v)
  (Heqv : ~comparable happens_before e1 e2)
  : equivocating_in_all_traces_ending_in_state (exist _ s Hs) v.
Proof.
  intro is; intros. simpl in Hlast.
  subst s.
  destruct (trace_generated_event_dec is tr e1) as [Hgen1| Hgen1].
  - apply uncomparable_with_generated_event_equivocation with e1 e2
    ; assumption.
  - exists e1. repeat split; assumption.
Qed.

(**
The counter-positive of the above says that if there exists a trace
leading to <<s>> which is not equivocating, then all events observed
for <<v>> in <<s>> must be comparable w.r.t. the [happens_before].
*)
Lemma evidence_implies_equivocation_converse
  (s : vstate X)
  (Hs : protocol_state_prop X s)
  (v : validator)
  (Hneqv : not_equivocating_in_some_traces_ending_in_state (exist _ s Hs) v)
  (e1 e2 : event)
  (He1 : has_been_observed s e1)
  (He2 : has_been_observed s e2)
  (Hv1 : subject_of_observation e1 = Some v)
  (Hv2 : subject_of_observation e2 = Some v)
  : comparable happens_before e1 e2.
Proof.
  destruct (comparable_dec happens_before e1 e2) as [|Hcmp]; [assumption|].
  specialize (evidence_implies_equivocation s Hs v e1 e2 He1 He2 Hv1 Hv2 Hcmp)
    as Heqv.
  destruct Hneqv as [is [tr [Htr [Hlast Hneqv]]]]. elim Hneqv.
  specialize (Heqv is tr Htr Hlast). assumption.
Qed.

(** ** No-equivocation composition constraint guarantees no equivocations
*)

(**
If the composition constraint subsumes the no-equivocations constraint,
then all observable events for a validator are comparable w.r.t.
the [happens_before_fn].
*)
Lemma no_equivocation_constraint_implies_no_equivocations
  (Xhbs : has_been_sent_capability X)
  (Hno_equiv : forall l som, vvalid X l som -> (no_equivocations X l som))
  (s : vstate X)
  (Hs : protocol_state_prop X s)
  (v : validator)
  : not_equivocating_in_all_traces_ending_in_state (exist _ s Hs) v.
Proof.
  intro is; intros. simpl in Hlast.
  intro contra.
  apply event_equivocation_implies_message_equivocation in contra; try assumption.
  destruct contra as [m [contra Hnoinitial]].
  destruct contra as [pre [suf [item [Heq [Hinput contra]]]]].
  subst tr.
  destruct Htr as [Htr Hinit].
  apply finite_protocol_trace_from_app_iff in Htr.
  destruct Htr as [Hpre Htr].
  inversion Htr.
  subst. simpl in Hinput. subst.
  destruct H3 as [[Hps [Hpm Hv]] Ht].
  apply Hno_equiv in Hv.
  pose (Pre := pre_loaded_with_all_messages_vlsm X).
  assert (Hpps : protocol_state_prop Pre (last (map destination pre) is)).
  { destruct Hps as [_om Hps].
    exists _om.
    apply (pre_loaded_with_all_messages_protocol_prop X).
    assumption.
  }
  destruct Hv as [Hv | Hinitial]; [|contradiction].
  apply (@proper_sent _ _ Xhbs _ Hpps) in Hv.
  spec Hv is pre.
  assert (Hincl : VLSM_incl X Pre)
    by apply vlsm_incl_pre_loaded_with_all_messages_vlsm.
  specialize (VLSM_incl_finite_protocol_trace_from _ _ Hincl) as Htr_incl.
  spec Hv.
  { split; [|assumption].
    apply Htr_incl. clear -Hpre.
    destruct X as (Xt, (Xs, Xm)). assumption.
  }
  specialize (Hv eq_refl).
  apply Exists_exists in Hv.
  elim contra.
  apply in_map_iff.
  firstorder.
Qed.

(**
As a corollary, if the composition constraint subsumes the
no-equivocations constraint, then for any validator, all observable events
in a protocol state are comparable w.r.t. the [happens_before_fn].
*)
Lemma no_equivocation_constraint_implies_comparable_events
  (Xhbs : has_been_sent_capability X)
  (Hno_equiv : forall l som, vvalid X l som -> (no_equivocations X l som))
  (s : vstate X)
  (Hs : protocol_state_prop X s)
  (e1 e2 : event)
  (v : validator)
  (He1 : has_been_observed s e1)
  (He2 : has_been_observed s e2)
  (Hv1 : subject_of_observation e1 = Some v)
  (Hv2 : subject_of_observation e2 = Some v)
  : comparable happens_before e1 e2.
Proof.
  apply evidence_implies_equivocation_converse with s Hs v; try assumption.
  apply not_equivocating_in_traces_ending_in_state.
  apply no_equivocation_constraint_implies_no_equivocations with Xhbs.
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
  unfold equivocating_in_all_traces_ending_in_state.
  intro contra.
  specialize (contra is []).
  spec contra.
  { split; try assumption. constructor. assumption. }
  specialize (contra eq_refl).
  destruct contra as [e [Hv [He _]]]. simpl in He.
  specialize (no_event_subject_in_initial_state is Hs) as Heis.
  spec Heis e He. congruence.
Qed.

End vlsm_observable_events.

Section observable_events_fn_in_composition.

Context
  {message validator event : Type}
  `{EqDecision event}
  {index : Type}
  `{EqDecision index}
  (index_listing witness_set : list index)
  (IM : index -> VLSM message)
  (Hstate_events_fn : forall (i : index), vstate (IM i) -> validator -> set event)
  (Hstate_validators : forall (i : index), vstate (IM i) -> set validator)
  (Hstate_events : forall (i : index), observable_events (vstate (IM i)) event
    := fun i => state_observable_events_instance state validator event _ (Hstate_events_fn i) (Hstate_validators i)
  )
  `{EqDecision validator}
  .

Definition composite_state_events_fn
  (s : composite_state IM)
  (v : validator)
  : set event
  :=
  fold_right (set_union decide_eq) [] (map (fun i => Hstate_events_fn i (s i) v) witness_set).

Definition composite_validators
  (s : composite_state IM)
  : set validator
  :=
  fold_right (set_union decide_eq) [] (map (fun i => Hstate_validators i (s i)) index_listing).

Definition composite_state_observable_events_instance
  : observable_events (composite_state IM) event
  :=
  state_observable_events_instance (composite_state IM) validator event _ composite_state_events_fn composite_validators.

Context
  (happens_before : event -> event -> Prop)
  (happens_before_dec : RelDecision happens_before)
  (subject_of_observation : event -> option validator)
  .

Definition composite_observable_events_equivocation_evidence
  : observation_based_equivocation_evidence _ validator _
    composite_state_observable_events_instance _ _ happens_before_dec subject_of_observation
  :=
  observable_events_equivocation_evidence (composite_state IM) validator event _ composite_state_events_fn composite_validators
    happens_before happens_before_dec subject_of_observation.

Existing Instance composite_observable_events_equivocation_evidence.

Definition composite_observable_events_equivocation_evidence_dec
  : RelDecision equivocation_evidence
  :=
  observable_events_equivocation_evidence_dec (composite_state IM) validator event _ composite_state_events_fn composite_validators _
    happens_before happens_before_dec subject_of_observation.

End observable_events_fn_in_composition.

Section observable_equivocation_in_composition.

(** ** Observable messages in a VLSM composition

We assume a composition of [VLSM]s where each machine has a way to
produce [observation_based_equivocation_evidence].
*)

Context
  {message validator event : Type}
  `{EqDecision event}
  {happens_before: event -> event -> Prop}
  {happens_before_dec: RelDecision happens_before}
  {subject_of_observation : event -> option validator}
  {index : Type}
  `{EqDecision index}
  (index_listing : list index)
  (finite_index : Listing index_listing)
  (IM : index -> VLSM message)
  (Hstate_events : forall (i : index), observable_events (vstate (IM i)) event)
  (Hmessage : observable_events message event)
  (Hevents : forall (i : index), vlsm_observable_events (IM i) subject_of_observation)
  (Hevidence : forall (i : index),
    observation_based_equivocation_evidence
        (vstate (IM i)) validator event (Hstate_events i) decide_eq happens_before happens_before_dec subject_of_observation
  )
  {i0 : Inhabited index}
  (constraint : composite_label IM -> composite_state IM * option message -> Prop)
  (X := composite_vlsm IM constraint)
  (PreX := pre_loaded_with_all_messages_vlsm X)
  .

(**
It is easy to define a [observation_based_equivocation_evidence] mechanism for
the composition, by just defining the [observable_events] for the composite state
to be the union of [observable_events] for each of the component states.
*)

Definition composed_witness_has_been_observed
  (witness_set : set index)
  (s : composite_state IM)
  (e : event)
  : Prop
  :=
  exists i : index, In i witness_set /\ has_been_observed (s i) e.

Lemma composed_witness_has_been_observed_dec
  (witness_set : set index)
  (s : composite_state IM)
  (e : event)
  : Decision (composed_witness_has_been_observed witness_set s e).
Proof.
  apply (Decision_iff (Exists_exists _ _ )).
  apply @Exists_dec.
  intro i.
  apply has_been_observed_dec.
Qed.

Definition composed_has_been_observed
  (s : composite_state IM)
  (e : event)
  : Prop
  :=
  exists i : index, has_been_observed (s i) e.

Lemma composed_has_been_observed_dec : RelDecision composed_has_been_observed.
Proof.
  intros s e.
  specialize (composed_witness_has_been_observed_dec index_listing s e) as Hdec.
  apply (Decision_iff (P := (composed_witness_has_been_observed index_listing s e)))
  ; [|assumption].
  unfold composed_witness_has_been_observed. unfold composed_has_been_observed.
  split; intros [i He]; exists i; intuition. apply finite_index.
Qed.

Definition composed_witness_state_observable_events
  (witness_set : set index)
  : observable_events (composite_state IM) event
  :=
  {|
    has_been_observed := (composed_witness_has_been_observed witness_set);
    has_been_observed_dec := (composed_witness_has_been_observed_dec witness_set);
  |}.

Instance composed_state_observable_events
  : observable_events (composite_state IM) event
  :=
  {|
    has_been_observed := composed_has_been_observed;
    has_been_observed_dec := composed_has_been_observed_dec
  |}.

Definition composed_witness_observation_based_equivocation_evidence
  (witness_set : set index)
  : observation_based_equivocation_evidence
    (composite_state IM) validator event
    (composed_witness_state_observable_events witness_set)
    decide_eq happens_before happens_before_dec subject_of_observation.
Proof. split. Defined.

Instance composed_observation_based_equivocation_evidence
  : observation_based_equivocation_evidence (composite_state IM) validator event composed_state_observable_events decide_eq happens_before happens_before_dec subject_of_observation.
Proof. split. Defined.

Lemma equivocation_evidence_lift
  (s : composite_state IM)
  (v : validator)
  (i : index)
  (Hsi : equivocation_evidence (s i) v)
  : equivocation_evidence s v.
Proof.
  firstorder.
Qed.

(**
Let us now show that the notion of 'vlsm_observable_events' can be lifted to
the composite vlsm.
*)
Definition composite_vlsm_observable : vlsm_observable_events X subject_of_observation.
Proof.
  split.
  - intros. destruct He as [i He].
    spec His i.
    spec Hevents i. destruct Hevents.
    firstorder.
  - intros. destruct His as [i [[mi Hmi] His]].
    simpl in His. subst mi.
    spec Hevents i. destruct Hevents. firstorder.
  - intros. destruct l as (i, li). destruct som as (s, om).
    unfold vtransition in Ht. simpl in Ht.
    spec Hevents i. destruct Hevents.
    spec message_observable_consistency0 li (s i, om).
    destruct (vtransition (IM i) li (s i, om)) as (si', om'').
    inversion Ht. subst. clear Ht. exists i.
    rewrite state_update_eq. firstorder.
Qed.

Existing Instance composite_vlsm_observable.

Context
  `{EqDecision message}
  {measurable_V : Measurable validator}
  {reachable_threshold : ReachableThreshold validator}
  (validators : composite_state IM -> set validator)
  (validators_nodup : forall (s : composite_state IM), NoDup (validators s))
  (composed_equivocation_evidence := @equivocation_evidence _ _ _ _ _ _ _ subject_of_observation composed_observation_based_equivocation_evidence)
  (composed_equivocation_evidence_dec : RelDecision composed_equivocation_evidence)
  .

Definition composed_observable_basic_equivocation
  : basic_equivocation (composite_state IM) validator
  := @basic_observable_equivocation (composite_state IM) validator event
      decide_eq
      happens_before
      happens_before_dec
      _
      subject_of_observation
      composed_observation_based_equivocation_evidence
      composed_equivocation_evidence_dec
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
    (filter _ (validators is))
    with (@nil validator)
  ; try assumption.
  symmetry.
  apply filter_nil. rewrite Forall_forall. intros v Hv.
  apply bool_decide_eq_false.
  intros [e1 [He1 [Hv1 H]]].
  specialize (no_event_subject_in_initial_state is Hs _ He1) as Hno.
  congruence.
Qed.

End observable_equivocation_in_composition.

Section unforgeable_messages.

(** ** Unforgeability and observations *)

Context
  {message validator event : Type}
  `{EqDecision event}
  {happens_before: event -> event -> Prop}
  {happens_before_dec: RelDecision happens_before}
  {subject_of_observation : event -> option validator}
  {index : Type}
  `{EqDecision index}
  (index_listing : list index)
  (finite_index : Listing index_listing)
  (IM : index -> VLSM message)
  (Hstate_events : forall (i : index), observable_events (vstate (IM i)) event)
  (Hmessage : observable_events message event)
  (Hevents : forall (i : index), vlsm_observable_events (IM i) subject_of_observation)
  (Hcomposed_state_events : observable_events (composite_state IM) event := composed_state_observable_events _ finite_index IM Hstate_events)
  (Hevidence : forall (i : index),
    observation_based_equivocation_evidence
        (vstate (IM i)) validator event (Hstate_events i) decide_eq happens_before happens_before_dec subject_of_observation
  )
  {i0 : Inhabited index}
  (constraint : composite_label IM -> composite_state IM * option message -> Prop)
  (A : validator -> index)
  (X := composite_vlsm IM constraint)
  (PreX := pre_loaded_with_all_messages_vlsm X)
.

Existing Instance Hcomposed_state_events.

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
      (e : event)
      (He : has_been_observed (s' i) e)
      (Hv : subject_of_observation e = Some v)
      : has_been_observed (s i) e \/
        option_message_has_been_observed om e
      ;
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
  {Hunforge : unforgeable_messages}
  .

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
  (Hv : subject_of_observation e = Some v)
  (prefix suffix : list transition_item)
  (item : transition_item)
  (Heq : tr = prefix ++ [item] ++ suffix)
  (i := projT1 (l item))
  (s := last (map destination prefix) is)
  (s' := destination item)
  (He : transition_generated_event X s (input item) s' e)
  : A v = i.
Proof.
  destruct (decide ((A v) = i)); [assumption|].
  specialize
    (protocol_transition_to X is item tr prefix suffix Heq (proj1 Htr))
    as Hpt.
  specialize
    (sent_messages_unforgeability s s' (input item) (output item) (l item) Hpt v n e)
    as Hincl.
  destruct Hpt as [Hvalid Ht].
  destruct item. simpl in *.
  destruct l as (j, li). simpl in *. unfold i in *. clear i.
  match type of Ht with (let (si', om') := ?t in _) = _ =>
    destruct t as (si', om') eqn:Hti
  end.
  inversion Ht. subst. clear Ht.
  destruct (Hevents j).
  destruct He as [[i He] [Hnse Hnme]].
  unfold s' in *. clear s'.
  rewrite state_update_eq in Hincl.
  destruct (decide (i = j)).
  - subst. rewrite state_update_eq in He. spec Hincl He Hv. clear -Hnse Hnme Hincl. firstorder.
  - rewrite state_update_neq in He by assumption.
    elim Hnse. exists i. assumption.
Qed.

End unforgeable_messages.
