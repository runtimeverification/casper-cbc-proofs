Require Import Bool List ListSet FinFun
  Reals.
Import ListNotations.
From CasperCBC
  Require Import
    Preamble ListExtras ListSetExtras
    Lib.Classes
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
The <<event>> type is equiped with a decidable relation [happens_before] which should tell
whether an event was generated befor another.

We assume that all events for a given validator must be comparable through
[happens_before]. Under this assumption, if there are events for the same
validator which are not comparable through [happens_before], this constitutes
an [equivocation_evidence].
*)

Class observation_based_equivocation_evidence
  (state validator event : Type)
  (event_eq : EqDecision event)
  (happens_before : event -> event -> Prop)
  (happens_before_dec : RelDecision happens_before)
  (subject_of_observation : event -> option validator)
  :=
  {
    has_been_observed : state -> event -> Prop;
    has_been_observed_dec : RelDecision has_been_observed;
    equivocation_evidence (s : state) (v : validator) : Prop :=
      exists e1,
        has_been_observed s e1 /\
        subject_of_observation e1 = Some v /\
        exists e2,
          has_been_observed s e2 /\
          subject_of_observation e2 = Some v /\
        ~ comparable happens_before e1 e2;
  }.

Section observable_events.

Context
  (state validator event : Type)
  (event_eq : EqDecision event)
  (validator_eq : EqDecision validator)
  (happens_before : event -> event -> Prop)
  (happens_before_dec : RelDecision happens_before)
  (observable_events : state -> validator -> set event)
  (observed_validators :
    forall s, {vs | forall v e, In e (observable_events s v) -> In v vs})
  (subject_of_observation : event -> option validator)
  (observed_event_subject : forall s v e,
      In e (observable_events s v) -> subject_of_observation e = Some v)
  .

Definition observable_events_has_been_observed (s : state) (e : event) : Prop :=
  exists (v : validator), In e (observable_events s v).

Lemma observable_events_has_been_observed_dec : RelDecision observable_events_has_been_observed.
Proof.
  intros s e.
  destruct
    (existsb
      (fun v => inb decide_eq e (observable_events s v))
      (proj1_sig (observed_validators s))
    ) eqn:Hexist; [left|right].
  - apply existsb_exists in Hexist.
    destruct Hexist as [v [Hv He]].
    exists v. apply in_correct in He. assumption.
  - rewrite existsb_forall in Hexist.
    intros [v contra].
    spec Hexist v. rewrite <- in_correct' in Hexist.
    apply Hexist; [|assumption]. clear -contra.
    spec observed_validators s.
    destruct observed_validators as [vs Hvs].
    simpl. apply Hvs with e. assumption.
Qed.

Definition observable_events_subject_of_observation
  (s : state)
  (v1 v2 : validator)
  (e : event)
  (H1: In e (observable_events s v1))
  (H2: In e (observable_events s v2))
  : v1 = v2.
Proof.
  apply observed_event_subject in H1.
  apply observed_event_subject in H2.
  congruence.
Qed.

Local Instance observable_events_equivocation_evidence
  : observation_based_equivocation_evidence state validator _ event_eq _ happens_before_dec subject_of_observation
  := {| has_been_observed := observable_events_has_been_observed;
        has_been_observed_dec := observable_events_has_been_observed_dec
     |}.

Instance equivocation_evidence_dec : RelDecision equivocation_evidence.
Proof.
  intros s v.
  assert
    (Exists (fun e1 => subject_of_observation e1 = Some v /\ Exists (fun e2 => subject_of_observation e2 = Some v /\ ~ comparable happens_before e1 e2)
                                   (observable_events s v)) (observable_events s v)
    <-> equivocation_evidence s v).
  {
  unfold equivocation_evidence.
  rewrite Exists_exists.
  apply Morphisms_Prop.ex_iff_morphism; intro e1.
  repeat rewrite <- and_assoc.
  assert
    (In e1 (observable_events s v) /\ subject_of_observation e1 = Some v
    <->
    has_been_observed s e1 /\ subject_of_observation e1 = Some v).
  { firstorder. replace v with x; [assumption|]. apply observed_event_subject in H.
    congruence.
  }
  rewrite H.
  apply and_iff_compat_l.
  rewrite Exists_exists.
  apply Morphisms_Prop.ex_iff_morphism; intro e2.
  repeat rewrite <- and_assoc.
  apply and_iff_compat_r.
  firstorder. replace v with x; [assumption|]. apply observed_event_subject in H1.
  congruence.
  }

  apply (Decision_iff H);clear H.
  apply @Exists_dec;intro e1.
  apply Decision_and; [apply option_eq_dec|].
  apply @Exists_dec;intro e2.
  apply Decision_and; [apply option_eq_dec|].
  destruct (decide (comparable happens_before e1 e2)); [right|left]; tauto.
Qed.

End observable_events.

(** We can use this notion of [observation_based_equivocation_evidence]
 to obtain the [basic_equivocation] between states and validators.
 *)
Definition basic_observable_equivocation
  (state validator event : Type)
  {event_eq: EqDecision event}
  (happens_before : event -> event -> Prop)
  {happens_before_dec : RelDecision happens_before}
  (subject_of_observation : event -> option validator)
  {Hevidence : observation_based_equivocation_evidence state validator event event_eq happens_before happens_before_dec subject_of_observation}
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
  (subject_of_observation : event -> option validator)
  {Hevidence : observation_based_equivocation_evidence state validator event decide_eq happens_before happens_before_dec subject_of_observation}
  {equivocation_evidence_dec : RelDecision equivocation_evidence}
  {measurable_V : Measurable validator}
  {reachable_threshold : ReachableThreshold validator}
  (validators : state -> set validator)
  (validators_nodup : forall (s : state), NoDup (validators s))
  (basic_eqv := basic_observable_equivocation state validator event happens_before subject_of_observation validators validators_nodup)
  .

Existing Instance basic_eqv.

Lemma equivocation_fault_incl
  (sigma sigma' : state)
  (Hincl_validators : incl (validators sigma) (validators sigma'))
  (Hincl : forall e, has_been_observed sigma e -> has_been_observed sigma' e)
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
  (Hincl : forall e, has_been_observed sigma e -> has_been_observed sigma' e)
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
  {happens_before: event -> event -> Prop}
  {happens_before_dec: RelDecision happens_before}
  {subject_of_observation : event -> option validator}
  {index : Type}
  `{EqDecision index}
  (index_listing : list index)
  (finite_index : Listing index_listing)
  (IM : index -> VLSM message)
  (Hevidence : forall (i : index),
    observation_based_equivocation_evidence
        (vstate (IM i)) validator event decide_eq happens_before happens_before_dec subject_of_observation
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
  composed_witness_has_been_observed index_listing s e.

Lemma composed_has_been_observed_dec : RelDecision composed_has_been_observed.
Proof.
  specialize (composed_witness_has_been_observed_dec index_listing) as Hdec.
  assumption.
Qed.


Definition composed_witness_observation_based_equivocation_evidence
  (witness_set : set index)
  : observation_based_equivocation_evidence (composite_state IM) validator event decide_eq happens_before happens_before_dec subject_of_observation
  :=
    {|
      has_been_observed := (composed_witness_has_been_observed witness_set);
      has_been_observed_dec := (composed_witness_has_been_observed_dec witness_set);
    |}.

Instance composed_observation_based_equivocation_evidence
  : observation_based_equivocation_evidence (composite_state IM) validator event decide_eq happens_before happens_before_dec subject_of_observation
  := composed_witness_observation_based_equivocation_evidence index_listing.

Lemma equivocation_evidence_lift
  (s : composite_state IM)
  (v : validator)
  (i : index)
  (Hsi : equivocation_evidence (s i) v)
  : equivocation_evidence s v.
Proof.
  destruct Hsi as [e1 [Hsi1 [He1 [e2 [Hsi2 [He2 He12]]]]]].
  exists e1. firstorder.
  - exists i. firstorder.
  - exists e2. firstorder. exists i. firstorder.
Qed.

(**
Let us now factor [VLSM]s into the event observability framework.

[message_observable_events] can be extracted from any message.
*)
Class composite_vlsm_observable_messages
  :=
  {
(**
To simplify the presentation, we assume that the events which can be observed
in initial states have no subject, thus they cannot contribute to any
evidence of equivocation.
*)
    no_events_in_initial_state
      (s : state)
      (His : vinitial_state_prop X s)
      (e : event)
      (He : has_been_observed s e)
      : subject_of_observation e = None;

(**
We assume that machines communicate through messages,
and that messages can carry some of the information of their originating
states.

To formalize that, we willl assume a property [message_has_been_observed]
characterizing the events which can be observed in a message,
and we will require that we cannot observe in a sent message events which
were not available in the transition that generated it
([message_observable_consistency]).
*)
    message_has_been_observed : message -> event -> Prop;
    message_has_been_observed_dec : RelDecision message_has_been_observed ;
    message_observable_consistency
      (m : message)
      (som : state * option message)
      (l : label)
      (s : state)
      (Ht : protocol_transition X l som (s, Some m))
      : forall e, message_has_been_observed m e -> has_been_observed (s (projT1 l)) e;
  }.

Context
  {Hcomposite : composite_vlsm_observable_messages}
  `{EqDecision message}
  .

Definition option_message_has_been_observed
  (om : option message)
  (e : event)
  : Prop
  :=
  match om with
  | Some m => message_has_been_observed m e
  | None => False
  end.

Lemma option_message_has_been_observed_dec
  : RelDecision option_message_has_been_observed.
Proof.
  intros om e.
  destruct om; simpl; [|right; intuition].
  apply message_has_been_observed_dec.
Qed.

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
  - subst tr. destruct Htr as [Htr His].
    left. reflexivity.
  - destruct (exists_last Htr0) as [l' [a Heq]].
    specialize
      (Exists_first tr (fun item => has_been_observed (destination item) e))
      as Hfirst.
    spec Hfirst. { intro item. apply has_been_observed_dec. }
    spec Hfirst.
    + apply Exists_exists. exists a.
      split.
      * subst tr. apply in_app_iff. right. left. reflexivity.
      * unfold s in *. clear s. rewrite Heq in He.
        rewrite map_app in He. simpl in He. rewrite last_last in He.
        assumption.
    + right.
      destruct Hfirst as [pre [suf [a' [He' [Heq' Hfirst]]]]].
      exists pre, suf, a'.
      repeat (split; [assumption|]).
      apply Forall_forall.
      intros x Hx contra.
      elim Hfirst. apply Exists_exists. exists x.
      intuition.
Qed.

(** ** Defining observable equivocation based on observable messages
*)

Definition transition_generated_event
  {i : index}
  (s : vstate (IM i))
  (om : option message)
  (s' : vstate (IM i))
  (e : event)
  : Prop
  :=
  has_been_observed s' e /\
  ~ has_been_observed s e /\
  ~ option_message_has_been_observed om e.


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
  (i := projT1 (l item))
  (s := last (map destination prefix) is)
  (s' := destination item),
  tr = prefix ++ [item] ++ suffix /\
  transition_generated_event (s i) (input item) (s' i) e.

Lemma trace_generated_event_dec
  (is : vstate X)
  (tr : list (vtransition_item X))
  (e : event)
  : Decision (trace_generated_event is tr e).
Proof.
  destruct
    (existsb
      (fun t : list (vtransition_item X) * vtransition_item X * list (vtransition_item X) =>
        match t with (pre, item, _) =>
          let i := projT1 (l item) in
            let s := last (map destination pre) is in
            let s' := destination item in
            andb
              (@bool_decide _ (has_been_observed_dec (s' i) e))
              (negb
                (orb
                  (@bool_decide _ (has_been_observed_dec (s i) e))
                  (@bool_decide _ (option_message_has_been_observed_dec (input item) e)))
              )
        end
      )
      (one_element_decompositions tr)
    ) eqn:Hdec; [left|right].
  - apply existsb_exists in Hdec.
    destruct Hdec as [((pre,item), suf) [Hin Hdec]].
    apply in_one_element_decompositions_iff in Hin.
    exists pre, suf, item. split; [symmetry; assumption|].
    simpl in Hdec. apply Bool.andb_true_iff in Hdec.
    rewrite Bool.negb_true_iff in Hdec.
    rewrite Bool.orb_false_iff in Hdec.
    rewrite bool_decide_eq_true in Hdec.
    repeat rewrite bool_decide_eq_false in Hdec.
    assumption.
  - rewrite existsb_forall in Hdec.
    intros [pre [suf [item [Htr Hgen]]]].
    spec Hdec (pre, item, suf).
    spec Hdec. { apply in_one_element_decompositions_iff. symmetry. assumption. }
    simpl in Hdec. apply Bool.andb_false_iff in Hdec.
    rewrite Bool.negb_false_iff in Hdec.
    rewrite Bool.orb_true_iff in Hdec.
    repeat rewrite bool_decide_eq_true in Hdec.
    rewrite bool_decide_eq_false in Hdec.
    clear -Hgen Hdec.
    firstorder.
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
  (i := projT1 (l item))
  (s := last (map destination prefix) is)
  (s' := destination item)
  (Hin : has_been_observed (s' i) e)
  : has_been_observed (s i) e \/ option_message_has_been_observed (input item) e.
Proof.
  destruct (has_been_observed_dec (s i) e) as [|Hsi]; [left; assumption|].
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
  specialize (no_events_in_initial_state (last (map destination []) s) Hs) as Hno.
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
  : exists (m : message), VLSM.Equivocation.equivocation_in_trace X m tr.
Proof.
  destruct Heqv as [e [Hv [He Hne]]].
  unfold trace_generated_event in Hne.
  assert (Hcon : ~ has_been_observed is e).
  { intro contra. apply no_events_in_initial_state in contra; [|apply (proj2 Htr)].
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
  destruct He as [i [_ He]].
  assert (Hnpre : ~has_been_observed (last (map destination pre) is) e).
  { destruct (null_dec pre) as [Hpre0 | Hpre0].
    - subst pre. assumption.
    - destruct (exists_last Hpre0) as [pre' [item' Heq']].
      subst pre.
      rewrite map_app. simpl. rewrite last_last.
      apply (Hpre item').
      apply in_app_iff. right. left. reflexivity.
  }
  assert (Hnei : ~has_been_observed (last (map destination pre) is (projT1 l)) e).
  { intro contra. elim Hnpre. simpl.
    simpl. exists (projT1 l). split; [|assumption]. apply (proj2 finite_index).
  }
  destruct (decide (i = (projT1 l))).
  - specialize
    (not_trace_generated_event _ _ _ Hne
      pre [] {| l := l; input := iom; destination := s; output := oom |}
      eq_refl
    ) as Hng.
    simpl in Hng. subst i.
    specialize (Hng He).
    destruct Hng as [Hng | Hng]; [elim Hnei; assumption|].
    destruct iom as [m|]; [|inversion Hng].
    exists m.
    exists pre. exists suf. exists {| l := l; input := Some m; destination := s; output := oom |}.
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
    apply (message_observable_consistency m _ _ _ H4) in Hng.
    exists (projT1 l0). split; [|assumption]. apply (proj2 finite_index).
  - replace (s i) with (last (map destination pre) is i) in He.
    + elim Hnpre. exists i. split; [|assumption]. apply (proj2 finite_index).
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
the [happens_before].
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
      (He1 : trace_generated_event is tr e1)
      (He2 : trace_generated_event is tr e2)
      (Hv1 : subject_of_observation e1 = Some v)
      (Hv2 : subject_of_observation e2 = Some v)
      : comparable happens_before e1 e2;
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
  (Hbs : forall i : index, has_been_sent_capability (IM i))
  (Xhbs : has_been_sent_capability (composite_vlsm IM i0 constraint) := composite_has_been_sent_capability IM i0 constraint finite_index Hbs)
  (Hno_equiv : constraint_subsumption IM constraint (no_equivocations IM i0 constraint finite_index Hbs))
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
  apply Hno_equiv in Hconstr.
  assert (Hpps : protocol_state_prop (pre_loaded_with_all_messages_vlsm X) (last (map destination pre) is)).
  { destruct Hps as [_om Hps].
    exists _om.
    apply (pre_loaded_with_all_messages_protocol_prop X).
    assumption.
  }
  apply (@proper_sent _ _ Xhbs _ Hpps) in Hconstr.
  spec Hconstr is pre.
  assert (Hincl : VLSM_incl X (pre_loaded_with_all_messages_vlsm X))
    by apply vlsm_incl_pre_loaded_with_all_messages_vlsm.
  apply (VLSM_incl_finite_trace _ (machine (pre_loaded_with_all_messages_vlsm X))) in Hpre
  ; [|assumption].
  specialize (Hconstr (conj Hpre Hinit) eq_refl).
  elim contra. apply in_map_iff. apply Exists_exists in Hconstr.
  destruct Hconstr as [item [Hitem Hout]]. exists item. split; assumption.
Qed.

(**
As a corollary, if the composition constraint subsumes the
no-equivocations constraint, then for any validator, all observable events
in a protocol state are comparable w.r.t. the [happens_before_fn].
*)
Lemma no_equivocation_constraint_implies_comparable_events
  (Hbs : forall i : index, has_been_sent_capability (IM i))
  (Hno_equiv :
    constraint_subsumption IM constraint (no_equivocations IM i0 constraint finite_index Hbs)
  )
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
  unfold equivocating_in_all_traces_ending_in_state.
  intro contra.
  specialize (contra is []).
  spec contra.
  { split; try assumption. constructor. assumption. }
  specialize (contra eq_refl).
  destruct contra as [e [Hv [He _]]]. simpl in He.
  specialize (no_events_in_initial_state is Hs) as Heis.
  spec Heis e He. congruence.
Qed.


Context
  {measurable_V : Measurable validator}
  {reachable_threshold : ReachableThreshold validator}
  (validators : composite_state IM -> set validator)
  (validators_nodup : forall (s : composite_state IM), NoDup (validators s))
  (composed_equivocation_evidence := @equivocation_evidence _ _ _ _ _ _ _ composed_observation_based_equivocation_evidence)
  (composed_equivocation_evidence_dec : RelDecision composed_equivocation_evidence)
  .

Definition composed_observable_basic_equivocation
  : basic_equivocation (composite_state IM) validator
  := @basic_observable_equivocation (composite_state IM) validator event
      decide_eq
      happens_before
      happens_before_dec
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
  specialize (no_events_in_initial_state is Hs _ He1) as Hno.
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
  (Hevidence : forall (i : index),
    observation_based_equivocation_evidence
        (vstate (IM i)) validator event decide_eq happens_before happens_before_dec subject_of_observation
  )
  (i0 : index)
  (constraint : composite_label IM -> composite_state IM * option message -> Prop)
  (A : validator -> index)
  (X := composite_vlsm IM i0 constraint)
  (PreX := pre_loaded_with_all_messages_vlsm X)
  {Hobservable_messages :
    @composite_vlsm_observable_messages _ _ _ decide_eq happens_before happens_before_dec subject_of_observation _ decide_eq
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
      (e : event)
      (He : has_been_observed (s' i) e)
      (Hv : subject_of_observation e = Some v)
      : has_been_observed (s i) e \/
        option_message_has_been_observed index_listing IM Hevidence i0 constraint om e
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
  (Hv : subject_of_observation e = Some v)
  (prefix suffix : list transition_item)
  (item : transition_item)
  (Heq : tr = prefix ++ [item] ++ suffix)
  (i := projT1 (l item))
  (s := last (map destination prefix) is)
  (s' := destination item)
  (He : transition_generated_event index_listing IM Hevidence i0 constraint (s i) (input item) (s' i) e)
  : A v = i.
Proof.
  destruct (decide ((A v) = i)); [assumption|].
  specialize
    (protocol_transition_to X is item tr prefix suffix Heq (proj1 Htr))
    as Hpt.
  specialize
    (sent_messages_unforgeability s s' (input item) (output item) (l item) Hpt v n e)
    as Hincl.
  destruct He as [He Hne].
  apply Hincl in He; [|assumption]. clear -He Hne. firstorder.
Qed.

End unforgeable_messages.
