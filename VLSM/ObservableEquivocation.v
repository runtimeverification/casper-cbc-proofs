Require Import List ListSet FinFun.
Import ListNotations.
From CasperCBC
  Require Import
    Preamble ListExtras ListSetExtras
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
              negb (comparableb happens_before_fn e1 e2)
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

    observable_event_witness
      (is : vstate X)
      (tr : list transition_item)
      (s := last (map destination tr) is)
      (v : validator)
      (e : event)
      (i : index)
      (He : In e (observable_events (s i) v))
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
        In e (message_observable_events m v);

    equivocating_in_trace_last
      (is : vstate X)
      (tr : list transition_item)
      (s := last (map destination tr) is)
      (v : validator)
      : Prop
      := exists
          (e : event)
          (i : index)
          (Hvi : A v <> i)
          (He : In e (observable_events (s i) v)),
          ~ observable_event_witness is tr v e i He;
    
    equivocating_in_trace
      (tr : protocol_trace X)
      (v : validator)
      : Prop
      :=
      exists
        (prefix : list transition_item)
        (last : transition_item)
        (Hpr : trace_prefix X (proj1_sig tr) last prefix),
        equivocating_in_trace_last (trace_first (proj1_sig tr)) prefix v;

    equivocating_in_state
      (s : protocol_state X)
      (v : validator)
      : Prop
      := forall 
        (is : vstate X)
        (tr : list transition_item)
        (Htr : finite_protocol_trace X is tr)
        (Hlast : last (map destination tr) is = proj1_sig s),
        equivocating_in_trace_last is tr v;
    
    evidence_implies_equivocation
      (s : vstate X)
      (Hs : protocol_state_prop X s)
      (v : validator)
      (e1 e2 : event)
      (He1 : In e1 (observable_events s v))
      (He2 : In e2 (observable_events s v))
      (Heqv : comparableb happens_before_fn e1 e2 = false)
      : equivocating_in_state (exist _ s Hs) v
  }.

End observable_equivocation_in_composition.

Section message_observable_equivocation_equivalent_defnitions.

Context
  (state message validator : Type)
  `{Hmsgeqv : message_equivocation_evidence message validator}
  {Hstate : state_encapsulating_messages state message}
  {measurable_V : Measurable validator}
  {reachable_threshold : ReachableThreshold validator}
  .

Definition message_comparable_events
  : comparable_events message
  :=
  {| happens_before_fn := message_preceeds_fn |}.

Definition observable_messages
  (s : state)
  (v : validator)
  :=
  filter (fun m => if eq_dec (sender m) v then true else false) (get_messages s).

Definition message_computable_observable_equivocation_evidence
  : @computable_observable_equivocation_evidence state validator message _ message_comparable_events
  :=
  {| observable_events := observable_messages |}.

Definition message_basic_observable_equivocation
  (Hevidence := message_computable_observable_equivocation_evidence)
  (validators := fun s => set_map eq_dec sender (get_messages s))
  (validators_nodup := fun s => set_map_nodup eq_dec sender (get_messages s))
  : basic_equivocation state validator
  := @basic_observable_equivocation state validator message _ _ Hevidence _ _ validators validators_nodup.

Lemma message_basic_observable_equivocation_iff
  (Hbas_eqv_obs := message_basic_observable_equivocation)
  (Hbas_eqv_msg := state_encapsulating_messages_equivocation state message validator)
  (s : state)
  (v : validator)
  : @is_equivocating_fn _ _ _ _ Hbas_eqv_obs s v
  = @is_equivocating_fn _ _ _ _ Hbas_eqv_msg s v.
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