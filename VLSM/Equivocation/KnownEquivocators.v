From Coq Require Import List ListSet FinFun Rdefinitions.
Import ListNotations.

From CasperCBC Require Import
    Lib.Preamble Lib.ListExtras Lib.ListSetExtras Lib.Measurable
    VLSM.Common
    VLSM.Composition
    VLSM.Equivocation
    VLSM.Equivocation.NoEquivocation
    VLSM.Equivocation.FixedSetEquivocation
    .

Section known_equivocators.

Context
  {message : Type}
  {index : Type}
  {IndEqDec : EqDecision index}
  {i0 : Inhabited index}
  (IM : index -> VLSM message)
  (Hbs : forall i : index, has_been_sent_capability (IM i))
  (Hbr : forall i : index, has_been_received_capability (IM i))
  {validator : Type}
  (A : validator -> index)
  (sender : message -> option validator)
  (PreFree := pre_loaded_with_all_messages_vlsm (free_composite_vlsm IM))
  .

Class known_equivocators_capability
  (globally_known_equivocators : composite_state IM -> set validator)
  :=
  { known_equivocators_nodup :
    forall s, NoDup (globally_known_equivocators s)
  ; known_equivocators_is_equivocating_tracewise_char :
    forall s v,
      In v (globally_known_equivocators s) <-> is_equivocating_tracewise_alt IM A sender s v
  }.

Section known_equivocators_properties.

Context 
  (globally_known_equivocators : composite_state IM -> set validator)
  (Hke : known_equivocators_capability globally_known_equivocators)
  {ValEqDec : EqDecision validator}
  .

(** Since is_equivocating_tracewise is characterized by the *globally_known_equivocators*
function ([known_equivocators_is_equivocating_tracewise_char]), it becomes
decidable.
*)
Lemma known_equivocators_is_equivocating_tracewise_alt_dec
  : RelDecision (is_equivocating_tracewise_alt IM A sender).
Proof.
  intros s v.
  destruct (in_dec ValEqDec v (globally_known_equivocators s)).
  - left. apply known_equivocators_is_equivocating_tracewise_char. assumption.
  - right. rewrite <- known_equivocators_is_equivocating_tracewise_char. assumption.
Qed.


Lemma known_equivocators_empty_in_initial_state
  (s : composite_state IM)
  (His : composite_initial_state_prop IM s)
  : globally_known_equivocators s = [].
Proof.
  specialize (known_equivocators_is_equivocating_tracewise_char s) as Heqv.
  destruct (globally_known_equivocators s); [reflexivity|].
  specialize (Heqv v). apply proj1 in Heqv.
  spec Heqv. { left. reflexivity. }
  apply initial_state_not_is_equivocating_tracewise with (i1 := i0) (A0 := A) (sender0 := sender) (v0 := v) in His.
  contradiction.
Qed.

Lemma protocol_transition_receiving_None_reflects_known_equivocators l s s' om'
  (Ht : protocol_transition PreFree l (s, None) (s', om'))
  : incl (globally_known_equivocators s') (globally_known_equivocators s).
Proof.
  intro v. setoid_rewrite known_equivocators_is_equivocating_tracewise_char.
  revert Ht v.
  apply transition_receiving_None_reflects_is_equivocating_tracewise.
Qed.

Context
  {ValMeasurable : Measurable validator}
  {EqDecision : EqDecision validator}
  {threshold_V : ReachableThreshold validator}
  {validator_listing : list validator}
  (finite_validator : Listing validator_listing)
  .


Local Instance known_equivocators_basic_equivocation : basic_equivocation (composite_state IM) validator
  := equivocation_dec_tracewise IM A sender finite_validator known_equivocators_is_equivocating_tracewise_alt_dec .

Lemma globally_known_equivocators_equivocating_validators
  : forall s, set_eq (equivocating_validators s) (globally_known_equivocators s).
Proof.
  intro s.
  unfold equivocating_validators, is_equivocating, set_eq, incl.
  simpl.
  setoid_rewrite filter_In. setoid_rewrite bool_decide_eq_true.
  setoid_rewrite known_equivocators_is_equivocating_tracewise_char.
  split; intros; [apply proj2 in H; assumption|].
  split; [apply finite_validator| assumption].
Qed.


Lemma eq_globally_known_equivocators_equivocation_fault
  : forall s1 s2,
    set_eq (globally_known_equivocators s1) (globally_known_equivocators s2) ->
    equivocation_fault s1 = equivocation_fault s2.
Proof.
  intros.
  apply
    (set_eq_nodup_sum_weight_eq
      (equivocating_validators s1)
      (equivocating_validators s2)
    ).
  - apply NoDup_filter. apply state_validators_nodup. 
  - apply NoDup_filter. apply state_validators_nodup. 
  - apply (set_eq_tran (equivocating_validators s1) (globally_known_equivocators s1) (equivocating_validators s2))
    ; [apply globally_known_equivocators_equivocating_validators|].
    apply (set_eq_tran (globally_known_equivocators s1) (globally_known_equivocators s2) (equivocating_validators s2))
    ; [assumption|].
    apply set_eq_comm. apply globally_known_equivocators_equivocating_validators.
Qed.

Lemma incl_globally_known_equivocators_equivocation_fault
  : forall s1 s2,
    incl (globally_known_equivocators s1) (globally_known_equivocators s2) ->
    (equivocation_fault s1 <= equivocation_fault s2)%R.
Proof.
  intros.
  apply
    (sum_weights_incl
      (equivocating_validators s1)
      (equivocating_validators s2)
    ).
  - apply NoDup_filter. apply state_validators_nodup. 
  - apply NoDup_filter. apply state_validators_nodup. 
  - specialize (globally_known_equivocators_equivocating_validators s1) as Hs1.
    specialize (globally_known_equivocators_equivocating_validators s2) as Hs2.
    apply proj1 in Hs1. apply proj2 in Hs2.
    specialize (incl_tran H Hs2) as Hs12.
    revert Hs1 Hs12. apply incl_tran.
Qed.

Lemma initial_state_equivocators_weight
  (s : composite_state IM)
  (Hs : composite_initial_state_prop IM s)
  : equivocation_fault s = 0%R.
Proof.
  apply known_equivocators_empty_in_initial_state in Hs.
  assert (sum_weights (globally_known_equivocators s) = 0%R).
  { rewrite Hs. reflexivity. }
  rewrite <- H.
  apply set_eq_nodup_sum_weight_eq.
  - apply NoDup_filter. apply state_validators_nodup.
  - apply known_equivocators_nodup.
  - apply globally_known_equivocators_equivocating_validators.
Qed.

Lemma composite_transition_None_equivocators_weight
  l s s' om'
  (Ht : protocol_transition (pre_loaded_with_all_messages_vlsm (free_composite_vlsm IM)) l (s, None) (s', om'))
  : (equivocation_fault s' <= equivocation_fault s)%R.
Proof.
  specialize (protocol_transition_receiving_None_reflects_known_equivocators _ _ _ _ Ht) as Heqv.
  revert Heqv.
  apply incl_globally_known_equivocators_equivocation_fault.
Qed.

End known_equivocators_properties.
End known_equivocators.

Section known_equivocators_fixed_set.

Context
  {message : Type}
  {index : Type}
  {IndEqDec : EqDecision index}
  {index_listing : list index}
  (finite_index : Listing index_listing)
  (IM : index -> VLSM message)
  (Hbs : forall i, has_been_sent_capability (IM i))
  (Hbr : forall i, has_been_received_capability (IM i))
  (Hbo := fun i => has_been_observed_capability_from_sent_received (IM i))
  (i0 : Inhabited index)
  (Free := free_composite_vlsm IM)
  (sender : message -> option index)
  (globally_known_equivocators : composite_state IM -> set index)
  .


Definition known_equivocators_fixed_equivocation_constraint
  (s : composite_state IM)
  (ke := globally_known_equivocators s)
  : composite_label IM -> composite_state IM * option message -> Prop
  :=
  match null_dec ke with
  | left _ => composite_no_equivocations IM Hbs
  | right n => fixed_equivocation_constraint IM Hbs Hbr ke n finite_index
  end.

Definition known_equivocators_fixed_equivocation_characterization : Prop :=
  forall s,
    protocol_state_prop Free s ->
    exists s0 tr
      (Y := composite_vlsm IM (known_equivocators_fixed_equivocation_constraint s)),
      finite_protocol_trace_init_to Y s0 s tr.

End known_equivocators_fixed_set.