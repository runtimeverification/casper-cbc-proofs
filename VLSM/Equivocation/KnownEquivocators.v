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
  (IM : index -> VLSM message)
  (i0 : Inhabited index)
  (Hbs : forall i : index, has_been_sent_capability (IM i))
  (Hbr : forall i : index, has_been_received_capability (IM i))
  (validator : Type)
  (A : validator -> index)
  (sender : message -> option validator)
  .

Class known_equivocators_capability
  (globally_known_equivocators : composite_state IM -> set validator)
  :=
  { known_equivocators_nodup :
    forall s, NoDup (globally_known_equivocators s)
  ; known_equivocators_transition_None :
      forall
        l s s' oom,
        composite_transition IM l (s, None) = (s', oom) ->
        set_eq (globally_known_equivocators s') (globally_known_equivocators s)
  ; known_equivocators_exhibit_message_equivocation :
    forall s v,
      In v (globally_known_equivocators s) -> is_equivocating_statewise IM Hbs A sender Hbr s v
  }.

Section known_equivocators_properties.

Context 
  (globally_known_equivocators : composite_state IM -> set validator)
  (Hke : known_equivocators_capability globally_known_equivocators)
  .

Lemma known_equivocators_initial_state
  (s : composite_state IM)
  (His : composite_initial_state_prop IM s)
  : globally_known_equivocators s = [].
Proof.
  specialize (known_equivocators_exhibit_message_equivocation s) as Heqv.
  destruct (globally_known_equivocators s); [reflexivity|].
  specialize (Heqv v).
  spec Heqv. { left. reflexivity. }
  apply initial_state_is_not_equivocating with (A0 := A) (sender0 := sender) (has_been_sent_capabilities := Hbs) (has_been_received_capabilities := Hbr) (v0 := v) in His.
  contradiction.
Qed.

Context
  {ValMeasurable : Measurable validator}
  {EqDecision : EqDecision validator}
  {threshold_V : ReachableThreshold validator}
  (validator_listing : list validator)
  (finite_validator : Listing validator_listing)
  .


Program Instance known_equivocators_basic_equivocation : basic_equivocation (composite_state IM) validator
:= {
  is_equivocating := fun s v => In v (globally_known_equivocators s) ;
  state_validators := fun s => validator_listing
}.
Next Obligation.
  intro. intros.
  apply in_dec. assumption.
Qed.
Next Obligation.
  apply finite_validator.
Qed.

Lemma globally_known_equivocators_equivocating_validators
  : forall s, set_eq (equivocating_validators s) (globally_known_equivocators s).
Proof.
  intro s.
  unfold equivocating_validators, is_equivocating, set_eq, incl.
  simpl.
  setoid_rewrite filter_In. setoid_rewrite bool_decide_eq_true.
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

Lemma initial_state_equivocators_weight
  (s : composite_state IM)
  (Hs : composite_initial_state_prop IM s)
  : equivocation_fault s = 0%R.
Proof.
  apply known_equivocators_initial_state in Hs.
  assert (sum_weights (globally_known_equivocators s) = 0%R).
  { rewrite Hs. reflexivity. }
  rewrite <- H.
  apply set_eq_nodup_sum_weight_eq.
  - apply NoDup_filter. apply state_validators_nodup.
  - apply known_equivocators_nodup.
  - apply globally_known_equivocators_equivocating_validators.
Qed.

Lemma composite_transition_None_equivocators_weight
  l s s' oom
  : composite_transition IM l (s, None) = (s', oom) ->
    equivocation_fault s' = equivocation_fault s.
Proof.
  intro Ht.
  specialize (known_equivocators_transition_None _ _ _ _ Ht) as Heqv.
  revert Heqv.
  apply eq_globally_known_equivocators_equivocation_fault.
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