Require Import
  List Coq.Vectors.Fin FinFun ListSet
  Arith.Compare_dec Lia
  Program Program.Equality
  Coq.Logic.JMeq
  .
Import ListNotations.
From CasperCBC
  Require Import
    Preamble ListExtras FinExtras
    VLSM.Common VLSM.Composition VLSM.Equivocation
    VLSM.Equivocators.Common VLSM.Equivocators.Projections
    VLSM.Equivocators.MessageProperties
    VLSM.Equivocators.Composition.Common
    .

Section equivocators_fixed_equivocations_vlsm.

Context
  {message : Type}
  (index : Type)
  {IndEqDec : EqDecision index}
  (IM : index -> VLSM message)
  (Hbs : forall i : index, has_been_sent_capability (IM i))
  (i0 : index)
  (equivocator_IM := equivocator_IM IM)
  (index_listing : list index)
  (finite_index : Listing index_listing)
  (equivocating : set index)
  .

Definition equivocators_fixed_equivocations_constraint
  (l : composite_label equivocator_IM)
  (som : composite_state equivocator_IM * option message)
  (som' := composite_transition equivocator_IM l som)
  : Prop
  := equivocators_no_equivocations_constraint IM Hbs i0 index_listing finite_index l som
  /\ incl (equivocating_indices IM index_listing (fst som')) equivocating.

Definition equivocators_fixed_equivocations_vlsm
  : VLSM message
  :=
  equivocators_constrained_vlsm IM i0 equivocators_fixed_equivocations_constraint.

End equivocators_fixed_equivocations_vlsm.

Section fixed_equivocation_without_fullnode.

Context {message : Type}
  (index : Type)
  {IndEqDec : EqDecision index}
  (IM : index -> VLSM message)
  (Hbs : forall i : index, has_been_sent_capability (IM i))
  (i0 : index)
  (X := free_composite_vlsm IM i0)
  (index_listing : list index)
  (finite_index : Listing index_listing)
  (equivocators_choice := equivocators_choice IM)
  (equivocators_state_project := equivocators_state_project IM i0)
  (equivocator_IM := equivocator_IM IM)
  (equivocators_choice_update := equivocators_choice_update IM)
  (proper_equivocators_choice := proper_equivocators_choice IM i0)
  (equivocating : set index)
  (i0_equiv : index)
  (Hi0_equiv : In i0_equiv equivocating)
  .

Definition index_equivocating_prop (i : index) : Prop := In i equivocating.

Local Instance index_equivocating_prop_dec
  (i : index)
  : Decision (index_equivocating_prop i).
Proof.
  apply in_dec. assumption.
Qed.

Definition equivocating_index : Type
  := dec_sig index_equivocating_prop.

Definition equivocating_i0 : equivocating_index
  := (@dec_exist _ _ index_equivocating_prop_dec _ Hi0_equiv).

Local Instance equivocating_index_eq_dec : EqDecision equivocating_index.
Proof.
  apply dec_sig_eq_dec. assumption.
Qed.

Definition equivocating_IM
  (ei : equivocating_index)
  : VLSM message
  := IM (proj1_sig ei).

Definition free_equivocating_vlsm_composition : VLSM message
  := free_composite_vlsm equivocating_IM equivocating_i0.

Definition sent_by_non_equivocating
  (s : composite_state IM)
  (m : message)
  : Prop
  :=
  exists
    (i : index)
    (Hi : ~In i equivocating),
    has_been_sent (IM i) (s i) m.

Definition seeded_free_equivocators_composition
  (messageSet : message -> Prop)
  := vlsm_add_initial_messages free_equivocating_vlsm_composition messageSet.

  Context
    {validator : Type}
    (A : validator -> index)
    (sender : message -> option validator)
    (Hsender_safety : Prop := sender_safety_prop IM i0 (free_constraint IM) A sender)
    .

Definition fixed_equivocation_constraint
  (l : composite_label IM)
  (som : composite_state IM * option message)
  : Prop
  :=
  let (s, om) := som in
  match om with
  | None => True
  | Some m =>
    let ov := sender m in
    match ov with
    | None => composite_initial_message_prop IM m
    | Some v =>
      let i := A v in
      if index_equivocating_prop_dec i
      then protocol_message_prop (seeded_free_equivocators_composition (sent_by_non_equivocating s)) m
      else has_been_sent (IM i) (s i) m
    end
  end.

Definition fixed_equivocation_vlsm_composition : VLSM message
  := composite_vlsm IM i0 fixed_equivocation_constraint.

End fixed_equivocation_without_fullnode.