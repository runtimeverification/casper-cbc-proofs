From CasperCBC.stdpp Require Import base decidable numbers.
From Coq Require Import Vectors.Fin FinFun ListSet Arith.Compare_dec Lia Reals Program JMeq.
From CasperCBC Require Import Lib.Preamble Lib.ListExtras Lib.FinExtras Lib.Measurable.
From CasperCBC Require Import VLSM.Common VLSM.Composition VLSM.Equivocation.
From CasperCBC Require Import VLSM.Equivocators.Common VLSM.Equivocators.Projections.
From CasperCBC Require Import VLSM.Equivocators.MessageProperties VLSM.Equivocators.Composition.Common.

(** * VLSM Limited Equivocation *)

Section equivocators_composition_projections.

Context {message : Type}
  (index := Type)
  {IndEqDec : EqDecision index}
  (IM : index -> VLSM message)
  (Hbs : forall i : index, has_been_sent_capability (IM i))
  {i0 : Inhabited index}
  (X := free_composite_vlsm IM)
  (index_listing : list index)
  (finite_index : Listing index_listing)
  (equivocator_descriptors := equivocator_descriptors IM)
  (equivocators_state_project := equivocators_state_project IM)
  (equivocator_IM := equivocator_IM IM)
  (equivocator_descriptors_update := equivocator_descriptors_update IM)
  (proper_equivocator_descriptors := proper_equivocator_descriptors IM)
  {Hmeasurable : Measurable index}
  (equivocating : set index)
  {reachable_threshold : ReachableThreshold index}
  .

Definition equivocators_limited_equivocations_constraint
  (l : composite_label equivocator_IM)
  (som : composite_state equivocator_IM * option message)
  (som' := composite_transition equivocator_IM l som)
  : Prop
  := equivocators_no_equivocations_constraint IM Hbs finite_index l som
  /\ (sum_weights (equivocating_indices IM index_listing (fst som'))
      <= proj1_sig threshold)%R.

Definition equivocators_limited_equivocations_vlsm
  : VLSM message
  :=
  composite_vlsm equivocator_IM equivocators_limited_equivocations_constraint.

End equivocators_composition_projections.
