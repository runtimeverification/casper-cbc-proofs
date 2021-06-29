From Coq Require Import List ListSet FinFun Rdefinitions.
Import ListNotations.

From CasperCBC Require Import Lib.Preamble Lib.ListSetExtras Lib.Measurable VLSM.Common VLSM.MessageDependencies VLSM.Composition
  VLSM.Equivocation VLSM.Equivocation.KnownEquivocators.

Section limited_message_equivocation.

Context
  {message : Type}
  {index : Type}
  {IndEqDec : EqDecision index}
  {index_listing : list index}
  (finite_index : Listing index_listing)
  {ValMeasurable : Measurable index}
  (IM : index -> VLSM message)
  (Hbs : forall i, has_been_sent_capability (IM i))
  (Hbr : forall i, has_been_received_capability (IM i))
  (Hbo := fun i => has_been_observed_capability_from_sent_received (IM i))
  (i0 : Inhabited index)
  (X := free_composite_vlsm IM)
  (X_has_been_sent_capability : has_been_sent_capability X := free_composite_has_been_sent_capability IM finite_index Hbs)
  (X_has_been_received_capability : has_been_received_capability X := free_composite_has_been_received_capability IM finite_index Hbr)
  (X_has_been_observed_capability : has_been_observed_capability X := has_been_observed_capability_from_sent_received X)
  (sender : message -> option index)
  {Hdm : MessageDependencies sender (fun i => i) IM}
  {reachable_threshold : ReachableThreshold index}
  (globally_known_equivocators : composite_state IM -> set index)
  {Hknown_equivocators : known_equivocators_capability IM Hbs Hbr index  (fun i => i) sender globally_known_equivocators}
  (Hknown_equivocators_basic_equivocation := known_equivocators_basic_equivocation IM index globally_known_equivocators _ finite_index)
  .

Existing Instance Hknown_equivocators_basic_equivocation.

Definition full_node_limited_equivocation_constraint
  (l : composite_label IM)
  (som : composite_state IM * option message)
  :=
  message_dependencies_local_full_node_constraint l som /\
  let s' := fst (composite_transition IM l som) in
  not_heavy s'.


Definition full_node_limited_equivocation_vlsm_composition
  :=
  composite_vlsm IM full_node_limited_equivocation_constraint.

Lemma full_node_limited_equivocation_protocol_state_weight s
  : protocol_state_prop full_node_limited_equivocation_vlsm_composition s ->
    not_heavy s.
Proof.
  intro Hs.
  unfold not_heavy.
  induction Hs using protocol_state_prop_ind.
  - specialize (initial_state_equivocators_weight  _ _ _ _ _ _ _ _ _ finite_index s Hs)
      as Hrew.
    unfold Hknown_equivocators_basic_equivocation.
    unfold composite_state in Hrew. simpl in *.
    rewrite Hrew.
    destruct threshold. intuition.
  - destruct Ht as [[Hs [Hom [Hv [Hc Hw]]]] Ht].
    unfold transition in Ht. simpl in Ht.
    simpl in Hw.
    rewrite Ht in Hw.
    assumption.
Qed.

End limited_message_equivocation.
