Require Import
  Coq.Classes.RelationClasses
  .

From CasperCBC
  Require Import
    Preamble
    CBC.Equivocation
    VLSM.Common 
    VLSM.Composition
    VLSM.Equivocation
    .

(** * VLSM equivocation based-on full-node-like  [message_equivocation_evidence]

Given a [VLSM] X over a type of messages which [message_equivocation_evidence], we say
that @X@ has [vlsm_message_equivocation_evidence] if [message_preceeds_fn]
determines a [StrictOrder] on the [protocol_message]s of @X@.
*)

Section vlsm_message_equivocation_evidence.

  Context
    {message : Type}
    (validator : Type)
    `{Eqv : message_equivocation_evidence message validator}
    (X : VLSM message).

  Class vlsm_message_equivocation_evidence
    :=
    { protocol_message_preceeds
        (pm1 pm2 : byzantine_message X)
        : Prop
        := message_preceeds_fn (proj1_sig pm1) (proj1_sig pm2) = true
    ; protocol_message_preceeds_strict_order
      : StrictOrder protocol_message_preceeds
    ; evidence_of_equivocation
        (pm1 pm2 : byzantine_message X)
        (m1 := proj1_sig pm1)
        (m2 := proj1_sig pm2)
        (Heqv : equivocating_with m1 m2 = true)
        (s : state)
        (tr : list transition_item)
        (Htr : finite_protocol_trace (pre_loaded_vlsm X) s tr)
        (Hm1 : trace_has_message X input m1 tr)
        (Hm2 : trace_has_message X input m2 tr)
        : equivocation_in_trace X m1 tr
        \/ equivocation_in_trace X m2 tr
    }.

End vlsm_message_equivocation_evidence.

Section composite_preceeds_equivocation.

  Context
    {message validator : Type}
    `{Eqv : message_equivocation_evidence message validator}
    {index : Type}
    {IndEqDec : EqDec index}
    (IM : index -> VLSM message)
    (i0 : index)
    (constraint1 : composite_label IM -> composite_state IM * option message -> Prop)
    (constraint2 : composite_label IM -> composite_state IM * option message -> Prop)
    (Hsubsumption : constraint_subsumption IM constraint1 constraint2)
    (X1 := composite_vlsm IM i0 constraint1)
    (X2 := composite_vlsm IM i0 constraint2)
    .

  Lemma preceeds_equivocation_constrained
    (Heqv : vlsm_message_equivocation_evidence validator X2)
    : vlsm_message_equivocation_evidence validator X1.
  Proof.
    destruct Heqv as
      [ protocol_message_preceeds2
        [ protocol_message_preceeds2_irreflexive
          protocol_message_preceeds2_transitive
        ]
        Heqv
      ].
    specialize
      (constraint_subsumption_byzantine_message_prop
        IM i0 constraint1 constraint2 Hsubsumption
      ); intro Hem.
    repeat split.
    - intros [m1 Hem1].
      unfold complement. simpl.
      apply Hem in Hem1.
      specialize (protocol_message_preceeds2_irreflexive (exist _ m1 Hem1)).
      unfold complement in protocol_message_preceeds2_irreflexive.
      assumption.
    - intros [m1 Hem1] [m2 Hem2] [m3 Hem3]
      ; simpl.
      intros H12 H23.
      apply Hem in Hem1.
      apply Hem in Hem2.
      apply Hem in Hem3.
      specialize
        (protocol_message_preceeds2_transitive
          (exist _ m1 Hem1)
          (exist _ m2 Hem2)
          (exist _ m3 Hem3)
          H12
          H23
        ).
      assumption.
    - intros [m1 Hm1] [m2 Hm2]. simpl. intros.
      assert (Hm1': byzantine_message_prop X2 m1)
        by (apply constraint_subsumption_byzantine_message_prop with constraint1; assumption).
      assert (Hm2': byzantine_message_prop X2 m2)
        by (apply constraint_subsumption_byzantine_message_prop with constraint1; assumption).
      specialize (constraint_subsumption_pre_loaded_incl IM i0 constraint1 constraint2 Hsubsumption (@Finite _ (type X1) s tr) Htr)
        as Htrace'.
      simpl in Htrace'.
      specialize (Heqv (exist _ _ Hm1') (exist _ _ Hm2')). simpl in Heqv.
      specialize (Heqv Heqv0 s tr Htrace' Hm0 Hm3).
      assumption.
  Qed.

End composite_preceeds_equivocation.
