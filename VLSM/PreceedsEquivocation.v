Require Import
  Coq.Classes.RelationClasses
  .

From CasperCBC
  Require Import
    Preamble
    CBC.Equivocation
    VLSM.Common Composition
    .

(** * VLSM equivocation based-on full-node-like  [HasEquivocation]

Given a [VLSM] X over a type of messages which [HasEquivocation], we say
that @X@ [HasPreceedsEquivocation] if [message_preceeds_fn] determines
a [StrictOrder] on the [protocol_message]s of @X@.
*)

Section PreceedsEquivocation.

  Context
    {message : Type}
    {Eqv : HasEquivocation message}
    (X : VLSM message).

  Class HasPreceedsEquivocation
    :=
    { protocol_message_preceeds
        (pm1 pm2 : byzantine_message X)
        : Prop
        := message_preceeds_fn (proj1_sig pm1) (proj1_sig pm2) = true
    ; protocol_message_preceeds_strict_order
      : StrictOrder protocol_message_preceeds
    }.

End PreceedsEquivocation.

Section composite_preceeds_equivocation.

  Context {message : Type}
    {Eqv : HasEquivocation message}
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
    (Heqv : HasPreceedsEquivocation X2)
    : HasPreceedsEquivocation X1.
  Proof.
    destruct Heqv as
      [ protocol_message_preceeds2
        [ protocol_message_preceeds2_irreflexive
          protocol_message_preceeds2_transitive
        ]
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
  Qed.

End composite_preceeds_equivocation.
