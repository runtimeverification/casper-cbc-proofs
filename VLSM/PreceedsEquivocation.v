Require Import
  Coq.Classes.RelationClasses
  .

From CasperCBC
  Require Import
    CBC.Equivocation
    VLSM.Common
    .

Section PreceedsEquivocation.

  Context
    {message : Type}
    {vtype : VLSM_type message}
    {Sig : VLSM_sign vtype}
    {Eqv : HasEquivocation message}
    (X : VLSM Sig).
  
  Class HasPreceedsEquivocation
    :=
    { protocol_message_preceeds
        (pm1 pm2 : protocol_message X)
        : Prop
        := message_preceeds (proj1_sig pm1) (proj1_sig pm2)
    ; protocol_message_preceeds_strict_order
      : StrictOrder protocol_message_preceeds
    }.
  
End PreceedsEquivocation.