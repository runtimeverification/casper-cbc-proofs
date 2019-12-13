From Casper
Require Import preamble vlsm composed_vlsm composed_vlsm_projections indexed_vlsm.

Definition indexed_vlsm_projection
  {message : Type}
  {oindex : Set} {message : Type} `{Heqd : EqDec oindex}
  (IS : oindex -> LSM_sig message)
  (IM : forall i : oindex, @VLSM message (IS i))
  (i : oindex)
  : VLSM (message : Type)
  :=
  @vlsm_projection message
    (indexed_sig IS i)
    (indexed_sig_composed_instance IS i)
    (indexed_vlsm IM i)
    (@indexed_vlsm_composed_instance oindex message Heqd IS IM i)
    i
  .

(* Definition indexed_vlsm_constrained_projection
  {oindex : Set} {message : Type} `{Heqd : EqDec oindex}
  (IS : oindex -> LSM_sig message)
  (IM : forall i : oindex, @VLSM message (IS i))
  (constraint : indexed_label IS -> indexed_state IS * option (indexed_proto_message IS) -> Prop)
  (i : oindex)
  : VLSM (message : Type)
  :=
  @vlsm_projection message
    (indexed_sig IS (inhabits i))
    (indexed_sig_composed_instance IS (inhabits i))
    (indexed_vlsm_constrained IS (inhabits i) constraint)
    (@indexed_vlsm_constrained_composed_instance oindex message Heqd IS (inhabits i) constraint)
    i
  .

 *)
