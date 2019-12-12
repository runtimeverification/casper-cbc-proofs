From Casper
Require Import vlsm indexed_vlsm.

Definition indexed_vlsm_constrained_projection_sig
  {index : Set} {message : Type} `{Heqd : EqDec index}
  {IS : index -> LSM_sig message}
  (IM : forall i : index, @VLSM message (IS i))
  (Hi : index)
  (constraint : indexed_label IS -> indexed_state IS * option (indexed_proto_message IS) -> Prop)
  (X := indexed_vlsm_constrained IM Hi constraint)
  (i : index)
  : LSM_sig message
  :=
  {|  state := @state _ (IS i)
  ;   label := @label _ (IS i)
  ;   proto_message_prop := @proto_message_prop _ (IS i)
  ;   proto_message_decidable := @proto_message_decidable _ (IS i)
  ;   initial_state_prop := @initial_state_prop _ (IS i)
  ;   initial_message_prop := fun pmi => exists xm : (@protocol_message _ _ X), proj1_sig (proj1_sig xm) = proj1_sig pmi
  ;   s0 := @s0 _ (IS i)
  ;   m0 := @m0 _ (IS i)
  ;   l0 := @l0 _ (IS i)
  |}.


Definition indexed_vlsm_free_projection_sig
  {index : Set} {message : Type} `{Heqd : EqDec index}
  {IS : index -> LSM_sig message}
  (IM : forall i : index, @VLSM message (IS i))
  (Hi : index)
  (i : index)
  : LSM_sig message
  :=
  indexed_vlsm_constrained_projection_sig IM Hi free_constraint i.

Definition indexed_vlsm_constrained_projection
  {index : Set} {message : Type} `{Heqd : EqDec index}
  {IS : index -> LSM_sig message}
  (IM : forall i : index, @VLSM message (IS i))
  (Hi : index)
  (constraint : indexed_label IS -> indexed_state IS * option (indexed_proto_message IS) -> Prop)
  (S := indexed_sig IS Hi)
  (X := indexed_vlsm_constrained IM Hi constraint)
  (i : index)
  : @VLSM message (indexed_vlsm_constrained_projection_sig IM Hi constraint i).
unfold indexed_vlsm_constrained_projection_sig; simpl.
split; simpl; unfold proto_message; simpl.
- exact (@transition _ _ (IM i)).
- intros l som. destruct (@transition _ _ (IM i) l som) as  [si' omi']. 
  exact
    (   @valid _ _ (IM i) l som
    /\  exists s' : @protocol_state _ _ X, exists om' : option (@protocol_message _ _ X),
          (  (proj1_sig s') i = si'
          /\ option_map (@proj1_sig _ _) (option_map (@proj1_sig _ _) om') = option_map (@proj1_sig _ _) omi' 
          )
    ).
Defined.

Definition indexed_vlsm_free_projection
  {index : Set} {message : Type} `{Heqd : EqDec index}
  {IS : index -> LSM_sig message}
  (IM : forall i : index, @VLSM message (IS i))
  (Hi : index)
  (i : index)
  : @VLSM message (indexed_vlsm_free_projection_sig IM Hi i)
  :=
  indexed_vlsm_constrained_projection IM Hi free_constraint i.

