Require Import Logic.FunctionalExtensionality.

Require Import ClassicalDescription ClassicalChoice ChoiceFacts.

From Casper
     Require Import preamble vlsm.

(*
Composition of indexed VLSMs.

Assumes classical logic (excluded middle) and the axiom of choice.
 *)

Section indexing. 

  Context {message : Type}
          {index : Type}
          {IndEqDec : EqDec index}
          (i0 : index)
          (IS : index -> LSM_sig message).

  Definition indexed_state : Type :=
    forall n : index, (@state _ (IS n)).

  Definition indexed_label
    : Type
    := sigT (fun n => @label _ (IS n)).

  Definition indexed_proto_message_prop
             (m : message)
    : Prop
    :=
      exists n : index, @proto_message_prop message (IS n) m.

  Lemma indexed_proto_message_decidable
    : forall m : message, {indexed_proto_message_prop m} + {~indexed_proto_message_prop m}.
  Proof.
    intros.
    apply excluded_middle_informative.
  Qed.

  Definition indexed_proto_message
    := { m : message | indexed_proto_message_prop m }.

  Definition indexed_initial_state_prop
             (s : indexed_state)
    : Prop
    :=
      forall n : index, @initial_state_prop _ (IS n) (s n).

  Definition indexed_initial_state
    := { s : indexed_state | indexed_initial_state_prop s }.

  Definition indexed_s0
    : indexed_initial_state.
    exists (fun (n : index) => proj1_sig (@s0 _ (IS n))).
    intro i. destruct s0 as [s Hs]. assumption.
  Defined.

  Definition indexed_initial_message_prop
             (m : indexed_proto_message)
    : Prop
    :=
      exists (n : index) (mi : @initial_message _ (IS n)), proj1_sig (proj1_sig mi) = proj1_sig m.

  (* An explicit argument for the initial state witness is no longer required: *) 
  Definition indexed_m0
    : indexed_proto_message.
    destruct (@m0 _ (IS i0)) as [m Hpm].
    exists m. exists i0. assumption.
  Defined.

  Definition indexed_l0
    : indexed_label
    := existT _ i0 (@l0 message (IS i0)) .
  
  Definition lift_proto_messageI
             (n : index)
             (mi : @proto_message _ (IS n))
    : indexed_proto_message.
    destruct mi as [m Hm].
    exists m. exists n. assumption.
  Defined.

  Definition indexed_sig
    : LSM_sig message
    :=
      {| state := indexed_state 
         ; label := indexed_label
         ; proto_message_prop := indexed_proto_message_prop
         ; proto_message_decidable := indexed_proto_message_decidable
         ; initial_state_prop := indexed_initial_state_prop
         ; s0 := indexed_s0
         ; initial_message_prop := indexed_initial_message_prop
         ; m0 := indexed_m0
         ; l0 := indexed_l0 
      |}.

  Definition state_update
             (s : @state message (indexed_sig))
             (i : index)
             (si : @state message (IS i))
             (j : index)
    : @state message (IS j).
    destruct (eq_dec i j); subst.
    - exact si.
    - exact (s j).
  Defined.

  Definition indexed_transition
             (IM : forall n : index, @VLSM message (IS n))
             (l : @label _ (indexed_sig))
             (som : @state _ (indexed_sig) * option (@proto_message _ (indexed_sig)))
    : @state _ (indexed_sig) * option (@proto_message _ (indexed_sig)).
    destruct som as [s om].
    destruct l as [i li].
    destruct om as [[m _]|].
    - destruct (@proto_message_decidable _ (IS i) m) as [Hi | _].
      + destruct (@transition _ _ _ li (s i, Some (exist _ m Hi))) as [si' om'].
        exact (state_update s i si', option_map (lift_proto_messageI i) om').
      + exact (s, None).
    - destruct (@transition _ _ _ li (s i, None)) as [si' om'].
      exact (state_update s i si', option_map (lift_proto_messageI i) om').
  Defined.

  Definition indexed_valid
             (IM : forall n : index, @VLSM message (IS n))
             (l : @label _ (indexed_sig))
             (som : @state _ (indexed_sig) * option (@proto_message _ (indexed_sig)))
    : Prop.
    destruct som as [s om].
    destruct l as [i li].
    destruct om as [[m _]|].
    - destruct (@proto_message_decidable _ (IS i) m) as [Hi | _].
      + exact (@valid _ _ _ li (s i, Some (exist _ m Hi))).
      + exact False.
    - exact (@valid _ _ _ li (s i, None)).
  Defined.

  Definition indexed_valid_decidable
             {IM : forall n : index, @VLSM message (IS n)}
             (IDM : forall n : index, @VLSM_vdecidable _ _ (IM n))
             (l : @label _ (indexed_sig))
             (som : @state _ (indexed_sig) * option (@proto_message _ (indexed_sig)))
    : {indexed_valid IM l som} + {~indexed_valid IM l som}.
    destruct som as [s om].
    destruct l as [i li]; simpl.
    destruct om as [[m _]|]; simpl.
    - destruct (@proto_message_decidable _ (IS i) m) as [Hi | _].
      + apply valid_decidable.
        apply IDM; assumption. 
      + right; intro; contradiction.
    - apply valid_decidable.
      apply IDM; assumption.
  Defined.

  (* Constrained VLSM composition *)

  Definition indexed_valid_constrained
             (IM : forall n : index, @VLSM message (IS n))
             (constraint : indexed_label -> indexed_state * option (indexed_proto_message) -> Prop)
             (l : @label _ (indexed_sig))
             (som : @state _ (indexed_sig) * option (@proto_message _ (indexed_sig)))
    :=
      indexed_valid IM l som /\ constraint l som.

  Definition indexed_vlsm_constrained
             (IM : forall n : index, @VLSM message (IS n))
             (constraint : indexed_label -> indexed_state * option (indexed_proto_message) -> Prop)
    : @VLSM message (indexed_sig)
    :=
      {|  transition := indexed_transition IM
          ;   valid := indexed_valid_constrained IM constraint
      |}.

  Definition indexed_valid_constrained_decidable
             {IM : forall n : index, @VLSM message (IS n)}
             (IDM : forall n : index, @VLSM_vdecidable _ _ (IM n))
             {constraint : indexed_label -> indexed_state * option (indexed_proto_message) -> Prop}
             (constraint_decidable : forall (l : indexed_label) (som : indexed_state * option (indexed_proto_message)), {constraint l som} + {~constraint l som})
             (l : @label _ (indexed_sig))
             (som : @state _ (indexed_sig) * option (@proto_message _ (indexed_sig)))
    : {@valid _ _ (indexed_vlsm_constrained IM constraint) l som} + {~@valid _ _ (indexed_vlsm_constrained IM constraint) l som}.
    intros.
    unfold indexed_valid_constrained.
    destruct (constraint_decidable l som) as [Hc | Hnc].
    - destruct (indexed_valid_decidable IDM l som) as [Hv | Hnv].
      + left. split; try assumption.
      + right. intros [Hv _]. contradiction.
    - right. intros [_ Hc]. contradiction.
  Defined.

  Definition indexed_vlsm_constrained_vdecidable
             {IM : forall n : index, @VLSM message (IS n)}
             (IDM : forall n : index, @VLSM_vdecidable _ _ (IM n))
             {constraint : indexed_label -> indexed_state * option (indexed_proto_message) -> Prop}
             (constraint_decidable : forall (l : indexed_label) (som : indexed_state * option (indexed_proto_message)), {constraint l som} + {~constraint l som})
    : @VLSM_vdecidable _ _ (indexed_vlsm_constrained IM constraint)
    :=
      {|  valid_decidable := indexed_valid_constrained_decidable IDM constraint_decidable
      |}.

  (* Free VLSM composition *)

  Definition free_constraint 
             (l : indexed_label)
             (som : indexed_state * option (indexed_proto_message))
    : Prop
    :=
      True.

  Definition free_constraint_decidable
             (l : indexed_label)
             (som : indexed_state * option (indexed_proto_message))
    : {free_constraint l som} + {~free_constraint l som}
    := left I.

  Definition indexed_vlsm_free
             (IM : forall n : index, @VLSM message (IS n))
    : @VLSM message (indexed_sig)
    :=
      indexed_vlsm_constrained IM free_constraint
  .

  Definition indexed_vlsm_free_vdecidable
             {IM : forall n : index, @VLSM message (IS n)}
             (IDM : forall n : index, @VLSM_vdecidable _ _ (IM n))
    : @VLSM_vdecidable _ _ (indexed_vlsm_free IM)
    :=
      indexed_vlsm_constrained_vdecidable IDM free_constraint_decidable.

  (* From indexed_vlsm_projections.v *)
  Section projections. 

    Definition indexed_vlsm_constrained_projection_sig
               (IM : forall n : index, VLSM (IS n))
               (constraint : indexed_label -> indexed_state * option (indexed_proto_message) -> Prop)
               (X := indexed_vlsm_constrained IM constraint)
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
               (IM : forall i : index, VLSM (IS i))
               (i : index)
      : LSM_sig message
      :=
        indexed_vlsm_constrained_projection_sig IM free_constraint i.

    Definition indexed_vlsm_constrained_projection
               (IM : forall i : index, VLSM (IS i))
               (constraint : indexed_label -> indexed_state * option (indexed_proto_message) -> Prop)
               (S := indexed_sig)
               (X := indexed_vlsm_constrained IM constraint)
               (i : index)
      : VLSM (indexed_vlsm_constrained_projection_sig IM constraint i).
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
               (IM : forall i : index, VLSM (IS i))
               (i : index)
      : VLSM (indexed_vlsm_free_projection_sig IM i)
      :=
        indexed_vlsm_constrained_projection IM free_constraint i.

  End projections.
  
End indexing.
