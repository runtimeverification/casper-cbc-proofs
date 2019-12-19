Require Import Logic.FunctionalExtensionality.


Require Import ClassicalDescription ClassicalChoice ChoiceFacts.

From Casper
Require Import preamble vlsm.

(*
Composition of indexed VLSMs.

Assumes classical logic (excluded middle) and the axiom of choice.
*)

Definition indexed_state
  {message : Type}
  (IS : nat -> LSM_sig message)
  : Type
  :=
  forall n : nat, (@state _ (IS n)).

Definition indexed_label
  {message : Type}
  (IS : nat -> LSM_sig message)
  : Type
  := sigT (fun n => @label _ (IS n)).

Definition indexed_proto_message_prop
  {message : Type}
  (IS : nat -> LSM_sig message)
  (m : message)
  : Prop
  :=
  exists n : nat, @proto_message_prop message (IS n) m.

Lemma indexed_proto_message_decidable
  {message : Type}
  (IS : nat -> LSM_sig message)
  : forall m : message, {indexed_proto_message_prop IS m} + {~indexed_proto_message_prop IS m}.
Proof.
  intros.
  apply excluded_middle_informative.
Qed.

Definition indexed_proto_message
  {message : Type}
  (IS : nat -> LSM_sig message)
  := { m : message | indexed_proto_message_prop IS m }.

Definition indexed_initial_state_prop
  {message : Type}
  (IS : nat -> LSM_sig message)
  (s : indexed_state IS)
  : Prop
  :=
  forall n : nat, @initial_state_prop _ (IS n) (s n).

Definition indexed_initial_state
  {message : Type}
  (IS : nat -> LSM_sig message)
  := { s : indexed_state IS | indexed_initial_state_prop IS s }.

Definition indexed_s0
  {message : Type}
  (IS : nat -> LSM_sig message)
  : indexed_initial_state IS.
exists (fun (n : nat) => proj1_sig (@s0 _ (IS n))).
intro i. destruct s0 as [s Hs]. assumption.
Defined.

Definition indexed_initial_message_prop
  {message : Type}
  (IS : nat -> LSM_sig message)
  (m : indexed_proto_message IS)
  : Prop
  :=
  exists (n : nat) (mi : @initial_message _ (IS n)), proj1_sig (proj1_sig mi) = proj1_sig m.

(* An explicit argument for the initial state witness is no longer required: *) 
Definition indexed_m0
  {message : Type}
  (IS : nat -> LSM_sig message)
  : indexed_proto_message IS. 
destruct (@m0 _ (IS 0)) as [m Hpm].
exists m. exists 0. assumption.
Defined.

Definition indexed_l0
  {message : Type}
  (IS : nat -> LSM_sig message)
  : indexed_label IS
  := existT _ 0 (@l0 message (IS 0)) .
 
Definition lift_proto_messageI
  {message : Type}
  (IS : nat -> LSM_sig message)
  (n : nat)
  (mi : @proto_message _ (IS n))
  : indexed_proto_message IS.
destruct mi as [m Hm].
exists m. exists n. assumption.
Defined.

Definition indexed_sig
  {message : Type} 
  (IS : nat -> LSM_sig message)
  : LSM_sig message
  :=
  {| state := indexed_state IS
  ; label := indexed_label IS
  ; proto_message_prop := indexed_proto_message_prop IS
  ; proto_message_decidable := indexed_proto_message_decidable IS
  ; initial_state_prop := indexed_initial_state_prop IS
  ; s0 := indexed_s0 IS
  ; initial_message_prop := indexed_initial_message_prop IS
  ; m0 := indexed_m0 IS 
  ; l0 := indexed_l0 IS 
  |}.

Definition state_update
  {message : Type} 
  {IS : nat -> LSM_sig message}
  (s : @state message (indexed_sig IS))
  (i : nat)
  (si : @state message (IS i))
  (j : nat)
  : @state message (IS j).
destruct (nat_eq_dec i j); subst.
- exact si.
- exact (s j).
Defined.

Definition indexed_transition
  {message : Type} 
  {IS : nat -> LSM_sig message}
  (IM : forall n : nat, @VLSM message (IS n))
  (l : @label _ (indexed_sig IS))
  (som : @state _ (indexed_sig IS) * option (@proto_message _ (indexed_sig IS)))
  : @state _ (indexed_sig IS) * option (@proto_message _ (indexed_sig IS)).
destruct som as [s om].
destruct l as [i li].
destruct om as [[m _]|].
- destruct (@proto_message_decidable _ (IS i) m) as [Hi | _].
  + destruct (transition li (s i, Some (exist _ m Hi))) as [si' om'].
    exact (state_update s i si', option_map (lift_proto_messageI IS i) om').
  + exact (s, None).
- destruct (transition li (s i, None)) as [si' om'].
    exact (state_update s i si', option_map (lift_proto_messageI IS i) om').
Defined.

Definition indexed_valid
  {message : Type} 
  {IS : nat -> LSM_sig message}
  (IM : forall n : nat, @VLSM message (IS n))
  (l : @label _ (indexed_sig IS))
  (som : @state _ (indexed_sig IS) * option (@proto_message _ (indexed_sig IS)))
  : Prop.
destruct som as [s om].
destruct l as [i li].
destruct om as [[m _]|].
- destruct (@proto_message_decidable _ (IS i) m) as [Hi | _].
  + exact (valid li (s i, Some (exist _ m Hi))).
  + exact False.
- exact (valid li (s i, None)).
Defined.

Definition indexed_valid_decidable
  {message : Type} 
  {IS : nat -> LSM_sig message}
  {IM : forall n : nat, @VLSM message (IS n)}
  (IDM : forall n : nat, @VLSM_vdecidable _ _ (IM n))
  (l : @label _ (indexed_sig IS))
  (som : @state _ (indexed_sig IS) * option (@proto_message _ (indexed_sig IS)))
  : {indexed_valid IM l som} + {~indexed_valid IM l som}.
destruct som as [s om].
destruct l as [i li]; simpl.
destruct om as [[m _]|]; simpl.
- destruct (@proto_message_decidable _ (IS i) m) as [Hi | _].
  + apply valid_decidable.
  + right; intro; contradiction.
- apply valid_decidable.
Defined.

(* Constrained VLSM composition *)

Definition indexed_valid_constrained
  {message : Type} 
  {IS : nat -> LSM_sig message}
  (IM : forall n : nat, @VLSM message (IS n))
  (constraint : indexed_label IS -> indexed_state IS * option (indexed_proto_message IS) -> Prop)
  (l : @label _ (indexed_sig IS))
  (som : @state _ (indexed_sig IS) * option (@proto_message _ (indexed_sig IS)))
  :=
  indexed_valid IM l som /\ constraint l som.


Definition indexed_vlsm_constrained
  {message : Type} 
  {IS : nat -> LSM_sig message}
  (IM : forall n : nat, @VLSM message (IS n))
  (constraint : indexed_label IS -> indexed_state IS * option (indexed_proto_message IS) -> Prop)
  : @VLSM message (indexed_sig IS)
  :=
  {|  transition := indexed_transition IM
  ;   valid := indexed_valid_constrained IM constraint
  |}.

Definition indexed_valid_constrained_decidable
  {message : Type} 
  {IS : nat -> LSM_sig message}
  {IM : forall n : nat, @VLSM message (IS n)}
  (IDM : forall n : nat, @VLSM_vdecidable _ _ (IM n))
  {constraint : indexed_label IS -> indexed_state IS * option (indexed_proto_message IS) -> Prop}
  (constraint_decidable : forall (l : indexed_label IS) (som : indexed_state IS * option (indexed_proto_message IS)), {constraint l som} + {~constraint l som})
  (l : @label _ (indexed_sig IS))
  (som : @state _ (indexed_sig IS) * option (@proto_message _ (indexed_sig IS)))
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
  {message : Type} 
  {IS : nat -> LSM_sig message}
  {IM : forall n : nat, @VLSM message (IS n)}
  (IDM : forall n : nat, @VLSM_vdecidable _ _ (IM n))
  {constraint : indexed_label IS -> indexed_state IS * option (indexed_proto_message IS) -> Prop}
  (constraint_decidable : forall (l : indexed_label IS) (som : indexed_state IS * option (indexed_proto_message IS)), {constraint l som} + {~constraint l som})
  : @VLSM_vdecidable _ _ (indexed_vlsm_constrained IM constraint)
  :=
  {|  valid_decidable := indexed_valid_constrained_decidable IDM constraint_decidable
  |}.


(* Free VLSM composition *)

Definition free_constraint 
  {message : Type} 
  {IS : nat -> LSM_sig message}
  (l : indexed_label IS)
  (som : indexed_state IS * option (indexed_proto_message IS))
  : Prop
  :=
  True.

Definition free_constraint_decidable
  {message : Type} 
  {IS : nat -> LSM_sig message}
  (l : indexed_label IS)
  (som : indexed_state IS * option (indexed_proto_message IS))
  : {free_constraint l som} + {~free_constraint l som}
  := left I.

Definition indexed_vlsm_free
  {message : Type} 
  {IS : nat -> LSM_sig message}
  (IM : forall n : nat, @VLSM message (IS n))
  : @VLSM message (indexed_sig IS)
  :=
  indexed_vlsm_constrained IM free_constraint
  .

Definition indexed_vlsm_free_vdecidable
  {message : Type} 
  {IS : nat -> LSM_sig message}
  {IM : forall n : nat, @VLSM message (IS n)}
  (IDM : forall n : nat, @VLSM_vdecidable _ _ (IM n))
  : @VLSM_vdecidable _ _ (indexed_vlsm_free IM)
  :=
  indexed_vlsm_constrained_vdecidable IDM free_constraint_decidable.
