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
  forall i : nat, (@state _ (IS i)).

Definition indexed_label
  {message : Type}
  (IS : nat -> LSM_sig message)
  : Type
  := sigT (fun i => @label _ (IS i)).

Definition indexed_proto_message_prop
  {message : Type}
  (IS : nat -> LSM_sig message)
  (m : message)
  : Prop
  :=
  exists i : nat, @proto_message_prop message (IS i) m.

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
  forall i : nat, @initial_state_prop _ (IS i) (s i).

Definition indexed_initial_state
  {message : Type}
  (IS : nat -> LSM_sig message)
  := { s : indexed_state IS | indexed_initial_state_prop IS s }.

Definition indexed_s0
  {message : Type}
  (IS : nat -> LSM_sig message)
  : indexed_initial_state IS.
exists (fun (i : nat) => proj1_sig (@s0 _ (IS i))).
intro i. destruct s0 as [s Hs]. assumption.
Defined.

Definition indexed_initial_message_prop
  {message : Type}
  (IS : nat -> LSM_sig message)
  (m : indexed_proto_message IS)
  : Prop
  :=
  exists (i : nat) (mi : @initial_message _ (IS i)), proj1_sig (proj1_sig mi) = proj1_sig m.


Definition indexed_m0
  {message : Type}
  (IS : nat -> LSM_sig message)
  (i0 : nat)
  : indexed_proto_message IS
  .
destruct (@m0 _ (IS i0)) as [m Hpm].
exists m. exists i0. assumption.
Defined.

Definition indexed_l0
  {message : Type}
  (IS : nat -> LSM_sig message)
  (i0 : nat)
  : indexed_label IS
  := existT _ i0 (@l0 message (IS i0)) .

Definition lift_proto_messageI
  {message : Type}
  (IS : nat -> LSM_sig message)
  (i : nat)
  (mi : @proto_message _ (IS i))
  : indexed_proto_message IS.
destruct mi as [m Hm].
exists m. exists i. assumption.
Defined.


Definition indexed_sig
  {message : Type} 
  (IS : nat -> LSM_sig message)
  (i0 : nat)
  : LSM_sig message
  :=
  {| state := indexed_state IS
  ; label := indexed_label IS
  ; proto_message_prop := indexed_proto_message_prop IS
  ; proto_message_decidable := indexed_proto_message_decidable IS
  ; initial_state_prop := indexed_initial_state_prop IS
  ; s0 := indexed_s0 IS
  ; initial_message_prop := indexed_initial_message_prop IS
  ; m0 := indexed_m0 IS i0
  ; l0 := indexed_l0 IS i0
  |}.

Definition state_update
  {message : Type} 
  {IS : nat -> LSM_sig message}
  {i0 : nat}
  (s : @state message (indexed_sig IS i0))
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
  (IM : forall i : nat, @VLSM message (IS i))
  {Hinh : nat}
  (l : @label _ (indexed_sig IS Hinh))
  (som : @state _ (indexed_sig IS Hinh) * option (@proto_message _ (indexed_sig IS Hinh)))
  : @state _ (indexed_sig IS Hinh) * option (@proto_message _ (indexed_sig IS Hinh)).
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
  (IM : forall i : nat, @VLSM message (IS i))
  {Hinh : nat}
  (l : @label _ (indexed_sig IS Hinh))
  (som : @state _ (indexed_sig IS Hinh) * option (@proto_message _ (indexed_sig IS Hinh)))
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
  {IM : forall i : nat, @VLSM message (IS i)}
  (IDM : forall i : nat, @VLSM_vdecidable _ _ (IM i))
  {Hinh : nat}
  (l : @label _ (indexed_sig IS Hinh))
  (som : @state _ (indexed_sig IS Hinh) * option (@proto_message _ (indexed_sig IS Hinh)))
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
  (IM : forall i : nat, @VLSM message (IS i))
  {Hinh : nat}
  (constraint : indexed_label IS -> indexed_state IS * option (indexed_proto_message IS) -> Prop)
  (l : @label _ (indexed_sig IS Hinh))
  (som : @state _ (indexed_sig IS Hinh) * option (@proto_message _ (indexed_sig IS Hinh)))
  :=
  indexed_valid IM l som /\ constraint l som.


Definition indexed_vlsm_constrained
  {message : Type} 
  {IS : nat -> LSM_sig message}
  (IM : forall i : nat, @VLSM message (IS i))
  (Hi : nat)
  (constraint : indexed_label IS -> indexed_state IS * option (indexed_proto_message IS) -> Prop)
  : @VLSM message (indexed_sig IS Hi)
  :=
  {|  transition := indexed_transition IM
  ;   valid := indexed_valid_constrained IM constraint
  |}.

Definition indexed_valid_constrained_decidable
  {message : Type} 
  {IS : nat -> LSM_sig message}
  {IM : forall i : nat, @VLSM message (IS i)}
  (IDM : forall i : nat, @VLSM_vdecidable _ _ (IM i))
  {Hinh : nat}
  {constraint : indexed_label IS -> indexed_state IS * option (indexed_proto_message IS) -> Prop}
  (constraint_decidable : forall (l : indexed_label IS) (som : indexed_state IS * option (indexed_proto_message IS)), {constraint l som} + {~constraint l som})
  (l : @label _ (indexed_sig IS Hinh))
  (som : @state _ (indexed_sig IS Hinh) * option (@proto_message _ (indexed_sig IS Hinh)))
  : {@valid _ _ (indexed_vlsm_constrained IM Hinh constraint) l som} + {~@valid _ _ (indexed_vlsm_constrained IM Hinh constraint) l som}.
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
  {IM : forall i : nat, @VLSM message (IS i)}
  (IDM : forall i : nat, @VLSM_vdecidable _ _ (IM i))
  (Hinh : nat)
  {constraint : indexed_label IS -> indexed_state IS * option (indexed_proto_message IS) -> Prop}
  (constraint_decidable : forall (l : indexed_label IS) (som : indexed_state IS * option (indexed_proto_message IS)), {constraint l som} + {~constraint l som})
  : @VLSM_vdecidable _ _ (indexed_vlsm_constrained IM Hinh constraint)
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
  (IM : forall i : nat, @VLSM message (IS i))
  (Hi : nat)
  : @VLSM message (indexed_sig IS Hi)
  :=
  indexed_vlsm_constrained IM Hi free_constraint
  .

Definition indexed_vlsm_free_vdecidable
  {message : Type} 
  {IS : nat -> LSM_sig message}
  {IM : forall i : nat, @VLSM message (IS i)}
  (IDM : forall i : nat, @VLSM_vdecidable _ _ (IM i))
  (Hi : nat)
  : @VLSM_vdecidable _ _ (indexed_vlsm_free IM Hi)
  :=
  indexed_vlsm_constrained_vdecidable IDM Hi free_constraint_decidable.
