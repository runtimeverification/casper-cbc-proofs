Require Import Logic.FunctionalExtensionality.


Require Import ClassicalDescription ClassicalChoice ChoiceFacts.

From Casper
Require Import preamble vlsm.

(*
Composition of indexed VLSMs.

Assumes classical logic (excluded middle) and the axiom of choice.
*)

Definition indexed_state
  {index : Set} {message : Type}
  (IS : index -> LSM_sig message)
  : Type
  :=
  forall i : index, (@state _ (IS i)).

Definition indexed_label
  {index : Set} {message : Type}
  (IS : index -> LSM_sig message)
  : Type
  := sigT (fun i => @label _ (IS i)).

Definition indexed_proto_message_prop
  {index : Set} {message : Type}
  (IS : index -> LSM_sig message)
  (m : message)
  : Prop
  :=
  exists i : index, @proto_message_prop message (IS i) m.

Lemma indexed_proto_message_decidable
  {index : Set} {message : Type}
  (IS : index -> LSM_sig message)
  : forall m : message, {indexed_proto_message_prop IS m} + {~indexed_proto_message_prop IS m}.
Proof.
  intros.
  apply excluded_middle_informative.
Qed.

Definition indexed_proto_message
  {index : Set} {message : Type}
  (IS : index -> LSM_sig message)
  := { m : message | indexed_proto_message_prop IS m }.

Definition indexed_initial_state_prop
  {index : Set} {message : Type}
  (IS : index -> LSM_sig message)
  (s : indexed_state IS)
  : Prop
  :=
  forall i : index, @initial_state_prop _ (IS i) (s i).

Definition indexed_initial_state
  {index : Set} {message : Type}
  (IS : index -> LSM_sig message)
  := { s : indexed_state IS | indexed_initial_state_prop IS s }.

Definition indexed_s0
  {index : Set} {message : Type}
  (IS : index -> LSM_sig message)
  : indexed_initial_state IS.
exists (fun (i : index) => proj1_sig (@s0 _ (IS i))).
intro i. destruct s0 as [s Hs]. assumption.
Defined.

Definition indexed_initial_message_prop
  {index : Set} {message : Type}
  (IS : index -> LSM_sig message)
  (m : indexed_proto_message IS)
  : Prop
  :=
  exists (i : index) (mi : @initial_message _ (IS i)), proj1_sig (proj1_sig mi) = proj1_sig m.


Definition indexed_m0
  {index : Set} {message : Type}
  (IS : index -> LSM_sig message)
  (i0 : index)
  : indexed_proto_message IS
  .
destruct (@m0 _ (IS i0)) as [m Hpm].
exists m. exists i0. assumption.
Defined.

Definition indexed_l0
  {index : Set} {message : Type}
  (IS : index -> LSM_sig message)
  (i0 : index)
  : indexed_label IS
  := existT _ i0 (@l0 message (IS i0)) .

Definition lift_proto_messageI
  {index : Set} {message : Type}
  (IS : index -> LSM_sig message)
  (i : index)
  (mi : @proto_message _ (IS i))
  : indexed_proto_message IS.
destruct mi as [m Hm].
exists m. exists i. assumption.
Defined.


Definition indexed_sig
  {index : Set} {message : Type} `{Heqd : EqDec index}
  (IS : index -> LSM_sig message)
  (i0 : index)
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
  {index : Set} {message : Type} `{Heqd : EqDec index}
  {IS : index -> LSM_sig message}
  {i0 : index}
  (s : @state message (indexed_sig IS i0))
  (i : index)
  (si : @state message (IS i))
  (j : index)
  : @state message (IS j).
destruct (eq_dec i j); subst.
- exact si.
- exact (s j).
Defined.

Definition indexed_transition
  {index : Set} {message : Type} `{Heqd : EqDec index}
  {IS : index -> LSM_sig message}
  (IM : forall i : index, @VLSM message (IS i))
  {Hinh : index}
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
  {index : Set} {message : Type} `{Heqd : EqDec index}
  {IS : index -> LSM_sig message}
  (IM : forall i : index, @VLSM message (IS i))
  {Hinh : index}
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
  {index : Set} {message : Type} `{Heqd : EqDec index}
  {IS : index -> LSM_sig message}
  {IM : forall i : index, @VLSM message (IS i)}
  (IDM : forall i : index, @VLSM_vdecidable _ _ (IM i))
  {Hinh : index}
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
  {index : Set} {message : Type} `{Heqd : EqDec index}
  {IS : index -> LSM_sig message}
  (IM : forall i : index, @VLSM message (IS i))
  {Hinh : index}
  (constraint : indexed_label IS -> indexed_state IS * option (indexed_proto_message IS) -> Prop)
  (l : @label _ (indexed_sig IS Hinh))
  (som : @state _ (indexed_sig IS Hinh) * option (@proto_message _ (indexed_sig IS Hinh)))
  :=
  indexed_valid IM l som /\ constraint l som.


Definition indexed_vlsm_constrained
  {index : Set} {message : Type} `{Heqd : EqDec index}
  {IS : index -> LSM_sig message}
  (IM : forall i : index, @VLSM message (IS i))
  (Hi : index)
  (constraint : indexed_label IS -> indexed_state IS * option (indexed_proto_message IS) -> Prop)
  : @VLSM message (indexed_sig IS Hi)
  :=
  {|  transition := indexed_transition IM
  ;   valid := indexed_valid_constrained IM constraint
  |}.

Definition indexed_valid_constrained_decidable
  {index : Set} {message : Type} `{Heqd : EqDec index}
  {IS : index -> LSM_sig message}
  {IM : forall i : index, @VLSM message (IS i)}
  (IDM : forall i : index, @VLSM_vdecidable _ _ (IM i))
  {Hinh : index}
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
  {index : Set} {message : Type} `{Heqd : EqDec index}
  {IS : index -> LSM_sig message}
  {IM : forall i : index, @VLSM message (IS i)}
  (IDM : forall i : index, @VLSM_vdecidable _ _ (IM i))
  (Hinh : index)
  {constraint : indexed_label IS -> indexed_state IS * option (indexed_proto_message IS) -> Prop}
  (constraint_decidable : forall (l : indexed_label IS) (som : indexed_state IS * option (indexed_proto_message IS)), {constraint l som} + {~constraint l som})
  : @VLSM_vdecidable _ _ (indexed_vlsm_constrained IM Hinh constraint)
  :=
  {|  valid_decidable := indexed_valid_constrained_decidable IDM constraint_decidable
  |}.


(* Free VLSM composition *)

Definition free_constraint 
  {index : Set} {message : Type} `{Heqd : EqDec index}
  {IS : index -> LSM_sig message}
  (l : indexed_label IS)
  (som : indexed_state IS * option (indexed_proto_message IS))
  : Prop
  :=
  True.

Definition free_constraint_decidable
  {index : Set} {message : Type} `{Heqd : EqDec index}
  {IS : index -> LSM_sig message}
  (l : indexed_label IS)
  (som : indexed_state IS * option (indexed_proto_message IS))
  : {free_constraint l som} + {~free_constraint l som}
  := left I.

Definition indexed_vlsm_free
  {index : Set} {message : Type} `{Heqd : EqDec index}
  {IS : index -> LSM_sig message}
  (IM : forall i : index, @VLSM message (IS i))
  (Hi : index)
  : @VLSM message (indexed_sig IS Hi)
  :=
  indexed_vlsm_constrained IM Hi free_constraint
  .

Definition indexed_vlsm_free_vdecidable
  {index : Set} {message : Type} `{Heqd : EqDec index}
  {IS : index -> LSM_sig message}
  {IM : forall i : index, @VLSM message (IS i)}
  (IDM : forall i : index, @VLSM_vdecidable _ _ (IM i))
  (Hi : index)
  : @VLSM_vdecidable _ _ (indexed_vlsm_free IM Hi)
  :=
  indexed_vlsm_constrained_vdecidable IDM Hi free_constraint_decidable.
