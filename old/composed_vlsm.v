Require Import List.
Import ListNotations.

From Casper
Require Import vlsm two_vlsms indexed_vlsm.

Class composed_sig_class (message : Type) `{S : LSM_sig message} :=
  { index : Set
  ; index_eq_dec : EqDec index

  ; iproto_state : index -> Type
  ; istate_proj : forall i : index, state -> iproto_state i

  ; ilabel : label -> index
  ; ilabel_type := fun (i : index) => { l : label | ilabel l = i }
  ; il0 : forall i : index, ilabel_type i

  ; iproto_message_prop : index -> message -> Prop
  ; iproto_message_decidable : forall i : index, forall m : message, {iproto_message_prop i m} + {~iproto_message_prop i m}
  ; im0 : forall i : index,  {m : message | iproto_message_prop i m}
  ; iproto_message_consistent : forall i : index, forall m : message, iproto_message_prop i m -> proto_message_prop m
  }.

Definition istate
  { message : Type }
  `{composed_sig_class message}
  (i : index)
  :=
  { is : iproto_state i | exists s : state, istate_proj i s = is }.

Definition proj_istate
  { message : Type }
  `{composed_sig_class message}
  (s : state)
  (i : index)
  : istate i.
remember (istate_proj i s) as is.
assert (His : exists s', istate_proj i s' = is) by (exists s; subst; reflexivity).
exact (exist _ is His).
Defined.

Lemma proj_istate_eq
  { message : Type }
  `{composed_sig_class message}
  (s1 s2 : state)
  (i : index)
  : istate_proj i s1 = istate_proj i s2 <-> proj_istate s1 i = proj_istate s2 i.
Proof.
  unfold proj_istate.
  split; intros Heq.
  - apply exist_eq. simpl. assumption.
  - inversion Heq. reflexivity.
Qed.


Class composed_vlsm_class (message : Type) {S : LSM_sig message} `{@composed_sig_class message S} `{M : @VLSM message S}
  :=
  { transition_projection_consistency
    : forall (s1 s2 : state) (om : option proto_message) (l : label) (i : index := ilabel l)
        (Hproj_s : istate_proj i s1 = istate_proj i s2),
      let (s1', om1') := transition l (s1, om) in
      let (s2', om2') := transition l (s2, om) in
      om1' = om2' /\  istate_proj i s1' = istate_proj i s2'
  ; transition_projection_state_preservation
    : forall (s : state) (om : option proto_message) (l : label) (i : index)
        (Hnli : ilabel l <> i),
        let (s', _) := transition l (s, om) in
        istate_proj i s' = istate_proj i s
  ; transition_projection_message_type_preservation
    : forall (s : state) (om : option proto_message) (l : label) (i : index := ilabel l)
        (s' : state)
        (m' : proto_message)
        (Ht : transition l (s, om) = (s', Some m')),
        (iproto_message_prop i (proj1_sig m'))
  ; transition_projection_message_type_mismatch
    : forall (s : state) (m : proto_message) (l : label) (i : index := ilabel l)
        (Hnm : ~ (iproto_message_prop i (proj1_sig m))),
        ~ valid l (s, Some m)
  }.


Inductive composed2_index : Set := one | two.

Lemma composed2_index_eq_dec
  : EqDec composed2_index.
Proof.
  intros x y; destruct x; destruct y; try (left; reflexivity); right; intros C; inversion C.
Qed.

Definition composed2_iproto_state
  {message}
  (S1 : LSM_sig message)
  (S2 : LSM_sig message)
  (i : composed2_index)
  : Type
  :=
  match i with
  | one => @state message S1
  | two => @state message S2
  end.

Definition composed2_istate_proj
  {message}
  (S1 : LSM_sig message)
  (S2 : LSM_sig message)
  (i : composed2_index)
  (s : @state message (composed2_sig S1 S2))
  : composed2_iproto_state S1 S2 i
  :=
  match i with
  | one => fst s
  | two => snd s
  end.

Definition composed2_ilabel
  {message}
  (S1 : LSM_sig message)
  (S2 : LSM_sig message)
  (l : @label _ (composed2_sig S1 S2))
  : composed2_index
  :=
  match l with
  | inl _ => one
  | inr _ => two
  end.

Definition composed2_il0
  {message}
  (S1 : LSM_sig message)
  (S2 : LSM_sig message)
  (i : composed2_index)
  : { l : @label _ (composed2_sig S1 S2) | composed2_ilabel S1 S2 l = i }
  :=
  match i with
  | one => exist _ (inl (@l0 message S1)) eq_refl
  | two => exist _ (inr (@l0 message S2)) eq_refl
  end.

Definition composed2_iproto_message_prop
  {message}
  (S1 : LSM_sig message)
  (S2 : LSM_sig message)
  (i : composed2_index)
  : message -> Prop
  :=
  match i with
  | one => @proto_message_prop message S1
  | two => @proto_message_prop message S2
  end.

Lemma composed2_iproto_message_decidable
  {message}
  (S1 : LSM_sig message)
  (S2 : LSM_sig message)
  (i : composed2_index)
  : forall m : message, {composed2_iproto_message_prop S1 S2 i m} + {~composed2_iproto_message_prop S1 S2 i m}.
Proof.
  unfold composed2_iproto_message_prop. destruct i; apply proto_message_decidable.
Qed.

Definition composed2_im0
  {message}
  (S1 : LSM_sig message)
  (S2 : LSM_sig message)
  (i : composed2_index)
  : {m : message | composed2_iproto_message_prop S1 S2 i m}
  :=
  match i with
  | one => @m0 message S1
  | two => @m0 message S2
  end.

Lemma composed2_iproto_message_consistent
  {message}
  (S1 : LSM_sig message)
  (S2 : LSM_sig message)
  (i : composed2_index)
  (m : message)
  : composed2_iproto_message_prop S1 S2 i m -> composed2_proto_message_prop S1 S2 m.
Proof.
  intros Hmsg.
  unfold composed2_iproto_message_prop; intros. destruct i; (left; assumption) || (right; assumption).
Qed.

Definition composed2_sig_composed_instance
  {message}
  (S1 S2 : LSM_sig message)
  : @composed_sig_class message (composed2_sig S1 S2) :=
  {| index := composed2_index
  ; index_eq_dec := composed2_index_eq_dec
  ; iproto_state := composed2_iproto_state S1 S2
  ; istate_proj := composed2_istate_proj S1 S2
  ; ilabel := composed2_ilabel S1 S2
  ; il0 := composed2_il0 S1 S2
  ; iproto_message_prop := composed2_iproto_message_prop S1 S2
  ; iproto_message_decidable := composed2_iproto_message_decidable S1 S2
  ; im0 := composed2_im0 S1 S2
  ; iproto_message_consistent := composed2_iproto_message_consistent S1 S2
  |}.

Lemma composed2_transition_projection_consistency
  {message}
  {S1 S2 : LSM_sig message}
  (M1 : @VLSM message S1)
  (M2 : @VLSM message S2)
  (s1 s2 : @state _ (composed2_sig S1 S2))
  (om : option (@proto_message _ (composed2_sig S1 S2)))
  (l : @label _ (composed2_sig S1 S2))
  (i : @index _ _ (composed2_sig_composed_instance S1 S2) := composed2_ilabel S1 S2 l)
  (Hproj_s : composed2_istate_proj S1 S2 i s1 = composed2_istate_proj S1 S2 i s2)
  : let (s1', om1') := (@transition _ _ (composed2_vlsm M1 M2) l (s1, om)) in
    let (s2', om2') := (@transition _ _ (composed2_vlsm M1 M2) l (s2, om)) in
    (   om1' = om2'
    /\  composed2_istate_proj S1 S2 i s1' = composed2_istate_proj S1 S2 i s2'
    )
  .
Proof.
  intros.
  destruct s1 as [s1one s1two]. destruct s2 as [s2one s2two]. 
  unfold transition in *; simpl in *.
  destruct om as [[m Hm]|]
  ; destruct l as [lone | ltwo]
  ; simpl in Hproj_s; subst
  ; try destruct (proto_message_decidable m) as [Hpm | Hnpm]
  ; split; reflexivity
  .
Qed.

Lemma composed2_transition_projection_state_preservation
  {message}
  {S1 S2 : LSM_sig message}
  (M1 : @VLSM message S1)
  (M2 : @VLSM message S2)
  (s : @state _ (composed2_sig S1 S2))
  (om : option (@proto_message _ (composed2_sig S1 S2)))
  (l : @label _ (composed2_sig S1 S2))
  (i : @index _ _ (composed2_sig_composed_instance S1 S2))
  (Hnli : @ilabel _ _ (composed2_sig_composed_instance S1 S2) l <> i)
  : let (s', _) := @transition _ _ (composed2_vlsm M1 M2) l (s, om) in
    @istate_proj _ _ (composed2_sig_composed_instance S1 S2) i s' = @istate_proj _ _ (composed2_sig_composed_instance S1 S2) i s
  .
Proof.
  intros.
  destruct s as [sone stwo].
  simpl.
  destruct om as [[m Hm]|]
  ; destruct l as [lone | ltwo]
  ; try destruct (proto_message_decidable m) as [Hpm | Hnpm]
  ; destruct i;  simpl in Hnli; try contradiction
  ; reflexivity
  .
Qed.


Lemma composed2_transition_projection_message_type_mismatch
  {message}
  {S1 S2 : LSM_sig message}
  (M1 : @VLSM message S1)
  (M2 : @VLSM message S2)
  (s : @state _ (composed2_sig S1 S2))
  (m : @proto_message _ (composed2_sig S1 S2))
  (l : @label _ (composed2_sig S1 S2))
  (i : composed2_index := composed2_ilabel S1 S2 l)
  (Hnm : ~ (composed2_iproto_message_prop S1 S2 i (proj1_sig m)))
  : ~ @valid _ _ (composed2_vlsm M1 M2)  l (s, Some m).
Proof.
  simpl. destruct s as [s1 s2]. destruct m as [m Hm].
  destruct l as [lone | ltwo]
  ; destruct (proto_message_decidable m)
  ; intro; contradiction.
Qed.


Lemma composed2_transition_projection_message_type_preservation
  {message}
  {S1 S2 : LSM_sig message}
  (M1 : @VLSM message S1)
  (M2 : @VLSM message S2)
  (s : @state _ (composed2_sig S1 S2))
  (om : option (@proto_message _ (composed2_sig S1 S2)))
  (l : @label _ (composed2_sig S1 S2))
  (i : composed2_index := composed2_ilabel S1 S2 l)
  (s' : @state _ (composed2_sig S1 S2))
  (m' : @proto_message _ (composed2_sig S1 S2))
  (Ht : @transition _ _ (composed2_vlsm M1 M2) l (s, om) = (s', Some m'))
  : composed2_iproto_message_prop S1 S2 i (proj1_sig m').
Proof.
  unfold composed2_iproto_message_prop.
  destruct (transition l (s, om)) as [s'' om'] eqn:Ht'.
  inversion Ht; subst; clear Ht.
  simpl in Ht'.
  destruct s as [s1 s2]. destruct om as [[m Hm]|]
  ; destruct l as [lone | ltwo]; simpl in i; unfold i
  ; try destruct (proto_message_decidable m)
  ; inversion Ht' as [[Hs' Hm']]; subst; clear Ht'
  .
  - destruct (transition lone (s1, Some (exist proto_message_prop m p))) as [s'' [[m'' Hm'']|]]; inversion Hm'; subst; assumption.
  - destruct (transition ltwo (s2, Some (exist proto_message_prop m p))) as [s'' [[m'' Hm'']|]]; inversion Hm'; subst; assumption.
  - destruct (transition lone (s1, None)) as [s'' [[m'' Hm'']|]]; inversion Hm'; subst; assumption.
  - destruct (transition ltwo (s2, None)) as [s'' [[m'' Hm'']|]]; inversion Hm'; subst; assumption.
Qed.

Definition composed2_vlsm_composed_instance
  {message}
  {S1 S2 : LSM_sig message}
  (M1 : @VLSM message S1)
  (M2 : @VLSM message S2)
  : @composed_vlsm_class message _ (@composed2_sig_composed_instance _ S1 S2) (composed2_vlsm M1 M2) :=
  {| transition_projection_consistency := composed2_transition_projection_consistency M1 M2
  ; transition_projection_state_preservation := composed2_transition_projection_state_preservation M1 M2
  ; transition_projection_message_type_mismatch := composed2_transition_projection_message_type_mismatch M1 M2
  ; transition_projection_message_type_preservation := composed2_transition_projection_message_type_preservation M1 M2
  |}.


Definition indexed_istate
  {oindex : Set} {message : Type} `{Heqd : EqDec oindex}
  {IS : oindex -> LSM_sig message}
  (i : oindex)
  : Type
  := @state message (IS i).


Definition indexed_istate_proj
  {oindex : Set} {message : Type} `{Heqd : EqDec oindex}
  {IS : oindex -> LSM_sig message}
  {Hinh : oindex}
  (i : oindex)
  (s : @state message (indexed_sig IS Hinh))
  : @indexed_istate oindex message Heqd IS i
  :=
  s i.


Definition indexed_ilabel
  {oindex : Set} {message : Type} `{Heqd : EqDec oindex}
  {IS : oindex -> LSM_sig message}
  (l : indexed_label IS)
  : oindex
  :=
  projT1 l.


Definition indexed_il0
  {oindex : Set} {message : Type} `{Heqd : EqDec oindex}
  {IS : oindex -> LSM_sig message}
  (i : oindex)
  : { l : indexed_label IS | indexed_ilabel l = i }
  :=
  exist _ (existT _ i (@l0 message (IS i))) eq_refl
  .

Definition indexed_iproto_message_prop
  {oindex : Set} {message : Type} `{Heqd : EqDec oindex}
  {IS : oindex -> LSM_sig message}
  (i : oindex)
  : message -> Prop
  :=
  @proto_message_prop message (IS i).

Definition indexed_iproto_message_decidable
  {oindex : Set} {message : Type} `{Heqd : EqDec oindex}
  {IS : oindex -> LSM_sig message}
  (i : oindex)
  : forall m : message, {indexed_iproto_message_prop i m} + {~indexed_iproto_message_prop i m}
  :=
  @proto_message_decidable message (IS i).

Definition indexed_im0
  {oindex : Set} {message : Type} `{Heqd : EqDec oindex}
  {IS : oindex -> LSM_sig message}
  (i : oindex)
  : {m : message | indexed_iproto_message_prop i m}
  :=
  @m0 message (IS i).

Lemma indexed_iproto_message_consistent
  {index : Set} {message : Type} `{Heqd : EqDec index}
  {IS : index -> LSM_sig message}
  (i : index)
  (m : message)
  : indexed_iproto_message_prop i m -> indexed_proto_message_prop IS m.
Proof.
  unfold indexed_iproto_message_prop.
  intros Hmsg. exists i. assumption.
Qed.

Definition indexed_sig_composed_instance
  {oindex : Set} {message : Type} `{Heqd : EqDec oindex}
  (IS : oindex -> LSM_sig message)
  (Hinh : oindex)
  : @composed_sig_class message (indexed_sig IS Hinh) :=
  {| index := oindex
  ; iproto_state := @indexed_istate oindex message Heqd IS
  ; istate_proj := indexed_istate_proj
  ; ilabel := indexed_ilabel
  ; il0 := indexed_il0
  ; iproto_message_prop := indexed_iproto_message_prop
  ; iproto_message_decidable := indexed_iproto_message_decidable
  ; im0 := indexed_im0
  ; iproto_message_consistent := indexed_iproto_message_consistent
  |}.



Lemma indexed_transition_projection_consistency
  {oindex : Set} {message : Type} `{Heqd : EqDec oindex}
  {IS : oindex -> LSM_sig message}
  {IM : forall i : oindex, @VLSM message (IS i)}
  {Hinh : oindex}
  {constraint : indexed_label IS -> indexed_state IS * option (indexed_proto_message IS) -> Prop}
  (s1 s2 : @state _ (indexed_sig IS Hinh))
  (om : option (@proto_message _ (indexed_sig IS Hinh)))
  (l : @label _ (indexed_sig IS Hinh))
  (i : oindex := @ilabel _ _ (indexed_sig_composed_instance IS Hinh) l)
  (Hproj_s : @istate_proj _ _ (indexed_sig_composed_instance IS Hinh) i s1 = @istate_proj _ _ (indexed_sig_composed_instance IS Hinh) i s2)
  : let (s1', om1') := @transition _ _ (indexed_vlsm_constrained IM Hinh constraint) l (s1, om) in
    let (s2', om2') := @transition _ _ (indexed_vlsm_constrained IM Hinh constraint) l (s2, om) in
    (   om1' = om2'
    /\  @istate_proj _ _ (indexed_sig_composed_instance IS Hinh) i s1' = @istate_proj _ _ (indexed_sig_composed_instance IS Hinh) i s2'
    )
  .
Proof.
  simpl.  destruct l as [j l]. simpl in i. unfold i in *.
  unfold istate_proj in Hproj_s; simpl in Hproj_s. unfold indexed_istate_proj in *. rewrite Hproj_s.
  destruct om as [[m Hm]|]
  ; ( destruct (proto_message_decidable m) as [Hpm | Hnpm]; simpl; try (split; reflexivity || assumption)
    ; destruct (transition l (s2 j, Some (exist proto_message_prop m Hpm))) as [sj' om']
    ) || destruct (transition l (s2 j, None)) as  [sj' om']
  ; simpl; split; try reflexivity
  ;  unfold state_update
  ;  destruct (eq_dec j j); try contradiction
  ;  reflexivity
  .
Qed.


Lemma indexed_transition_projection_state_preservation
  {oindex : Set} {message : Type} `{Heqd : EqDec oindex}
  {IS : oindex -> LSM_sig message}
  {IM : forall i : oindex, @VLSM message (IS i)}
  {Hinh : oindex}
  {constraint : indexed_label IS -> indexed_state IS * option (indexed_proto_message IS) -> Prop}
  (s : indexed_state IS)
  (om : option (indexed_proto_message IS))
  (l : indexed_label IS)
  (i : oindex)
  (Hnli : indexed_ilabel l <> i)
  : let (s', _) := @transition _ _ (indexed_vlsm_constrained IM Hinh constraint) l (s, om) in
    @indexed_istate_proj _ _ _ _ Hinh i s' = @indexed_istate_proj _ _ _ _ Hinh i s
  .
Proof.
  destruct l as [j l]. simpl in Hnli.
  simpl.
  destruct om as [[m Hm]|]
  ; ( destruct (proto_message_decidable m) as [Hpm | Hnpm]; try reflexivity
      ; destruct (transition l (s j, Some (exist proto_message_prop m Hpm))) as [s'' om'']
    ) ||  destruct (transition l (s j, None)) as [s'' om'']
  ; unfold indexed_istate_proj; unfold state_update
  ; destruct (eq_dec j i); try contradiction
  ; reflexivity
  .
Qed.


Lemma indexed_transition_projection_message_type_mismatch
  {oindex : Set} {message : Type} `{Heqd : EqDec oindex}
  {IS : oindex -> LSM_sig message}
  {IM : forall i : oindex, @VLSM message (IS i)}
  {Hinh : oindex}
  {constraint : indexed_label IS -> indexed_state IS * option (indexed_proto_message IS) -> Prop}
  (s : indexed_state IS)
  (m : indexed_proto_message IS)
  (l : indexed_label IS)
  (i : oindex := indexed_ilabel l)
  (Hnm : ~ (indexed_iproto_message_prop i (proj1_sig m)))
  : ~ @valid _ _ (indexed_vlsm_constrained IM Hinh constraint)  l (s, Some m) .
Proof.
  simpl. destruct l as [j l]. simpl in i. unfold i in *. clear i.
  destruct m as [m Hm]; simpl in Hnm.
  intros [Hv Hc].
  unfold indexed_iproto_message_prop in Hnm.
  simpl in Hv.
  destruct (@proto_message_decidable message (IS j) m); contradiction.
Qed.


Lemma indexed_transition_projection_message_type_preservation
  {oindex : Set} {message : Type} `{Heqd : EqDec oindex}
  {IS : oindex -> LSM_sig message}
  {IM : forall i : oindex, @VLSM message (IS i)}
  {Hinh : oindex}
  {constraint : indexed_label IS -> indexed_state IS * option (indexed_proto_message IS) -> Prop}
  (s : indexed_state IS)
  (om : option (indexed_proto_message IS))
  (l : indexed_label IS)
  (i : oindex := indexed_ilabel l)
  (s' : indexed_state IS)
  (m' : indexed_proto_message IS)
  (Ht : @transition _ _ (indexed_vlsm_constrained IM Hinh constraint) l (s, om) = (s', Some m'))
  : indexed_iproto_message_prop i (proj1_sig m').
Proof.
  destruct l as [j l]. simpl in i. unfold i in *.
  unfold indexed_iproto_message_prop.
  simpl in Ht.
  destruct om as [[m Hm]|].
  - destruct (proto_message_decidable m) as [Hpm | Hnpm]
    ; try destruct (transition l (s j, Some (exist proto_message_prop m Hpm))) as [si' [[m'' Hm'']|]]
    ; simpl in Ht; inversion Ht; subst; clear Ht.
    assumption.
  - destruct (transition l (s j, None)) as [si' [[m'' Hm'']|]]
    ; simpl in Ht; inversion Ht; subst; clear Ht.
    assumption.
Qed.

Definition indexed_vlsm_constrained_composed_instance
  {oindex : Set} {message : Type} `{Heqd : EqDec oindex}
  {IS : oindex -> LSM_sig message}
  (IM : forall i : oindex, @VLSM message (IS i))
  (Hinh : oindex)
  (constraint : indexed_label IS -> indexed_state IS * option (indexed_proto_message IS) -> Prop)
  : @composed_vlsm_class message _ (indexed_sig_composed_instance IS Hinh) (indexed_vlsm_constrained IM Hinh constraint) :=
  {|  transition_projection_consistency := indexed_transition_projection_consistency
  ;   transition_projection_state_preservation := indexed_transition_projection_state_preservation
  ;   transition_projection_message_type_mismatch := indexed_transition_projection_message_type_mismatch
  ; transition_projection_message_type_preservation := indexed_transition_projection_message_type_preservation
  |}.

Definition indexed_vlsm_free_composed_instance
  {oindex : Set} {message : Type} `{Heqd : EqDec oindex}
  {IS : oindex -> LSM_sig message}
  (IM : forall i : oindex, @VLSM message (IS i))
  (Hinh : oindex)
  : @composed_vlsm_class message _ (indexed_sig_composed_instance IS Hinh) (indexed_vlsm_free IM Hinh) :=
  indexed_vlsm_constrained_composed_instance IM Hinh free_constraint.
