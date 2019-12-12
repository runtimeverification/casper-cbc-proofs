(** An Approach to VLSMs using a partial transition function.
*)
From Casper
Require Import vlsm.


Class PLSM (message : Type) `{Sig : LSM_sig message} :=
  { ptransition : label -> state * option proto_message -> option (state * option proto_message)
  }.


Definition ptransition_to_transition
  {message}
  {Sig : LSM_sig message}
  `{PM : @PLSM message Sig}
  (l : label)
  (som :  state * option proto_message)
  : state * option proto_message
  :=
  match ptransition l som with
  | Some som' => som'
  | None => (fst som, None)
  end
  .

Definition ptransition_to_valid
  {message}
  {Sig : LSM_sig message}
  `{PM : @PLSM message Sig}
  (l : label)
  (som :  state * option proto_message)
  : Prop
  :=
  ptransition l som = None
  .

Definition PLSM_VLSM_instance
  {message}
  {Sig : LSM_sig message}
  `{PM : @PLSM message Sig}
  : @VLSM message Sig
  :=
  {|  transition := ptransition_to_transition
  ;   valid := ptransition_to_valid
  |}.

Definition transition_valid_ptransition
  {message}
  {Sig : LSM_sig message}
  {VM : @VLSM message Sig}
  `{DVM : @VLSM_vdecidable message Sig VM}
  (l : label)
  (som :  state * option proto_message)
  : option (state * option proto_message)
  :=
  if valid_decidable l som
  then Some (transition l som)
  else None
  .

Definition DVLSM_PLSM_instance
  {message}
  {Sig : LSM_sig message}
  {VM : @VLSM message Sig}
  `(DVM : @VLSM_vdecidable message Sig VM)
  : @PLSM message Sig
  :=
  {|  ptransition := transition_valid_ptransition
  |}.


Section two_vlsms.
    From Casper
    Require Import two_vlsms.
    Require Import Logic.FunctionalExtensionality.

    Definition composed2_ptransition
        {message}
        {S1 : LSM_sig message}
        {S2 : LSM_sig message}
        (M1 : @PLSM message S1)
        (M2 : @PLSM message S2)
        (l : @label message (composed2_sig S1 S2))
        (som : @state message (composed2_sig S1 S2) * option (@proto_message _ (composed2_sig S1 S2)))
        : option (@state message (composed2_sig S1 S2) * option (@proto_message _ (composed2_sig S1 S2))).
    destruct som as [[s1 s2] [[m Hm]|]].
    - destruct l as [l1 | l2].
    + destruct (@proto_message_decidable _ S1 m) as [H1 | _].
        * destruct (ptransition l1 (s1, Some (exist _ m H1))) as [som'|].
        { exact (Some ((fst som', s2), option_map (lift_proto_message1 S1 S2) (snd som'))). }
        exact None.
        * exact None.
    + destruct (@proto_message_decidable _ S2 m) as [H2 | _].
        * destruct (ptransition l2 (s2, Some (exist _ m H2))) as [som'|].
        { exact (Some ((s1, fst som'), option_map (lift_proto_message2 S1 S2) (snd som'))). }
        exact None.
        * exact None.
    - destruct l as [l1 | l2].
    + destruct (ptransition l1 (s1, None)) as [som'|].
        * exact (Some ((fst som', s2), option_map (lift_proto_message1 S1 S2) (snd som'))).
        * exact None.
    + destruct (ptransition l2 (s2, None)) as [som'|].
        * exact (Some ((s1, fst som'), option_map (lift_proto_message2 S1 S2) (snd som'))).
        * exact None.
    Defined.


    Definition composed2_plsm
        {message}
        {S1 : LSM_sig message}
        {S2 : LSM_sig message}
        (M1 : @PLSM message S1)
        (M2 : @PLSM message S2)
    : @PLSM message (composed2_sig S1 S2)
    :=
    {|  ptransition := composed2_ptransition M1 M2
    |}.


  Definition composed2_ptransition_constrained
    {message}
    {S1 : LSM_sig message}
    {S2 : LSM_sig message}
    (M1 : @PLSM message S1)
    (M2 : @PLSM message S2)
    {constraint : (@label message S1) + (@label message S2) -> ((@state message S1) * (@state message S2)) * option (composed2_proto_message S1 S2) -> Prop}
    (constraint_decidable : forall (l : (@label message S1) + (@label message S2)) (som : ((@state message S1) * (@state message S2)) * option (composed2_proto_message S1 S2)), {constraint l som} + {~constraint l som})
    (l : @label message (composed2_sig S1 S2))
    (som : @state message (composed2_sig S1 S2) * option (@proto_message _ (composed2_sig S1 S2)))
  : option (@state message (composed2_sig S1 S2) * option (@proto_message _ (composed2_sig S1 S2)))
  :=
  if constraint_decidable l som then composed2_ptransition M1 M2 l som else None.

  Definition composed2_plsm_constrained
    {message}
    {S1 : LSM_sig message}
    {S2 : LSM_sig message}
    (M1 : @PLSM message S1)
    (M2 : @PLSM message S2)
    {constraint : (@label message S1) + (@label message S2) -> ((@state message S1) * (@state message S2)) * option (composed2_proto_message S1 S2) -> Prop}
    (constraint_decidable : forall (l : (@label message S1) + (@label message S2)) (som : ((@state message S1) * (@state message S2)) * option (composed2_proto_message S1 S2)), {constraint l som} + {~constraint l som})
    : @PLSM message (composed2_sig S1 S2)
  :=
  {|  ptransition := composed2_ptransition_constrained M1 M2 constraint_decidable
  |}.

  Lemma composed2_partial_composition_commute
    {message}
    {S1 S2 : LSM_sig message}
    {M1 : @VLSM message S1}
    {M2 : @VLSM message S2}
    (DS1 : @VLSM_vdecidable message S1 M1)
    (DS2 : @VLSM_vdecidable message S2 M2)
    : let PM12 := DVLSM_PLSM_instance (composed2_vlsm_vdecidable DS1 DS2) in
      let PM12' := composed2_plsm (DVLSM_PLSM_instance DS1) (DVLSM_PLSM_instance DS2) in
      @ptransition _ _ PM12 = @ptransition _ _ PM12'.
  Proof.
    intros.
    apply functional_extensionality; intros [l1 | l2]; apply functional_extensionality; intros [[s1 s2] [[m Hm]|]];
    unfold ptransition; simpl;
    unfold transition_valid_ptransition; unfold valid_decidable; simpl; try destruct (proto_message_decidable m) as [Hpm | Hnpm]; try reflexivity
    ; destruct DS1 as [valid_decidable1]; destruct DS2 as [valid_decidable2]; simpl
    .
    - destruct (valid_decidable1 l1 (s1, Some (exist proto_message_prop m Hpm))) as [Hv | Hnv]; reflexivity.
    - destruct (valid_decidable1 l1 (s1, None)) as [Hv | Hnv]; reflexivity.
    - destruct (valid_decidable2 l2 (s2, Some (exist proto_message_prop m Hpm))) as [Hv | Hnv]; reflexivity.
    - destruct (valid_decidable2 l2 (s2, None)) as [Hv | Hnv]; reflexivity.
  Qed.


  Lemma composed2_constrained_partial_composition_commute
    {message}
    {S1 S2 : LSM_sig message}
    {M1 : @VLSM message S1}
    {M2 : @VLSM message S2}
    (DS1 : @VLSM_vdecidable message S1 M1)
    (DS2 : @VLSM_vdecidable message S2 M2)
    {constraint : (@label message S1) + (@label message S2) -> (@state message S1 * @state message S2) * option (composed2_proto_message S1 S2) -> Prop}
    (constraint_decidable : forall (l : (@label message S1) + (@label message S2)) (som : ((@state message S1) * (@state message S2)) * option (composed2_proto_message S1 S2)), {constraint l som} + {~constraint l som})
    : let PM12 := DVLSM_PLSM_instance (composed2_vlsm_constrained_vdecidable DS1 DS2 constraint_decidable) in
      let PM12' := composed2_plsm_constrained (DVLSM_PLSM_instance DS1) (DVLSM_PLSM_instance DS2) constraint_decidable in
      @ptransition _ _ PM12 = @ptransition _ _ PM12'.
  Proof.
    intros.
    apply functional_extensionality; intros [l1 | l2]; apply functional_extensionality; intros [[s1 s2] [[m Hm]|]]
    ; unfold ptransition; simpl
    ; unfold transition_valid_ptransition; unfold composed2_ptransition_constrained
    ; unfold valid_decidable; simpl 
    ; unfold composed2_constrained_valid_decidable; simpl
    ; unfold composed2_valid_constrained; simpl
    ; try destruct
    (constraint_decidable (@inl (@label message S1) (@label message S2) l1)
        (s1, s2,
        @Some (@proto_message message (@composed2_sig message S1 S2))
        (@exist message
            (fun m0 : message => @composed2_proto_message_prop message S1 S2 m0) m Hm))
    )
    ; try reflexivity
    ; try destruct
    (constraint_decidable (@inl (@label message S1) (@label message S2) l1)
        (s1, s2, @None (@proto_message message (@composed2_sig message S1 S2)))
    )
    ; try reflexivity
    ; try destruct
    (constraint_decidable (@inr (@label message S1) (@label message S2) l2)
        (s1, s2,
        @Some (@proto_message message (@composed2_sig message S1 S2))
        (@exist message
            (fun m0 : message => @composed2_proto_message_prop message S1 S2 m0) m Hm))
    )
    ; try reflexivity
    ; try destruct
    (constraint_decidable (@inr (@label message S1) (@label message S2) l2)
        (s1, s2, @None (@proto_message message (@composed2_sig message S1 S2)))
    )
    ; try reflexivity
    ; unfold transition_valid_ptransition; simpl
    ; unfold valid_decidable; destruct DS1 as [valid_decidable1]; destruct DS2 as [valid_decidable2]; simpl
    ; try destruct (proto_message_decidable m) as [Hpm | Hnpm]
    ; try reflexivity
    .
    - destruct (valid_decidable1 l1 (s1, Some (exist proto_message_prop m Hpm))); reflexivity.
    - destruct (valid_decidable1 l1 (s1, Some (exist proto_message_prop m Hpm))); reflexivity.
    - destruct (valid_decidable1 l1 (s1, None)) as [Hv | Hnv]; reflexivity.
    - destruct (valid_decidable2 l2 (s2, Some (exist proto_message_prop m Hpm))) as [Hv | Hnv]; reflexivity.
    - destruct (valid_decidable2 l2 (s2, Some (exist proto_message_prop m Hpm))) as [Hv | Hnv]; reflexivity.
    - destruct (valid_decidable2 l2 (s2, None)) as [Hv | Hnv]; reflexivity.
  Qed.

End two_vlsms.

Section indexed_vlsm.
  From Casper
  Require Import indexed_vlsm.

  Definition indexed_ptransition
    {index : Set} {message : Type} `{Heqd : EqDec index}
    {IS : index -> LSM_sig message}
    (IM : forall i : index, @PLSM message (IS i))
    (i0 : index)
    (l : @label message (indexed_sig IS i0))
    (som : @state message (indexed_sig IS i0) * option (@proto_message _ (indexed_sig IS i0)))
    : option (@state message (indexed_sig IS i0) * option (@proto_message _ (indexed_sig IS i0))).
  destruct l as [i li].
  destruct som as [s [[m Hm]|]].
  - destruct (@proto_message_decidable _ (IS i) m) as [Him | _].
    + destruct (ptransition li (s i, Some (exist _ m Him))) as [[si' om']|].
      * exact (Some (state_update s i si', option_map (lift_proto_messageI IS i) om')).
      * exact None.
    + exact None.
  - destruct (ptransition li (s i, None)) as [[si' om']|].
    + exact (Some (state_update s i si', option_map (lift_proto_messageI IS i) om')).
    + exact None.
  Defined.

  Definition indexed_plsm
    {index : Set} {message : Type} `{Heqd : EqDec index}
    {IS : index -> LSM_sig message}
    (IM : forall i : index, @PLSM message (IS i))
    (i0 : index)
    : @PLSM message (indexed_sig IS i0)
    :=
    {|  ptransition := indexed_ptransition IM i0
    |}.


  Definition indexed_ptransition_constrained
    {index : Set} {message : Type} `{Heqd : EqDec index}
    {IS : index -> LSM_sig message}
    (IM : forall i : index, @PLSM message (IS i))
    (Hinh : index)
    {constraint : @label _ (indexed_sig IS Hinh) -> @state _ (indexed_sig IS Hinh) * option (@proto_message _ (indexed_sig IS Hinh)) -> Prop}
    (constraint_decidable : forall (l : @label _ (indexed_sig IS Hinh)) (som : @state _ (indexed_sig IS Hinh) * option (@proto_message _ (indexed_sig IS Hinh))), {constraint l som} + {~constraint l som})
    (l : @label message (indexed_sig IS Hinh))
    (som : @state message (indexed_sig IS Hinh) * option (@proto_message _ (indexed_sig IS Hinh)))
    : option (@state message (indexed_sig IS Hinh) * option (@proto_message _ (indexed_sig IS Hinh)))
    :=
    if constraint_decidable l som then indexed_ptransition IM Hinh l som else None.

  Definition indexed_plsm_constrained
    {index : Set} {message : Type} `{Heqd : EqDec index}
    {IS : index -> LSM_sig message}
    (IM : forall i : index, @PLSM message (IS i))
    (Hinh : index)
    {constraint : @label _ (indexed_sig IS Hinh) -> @state _ (indexed_sig IS Hinh) * option (@proto_message _ (indexed_sig IS Hinh)) -> Prop}
    (constraint_decidable : forall (l : @label _ (indexed_sig IS Hinh)) (som : @state _ (indexed_sig IS Hinh) * option (@proto_message _ (indexed_sig IS Hinh))), {constraint l som} + {~constraint l som})
    : @PLSM message (indexed_sig IS Hinh)
    :=
    {|  ptransition := indexed_ptransition_constrained IM Hinh constraint_decidable
    |}.


  Lemma indexed_constrained_partial_composition_commute
    {index : Set} {message : Type} `{Heqd : EqDec index}
    {IS : index -> LSM_sig message}
    {IM : forall i : index, @VLSM message (IS i)}
    (IDM : forall i : index, @VLSM_vdecidable _ _ (IM i))
    (Hinh : index)
    {constraint : @label _ (indexed_sig IS Hinh) -> @state _ (indexed_sig IS Hinh) * option (@proto_message _ (indexed_sig IS Hinh)) -> Prop}
    (constraint_decidable : forall (l : @label _ (indexed_sig IS Hinh)) (som : @state _ (indexed_sig IS Hinh) * option (@proto_message _ (indexed_sig IS Hinh))), {constraint l som} + {~constraint l som})
    : let PM12 := DVLSM_PLSM_instance (indexed_vlsm_constrained_vdecidable IDM Hinh constraint_decidable) in
      let PM12' := indexed_plsm_constrained (fun (i : index) => DVLSM_PLSM_instance (IDM i)) Hinh constraint_decidable in
      @ptransition _ _ PM12 = @ptransition _ _ PM12'.
  Proof.
    intros.
    apply functional_extensionality; intros [i li]; apply functional_extensionality; intros [s [[m Hm]|]]
    ; unfold ptransition; simpl
    ; unfold transition_valid_ptransition
    ; unfold indexed_ptransition_constrained; simpl
    ; unfold valid_decidable; simpl 
    ; unfold indexed_valid_constrained_decidable; simpl
    ; unfold indexed_valid_constrained; simpl
    ; unfold transition_valid_ptransition; simpl
    ; unfold valid_decidable
    ; destruct (IDM i) as [valid_decidablei]
    .
    - destruct (constraint_decidable (@existT index (fun i0 : index => @label message (IS i0)) i li)
          (@pair (@indexed_state index message IS) (option (@proto_message message (@indexed_sig index message Heqd IS Hinh))) s
             (@Some (@proto_message message (@indexed_sig index message Heqd IS Hinh))
                (@exist message (fun m0 : message => @indexed_proto_message_prop index message IS m0) m Hm)))
        )
      ; try reflexivity
      .
      try destruct (proto_message_decidable m) as [Hpm | Hnpm]
      ; try reflexivity
      .
      destruct (transition li (s i, Some (exist proto_message_prop m Hpm))) as [si' om'].
      destruct (valid_decidablei li (s i, Some (exist proto_message_prop m Hpm)))
      ; reflexivity
      .
    - destruct
        (constraint_decidable (@existT index (fun i0 : index => @label message (IS i0)) i li)
          (@pair (@indexed_state index message IS) (option (@proto_message message (@indexed_sig index message Heqd IS Hinh))) s
             (@None (@proto_message message (@indexed_sig index message Heqd IS Hinh))))
        )
      ; try reflexivity.
      destruct (transition li (s i, None)) as [si' om'].
      destruct (valid_decidablei li (s i, None)); reflexivity.
  Qed.


  Lemma indexed_partial_composition_commute
    {index : Set} {message : Type} `{Heqd : EqDec index}
    {IS : index -> LSM_sig message}
    {IM : forall i : index, @VLSM message (IS i)}
    (IDM : forall i : index, @VLSM_vdecidable _ _ (IM i))
    (Hinh : index)
    : let PM12 := DVLSM_PLSM_instance (indexed_vlsm_free_vdecidable IDM Hinh) in
      let PM12' := indexed_plsm (fun (i : index) => DVLSM_PLSM_instance (IDM i)) Hinh in
      @ptransition _ _ PM12 = @ptransition _ _ PM12'.
  Proof.
    intros. unfold PM12 in *; clear PM12. unfold PM12' in *; clear PM12'.
    specialize (indexed_constrained_partial_composition_commute IDM); intros HC.
    specialize (HC Hinh free_constraint free_constraint_decidable). assumption.
 Qed.

End indexed_vlsm.