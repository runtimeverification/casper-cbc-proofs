Require Import FinFun.
(* Section 4: Byzantine fault tolerance analysis *)
From Casper   
Require Import preamble vlsm indexed_vlsm.

Context
    {message : Type}
    {index : Type}
    {index_listing : list index}
    (finite_index : Listing index_listing)
    `{IndEqDec : EqDec index}
    (i0 : index)
    {IT : index -> VLSM_type message}
    {IS : forall i : index, LSM_sig (IT i)}
    (IM : forall n : index, VLSM (IS n))
    (T := indexed_type IT)
    (S := indexed_sig finite_index i0 IT IS)
    (constraint : @label _ T -> @state _ T * option (@proto_message _ _ S) -> Prop)
    (X := indexed_vlsm_constrained finite_index i0 IT IS IM constraint)
    .

Definition validating_received_messages
    (i : index)
    :=
    forall (si : @state _ (IT i)) (mi : @proto_message _ _ (IS i)) (li : @label _ (IT i)),
        (~ exists (ps : protocol_state X) (pm : protocol_message X),
            (proj1_sig ps) i = si
            /\
            (proj1_sig (proj1_sig pm)) = proj1_sig mi
            /\
            @valid _ _ _ X (existT _ i li) (proj1_sig ps, Some (proj1_sig pm))
        )
        -> ~ @valid _ _ _ (IM i) li (si, Some mi)
            .

Definition validating_messages
    (i : index)
    :=
    forall (si : @state _ (IT i)) (omi : option (@proto_message _ _ (IS i))) (li : @label _ (IT i)),
        @valid _ _ _ (IM i) li (si, omi) ->
        exists (ps : protocol_state X) (opm : option (protocol_message X)),
            (proj1_sig ps) i = si
            /\
            option_map (@proj1_sig _ _) (option_map (@proj1_sig _ _) opm)
                = option_map (@proj1_sig _ _) omi
            /\
            @valid _ _ _ X (existT _ i li) (proj1_sig ps,  option_map (@proj1_sig _ _) opm)
            .

Lemma validating_messages_received
    (i : index)
    : validating_messages i -> validating_received_messages i.
Proof.
    unfold validating_messages. unfold validating_received_messages. intros.
    intro Hvalid. apply H0. clear H0.
    specialize (H si (Some mi) li Hvalid). clear Hvalid.
    destruct H as [ps [opm [Hsi [Hmi Hvalid]]]].
    destruct opm as [pm|]; simpl in Hmi; inversion Hmi.
    exists ps. exists pm.
    split; try assumption.
    split; try assumption.
    reflexivity.
Qed.

Definition validating_transitions
    (i : index)
    :=
    forall
        (si : @state _ (IT i))
        (omi : option (@proto_message _ _ (IS i)))
        (li : @label _ (IT i))
        ,
        @valid _ _ _ (IM i) li (si, omi)
        ->
        (exists 
            (s s' : @state _ T)
            (om om' : option (@proto_message _ _ S)),
            si = s i
            /\
            option_map (@proj1_sig _ _) om = option_map (@proj1_sig _ _) omi
            /\
            verbose_valid_protocol_transition X (existT _ i li) s s' om om'
        )
        .

Lemma validating_messages_transitions
    (i : index)
    : validating_messages i -> validating_transitions i.
Proof.
    unfold validating_messages. unfold validating_transitions. intros.
    specialize (H si omi li H0). clear H0.
    destruct H as [ps [opm [Hsi [Homi Hvalid]]]].
    remember (proj1_sig ps) as s.
    remember (option_map (@proj1_sig _ _) opm) as om.
    remember (@transition _ _ _ X (existT _ i li) (s, om)) as t.
    destruct t as [s' om'].
    exists s. exists s'. exists om. exists om'.
    symmetry in Hsi. split; try assumption. split; try assumption.
    subst.
    destruct ps as [s Hps]. split; try assumption.
    symmetry in Heqt.
    repeat (split; try assumption).
    destruct opm as [[m Hpm]|]; simpl; try assumption.
    remember (proj1_sig (@s0 _ _ S)) as sz.
    exists sz.
    specialize (protocol_initial_state X s0); simpl; intro Hs0.
    subst. assumption.
Qed.
    
Lemma validating_transitions_messages
    (i : index)
    : validating_transitions i -> validating_messages i.
Proof.
    unfold validating_messages. unfold validating_transitions. intros.
    specialize (H si omi li H0); clear H0.
    destruct H as [s [s' [om [om' [Hsi [Homi [Hps [Hopm [Hvalid Htransition]]]]]]]]].
    symmetry in Hsi.
    exists (exist _ s Hps).
    destruct om as [m|].
    - exists (Some (exist _ m Hopm)).
      repeat (split; try assumption).
    - exists None.
      repeat (split; try assumption).
Qed.

