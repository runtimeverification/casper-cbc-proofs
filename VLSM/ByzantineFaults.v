Require Import FinFun.
(* Section 4: Byzantine fault tolerance analysis *)
From Casper   
Require Import Lib.Preamble VLSM.Common VLSM.Composition.

Context
    {message : Type}
    {index : Type}
    `{IndEqDec : EqDec index}
    (i0 : index)
    {IT : index -> VLSM_type message}
    {IS : forall i : index, LSM_sig (IT i)}
    (IM : forall n : index, VLSM (IS n))
    (T := indexed_type IT)
    (S := indexed_sig i0 IS)
    (constraint : @label _ T -> @state _ T * option message -> Prop)
    (X := indexed_vlsm_constrained i0 IM constraint)
    .

Definition validating_received_messages
    (i : index)
    :=
    forall (si : @state _ (IT i)) (mi : message) (li : @label _ (IT i)),
        (~ exists (ps : protocol_state X) (pm : protocol_message X),
            (proj1_sig ps) i = si
            /\
            proj1_sig pm = mi
            /\
            @valid _ _ _ X (existT _ i li) (proj1_sig ps, Some (proj1_sig pm))
        )
        -> ~ @valid _ _ _ (IM i) li (si, Some mi)
            .

Definition validating_messages
    (i : index)
    :=
    forall (li : @label _ (IT i)) (siomi : @state _ (IT i) * option message),
        @valid _ _ _ (IM i) li siomi ->
        composite_protocol_valid i0 IM constraint i li siomi.

Lemma validating_messages_received
    (i : index)
    : validating_messages i -> validating_received_messages i.
Proof.
    unfold validating_messages. unfold validating_received_messages. intros.
    intro Hvalid. apply H0. clear H0.
    specialize (H li (si, Some mi) Hvalid). clear Hvalid.
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
        (omi : option message)
        (li : @label _ (IT i))
        ,
        @valid _ _ _ (IM i) li (si, omi)
        ->
        (exists 
            (s s' : @state _ T)
            (om' : option message),
            si = s i
            /\
            verbose_valid_protocol_transition X (existT _ i li) s s' omi om'
        )
        .

Lemma validating_messages_transitions
    (i : index)
    : validating_messages i -> validating_transitions i.
Proof.
    unfold validating_messages. unfold validating_transitions. 
    unfold composite_protocol_valid. unfold verbose_valid_protocol_transition.
    simpl. intros.
    specialize (H li (si, omi) H0). clear H0. simpl in H.
    destruct H as [ps [opm [Hsi [Homi Hvalid]]]].
    remember (proj1_sig ps) as s.
    remember (@transition _ _ _ X (existT _ i li) (s, omi)) as t.
    destruct t as [s' om'].
    exists s. exists s'. exists om'.
    symmetry in Hsi. subst s; simpl.
    split; try assumption.
    destruct ps as [s Hps]; simpl in *.
    split; try assumption.
    symmetry in Heqt.
    subst.
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
    destruct siomi as [si omi].
    specialize (H si omi li H0); clear H0.
    destruct H as [s [s' [om' [Hsi [Hps [Hopm [Hvalid Htransition]]]]]]].
    symmetry in Hsi.
    exists (exist _ s Hps).
    destruct omi as [m|].
    - exists (Some (exist _ m Hopm)).
      repeat (split; try assumption).
    - exists None.
      repeat (split; try assumption).
Qed.

