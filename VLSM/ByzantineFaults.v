Require Import FinFun Streams.
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

Definition validating_messages
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

Definition validating_condition
    (i : index)
    :=
    forall (li : @label _ (IT i)) (siomi : @state _ (IT i) * option message),
        @valid _ _ _ (IM i) li siomi ->
        projection_valid i0 IM constraint i li siomi.

Lemma validating_messages_received
    (i : index)
    : validating_condition i -> validating_messages i.
Proof.
    unfold validating_condition. unfold validating_messages. intros.
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
    : validating_condition i -> validating_transitions i.
Proof.
    unfold validating_condition. unfold validating_transitions. 
    unfold projection_valid. unfold verbose_valid_protocol_transition.
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
    : validating_transitions i -> validating_condition i.
Proof.
    unfold validating_condition. unfold validating_transitions. intros.
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

Section message_full_validating_proj.
    Context
        (i : index)
        (Hvalidating : validating_condition i)
        (Proj := indexed_vlsm_constrained_projection i0 IM constraint i)
        (Full := message_full_vlsm (IM i))
        .

    Lemma validating_proj_protocol_message
        (m : message)
        (li : label)
        (si : state)
        (Hvalid_m : @valid _ _ _ (IM i) li (si, Some m))
        : protocol_message_prop Proj m
        .
    Proof.
        apply Hvalidating in Hvalid_m.
        destruct Hvalid_m as [ps [opm [Hsi [Hm Hvalid]]]].
        destruct opm as [[m' Hpm]|]; try inversion Hm; clear Hm; subst.
        apply protocol_message_projection. assumption.
    Qed.



    Lemma _message_full_validating_proj_protocol_state
        (som : state * option message)
        (Hps : protocol_prop Full som)
        : protocol_state_prop Proj (fst som).
    Proof.
        induction Hps.
        - exists None. apply (protocol_initial_state Proj is).
        - exists None. apply (protocol_initial_state Proj (@VLSM.Common.s0 _ _ (IS i))).
        - destruct
            (@transition message (IT i) (@message_full_vlsm_sig message (IT i) (IS i) (IM i)) Full l
                (@pair (@state message (IT i)) (option message) s om)) as [s' om'] eqn:Ht.
          exists om'. simpl. rewrite <- Ht.
          clear IHHps2. simpl in IHHps1. clear Hps1 Hps2 _s _om.
          destruct IHHps1 as [_om Hps].
          destruct om as [m|].
          + specialize (validating_proj_protocol_message m l s Hv); intros [_s Hpm].
            apply (protocol_generated Proj) with _om _s; try assumption.
            apply Hvalidating. assumption.
          + apply (protocol_generated Proj) with _om (proj1_sig s0); try assumption.
            * apply (protocol_initial_state Proj s0).
            * apply Hvalidating. assumption.
    Qed.

    Lemma message_full_validating_proj_protocol_state
        (s : state)
        (om : option message)
        (Hps : protocol_prop Full (s,om))
        : protocol_state_prop Proj s.
    Proof.
        remember (s, om) as som. 
        assert (Hs : s = fst som) by (subst; reflexivity).
        rewrite Hs. apply _message_full_validating_proj_protocol_state.
        assumption.
    Qed.

    Lemma message_full_validating_proj_verbose_valid_protocol_transition
        (l : label)
        (is os : state)
        (iom oom : option message)
        (Ht : verbose_valid_protocol_transition Full l is os iom oom)
        : verbose_valid_protocol_transition Proj l is os iom oom
        .
    Proof.
        destruct Ht as [[_om Hps] [[_s Hpm] [Hv Ht]]].
        repeat (split; try assumption).
        - apply message_full_validating_proj_protocol_state with _om.
          assumption.
        - destruct iom as [im|].
          + apply validating_proj_protocol_message with l is. assumption.
          + exists (proj1_sig s0). apply (protocol_initial_state Proj s0).
        - apply Hvalidating. assumption.
    Qed.

    Lemma message_full_validating_proj_finite_ptrace
        (s : state)
        (ls : list in_state_out)
        (Hpxt : finite_ptrace_from Full s ls)
        : finite_ptrace_from Proj s ls
        .
    Proof.
        induction Hpxt.
        - constructor.
          destruct H as [m H].
          apply message_full_validating_proj_protocol_state with m. assumption.
        - constructor; try assumption.
          apply message_full_validating_proj_verbose_valid_protocol_transition.
          assumption.
    Qed.

    Lemma message_full_validating_proj_infinite_ptrace
        (s : state)
        (ls : Stream in_state_out)
        (Hpxt : infinite_ptrace_from Full s ls)
        : infinite_ptrace_from Proj s ls
        .
    Proof.
        generalize dependent ls. generalize dependent s.
        cofix H.
        intros s [[l input destination output] ls] Hx.
        inversion Hx; subst.
        specialize (H destination ls H3).
        constructor; try assumption.
        apply message_full_validating_proj_verbose_valid_protocol_transition.
        assumption.
    Qed.

    Lemma message_full_validating_proj_incl
        : VLSM_incl Full Proj
        .
    Proof.
        intros [s ls| s ss]; simpl; intros [Hxt Hinit].  
        - apply message_full_validating_proj_finite_ptrace in Hxt.
          split; try assumption.
        - apply message_full_validating_proj_infinite_ptrace in Hxt.
          split; try assumption.
    Qed.

    Lemma message_full_validating_proj_eq
        : VLSM_eq Full Proj
        .
    Proof.
        split.
        - apply message_full_validating_proj_incl.
        - apply proj_message_full_incl.
    Qed.

End message_full_validating_proj.
