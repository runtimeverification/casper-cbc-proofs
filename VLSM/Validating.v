Require Import FinFun Streams.
From CasperCBC   
Require Import Lib.Preamble VLSM.Common VLSM.Composition.

Section validating_vlsm.

Context
    {message : Type}
    {T : VLSM_type message}
    {S : LSM_sig T}
    (X : VLSM S)
    .

Definition validating_vlsm_prop
    :=
    forall (l : label) (s : state) (om : option message),
        valid l (s, om) ->
        protocol_state_prop X s /\ option_protocol_message_prop X om
    .

Context
    (Hvalidating : validating_vlsm_prop)
    (PreLoaded := pre_loaded_vlsm X)
    .

    Lemma pre_loaded_validating_vlsm_protocol_state
        (s : state)
        (om : option message)
        (Hps : protocol_prop PreLoaded (s,om))
        : protocol_state_prop X s.
    Proof.
        remember (s, om) as som.
        generalize dependent om. generalize dependent s.
        induction Hps; intros; inversion Heqsom; subst; clear Heqsom.
        - exists None. apply (protocol_initial_state X is).
        - exists None. apply (protocol_initial_state X (@VLSM.Common.s0 _ _ S)).
        - exists om0. rewrite <- H0.
          specialize (Hvalidating _ _ _ Hv).
          destruct Hvalidating as [[_omX HpsX] [_sX HomX]].
         apply (protocol_generated X) with _omX _sX; assumption.
    Qed.

    Lemma pre_loaded_validating_vlsm_verbose_valid_protocol_transition
        (l : label)
        (is os : state)
        (iom oom : option message)
        (Ht : protocol_transition PreLoaded l (is, iom) (os, 
 oom))
        : protocol_transition X l (is, iom) (os, 
 oom)
        .
    Proof.
        destruct Ht as [[[_om Hps] [[_s Hpm] Hv]] Ht].
        specialize (Hvalidating _ _ _ Hv).
        destruct Hvalidating as [His Hiom].
        repeat split;  assumption.
    Qed.

    Lemma pre_loaded_validating_vlsm_incl
        : VLSM_incl PreLoaded X
        .
    Proof.
        apply (VLSM_incl_from_protocol_state PreLoaded X).
        - intros; assumption.
        - apply pre_loaded_validating_vlsm_protocol_state.
        - apply pre_loaded_validating_vlsm_verbose_valid_protocol_transition.
    Qed.

    Lemma pre_loaded_validating_vlsm_eq
        : VLSM_eq PreLoaded X
        .
    Proof.
        split.
        - apply pre_loaded_validating_vlsm_incl.
        - apply vlsm_incl_pre_loaded_vlsm.
    Qed.

End validating_vlsm.

Section validating_projection.

Context
    {message : Type}
    {index : Type}
    {IndEqDec : EqDec index}
    (i0 : index)
    {IT : index -> VLSM_type message}
    {IS : forall i : index, LSM_sig (IT i)}
    (IM : forall n : index, VLSM (IS n))
    (T := indexed_type IT)
    (S := indexed_sig i0 IS)
    (constraint : @label _ T -> @state _ T * option message -> Prop)
    (X := indexed_vlsm_constrained i0 IM constraint)
    .

Definition validating_projection_messages
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

Definition validating_projection_prop
    (i : index)
    :=
    forall (li : @label _ (IT i)) (siomi : @state _ (IT i) * option message),
        @valid _ _ _ (IM i) li siomi ->
        projection_valid i0 IM constraint i li siomi.

Lemma validating_projection_messages_received
    (i : index)
    : validating_projection_prop i -> validating_projection_messages i.
Proof.
    unfold validating_projection_prop. unfold validating_projection_messages. intros.
    intro Hvalid. apply H0. clear H0.
    specialize (H li (si, Some mi) Hvalid). clear Hvalid.
    destruct H as [ps [Hsi [Hps [Hpm [Hvalid Hctr]]]]].
    exists (exist _ ps Hps).
    exists (exist _ mi Hpm).
    repeat split; assumption.
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
            protocol_transition X (existT _ i li) (s, omi) (s', om')
        )
        .

Lemma validating_projection_messages_transitions
    (i : index)
    : validating_projection_prop i -> validating_transitions i.
Proof.
    unfold validating_projection_prop. unfold validating_transitions. 
    unfold projection_valid. unfold protocol_transition.
    simpl. intros.
    specialize (H li (si, omi) H0). clear H0. simpl in H.
    destruct H as [s [Hsi [Hps [Hopm [Hvalid Hctr]]]]].
    remember (@transition _ _ _ X (existT _ i li) (s, omi)) as t.
    destruct t as [s' om'].
    exists s. exists s'. exists om'.
    symmetry in Hsi. subst si; simpl.
    repeat split; try assumption.
    simpl in Heqt.
    remember (transition li (s i, omi)) as t.
    destruct t as [si' om''].
    inversion Heqt; subst.
    reflexivity.
Qed.
    
Lemma validating_transitions_messages
    (i : index)
    : validating_transitions i -> validating_projection_prop i.
Proof.
    unfold validating_projection_prop. unfold validating_transitions. intros.
    destruct siomi as [si omi].
    specialize (H si omi li H0); clear H0.
    destruct H as [s [s' [om' [Hsi [Hvalid Htransition]]]]].
    symmetry in Hsi.
    exists s. split; assumption.
Qed.

Section pre_loaded_validating_proj.
    Context
        (i : index)
        (Hvalidating : validating_projection_prop i)
        (Proj := indexed_vlsm_constrained_projection i0 IM constraint i)
        (PreLoaded := pre_loaded_vlsm (IM i))
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
        destruct Hvalid_m as [s [Hsi [Hps [Hopm Hvalid]]]].
        apply protocol_message_projection. assumption.
    Qed.

    Lemma _pre_loaded_validating_proj_protocol_state
        (som : state * option message)
        (Hps : protocol_prop PreLoaded som)
        : protocol_state_prop Proj (fst som).
    Proof.
        induction Hps.
        - exists None. apply (protocol_initial_state Proj is).
        - exists None. apply (protocol_initial_state Proj (@VLSM.Common.s0 _ _ (IS i))).
        - destruct
            (@transition message (IT i) (@pre_loaded_vlsm_sig message (IT i) (IS i) (IM i)) PreLoaded l
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

    Lemma pre_loaded_validating_proj_protocol_state
        (s : state)
        (om : option message)
        (Hps : protocol_prop PreLoaded (s,om))
        : protocol_state_prop Proj s.
    Proof.
        remember (s, om) as som. 
        assert (Hs : s = fst som) by (subst; reflexivity).
        rewrite Hs. apply _pre_loaded_validating_proj_protocol_state.
        assumption.
    Qed.

    Lemma pre_loaded_validating_proj_verbose_valid_protocol_transition
        (l : label)
        (is os : state)
        (iom oom : option message)
        (Ht : protocol_transition PreLoaded l (is, iom) (os, 
 oom))
        : protocol_transition Proj l (is, iom) (os, 
 oom)
        .
    Proof.
        destruct Ht as [[[_om Hps] [[_s Hpm] Hv]] Ht].
        repeat (split; try assumption).
        - apply pre_loaded_validating_proj_protocol_state with _om.
          assumption.
        - destruct iom as [im|].
          + apply validating_proj_protocol_message with l is. assumption.
          + exists (proj1_sig s0). apply (protocol_initial_state Proj s0).
        - apply Hvalidating. assumption.
    Qed.

    Lemma pre_loaded_validating_proj_incl
        : VLSM_incl PreLoaded Proj
        .
    Proof.
        apply (VLSM_incl_from_protocol_state PreLoaded Proj).
        - intros; assumption.
        - apply pre_loaded_validating_proj_protocol_state.
        - apply pre_loaded_validating_proj_verbose_valid_protocol_transition.
    Qed.

    Lemma pre_loaded_validating_proj_eq
        : VLSM_eq PreLoaded Proj
        .
    Proof.
        split.
        - apply pre_loaded_validating_proj_incl.
        - apply proj_pre_loaded_incl.
    Qed.

End pre_loaded_validating_proj.

End validating_projection.