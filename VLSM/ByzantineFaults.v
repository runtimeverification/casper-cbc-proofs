Require Import FinFun Streams.
(* Section 4: Byzantine fault tolerance analysis *)
From CasperCBC   
Require Import Lib.Preamble VLSM.Common VLSM.Composition.

Section ByzantineTraces.
Context
    {message : Type}
    {T : VLSM_type message}
    {S : LSM_sig T}
    (M : VLSM S)
    .

Definition byzantine_trace_prop
    (tr : @Trace _ T) :=
    exists (T' : VLSM_type message) (S' : LSM_sig T') (M' : VLSM S')
        (Proj := binary_free_composition_fst M M'),
        protocol_trace_prop Proj tr.

Lemma byzantine_pre_loaded
    (PreLoaded := pre_loaded_vlsm M)
    (tr : @Trace _ T)
    (Hbyz : byzantine_trace_prop tr)
    : protocol_trace_prop PreLoaded tr.
Proof.
    destruct Hbyz as [T' [S' [M' Htr]]].
    simpl in Htr.
    specialize
        (proj_pre_loaded_incl
            first
            (binary_IM M M')
            free_constraint
            first
            tr
            Htr
        ); intros Htr'.
    assumption.
Qed.
    

Definition all_messages_type : VLSM_type message :=
    {| label := message
     ; state := unit
    |}.

Definition all_messages_sig
    (inhm : message)
    : LSM_sig all_messages_type
    :=
    {| initial_state_prop := fun s => True
     ; initial_message_prop := fun m => False
     ; s0 := exist (fun s: @state _ all_messages_type => True) tt I
     ; m0 := inhm
     ; l0 := inhm
    |}.

Definition all_messages_transition
    (l : @label _ all_messages_type)
    (som : @state _ all_messages_type * option message)
    : @state _ all_messages_type * option message
    := (tt, Some l)
    .

Definition all_messages_valid
    (l : @label _ all_messages_type)
    (som : @state _ all_messages_type * option message)
    : Prop
    := True.

Definition all_messages_vlsm
    (inhm : message)
    : VLSM (all_messages_sig inhm)
    :=
    {| transition := all_messages_transition
     ; valid := all_messages_valid
    |}
    .

Definition byzantine_trace_prop_alt
    (tr : @Trace _ T)
    (Proj := binary_free_composition_fst M (all_messages_vlsm m0))
    :=
    protocol_trace_prop Proj tr.

Lemma byzantine_alt_byzantine
    (tr : @Trace _ T)
    (Halt : byzantine_trace_prop_alt tr)
    : byzantine_trace_prop tr.
Proof.
    exists all_messages_type.
    exists (all_messages_sig m0).
    exists (all_messages_vlsm m0).
    assumption.
Qed.

Section pre_loaded_byzantine_alt.
Context
    (PreLoaded := pre_loaded_vlsm M)
    (Proj := binary_free_composition_fst M (all_messages_vlsm m0))
    (Alt := binary_free_composition M (all_messages_vlsm m0))
    .

    Lemma alt_protocol_message
        (m : message)
        : protocol_message_prop Alt m.
    Proof.
        remember (proj1_sig (@s0 _ _ (sign Alt))) as s.
        exists s.
        assert (Ht : @transition _ _ _ Alt (existT _ second m) (s, None) = (s, Some m)).
        { simpl.
          f_equal.
          apply state_update_id.
          subst. reflexivity.
        }
        rewrite <- Ht.
        assert (Hps : protocol_prop Alt (s, None))
            by (subst; apply protocol_initial_state). 
        apply protocol_generated with None s; try assumption.
        split; exact I.
    Qed.

    Lemma alt_proj_protocol_message
        (m : message)
        : protocol_message_prop Proj m.
    Proof.
        apply protocol_message_projection.
        apply alt_protocol_message.
    Qed.

    Definition lifted_alt_state
        (s : @state _ T)
        (init := proj1_sig (@s0 _ _ (sign Alt)))
        : @state _ (type Alt)
        := @state_update _ _ binary_index_dec binary_IT init first s.

    Lemma proj_alt_protocol_state
        (sj : state)
        (om : option message)
        (Hp : protocol_prop Proj (sj, om))
        : protocol_state_prop Alt (lifted_alt_state sj).
    Proof.
      remember (sj, om) as sjom.
      generalize dependent om. generalize dependent sj.
      induction Hp; intros; inversion Heqsjom; subst; clear Heqsjom.
      - assert (Hinit : @initial_state_prop _ _ (sign Alt) (lifted_alt_state s)).
        { intros [|]; try exact I.
          unfold lifted_alt_state.
          rewrite state_update_eq. unfold s. destruct is. assumption.
        }
        remember (exist (@initial_state_prop _ _ (sign Alt)) (lifted_alt_state s) Hinit) as six.
        replace (lifted_alt_state s) with (proj1_sig six); try (subst; reflexivity).
        exists None.
        apply (protocol_initial_state Alt).
      - assert (Hinit : @initial_state_prop _ _ (sign Alt) (lifted_alt_state s)).
        { intros [|]; try exact I.
          unfold lifted_alt_state.
          rewrite state_update_eq. unfold s. destruct s0. assumption.
        }
        remember (exist (@initial_state_prop _ _ (sign Alt)) (lifted_alt_state s) Hinit) as six.
        replace (lifted_alt_state s) with (proj1_sig six); try (subst; reflexivity).
        exists None.
        apply (protocol_initial_state Alt).
      - destruct Hv as [[psX HpsX] [opm [Heqs [Heqopm Hv]]]].
        simpl in Heqs. rewrite <- Heqs in *. clear Heqs.
        specialize (IHHp1 (psX first) _om eq_refl).
        destruct Hv as [Hv _].
        simpl in Hv.
        rewrite Heqopm in Hv.
        remember (@transition _ _ _ Alt (existT _ first l) ((lifted_alt_state (psX first)), om)) as xsom'.
        destruct xsom' as [xs' om'].
        destruct IHHp1 as [_omX Hlift].
        exists om'.
        replace (lifted_alt_state sj) with xs'.
        + rewrite Heqxsom'.
          assert (Hsj : exists sj : state, protocol_prop Proj (sj, om))
            by (exists _s; assumption).
          specialize
            (@protocol_message_projection_rev
                _ _ binary_index_dec first _ _
                (binary_IM M (all_messages_vlsm m0))
                free_constraint
                first
                om
                Hsj
            ); intros [_sX HpmX].
          apply (protocol_generated Alt) with _omX _sX; try assumption.
          split; try exact I.
          assumption.
        + simpl in Heqxsom'. 
          unfold lifted_alt_state at 1 in Heqxsom'.
          rewrite state_update_eq in Heqxsom'.
          rewrite H0 in Heqxsom'.
          inversion Heqxsom'; subst.
          unfold lifted_alt_state.
          apply state_update_twice.
    Qed.

    Lemma pre_loaded_alt_protocol_state
        (sj : state)
        (om : option message)
        (Hp : protocol_prop PreLoaded (sj, om))
        : protocol_state_prop Proj sj.
    Proof.
        remember (sj, om) as sjom.
        generalize dependent om. generalize dependent sj.
        induction Hp; intros; inversion Heqsjom; subst; clear Heqsjom.
        - exists None. apply (protocol_initial_state Proj).
        - exists None. apply (protocol_initial_state Proj).
        - specialize (IHHp1 s _om eq_refl).
          specialize (IHHp2 _s om eq_refl).
          exists om0.
          replace
            (@pair
                (@state message (@binary_IT message T all_messages_type first))
                (option message)
                sj
                om0
            ) with (@transition _ _ _ Proj l (s, om)).
          destruct IHHp1 as [_omp Hpsp].
          specialize (proj_alt_protocol_state s _omp Hpsp)
          ; intro HpsX.
          destruct om as [m|].
          + destruct (alt_proj_protocol_message m) as [_smp Hpmp].
            apply (protocol_generated Proj) with _omp _smp
            ; try assumption.
            exists (exist _ (lifted_alt_state s) HpsX).
            specialize (alt_protocol_message m); intro HpmX.
            exists (Some (exist _ m HpmX)).
            repeat split; assumption.
          + apply (protocol_generated Proj) with _omp (proj1_sig (@s0 _ _ (sign Proj)))
            ; try assumption.
            * apply protocol_initial_state.
            * exists (exist _ (lifted_alt_state s) HpsX).
              exists None.
              repeat split; assumption.
    Qed.
 
    Lemma pre_loaded_alt_verbose_valid_protocol_transition
        (l : label)
        (is os : state)
        (iom oom : option message)
        (Ht : verbose_valid_protocol_transition PreLoaded l is os iom oom)
        : verbose_valid_protocol_transition Proj l is os iom oom
        .
    Proof.
        destruct Ht as [[_om Hps] [[_s Hpm] [Hv Ht]]].
        repeat (split; try assumption).
        - apply pre_loaded_alt_protocol_state with _om.
          assumption.
        - destruct iom as [im|].
          + apply alt_proj_protocol_message.
          + exists (proj1_sig s0). apply (protocol_initial_state Proj s0).
        - specialize (pre_loaded_alt_protocol_state is _om Hps)
          ; intros [_ism Hpsp].
          specialize (proj_alt_protocol_state is _ism Hpsp)
          ; intro Hps_alt.
          exists (exist _ (lifted_alt_state is) Hps_alt).
          destruct iom as [im|].
          + specialize (alt_protocol_message im); intro Hpim_alt.
            exists (Some (exist _ im Hpim_alt)).
            repeat split; assumption.
          + exists None.
            repeat split; assumption.
    Qed.

    Lemma pre_loaded_alt_incl
        : VLSM_incl PreLoaded Proj
        .
    Proof.
        apply (VLSM_incl_from_protocol_state PreLoaded Proj).
        - intros; try assumption.
        - apply pre_loaded_alt_protocol_state.
        - apply pre_loaded_alt_verbose_valid_protocol_transition.
    Qed.

    Lemma alt_pre_loaded_incl
        : VLSM_incl Proj PreLoaded
        .
    Proof.
        intros t Hpt.
        apply byzantine_pre_loaded.
        apply byzantine_alt_byzantine.
        assumption.
    Qed.

End pre_loaded_byzantine_alt.

Lemma byzantine_alt_byzantine_iff
    (tr : @Trace _ T)
    : byzantine_trace_prop_alt tr <-> byzantine_trace_prop tr.
Proof.
    split; intros.
    - apply byzantine_alt_byzantine; assumption.
    - apply pre_loaded_alt_incl.
      apply byzantine_pre_loaded.
      assumption.
Qed.

End ByzantineTraces.

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
        protocol_state_prop X s /\ exists _s, protocol_prop X (_s, om)
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
        (Ht : verbose_valid_protocol_transition PreLoaded l is os iom oom)
        : verbose_valid_protocol_transition X l is os iom oom
        .
    Proof.
        destruct Ht as [[_om Hps] [[_s Hpm] [Hv Ht]]].
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

Lemma validating_projection_messages_transitions
    (i : index)
    : validating_projection_prop i -> validating_transitions i.
Proof.
    unfold validating_projection_prop. unfold validating_transitions. 
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
    : validating_transitions i -> validating_projection_prop i.
Proof.
    unfold validating_projection_prop. unfold validating_transitions. intros.
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
        destruct Hvalid_m as [ps [opm [Hsi [Hm Hvalid]]]].
        destruct opm as [[m' Hpm]|]; try inversion Hm; clear Hm; subst.
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
        (Ht : verbose_valid_protocol_transition PreLoaded l is os iom oom)
        : verbose_valid_protocol_transition Proj l is os iom oom
        .
    Proof.
        destruct Ht as [[_om Hps] [[_s Hpm] [Hv Ht]]].
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

Section composite_validating_byzantine_traces.

    Context {message : Type}
            {index : Type}
            {IndEqDec : EqDec index}
            {IT : index -> VLSM_type message}
            (i0 : index)
            {IS : forall i : index, LSM_sig (IT i)}
            (IM : forall n : index, VLSM (IS n))
            (constraint : indexed_label IT -> indexed_state IT  * option message -> Prop)
            (X := indexed_vlsm_constrained i0 IM constraint)
            (PreLoadedX := pre_loaded_vlsm X)
            (FreeX := indexed_vlsm_free i0 IM)
            (Hvalidating: forall i : index, validating_projection_prop i0 IM constraint i)
            .
    
    Lemma pre_loaded_composite_free_protocol_message
        (l : label)
        (s : state)
        (om : option message)
        (Hv : @valid _ _ _ PreLoadedX l (s, om))
        : exists _s : state, protocol_prop FreeX (_s, om).
    Proof.
        destruct l as (i, li).
        destruct Hv as [Hv Hconstraint].
        specialize (Hvalidating i li (s i, om) Hv).
        specialize (constraint_subsumption_protocol_prop i0 IM constraint free_constraint)
        ; intro Hprotocol.
        assert (Hsubsum : constraint_subsumption constraint free_constraint)
          by (intro; intros; exact I).
        specialize (Hprotocol Hsubsum).
        destruct Hvalidating as [_ [[[mX [_sX HpmX]]|] [_ [Heqm _]]]]
        ; simpl in Heqm
        ; try apply Hprotocol in HpmX;  subst.
        + exists _sX. assumption.
        + exists (proj1_sig (@Common.s0 _ _ (sign FreeX))).
          apply (protocol_initial_state FreeX).
    Qed.

    
    Lemma pre_loaded_composite_free_protocol_state
        (s : state)
        (om : option message)
        (Hps : protocol_prop PreLoadedX (s,om))
        : protocol_state_prop FreeX s.
    Proof.
        apply VLSM_incl_protocol_state with PreLoadedX om
        ; try (intros; assumption).
        - apply pre_loaded_composite_free_protocol_message.
        - intros. destruct H as [Hv Hc].
          split; try assumption.
          exact I.
        - intros; reflexivity.
    Qed.

    Lemma pre_loaded_composite_free_incl
        : VLSM_incl PreLoadedX FreeX
        .
    Proof.
        apply basic_VLSM_incl
        ; try (intros; assumption).
        - apply pre_loaded_composite_free_protocol_message.
        - intros. destruct H as [Hv Hc].
          split; try assumption.
          exact I.
        - intros; reflexivity.
    Qed.

    Lemma composite_validating_byzantine_traces_are_free
        (tr : @Trace _ (type X))
        (Hbyz : byzantine_trace_prop X tr)
        : protocol_trace_prop FreeX tr.
    Proof.
        apply pre_loaded_composite_free_incl.
        apply alt_pre_loaded_incl.
        apply byzantine_alt_byzantine_iff.
        assumption.
    Qed.

End composite_validating_byzantine_traces.