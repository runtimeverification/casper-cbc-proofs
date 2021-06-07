Require Import
  List Coq.Vectors.Fin FinFun ListSet
  Arith.Compare_dec Lia
  Program
  Coq.Logic.JMeq
  .
Import ListNotations.
From CasperCBC
  Require Import
    Preamble ListExtras FinExtras FinFunExtras
    Lib.Measurable
    VLSM.Common VLSM.Composition VLSM.Equivocation VLSM.ProjectionTraces
    VLSM.Equivocators.Common VLSM.Equivocators.Projections
    VLSM.Equivocators.MessageProperties
    VLSM.Equivocators.Composition.Common
    VLSM.Equivocators.Composition.Projections
    VLSM.Equivocators.Composition.SimulatingFree.FullReplayTraces
    VLSM.Equivocators.Composition.LimitedEquivocation.LimitedEquivocation
    VLSM.Plans
    VLSM.DependentMessages
    .

(** * VLSM Equivocators Simulating Limited Composite *)

Section all_equivocating.

Context
  {message : Type}
  `{EqDecision message}
  (index : Type)
  {IndEqDec : EqDecision index}
  (IM : index -> VLSM message)
  (Hbs : forall i : index, has_been_sent_capability (IM i))
  (Hbr : forall i : index, has_been_received_capability (IM i))
  (Hbo : forall i : index, has_been_observed_capability (IM i) := fun i => has_been_observed_capability_from_sent_received (IM i))
  (i0 : Inhabited index)
  {index_listing : list index}
  (finite_index : Listing index_listing)
  {ValMeasurable : Measurable index}
  (sender : message -> option index)
  (globally_known_equivocators : composite_state IM -> set index)
  {Hdm : DependentMessages sender (fun i => i) IM Hbs Hbr}
  {Hknown_equivocators : known_equivocators_capability finite_index IM Hbs Hbr i0 sender globally_known_equivocators}
  {reachable_threshold : ReachableThreshold index}
  (XE : VLSM message := full_node_equivocators_limited_equivocation_vlsm IM Hbs finite_index sender Hbr)
  (X : VLSM message := full_node_limited_equivocation_vlsm_composition IM Hbs Hbr i0 sender globally_known_equivocators)
  (equivocators_free_Hbs := composite_has_been_sent_capability (equivocator_IM IM) (free_constraint (equivocator_IM IM)) finite_index (equivocator_Hbs IM Hbs))
  (FreeE : VLSM message := free_composite_vlsm (equivocator_IM IM))
  (FreeE_has_been_sent_capability : has_been_sent_capability FreeE := composite_has_been_sent_capability (equivocator_IM IM) (free_constraint (equivocator_IM IM)) finite_index (equivocator_Hbs IM Hbs))
  (Hdec_init : forall i, vdecidable_initial_messages_prop (IM i))
  (comopsite_initial_decidable := composite_decidable_initial_message IM finite_index Hdec_init)
  (Free := free_composite_vlsm IM)
  (Free_has_been_sent_capability : has_been_sent_capability Free := composite_has_been_sent_capability IM (free_constraint IM) finite_index Hbs)
  (Free_has_been_received_capability : has_been_received_capability Free := composite_has_been_received_capability IM (free_constraint IM) finite_index Hbr)
  (Free_has_been_observed_capability : has_been_observed_capability Free := has_been_observed_capability_from_sent_received Free)
  (Free_no_additional_equivocation_decidable := no_additional_equivocations_dec Free comopsite_initial_decidable)
  (Free_no_additional_equivocation_constraint_dec : RelDecision (no_additional_equivocations_constraint Free):= no_additional_equivocations_constraint_dec finite_index IM Hbs Hbr i0 Hdec_init)
  .


Local Ltac unfold_transition  Ht :=
  ( unfold transition, equivocator_IM, Common.equivocator_IM, equivocator_vlsm
  , mk_vlsm, machine, projT2, equivocator_vlsm_machine, equivocator_transition
  in Ht).

Local Ltac unfold_equivocators_transition_item_project :=
(
  simpl;
  unfold equivocators_transition_item_project; simpl;
  unfold composite_transition_item_projection; simpl;
  unfold composite_transition_item_projection_from_eq; simpl;
  unfold eq_rect_r; simpl
).

(**
By replaying a [protocol_trace] on top of a [protocol_state] we obtain
a [protocol_trace]. The proof is parameterized in a constraint having "good"
properties, to allow deriving the [protocol_trace] property both for
the free composition of equivocators and for the no message equivocation
composition of equivocators (the latter proof uses the first result,
and both use the one below)
*)
Lemma replayed_trace_from_protocol
  (full_replay_state : composite_state (equivocator_IM IM))
  (Hfull_replay_state : protocol_state_prop XE full_replay_state)
  (is : composite_state (equivocator_IM IM))
  (tr : list (composite_transition_item (equivocator_IM IM)))
  (Htr : finite_protocol_trace XE is tr)
  (constraint :  composite_label (equivocator_IM IM) -> composite_state (equivocator_IM IM) * option message -> Prop)
  (Hconstraint_subsumption :
    constraint_subsumption (equivocator_IM IM)
      (no_equivocations_additional_constraint (equivocator_IM IM)
        (free_constraint (equivocator_IM IM)) (equivocator_Hbs IM Hbs) finite_index)
      constraint)
  (Hconstraint :
    forall
      [epref esuf
      eitem
      id fd eqv l0]
      (Htr_eq : tr = epref ++ [eitem] ++ esuf)
      (Hleitem : l eitem = existT _ eqv (l0, Existing (IM (eqv)) id fd)),
      constraint
        (existT _ eqv (l0, Existing (IM eqv) (id + S (projT1 (full_replay_state eqv))) fd))
        (finite_trace_last full_replay_state (replayed_trace_from IM index_listing full_replay_state is epref)
        , input eitem)
  )
  : finite_protocol_trace_from (composite_vlsm (equivocator_IM IM) constraint)
      full_replay_state (replayed_trace_from IM index_listing full_replay_state is tr).
Proof.
  assert (Hfull_replay_state' : protocol_state_prop (composite_vlsm (equivocator_IM IM) constraint) full_replay_state).
  { revert Hfull_replay_state.
    apply VLSM_incl_protocol_state.
    apply parametric_constrained_incl.
    assumption.
  }
  apply (finite_protocol_plan_iff  (pre_loaded_vlsm  (composite_vlsm equivocator_IM constraint) seed)).
  split; [assumption|].
  specialize
    (finite_protocol_trace_from_to_plan SeededXE _ _ (proj1 Htr))
    as Htr'.
  apply finite_protocol_plan_iff in Htr'.
  split.
  - apply Forall_forall. intros a Ha.
    apply in_app_iff in Ha.
    destruct Ha as [Ha | Ha].
    + apply in_map_iff in Ha.
      destruct Ha as [eqv [Ha _]].
      subst. simpl. apply option_protocol_message_None.
    + apply in_map_iff in Ha.
      destruct Ha as [item [Ha Hitem]].
      destruct Htr' as [_ [Hinputs _]].
      rewrite Forall_forall in Hinputs.
      unfold update_equivocators_transition_item_descriptor in Ha.
      destruct item. destruct l eqn:Hl.
      specialize (Hinputs {| label_a := l; input_a := input|}).
      spec Hinputs.
      { apply in_map_iff. eexists _. split; [|apply Hitem].
        subst l. reflexivity.
      }
      simpl in Hinputs. subst a.
      assert (Hinputs' : option_protocol_message_prop (pre_loaded_vlsm (composite_vlsm equivocator_IM constraint) seed) input).
      { destruct input; [|apply option_protocol_message_None].
        apply can_emit_protocol_iff. apply can_emit_protocol_iff in Hinputs.
        destruct Hinputs as [Hinit | Hemit]; [left; assumption|].
        right. revert Hemit. apply VLSM_incl_can_emit.
        apply (parametric_constrained_incl constraint). assumption.
      }
      destruct v. destruct m; assumption.
  - intros.
    rewrite app_assoc in Heqa. apply order_decompositions in Heqa as Hprefa.
    rewrite <- or_assoc in Hprefa.
    destruct Hprefa as [Hprefa | [suf Hprefa]].
    + assert (Hai: In ai (spawn_initial_state is)).
      { destruct Hprefa as [Hprefa | Hprefa].
        - rewrite Hprefa; apply in_app_iff; right; left; reflexivity.
        - destruct Hprefa as [suf1 Hprefa].
          rewrite Hprefa.
          apply in_app_iff. left.
          apply in_app_iff. right.
          left. reflexivity.
      }
      apply in_map_iff in Hai. destruct Hai as [eqv [Hai _]].
      subst ai.
      apply equivocators_no_equivocations_vlsm_newmachine_always_valid; [|assumption].
      destruct Htr as [Htr His]. specialize (His (eqv)).
      destruct His as [Hzero His]. assumption.
    + rewrite Hprefa in Heqa.
      rewrite <- app_assoc in Heqa.
      apply app_inv_head in Heqa.
      assert (Hsuf: suf = [] \/ suf <> [])
        by (destruct suf; [left; congruence | right; congruence]).
      destruct Hsuf as [Hsuf|Hsuf].
      * subst.
        assert (Hai: In ai (spawn_initial_state is)).
        { rewrite app_nil_r in Hprefa. rewrite <- Hprefa; apply in_app_iff; right; left; reflexivity.
        }
        apply in_map_iff in Hai. destruct Hai as [eqv [Hai _]].
        subst ai.
        apply equivocators_no_equivocations_vlsm_newmachine_always_valid; [|assumption].
        destruct Htr as [Htr His]. specialize (His (eqv)).
        destruct His as [Hzero His]. assumption.
      * apply exists_last in Hsuf. destruct Hsuf as (pref, (ai', Hpref)).
        subst suf. rewrite app_assoc in Hprefa.
        apply app_inj_tail in Hprefa.
        destruct Hprefa. subst ai' prefa.
        apply  map_eq_app in Heqa.
        destruct Heqa as [eprefai [esuf [Heq_tr [Heprefai Hesuf]]]].
        apply map_eq_app in Heprefai.
        destruct Heprefai as [epref [eai [Heq_prefai [Hepref Heai]]]].
        apply map_eq_cons in Heai.
        destruct Heai as [ea [enil [Heq_eai [Heai Henil]]]].
        apply map_eq_nil in Henil. subst enil. subst eai. subst eprefai.
        rewrite <- app_assoc in Heq_tr.
        destruct Htr' as [His [Hinputs Hvalids]].
        specialize
          (Hvalids
            (trace_to_plan SeededXE epref)
            (trace_to_plan SeededXE esuf)
            (_transition_item_to_plan_item ea)
          ).
        spec Hvalids.
        { subst tr. unfold trace_to_plan, _trace_to_plan. repeat rewrite map_app. reflexivity. }
        destruct ea. simpl in *.
        destruct l as (eqv, l).
        destruct l as (l,d).
        destruct Hvalids as [Hvalids Hnoequiv].
        unfold vvalid in Hvalids. simpl in Hvalids.
        unfold vvalid in Hvalids. simpl in Hvalids.
        unfold no_equivocations_additional_constraint_with_pre_loaded in Hnoequiv.
        unfold no_equivocations_except_from in Hnoequiv.
        simpl in Hnoequiv.
        destruct d as [sd | id fd].
        -- subst ai. simpl. destruct Hvalids as [Hsd Hinput]. subst input.
          repeat split; [assumption|].
          apply Hconstraint_subsumption.
          assumption.
        -- subst. simpl. destruct Hvalids as [Hid Hvalids].
          unfold lst. clear lst.
          split.
          ++ simpl. unfold vvalid. simpl.
            specialize
              (replayed_trace_from_state_correspondence' full_replay_state _ (proj2 Htr)
              epref eqv
              )
              as Hstate.
            destruct Hstate as [Hsize [Houtput [Hstate Hstate_pre]]].
            spec Hstate id Hid.
            destruct Hstate as [Hi Hstate].
            exists Hi.
            clear -Hstate Hvalids.
            match goal with
            |- vvalid _ _ (?s1,_) =>
              match type of Hvalids with
              | vvalid _ _ (?s2,_) =>
                replace s1 with s2
              end
            end.
            assumption.
          ++ simpl. rewrite <- (apply_plan_last SeededXE) in *.
            rewrite <- (apply_plan_last (pre_loaded_vlsm (composite_vlsm equivocator_IM constraint) seed)).
            apply (Hconstraint _ _ _  _ _ _ _ eq_refl eq_refl).
Qed.

Lemma replayed_trace_from_protocol_free
  (full_replay_state : vstate equivocators_no_equivocations_vlsm)
  (Hfull_replay_state : protocol_state_prop SeededXE full_replay_state)
  (is : vstate equivocators_no_equivocations_vlsm)
  (tr : list (composite_transition_item equivocator_IM))
  (Htr : finite_protocol_trace SeededXE is tr)
  : finite_protocol_trace_from SeededFree
      full_replay_state (replayed_trace_from full_replay_state is tr).
Proof.
  specialize
    (replayed_trace_from_protocol _ Hfull_replay_state _ _ Htr (free_constraint equivocator_IM))
    as Hreplay.
  spec Hreplay. { intro; intros. exact I. }
  spec Hreplay. { intros. exact I. }
  assumption.
Qed.



Lemma replayed_trace_from_protocol_equivocating
  (full_replay_state : composite_state (equivocator_IM IM))
  (Hfull_replay_state : protocol_state_prop XE full_replay_state)
  (is : vstate XE)
  (tr : list (composite_transition_item (equivocator_IM IM)))
  (Htr : finite_protocol_trace XE is tr)
  : finite_protocol_trace_from XE
      full_replay_state (replayed_trace_from IM index_listing full_replay_state is tr).
Proof.
  apply replayed_trace_from_protocol
  ;[assumption|assumption|intro; intros; assumption|].
  intros.
  split; [|exact I].
  subst tr.
  destruct Htr as [Htr His].
  apply finite_protocol_trace_from_app_iff in Htr.
  destruct Htr as [Hepref Hesuf].
  specialize (replayed_trace_from_protocol_free _ Hfull_replay_state _ _ (conj Hepref His))
    as Hreplay_epref_free.
  assert
    (Hreplay_epref_pre :
      finite_protocol_trace_from PreFree full_replay_state (replayed_trace_from full_replay_state is epref)
    ).
  { revert Hreplay_epref_free. apply VLSM_incl_finite_protocol_trace_from.
    apply pre_loaded_vlsm_incl_pre_loaded_with_all_messages.
  }
  specialize (finite_ptrace_last_pstate _ _ _ Hreplay_epref_pre) as Hlast_replay_pre.
  destruct (input eitem) as [m|] eqn:Hinput; [|exact I].
  apply finite_ptrace_first_valid_transition in Hesuf as Hitem.
  destruct Hitem as [[Hs [Hinp [_ Heqv] ]] _].
  destruct eitem. simpl in Hinput, Hleitem. subst l.
  subst input.
  destruct Heqv as [[Heqv | Hinitial] _]; [| right; assumption].
  left. apply proper_sent; [assumption|].
  assert
    (Hepref_pre :
      finite_protocol_trace_from PreFree is epref
    ).
  { revert Hepref. apply VLSM_incl_finite_protocol_trace_from.
    apply seeded_equivocators_incl_preloaded.
  }
  specialize (finite_ptrace_last_pstate _ _ _ Hepref_pre) as Hlast_pre.

  apply proper_sent in Heqv; [|assumption].
  apply ptrace_add_default_last in Hepref_pre as Hepref_pre'.
  specialize (Heqv is epref (conj Hepref_pre' His)).
  apply has_been_sent_consistency; [|assumption|].
  { apply (composite_has_been_sent_capability equivocator_IM (free_constraint equivocator_IM) finite_index (equivocator_Hbs IM Hbs)).
  }
  apply finite_protocol_trace_from_complete_left in Hreplay_epref_pre as Hpre_replay.
  destruct Hpre_replay as [is_replay [trs_replay [Htrs_replay Hfull_replay_state_lst]]].
  apply ptrace_add_default_last in Htrs_replay as Htrs_replay'.
  rewrite finite_trace_last_app in Htrs_replay'.
  rewrite Hfull_replay_state_lst in Htrs_replay'.
  eexists _. eexists _. exists Htrs_replay'.
  - apply Exists_exists in Heqv.
    destruct Heqv as [mitem [Hmitem Houtput]].
    apply in_split in Hmitem.
    destruct Hmitem as [pref [suf Heqepref]].
    change (mitem :: suf) with ([mitem] ++ suf) in Heqepref.
    subst epref.
    rewrite app_assoc.
    rewrite replayed_trace_from_app.
    apply Exists_app. right. apply Exists_app. left.
    destruct
      (replayed_trace_from_state_correspondence' full_replay_state is His (pref ++ [mitem]) eqv)
      as [_ [Houtput' _]].
    spec Houtput'.
    { intro contra; destruct pref; discriminate contra. }
    rewrite app_assoc in Hepref.
    apply (finite_protocol_trace_from_app_iff SeededXE) in Hepref.
    apply proj1 in Hepref.
    specialize (trace_to_plan_to_trace SeededXE _ _ Hepref) as Hfst.

    replace (fst(composite_apply_plan equivocator_IM is
      (composite_trace_to_plan equivocator_IM
        (pref ++ [mitem])))) with (pref ++ [mitem])
      in Houtput'.
    change
      (fst (applied_replay_plan_from full_replay_state is (pref ++ [mitem])))
      with (replayed_trace_from full_replay_state is (pref ++ [mitem]))
      in Houtput'.
    rewrite! replayed_trace_from_app in Houtput'.
    simpl in Houtput'.
    rewrite last_error_is_last in Houtput'.
    rewrite replayed_trace_from_app.
    apply Exists_app. right. simpl.
    unfold composite_apply_plan,_apply_plan in Houtput'.
    unfold composite_apply_plan,_apply_plan. simpl in *.
    destruct (update_equivocators_transition_item_descriptor full_replay_state mitem) eqn:Hupdated_item.
    simpl in *.
    destruct label_a as (i, li).
    match goal with
    |- context [vtransition ?V ?l ?som] =>
      destruct (vtransition V l som) eqn:Ht
    end.
    simpl in *.
    rewrite last_error_is_last in Houtput'.
    simpl in Houtput'. inversion Houtput'.
    left. simpl. assumption.
Qed.



Lemma equivocators_protocol_vlsm_run_project
  (runX : vproto_run X)
  (HrunX : vlsm_run_prop X runX)
  : exists
    (run : vproto_run XE)
    (Hrun : vlsm_run_prop XE run)
    (eqv_descriptors : equivocator_descriptors IM)
    (Heqv : not_equivocating_equivocator_descriptors IM eqv_descriptors (fst (final run)))
    (Hproject : equivocators_trace_project IM eqv_descriptors (transitions run)
      = Some (transitions runX, zero_descriptor _))
    (Hdestination : equivocators_state_project IM eqv_descriptors (fst (final run)) = fst (final runX))
    (Houtput : snd (final run) = snd (final runX)),
    equivocators_state_project IM (zero_descriptor _) (start run) = start runX.
Proof.
  induction HrunX.
  - specialize (lift_initial_to_equivocators_state IM Hbs finite_index is His) as Hs.
    remember (lift_to_equivocators_state IM is) as s.
    exists (@mk_proto_run _ (type XE) s [] (s, None)).
    split; [constructor; assumption|].
    exists (zero_descriptor _).
    split; [apply zero_descriptor_not_equivocating|].
    exists eq_refl.
    subst.
    simpl.
    assert
      (Hproject : equivocators_state_project IM (zero_descriptor IM)
        (lift_to_equivocators_state IM is) = is)
    ; [|exists Hproject; exists eq_refl; assumption].
    apply functional_extensionality_dep_good.
    reflexivity.
  - rename s into is, Hs into His.
    simpl.
    pose ((exist _ is His) : vinitial_state X) as v.
    pose ((fun i => mk_singleton_state _ (is i)) :
          vstate XE) as is'.
    assert (vinitial_state_prop _ is') as His'.
    {
      intro i. apply mk_singleton_initial_state. apply His.
    }
    pose ((exist _ is' His') : vinitial_state XE) as vsz.
    exists (@mk_proto_run _ (type XE) (proj1_sig vsz) [] ((proj1_sig vsz), Some im)).
    assert (Him' : vinitial_message_prop XE im).
    { unfold vinitial_message_prop. simpl.
      destruct Him as (eqv, ((imi, Himi), Himeq)).
      subst im. simpl in *.
      exists eqv. simpl in *.
      exists (exist _ imi Himi). reflexivity.
    }
    split; [apply (empty_run_initial_message XE im Him'); apply proj2_sig|].
    exists (zero_descriptor _).
    split; [apply zero_descriptor_not_equivocating|].
    exists eq_refl. unfold final. unfold start. unfold fst. unfold snd.
    assert
      (Hproject : equivocators_state_project IM (zero_descriptor IM) (` vsz) = is)
    ; [| exists Hproject; exists eq_refl; assumption].
    unfold vsz, is'; simpl.
    apply functional_extensionality_dep_good.
    reflexivity.
  - destruct IHHrunX1 as [eqv_state_run [Heqv_state_run [eqv_state_descriptors [Heqv_state_descriptors [Hstate_project [Hstate_final_project [_ Hstate_start_project]]]]]]].
    destruct IHHrunX2 as [eqv_msg_run [Heqv_msg_run [eqv_msg_descriptors [Heqv_msg_descriptors [Hmsg_project [_ [Hom Hmsg_start_project]]]]]]].
    specialize (run_is_trace XE (exist _ _ Heqv_state_run))
      as Hstate_trace.
    simpl in Hstate_trace.
    specialize
      (vlsm_run_last_state X
        (exist _ _ HrunX1)
      ) as Hstate_final.
    simpl in Hstate_final.
    simpl in Hstate_final_project.
    rewrite <- Hstate_final in Hstate_final_project.
    specialize (run_is_trace XE (exist _ _ Heqv_msg_run))
      as Hmsg_trace.
    specialize
      (finite_ptrace_last_pstate XE _ _ (proj1 Hstate_trace))
      as Hstate_protocol.
    simpl in Hmsg_trace.
    specialize
      (replayed_trace_from_protocol_equivocating
        IM Hbs index_listing finite_index
        _ _ Hstate_protocol _ _ Hmsg_trace
      )
      as Hmsg_trace_full_replay.
    simpl in Hmsg_trace_full_replay.
    match type of Hmsg_trace_full_replay with
    | finite_protocol_trace_from _ _ ?EMsgTr =>
      remember EMsgTr as emsg_tr
    end.
    specialize
      (finite_protocol_trace_from_app_iff SeededXE
        (start eqv_state_run) (transitions eqv_state_run)
        emsg_tr
      ) as Happ.
    apply proj1 in Happ.
    specialize (Happ (conj (proj1 Hstate_trace) Hmsg_trace_full_replay)).
    simpl.
    specialize
      (extend_right_finite_trace_from SeededXE Happ) as Happ_extend.
    destruct l as (eqv, li).
    specialize (Heqv_state_descriptors eqv) as Heqv_state_descriptors_i.
    destruct (eqv_state_descriptors eqv) as [| eqv_state_descriptors_i eqv_state_descriptors_f]
    eqn:Heqv_state_descriptors_eqv
    ; [contradict Heqv_state_descriptors_i|].
    destruct eqv_state_descriptors_f; [contradict Heqv_state_descriptors_i|].
    pose
      (existT (fun i : index => vlabel (equivocator_IM i)) (eqv) (li, Existing (IM (eqv)) eqv_state_descriptors_i false))
      as el.
    pose (finite_trace_last (start eqv_state_run) (transitions eqv_state_run ++ emsg_tr))
      as es.

    destruct (vtransition SeededXE el (es, om))
      as (es', om') eqn:Hesom'.
    specialize
      (Happ_extend  el om es' om').
    unfold protocol_transition in Happ_extend.
    match type of Happ_extend with
    | context [?t = _] =>
      replace t with (es', om')
    end.
    simpl in Heqv_state_descriptors_i.
    assert (Heqv_t := Hesom').
    unfold vtransition in Hesom'. simpl in Hesom'.
    unfold vtransition in Hesom'.
    match type of Hesom' with
    | (let (_, _) := ?t in _) = _ => remember t as tesom'
    end.
    unfold_transition Heqtesom'. unfold snd in Heqtesom'.
    subst tesom'.
    destruct
      (replayed_trace_from_state_correspondence
        IM Hbs index_listing finite_index seed
        (finite_trace_last (start eqv_state_run) (transitions eqv_state_run))
        _  _ Hmsg_trace
      )
      as [Houtput Hstate].
    specialize (Hstate eqv) as Hstate_eqv.
    destruct Hstate_eqv as [Hstate_size [Hstate_msg Hstate_state]].
    spec Hstate_state eqv_state_descriptors_i.

    remember (finite_trace_last (start eqv_state_run) (transitions eqv_state_run ++ emsg_tr))
      as ess.
    rewrite finite_trace_last_app in Heqess.
    specialize
      (vlsm_run_last_state SeededXE
        (exist _ _ Heqv_state_run)
      ) as Heqv_state_final.
    simpl in Heqv_state_final.
    simpl in Heqess, Hstate_state, Heqemsg_tr.
    rewrite Heqv_state_final in Heqess, Heqemsg_tr, Hstate_state.
    specialize (Hstate_state Heqv_state_descriptors_i) as Hstate_state_i.
    destruct Hstate_state_i as [Heqv_merged_descriptors_i Hstate_state_i].
    rewrite Heqemsg_tr in Heqess.
    change ess with es in Happ_extend.
    subst ess. unfold es in Hesom'.

    match type of Hesom' with
    | context [le_lt_dec ?X ?Y] =>
       destruct (le_lt_dec X Y)
    end
    ; [lia|].
    replace (of_nat_lt l) with (of_nat_lt Heqv_merged_descriptors_i) in Hesom' by apply of_nat_ext. clear l.
    rewrite Hstate_state_i in Hesom'.
    unfold fst in Hesom' at 1.
    specialize (equal_f_dep Hstate_final_project (eqv)) as Hstate_final_project_eqv.
    unfold equivocators_state_project in Hstate_final_project_eqv.
    unfold Common.equivocators_state_project in Hstate_final_project_eqv.
    unfold equivocator_state_descriptor_project in Hstate_final_project_eqv.
    unfold equivocator_state_project in Hstate_final_project_eqv.
    rewrite Heqv_state_descriptors_eqv in Hstate_final_project_eqv.
    match type of Heqv_state_descriptors_i with
    | context [projT1 ?s] => destruct s as (n_eqv_state_run_eqv, s_eqv_state_run_eqv) eqn:Heqeqv_state_run_eqv
    end.
    simpl in Heqv_state_descriptors_i.
    destruct (le_lt_dec (S n_eqv_state_run_eqv) eqv_state_descriptors_i); [lia|].
    replace (of_nat_lt l) with (of_nat_lt Heqv_state_descriptors_i) in Hstate_final_project_eqv by apply of_nat_ext. clear l.
    simpl in Hesom', Hstate_final_project_eqv.
    rewrite Hstate_final_project_eqv in Hesom'.
    rewrite Hstate_final in Hesom'.
    simpl in som'.
    remember som' as som''. unfold som' in *. clear som'.
    unfold s in Heqsom''. simpl in Heqsom''.
    match type of Heqsom'' with
    | _ = (let (_,_) := ?t in _)  => destruct t as (si', om'') eqn:Ht
    end.
    subst som''. simpl.
    inversion Hesom'. clear Hesom'. subst om''.

    spec Happ_extend.
    {
      split; [|assumption].
      specialize (finite_ptrace_last_pstate SeededXE _ _ Happ) as Hps.
      rewrite finite_trace_last_app in Hps. progress simpl in Hps.
      rewrite Heqv_state_final in Hps.
      split; [subst; assumption|].
      assert (Hpom : option_protocol_message_prop SeededXE om).
      { exists (fst (final eqv_msg_run)).
        unfold om. rewrite <- Hom.
        specialize
          (run_is_protocol SeededXE
            (exist _ _ Heqv_msg_run)
          ) as Hpom.
        simpl in Hpom.
        destruct (final eqv_msg_run) eqn:Hfin. simpl.
        simpl in *. rewrite Hfin in Hpom.
        assumption.
      }
      split; [assumption|].
      split.
      - simpl. unfold vvalid. simpl.
        exists Heqv_merged_descriptors_i.
        unfold es.
        rewrite Hstate_state_i. simpl.
        rewrite Hstate_final_project_eqv.
        rewrite Hstate_final. clear -Hv.
        simpl in Hv. destruct Hv as [Hv _].
        assumption.
      - split; [|exact I].
        unfold om in *. destruct (snd (final msg_run)) eqn:Hm; [|exact I].
        destruct (null_dec (transitions eqv_msg_run)).
        + right.
          apply (vlsm_run_no_transitions_output SeededXE)
            with (run := eqv_msg_run); assumption.
        + left. apply proper_sent.
          {
            specialize (finite_ptrace_last_pstate SeededXE _ _ Happ)
              as Hlst.
            rewrite finite_trace_last_app in Hlst. progress simpl in Hlst.
            rewrite Heqv_state_final in Hlst.
            subst. subst es.
            revert Hlst.
            apply VLSM_incl_protocol_state.
            apply seeded_equivocators_incl_preloaded.
          }
          specialize
            (vlsm_run_last_final SeededXE (exist _ _ Heqv_msg_run))
            as Hfinal.
          simpl in Hfinal.
          spec Hfinal n.
          assert
            (Happ_pre :
              finite_protocol_trace PreFree
                (start eqv_state_run) (transitions eqv_state_run ++ emsg_tr)).
          {
            apply VLSM_incl_finite_protocol_trace; [apply seeded_equivocators_incl_preloaded|].
            split; [assumption|].
            apply vlsm_run_initial_state. assumption.
          }
          assert
            (Hbs_free : has_been_sent_capability (free_composite_vlsm equivocator_IM)).
          { exact (composite_has_been_sent_capability equivocator_IM (free_constraint equivocator_IM) finite_index (equivocator_Hbs IM Hbs)).
          }
          apply ptrace_add_last with (f:=es) in Happ_pre.
          2:{
            rewrite finite_trace_last_app.
            simpl.
            unfold es.
            rewrite !Heqv_state_final. subst. reflexivity.
          }
          apply has_been_sent_consistency;
          [assumption
          |apply ptrace_last_pstate in Happ_pre;assumption
          |].
          eexists _. eexists _. exists Happ_pre.

          apply Exists_app. right. subst.
          spec Houtput n.
          clear - Hfinal Houtput Hom n Heqv_state_final.
          simpl in Heqv_state_final, Houtput.
          rewrite Heqv_state_final in Houtput.
          destruct Hfinal as [_ Hfinal].
          simpl in *.
          rewrite Hom in Hfinal.
          match type of Houtput with
          | ?A = ?B => replace A with (Some (Some m)) in Houtput
          end.
          simpl in *.
          match goal with
          |- Exists _ ?new => remember new as newtr
          end.
          clear Heqnewtr.
          destruct (null_dec newtr)
           ; [subst; discriminate Houtput|].
          apply exists_last in n0.
          destruct n0 as [newtr' [lst Hnewtr]].
          subst newtr.
          apply Exists_exists. exists lst.
          rewrite last_error_is_last in Houtput. simpl in Houtput.
          inversion Houtput. symmetry in H0.
          split; [|assumption].
          apply in_app_iff. right. left. reflexivity.
    }
    destruct
      (trace_is_run SeededXE _ _
        (conj Happ_extend (proj2 Hstate_trace))
      )
      as [eqv_merged_run [Heqv_merged_run [Heqv_merged_run_start Heqv_merged_run_transitions]]].
    exists eqv_merged_run.
    exists Heqv_merged_run.
    exists eqv_state_descriptors.
    specialize
      (vlsm_run_last_final SeededXE (exist _ _ Heqv_merged_run))
      as Hmerged_final.
    simpl in Hmerged_final. simpl in Heqv_merged_run_transitions.
    rewrite Heqv_merged_run_transitions in Hmerged_final.
    spec Hmerged_final; [apply last_not_null|].
    rewrite last_error_is_last in Hmerged_final. simpl in Hmerged_final.
    destruct Hmerged_final as [Hfinal_es Hfinal_om].
    inversion Hfinal_es as [Hfinal_es']. rewrite <- Hfinal_es'.
    inversion Hfinal_om as [Hfinal_om']. rewrite <- Hfinal_om'.
    assert (Hnext_state_descriptors : not_equivocating_equivocator_descriptors eqv_state_descriptors es').
    { intro eqv'. spec Heqv_state_descriptors eqv'.
      specialize (Hstate eqv').
      destruct Hstate as [Hstate_size' _].
      destruct (eqv_state_descriptors eqv') as [| eqv_state_descriptors_i' eqv_state_descriptors_f']
      eqn:Heqv_state_descriptors_eqv'
      ; [contradict Heqv_state_descriptors|].
      destruct eqv_state_descriptors_f'; [contradict Heqv_state_descriptors|].
      simpl in Heqv_state_descriptors. simpl.
      subst es'.
      simpl in Hstate_size'.
      rewrite Heqv_state_final in Hstate_size'.
      destruct (decide (eqv' = eqv)).
      - inversion e. subst. rewrite state_update_eq.
        rewrite equivocator_state_update_size.
        lia.
      - rewrite state_update_neq; [|assumption].
        lia.
    }
    exists Hnext_state_descriptors.
    match type of H0 with
    | state_update _ _ _ ?e = _ => remember e as esu
    end.
    match type of Heqesu with
    | context [equivocator_state_update _ ?l _ _] => remember l as lst
    end.
    assert (Hesu_size : projT1 esu = projT1 lst)
      by (subst; apply equivocator_state_update_size).
    assert
      (Hproject :
        equivocators_state_project eqv_state_descriptors es' =
        state_update IM (fst (final state_run)) (eqv) si'
      ).
    {
      subst es'.
      apply functional_extensionality_dep_good.
      intro i.
      unfold equivocators_state_project.
      rewrite equivocators_state_project_state_update_eqv.
      rewrite Heqv_state_descriptors_eqv.
      destruct (le_lt_dec (S (projT1 esu)) eqv_state_descriptors_i)
      ; [subst; rewrite equivocator_state_update_size in l; lia|].
      f_equal.
      - specialize
        (replayed_trace_from_full_replay_state_project IM Hbs _ finite_index seed
          (fst (final eqv_state_run)) (start eqv_msg_run)
          _ Hmsg_trace eqv_state_descriptors
        ) as Hproject.
        spec Hproject
        ; [apply not_equivocating_equivocator_descriptors_proper; assumption|].
        destruct Hproject as [_ Hproject].
        simpl in Hproject.
        rewrite Hproject.
        simpl.
        rewrite <- Hstate_final.
        assumption.
      - clear - Heqesu.
        subst.
        simpl.
        rewrite eq_dec_if_true; [reflexivity|].
        apply of_nat_ext.
    }
    repeat split
    ; [
      | apply Hproject
      | simpl in *; rewrite Heqv_merged_run_start; rewrite Hstate_start_project; reflexivity].
    rewrite Heqv_merged_run_transitions.
    rewrite <- app_assoc.
    unfold equivocators_trace_project.
    unfold Projections.equivocators_trace_project.
    rewrite fold_right_app.
    rewrite fold_right_app.
    unfold fold_right at 3.
    match goal with
    |- fold_right _ (fold_right _ ?l1 _) _ = _ => remember l1 as last_prj
    end.
    match goal with
    |- context [ts ++ ?l] => remember l as last_item
    end.
    assert (last_prj = Some (last_item, eqv_state_descriptors)).
    { subst last_prj. subst last_item.
      unfold equivocators_trace_project_folder.
      subst el.
      unfold_equivocators_transition_item_project.
      simpl in Hproject.
      rewrite <- Hproject.
      rewrite Heqv_state_descriptors_eqv.
      unfold equivocator_vlsm_transition_item_project.
      rewrite <- H0.
      rewrite state_update_eq.
      destruct esu as (n_esu, s_esu) eqn:Hesu.
      destruct (le_lt_dec (S n_esu) eqv_state_descriptors_i)
      ; [simpl in *; subst; lia|].
      rewrite eq_dec_if_true by reflexivity.
      simpl.
      repeat f_equal.
      apply equivocator_descriptors_update_id.
      assumption.
    }
    rewrite H.
    assert (equivocators_trace_project eqv_state_descriptors emsg_tr = Some ([], eqv_state_descriptors)).
    {
      subst emsg_tr.
      apply equivocators_trace_project_skip_full_replay_trace_full. assumption.
    }
    specialize
      (equivocators_trace_project_folder_additive IM
        _ last_item _ _ _ H1
      ) as Hmsg_tr.
    simpl in Hmsg_tr.
    match goal with
    |- fold_right _ ?r _ = _ => replace r with (Some (last_item, eqv_state_descriptors))
    end.
    clear Hmsg_tr.
    specialize
      (equivocators_trace_project_folder_additive IM
        _ last_item _ _ _ Hstate_project
      ) as Heqv_state.
    assumption.
Qed.

Lemma seeded_equivocators_protocol_trace_project_rev
  (isX : composite_state IM)
  (trX : list (composite_transition_item IM))
  (HtrX : finite_protocol_trace SeededX isX trX)
  : exists
    (is : composite_state equivocator_IM)
    (tr : list (composite_transition_item equivocator_IM))
    (Htr : finite_protocol_trace SeededXE is tr)
    (eqv_descriptors : equivocator_descriptors)
    (Hproject : equivocators_trace_project eqv_descriptors tr = Some (trX, zero_descriptor _)),
    equivocators_state_project (zero_descriptor _) is = isX.
Proof.
  destruct (trace_is_run SeededX _ _ HtrX) as [runX [HrunX [_HstartX _HtrX]]].
  subst.
  destruct
    (equivocators_protocol_vlsm_run_project
      _ HrunX
    )
    as [run [Hrun [descriptors [Hproper [Hproject [Hfinal_state [Hfinal_msg Hstart]]]]]]].
  exists (start run).
  exists (transitions run).
  specialize (run_is_trace SeededXE (exist _ _ Hrun)) as Htr.
  simpl in Htr.
  exists Htr.
  exists descriptors.
  exists Hproject.
  exact Hstart.
Qed.

End all_equivocating.

Lemma equivocators_protocol_trace_project_rev
  {message : Type}
  {index : Type}
  {IndEqDec : EqDecision index}
  {i0 : Inhabited index}
  (IM : index -> VLSM message)
  (X := free_composite_vlsm IM)
  (isX : vstate X)
  (trX : list (vtransition_item X))
  (HtrX : finite_protocol_trace X isX trX)
  {index_listing : list index}
  (finite_index : Listing index_listing)
  (Hbs : forall i : index, has_been_sent_capability (IM i))
  (equivocators_no_equivocations_vlsm := equivocators_no_equivocations_vlsm IM Hbs finite_index)
  : exists
    (is : vstate equivocators_no_equivocations_vlsm)
    (tr : list (composite_transition_item (equivocator_IM IM)))
    (Htr : finite_protocol_trace equivocators_no_equivocations_vlsm is tr)
    (eqv_descriptors : equivocator_descriptors IM)
    (Hproject : equivocators_trace_project IM eqv_descriptors tr = Some (trX, zero_descriptor _)),
    equivocators_state_project IM (zero_descriptor _) is = isX.
Proof.
  specialize (vlsm_is_pre_loaded_with_False X) as Hincl.
  apply VLSM_eq_incl_iff in Hincl. apply proj1 in Hincl.
  assert (HtrX' : finite_protocol_trace (pre_loaded_vlsm X (fun _ => False)) isX trX).
  {
    revert HtrX.
    apply VLSM_incl_finite_protocol_trace. apply Hincl.
  }
  destruct
    (seeded_equivocators_protocol_trace_project_rev IM Hbs _ finite_index
       _ _ _ HtrX'
    )
    as [is [tr [Htr [descriptors [Hpr_tr Hpr_is]]]]].
  exists is, tr.
  split; [|exists descriptors, Hpr_tr; assumption].
  revert Htr.
  apply VLSM_incl_finite_protocol_trace.
  match goal with
  |- context [projT2 (projT2 ?M)] => apply VLSM_incl_trans with (machine M)
    ; [specialize (vlsm_is_pre_loaded_with_False M) |]
  end.
  - intro Heq. apply VLSM_eq_incl_iff in Heq. apply proj2 in Heq.
    apply Heq.
  - apply basic_VLSM_incl.
    + intros. assumption.
    + intros. apply initial_message_is_protocol. assumption.
    + intros l s om [Hs [Hom [Hv [Hc _]]]].
      repeat split; [assumption|].
      destruct om; [|exact I]. simpl in *.
      apply or_assoc in Hc.
      destruct Hc as [Hc | Hfalse]; [|contradiction].
      assumption.
    + intros; reflexivity.
Qed.
