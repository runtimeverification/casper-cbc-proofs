From Coq Require Import List ListSet FinFun Rdefinitions.
Import ListNotations.

From CasperCBC Require Import
    Lib.Preamble Lib.ListExtras Lib.ListSetExtras Lib.Measurable
    VLSM.Common
    VLSM.Composition
    VLSM.Equivocation
    VLSM.Equivocation.NoEquivocation
    VLSM.Equivocation.FixedSetEquivocation
    VLSM.ProjectionTraces
    .

Section known_equivocators.

Context
  {message : Type}
  {index : Type}
  {IndEqDec : EqDecision index}
  {i0 : Inhabited index}
  (IM : index -> VLSM message)
  (Hbs : forall i : index, has_been_sent_capability (IM i))
  (Hbr : forall i : index, has_been_received_capability (IM i))
  {validator : Type}
  (A : validator -> index)
  (sender : message -> option validator)
  (PreFree := pre_loaded_with_all_messages_vlsm (free_composite_vlsm IM))
  .

Definition trace_witnessing_equivocation_prop  
  (globally_known_equivocators : composite_state IM -> set validator)
  is tr
  (s := finite_trace_last is tr)
  : Prop := 
  forall v, In v (globally_known_equivocators s) <->
    exists (m : message), (sender m = Some v) /\ equivocation_in_trace PreFree m tr.

Class known_equivocators_capability
  (globally_known_equivocators : composite_state IM -> set validator)
  :=
  { known_equivocators_nodup :
    forall s, NoDup (globally_known_equivocators s)
  ; known_equivocators_is_equivocating_tracewise_char :
    forall s v,
      In v (globally_known_equivocators s) <-> is_equivocating_tracewise_alt IM A sender s v
  ; known_equivocators_is_equivocating_tracewise_witness :
    forall s, protocol_state_prop PreFree s ->
    exists is tr, finite_protocol_trace_init_to PreFree is s tr /\
      trace_witnessing_equivocation_prop globally_known_equivocators is tr
  }.

Section known_equivocators_properties.

Context 
  (globally_known_equivocators : composite_state IM -> set validator)
  (Hke : known_equivocators_capability globally_known_equivocators)
  {ValEqDec : EqDecision validator}
  (Hsender_safety : sender_safety_alt_prop IM A sender)
  .

(** Since is_equivocating_tracewise is characterized by the *globally_known_equivocators*
function ([known_equivocators_is_equivocating_tracewise_char]), it becomes
decidable.
*)
Lemma known_equivocators_is_equivocating_tracewise_alt_dec
  : RelDecision (is_equivocating_tracewise_alt IM A sender).
Proof.
  intros s v.
  destruct (in_dec ValEqDec v (globally_known_equivocators s)).
  - left. apply known_equivocators_is_equivocating_tracewise_char. assumption.
  - right. rewrite <- known_equivocators_is_equivocating_tracewise_char. assumption.
Qed.


Lemma known_equivocators_empty_in_initial_state
  (s : composite_state IM)
  (His : composite_initial_state_prop IM s)
  : globally_known_equivocators s = [].
Proof.
  specialize (known_equivocators_is_equivocating_tracewise_char s) as Heqv.
  destruct (globally_known_equivocators s); [reflexivity|].
  specialize (Heqv v). apply proj1 in Heqv.
  spec Heqv. { left. reflexivity. }
  apply initial_state_not_is_equivocating_tracewise with (i1 := i0) (A0 := A) (sender0 := sender) (v0 := v) in His.
  contradiction.
Qed.

Lemma protocol_transition_receiving_no_sender_reflects_known_equivocators l s om s' om'
  (Ht : protocol_transition PreFree l (s, om) (s', om'))
  (Hno_sender : option_bind sender om = None)
  : incl (globally_known_equivocators s') (globally_known_equivocators s).
Proof.
  intro v. setoid_rewrite known_equivocators_is_equivocating_tracewise_char.
  revert Ht Hno_sender v.
  apply transition_receiving_no_sender_reflects_is_equivocating_tracewise.
Qed.

Context
  (Hno_resend : forall i : index, cannot_resend_message_stepwise_prop (IM i))
  .

Lemma initial_state_witnessing_equivocation_prop
  s
  (Hs : composite_initial_state_prop IM s)
  : trace_witnessing_equivocation_prop globally_known_equivocators s [].
Proof.
  specialize (known_equivocators_empty_in_initial_state s Hs) as Hempty.
  intros v.
  unfold finite_trace_last. simpl.
  rewrite Hempty. simpl.
  split; [intro; contradiction|].
  intros [m [_ Hm]].
  elim (no_equivocation_in_empty_trace PreFree m).
  assumption.
Qed.

Lemma known_equivocators_witness_monotonicity
  (is : composite_state IM)
  (tr : list (composite_transition_item IM))
  (l : composite_label IM)
  (om : option message)
  (s' : composite_state IM)
  (om' : option message)
  (item  := {| l := l; input := om; destination := s'; output := om' |})
  (Htr_item : finite_protocol_trace_init_to PreFree is s' (tr ++ [item]))
  (Hwitness : trace_witnessing_equivocation_prop globally_known_equivocators is (tr ++ [item]))
  (s := finite_trace_last is tr)
  : incl (globally_known_equivocators s) (globally_known_equivocators s').
Proof.
  apply finite_protocol_trace_init_to_last in Htr_item as Heq_s'.
  destruct Htr_item as [Htr Hinit].
  apply finite_protocol_trace_from_to_app_split in Htr.
  destruct Htr as [Htr Hitem].
  inversion Hitem. subst f l0 iom oom s0 tl s. clear H3.
  intros v Hv.  simpl in *. rewrite <- H1 in *.
  specialize (Hwitness v). rewrite Heq_s' in Hwitness.
  apply Hwitness.
  apply known_equivocators_is_equivocating_tracewise_char in Hv.
  specialize (Hv _ _ (conj Htr Hinit)).
  destruct Hv as [m [Hm Heqv]].
  exists m. split; [assumption|].
  apply equivocation_in_trace_prefix. assumption.
Qed.

Lemma known_equivocators_witness_last_char
  (is : composite_state IM)
  (tr : list (composite_transition_item IM))
  (l : composite_label IM)
  (om : option message)
  (s' : composite_state IM)
  (om' : option message)
  (item  := {| l := l; input := om; destination := s'; output := om' |})
  (Htr_item : finite_protocol_trace_init_to PreFree is s' (tr ++ [item]))
  (Hwitness : trace_witnessing_equivocation_prop globally_known_equivocators is (tr ++ [item]))
  (s := finite_trace_last is tr)
  : set_eq (globally_known_equivocators s) (globally_known_equivocators s')
    \/
    (exists m, om = Some m /\
     exists v, sender m = Some v /\
     set_eq (globally_known_equivocators s') (set_add decide_eq v (globally_known_equivocators s))
    ).
Proof.
  apply known_equivocators_witness_monotonicity in Hwitness as Hincl
  ; [|assumption].
  apply finite_protocol_trace_init_to_last in Htr_item as Heq_s'.
  destruct Htr_item as [Htr Hinit].
  apply finite_protocol_trace_from_to_app_split in Htr.
  destruct Htr as [Htr Hitem].
  inversion Hitem. subst f l0 iom oom s s0 tl. clear H3.
  simpl in *.
  rewrite <- H1 in *.
  specialize (protocol_transition_receiving_no_sender_reflects_known_equivocators _ _ _ _ _ H7)
    as Hreflect.
  destruct (option_bind sender om) as [v|] eqn:Heq_v
  ;[| left; split; [assumption| apply Hreflect; reflexivity]].
  clear Hreflect.
  destruct om as [m|]; [|inversion Heq_v]. simpl in Heq_v.
  destruct (set_eq_dec (globally_known_equivocators s'0) (globally_known_equivocators s'))
  ; [left;assumption|].
  right. exists m; split; [reflexivity|]. exists v. split; [assumption|].
  assert (Honly_v : forall v', In v' (globally_known_equivocators s') /\ ~ In v' (globally_known_equivocators s'0) -> v' = v).
  { intros v' [Hv' Hnv'].
    inversion Hitem. subst s'1 f l0 iom s oom tl.
    apply known_equivocators_is_equivocating_tracewise_char in Hv'.
    rewrite known_equivocators_is_equivocating_tracewise_char in Hnv'.
    destruct (transition_is_equivocating_tracewise_char IM A sender _ _ _ _ _ _ H9 v' Hv')
      as [H|Hsender]
    ; [contradiction | ].
    simpl in Hsender.
    rewrite Heq_v in Hsender. inversion Hsender. reflexivity.
  }
  assert (Hv : exists v, In v (globally_known_equivocators s') /\ ~ In v (globally_known_equivocators s'0)).
  { apply Exists_exists.
    apply neg_Forall_Exists_neg; [intro; apply in_dec; assumption|].
    intro all. elim n.
    split; [assumption|].
    rewrite Forall_forall in all.
    assumption.
  }
  destruct Hv as [v' Heqv].
  apply Honly_v in Heqv as Heq_v'.
  subst v'.
  split; intros v' Hv'.
  + apply set_add_iff.
  destruct (in_dec decide_eq v' (globally_known_equivocators s'0))
  ; [right; assumption|].
  left. apply Honly_v. split; assumption.
  + destruct Heqv as [Hv Hnv]. apply set_add_iff in Hv'.
    destruct Hv' as [Heq_v' | Hs'0]
    ; [subst v'; assumption|].
    apply Hincl. assumption.
Qed.


Lemma known_equivocators_witness_for_all_times
  is tr
  (Htr : finite_protocol_trace PreFree is tr)
  : forall prefix suffix, prefix ++ suffix = tr -> trace_witnessing_equivocation_prop globally_known_equivocators is prefix.
Proof.
  remember (length tr) as n.
  revert tr Heqn Htr.
  induction n using Wf_nat.lt_wf_ind.
  intros tr Heq_n Htr.
  induction Htr using finite_protocol_trace_rev_ind.
  - intros prefix suffix Htr.
    apply app_eq_nil  in Htr. destruct Htr; subst.
    apply initial_state_witnessing_equivocation_prop. assumption.
  - destruct IHHs as [is [tr [Htr Hprefix]]].
    exists is, (tr ++ [{| l := l; input := om; output := om'; destination := s'|}]).
    assert (Htr_item : finite_protocol_trace_init_to PreFree is s' (tr ++ [{| l := l; input := om; destination := s'; output := om' |}])).
    { split; [|apply Htr].
      apply finite_protocol_trace_from_to_app with s; [apply Htr|].
      apply finite_ptrace_from_to_singleton. assumption.
    }
    split; [assumption|].

  apply finite_protocol_trace_init_to_last in Htr_item as Heq_s'.
  destruct Htr_item as [Htr Hinit].
  apply finite_protocol_trace_from_to_app_split in Htr.
  destruct Htr as [Htr Hitem].
  inversion Hitem. subst f l0 iom oom s tl. clear H3.
  intro v. simpl in *.
  rewrite <- H1 in *.
  split.
  - intros Hs'0. apply known_equivocators_is_equivocating_tracewise_char in Hs'0.
    apply (Hs'0 is tr (conj Htr Hinit)).
  - intros [m [Hsender Heqv]].
    apply equivocation_in_trace_prefix with (suffix := [item]) in Heqv as Heqv'.
    specialize (Hwitness v). rewrite Heq_s' in Hwitness.
    apply proj2 in Hwitness.
    spec Hwitness.  { exists m. split; assumption. }
    specialize (protocol_transition_receiving_None_reflects_known_equivocators l s'0 s' om')
      as Hreflect.
    destruct om as [m'|]
    ; [|apply Hreflect; assumption].
    apply known_equivocators_is_equivocating_tracewise_char in Hwitness.
    apply known_equivocators_is_equivocating_tracewise_char.
    intros is' tr' Htr'.

    assert
      (Htr'_item : finite_protocol_trace_init_to
        (pre_loaded_with_all_messages_vlsm (free_composite_vlsm IM)) is' s'
        (tr' ++ [item])).
    { destruct Htr' as [Htr' Hinit']. split; [|assumption].
      apply finite_protocol_trace_from_to_app with s'0; [assumption|].
      apply finite_ptrace_from_to_singleton.
      assumption.
    }
    specialize (Hwitness _ _ Htr'_item).
(*
    destruct Hwitness as 
  


    destruct Heqv as [prefix [suffix [item0 [Heq_tr_item [Hinput Heqv]]]]].
    destruct_list_last suffix suffix' lst Heq_suffix.
    + apply app_inj_tail in Heq_tr_item. destruct Heq_tr_item; subst prefix item0 suffix.
      simpl in Hinput. subst iom.
      apply known_equivocators_is_equivocating_tracewise_char.
      apply (is_equivocating_tracewise_alt_iff IM Hbs); [assumption|].
      apply is_equivocating_statewise_implies_is_equivocating_tracewise with (has_been_received_capabilities := Hbr).
      destruct l as (i, li).
      exists i.
      exists m. split; [assumption|].
      specialize (Hno_resend i).
      specialize (protocol_transition_received_not_sent (IM i) Hno_resend li (s i) m (s' i) oom)
        as Hneq_oom.
      spec Hneq_oom.
      { simpl in Ht. destruct (vtransition (IM i) li (s i, Some m)) as (si', om') eqn:Hti.
        inversion Ht. subst s' om'. rewrite state_update_eq.
        repeat split; [| apply any_message_is_protocol_in_preloaded|assumption|assumption].
        apply preloaded_finite_ptrace_init_to_projection with (j := i),proj1
          , finite_protocol_trace_from_to_last_pstate
          in Htr.
        assumption.
      }
      assert (Hbr_m : has_been_received (IM i) (s' i) m).
      { clear -Htr_item.
        apply preloaded_finite_ptrace_init_to_projection with (j := i) in Htr_item as Htri.
        apply proj1 in Htri as Hlsti.
        apply finite_protocol_trace_from_to_last_pstate in Hlsti.
        apply proper_received; [assumption|].
        apply has_been_received_consistency; [apply Hbr|assumption|].
        exists _,_,Htri.
        rewrite finite_trace_projection_list_app.
        apply Exists_app. right.
        simpl. destruct (decide (i = i)); [|congruence].
        apply Exists_cons_hd. 
        reflexivity.
      }
      split; [|assumption].

      clear -Heqv Hneq_oom Htr_item.
      apply preloaded_finite_ptrace_init_to_projection with (j := A v) in Htr_item as Htrv.
      apply proj1 in Htrv as Hlstv.
      apply finite_protocol_trace_from_to_last_pstate in Hlstv.
      intros Hbs_m.
      apply proper_sent in Hbs_m; [|assumption].
      specialize (Hbs_m _ _ Htrv).
      rewrite finite_trace_projection_list_app in Hbs_m.
      apply Exists_app in Hbs_m.
      destruct Hbs_m as [Hbs_m | Hitem_m].
      * elim Heqv. clear Heqv. apply Exists_exists in Hbs_m.
        destruct Hbs_m as [sitemv [Hsitemv Houtput]].
        apply (finite_trace_projection_list_in_rev IM) in Hsitemv.
        destruct Hsitemv as [sitem [Heq_output [_ [_ [_ [_ Hsitem]]]]]].
        simpl in Houtput.
        rewrite <- Heq_output in Houtput.
        apply in_map_iff. exists sitem. split; assumption. 
      * simpl in Hitem_m.
        destruct (decide (A v = i)); [|inversion Hitem_m].
        apply Exists_cons in Hitem_m. simpl in Hitem_m.
        destruct Hitem_m as [H | Hitem_m]; [congruence|inversion Hitem_m].
    + replace (prefix ++ item0 :: suffix' ++ [lst]) with ((prefix ++ ([item0] ++ suffix')) ++ [lst])
        in Heq_tr_item
        by (rewrite <- !app_assoc; reflexivity). 
      apply app_inj_tail in Heq_tr_item.
      destruct Heq_tr_item; subst lst.
      specialize (Hwitness v).
      apply proj2 in Hwitness.
      spec Hwitness.
      { exists m. split; [assumption|]. exists prefix, suffix', item0.
        repeat split; assumption.
      }
      rewrite Hlst in Hwitness.
      revert Hwitness.
      apply (protocol_transition_preserves_known_equivocators l s iom s' oom).
      repeat split; [| apply any_message_is_protocol_in_preloaded|assumption|assumption].
      apply proj1, finite_protocol_trace_from_to_last_pstate in Htr.
      assumption.
Qed.
*)
Admitted.

Context
  {ValMeasurable : Measurable validator}
  {EqDecision : EqDecision validator}
  {threshold_V : ReachableThreshold validator}
  {validator_listing : list validator}
  (finite_validator : Listing validator_listing)
  .

Local Instance known_equivocators_basic_equivocation : basic_equivocation (composite_state IM) validator
  := equivocation_dec_tracewise IM A sender finite_validator known_equivocators_is_equivocating_tracewise_alt_dec .

Lemma globally_known_equivocators_equivocating_validators
  : forall s, set_eq (equivocating_validators s) (globally_known_equivocators s).
Proof.
  intro s.
  unfold equivocating_validators, is_equivocating, set_eq, incl.
  simpl.
  setoid_rewrite filter_In. setoid_rewrite bool_decide_eq_true.
  setoid_rewrite known_equivocators_is_equivocating_tracewise_char.
  split; intros; [apply proj2 in H; assumption|].
  split; [apply finite_validator| assumption].
Qed.


Lemma eq_globally_known_equivocators_equivocation_fault
  : forall s1 s2,
    set_eq (globally_known_equivocators s1) (globally_known_equivocators s2) ->
    equivocation_fault s1 = equivocation_fault s2.
Proof.
  intros.
  apply
    (set_eq_nodup_sum_weight_eq
      (equivocating_validators s1)
      (equivocating_validators s2)
    ).
  - apply NoDup_filter. apply state_validators_nodup. 
  - apply NoDup_filter. apply state_validators_nodup. 
  - apply (set_eq_tran (equivocating_validators s1) (globally_known_equivocators s1) (equivocating_validators s2))
    ; [apply globally_known_equivocators_equivocating_validators|].
    apply (set_eq_tran (globally_known_equivocators s1) (globally_known_equivocators s2) (equivocating_validators s2))
    ; [assumption|].
    apply set_eq_comm. apply globally_known_equivocators_equivocating_validators.
Qed.

Lemma incl_globally_known_equivocators_equivocation_fault
  : forall s1 s2,
    incl (globally_known_equivocators s1) (globally_known_equivocators s2) ->
    (equivocation_fault s1 <= equivocation_fault s2)%R.
Proof.
  intros.
  apply
    (sum_weights_incl
      (equivocating_validators s1)
      (equivocating_validators s2)
    ).
  - apply NoDup_filter. apply state_validators_nodup. 
  - apply NoDup_filter. apply state_validators_nodup. 
  - specialize (globally_known_equivocators_equivocating_validators s1) as Hs1.
    specialize (globally_known_equivocators_equivocating_validators s2) as Hs2.
    apply proj1 in Hs1. apply proj2 in Hs2.
    specialize (incl_tran H Hs2) as Hs12.
    revert Hs1 Hs12. apply incl_tran.
Qed.

Lemma initial_state_equivocators_weight
  (s : composite_state IM)
  (Hs : composite_initial_state_prop IM s)
  : equivocation_fault s = 0%R.
Proof.
  apply known_equivocators_empty_in_initial_state in Hs.
  assert (sum_weights (globally_known_equivocators s) = 0%R).
  { rewrite Hs. reflexivity. }
  rewrite <- H.
  apply set_eq_nodup_sum_weight_eq.
  - apply NoDup_filter. apply state_validators_nodup.
  - apply known_equivocators_nodup.
  - apply globally_known_equivocators_equivocating_validators.
Qed.

Lemma composite_transition_None_equivocators_weight
  l s s' om'
  (Ht : protocol_transition (pre_loaded_with_all_messages_vlsm (free_composite_vlsm IM)) l (s, None) (s', om'))
  : (equivocation_fault s' <= equivocation_fault s)%R.
Proof.
  specialize (protocol_transition_receiving_None_reflects_known_equivocators _ _ _ _ Ht) as Heqv.
  revert Heqv.
  apply incl_globally_known_equivocators_equivocation_fault.
Qed.

End known_equivocators_properties.
End known_equivocators.

Section known_equivocators_fixed_set.

Context
  {message : Type}
  {index : Type}
  {IndEqDec : EqDecision index}
  {index_listing : list index}
  (finite_index : Listing index_listing)
  (IM : index -> VLSM message)
  (Hbs : forall i, has_been_sent_capability (IM i))
  (Hbr : forall i, has_been_received_capability (IM i))
  (Hbo := fun i => has_been_observed_capability_from_sent_received (IM i))
  (i0 : Inhabited index)
  (Free := free_composite_vlsm IM)
  (sender : message -> option index)
  (globally_known_equivocators : composite_state IM -> set index)
  (Hke : known_equivocators_capability IM (fun i => i) sender globally_known_equivocators)
  .


Definition known_equivocators_fixed_equivocation_constraint
  (s : composite_state IM)
  (ke := globally_known_equivocators s)
  : composite_label IM -> composite_state IM * option message -> Prop
  :=
  match null_dec ke with
  | left _ => composite_no_equivocations IM Hbs
  | right n => fixed_equivocation_constraint IM Hbs Hbr ke n finite_index
  end.

Lemma known_equivocators_fixed_equivocation_characterization
  : forall s,
    protocol_state_prop Free s ->
    protocol_state_prop
      (composite_vlsm IM (known_equivocators_fixed_equivocation_constraint s)) s.
Proof.
  intros s Hs.
  specialize
    (known_equivocators_is_equivocating_tracewise_witness IM (fun i => i) sender s)
    as Hex.
  spec Hex.
  { revert Hs. apply VLSM_incl_protocol_state.
    apply vlsm_incl_pre_loaded_with_all_messages_vlsm.
  }
  destruct Hex as [is [tr [Htr Heqv]]].
  cut (finite_protocol_trace_from_to (composite_vlsm IM (known_equivocators_fixed_equivocation_constraint s)) is s tr).
  { intro Htr'. apply finite_protocol_trace_from_to_last_pstate in Htr'.
    assumption.
  }
  induction Htr using @finite_protocol_trace_init_to_rev_ind.
  - apply (finite_ptrace_from_to_empty (composite_vlsm IM (known_equivocators_fixed_equivocation_constraint si))).
    apply initial_is_protocol. assumption.
Admitted.

End known_equivocators_fixed_set.