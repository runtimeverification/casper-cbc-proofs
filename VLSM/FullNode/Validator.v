Require Import Bool List ListSet.

Import ListNotations.

From CasperCBC
  Require Import
    Lib.Preamble
    Lib.ListExtras
    Lib.ListSetExtras
    VLSM.Common
    CBC.Common
    CBC.Equivocation
    Validator.State
    Validator.Equivocation
    VLSM.Equivocation
    VLSM.ObservableEquivocation
    VLSM.FullNode.Client
    .

Section CompositeValidator.

  Context
    {C V : Type}
    {about_C : StrictlyComparable C}
    {about_V : StrictlyComparable V}
    {Hmeasurable : Measurable V}
    {Hrt : ReachableThreshold V}
    {Hestimator : Estimator (state C V) C}
    (eq_V := @strictly_comparable_eq_dec _ about_V)
    (message := State.message C V)
    (message_preceeds_dec := validator_message_preceeds_dec C V)
    .
  Existing Instance eq_V.
  Existing Instance message_preceeds_dec.


  Definition full_node_validator_observable_messages_fn
    (s : state C V)
    (v : V)
    : set message
    :=
    filter (fun m => bool_decide (sender m = v)) (get_message_set s).

    Definition full_node_validator_state_validators
    (s : state C V)
    : set V
    :=
    full_node_client_state_validators (get_message_set s).

  Instance full_node_validator_observable_messages
    : observable_events (state C V) message
    :=
    state_observable_events_instance (state C V) V message _
      full_node_validator_observable_messages_fn full_node_validator_state_validators.

  Lemma full_node_validator_has_been_observed_iff
    (s : state C V)
    (m : message)
    : has_been_observed s m <-> In m (get_message_set s).
  Proof.
    simpl.
    unfold observable_events_has_been_observed.
    unfold state_observable_events_fn.
    split; intro H.
    - apply union_fold in H.
      destruct H as [needle [Hm Hneedle]] .
      apply in_map_iff in Hneedle.
      destruct Hneedle as [v0 [Hneedle Hv0]].
      subst needle.
      apply filter_In in Hm.
      destruct Hm as [Hm Hv0eq].
      assumption.
    - apply union_fold.
      exists (full_node_validator_observable_messages_fn s (sender m)).
      split.
      * apply filter_In.
        split; [assumption|].
        apply bool_decide_eq_true. reflexivity.
      * apply in_map_iff.
        exists (sender m). split; [intuition|].
        apply set_map_exists.
        exists m. split; [assumption|reflexivity].
  Qed.

  Instance full_node_validator_observation_based_equivocation_evidence
    : observation_based_equivocation_evidence (state C V) V message _ decide_eq _ message_preceeds_dec full_node_message_subject_of_observation
    :=
    observable_events_equivocation_evidence _ _ _ _
      full_node_validator_observable_messages_fn full_node_validator_state_validators
      _ message_preceeds_dec full_node_message_subject_of_observation.

  Instance full_node_validator_observation_based_equivocation_evidence_dec
    : RelDecision (@equivocation_evidence _ _ _ _ _ _ _ _ full_node_validator_observation_based_equivocation_evidence)
    :=
    observable_events_equivocation_evidence_dec _ _ _ _
      full_node_validator_observable_messages_fn full_node_validator_state_validators
      _ _ message_preceeds_dec full_node_message_subject_of_observation.

  Lemma full_node_validator_state_validators_nodup
    (s : state C V)
    : NoDup (full_node_validator_state_validators s).
  Proof.
    apply set_map_nodup.
  Qed.

  Definition validator_basic_equivocation
    : basic_equivocation (state C V) V
    := @basic_observable_equivocation (state C V) V message
        message_eq _ (validator_message_preceeds_dec C V) full_node_validator_observable_messages full_node_message_subject_of_observation full_node_validator_observation_based_equivocation_evidence _ _ _  full_node_validator_state_validators full_node_validator_state_validators_nodup.

  (** * Full-node validator VLSM instance

  Here we define a VLSM for a full-node validator identifying itself as
  <<v>> when sending messages.

  The validator and incorporates messages (sent by other validators), and
  creates and sends new messages proposing consensus values estimated based
  on its current state, signing them with its name and current state.

  Unlike the client, no equivocation check is done within the validator upon
  receiving a new message.
  *)
  Definition labelv : Type := option C.

  Definition vtransitionv
    (v : V)
    (l : labelv)
    (som : state C V * option message)
    : state C V * option message
    :=
    let (s, om) := som in
    let (msgs, final) := s in
    match l with
    | None => match om with
             | None => som
             | Some msg => pair (pair (set_add decide_eq msg msgs) final) None
           end
    | Some c =>
      let msg := Msg c v (make_justification s) in
      pair (pair (set_add decide_eq msg msgs) (Some msg)) (Some msg)
    end.

  Lemma vtransitionv_inv_out
    (v : V)
    (l : labelv)
    (s s' : state C V)
    (om : option message)
    (m' : message)
    (Ht : vtransitionv v l (s, om) = pair s' (Some m'))
    : s' = pair (set_add decide_eq m' (get_message_set s)) (Some m')
    /\ get_justification m' = make_justification s
    /\ sender m' = v
    /\ exists (c : C), l = Some c.
  Proof.
    unfold vtransitionv in Ht. destruct s as (msgs, final).
    destruct l as [c|].
    - inversion Ht. repeat split; try reflexivity. exists c. reflexivity.
    - destruct om as [msg|]; inversion Ht.
  Qed.

  Definition valid_validator
    (l : labelv)
    (som : state C V * option message)
    : Prop
    :=
    let (s, om) := som in
    match l, om with
    | None, None => True
    | None, Some msg =>
      ~In msg (get_message_set s)
      /\
      incl (get_message_set (unmake_justification (get_justification msg))) (get_message_set s)
    | Some c, None =>
      @estimator (state C V) C Hestimator s c
    | _,_ => False
    end.

  Instance VLSM_type_full_validator : VLSM_type message :=
    { state := state C V
    ; label := labelv
    }.

  Definition initial_state_prop
    (s : state C V)
    : Prop
    :=
    s = pair [] None.

  Definition state0 : {s | initial_state_prop s} :=
    exist _ (pair [] None) eq_refl.

  Definition initial_message_prop (m : message) : Prop := False.

  Instance LSM_full_validator : VLSM_sign VLSM_type_full_validator :=
    { initial_state_prop := initial_state_prop
    ; initial_message_prop := initial_message_prop
    ; s0 := state0
    ; m0 := State.message0
    ; l0 := None
    }.

  Definition VLSM_full_validator_machine (v : V) : VLSM_class LSM_full_validator :=
    {| transition := vtransitionv v
     ; valid := valid_validator
    |}.

  Definition VLSM_full_validator (v : V) : VLSM message :=
    mk_vlsm (VLSM_full_validator_machine v).

  Existing Instance observable_messages.

  Definition full_node_validator_vlsm_observable_messages
    (v : V)
    : vlsm_observable_events (VLSM_full_validator v) full_node_message_subject_of_observation.
  Proof.
    split; intros.
    - replace s with (@nil message, @None message) in He by assumption.
      inversion He.
    - inversion His.
    - destruct som as (s, om). destruct s as (msgs, final).
      destruct l as [c|]; [|destruct om as [msg|]]; inversion Ht.
      subst. clear Ht.
      match type of H with
      | context[Msg _ _ ?s] => remember s as j
      end.
      apply full_node_validator_has_been_observed_iff.
      simpl.
      apply set_add_iff.
      destruct H as [Hmsg | Hj]; intuition.
      right.
      apply in_unmake_justification in Hj.
      apply in_make_message_set.
      subst.
      destruct final; assumption.
  Qed.

Section proper_sent_received.
  Context
    (v : V)
    (vlsm := VLSM_full_validator v)
    (bvlsm := pre_loaded_with_all_messages_vlsm vlsm)
    .

  Lemma validator_protocol_state_nodup
    (s : state C V)
    (Hs : protocol_state_prop bvlsm s)
    : NoDup (get_message_set s).
  Proof.
    induction Hs using protocol_state_prop_ind.
    - inversion Hs. constructor.
    - destruct Ht as [_ Ht].
      simpl in Ht. unfold vtransition in Ht. simpl in Ht.
      destruct s as (msgs, final).
      destruct l as [c|].
      + apply pair_equal_spec in Ht. destruct Ht as [Hs' _].
        subst s'. apply set_add_nodup. assumption.
      + destruct om as [msg|]; inversion Ht.
        * apply set_add_nodup. assumption.
        * assumption.
  Qed.

  Lemma vtransition_inv_out
    (l : label)
    (s s' : state C V)
    (om : option message)
    (m' : message)
    (Ht : vtransition bvlsm l (s, om) = pair s' (Some m'))
    : s' = pair (set_add decide_eq m' (get_message_set s)) (Some m')
    /\ get_justification m' = make_justification s
    /\ sender m' = v
    /\ exists (c : C), l = Some c.
  Proof.
    apply vtransitionv_inv_out in Ht. assumption.
  Qed.

  Lemma protocol_transition_inv_out
    (l : label)
    (s s' : state C V)
    (om : option message)
    (m' : message)
    (Ht : protocol_transition bvlsm l (s, om) (s', Some m'))
    : s' = pair (set_add decide_eq m' (get_message_set s)) (Some m')
    /\ get_justification m' = make_justification s
    /\ sender m' = v
    /\ exists (c : C), l = Some c.
  Proof.
    destruct Ht as [_ Ht]. apply vtransition_inv_out in Ht. assumption.
  Qed.

  Lemma protocol_transition_inv_in
    (l : label)
    (s s' : state C V)
    (m : message)
    (om' : option message)
    (Ht : protocol_transition bvlsm l (s, Some m) (s', om'))
    : s' = pair (set_add decide_eq m (get_message_set s)) (last_sent s)
    /\ om' = None
    /\ ~In m (get_message_set s)
    /\ incl
        (unmake_message_set (justification_message_set (get_justification m)))
        (get_message_set s)
    /\ protocol_state_prop bvlsm s
    /\ protocol_message_prop bvlsm m
    /\ protocol_state_prop bvlsm s'.
  Proof.
    pose Ht as Hs'.
    apply protocol_transition_destination in Hs'.
    destruct Ht as [[Hs [Hm Hv]] Ht].
    simpl in Ht. unfold vtransition in Ht. simpl in Ht.
    simpl in Hv. unfold vvalid in Hv. simpl in Hv.
    destruct l as [c|]; try inversion Hv.
    destruct s as (msgs, final).
    inversion Ht. subst. simpl.
    repeat split; try reflexivity; assumption.
  Qed.

  Lemma last_sent_in_messages
    (s : state C V)
    (Hs : protocol_state_prop bvlsm s)
    (lst : message)
    (Hlst : last_sent s = Some lst)
    : In lst (get_message_set s).
  Proof.
    induction Hs using protocol_state_prop_ind.
    - inversion Hs. subst s. inversion Hlst.
    - destruct Ht as [_ Ht]. simpl in Ht. unfold vtransition in Ht. simpl in Ht.
      destruct s as (msgs, final).
      destruct l as [c|].
      + inversion Ht; subst. destruct final as [m|]; simpl in *
        ; inversion Hlst; apply set_add_iff; left; reflexivity.
      + destruct om as [msg|]; inversion Ht; subst
        ; simpl in Hlst; subst final
        ; specialize (IHHs eq_refl); simpl; [|assumption].
        apply set_add_iff. right. assumption.
  Qed.

  Lemma last_sent_justification_protocol
    (s : state C V)
    (Hs : protocol_state_prop bvlsm s)
    (lst : message)
    (Hlst : last_sent s = Some lst)
    (j := get_justification lst)
    : exists sj : state C V, protocol_state_prop bvlsm sj /\ make_justification sj = j.
  Proof.
    subst j.
    induction Hs using protocol_state_prop_ind.
    - inversion Hs. subst s. inversion Hlst.
    - destruct Ht as [[Hps [Hom Hv]] Ht].
       simpl in Ht. unfold vtransition in Ht. simpl in Ht.
      destruct s as (msgs, final).
      destruct l as [c|].
      + inversion Ht; subst.
        exists (msgs, final).
        destruct final as [m|]; simpl in *; inversion Hlst; simpl
        ; split; try assumption; reflexivity.
      + destruct om as [msg|]; inversion Ht; subst
        ; simpl in Hlst; subst final
        ; specialize (IHHs eq_refl); simpl; assumption.
  Qed.

  Lemma in_protocol_state
    (s : state C V)
    (Hs : protocol_state_prop bvlsm s)
    (m : message)
    (Hm : In m (get_message_set s))
    : incl (unmake_message_set (justification_message_set (get_justification m))) (get_message_set s).
  Proof.
    induction Hs using protocol_state_prop_ind.
    - inversion Hs. subst s. inversion Hm.
    - destruct Ht as [[Hps [Hom Hv]] Ht].
      simpl in Ht. unfold vtransition in Ht. simpl in Ht.
      simpl in Hv. unfold vvalid in Hv. simpl in Hv.
      destruct s as (msgs, final).
      destruct l as [c|].
      + inversion Ht; subst s' om';clear Ht;simpl in * |- *.
        apply set_add_iff in Hm.
        intros msg Hmsg; apply set_add_iff; right.
        destruct Hm;[|apply IHHs;assumption].
        subst m; clear -Hmsg;simpl in Hmsg.
        apply make_unmake_message_set_eq.
        destruct final;assumption.
      + destruct om as [msg|]; inversion Ht; subst; clear Ht
        ; simpl in IHHs; simpl in Hv; simpl
        ; [|apply IHHs; assumption].
        destruct Hv as [Hnmsg Hv].
        apply set_add_iff in Hm.
        destruct Hm as [Heqm | Hm].
        * subst m.
          apply incl_tran with msgs; try assumption.
          intros x Hx; apply set_add_iff. right. assumption.
        * specialize (IHHs Hm).
          apply incl_tran with msgs; try assumption.
          intros x Hx; apply set_add_iff. right. assumption.
  Qed.

  Lemma has_been_sent_in_futures
    (s1 s2 : state C V)
    (Hs : in_futures bvlsm s1 s2)
    : incl (State.sent_messages s1) (State.sent_messages s2).
  Proof.
    unfold in_futures in Hs. destruct Hs as [tr [Htr Hs2]].
    generalize dependent s2. generalize dependent s1.
    induction tr; intros.
    - simpl in Hs2. subst s2. apply incl_refl.
    - inversion Htr. subst a s' tl.
      rewrite map_cons in Hs2. rewrite unroll_last in Hs2. simpl in Hs2.
      specialize (IHtr s H2 s2 Hs2).
      apply incl_tran with (State.sent_messages s); try assumption.
      clear -H3.
      destruct H3 as [_ Ht]. simpl in Ht. unfold vtransition in Ht. simpl in Ht.
      destruct s1 as (msgs, final).
      destruct l as [c|].
      + inversion Ht; subst; clear Ht. unfold State.sent_messages. simpl.
        destruct final as [m|]; subst; simpl in *; try apply incl_nil_l.
        destruct m as (c0, v0, j0). intros m Hm.
        apply set_add_iff. right. assumption.
      + destruct iom as [msg|]; inversion Ht; apply incl_refl.
  Qed.

  Lemma get_messages_in_futures
    (s1 s2 : state C V)
    (Hs : in_futures bvlsm s1 s2)
    : incl (get_message_set s1) (get_message_set s2).
  Proof.
    unfold in_futures in Hs. destruct Hs as [tr [Htr Hs2]].
    generalize dependent s2. generalize dependent s1.
    induction tr; intros.
    - simpl in Hs2. subst s2. apply incl_refl.
    - inversion Htr. subst a s' tl.
      rewrite map_cons in Hs2. rewrite unroll_last in Hs2. simpl in Hs2.
      specialize (IHtr s H2 s2 Hs2).
      apply incl_tran with (get_message_set s); try assumption.
      clear -H3.
      destruct H3 as [_ Ht]. simpl in Ht. unfold vtransition in Ht. simpl in Ht.
      destruct s1 as (msgs, final).
      destruct l as [c|].
      + inversion Ht; subst; clear Ht. unfold get_message_set. simpl.
        intros m Hm. apply set_add_iff. right. assumption.
      + destruct iom as [msg|]; inversion Ht; try apply incl_refl.
        simpl. intros m Hm. apply set_add_iff. right. assumption.
  Qed.

  Lemma has_been_sent_protocol_transition
    (l : vlabel bvlsm)
    (s1 s2 : state C V)
    (iom oom : option message)
    (Hpt : protocol_transition bvlsm l (s1, iom) (s2, oom))
    (m : message)
    (Hs1 : ~ In m (State.sent_messages s1))
    : In m (State.sent_messages s2) <-> oom = Some m.
  Proof.
    destruct Hpt as [_ Ht]. simpl in Ht.
    unfold vtransition in Ht. simpl in Ht.
    destruct s1 as (msgs, final).
    destruct l as [c|]; inversion Ht; subst.
    + unfold State.sent_messages. simpl.  split; intro H.
      * apply set_add_iff in H.
        destruct H as [Heq | H]; subst; try reflexivity.
        elim Hs1. unfold State.sent_messages. simpl.
        destruct final; simpl in *; assumption.
      * inversion H; subst.
        apply set_add_iff. left. reflexivity.
    + destruct iom as [msg|]; inversion H0; subst; split; intro H
      ; try discriminate H
      ; elim Hs1
      ; assumption.
  Qed.

  Lemma has_been_sent_in_trace
    (s : state C V)
    (m: message)
    (is : state C V)
    (tr: list transition_item)
    (Htr: finite_protocol_trace bvlsm is tr)
    (item: transition_item)
    (Hitem: In item tr)
    (Hm: output item = Some m)
    (Hs: last (map destination tr) is = s)
    : In m (State.sent_messages s).
  Proof.
    apply in_split in Hitem.
    destruct Hitem as [l1 [l2 Hitem]]. subst tr.
    destruct Htr as [Htr Hinit].
    pose (finite_protocol_trace_from_app_iff bvlsm is l1 (item :: l2)) as Htr_app.
    simpl in Htr_app. destruct Htr_app as [_ Htr_app].
    specialize (Htr_app Htr).
    clear Htr. destruct Htr_app as [_ Htr].
    inversion Htr. subst tl item. simpl in Hm. subst oom.
    assert (Hm0 : In m (State.sent_messages s0)).
    { clear -H3. destruct H3 as [_ Ht].
      simpl in Ht. unfold vtransition in Ht. simpl in Ht.
      destruct
        (@last (state C V)
        (@map (@transition_item message VLSM_type_full_validator)
           (state C V) (@destination message VLSM_type_full_validator) l1)
        is)
        as (msgs, final).
      destruct l as [c|].
      - inversion Ht; subst; clear Ht.
        unfold State.sent_messages. simpl.
        apply set_add_iff. left. reflexivity.
      - destruct iom as [msg|]; inversion Ht.
    }
    assert (Hs0 : in_futures bvlsm s0 s).
    { exists l2. split; try assumption.
      rewrite map_app in Hs. rewrite map_cons in Hs.
      rewrite last_app in Hs. rewrite unroll_last in Hs.
      simpl in Hs.
      assumption.
    }
    apply has_been_sent_in_futures with s0; assumption.
  Qed.

  Lemma has_been_sent_witness
    (s: state C V)
    (m: message)
    (Horacle: In m (State.sent_messages s))
    (start: Common.state)
    (Hstart: ~In m (State.sent_messages start))
    (prefix: list transition_item)
    (Hprefix: finite_protocol_trace_from (pre_loaded_with_all_messages_vlsm vlsm) start prefix)
    (Hlast: last (map destination prefix) start = s)
    : exists item : transition_item, In item prefix /\ output item = Some m.
  Proof.
    generalize dependent start.
    induction prefix; intros.
    + inversion Hprefix; subst.
      simpl in Horacle. elim Hstart. assumption.
    + rewrite map_cons in Hlast. rewrite unroll_last in Hlast.
      inversion Hprefix; subst. simpl in *.
      destruct oom as [om|]; try destruct (decide (om = m)); try subst om.
      * exists (@Build_transition_item message VLSM_type_full_validator l iom s0 (@Some message m)).
        split; try reflexivity.
        left. reflexivity.
      * assert (Hs0 : ~In m (State.sent_messages s0)).
        { intro Hbs.
          apply (has_been_sent_protocol_transition _ _ _ _ _ H3 _ Hstart) in Hbs.
          elim n.
          inversion Hbs. reflexivity.
        }
        specialize (IHprefix s0 Hs0 H2 eq_refl).
        destruct IHprefix as [x [Hx Hm]].
        exists x.
        split; try assumption.
        right. assumption.
      * assert (Hs0 : ~In m (State.sent_messages s0)).
        { intro Hbs.
          apply (has_been_sent_protocol_transition _ _ _ _ _ H3 _ Hstart) in Hbs.
          discriminate Hbs.
        }
        specialize (IHprefix s0 Hs0 H2 eq_refl).
        destruct IHprefix as [x [Hx Hm]].
        exists x.
        split; try assumption.
        right. assumption.
  Qed.

  Lemma has_been_sent_in_trace_rev
    (s: state C V)
    (m: message)
    (Horacle: In m (State.sent_messages s))
    (is : state C V)
    (tr: list transition_item)
    (Htr: finite_protocol_trace bvlsm is tr)
    (Hlast: last (map destination tr) is = s)
    : exists item : transition_item, In item tr /\ output item = Some m.
  Proof.
    destruct Htr as [Htr Hinit].
    apply has_been_sent_witness with s is; try assumption.
    inversion Hinit. intro. contradiction H0.
  Qed.

  Lemma has_been_received_in_futures
    (s1 s2 : state C V)
    (Hs : in_futures bvlsm s1 s2)
    : incl (State.received_messages s1) (State.received_messages s2).
  Proof.
    unfold State.received_messages.
    intros m Hm. apply set_diff_iff in Hm. apply set_diff_iff.
    destruct Hm as [Hm Hnm].
    specialize (get_messages_in_futures s1 s2 Hs _ Hm) as Hm1.
    split; try assumption.
    intro Hsm; elim Hnm.
    destruct Hs as [tr [Htr Hs2]].
    destruct
      (has_been_sent_witness s2 m Hsm s1 Hnm tr Htr Hs2)
      as [item [Hitem Hm']].
    apply in_split in Hitem. destruct Hitem as [l1 [l2 Hitem]].
    subst tr.
    pose (finite_protocol_trace_from_app_iff bvlsm s1 l1 (item :: l2)) as Happ.
    simpl in Happ. apply proj2 in Happ. specialize (Happ Htr).
    destruct Happ as [Hl1 Hl2].
    remember
      (@last (state C V)
      (@map (@transition_item message VLSM_type_full_validator)
         (state C V) (@destination message VLSM_type_full_validator) l1)
      s1)
      as s1'.
    assert (Hs1' : in_futures bvlsm s1 s1')
      by (exists l1; subst; split; try assumption; reflexivity).
    assert (Hm1' : In m (get_message_set s1'))
      by (apply (get_messages_in_futures s1 s1' Hs1'); assumption).
    inversion Hl2. subst s' tl item.
    simpl in Hm'. subst oom.
    clear - Hm1' H3.
    destruct H3 as [_ Ht].
    simpl in Ht. unfold vtransition in Ht. simpl in Ht.
    destruct s1' as (msgs, final). simpl in *.
    destruct l as [c|].
    - inversion Ht; subst. destruct final as [m|]; clear Ht.
      + elim
        (in_justification_recursive'
          (Msg c v (LastSent (make_message_set msgs) m))
          msgs
          eq_refl
        ).
        assumption.
      + elim
        (in_justification_recursive'
          (Msg c v (NoSent (make_message_set msgs)))
          msgs
          eq_refl
        ).
        assumption.
    - destruct iom as [msg|]; inversion Ht.
  Qed.

  Lemma last_state_empty_segment
    (start: Common.state)
    (prefix: list transition_item)
    (Hprefix: finite_protocol_trace_from bvlsm start prefix)
    (Hlast: last (map destination prefix) start = pair [] None)
    (item : transition_item)
    (Hitem : In item prefix)
    : input item = None /\ output item = None /\ destination item = pair [] None /\ l item = None.
  Proof.
    induction prefix using rev_ind.
    - inversion Hitem.
    - apply in_app_iff in Hitem.
      rewrite map_app in Hlast.
      simpl in Hlast. rewrite last_last in Hlast.
      apply finite_protocol_trace_from_app_iff in Hprefix.
      destruct Hprefix as [Hprefix Hx].
      specialize (IHprefix Hprefix).
      inversion Hx. subst s' x tl.
      simpl in Hlast. subst s.
      destruct H3 as [Hv Ht].
      simpl in Ht. unfold vtransition in Ht. simpl in Ht.
      destruct
        (@last (state C V)
        (@map (@transition_item message VLSM_type_full_validator)
           (state C V) (@destination message VLSM_type_full_validator)
           prefix) start)
        as (msgs, final) eqn:Hlast.
      destruct l as [c|]; inversion Ht.
      destruct iom as [msg|]; inversion Ht; subst.
      + specialize (set_add_not_empty decide_eq msg msgs) as Hempty. elim Hempty. assumption.
      + clear Ht H2 H0. specialize (IHprefix Hlast).
        destruct Hitem as [Hin |[Heq |Hfalse]]; try contradiction Hfalse.
        * specialize (IHprefix Hin). assumption.
        * subst item. simpl. repeat split; reflexivity.
  Qed.

  Lemma last_state_empty_trace
    (is : state C V)
    (tr: list transition_item)
    (Htr: finite_protocol_trace bvlsm is tr)
    (Hlast: last (map destination tr) is = pair [] None)
    (item : transition_item)
    (Hitem : In item tr)
    : input item = None /\ output item = None /\ destination item = pair [] None /\ l item = None.
  Proof.
    destruct Htr as [Htr _].
    specialize (last_state_empty_segment is tr Htr Hlast item Hitem) as H.
    assumption.
  Qed.

  Lemma sent_messages_prop
    (s : state C V)
    (Hs : protocol_state_prop bvlsm s)
    (m : message)
    : In m (State.sent_messages s) <->
    exists (sm : sent_messages vlsm s), proj1_sig sm = m.
  Proof.
    destruct Hs as [_om Hs].
    pose (protocol_is_trace bvlsm s _om Hs) as Htr.
    destruct Htr as [His | [is [tr [Htr [Hdest _]]]]]; split; intros
    ; try (inversion His; subst s; inversion H)
    ; try assert (Hlst : last (List.map destination tr) is = s)
      by (destruct tr as [|i tr]; inversion Hdest; apply last_map)
    .
    - destruct x as [m0 Hm0].
      destruct Hm0 as [is [tr [Htr [Hlst Hex]]]];simpl in *.
      apply Exists_exists in Hex.
      destruct Hex as [item [Hitem Hout]].
      specialize (last_state_empty_trace is tr Htr Hlst item Hitem).
      intros [_ [Hnout _]].
      simpl in Hout.
      rewrite Hnout in Hout. discriminate Hout.
    - assert (Hm : selected_message_exists_in_some_preloaded_traces vlsm (field_selector output) s m).
      { exists is. exists tr. exists Htr. exists Hlst.
        apply Exists_exists.
        apply (has_been_sent_in_trace_rev s m H is tr Htr Hlst).
      }
      exists (exist _ m Hm). reflexivity.
    - destruct H as [[m0 Hm] Heq].
      simpl in Heq. subst m0.
      destruct Hm as [ism [trm [Htrm [Hlastm Hexistm]]]].
      apply Exists_exists in Hexistm.
      destruct Hexistm as [item [Hin Hout]].
      apply (has_been_sent_in_trace s m ism trm Htrm item Hin Hout Hlastm).
  Qed.

  Lemma VLSM_full_validator_sent_consistency
    (s : vstate vlsm)
    (Hs : protocol_state_prop bvlsm s)
    (m : message)
    : selected_message_exists_in_some_preloaded_traces vlsm (field_selector output) s m <->
    selected_message_exists_in_all_preloaded_traces vlsm (field_selector output) s m.
  Proof.
    specialize (sent_messages_prop s Hs m) as Hin.
    split; intros.
    - intro is; intros.
      apply proj2 in Hin.
      spec Hin; try (exists (exist _ m H); reflexivity).
      specialize (has_been_sent_in_trace_rev s m Hin is tr Htr Hlast) as Hex.
      apply Exists_exists. assumption.
    - destruct Hs as [_om Hs].
      pose (protocol_is_trace bvlsm s _om Hs) as Htr.
      destruct Htr as [Hinit | [is [tr [Htr [Hlsts _]]]]].
      + specialize (selected_message_exists_in_all_traces_initial_state vlsm s Hinit (field_selector output) m) as Hsm.
        elim Hsm. assumption.
      + exists is. exists tr. exists Htr.
        assert (Hlst : last (List.map destination tr) is = s).
        { destruct tr as [|i tr]; inversion Hlsts. apply last_map. }
        exists Hlst.
        specialize (H is tr Htr Hlst). assumption.
  Qed.

  Instance VLSM_full_validator_computable_sent_messages
    : computable_sent_messages vlsm
    :=
    { sent_messages_fn := State.sent_messages;
      sent_messages_full := sent_messages_prop;
      sent_messages_consistency := VLSM_full_validator_sent_consistency
    }.

  Definition VLSM_full_validator_has_been_sent
    : has_been_sent_capability vlsm
    :=
    computable_sent_messages_has_been_sent_capability vlsm.

  Lemma get_sent_messages
    (s : state C V)
    (Hs : protocol_state_prop bvlsm s)
    : incl (State.sent_messages s) (get_message_set s).
  Proof.
    intros m Hm.
    apply sent_messages_prop in Hm; try assumption.
    destruct Hm as [[m0 Hm] Heq]. simpl in Heq. subst m0.
    apply VLSM_full_validator_sent_consistency in Hm; try assumption.
    destruct Hs as [_om Hs].
    pose (protocol_is_trace bvlsm s _om Hs) as Htr.
    destruct Htr as [Hinit | [is [tr [Htr [Hlsts _]]]]].
    + elim (selected_message_exists_in_all_traces_initial_state vlsm s Hinit (field_selector output) m).
      assumption.
    + assert (Hlst : last (map destination tr) is = s).
      { destruct tr as [|i tr]; inversion Hlsts.
        apply last_map.
      }
      specialize (Hm is tr Htr Hlst).
      apply Exists_exists in Hm. destruct Hm as [item [Hitem Hm]].
      apply in_split in Hitem.
      destruct Hitem as [l1 [l2 Hitem]]. subst tr.
      pose (finite_protocol_trace_from_app_iff bvlsm is l1 (item :: l2)) as Htr_app.
      simpl in Htr_app. destruct Htr_app as [_ Htr_app].
      destruct Htr as [Htr Hinit].
      specialize (Htr_app Htr).
      destruct Htr_app as [Hl1 Hl2].
      inversion Hl2. subst item tl.
      rewrite <- H1 in *.
      simpl in Hm. subst oom.
      apply protocol_transition_inv_out in H3.
      destruct H3 as [Hs0 [c Hc]].
      assert (Hfutures : in_futures bvlsm s0 s).
      {
        exists l2. split; try assumption.
        rewrite map_app in Hlst. rewrite last_app in Hlst.
        rewrite map_cons in Hlst. rewrite unroll_last in Hlst. simpl in Hlst.
        assumption.
      }
      apply (get_messages_in_futures s0 s Hfutures).
      subst s0. simpl. apply set_add_iff. left. reflexivity.
  Qed.

  Lemma has_been_received_in_trace
    (s : state C V)
    (m: message)
    (is : state C V)
    (tr: list transition_item)
    (Htr: finite_protocol_trace bvlsm is tr)
    (item: transition_item)
    (Hitem: In item tr)
    (Hm: input item = Some m)
    (Hs: last (map destination tr) is = s)
    : In m (State.received_messages s).
  Proof.
    apply in_split in Hitem.
    destruct Hitem as [l1 [l2 Hitem]]. subst tr.
    destruct Htr as [Htr Hinit].
    pose (finite_protocol_trace_from_app_iff bvlsm is l1 (item :: l2)) as Htr_app.
    simpl in Htr_app. destruct Htr_app as [_ Htr_app].
    specialize (Htr_app Htr).
    clear Htr. destruct Htr_app as [_ Htr].
    remember
      (@last (state C V)
      (@map (@transition_item message VLSM_type_full_validator)
         (state C V) (@destination message VLSM_type_full_validator) l1)
      is)
      as sl1.
    inversion Htr. subst tl item. simpl in Hm. subst iom.
    assert (Hs0 : in_futures bvlsm s0 s).
    { exists l2. split; try assumption.
      rewrite map_app in Hs. rewrite map_cons in Hs.
      rewrite last_app in Hs. rewrite unroll_last in Hs.
      simpl in Hs.
      assumption.
    }
    apply has_been_received_in_futures with s0; try assumption.
    specialize (has_been_sent_protocol_transition _ _ _ _ _ H3 m) as Hbspt.
    apply protocol_transition_inv_in in H3.
    destruct H3 as [Hs0' [Hoom [Hnin [Hincl [Hsl1 [Hm Hps0]]]]]].
    destruct (in_dec decide_eq m (State.sent_messages sl1)).
    - exfalso.
      apply get_sent_messages in i; try assumption.
      elim Hnin. assumption.
    - specialize (Hbspt n). subst oom.
      assert (Hnbs : ~In m (State.sent_messages s0)).
      { destruct (in_dec decide_eq m (State.sent_messages s0)); try assumption.
        apply Hbspt in i. discriminate i.
      }
      unfold State.received_messages.
      apply set_diff_iff. split; try assumption.
      subst s0. simpl.
      apply set_add_iff. left. reflexivity.
  Qed.

  Lemma has_been_received_in_trace_rev
    (s: state C V)
    (m: message)
    (Horacle: In m (State.received_messages s))
    (is : state C V)
    (tr: list transition_item)
    (Htr: finite_protocol_trace bvlsm is tr)
    (Hlast: last (map destination tr) is = s)
    : exists item : transition_item, In item tr /\ input item = Some m.
  Proof.
      apply set_diff_iff in Horacle.
      destruct Horacle as [Hin Hns].
      destruct Htr as [Htr Hinit].
      assert (Hstart : ~In m (get_message_set is)).
      { inversion Hinit. simpl. intro n. contradiction n. }
      clear -Hin Hns Htr Hlast Hstart bvlsm.
      generalize dependent is.
      induction tr; intros.
      + simpl in Hlast. subst is. elim Hstart. assumption.
      + inversion Htr. subst s' a tl.
        assert (Hlast' := Hlast).
        rewrite map_cons in Hlast. rewrite unroll_last in Hlast. simpl in Hlast.
        assert (Hfutures : in_futures bvlsm s0 s)
          by (exists tr; split; assumption).
        assert (Hnbs : ~In m (State.sent_messages s0)).
        { destruct (in_dec decide_eq  m (State.sent_messages s0)); try assumption.
          apply (has_been_sent_in_futures s0 s Hfutures) in i.
          elim Hns. assumption.
        }
        specialize (IHtr s0 H2).
        destruct (in_dec decide_eq m (get_message_set s0)).
        * specialize (finite_ptrace_first_pstate bvlsm is _ Htr) as Hpstart.
          destruct Hpstart as [_om Hpstart].
          pose (protocol_is_trace bvlsm is _om Hpstart) as Htr_start.
          assert  (Hiom : iom = Some m).
          { destruct H3 as [_ Ht]. simpl in Ht. unfold vtransition in Ht. simpl in Ht.
            destruct is as (msgs, final).
            destruct l as [c|].
            - inversion Ht. subst. clear Ht.
              simpl in *.
              apply set_add_iff in i.
              destruct i as [i | i]; try (elim Hstart; assumption).
              subst m.
              clear -Hnbs. exfalso.
              elim Hnbs.
              destruct final as [m|].
              + unfold State.sent_messages. simpl.
                apply set_add_iff. left. reflexivity.
              + unfold State.sent_messages. simpl.
                left. reflexivity.
            - destruct iom as [msg|]; inversion Ht; subst; clear Ht. simpl in *.
              + apply set_add_iff in i.
                destruct i as [i | i]; try (elim Hstart; assumption).
                subst m. reflexivity.
              + elim Hstart. assumption.
          }
          subst iom.
          exists {| l := l; input := Some m; destination := s0; output := oom |}.
          split; try reflexivity. left. reflexivity.
        * specialize (IHtr Hlast n).
          destruct IHtr as [item [Hitem Hin']]. exists item. split; try assumption.
          right. assumption.
  Qed.

  Lemma received_messages_prop
    (s : state C V)
    (Hs : protocol_state_prop bvlsm s)
    (m : message)
    : In m (State.received_messages s) <->
    exists (sm : received_messages vlsm s), proj1_sig sm = m.
  Proof.
    split; intros.
    - assert (Hm : selected_message_exists_in_some_preloaded_traces vlsm (field_selector input) s m)
      ; try (exists (exist _ m Hm); reflexivity).
      destruct Hs as [_om Hs].
      pose (protocol_is_trace bvlsm s _om Hs) as Htr.
      destruct Htr as [Hinit | [start [tr [Htr [Hdest _]]]]].
      + apply set_diff_iff in H. destruct H as [Hin Hns].
        inversion Hinit. subst s. inversion Hin.
      + specialize (has_been_received_in_trace_rev s m H start tr Htr) as Hbr.
        assert (Hlast : last (List.map destination tr) start = s)
        by (destruct tr as [|i tr]; inversion Hdest; apply last_map).
        specialize (Hbr Hlast).
        exists start. exists tr. exists Htr. exists Hlast. apply Exists_exists. assumption.
    - destruct H as [[m0 H] Heq]; simpl in Heq; subst m0.
      destruct H as [is [tr [Htr [Hlast Hitem]]]].
      apply Exists_exists in Hitem. destruct Hitem as [item [Hitem Hin]].
      apply (has_been_received_in_trace s m is tr Htr item Hitem Hin Hlast).
  Qed.

  Lemma VLSM_full_validator_received_consistency
    (s : vstate vlsm)
    (Hs : protocol_state_prop bvlsm s)
    (m : message)
    : selected_message_exists_in_some_preloaded_traces vlsm (field_selector input) s m <->
    selected_message_exists_in_all_preloaded_traces vlsm (field_selector input) s m.
  Proof.
    specialize (received_messages_prop s Hs m) as Hin.
    split; intros.
    - intro is; intros.
      apply proj2 in Hin.
      spec Hin; try (exists (exist _ m H); reflexivity).
      specialize (has_been_received_in_trace_rev s m Hin is tr Htr Hlast) as Hex.
      apply Exists_exists. assumption.
    - destruct Hs as [_om Hs].
      pose (protocol_is_trace bvlsm s _om Hs) as Htr.
      destruct Htr as [Hinit | [is [tr [Htr [Hlsts _]]]]].
      + specialize (selected_message_exists_in_all_traces_initial_state vlsm s Hinit (field_selector input) m) as Hsm.
        elim Hsm. assumption.
      + exists is. exists tr. exists Htr.
        assert (Hlst : last (List.map destination tr) is = s).
        { destruct tr as [|i tr]; inversion Hlsts. apply last_map. }
        exists Hlst.
        specialize (H is tr Htr Hlst). assumption.
  Qed.

  Instance VLSM_full_validator_computable_received_messages
    : computable_received_messages vlsm
    :=
    { received_messages_fn := State.received_messages;
      received_messages_full := received_messages_prop;
      received_messages_consistency := VLSM_full_validator_received_consistency
    }.

  Definition VLSM_full_validator_has_been_received
    : has_been_received_capability vlsm
    :=
    computable_received_messages_has_been_received_capability vlsm.

  Lemma VLSM_full_validator_sent_messages_comparable'
    (s : vstate vlsm)
    (tr : list transition_item)
    (Htr : finite_protocol_trace bvlsm s tr)
    (prefix middle suffix : list transition_item)
    (item1 item2 : transition_item)
    (Htreq: tr = prefix ++ cons item1 middle ++ item2 :: suffix)
    (m1 m2 : message)
    (Hm1 : output item1 = Some m1)
    (Hm2 : output item2 = Some m2)
    : validator_message_preceeds _ _ m1 m2.
  Proof.
    rewrite app_assoc in Htreq.
    subst tr.
    destruct Htr as [Htr Hinit].
    apply finite_protocol_trace_from_app_iff in Htr.
    destruct Htr as [Htr1 Htr2].
    specialize
      (has_been_sent_in_trace (last (map destination (prefix ++ item1 :: middle)) s)
        m1 s (prefix ++ item1 :: middle)
        (conj Htr1 Hinit)
        item1
      ) as Hm1'.
    spec Hm1'.
    { apply in_app_iff. right. left. reflexivity. }
    specialize (Hm1' Hm1 eq_refl).
    inversion Htr2. subst. simpl in Hm2. subst oom.
    apply protocol_transition_inv_out in H3.
    destruct H3 as [_ [Hjust _]].
    unfold validator_message_preceeds.
    unfold validator_message_preceeds_fn.
    destruct m2. simpl in Hjust.
    subst j. simpl.
    apply in_correct.
    apply in_unmake_message_set.
    apply in_make_justification.
    apply get_sent_messages; try assumption.
    apply finite_ptrace_last_pstate. assumption.
  Qed.

  Lemma VLSM_full_validator_sent_messages_comparable
    (s : vstate vlsm)
    (tr : list transition_item)
    (Htr : finite_protocol_trace bvlsm s tr)
    (m1 m2 : message)
    (Hm1 : trace_has_message (field_selector output) m1 tr)
    (Hm2 : trace_has_message (field_selector output) m2 tr)
    : m1 = m2 \/ validator_message_preceeds _ _ m1 m2 \/ validator_message_preceeds _ _ m2 m1.
  Proof.
    unfold trace_has_message in *.
    apply Exists_exists in Hm1. destruct Hm1 as [item1 [Hitem1 Hm1]].
    apply Exists_exists in Hm2. destruct Hm2 as [item2 [Hitem2 Hm2]].
    apply in_split in Hitem1.
    destruct Hitem1 as [prefix1 [suffix1 Hitem1]].
    rewrite Hitem1 in Hitem2.
    apply in_app_iff in Hitem2.
    destruct Hitem2 as [Hitem2 | [Heq | Hitem2]]
    ; try
      (apply in_split in Hitem2; destruct Hitem2 as [prefix2 [suffix2 Hitem2]]
      ; rewrite Hitem2 in Hitem1; clear Hitem2
      ).
    - right. right.
      rewrite <- app_assoc in Hitem1.
      apply
        (VLSM_full_validator_sent_messages_comparable'
          s tr Htr prefix2 suffix2 suffix1 item2 item1 Hitem1
          m2 m1 Hm2 Hm1
        ).
    - left. subst. simpl in Hm1, Hm2. rewrite Hm1 in Hm2. inversion Hm2. reflexivity.
    - right. left.
      apply
        (VLSM_full_validator_sent_messages_comparable'
          s tr Htr prefix1 prefix2 suffix2 item1 item2 Hitem1
          m1 m2 Hm1 Hm2
        ).
  Qed.

End proper_sent_received.

End CompositeValidator.
