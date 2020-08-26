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
    .

Section CompositeValidator.

  Context
    {C V : Type}
    {about_C : StrictlyComparable C}
    {about_V : StrictlyComparable V}
    {Hmeasurable : Measurable V}
    {Hrt : ReachableThreshold V}
    {Hestimator : Estimator (state C V) C}
    (message := State.message C V)
    .

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
             | Some msg => pair (pair (set_add compare_eq_dec msg msgs) final) None
           end
    | Some c =>
      let msg := (c, v, make_justification s) in
      pair (pair (set_add compare_eq_dec msg msgs) (Some msg)) (Some msg)
    end.

  Lemma vtransitionv_inv_out
    (v : V)
    (l : labelv)
    (s s' : state C V)
    (om : option message)
    (m' : message)
    (Ht : vtransitionv v l (s, om) = pair s' (Some m'))
    : s' = pair (set_add compare_eq_dec m' (get_message_set s)) (Some m')
    /\ exists (c : C), l = Some c.
  Proof.
    unfold vtransitionv in Ht. destruct s as (msgs, final).
    destruct l as [c|].
    - inversion Ht. split; try reflexivity. exists c. reflexivity.
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


Section proper_sent_received.
  Context
    (v : V)
    (vlsm := VLSM_full_validator v)
    (bvlsm := pre_loaded_vlsm vlsm)
    .

  Lemma validator_protocol_state_nodup
    (s : state C V)
    (Hs : protocol_state_prop bvlsm s)
    : NoDup (get_message_set s).
  Proof.
    generalize dependent s.
    apply
      (protocol_state_prop_ind bvlsm
        (fun (s : vstate bvlsm) =>
          NoDup (get_message_set s)
        )
      ); intros.
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
    : s' = pair (set_add compare_eq_dec m' (get_message_set s)) (Some m')
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
    : s' = pair (set_add compare_eq_dec m' (get_message_set s)) (Some m')
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
    : s' = pair (set_add compare_eq_dec m (get_message_set s)) (last_sent s)
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
    generalize dependent lst.
    generalize dependent s.
    apply
      (protocol_state_prop_ind bvlsm
        (fun (s : vstate bvlsm) =>
          forall (lst: message) (Hlst : last_sent s = Some lst),
            In lst (get_message_set s)
        )
      ); intros.
    - inversion Hs. subst s. inversion Hlst.
    - destruct Ht as [_ Ht]. simpl in Ht. unfold vtransition in Ht. simpl in Ht.
      destruct s as (msgs, final).
      destruct l as [c|].
      + inversion Ht; subst. destruct final as [m|]; simpl in *
        ; inversion Hlst; apply set_add_iff; left; reflexivity.
      + destruct om as [msg|]; inversion Ht; subst
        ; simpl in Hlst; subst final
        ; specialize (Hs lst eq_refl); simpl; try assumption.
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
    generalize dependent lst. simpl.
    generalize dependent s.
    apply
      (protocol_state_prop_ind bvlsm
        (fun (s : vstate bvlsm) =>
          forall (lst: message) (Hlst : last_sent s = Some lst),
            exists sj : state C V,
              protocol_state_prop bvlsm sj
              /\ make_justification sj = get_justification lst
        )
      ); intros.
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
        ; specialize (Hs lst eq_refl); simpl; assumption.
  Qed.

  Lemma in_protocol_state
    (s : state C V)
    (Hs : protocol_state_prop bvlsm s)
    (m : message)
    (Hm : In m (get_message_set s))
    : incl (unmake_message_set (justification_message_set (get_justification m))) (get_message_set s).
  Proof.
    generalize dependent m. generalize dependent s.
    pose
      (fun (s : state C V) =>
        forall (m : message) (Hm : In m (get_message_set s)),
          incl
            (unmake_message_set (justification_message_set (get_justification m)))
            (get_message_set s)
      ) as P.
    apply (protocol_state_prop_ind bvlsm P); unfold P; intros.
    - inversion Hs. subst s. inversion Hm.
    - destruct Ht as [[Hps [Hom Hv]] Ht].
      simpl in Ht. unfold vtransition in Ht. simpl in Ht.
      simpl in Hv. unfold vvalid in Hv. simpl in Hv.
      destruct s as (msgs, final).
      destruct l as [c|].
      + inversion Ht; subst; clear Ht.
        destruct final as [m0|]; simpl in *
        ; apply set_add_iff in Hm
        ; destruct Hm as [Heq | Hm]
        ; intros msg Hmsg
        ; apply set_add_iff
        ; right
        ; try (subst m; simpl in Hmsg; apply make_unmake_message_set_eq; assumption)
        ; specialize (Hs m Hm); apply Hs; assumption.
      + destruct om as [msg|]; inversion Ht; subst; clear Ht
        ; simpl in Hs; simpl in Hv; simpl
        ; try (apply Hs; assumption).
        destruct Hv as [Hnmsg Hv].
        apply set_add_iff in Hm.
        destruct Hm as [Heqm | Hm].
        * subst m.
          apply incl_tran with msgs; try assumption.
          intros x Hx; apply set_add_iff. right. assumption.
        * specialize (Hs m Hm).
          apply incl_tran with msgs; try assumption.
          intros x Hx; apply set_add_iff. right. assumption.
  Qed.

  Lemma sent_messages_in_futures
    (s1 s2 : state C V)
    (Hs : in_futures bvlsm s1 s2)
    : incl (sent_messages s1) (sent_messages s2).
  Proof.
    unfold in_futures in Hs. destruct Hs as [tr [Htr Hs2]].
    generalize dependent s2. generalize dependent s1.
    induction tr; intros.
    - simpl in Hs2. subst s2. apply incl_refl.
    - inversion Htr. subst a s' tl.
      rewrite map_cons in Hs2. rewrite unroll_last in Hs2. simpl in Hs2.
      specialize (IHtr s H2 s2 Hs2).
      apply incl_tran with (sent_messages s); try assumption.
      clear -H3.
      destruct H3 as [_ Ht]. simpl in Ht. unfold vtransition in Ht. simpl in Ht.
      destruct s1 as (msgs, final).
      destruct l as [c|].
      + inversion Ht; subst; clear Ht. unfold sent_messages. simpl.
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

  Lemma has_been_sent_in_futures
    (s1 s2 : state C V)
    (Hs : in_futures bvlsm s1 s2)
    (m : message)
    (Hm : has_been_sent_oracle s1 m = true)
    : has_been_sent_oracle s2 m = true.
  Proof.
    unfold has_been_sent_oracle in *.
    pose (proj2 (in_correct (sent_messages s1) m)) as Hin1.
    specialize (Hin1 Hm).
    pose (proj1 (in_correct (sent_messages s2) m)) as Hin2.
    apply Hin2.
    pose (sent_messages_in_futures s1 s2 Hs) as Hsent.
    apply Hsent. assumption.
  Qed.

  Lemma has_been_sent_protocol_transition
    (l : vlabel bvlsm)
    (s1 s2 : state C V)
    (iom oom : option message)
    (Hpt : protocol_transition bvlsm l (s1, iom) (s2, oom))
    (m : message)
    (Hs1 : has_been_sent_oracle s1 m = false)
    : has_been_sent_oracle s2 m = true <-> oom = Some m.
  Proof.
    destruct Hpt as [_ Ht]. simpl in Ht.
    unfold vtransition in Ht. simpl in Ht.
    destruct s1 as (msgs, final).
    unfold has_been_sent_oracle in *.
    pose (in_correct' (sent_messages (msgs, final)) m)  as Hnin.
    rewrite <- Hnin in Hs1.
    pose (in_correct (sent_messages s2) m)  as Hin.
    rewrite <- Hin.
    destruct l as [c|]; inversion Ht; subst.
    + unfold sent_messages. simpl.  split; intro H.
      * apply set_add_iff in H.
        destruct H as [Heq | H]; subst; try reflexivity.
        elim Hs1. unfold sent_messages. simpl.
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
    : has_been_sent_oracle s m = true.
  Proof.
    apply in_split in Hitem.
    destruct Hitem as [l1 [l2 Hitem]]. subst tr.
    destruct Htr as [Htr Hinit].
    pose (finite_protocol_trace_from_app_iff bvlsm is l1 (item :: l2)) as Htr_app.
    simpl in Htr_app. destruct Htr_app as [_ Htr_app].
    specialize (Htr_app Htr).
    clear Htr. destruct Htr_app as [_ Htr].
    inversion Htr. subst tl item. simpl in Hm. subst oom.
    assert (Hm0 : has_been_sent_oracle s0 m = true).
    { clear -H3. destruct H3 as [_ Ht].
      simpl in Ht. unfold vtransition in Ht. simpl in Ht.
      destruct
        (@last (state C V)
        (@map (@transition_item message VLSM_type_full_validator)
           (state C V) (@destination message VLSM_type_full_validator) l1)
        is)
        as (msgs, final).
      destruct l as [c|].
      - unfold has_been_sent_oracle.
        pose (proj1 (in_correct (sent_messages s0) m)) as Hin.
        apply Hin.
        inversion Ht; subst; clear Ht.
        unfold sent_messages. simpl.
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
    (Horacle: has_been_sent_oracle s m = true)
    (start: Common.state)
    (Hstart: has_been_sent_oracle start m = false)
    (prefix: list transition_item)
    (Hprefix: finite_protocol_trace_from (pre_loaded_vlsm vlsm) start prefix)
    (Hlast: last (map destination prefix) start = s)
    : exists item : transition_item, In item prefix /\ output item = Some m.
  Proof.
    generalize dependent start.
    induction prefix; intros.
    + inversion Hprefix; subst.
      simpl in Horacle. rewrite Hstart in Horacle. discriminate Horacle.
    + rewrite map_cons in Hlast. rewrite unroll_last in Hlast.
      inversion Hprefix; subst. simpl in *.
      destruct oom as [om|]; try destruct (compare_eq_dec om m); try subst om.
      * exists (@Build_transition_item message VLSM_type_full_validator l iom s0 (@Some message m)).
        split; try reflexivity.
        left. reflexivity.
      * assert (Hs0 : has_been_sent_oracle s0 m = false).
        { apply not_true_is_false.
          intro Hbs.
          apply (has_been_sent_protocol_transition _ _ _ _ _ H3 _ Hstart) in Hbs.
          elim n.
          inversion Hbs. reflexivity.
        }
        specialize (IHprefix s0 Hs0 H2 eq_refl).
        destruct IHprefix as [x [Hx Hm]].
        exists x.
        split; try assumption.
        right. assumption.
      * assert (Hs0 : has_been_sent_oracle s0 m = false).
        { apply not_true_is_false.
          intro Hbs.
          apply (has_been_sent_protocol_transition _ _ _ _ _ H3 _ Hstart) in Hbs.
          discriminate Hbs.
        }
        specialize (IHprefix s0 Hs0 H2 eq_refl).
        destruct IHprefix as [x [Hx Hm]].
        exists x.
        split; try assumption.
        right. assumption.
  Qed.

  Lemma has_been_received_in_futures
    (s1 s2 : state C V)
    (Hs : in_futures bvlsm s1 s2)
    (m : message)
    (Hm : has_been_received_oracle s1 m = true)
    : has_been_received_oracle s2 m = true.
  Proof.
    unfold has_been_received_oracle in *.
    apply andb_true_iff in Hm.
    destruct Hm as [Hm Hnm].
    apply negb_true_iff in Hnm.
    pose (proj2 (in_correct (get_message_set s1) m)) as Hin1.
    apply Hin1 in Hm.
    pose (get_messages_in_futures s1 s2 Hs) as Hsent.
    specialize (Hsent _ Hm).
    apply in_correct in Hsent.
    apply andb_true_iff.
    split; try assumption.
    apply negb_true_iff.
    destruct (has_been_sent_oracle s2 m) eqn:Hm2; try reflexivity.
    destruct Hs as [tr [Htr Hs2]].
    destruct
      (has_been_sent_witness s2 m Hm2 s1 Hnm tr Htr Hs2)
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
          ((c, v, LastSent C V (make_message_set msgs) m))
          msgs
          eq_refl
        ).
        assumption.
      + elim
        (in_justification_recursive'
          ((c, v, NoSent C V (make_message_set msgs)))
          msgs
          eq_refl
        ).
        assumption.
    - destruct iom as [msg|]; inversion Ht.
  Qed.

  Lemma VLSM_full_validator_proper_sent
    (s : state C V)
    (Hs : protocol_state_prop bvlsm s)
    (m : message)
    : has_been_sent_prop vlsm has_been_sent_oracle s m.
  Proof.
    unfold has_been_sent_prop. unfold all_traces_have_message_prop.
    split.
    - intros Horacle start prefix Hprefix Hlast.
      apply Exists_exists.
      destruct Hprefix as [Hprefix Hinit].
      assert (Hstart : has_been_sent_oracle start m = false)
        by (inversion Hinit; reflexivity).
      clear -Hprefix Horacle Hstart Hlast bvlsm.
      apply has_been_sent_witness with s start; assumption.
    - intros.
      destruct Hs as [_om Hs].
      pose (protocol_is_trace bvlsm s _om Hs) as Htr.
      destruct Htr as [Hinit | [is [tr [Htr [Hlsts _]]]]].
      + exfalso.
        assert (Htrs : finite_protocol_trace bvlsm s []).
        { split; try assumption. constructor. exists _om. assumption. }
        specialize (H s [] Htrs eq_refl).
        apply Exists_exists in H. destruct H as [x [Hin _]]. inversion Hin.
      + assert (Hlst : last (map destination tr) is = s).
        { destruct tr as [|i tr]; inversion Hlsts.
          apply last_map.
        }
        specialize (H is tr Htr Hlst).
        apply Exists_exists in H.
        destruct H as [item [Hitem Hm]].
        apply has_been_sent_in_trace with is tr item; assumption.
  Qed.

  Lemma has_been_sent_in
    (s : state C V)
    (Hs : protocol_state_prop bvlsm s)
    (m : message)
    (Hbs : has_been_sent_oracle s m = true)
    : In m (get_message_set s).
  Proof.
    pose (VLSM_full_validator_proper_sent s Hs m) as Hps.
    unfold has_been_sent_prop in Hps. unfold all_traces_have_message_prop in Hps.
    simpl in Hps. rewrite Hps in Hbs. clear Hps.
    destruct Hs as [_om Hs].
    pose (protocol_is_trace bvlsm s _om Hs) as Htr.
    destruct Htr as [Hinit | [is [tr [Htr [Hlsts _]]]]].
    + exfalso.
      assert (Htrs : finite_protocol_trace bvlsm s []).
      { split; try assumption. constructor. exists _om. assumption. }
      specialize (Hbs s [] Htrs eq_refl).
      apply Exists_exists in Hbs. destruct Hbs as [x [Hin _]]. inversion Hin.
    + assert (Hlst : last (map destination tr) is = s).
      { destruct tr as [|i tr]; inversion Hlsts.
        apply last_map.
      }
      specialize (Hbs is tr Htr Hlst).
      apply Exists_exists in Hbs. destruct Hbs as [item [Hitem Hm]].
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
    : has_been_received_oracle s m = true.
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
    pose (has_been_sent_protocol_transition _ _ _ _ _ H3) as Hbspt.
    specialize (Hbspt m).
    apply protocol_transition_inv_in in H3.
    destruct H3 as [Hs0' [Hoom [Hnin [Hincl [Hsl1 [Hm Hps0]]]]]].
    destruct (has_been_sent_oracle sl1 m) eqn:Hnbs.
    - exfalso.
      apply has_been_sent_in in Hnbs; try assumption.
      elim Hnin. assumption.
    - specialize (Hbspt eq_refl). subst oom.
      clear Hnbs.
      assert (Hnbs : has_been_sent_oracle s0 m = false).
      { destruct (has_been_sent_oracle s0 m); try reflexivity.
        apply proj1 in Hbspt. specialize (Hbspt eq_refl). discriminate Hbspt.
      }
     unfold has_been_received_oracle.
     apply andb_true_iff.
     rewrite negb_true_iff.
     split; try assumption.
     pose (proj1 (in_correct (get_message_set s0) m)) as Hin.
     apply Hin.
     subst s0. simpl. apply set_add_iff. left. reflexivity.
  Qed.

  Lemma get_sent_messages
    (s : state C V)
    (Hs : protocol_state_prop bvlsm s)
    : incl (sent_messages s) (get_message_set s).
  Proof.
    intros m Hm.
    apply has_been_sent_in; try assumption.
    apply in_correct in Hm.
    assumption.
  Qed.

  Definition has_not_been_sent_oracle
    (s : state C V)
    (m : message)
    : bool
    :=
    negb (has_been_sent_oracle s m).

  Lemma VLSM_full_validator_proper_not_sent
    (s : state C V)
    (Hs : protocol_state_prop bvlsm s)
    (m : message)
    : has_not_been_sent_prop vlsm has_not_been_sent_oracle s m.
  Proof.
    unfold has_not_been_sent_prop. unfold no_traces_have_message_prop.
    unfold has_not_been_sent_oracle. rewrite negb_true_iff.
    split.
    - intros.
      rewrite <- Forall_Exists_neg.
      apply Forall_forall.
      intros item Hitem Hm.
      pose (has_been_sent_in_trace s m start tr Htr item Hitem Hm Hlast).
      rewrite e in H. discriminate H.
    - pose (VLSM_full_validator_proper_sent s Hs m) as Hsent.
      intro H. destruct Hs as [_om Hs].
      pose (protocol_is_trace bvlsm s _om Hs) as Htr.
      destruct Htr as [Hinit | [is [tr [Htr [Hlsts _]]]]].
      + inversion Hinit. unfold has_been_sent_oracle. unfold sent_messages. unfold inb.
        reflexivity.
      + assert (Hlst : last (map destination tr) is = s).
        { destruct tr as [|i tr]; inversion Hlsts.
          apply last_map.
        }
        specialize (H is tr Htr Hlst).
        destruct (has_been_sent_oracle s m) eqn:Hbs; try reflexivity.
        exfalso.
        unfold has_been_sent_prop in Hsent.
        unfold all_traces_have_message_prop in Hsent.
        rewrite Hsent in Hbs.
        specialize (Hbs is tr Htr Hlst).
        elim H. assumption.
  Qed.

  Definition has_been_sent_oracle' : state_message_oracle (VLSM_full_validator v)
    := has_been_sent_oracle.

  Definition VLSM_full_validator_has_been_sent
    : has_been_sent_capability (VLSM_full_validator v)
    :=
    {| has_been_sent := has_been_sent_oracle'
     ; proper_sent := VLSM_full_validator_proper_sent
     ; proper_not_sent := VLSM_full_validator_proper_not_sent
    |}.

  Lemma VLSM_full_validator_proper_received
    (s : state C V)
    (Hs : protocol_state_prop bvlsm s)
    (m : message)
    : has_been_received_prop vlsm has_been_received_oracle s m.
  Proof.
    unfold has_been_received_prop. unfold all_traces_have_message_prop.
    split; intros.
    - apply Exists_exists.
      apply andb_true_iff in H.
      destruct H as [Hin Hns].
      apply negb_true_iff in Hns.
      pose (in_correct (get_message_set s) m) as Hinc. apply Hinc in Hin.
      destruct Htr as [Htr Hinit].
      assert (Hstart : ~In m (get_message_set start)).
      { inversion Hinit. simpl. intro n. contradiction n. }
      clear -Hin Hns Htr Hlast Hstart bvlsm.
      generalize dependent start.
      induction tr; intros.
      + simpl in Hlast. subst start. elim Hstart. assumption.
      + inversion Htr. clear Htr. subst s' a tl.
        rewrite map_cons in Hlast. rewrite unroll_last in Hlast. simpl in Hlast.
        assert (Hfutures : in_futures bvlsm s0 s)
          by (exists tr; split; assumption).
        assert (Hnbs : has_been_sent_oracle s0 m = false).
        { destruct (has_been_sent_oracle s0 m) eqn:Hs0; try reflexivity.
          apply (has_been_sent_in_futures s0 s Hfutures) in Hs0.
          rewrite Hns in Hs0. discriminate Hs0.
        }
        specialize (IHtr s0 H2 Hlast).
        destruct (in_dec compare_eq_dec m (get_message_set s0)).
        * destruct H3 as [_ Ht]. simpl in Ht. unfold vtransition in Ht. simpl in Ht.
          exists {| l := l; input := iom; destination := s0; output := oom |}.
          split; try (left; reflexivity). simpl.
          destruct start as (msgs, final).
          { destruct l as [c|].
          - inversion Ht. subst. clear Ht.
            simpl in *.
            apply set_add_iff in i.
            destruct i as [i | i]; try (elim Hstart; assumption).
            subst m.
            clear -Hnbs. exfalso.
            unfold has_been_sent_oracle in Hnbs. unfold sent_messages in Hnbs.
            simpl in Hnbs.
            destruct final as [m|].
            + pose
              (proj2 (in_correct'
                (set_add compare_eq_dec
                  ((c, v, LastSent C V (make_message_set msgs) m))
                    (sent_messages_justification
                       (LastSent C V (make_message_set msgs) m)))
               ((c, v, LastSent C V (make_message_set msgs) m))
              ))  as Hin.
              apply Hin in Hnbs. elim Hnbs.
              apply set_add_iff. left. reflexivity.
            + pose
              (proj2 (in_correct'
                  (set_add compare_eq_dec ((c, v, NoSent C V (make_message_set msgs)))
                    (sent_messages_justification (NoSent C V (make_message_set msgs))))
                  ((c, v, NoSent C V (make_message_set msgs)))
              ))  as Hin.
              apply Hin in Hnbs. elim Hnbs.
              apply set_add_iff. left. reflexivity.
          - destruct iom as [msg|]; inversion Ht; subst; clear Ht. simpl in *.
            + apply set_add_iff in i.
              destruct i as [i | i]; try (elim Hstart; assumption).
              subst m. reflexivity.
            + elim Hstart. assumption.
          }
        * specialize (IHtr n). destruct IHtr as [item [Hitem Hm]].
          exists item. split; try assumption. right. assumption.
    - destruct Hs as [_om Hs].
      pose (protocol_is_trace bvlsm s _om Hs) as Htr.
      destruct Htr as [Hinit | [is [tr [Htr [Hlsts _]]]]].
      + exfalso.
        assert (Htrs : finite_protocol_trace bvlsm s []).
        { split; try assumption. constructor. exists _om. assumption. }
        specialize (H s [] Htrs eq_refl).
        apply Exists_exists in H. destruct H as [x [Hin _]]. inversion Hin.
      + assert (Hlst : last (map destination tr) is = s).
        { destruct tr as [|i tr]; inversion Hlsts.
          apply last_map.
        }
        clear Hlsts.
        specialize (H is tr Htr Hlst). apply Exists_exists in H.
        destruct H as [item [Hitem Hm]].
        apply has_been_received_in_trace with is tr item; assumption.
(*
        remember (length tr) as len.
        generalize dependent tr.
        induction len; intros
        ; specialize (H is tr Htr Hlst); apply Exists_exists in H
        ; destruct H as [item [Hitem Hm]].
        * symmetry in Heqlen. apply length_zero_iff_nil in Heqlen. subst tr.
          inversion Hitem.
        * destruct (has_been_sent_oracle (destination item) m) eqn:Hbs
          ; try (apply has_been_received_in_trace with is tr item; assumption).
          apply in_split in Hitem.
          destruct Hitem as [l1 [l2 Hitem]]. subst tr.
          specialize (IHlen (l1 ++ l2)).
          destruct Htr as [Htr Hinit].
          pose (finite_protocol_trace_from_app_iff bvlsm is l1 (item :: l2)) as Htr_app.
          simpl in Htr_app. destruct Htr_app as [_ Htr_app].
          specialize (Htr_app Htr).
          destruct Htr_app as [Hl1 Hl2].
          inversion Hl2. subst item tl.
          rewrite <- H1 in *.
          simpl in Hm. subst iom. simpl in Hbs.
          apply protocol_transition_inv_in in H3.
          destruct H3 as [Hs0 [Hoom [Hnin [Hincl [Hs' [Hm Hps0]]]]]].
          assert (Hbs' : has_been_sent_oracle s' m = true).
          { unfold has_been_sent_oracle. unfold sent_messages.
            rewrite Hs0 in Hbs.
            unfold has_been_sent_oracle in Hbs.
            unfold sent_messages in Hbs. simpl in Hbs.
            assumption.
          }
          assert (Hss0 : s0 = s').
          { pose (has_been_sent_in s' Hs' m Hbs') as Hin.
            rewrite Hs0. destruct s' as (msgs', final').
            simpl. f_equal.
            pose (set_add_ignore msgs' m) as Hadd.
            apply Hadd.
            assumption.
          }
          { apply IHlen.
          - split; try assumption.
            apply (finite_protocol_trace_from_app_iff bvlsm is l1 l2).
            split; try assumption.
            clear Hs0. subst. assumption.
          - rewrite map_app. rewrite last_app.
            rewrite map_app in Hlst. rewrite last_app in Hlst.
            rewrite map_cons in Hlst. rewrite unroll_last in Hlst.
            simpl in Hlst. clear Hs0. subst. reflexivity.
          - rewrite app_length. rewrite app_length in Heqlen.
            simpl in Heqlen. clear -Heqlen.
            rewrite Plus.plus_comm in Heqlen. inversion Heqlen.
            apply Plus.plus_comm.
          }
*)
  Qed.

  Definition has_not_been_received_oracle
    (s : state C V)
    (m : message)
    : bool
    :=
    negb (has_been_received_oracle s m).

  Lemma VLSM_full_validator_proper_not_received
    (s : state C V)
    (Hs : protocol_state_prop bvlsm s)
    (m : message)
    : has_not_been_received_prop vlsm has_not_been_received_oracle s m.
  Proof.
    unfold has_not_been_received_prop. unfold no_traces_have_message_prop.
    unfold has_not_been_received_oracle. rewrite negb_true_iff.
    split.
    - intros.
      rewrite <- Forall_Exists_neg.
      apply Forall_forall.
      intros item Hitem Hm.
      assert (Hbr : has_been_received_oracle s m = true)
      ; try (rewrite H in Hbr; discriminate Hbr).
      pose (has_been_received_in_trace s m start tr Htr item Hitem Hm Hlast).
      rewrite e in H. discriminate H.
    - pose (VLSM_full_validator_proper_received s Hs m) as Hreceived.
      intro H. destruct Hs as [_om Hs].
      pose (protocol_is_trace bvlsm s _om Hs) as Htr.
      destruct Htr as [Hinit | [is [tr [Htr [Hlsts _]]]]].
      + inversion Hinit. unfold has_been_received_oracle.
        reflexivity.
      + assert (Hlst : last (map destination tr) is = s).
        { destruct tr as [|i tr]; inversion Hlsts.
          apply last_map.
        }
        specialize (H is tr Htr Hlst).
        destruct (has_been_received_oracle s m) eqn:Hbr; try reflexivity.
        exfalso.
        unfold has_been_received_prop in Hreceived.
        unfold all_traces_have_message_prop in Hreceived.
        rewrite Hreceived in Hbr.
        specialize (Hbr is tr Htr Hlst).
        elim H. assumption.
  Qed.

  Definition has_been_received_oracle' : state_message_oracle (VLSM_full_validator v)
    := has_been_received_oracle.

  Definition VLSM_full_validator_has_been_received
    : has_been_received_capability (VLSM_full_validator v)
    :=
    {| has_been_received := has_been_received_oracle'
     ; proper_received := VLSM_full_validator_proper_received
     ; proper_not_received := VLSM_full_validator_proper_not_received
    |}.

End proper_sent_received.

End CompositeValidator.
