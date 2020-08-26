Require Import List ListSet.

Import ListNotations.

From CasperCBC
  Require Import
    Lib.Preamble
    Lib.ListExtras
    VLSM.Common
    CBC.Common
    CBC.Equivocation
    Validator.State
    Validator.Equivocation
    VLSM.Equivocation
    .

Section CompositeClient.

(** * Full-node client as a VLSM

This section defines a full-node client as a VLSM.
The full node client does not produce messages, but incorporates received
messages, implementing a limited equivocation tolerance policy.
*)

  Context
    {C V : Type}
    {about_C : StrictlyComparable C}
    {about_V : StrictlyComparable V}
    {Hmeasurable : Measurable V}
    {Hrt : ReachableThreshold V}
    (eq_V := strictly_comparable_eq_dec about_V)
    (message := State.message C V)
    .
  
  Existing Instance eq_V.

  Existing Instance full_node_message_equivocation_evidence.

  Instance client_state_encapsulating_messages
    : state_encapsulating_messages (set message) message
    :=
    {| get_messages := fun s => s |}.

  Definition client_basic_equivocation
    := state_encapsulating_messages_equivocation (set message) message V.

  Existing Instance client_basic_equivocation.

  (* 2.5.1 Minimal full client protocol: Client2 *)
  Definition label2 : Type := unit.

  Definition vtransition2
    (l : unit)
    (sm : set message * option message)
    : set message * option message
    :=
    let (msgs, om) := sm in
    match om with
    | None => pair msgs None
    | Some msg => pair (set_add eq_dec msg msgs)  None
    end.

  Definition valid_client2
    (_ : unit)
    (som : set message * option message)
    :=
    let (msgs, om) := som in
    match om with
    | None => True
    | Some msg =>
      ~In msg msgs
      /\ incl (get_message_set (unmake_justification (get_justification msg))) msgs
      /\ not_heavy (set_add eq_dec msg msgs)
    end.

  Instance VLSM_type_full_client2 : VLSM_type message :=
    { state := set message
    ; label := label2
    }.

  Definition initial_state_prop
    (s : set message)
    : Prop
    :=
    s = [].

  Definition state0 : {s | initial_state_prop s} :=
    exist _ [] eq_refl.

  Definition initial_message_prop (m : message) : Prop := False.

  Instance LSM_full_client2 : VLSM_sign VLSM_type_full_client2 :=
    { initial_state_prop := initial_state_prop
    ; initial_message_prop := initial_message_prop
    ; s0 := state0
    ; m0 := State.message0
    ; l0 := tt
    }.

  Definition VLSM_full_client2_machine  : VLSM_class LSM_full_client2 :=
    {| transition := vtransition2
      ; valid := valid_client2
    |}.

  Definition VLSM_full_client2 : VLSM message := mk_vlsm VLSM_full_client2_machine.

  Section proper_sent_received.
  Context
    (vlsm := VLSM_full_client2)
    (bvlsm := pre_loaded_vlsm vlsm)
    .

  Lemma client_protocol_state_nodup
    (s : set message)
    (Hs : protocol_state_prop bvlsm s)
    : NoDup s.
  Proof.
    generalize dependent s.
    apply
      (protocol_state_prop_ind (pre_loaded_vlsm VLSM_full_client2)
        (fun (s : vstate (pre_loaded_vlsm VLSM_full_client2)) =>
          NoDup s
        )
      ); intros.
    - inversion Hs. constructor.
    - destruct Ht as [_ Ht].
      simpl in Ht. unfold vtransition in Ht. simpl in Ht.
      destruct om as [msg|]; inversion Ht.
      * apply set_add_nodup. assumption.
      * subst. assumption.
  Qed.

  Lemma protocol_transition_inv_in
    (l : label)
    (s s' : set message)
    (m : message)
    (om' : option message)
    (Ht : protocol_transition bvlsm l (s, Some m) (s', om'))
    : s' = set_add eq_dec m s
    /\ om' = None
    /\ ~In m s
    /\ incl
        (unmake_message_set (justification_message_set (get_justification m)))
        s
    /\ not_heavy s'
    /\ protocol_state_prop bvlsm s
    /\ protocol_message_prop bvlsm m
    /\ protocol_state_prop bvlsm s'.
  Proof.
    pose Ht as Hs'.
    apply protocol_transition_destination in Hs'.
    destruct Ht as [[Hs [Hm [Hnin [Hincl Hnh]]]] Ht].
    inversion Ht. subst. simpl.
    repeat split; try reflexivity; assumption.
  Qed.

  Lemma protocol_transition_inv_out
    (l : vlabel bvlsm)
    (s1 s2 : set message)
    (iom : option message)
    (m : message)
    (Ht : protocol_transition bvlsm l (s1, iom) (s2, Some m))
    : False.
  Proof.
    destruct Ht as [Hv Ht].
    simpl in Ht. unfold vtransition in Ht. simpl in Ht.
    destruct iom; inversion Ht.
  Qed.

  Lemma in_protocol_state
    (s : set message)
    (Hs : protocol_state_prop bvlsm s)
    (m : message)
    (Hm : In m s)
    : incl (unmake_message_set (justification_message_set (get_justification m))) s.
  Proof.
    generalize dependent m. generalize dependent s.
    pose
      (fun (s : set message) =>
        forall (m : message) (Hm : In m s),
          incl
            (unmake_message_set (justification_message_set (get_justification m)))
            s
      ) as P.
    apply (protocol_state_prop_ind bvlsm P); unfold P; intros.
    - inversion Hs. subst s. inversion Hm.
    - destruct Ht as [[Hps [Hom Hv]] Ht].
      simpl in Ht. unfold vtransition in Ht. simpl in Ht.
      simpl in Hv. unfold vvalid in Hv. simpl in Hv.
      destruct om as [msg|]; inversion Ht; subst; clear Ht
      ; simpl in Hs; simpl in Hv; simpl
      ; try (apply Hs; assumption).
      destruct Hv as [Hnmsg [Hv Hnh]].
      apply set_add_iff in Hm.
      destruct Hm as [Heqm | Hm].
      + subst m.
        apply incl_tran with s; try assumption.
        intros x Hx; apply set_add_iff. right. assumption.
      + specialize (Hs m Hm).
        apply incl_tran with s; try assumption.
        intros x Hx; apply set_add_iff. right. assumption.
  Qed.

  Lemma get_messages_in_futures
    (s1 s2 : set message)
    (Hs : in_futures bvlsm s1 s2)
    : incl s1 s2.
  Proof.
    unfold in_futures in Hs. destruct Hs as [tr [Htr Hs2]].
    generalize dependent s2. generalize dependent s1.
    induction tr; intros.
    - simpl in Hs2. subst s2. apply incl_refl.
    - inversion Htr. subst a s' tl.
      rewrite map_cons in Hs2. rewrite unroll_last in Hs2. simpl in Hs2.
      specialize (IHtr s H2 s2 Hs2).
      apply incl_tran with s; try assumption.
      clear -H3.
      destruct H3 as [_ Ht]. simpl in Ht. unfold vtransition in Ht. simpl in Ht.
      destruct iom as [msg|]; inversion Ht; try apply incl_refl.
      simpl. intros m Hm. apply set_add_iff. right. assumption.
  Qed.

  Definition client_has_been_sent
    : state_message_oracle vlsm
    :=
    fun _ _ => false.

  Definition client_has_been_received
    : state_message_oracle vlsm
    :=
    fun s m => inb eq_dec m s.

  Lemma has_been_sent_in_trace
    (s : set message)
    (m: message)
    (is : set message)
    (tr: list transition_item)
    (Htr: finite_protocol_trace bvlsm is tr)
    (item: transition_item)
    (Hitem: In item tr)
    (Hm: output item = Some m)
    (Hs: last (map destination tr) is = s)
    : False.
  Proof.
    apply in_split in Hitem.
    destruct Hitem as [l1 [l2 Hitem]]. subst tr.
    destruct Htr as [Htr Hinit].
    pose (finite_protocol_trace_from_app_iff bvlsm is l1 (item :: l2)) as Htr_app.
    simpl in Htr_app. destruct Htr_app as [_ Htr_app].
    specialize (Htr_app Htr).
    clear Htr. destruct Htr_app as [_ Htr].
    inversion Htr. subst tl item. simpl in Hm. subst oom.
    apply protocol_transition_inv_out in H3. contradiction H3.
  Qed.

  Lemma VLSM_full_client_proper_sent
    (s : set message)
    (Hs : protocol_state_prop bvlsm s)
    (m : message)
    : has_been_sent_prop vlsm client_has_been_sent s m.
  Proof.
    unfold has_been_sent_prop. unfold all_traces_have_message_prop.
    split; intro H; try discriminate H.
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
        specialize (H is tr Htr Hlst).
        apply Exists_exists in H.
        destruct H as [item [Hitem Hm]].
        exfalso.
        apply has_been_sent_in_trace with s m is tr item; assumption.
  Qed.

  Lemma has_been_received_in_trace
    (s : set message)
    (m: message)
    (is : set message)
    (tr: list transition_item)
    (Htr: finite_protocol_trace bvlsm is tr)
    (item: transition_item)
    (Hitem: In item tr)
    (Hm: input item = Some m)
    (Hs: last (map destination tr) is = s)
    : In m s.
  Proof.
    apply in_split in Hitem.
    destruct Hitem as [l1 [l2 Hitem]]. subst tr.
    destruct Htr as [Htr Hinit].
    pose (finite_protocol_trace_from_app_iff bvlsm is l1 (item :: l2)) as Htr_app.
    simpl in Htr_app. destruct Htr_app as [_ Htr_app].
    specialize (Htr_app Htr).
    clear Htr. destruct Htr_app as [_ Htr].
    remember
      (@last (set message)
      (@map (@transition_item message VLSM_type_full_client2)
         (set message) (@destination message VLSM_type_full_client2) l1)
      is)
      as sl1.
    inversion Htr. subst tl item. simpl in Hm. subst iom.
    apply protocol_transition_inv_in in H3.
    assert (Hs0 : in_futures bvlsm s0 s).
    { exists l2. split; try assumption.
      rewrite map_app in Hs. rewrite map_cons in Hs.
      rewrite last_app in Hs. rewrite unroll_last in Hs.
      simpl in Hs.
      assumption.
    }
    apply (get_messages_in_futures s0 s Hs0).
    destruct H3 as [Hs0' _]. subst s0.
    apply set_add_iff. left. reflexivity.
  Qed.

  Definition client_has_not_been_sent
    (s : set message)
    (m : message)
    : bool
    :=
    negb (client_has_been_sent s m).

  Lemma VLSM_full_client_proper_not_sent
    (s : set message)
    (Hs : protocol_state_prop bvlsm s)
    (m : message)
    : has_not_been_sent_prop vlsm client_has_not_been_sent s m.
  Proof.
    unfold has_not_been_sent_prop. unfold no_traces_have_message_prop.
    unfold client_has_not_been_sent. simpl.
    split; intros; try reflexivity.
    intros.
    rewrite <- Forall_Exists_neg.
    apply Forall_forall.
    intros item Hitem Hm.
    apply (has_been_sent_in_trace s m start tr Htr item Hitem Hm Hlast).
  Qed.

  Definition VLSM_full_client_has_been_sent
    : has_been_sent_capability VLSM_full_client2
    :=
    {| has_been_sent := client_has_been_sent
     ; proper_sent := VLSM_full_client_proper_sent
     ; proper_not_sent := VLSM_full_client_proper_not_sent
    |}.

  Lemma VLSM_full_client_proper_received
    (s : set message)
    (Hs : protocol_state_prop bvlsm s)
    (m : message)
    : has_been_received_prop vlsm client_has_been_received s m.
  Proof.
    unfold has_been_received_prop. unfold all_traces_have_message_prop.
    unfold client_has_been_received.
    pose (in_correct s m) as Hin. rewrite <- Hin. clear Hin.
    split; intros.
    - apply Exists_exists.
      destruct Htr as [Htr Hinit].
      assert (Hstart : ~In m start).
      { inversion Hinit. simpl. intro n. contradiction n. }
      clear -H Htr Hlast Hstart bvlsm.
      generalize dependent start.
      induction tr; intros.
      + simpl in Hlast. subst start. elim Hstart. assumption.
      + inversion Htr. clear Htr. subst s' a tl.
        rewrite map_cons in Hlast. rewrite unroll_last in Hlast. simpl in Hlast.
        assert (Hfutures : in_futures bvlsm s0 s)
          by (exists tr; split; assumption).
        specialize (IHtr s0 H3 Hlast).
        destruct (in_dec eq_dec m s0).
        * destruct H4 as [_ Ht]. simpl in Ht. unfold vtransition in Ht. simpl in Ht.
          exists {| l := l; input := iom; destination := s0; output := oom |}.
          split; try (left; reflexivity). simpl.
          {destruct iom as [msg|]; inversion Ht; subst; clear Ht.
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
  Qed.

  Definition client_has_not_been_received
    (s : set message)
    (m : message)
    : bool
    :=
    negb (client_has_been_received s m).

  Lemma VLSM_full_client_proper_not_received
    (s : set message)
    (Hs : protocol_state_prop bvlsm s)
    (m : message)
    : has_not_been_received_prop vlsm client_has_not_been_received s m.
  Proof.
    unfold has_not_been_received_prop. unfold no_traces_have_message_prop.
    unfold client_has_not_been_received. rewrite Bool.negb_true_iff.
    unfold client_has_been_received.
    pose (in_correct' s m) as Hin.
    rewrite <- Hin. clear Hin.
    split.
    - intros.
      rewrite <- Forall_Exists_neg.
      apply Forall_forall.
      intros item Hitem Hm.
      pose (has_been_received_in_trace s m start tr Htr item Hitem Hm Hlast).
      elim H. assumption.
    - pose (VLSM_full_client_proper_received s Hs m) as Hreceived.
      intro H. destruct Hs as [_om Hs].
      pose (protocol_is_trace bvlsm s _om Hs) as Htr.
      destruct Htr as [Hinit | [is [tr [Htr [Hlsts _]]]]].
      + inversion Hinit. intro Hin. inversion Hin.
      + assert (Hlst : last (map destination tr) is = s).
        { destruct tr as [|i tr]; inversion Hlsts.
          apply last_map.
        }
        specialize (H is tr Htr Hlst).
        intro Hbr.
        unfold has_been_received_prop in Hreceived.
        unfold all_traces_have_message_prop in Hreceived.
        unfold client_has_been_received in Hreceived.
        pose (in_correct s m) as Hin.
        rewrite <- Hin in Hreceived. clear Hin.
        rewrite Hreceived in Hbr.
        specialize (Hbr is tr Htr Hlst).
        elim H. assumption.
  Qed.

  Definition VLSM_full_client_has_been_received
    : has_been_received_capability VLSM_full_client2
    :=
    {| has_been_received := client_has_been_received
     ; proper_received := VLSM_full_client_proper_received
     ; proper_not_received := VLSM_full_client_proper_not_received
    |}.

End proper_sent_received.

End CompositeClient.
