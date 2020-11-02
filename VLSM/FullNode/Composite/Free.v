Require Import PeanoNat Lia FinFun Fin List ListSet RelationClasses Reals.

Import ListNotations.

From CasperCBC
  Require Import
    Preamble
    ListExtras
    ListSetExtras
    CBC.Common
    VLSM.Common
    VLSM.Composition
    VLSM.ProjectionTraces
    VLSM.ObservableEquivocation
    Validator.State
    FullNode.Client
    FullNode.Validator
    Validator.Equivocation
    CBC.Equivocation
    .

Section ClientsAndValidators.

(** * Full-node VLSM clients and validators  free composition
*)

  Context
    {C V : Type}
    {about_C : StrictlyComparable C}
    {about_V : StrictlyComparable V}
    {Hmeasurable : Measurable V}
    {Hrt : ReachableThreshold V}
    {Hestimator : Estimator (state C V) C}
    (message := State.message C V)
    (message_preceeds := validator_message_preceeds C V)
    (message_preceeds_dec := validator_message_preceeds_dec C V)
    .
Parameter clients : Type.
Parameter clients_eq_dec : EqDecision clients.
Let index : Type := V + clients.
Parameter i0 : index.

Existing Instance clients_eq_dec.

Let v_eq_dec := @strictly_comparable_eq_dec _ about_V.
Existing Instance v_eq_dec.

Instance index_eq_dec : EqDecision index.
Proof.
  intros [v | c] [v' | c'].
  - destruct (decide (v = v')).
    + subst. left. reflexivity.
    + right. intro H. elim n. inversion H. reflexivity.
  - right. intro H. discriminate H.
  - right. intro H. discriminate H.
  - destruct (decide (c = c')).
    + subst. left. reflexivity.
    + right. intro H. elim n. inversion H. reflexivity.
Defined.

(**
In order to create a composition of clients and validators
we assume a set of validators names <<V>> and a set of client
identifiers <<clients>>, and let <<index>> be their disjoint union.

We define a set of VLSMs indexed by <<index>>, associating to
validator names the validator VLSM identifying as that name,
and to client identifiers.
*)

Definition IM_index
  (i : index)
  : VLSM message
  :=
  match i with
  | inl v => VLSM_full_validator v
  | _ => VLSM_full_client2
  end.

Definition VLSM_full_composed_free : VLSM message
  := free_composite_vlsm IM_index i0.

Definition project
  (s : vstate VLSM_full_composed_free)
  (i : index)
  : state C V
  :=
  match i with
  | inl v => s (inl v)
  | inr c => pair (s (inr c)) None
  end.

Lemma pre_free_protocol_transition_out
  (l : label)
  (is os : vstate VLSM_full_composed_free)
  (iom : option message)
  (m : message)
  (Ht :
    protocol_transition (pre_loaded_with_all_messages_vlsm VLSM_full_composed_free)
      l (is, iom) (os, Some m)
  )
  : projT1 l = inl (State.sender m)
  /\ State.get_justification m = make_justification (project is (projT1 l))
  /\ In m (State.get_message_set (project os (projT1 l))).
Proof.
  destruct Ht as [Hv Ht]. simpl in Ht. unfold vtransition in Ht.
  simpl in Ht.
  destruct l as [il l].
  destruct (vtransition (IM_index il) l (is il, iom)) as (os', om') eqn:Hvt.
  inversion Ht. subst. clear Ht. simpl in *.
  destruct il; simpl in Hvt.
  - apply vtransitionv_inv_out in Hvt.
    destruct Hvt as [Hos' [Hj [Hsender _]]].
    subst.
    repeat split; try reflexivity; try assumption.
    simpl. rewrite state_update_eq. simpl. apply set_add_iff. left. reflexivity.
  - unfold vtransition in Hvt. simpl in Hvt.
    destruct iom; inversion Hvt.
Qed.

Lemma free_protocol_transition_out
  (l : label)
  (is os : vstate VLSM_full_composed_free)
  (iom : option message)
  (m : message)
  (Ht :
    protocol_transition VLSM_full_composed_free
      l (is, iom) (os, Some m)
  )
  : projT1 l = inl (State.sender m)
  /\ State.get_justification m = make_justification (project is (projT1 l))
  /\ In m (State.get_message_set (project os (projT1 l))).
Proof.
  destruct Ht as [Hv Ht]. simpl in Ht.
  destruct l as [il l].
  destruct (vtransition (IM_index il) l (is il, iom)) as (os', om') eqn:Hvt.
  inversion Ht. subst. clear Ht. simpl in *.
  destruct il; simpl in Hvt.
  - apply vtransitionv_inv_out in Hvt.
    destruct Hvt as [Hos' [Hj [Hsender _]]].
    subst.
    repeat split; try reflexivity; try assumption.
    simpl. rewrite state_update_eq. simpl. apply set_add_iff. left. reflexivity.
  - unfold vtransition in Hvt. simpl in Hvt.
    destruct iom; inversion Hvt.
Qed.

Lemma VLSM_full_protocol_state_nodup
  (s : vstate VLSM_full_composed_free)
  (Hs : protocol_state_prop (pre_loaded_with_all_messages_vlsm VLSM_full_composed_free) s)
  (i : index)
  : NoDup (get_message_set (project s i)).
Proof.
  pose (preloaded_composed_protocol_state IM_index i0 s Hs i) as Hi.
  destruct i as [v | client]; simpl.
  - apply (validator_protocol_state_nodup v). assumption.
  - apply client_protocol_state_nodup. assumption.
Qed.

Definition  free_full_byzantine_message_preceeds
  (pm1 pm2 : byzantine_message VLSM_full_composed_free)
  : Prop
  := validator_message_preceeds _ _ (proj1_sig pm1) (proj1_sig pm2).

Lemma free_full_byzantine_message_preceeds_irreflexive
  : Irreflexive free_full_byzantine_message_preceeds.
Proof.
  intros (x, Hx).
  unfold complement; unfold free_full_byzantine_message_preceeds; simpl.
  apply validator_message_preceeds_irreflexive.
Qed.

Lemma free_byzantine_message_justification
  (m : message)
  (Hm : byzantine_message_prop VLSM_full_composed_free m)
  (j := get_justification m)
  : exists
    (s : vstate VLSM_full_composed_free)
    (Hs : protocol_state_prop (pre_loaded_with_all_messages_vlsm VLSM_full_composed_free) s)
    (i : index)
    (v : V),
    i = inl v /\  make_justification (project s i) = j.
Proof.
  destruct Hm as [(s0, om0) [l [s [[[_om0 Hs0] [[_s0 Hom0] Hv]] Ht]]]].
  exists s0.
  assert (Hpsp : protocol_state_prop (pre_loaded_with_all_messages_vlsm VLSM_full_composed_free) s0)
    by (exists _om0; assumption).
  exists Hpsp.
  simpl in Ht.
  unfold vtransition in Ht. simpl in Ht.
  unfold vtransition in Ht.
  destruct l as (i, li).
  exists i.
  destruct i.
  - exists v. split; try reflexivity. simpl.
    destruct (s0 (inl v)) as (msgs, final) eqn: Hsv.
    simpl in Ht.
    destruct li as [c|].
    + apply pair_equal_spec in Ht. destruct Ht as [Hs Hom]; subst.
      inversion Hom. subst m. unfold j. reflexivity.
    + destruct om0; discriminate Ht.
  - exfalso.
    simpl in Ht.
    destruct om0; discriminate Ht.
Qed.

Lemma in_free_byzantine_state_justification
  (s : vstate VLSM_full_composed_free)
  (Hs : protocol_state_prop (pre_loaded_with_all_messages_vlsm VLSM_full_composed_free) s)
  (m : message)
  (v : index)
  (Hm : In m (get_message_set (project s v)))
  : incl (get_message_set (unmake_justification (get_justification m))) (get_message_set (project s v)).
Proof.
  destruct  Hs as [om Hsom].
  remember
    (@pair (@Common.state message (@type message (@pre_loaded_with_all_messages_vlsm message VLSM_full_composed_free))) (option message)
      s om)
    as som.
  generalize dependent v.
  generalize dependent m.
  generalize dependent om.
  generalize dependent s.
  induction Hsom; intros; inversion Heqsom; subst; clear Heqsom.
  - unfold s in *; clear s. destruct is as [is His]. simpl in *.
    specialize (His v).
    destruct v
    ; simpl in Hm; inversion His
    ; rewrite H0 in Hm
    ; inversion Hm
    .
  - unfold s in *; clear s. destruct s0 as [is His]. simpl in *.
    specialize (His v).
    destruct v
    ; simpl in Hm; inversion His
    ; rewrite H0 in Hm
    ; inversion Hm
    .
  - unfold vtransition in H0. simpl in H0.
    destruct l as (v', lv').
    { destruct v' as [v' | client'].
    - destruct (s (inl v')) as (msgsv', finalv') eqn:Hsv'.
      unfold vtransition in H0. simpl in H0.
      destruct lv' as [c|].
      + apply pair_equal_spec in H0. destruct H0 as [Hs Hom]; subst.
        destruct (decide (v = inl v')); subst; simpl in *.
        * rewrite state_update_eq in *. simpl in Hm.
          apply set_add_iff in Hm.
          { destruct Hm as [Heqm | Hinm]; subst.
          - specialize (make_unmake_message_set_eq msgsv'); intros [Hincl _].
            simpl. destruct finalv'; simpl
            ; apply incl_tran with msgsv'; try assumption
            ; intros x Hx; rewrite set_add_iff
            ; right; assumption
            .
          - specialize (IHHsom1  s _om eq_refl m (inl v')).
            simpl in IHHsom1.
            rewrite Hsv' in IHHsom1.
            specialize (IHHsom1 Hinm).
            apply incl_tran with msgsv'; try assumption.
            intros x Hx. simpl. rewrite set_add_iff.
            right; assumption.
          }
        * specialize (IHHsom1  s _om eq_refl m v).
          destruct v
          ; simpl in Hm; rewrite state_update_neq in Hm; try assumption
          ; simpl; rewrite state_update_neq; try assumption
          ; apply IHHsom1 ; assumption.
      + destruct om as [m'|].
        * apply pair_equal_spec in H0.  destruct H0 as [Hs Hom]; subst.
          { destruct (decide (v = inl v')); subst.
          - simpl in Hm. rewrite state_update_eq in Hm. simpl. rewrite state_update_eq.
            apply set_add_iff in Hm.
            destruct Hm as [Heqm | Hinm]; subst.
            + destruct Hv as [Hv _]. simpl in Hv.
              rewrite Hsv' in Hv. destruct Hv as [Hnin Hincl].
              apply incl_tran with msgsv'; try assumption.
              intros x Hx. simpl. rewrite set_add_iff.
              right; assumption.
            + specialize (IHHsom1  s _om eq_refl m (inl v')).
              simpl in IHHsom1.
              rewrite Hsv' in IHHsom1; simpl in IHHsom1.
              specialize (IHHsom1 Hinm).
              apply incl_tran with msgsv'; try assumption.
              intros x Hx. simpl. rewrite set_add_iff.
              right; assumption.
          - specialize (IHHsom1  s _om eq_refl m v).
            destruct v
            ; simpl in Hm; rewrite state_update_neq in Hm; try assumption
            ; simpl; rewrite state_update_neq; try assumption
            ; apply IHHsom1; assumption.
          }
      * apply pair_equal_spec in H0.  destruct H0 as [Hs Hom]; subst.
        rewrite state_update_id in Hm; try assumption.
        rewrite state_update_id; try assumption.
        apply (IHHsom1  s _om eq_refl m v).
        assumption.
    - unfold vtransition in H0. simpl in H0.
      specialize (IHHsom1 s _om eq_refl m v).
      destruct om as [msg|]; inversion H0; subst; clear H0; destruct v as [v | client]
      ; simpl in Hm.
      + rewrite state_update_neq in Hm by (intro H; discriminate H).
        simpl.
        rewrite state_update_neq by (intro H; discriminate H).
        apply IHHsom1.
        assumption.
      + destruct (decide (inr client = inr client')).
        * inversion e. subst.
          rewrite state_update_eq in Hm. simpl in Hm.
          simpl; rewrite state_update_eq.
          apply set_add_iff in Hm.
          simpl in IHHsom1.
          { destruct Hm as [Heq | Hm].
          - subst msg.
            destruct Hv as [Hv _]. simpl in Hv.
            unfold vvalid in Hv. simpl in Hv.
            destruct Hv as [_ [Hv _]].
            apply incl_tran with (s (inr client')); try assumption.
            intros msg Hmsg. apply set_add_iff. right. assumption.
          - specialize (IHHsom1 Hm).
            apply incl_tran with (s (inr client')); try assumption.
            intros msg' Hmsg'. apply set_add_iff. right. assumption.
          }
        * rewrite state_update_neq in Hm; try assumption.
          simpl. rewrite state_update_neq; try assumption.
          apply IHHsom1. assumption.
      + rewrite state_update_neq in Hm by (intro H; discriminate H).
        simpl.
        rewrite state_update_neq by (intro H; discriminate H).
        apply IHHsom1.
        assumption.
      + simpl. simpl in IHHsom1. destruct (decide (inr client = inr client')).
        * inversion e. subst.
          rewrite state_update_eq in Hm. simpl in Hm.
          simpl; rewrite state_update_eq.
          apply IHHsom1. assumption.
        * rewrite state_update_neq in Hm; try assumption.
          simpl. rewrite state_update_neq; try assumption.
          apply IHHsom1. assumption.
    }
Qed.

Lemma free_full_byzantine_message_preceeds_justification_incl
  (y z : byzantine_message VLSM_full_composed_free)
  (Hyz : free_full_byzantine_message_preceeds y z)
  (jy := get_justification (proj1_sig y))
  (jz := get_justification (proj1_sig z))
  : justification_incl jy jz.
Proof.
  unfold jy; clear jy. unfold jz; clear jz.
  destruct y as (y, Hy).
  destruct z as (z, Hz).
  unfold free_full_byzantine_message_preceeds in Hyz.
  simpl in *.
  specialize (free_byzantine_message_justification z Hz); intros [jz [Hpjz [i [v [Heq Hjz]]]]].
  subst i.
  unfold validator_message_preceeds in Hyz.
  destruct z as (cz, vz, jz'); simpl in Hyz.
  simpl in Hjz; subst.
  specialize
    (in_correct
      (unmake_message_set (justification_message_set (make_justification (jz (inl v)))))
      y
    ); intro Hin_in
  ; apply proj2 in Hin_in
  ; apply Hin_in in Hyz; clear Hin_in.
  apply in_unmake_message_set in Hyz.
  apply in_make_justification in Hyz.
  specialize (in_free_byzantine_state_justification jz Hpjz y (inl v) Hyz)
  ; intro Hincljyjz.
  simpl.
  intros m Hm.
  apply in_make_justification.
  apply Hincljyjz.
  apply in_unmake_justification.
  assumption.
Qed.

Lemma free_full_byzantine_message_preceeds_transitive
  : Transitive free_full_byzantine_message_preceeds.
Proof.
  intros x y z Hxy Hyz.
  specialize
    (free_full_byzantine_message_preceeds_justification_incl
      y z Hyz
    ); simpl; intro Hinclyz.
  destruct x as ((cx, vx, jx), Hx).
  destruct y as ((cy, vy, jy), Hy).
  destruct z as ((cz, vz, jz), Hz).
  unfold free_full_byzantine_message_preceeds in *; simpl in *.
  unfold validator_message_preceeds in *.
  unfold validator_message_preceeds_fn in *.
  specialize
    (in_correct
      (get_message_set (unmake_justification jy))
      ((cx, vx, jx))
    ); intro Hin_in
  ; apply proj2 in Hin_in
  ; apply Hin_in in Hxy; clear Hin_in.
  apply in_unmake_justification in Hxy.
  apply Hinclyz in Hxy.
  specialize
    (in_correct
      (get_message_set (unmake_justification jz))
      ((cx, vx, jx))
    ); intro Hin_in
  ; apply proj1 in Hin_in
  ; apply Hin_in; clear Hin_in.
  apply in_unmake_justification.
  assumption.
Qed.

Definition free_full_byzantine_message_preceeds_stict_order
  : StrictOrder free_full_byzantine_message_preceeds.
Proof.
  split.
  apply free_full_byzantine_message_preceeds_irreflexive.
  apply free_full_byzantine_message_preceeds_transitive.
Defined.

Lemma full_composed_free_sent_messages_comparable'
  (s : vstate VLSM_full_composed_free)
  (tr : list (vtransition_item VLSM_full_composed_free))
  (Htr : finite_protocol_trace (pre_loaded_with_all_messages_vlsm VLSM_full_composed_free) s tr)
  (m1 m2 : message)
  (Hvalidator : State.sender m1 = State.sender m2)
  (item1 item2 : vtransition_item VLSM_full_composed_free)
  (prefix middle suffix: list (vtransition_item VLSM_full_composed_free))
  (Heq: tr = prefix ++ [item1] ++ middle ++ [item2] ++ suffix)
  (Hm1: output item1 = Some m1)
  (Hm2: output item2 = Some m2)
  : validator_message_preceeds _ _ m1 m2.
Proof.
  unfold validator_message_preceeds.
  unfold validator_message_preceeds_fn.
  destruct m2 as (c2, v2, j2).
  subst tr.
  destruct Htr as [Htr Hinit].
  rewrite <- finite_protocol_trace_from_app_iff in Htr.
  destruct Htr as [Hpre Htr].
  rewrite app_assoc  in Htr.
  rewrite <- finite_protocol_trace_from_app_iff in Htr.
  destruct Htr as [Htr1 Htr2].
  inversion Htr1. subst. clear Htr1.
  simpl in Hm1. subst.
  rewrite map_app in Htr2.
  rewrite last_app in Htr2. simpl in Htr2.
  apply pre_free_protocol_transition_out in H3.
  destruct H3 as [Hl [_ Hm1]].
  simpl in Hvalidator. rewrite Hvalidator in Hl.
  destruct l as [il l1]. simpl in Hl. subst il. simpl in *.
  apply in_correct.
  inversion Htr2; subst. clear Htr2 H3. simpl in Hm2. subst oom.
  apply pre_free_protocol_transition_out in H4.
  destruct H4 as [Hl [Hj2 Hm2]].
  destruct l as [il l2]. simpl in Hl. subst il. simpl in *.
  subst j2.
  apply in_unmake_message_set.
  apply in_make_justification.
  apply
    (@get_messages_in_futures C V about_C about_V Hestimator
      (State.sender m1) (s0 (inl (State.sender m1)))
      (last (map destination middle) s0 (inl (State.sender m1)))
    ); try assumption.
  specialize
    (pre_loaded_with_all_messages_projection_in_futures IM_index i0 s0 (last (map destination middle) s0))
    as Hproj.
  spec Hproj; try (specialize (Hproj (inl (State.sender m1))); apply Hproj).
  exists middle.
  split; try assumption.
  reflexivity.
Qed.

Lemma full_composed_free_sent_messages_comparable
  (s : vstate VLSM_full_composed_free)
  (tr : list transition_item)
  (Htr : finite_protocol_trace (pre_loaded_with_all_messages_vlsm VLSM_full_composed_free) s tr)
  (m1 m2 : message)
  (Hvalidator : sender m1 = sender m2)
  (Hm1 : Equivocation.trace_has_message VLSM_full_composed_free output m1 tr)
  (Hm2 : Equivocation.trace_has_message VLSM_full_composed_free output m2 tr)
  : m1 = m2 \/ validator_message_preceeds _ _ m1 m2 \/ validator_message_preceeds _ _ m2 m1.
Proof.
  unfold Equivocation.trace_has_message in *.
  apply Exists_exists in Hm1. destruct Hm1 as [item1 [Hitem1 Hm1]].
  apply Exists_exists in Hm2. destruct Hm2 as [item2 [Hitem2 Hm2]].
  apply in_split in Hitem1.
  destruct Hitem1 as [prefix1 [suffix1 Hitem1]].
  rewrite Hitem1 in Hitem2.
  apply in_app_iff in Hitem2.
  specialize (full_composed_free_sent_messages_comparable' s tr Htr) as Hcomparable.
  destruct Hitem2 as [Hitem2 | [Heq | Hitem2]]
  ; try
    (apply in_split in Hitem2; destruct Hitem2 as [prefix2 [suffix2 Hitem2]]
    ; rewrite Hitem2 in Hitem1; clear Hitem2
    ).
  - right. right. symmetry in Hvalidator. rewrite <- app_assoc in Hitem1. subst tr.
    apply
      (Hcomparable m2 m1 Hvalidator item2 item1 prefix2 suffix2 suffix1 eq_refl Hm2 Hm1).
  - left. subst. rewrite Hm1 in Hm2. inversion Hm2. reflexivity.
  - right. left. subst tr.
    apply
      (Hcomparable m1 m2 Hvalidator item1 item2 prefix1 prefix2 suffix2 eq_refl Hm1 Hm2).
Qed.

Definition free_observation_based_equivocation_evidence_index
  (i : index)
  : observation_based_equivocation_evidence
        (vstate (IM_index i)) V message message_eq _ message_preceeds_dec.
Proof.
  destruct i.
  - apply full_node_validator_observation_based_equivocation_evidence.
  - apply full_node_client_observation_based_equivocation_evidence.
Defined.

Parameter indices : list index.
Parameter finite_index : Listing indices.

Definition validators : list V
  := flat_map (fun i : index => match i with inl v => [v] | _ => [] end) indices.

Lemma finite_validators : Listing validators.
Proof.
  split.
  - unfold validators. assert (Hnodup := proj1 finite_index).
    induction indices.
    + constructor.
    + simpl. inversion Hnodup; subst. specialize (IHl H2).
      destruct a; try assumption.
      simpl. constructor; try assumption.
      intro contra.
      apply in_flat_map in contra.
      destruct contra as [[iv| ic] [Hi Hv]].
      * destruct Hv as [Heq | Hcontra]; try inversion Hcontra.
        subst iv. elim H1. assumption.
      * inversion Hv.
  - intro v. specialize (proj2 finite_index (inl v)) as Hv.
    apply in_flat_map. exists (inl v).
    split; try assumption. left. reflexivity.
Qed.

Definition composed_equivocation_evidence
  : observation_based_equivocation_evidence (vstate VLSM_full_composed_free) V message message_eq message_preceeds message_preceeds_dec
  := @composed_observation_based_equivocation_evidence message V message message_eq message_preceeds message_preceeds_dec index indices IM_index free_observation_based_equivocation_evidence_index.

Existing Instance composed_equivocation_evidence.

Definition composed_basic_observable_equivocation
  : basic_equivocation (vstate VLSM_full_composed_free) V
  := @composed_observable_basic_equivocation
      message V message message_eq message_preceeds message_preceeds_dec
      index indices IM_index
      free_observation_based_equivocation_evidence_index
      Hmeasurable Hrt
      (fun s => validators)
      (fun s => proj1 finite_validators).


Program Instance free_composite_vlsm_observable_messages
  : composite_vlsm_observable_messages indices IM_index free_observation_based_equivocation_evidence_index i0 (free_constraint IM_index)
  :=
  {
    message_observable_events := full_message_observable_messages
  }.
Next Obligation.
  apply set_union_iterated_empty. intros msgsi Hmsgsi.
  apply in_map_iff in Hmsgsi. destruct Hmsgsi as [i [Hmsgsi _]].
  subst.
  specialize (free_observation_based_equivocation_evidence_index i) as Hev.
  specialize (His i). unfold IM_index in *.
  destruct i; inversion His; rewrite H0; reflexivity.
Qed.
Next Obligation.
  apply free_protocol_transition_out in Ht.
  destruct Ht as [Hl [Hj Hm]].
  destruct l as (i, l). unfold full_message_observable_messages.
  simpl in *.

  destruct i as [v0|c]; try discriminate Hl.
  inversion Hl. subst. clear Hl.
  destruct (decide (v = sender m)); try apply incl_nil_l.
  subst. simpl.
  intros m' Hm'.
  destruct Hm' as [Hm' | contra]; try inversion contra.
  subst m'.
  apply filter_In. split; try assumption.
  rewrite decide_True; auto.
Qed.

Existing Instance message_eq.
Existing Instance message_preceeds_dec.

(**
Equivocation is defined as non-heaviness of the full set of exchanged messages.
[state_union] extracts that set from a composite state.
*)

Definition state_union
  (s : vstate VLSM_full_composed_free)
  : set message
  :=
  fold_right (set_union compare_eq_dec) []
    (map (fun v : V => observable_events s v) validators).

Lemma state_union_nodup
  (s : vstate VLSM_full_composed_free)
  (Hs : protocol_state_prop (pre_loaded_with_all_messages_vlsm VLSM_full_composed_free) s)
  : NoDup (state_union s).
Proof.
  apply set_union_iterated_nodup.
  intros msgsi Hmsgsi.
  apply in_map_iff in Hmsgsi.
  destruct Hmsgsi as [v [Hmsgsv _]]. subst.
  simpl. unfold composed_observable_events.
  apply set_union_iterated_nodup.
  intros msgsi Hmsgsi.
  apply in_map_iff in Hmsgsi.
  destruct Hmsgsi as [i [Hmsgsi _]]. subst.
  pose (preloaded_composed_protocol_state IM_index i0 s Hs i) as Hi.
  destruct i; simpl; apply NoDup_filter.
  + apply validator_protocol_state_nodup with v0. assumption.
  + apply client_protocol_state_nodup. assumption.
Qed.

Lemma state_union_iff
  (s : vstate VLSM_full_composed_free)
  (m : message)
  : In m (state_union s)
    <-> ex (fun v : V => In m (get_message_set (s (inl v))))
    \/ ex (fun client : clients => In m (s (inr client))).
Proof.
  split.
  - intros Hm.
    apply set_union_in_iterated in Hm.
    apply Exists_exists in Hm.
    destruct Hm as [msgs [Hmsgs Hm]].
    apply in_map_iff in Hmsgs.
    destruct Hmsgs as [v [Heq _]]. subst msgs.
    simpl in Hm.
    apply set_union_in_iterated in Hm.
    apply Exists_exists in Hm.
    destruct Hm as [msgs [Hmsgs Hm]].
    apply in_map_iff in Hmsgs.
    destruct Hmsgs as [i [Heq _]]. subst msgs.
    destruct i; simpl in Hm; apply filter_In in Hm; destruct Hm as [Hm Hsender].
    + left. exists v0. assumption.
    + right. exists c. assumption.
  - intro H.
    apply set_union_in_iterated.
    apply Exists_exists.
    exists (@observable_events _ _ _ _ _ _ composed_equivocation_evidence s (sender m)).
    split.
    + apply in_map_iff. exists (sender m). split; try reflexivity.
      apply (proj2 finite_validators).
    + simpl. apply set_union_in_iterated. apply Exists_exists.
      destruct H as [[v Hm] | [client Hm]]
      ; exists (@observable_events _ _ _ _ _ _ full_node_validator_observation_based_equivocation_evidence (s (inl v)) (sender m))
      || exists (@observable_events _ _ _ _ _ _ full_node_client_observation_based_equivocation_evidence (s (inr client)) (sender m))
      ; split; try (apply in_map_iff; exists (inl v) || exists (inr client); split; try reflexivity; apply (proj2 finite_index))
      ; simpl; apply filter_In; split; try assumption
      ; rewrite decide_True; auto.
Qed.

Lemma state_union_initially_empty
  (is : vinitial_state VLSM_full_composed_free)
  : state_union (proj1_sig is) = [].
Proof.
  apply incl_l_nil.
  intros m Hm.
  apply state_union_iff in Hm.
  destruct Hm as [[v Hm] | [client Hm]]
  ; destruct is as [is His]
  ; simpl in Hm
  ; specialize (His (inl v)) || specialize (His (inr client))
  ; simpl in His
  ; unfold initial_state_prop in His
  ;  rewrite His in Hm
  ; inversion Hm.
Qed.

Existing Instance composed_basic_observable_equivocation.

Let client_equivocation := @client_basic_equivocation C V about_C about_V Hmeasurable Hrt.

Existing Instance client_equivocation.

Lemma observable_event_sender
  (s : vstate VLSM_full_composed_free)
  (v : V)
  (m : message)
  (Hm : In m (observable_events s v))
  : sender m = v.
Proof.
  simpl in Hm. unfold composed_observable_events in Hm.
  apply set_union_in_iterated in Hm. apply Exists_exists in Hm.
  destruct Hm as [msgsi [Hmsgsi Hm]].
  apply in_map_iff in Hmsgsi. destruct Hmsgsi as [i [Heq _]]. subst.
  destruct i as [v0 | client]; simpl in Hm; apply filter_In in Hm;
  destruct Hm as [Hm Hsender];
  destruct (decide (sender m = v)); try discriminate Hsender
  ; assumption.
Qed.

Lemma observable_events_commute
  (s : vstate VLSM_full_composed_free)
  (v : V)
  : set_eq (observable_events s v) (@observable_events _ _ _ _ _  _ full_node_client_observation_based_equivocation_evidence (state_union s) v).
Proof.
  split; intros m Hm.
  - simpl.
    apply filter_In.
    split.
    + apply set_union_in_iterated. apply Exists_exists.
      exists (@observable_events _ _ _ _ _ _  composed_equivocation_evidence s v).
      split; try assumption.
      apply in_map_iff. exists v. split; try reflexivity.
      apply (proj2 finite_validators).
    + rewrite decide_True; try reflexivity. apply observable_event_sender with s.
      assumption.
  - simpl in Hm. apply filter_In in Hm.
    destruct Hm as [Hm Hsender].
    apply set_union_in_iterated in Hm. apply Exists_exists in Hm.
    destruct Hm as [msgsi [Hmsgsi Hm]].
    apply in_map_iff in Hmsgsi. destruct Hmsgsi as [v0 [Heq _]]. subst.
    replace v with v0; try assumption.
    destruct (decide (sender m = v)); try discriminate Hsender. subst.
    symmetry. apply  observable_event_sender with s. assumption.
Qed.

Lemma not_heavy_commute
  (s : vstate VLSM_full_composed_free)
  (Hnheavy : not_heavy s)
  : not_heavy (state_union s).
Proof.
  unfold not_heavy in *.
  apply Rle_trans with (equivocation_fault s);[clear Hnheavy|assumption].
  unfold equivocation_fault.
  apply sum_weights_incl;
    [apply NoDup_filter, set_map_nodup
    |apply NoDup_filter, finite_validators
    |];[].
  unfold equivocating_validators.

  apply incl_tran with (filter (is_equivocating_fn (state_union s)) (state_validators s)).
  * apply filter_incl. intros v Hv. apply finite_validators.

  * apply filter_incl_fn.
    simpl. intro v.
    rewrite !bool_decide_eq_true.
    unfold equivocation_evidence.
    intro H.
    setoid_rewrite observable_events_commute.
    exact H.
Qed.

End ClientsAndValidators.
