Require Import PeanoNat Lia FinFun Fin List ListSet RelationClasses.

Import ListNotations.

From CasperCBC
  Require Import
    Preamble
    ListExtras
    CBC.Common
    VLSM.Common
    VLSM.Composition
    VLSM.PreceedsEquivocation
    Validator.State
    FullNode.Client
    FullNode.Validator
    Validator.Equivocation
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
    .
Parameter clients : Type.
Parameter clients_eq_dec : EqDec clients.
Let index : Type := V + clients.
Parameter i0 : index.

Existing Instance clients_eq_dec.

Let v_eq_dec := strictly_comparable_eq_dec about_V.
Existing Instance v_eq_dec.

Lemma index_eq_dec : EqDec index.
Proof.
  intros [v | c] [v' | c'].
  - destruct (eq_dec v v').
    + subst. left. reflexivity.
    + right. intro H. elim n. inversion H. reflexivity.
  - right. intro H. discriminate H.
  - right. intro H. discriminate H.
  - destruct (eq_dec c c').
    + subst. left. reflexivity.
    + right. intro H. elim n. inversion H. reflexivity.
Qed.

Existing Instance index_eq_dec.

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
  | inr c => s (inr c)
  end.

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
    (Hs : protocol_state_prop (pre_loaded_vlsm VLSM_full_composed_free) s)
    (i : index)
    (v : V),
    i = inl v /\  make_justification (project s i) = j.
Proof.
  destruct Hm as [(s0, om0) [l [s [[[_om0 Hs0] [[_s0 Hom0] Hv]] Ht]]]].
  exists s0.
  assert (Hpsp : protocol_state_prop (pre_loaded_vlsm VLSM_full_composed_free) s0)
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
    destruct (s0 (inr c)) as (msgs, final) eqn: Hsv.
    destruct om0; discriminate Ht.
Qed.

Lemma in_free_byzantine_state_justification
  (s : vstate VLSM_full_composed_free)
  (Hs : protocol_state_prop (pre_loaded_vlsm VLSM_full_composed_free) s)
  (m : message)
  (v : index)
  (Hm : In m (get_message_set (project s v)))
  : incl (get_message_set (unmake_justification (get_justification m))) (get_message_set (project s v)).
Proof.
  destruct  Hs as [om Hsom].
  remember
    (@pair (@Common.state message (@type message (@pre_loaded_vlsm message VLSM_full_composed_free))) (option message)
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
        destruct (eq_dec v (inl v')); subst; simpl in *.
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
          { destruct (eq_dec v (inl v')); subst.
          - simpl in Hm. rewrite state_update_eq in Hm. simpl. rewrite state_update_eq.
            apply set_add_iff in Hm.
            destruct Hm as [Heqm | Hinm]; subst.
            + destruct Hv as [Hv _]. simpl in Hv.
              rewrite Hsv' in Hv.
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
      destruct (s (inr client')) as (msgsv', finalv') eqn:Hsv'.
      specialize (IHHsom1 s _om eq_refl m v).
      destruct om as [msg|]; inversion H0; subst; clear H0; destruct v as [v | client]
      ; simpl in Hm.
      + rewrite state_update_neq in Hm by (intro H; discriminate H).
        simpl.
        rewrite state_update_neq by (intro H; discriminate H).
        apply IHHsom1.
        assumption.
      + destruct (eq_dec (inr client) (inr client')).
        * inversion e. subst.
          rewrite state_update_eq in Hm. simpl in Hm.
          simpl; rewrite state_update_eq.
          apply set_add_iff in Hm.
          simpl in IHHsom1.
          rewrite Hsv' in IHHsom1. simpl in IHHsom1.
          { destruct Hm as [Heq | Hm].
          - subst msg.
            destruct Hv as [Hv _]. simpl in Hv.
            unfold vvalid in Hv. simpl in Hv.
            destruct Hv as [Hv _].
            rewrite Hsv' in Hv. simpl in Hv.
            apply incl_tran with msgsv'; try assumption.
            simpl.
            intros msg Hmsg. apply set_add_iff. right. assumption.
          - specialize (IHHsom1 Hm).
            apply incl_tran with msgsv'; try assumption.
            simpl.
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
      + simpl. simpl in IHHsom1. destruct (eq_dec (inr client) (inr client')).
        * inversion e. subst.
          rewrite state_update_eq in Hm. simpl in Hm.
          simpl; rewrite state_update_eq.
          rewrite Hsv' in IHHsom1. simpl in IHHsom1.
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

Global Instance VLSM_full_composed_free_preceeds_equivocation
  : HasPreceedsEquivocation VLSM_full_composed_free.
Proof.
  split.
  apply free_full_byzantine_message_preceeds_stict_order.
Defined.


End ClientsAndValidators.
