From Coq Require Import Reals List ListSet.

From CasperCBC Require Import Preamble ListExtras ListSetExtras.

(** * Measure-related definitions and lemmas *)

Definition pos_R := {r : R | (r > 0)%R}.

Class Measurable V := { weight : V -> pos_R}.
Hint Mode Measurable ! : typeclass_instances.

Definition sum_weights `{Measurable V} (l : list V) : R :=
  fold_right (fun v r => (proj1_sig (weight v) + r)%R) 0%R l.

Lemma sum_weights_positive
  `{Measurable V} (l : list V)
  : (0 <= sum_weights l)%R.
Proof.
  induction l; try apply Rle_refl.
  simpl. apply  Rplus_le_le_0_compat; try assumption.
  destruct (weight a). simpl.
  apply Rlt_le. assumption.
Qed.

Definition weight_proj1_sig (w : pos_R) : R := proj1_sig w.

Coercion weight_proj1_sig : pos_R >-> R.

Lemma sum_weights_in
  `{EqDecision V} `{Hm : Measurable V}
  : forall v (vs:list V),
  NoDup vs ->
  In v vs ->
  sum_weights vs = (proj1_sig (weight v) + sum_weights (set_remove decide_eq v vs))%R.
Proof.
  induction vs; intros; inversion H0; subst; clear H0.
  - inversion H; subst; clear H. simpl. apply Rplus_eq_compat_l.
    destruct (decide (v = v)); congruence.
  - inversion H; subst; clear H. simpl. assert (Hav := H3). apply (in_not_in _ _ _ _ H1) in Hav.
    destruct (decide (v = a)); try (exfalso; apply Hav; assumption). simpl.
    rewrite <- Rplus_assoc. rewrite (Rplus_comm (proj1_sig (weight v)) (proj1_sig (weight a))). rewrite Rplus_assoc.
    apply Rplus_eq_compat_l. apply IHvs; assumption.
Qed.

Lemma sum_weights_incl
  `{EqDecision V} `{Hm : Measurable V}
  : forall (vs vs':list V),
  NoDup vs ->
  NoDup vs' ->
  incl vs vs' ->
  (sum_weights vs <= sum_weights vs')%R.
Proof.
  induction vs; intros; try apply sum_weights_positive.
  specialize (sum_weights_in a vs' H0) as Hvs'.
  spec Hvs'; try (apply H1; left; reflexivity).
  rewrite Hvs'. simpl.
  apply Rplus_le_compat_l.
  inversion H. subst.  clear H.
  apply IHvs; try assumption.
  - apply set_remove_nodup. assumption.
  - intros v Hv. apply set_remove_iff; try assumption.
    split.
    + apply H1. right. assumption.
    + intro contra. elim H4. subst. assumption.
Qed.

Lemma set_eq_nodup_sum_weight_eq
  `{EqDecision V} `{Hm : Measurable V}
  : forall (lv1 lv2 : list V),
    NoDup lv1 ->
    NoDup lv2 ->
    set_eq lv1 lv2 ->
    sum_weights lv1 = sum_weights lv2.
Proof.
  intros lv1 lv2 H_nodup1 H_nodup2 [H_eq_l H_eq_r].
  assert (H_useful := sum_weights_incl lv1 lv2 H_nodup1 H_nodup2 H_eq_l).
  assert (H_useful' := sum_weights_incl lv2 lv1 H_nodup2 H_nodup1 H_eq_r).
  now apply Rle_antisym.
Qed.

Lemma sum_weights_app
  `{Hm : Measurable V}
  : forall (vs vs':list V),
  sum_weights (vs ++ vs') = (sum_weights vs + sum_weights vs')%R.
Proof.
  induction vs; intros; simpl.
  - rewrite Rplus_0_l. reflexivity.
  - rewrite IHvs. rewrite Rplus_assoc. reflexivity.
Qed.
