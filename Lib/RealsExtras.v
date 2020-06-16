Require Import Coq.Reals.Reals.

(** This lemma is needed in fault_weight_state_backwards **)
Lemma Rplusminus_assoc : forall r1 r2 r3, 
  (r1 + r2 - r3)%R = (r1 + (r2 - r3))%R.
Proof.
  intros. unfold Rminus.
  apply Rplus_assoc.
Qed.

(** This lemma is needed in fault_weight_state_sorted_subset **)
Lemma Rplusminus_assoc_r : forall r1 r2 r3, 
  (r1 - r2 + r3)%R = (r1 + (- r2 + r3))%R.
Proof.
  intros. unfold Rminus.
  apply Rplus_assoc.
Qed.

(** This lemma is needed in fault_weight_state_sorted_subset **)
Lemma Rplus_opp_l : forall r, (Ropp r + r)%R = 0%R.
Proof.
  intros.
  rewrite Rplus_comm.
  apply Rplus_opp_r.
Qed.

(** This lemma is needed in fault_weight_state_sorted_subset **)
Lemma Rplus_ge_reg_neg_r : forall r1 r2 r3,
  (r2 <= 0)%R -> (r3 <= r1 + r2)%R -> (r3 <= r1)%R.
Proof.
  intros.
  apply Rge_le.
  apply Rle_ge in H.
  apply Rle_ge in H0.
  apply (Rplus_ge_reg_neg_r r1 r2 r3 H H0).
Qed.

(** This lemma is needed in fault_weight_state_sorted_subset **)
Lemma Rminus_lt_r : forall r1 r2,
  (0 <= r2)%R -> (r1 - r2 <= r1)%R.
Proof.
  intros.
  rewrite <- Rplus_0_r.
  unfold Rminus.
  apply Rplus_le_compat_l. 
  apply Rge_le.
  apply Ropp_0_le_ge_contravar.
  assumption.
Qed.

Lemma Rminus_lt_r_strict : forall r1 r2,
  (0 < r2)%R -> (r1 - r2 <= r1)%R.
Proof.
  intros.
  rewrite <- Rplus_0_r.
  unfold Rminus.
  apply Rplus_le_compat_l. 
  apply Rge_le.
  apply Ropp_0_le_ge_contravar.
  apply Rlt_le in H.
  assumption.
Qed.

Lemma Rtotal_le_gt : forall x y,
  (x <= y)%R \/ (x > y)%R.
Proof.
  intros.
  destruct (Rtotal_order x y) as [Hlt | [Heq | Hgt]].
  - left. unfold Rle. left. assumption.
  - left. unfold Rle. right. assumption.
  - right. assumption.
Qed.