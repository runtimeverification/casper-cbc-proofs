(** This file collects general purpose definitions and theorems on
lists of numbers that are not in the Coq standard library. *)
From stdpp Require Export list.
Set Default Proof Using "Type*".

(** * Definitions *)
(** [seqZ m n] generates the sequence [m], [m + 1], ..., [m + n - 1]
over integers, provided [0 ≤ n]. If [n < 0], then the range is empty. **)
Definition seqZ (m len: Z) : list Z :=
  (λ i: nat, Z.add i m) <$> (seq 0 (Z.to_nat len)).
Arguments seqZ : simpl never.

Definition sum_list_with {A} (f : A → nat) : list A → nat :=
  fix go l :=
  match l with
  | [] => 0
  | x :: l => f x + go l
  end.
Notation sum_list := (sum_list_with id).

Definition max_list_with {A} (f : A → nat) : list A → nat :=
  fix go l :=
  match l with
  | [] => 0
  | x :: l => f x `max` go l
  end.
Notation max_list := (max_list_with id).

(** * Properties *)
(** ** Properties of the [seq] function *)
Section seq.
  Implicit Types m n i j : nat.

  Lemma fmap_add_seq j j' n : Nat.add j <$> seq j' n = seq (j + j') n.
  Proof.
    revert j'. induction n as [|n IH]; intros j'; csimpl; [reflexivity|].
    by rewrite IH, Nat.add_succ_r.
  Qed.
  Lemma fmap_S_seq j n : S <$> seq j n = seq (S j) n.
  Proof. apply (fmap_add_seq 1). Qed.
  Lemma imap_seq {A B} (l : list A) (g : nat → B) i :
    imap (λ j _, g (i + j)) l = g <$> seq i (length l).
  Proof.
    revert i. induction l as [|x l IH]; [done|].
    csimpl. intros n. rewrite <-IH, <-plus_n_O. f_equal.
    apply imap_ext; simpl; auto with lia.
  Qed.
  Lemma imap_seq_0 {A B} (l : list A) (g : nat → B) :
    imap (λ j _, g j) l = g <$> seq 0 (length l).
  Proof. rewrite (imap_ext _ (λ i o, g (0 + i))); [|done]. apply imap_seq. Qed.
  Lemma lookup_seq_lt j n i : i < n → seq j n !! i = Some (j + i).
  Proof.
    revert j i. induction n as [|n IH]; intros j [|i] ?; simpl; auto with lia.
    rewrite IH; auto with lia.
  Qed.
  Lemma lookup_total_seq_lt j n i : i < n → seq j n !!! i = j + i.
  Proof. intros. by rewrite !list_lookup_total_alt, lookup_seq_lt. Qed.
  Lemma lookup_seq_ge j n i : n ≤ i → seq j n !! i = None.
  Proof. revert j i. induction n; intros j [|i] ?; simpl; auto with lia. Qed.
  Lemma lookup_total_seq_ge j n i : n ≤ i → seq j n !!! i = inhabitant.
  Proof. intros. by rewrite !list_lookup_total_alt, lookup_seq_ge. Qed.
  Lemma lookup_seq j n i j' : seq j n !! i = Some j' ↔ j' = j + i ∧ i < n.
  Proof.
    destruct (le_lt_dec n i).
    - rewrite lookup_seq_ge by done. naive_solver lia.
    - rewrite lookup_seq_lt by done. naive_solver lia.
  Qed.
  Lemma NoDup_seq j n : NoDup (seq j n).
  Proof. apply NoDup_ListNoDup, seq_NoDup. Qed.
  Lemma seq_S_end_app j n : seq j (S n) = seq j n ++ [j + n].
  Proof.
    revert j. induction n as [|n IH]; intros j; simpl in *; f_equal; [done |].
    by rewrite IH, Nat.add_succ_r.
  Qed.

  Lemma Forall_seq (P : nat → Prop) i n :
    Forall P (seq i n) ↔ ∀ j, i ≤ j < i + n → P j.
  Proof.
    rewrite Forall_lookup. split.
    - intros H j [??]. apply (H (j - i)), lookup_seq. lia.
    - intros H j x [-> ?]%lookup_seq. auto with lia.
  Qed.
End seq.

(** ** Properties of the [seqZ] function *)
Section seqZ.
  Implicit Types (m n : Z) (i j : nat).
  Local Open Scope Z.

  Lemma seqZ_nil m n : n ≤ 0 → seqZ m n = [].
  Proof. by destruct n. Qed.
  Lemma seqZ_cons m n : 0 < n → seqZ m n = m :: seqZ (Z.succ m) (Z.pred n).
  Proof.
    intros H. unfold seqZ. replace n with (Z.succ (Z.pred n)) at 1 by lia.
    rewrite Z2Nat.inj_succ by lia. f_equal/=.
    rewrite <-fmap_S_seq, <-list_fmap_compose.
    apply map_ext; naive_solver lia.
  Qed.
  Lemma seqZ_length m n : length (seqZ m n) = Z.to_nat n.
  Proof. unfold seqZ; by rewrite fmap_length, seq_length. Qed.
  Lemma fmap_add_seqZ m m' n : Z.add m <$> seqZ m' n = seqZ (m + m') n.
  Proof.
    revert m'. induction n as [|n ? IH|] using (Z_succ_pred_induction 0); intros m'.
    - by rewrite seqZ_nil.
    - rewrite (seqZ_cons m') by lia. rewrite (seqZ_cons (m + m')) by lia.
      f_equal/=. rewrite Z.pred_succ, IH; simpl. f_equal; lia.
    - by rewrite !seqZ_nil by lia.
  Qed.
  Lemma lookup_seqZ_lt m n i : i < n → seqZ m n !! i = Some (m + i).
  Proof.
    revert m i. induction n as [|n ? IH|] using (Z_succ_pred_induction 0);
      intros m i Hi; [lia| |lia].
    rewrite seqZ_cons by lia. destruct i as [|i]; simpl.
    - f_equal; lia.
    - rewrite Z.pred_succ, IH by lia. f_equal; lia.
  Qed.
  Lemma lookup_total_seqZ_lt m n i : i < n → seqZ m n !!! i = m + i.
  Proof. intros. by rewrite !list_lookup_total_alt, lookup_seqZ_lt. Qed.
  Lemma lookup_seqZ_ge m n i : n ≤ i → seqZ m n !! i = None.
  Proof.
    revert m i.
    induction n as [|n ? IH|] using (Z_succ_pred_induction 0); intros m i Hi; try lia.
    - by rewrite seqZ_nil.
    - rewrite seqZ_cons by lia.
      destruct i as [|i]; simpl; [lia|]. by rewrite Z.pred_succ, IH by lia.
    - by rewrite seqZ_nil by lia.
  Qed.
  Lemma lookup_total_seqZ_ge m n i : n ≤ i → seqZ m n !!! i = inhabitant.
  Proof. intros. by rewrite !list_lookup_total_alt, lookup_seqZ_ge. Qed.
  Lemma lookup_seqZ m n i m' : seqZ m n !! i = Some m' ↔ m' = m + i ∧ i < n.
  Proof.
    destruct (Z_le_gt_dec n i).
    - rewrite lookup_seqZ_ge by lia. naive_solver lia.
    - rewrite lookup_seqZ_lt by lia. naive_solver lia.
  Qed.
  Lemma NoDup_seqZ m n : NoDup (seqZ m n).
  Proof. apply NoDup_fmap_2, NoDup_seq. intros ???; lia. Qed.

  Lemma Forall_seqZ (P : Z → Prop) m n :
    Forall P (seqZ m n) ↔ ∀ m', m ≤ m' < m + n → P m'.
  Proof.
    rewrite Forall_lookup. split.
    - intros H j [??]. apply (H (Z.to_nat (j - m))), lookup_seqZ.
      rewrite !Z2Nat.id by lia. lia.
    - intros H j x [-> ?]%lookup_seqZ. auto with lia.
  Qed.
End seqZ.

(** ** Properties of the [sum_list] and [max_list] functions *)
Section sum_list.
  Context {A : Type}.
  Implicit Types x y z : A.
  Implicit Types l k : list A.
  Lemma sum_list_with_app (f : A → nat) l k :
    sum_list_with f (l ++ k) = sum_list_with f l + sum_list_with f k.
  Proof. induction l; simpl; lia. Qed.
  Lemma sum_list_with_reverse (f : A → nat) l :
    sum_list_with f (reverse l) = sum_list_with f l.
  Proof.
    induction l; simpl; rewrite ?reverse_cons, ?sum_list_with_app; simpl; lia.
  Qed.
  Lemma join_reshape szs l :
    sum_list szs = length l → mjoin (reshape szs l) = l.
  Proof.
    revert l. induction szs as [|sz szs IH]; simpl; intros l Hl; [by destruct l|].
    by rewrite IH, take_drop by (rewrite drop_length; lia).
  Qed.
  Lemma sum_list_replicate n m : sum_list (replicate m n) = m * n.
  Proof. induction m; simpl; auto. Qed.
  Lemma max_list_elem_of_le n ns:
    n ∈ ns → n ≤ max_list ns.
  Proof. induction 1; simpl; lia. Qed.
End sum_list.
