From Coq Require Import List Vectors.Fin FinFun Program.
Import ListNotations.

(** * Finite type utility definitions and lemmas *)

Fixpoint fin_t_listing
  (n : nat)
  : list (Fin.t n)
  :=
  match n with
  | 0 => []
  | S n' => F1 :: map FS (fin_t_listing n')
  end.

Lemma fin_t_listing_length
  (n : nat)
  : length (fin_t_listing n) = n.
Proof.
  induction n; try reflexivity.
  simpl. f_equal.
  rewrite map_length.
  assumption.
Qed.

Lemma fin_t_full
  (n : nat)
  : Full (fin_t_listing n).
Proof.
  induction n; intro x.
  - inversion x.
  - simpl.
    dependent destruction x.
    + left. reflexivity.
    + right. apply in_map_iff. exists x.
      split; try reflexivity. apply IHn.
Qed.
