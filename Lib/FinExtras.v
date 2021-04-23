From Coq Require Import List Program.
From Coq Require FinFun.
Import ListNotations.
From CasperCBC.Lib Require Import Fin.

(** * Finite type utility definitions and lemmas *)

Lemma fin_t_listing_length
  (n : nat)
  : length (all_fin n) = n.
Proof.
  induction n; [reflexivity|].
  simpl. f_equal.
  rewrite map_length.
  assumption.
Qed.

Lemma fin_t_full
  (n : nat)
  : FinFun.Full (all_fin n).
Proof.
  induction n; intro x.
  - inversion x.
  - simpl.
    simpl in x.
    destruct x as [x|]; [|left;reflexivity].
    right. apply in_map_iff. exists x.
    split; [reflexivity|]. apply IHn.
Qed.
