Require Import Bool List ListSet Compare_dec RelationClasses.
Require Import Lia.
Import ListNotations.

From CasperCBC
  Require Import Preamble ListExtras ListSetExtras.

(** * Topological sorting algorithm *)

(**
This module describes an algorithm producing a linear extension for a
given partial order using an algorithm similar to Kahn's topological
sorting algorithm.

The algorithm extracts an element with a minimal number of predecessors
among the current elements, then recurses on the remaining elements.

To begin with we assume an unconstrained <<preceeds>> function to say
whether an element preceeds another.  The proofs will show that if
<<preceeds>> determines a strict order on the set of elements in the list,
then the [top_sort] algoritm produces a linear extension of that ordering
(Lemmas [top_sort_preceeds] and [top_sort_preceeds_before]).
*)

Section min_predecessors.
(** ** Finding an element with a minimal number of predecessors *)

(** For this section we will fix a list <<l>> and count the predecessors
occurring in that list. *)

Context
  {A : Type}
  (preceeds : A -> A -> bool)
  (l : list A)
  .

Definition count_predecessors
  (a : A)
  : nat
  := length (filter (fun b => preceeds b a) l).

Lemma zero_predecessors
  (a : A)
  (Ha : count_predecessors a = 0)
  : Forall (fun b => preceeds b a = false) l.
Proof.
  apply filter_nil.
  apply length_zero_iff_nil.
  assumption.
Qed.

(**
Finds an element minimizing [count_predecessesors] in <<min :: remainder>>
*)

Fixpoint min_predecessors
  (remainder : list A)
  (min : A)
  : A
  :=
  match remainder with
  | [] => min
  | h::t =>
    if (lt_dec (count_predecessors h) (count_predecessors min))
    then min_predecessors t h
    else min_predecessors t min
  end.

Lemma min_predecessors_in
  (l' : list A)
  (a : A)
  (min := min_predecessors l' a)
  : min = a \/ In min l'.
Proof.
  unfold min; clear min. generalize dependent a.
  induction l'; try (left; reflexivity).
  intro a0. simpl.
  destruct (lt_dec (count_predecessors a) (count_predecessors a0)).
  - right.
    specialize (IHl' a). destruct IHl' as [Heq | Hin].
    + left. symmetry. assumption.
    + right. assumption.
  - specialize (IHl' a0). destruct IHl' as [Heq | Hin].
    + left. assumption.
    + right. right. assumption.
Qed.

Lemma min_predecessors_correct
  (l' : list A)
  (a : A)
  (min := min_predecessors l' a)
  (mins := count_predecessors min)
  : Forall (fun b => mins <= count_predecessors b) (a :: l').
Proof.
  unfold mins; clear mins. unfold min; clear min. generalize dependent a.
  induction l'; intros; rewrite Forall_forall; intros.
  - simpl in H. inversion H; try contradiction. subst; clear H.
    simpl. lia.
  - apply in_inv in H. destruct H as [Heq | Hin]; subst.
    + simpl. destruct (lt_dec (count_predecessors a) (count_predecessors x)).
      * specialize (IHl' a). rewrite Forall_forall in IHl'.
        assert (Ha : In a (a :: l')) by (left; reflexivity).
        specialize (IHl' a Ha).
        lia.
      * specialize (IHl' x). rewrite Forall_forall in IHl'.
        assert (Hx : In x (x :: l')) by (left; reflexivity).
        specialize (IHl' x Hx).
        assumption.
    + simpl. destruct (lt_dec (count_predecessors a) (count_predecessors a0)).
      * specialize (IHl' a). rewrite Forall_forall in IHl'.
        specialize (IHl' x Hin).
        assumption.
      * apply not_lt in n. unfold ge in n.
        { destruct Hin as [Heq | Hin]; subst.
        - specialize (IHl' a0). rewrite Forall_forall in IHl'.
          assert (Ha0 : In a0 (a0 :: l')) by (left; reflexivity).
          specialize (IHl' a0 Ha0).
          lia.
        - specialize (IHl' a0). rewrite Forall_forall in IHl'.
          assert (Hx : In x (a0 :: l')) by (right; assumption).
          specialize (IHl' x Hx).
          assumption.
        }
Qed.

(** Given <<P>> a property on <<A>>, [preceeds_P] is the relation
induced by <<preceeds>> on the subset of <<A>> determined by <<P>>. *)

Definition preceeds_P
  (P : A -> Prop)
  (x y : sig P)
  : Prop
  := preceeds (proj1_sig x) (proj1_sig y) = true.

(** In what follows, let us fix a property <<P>> satisfied by all elements
of <<l>>, such that [preceeds_P] <<P>> is a [StrictOrder].

Consequently, this means that <<preceeds>> is a [StrictOrder] on the
elements of <<l>>.
*)

Context
  (P : A -> Prop)
  (HPl : Forall P l)
  {Hso : StrictOrder (preceeds_P P)}
  .

(** Next we derive easier to work with formulations for the [StrictOrder]
properties associated with [preceeds_P]. *)
Lemma preceeds_irreflexive
  (a : A)
  (Ha : P a)
  : preceeds a a = false.
Proof.
  specialize (StrictOrder_Irreflexive (exist P a Ha)).
  unfold complement; unfold preceeds_P; simpl; intro Hirr.
  destruct (preceeds a a); try reflexivity.
  elim Hirr.
  reflexivity.
Qed.

Lemma preceeds_asymmetric
  (a b : A)
  (Ha : P a)
  (Hb : P b)
  (Hab : preceeds a b = true)
  : preceeds b a = false.
Proof.
  destruct (preceeds b a) eqn:Hba; try reflexivity.
  specialize
    (StrictOrder_Asymmetric Hso
      (exist P a Ha) (exist P b Hb)
      Hab Hba
    ); intro H; inversion H.
Qed.

Lemma preceeds_transitive
  (a b c : A)
  (Ha : P a)
  (Hb : P b)
  (Hc : P c)
  (Hab : preceeds a b = true)
  (Hbc : preceeds b c = true)
  : preceeds a c = true.
Proof.
  specialize
    (RelationClasses.StrictOrder_Transitive
      (exist P a Ha) (exist P b Hb) (exist P c Hc)
      Hab Hbc
    ).
  intro.
  assumption.
Qed.

(** If <<preceeds>> is a [StrictOrder] on <<l>>, then there must exist an
element of <<l>> with no predecessors in <<l>>.
*)
Lemma count_predecessors_zero
  (Hl : l <> [])
  : Exists (fun a => count_predecessors a = 0) l.
Proof.
  unfold count_predecessors.
  induction l.
  - elim Hl. reflexivity.
  - inversion HPl; subst.
    specialize (IHl0 H2).
    apply Exists_cons.
    destruct l0 as [|b l1].
    + left. simpl. rewrite preceeds_irreflexive by assumption. reflexivity.
    + assert (Hbl1 : b :: l1 <> []) by (intro; discriminate).
      specialize (IHl0 Hbl1).
      apply Exists_exists in IHl0.
      destruct IHl0 as [x [Hin Hlen]].
      destruct (preceeds a x) eqn:Hxa.
      * left. inversion H2; subst.
        specialize (Forall_forall P (b :: l1)); intros [Hall _].
        specialize (Hall H2 x Hin).
        assert
          (Hax : forall ll (Hll: Forall P ll),
            Forall (fun c => preceeds c a = true -> preceeds c x = true) ll
          ).
        { intros. rewrite Forall_forall. intros c Hinc Hac.
          apply preceeds_transitive with a; try assumption.
          rewrite Forall_forall in Hll.
          apply Hll.
          assumption.
        }
        specialize (Hax (b :: l1) H2).
        specialize (filter_length_fn _ _ (b :: l1) Hax); intro Hlena.
        simpl in *. rewrite preceeds_irreflexive by assumption. lia.
      * right. apply Exists_exists. exists x. split; try assumption.
        simpl in *. rewrite Hxa. assumption.
Qed.

(**
Hence, computing [min_predecessors] on <<l>> yields an element with
no predecessors.
*)
Lemma min_predecessors_zero
  (l' : list A)
  (a : A)
  (Hl : l = a :: l')
  (min := min_predecessors l' a)
  : count_predecessors min = 0.
Proof.
  assert (Hl' : l <> []) by (intro H; rewrite Hl in H; inversion H).
  specialize (count_predecessors_zero Hl'); intro Hx.
  apply Exists_exists in Hx. destruct Hx as [x [Hinx Hcountx]].
  specialize (min_predecessors_correct l' a); simpl; intro Hall.
  rewrite Forall_forall in Hall.
  rewrite Hl in Hinx.
  specialize (Hall x Hinx).
  unfold min.
  lia.
Qed.

End min_predecessors.

Section top_sort.
(** ** The topological sorting algorithm
*)

Context
  {A : Type}
  {eq_dec_a : EqDec A}
  (preceeds : A -> A -> bool)
  .

(** Iteratively extracts <<n>> elements with minimal number of precessors
from a given list.
*)
Fixpoint top_sort_n
  (n : nat)
  (l : list A)
  : list A
  :=
  match n,l with
  | 0, _ => []
  | _, [] => []
  | S n', a :: l' =>
    let min := min_predecessors preceeds l l' a in
    let l'' := set_remove eq_dec min l in
    min :: top_sort_n n' l''
  end.

(** Repeats the procedure above to order all elements from the input list.
*)
Definition top_sort
  (l : list A)
  : list A
  := top_sort_n (length l) l.

(** The result of [top_sort] and its input are equal as sets.
*)
Lemma top_sort_set_eq
  (l : list A)
  : set_eq l (top_sort l).
Proof.
  unfold top_sort.
  remember (length l) as n. generalize dependent l.
  induction n; intros; destruct l; try apply set_eq_refl
  ; inversion Heqn.
  simpl.
  remember (min_predecessors preceeds (a :: l) l a) as min.
  remember (set_remove eq_dec min l) as l'.
  destruct (eq_dec min a); try rewrite e.
  - apply set_eq_cons. specialize (IHn l H0). subst. assumption.
  - specialize (min_predecessors_in preceeds (a :: l) l a).
    rewrite <- Heqmin. simpl. intros [Heq | Hin]; try (elim n0; assumption).
    specialize (IHn (a :: l')).
    specialize (set_remove_length eq_dec min l Hin).
    rewrite <- Heql'. rewrite <- H0. intro Hlen.
    specialize (IHn Hlen).
    split; intros x [Heq | Hinx]; try (subst x).
    + right. apply IHn. left. reflexivity.
    + destruct (eq_dec x min); try subst x.
      * left. reflexivity.
      * specialize (set_remove_3 eq_dec l Hinx n1).
        rewrite <- Heql'. intro Hinx'.
        right. apply IHn. right. assumption.
    + right. assumption.
    + apply IHn in Hinx.
      destruct Hinx as [Heq | Hinx]; try (subst; left; reflexivity).
      right. subst. apply set_remove_1 in Hinx. assumption.
Qed.

(** *** [top_sort] corectness *)

(** We can prove the corectness of [top_sort] under the assumption that
<<preceeds>> induces a [StrictOrder] on a subset of <<A>> including all
elements of <<l>>.

Let <<a>> and <<b>> be two elements of <<l>> such that <<a preceeds b>>.
*)

Context
  (P : A -> Prop)
  {Hso : StrictOrder (preceeds_P preceeds P)}
  (l : list A)
  (Hl : Forall P l)
  (a : A)
  (b : A)
  (Ha : In a l)
  (Hb : In b l)
  (Hab : preceeds a b = true)
  .

(** The main result of this section states that for any occurrence of <<b>>
in [top_sort] <<l>>, <<a>> must occur before it and cannot occur after it.

Quantifying over all occurrences of <<b>> guarantees that all occurrences
of <<a>> must be before all occurrences of <<b>> in [top_sort] <<l>>.
*)
Lemma top_sort_correct
  (l1 l2 : list A)
  (Heq : top_sort l = l1 ++ [b] ++ l2)
  : In a l1 /\ ~In a l2.
Proof.
  unfold top_sort in Heq.
  remember (length l) as n.
  generalize dependent Heq.
  generalize dependent l2.
  generalize dependent l1.
  clear Hb.
  generalize dependent Ha. clear Ha.
  generalize dependent Hab. clear Hab.
  generalize dependent b. clear b.
  generalize dependent a. clear a.
  generalize dependent l. clear Hl l.
  induction n; intros
  ; try (symmetry in Heqn;  apply length_zero_iff_nil in Heqn; subst l; inversion Ha).
  destruct l as [| a0 l0]; inversion Hl; subst.
  - inversion Ha.
  - simpl in Heq.
    remember (min_predecessors preceeds (a0 :: l0) l0 a0) as min.
    remember (if eq_dec min a0 then l0 else a0 :: set_remove eq_dec min l0) as l'.
    inversion Heqn.
    assert (Hall' : Forall P l').
    { rewrite Forall_forall. intros x Hx.
      rewrite Forall_forall in H2.
      destruct (eq_dec min a0).
      - subst a0 l'. apply H2. assumption.
      - subst l'.
        destruct Hx as [Heqx | Hx]; try (subst; assumption).
        apply set_remove_1 in Hx.
        apply H2. assumption.
    }
    assert (Hlenl' : n = length l').
    { destruct (eq_dec min a0).
      - subst a0.
        subst l'. assumption.
      - subst l'. simpl.
        rewrite <- set_remove_length; try assumption.
        specialize (min_predecessors_in preceeds (a0 :: l0) l0 a0).
        rewrite <- Heqmin. simpl.
        intros [Heq' | Hin]; try assumption.
        elim n0. assumption.
    }
    specialize (IHn l' Hall' Hlenl' a b Hab).
    assert (Hminb : b <> min).
    { destruct (eq_dec b min); try assumption.
      subst b.
      specialize (min_predecessors_zero preceeds (a0 :: l0) P Hl l0 a0 eq_refl).
      rewrite <- Heqmin. simpl. intro Hmin.
      apply zero_predecessors in Hmin.
      rewrite Forall_forall in Hmin. apply Hmin in Ha.
      rewrite Ha in Hab. discriminate Hab.
    }
    destruct l1 as [| _min l1]; inversion Heq
    ; try (subst b; elim Hminb; reflexivity).
    subst _min.
    replace (if eq_dec min a0 then l0 else a0 :: set_remove eq_dec min l0) with l' in H4.
    destruct (in_dec eq_dec a l').
    + specialize (IHn i l1 l2 H4).
      destruct IHn as [Hin Hnin].
      split; try assumption.
      right.
      assumption.
    + assert (Hmina : min = a).
      { destruct (eq_dec min a0).
      - subst a0 l'.
        inversion Ha; try assumption.
        elim n0. assumption.
      - subst l'.
        destruct Ha as [Heqa | Ha'].
        + subst a0. elim n0. left. reflexivity.
        + destruct (eq_dec a min); try (symmetry; assumption).
          apply (set_remove_3 eq_dec _ Ha') in n2.
          elim n0. right. assumption.
      }
      subst a.
      split; try (left; reflexivity).
      intro Hl2.
      apply n0.
      apply top_sort_set_eq.
      unfold top_sort. rewrite <- Hlenl'.
      rewrite H4.
      apply in_app_iff.
      right. right. assumption.
Qed.

(** As a corollary of the above, <<a>> can be found before <<b>> in
[top_sort l].

This result is equivalent with the one above when there are no duplicate
elements in <<l>>; however it is strictly weaker in the general case.
*)
Corollary top_sort_preceeds
  : exists l1 l2 l3, top_sort l = l1 ++ [a] ++ l2 ++ [b] ++ l3.
Proof.
  apply top_sort_set_eq in Hb.
  apply in_split in Hb.
  destruct Hb as [l12 [l3 Hb']].
  specialize (top_sort_correct l12 l3 Hb').
  intros [Ha12 _]. apply in_split in Ha12.
  destruct Ha12 as [l1 [l2 Ha12]].
  subst l12.
  exists l1. exists l2. exists l3. rewrite Hb'. rewrite <- app_assoc.
  reflexivity.
Qed.

End top_sort.
