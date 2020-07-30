Require Import Bool List ListSet Compare_dec RelationClasses.
Require Import Lia.
Import ListNotations.

From CasperCBC
  Require Import Preamble ListExtras ListSetExtras.

Section min_successors.

Context
  {A : Type}
  (preceeds : A -> A -> bool)
  (l : list A)
  .

Definition count_successors
  (a : A)
  : nat
  := length (filter (fun b => preceeds b a) l).

Fixpoint min_successors
  (remainder : list A)
  (min : A)
  : A
  :=
  match remainder with
  | [] => min
  | h::t =>
    if (lt_dec (count_successors h) (count_successors min))
    then min_successors t h
    else min_successors t min
  end.

Lemma min_successors_in
  (l' : list A)
  (a : A)
  (min := min_successors l' a)
  : min = a \/ In min l'.
Proof.
  unfold min; clear min. generalize dependent a.
  induction l'; try (left; reflexivity).
  intro a0. simpl.
  destruct (lt_dec (count_successors a) (count_successors a0)).
  - right.
    specialize (IHl' a). destruct IHl' as [Heq | Hin].
    + left. symmetry. assumption.
    + right. assumption.
  - specialize (IHl' a0). destruct IHl' as [Heq | Hin].
    + left. assumption.
    + right. right. assumption.
Qed.

Lemma min_successors_count
  (l' : list A)
  (a : A)
  (min := min_successors l' a)
  (mins := count_successors min)
  : Forall (fun b => mins <= count_successors b) (a :: l').
Proof.
  unfold mins; clear mins. unfold min; clear min. generalize dependent a.
  induction l'; intros; rewrite Forall_forall; intros.
  - simpl in H. inversion H; try contradiction. subst; clear H.
    simpl. lia.
  - apply in_inv in H. destruct H as [Heq | Hin]; subst.
    + simpl. destruct (lt_dec (count_successors a) (count_successors x)).
      * specialize (IHl' a). rewrite Forall_forall in IHl'.
        assert (Ha : In a (a :: l')) by (left; reflexivity).
        specialize (IHl' a Ha).
        lia.
      * specialize (IHl' x). rewrite Forall_forall in IHl'.
        assert (Hx : In x (x :: l')) by (left; reflexivity).
        specialize (IHl' x Hx).
        assumption.
    + simpl. destruct (lt_dec (count_successors a) (count_successors a0)).
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

Definition preceeds_P
  (P : A -> Prop)
  (x y : sig P)
  : Prop
  := preceeds (proj1_sig x) (proj1_sig y) = true.

Context
  (P : A -> Prop)
  (HPl : Forall P l)
  (preceeds_lt := preceeds_P P)
  {Hpreceeds_lt : StrictOrder preceeds_lt}
  .

Lemma preceeds_irreflexive
  (a : A)
  (Ha : P a)
  : preceeds a a = false.
Proof.
  specialize (StrictOrder_Irreflexive (exist P a Ha)).
  unfold complement; unfold preceeds_lt; unfold preceeds_P; simpl; intro Hirr.
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
    (StrictOrder_Asymmetric Hpreceeds_lt
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

Lemma count_successors_zero
  (Hl : l <> [])
  : Exists (fun a => count_successors a = 0) l.
Proof.
  unfold count_successors.
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

Lemma min_successors_zero
  (l' : list A)
  (a : A)
  (Hl : l = a :: l')
  (min := min_successors l' a)
  : count_successors min = 0.
Proof.
  assert (Hl' : l <> []) by (intro H; rewrite Hl in H; inversion H).
  specialize (count_successors_zero Hl'); intro Hx.
  apply Exists_exists in Hx. destruct Hx as [x [Hinx Hcountx]].
  specialize (min_successors_count l' a); simpl; intro Hall.
  rewrite Forall_forall in Hall.
  rewrite Hl in Hinx.
  specialize (Hall x Hinx).
  unfold min.
  lia.
Qed.

Lemma zero_successors
  (a : A)
  (Ha : count_successors a = 0)
  : Forall (fun b => preceeds b a = false) l.
Proof.
  apply filter_nil.
  apply length_zero_iff_nil.
  assumption.
Qed.

End min_successors.

Section top_sort.

Context
  {A : Type}
  {eq_dec_a : EqDec A}
  (preceeds : A -> A -> bool)
  .

Fixpoint top_sort_n
  (n : nat)
  (l : list A)
  : list A
  :=
  match n,l with
  | 0, _ => []
  | _, [] => []
  | S n', a :: l' =>
    let min := min_successors preceeds l l' a in
    let l'' := set_remove eq_dec min l in
    min :: top_sort_n n' l''
  end.

Definition top_sort
  (l : list A)
  : list A
  := top_sort_n (length l) l.

Lemma top_sort_set_eq
  (l : list A)
  : set_eq l (top_sort l).
Proof.
  unfold top_sort.
  remember (length l) as n. generalize dependent l.
  induction n; intros; destruct l; try apply set_eq_refl
  ; inversion Heqn.
  simpl.
  remember (min_successors preceeds (a :: l) l a) as min.
  remember (set_remove eq_dec min l) as l'.
  destruct (eq_dec min a); try rewrite e.
  - apply set_eq_cons. specialize (IHn l H0). subst. assumption.
  - specialize (min_successors_in preceeds (a :: l) l a).
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

Context
  (P : A -> Prop)
  (preceeds_lt := preceeds_P preceeds P)
  {Hpreceeds_lt : StrictOrder preceeds_lt}
  .

Lemma top_sort_preceeds_before
  (l : list A)
  (Hl : Forall P l)
  (b : A)
  (l1 l2 : list A)
  (Heq : top_sort l = l1 ++ [b] ++ l2)
  (a : A)
  (Ha : In a l)
  (Hab : preceeds a b = true)
  : In a l1.
Proof.
  unfold top_sort in Heq.
  remember (length l) as n.
  generalize dependent Heq.
  generalize dependent l2.
  generalize dependent l1.
  generalize dependent Ha.
  generalize dependent Hab.
  generalize dependent b.
  generalize dependent a.
  generalize dependent l.
  induction n; intros
  ; try (symmetry in Heqn;  apply length_zero_iff_nil in Heqn; subst l; inversion Ha).
  destruct l; inversion Hl; subst.
  - inversion Ha.
  - simpl in Heq.
    remember (min_successors preceeds (a0 :: l) l a0) as min.
    remember (if eq_dec min a0 then l else a0 :: set_remove eq_dec min l) as l'.
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
        specialize (min_successors_in preceeds (a0 :: l) l a0).
        rewrite <- Heqmin. simpl.
        intros [Heq' | Hin]; try assumption.
        elim n0. assumption.
    }
    specialize (IHn l' Hall' Hlenl' a b Hab).
    assert (Hminb : b <> min).
    { destruct (eq_dec b min); try assumption.
      subst b.
      specialize (min_successors_zero preceeds (a0 :: l) P Hl l a0 eq_refl).
      rewrite <- Heqmin. simpl. intro Hmin.
      apply zero_successors in Hmin.
      rewrite Forall_forall in Hmin. apply Hmin in Ha.
      rewrite Ha in Hab. discriminate Hab.
    }
    destruct l1 as [| _min l1]; inversion Heq
    ; try (subst b; elim Hminb; reflexivity).
    subst _min.
    replace (if eq_dec min a0 then l else a0 :: set_remove eq_dec min l) with l' in H4.
    destruct (eq_dec min a).
    + subst a. left. reflexivity.
    + assert (Hina : In a l').
      { destruct (eq_dec min a0).
        - subst a0 l'.
          inversion Ha; try assumption.
          elim n0. assumption.
        - subst l'.
          destruct Ha as [Heqa | Ha].
          + subst a0. left. reflexivity.
          + right. apply set_remove_3; try assumption.
            intro n2. apply n0. symmetry. assumption.
      }
      specialize (IHn Hina l1 l2 H4).
      right.
      assumption.
Qed.

Lemma top_sort_preceeds
  (l : list A)
  (Hl : Forall P l)
  (a b : A)
  (Ha : In a l)
  (Hb : In b l)
  (Hab : preceeds a b = true)
  : exists l1 l2 l3, top_sort l = l1 ++ [a] ++ l2 ++ [b] ++ l3.
Proof.
  apply top_sort_set_eq in Hb.
  apply in_split in Hb.
  destruct Hb as [l12 [l3 Hb]].
  specialize (top_sort_preceeds_before l Hl b l12 l3 Hb a Ha Hab).
  intro Ha12. apply in_split in Ha12.
  destruct Ha12 as [l1 [l2 Ha12]].
  subst l12.
  exists l1. exists l2. exists l3. rewrite Hb. rewrite <- app_assoc.
  reflexivity.
Qed.

End top_sort.