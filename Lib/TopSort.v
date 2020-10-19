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

Section topologically_sorted.

(** ** Topologically sorted lists. Definition and properties. *)

Context
  `{EqDecision A}
  (preceeds : A -> A -> bool)
  (l : list A)
  .

(**
We say that a list <<l>> is [topologically_sorted] w.r.t a <<preceeds>>
relation iff <<a preceeds b>> implies that <<a>> cannot occur after <<b>> in <<l>>.
*)
Definition topologically_sorted
  :=
  forall
    (a b : A)
    (Hab : preceeds a b = true)
    (l1 l2 : list A)
    (Heq : l = l1 ++ [b] ++ l2)
    , ~In a l2.

(** The following properties assume that <<preceeds>> determines a [StrictOrder]
on the list
*)
Context
  (P : A -> Prop)
  {Hso : StrictOrder (preceeds_P preceeds P)}
  .

Section topologically_sorted_fixed_list.

Context
  (Hl : Forall P l)
  (Hts : topologically_sorted)
  .

(** If <<l>> is [topologically_sorted], then for any occurences
of <<a>> and <<b>> in <<l>> such that <<a preceeds b>> it must be that
the occurrence of <<a>> is before that of <<b>>.

Hence all occurrences of <<a>> must be before all occurrences of <<b>> in
a [topologically_sorted] list.
*)
Lemma topologically_sorted_occurrences_ordering
  (a b : A)
  (Hab : preceeds a b = true)
  (la1 la2 : list A)
  (Heqa : l = la1 ++ [a] ++ la2)
  (lb1 lb2 : list A)
  (Heqb : l = lb1 ++ [b] ++ lb2)
  : exists (lab : list A), lb1 = la1 ++ a :: lab.
Proof.
  assert (Hpa : P a).
  { rewrite Forall_forall in Hl. apply Hl. rewrite Heqa. apply in_elt. }
  specialize (Hts a b Hab lb1 lb2 Heqb).
  rewrite Heqa in Heqb.
  assert (Ha : ~In a (b :: lb2)).
  { intro Ha. apply Hts. destruct Ha; try assumption. subst.
    rewrite (preceeds_irreflexive preceeds P a Hpa) in Hab.
    discriminate Hab.
  }
  specialize (occurrences_ordering a b la1 la2 lb1 lb2 Heqb Ha).
  intro; assumption.
Qed.


(**
If <<a>> and <<b>> are in a [topologically_sorted] list <<lts>> and <<a preceeds b>>
then there is an <<a>> before any occurence of <<b>> in <<lts>>.
*)
Corollary top_sort_before
  (a b : A)
  (Hab : preceeds a b = true)
  (Ha : In a l)
  (l1 l2 : list A)
  (Heq : l = l1 ++ [b] ++ l2)
  : In a l1.
Proof.
  apply in_split in Ha.
  destruct Ha as [la1 [la2 Ha]].
  specialize (topologically_sorted_occurrences_ordering a b Hab la1 la2 Ha l1 l2 Heq).
  intros [lab Hlab].
  subst. apply in_elt.
Qed.

(** As a corollary of the above, if <<a preceeds b>> then <<a>> can be found before
<<b>> in l.

*)
Corollary top_sort_preceeds
  (a b : A)
  (Hab : preceeds a b = true)
  (Ha : In a l)
  (Hb : In b l)
  : exists l1 l2 l3, l = l1 ++ [a] ++ l2 ++ [b] ++ l3.
Proof.
  apply in_split in Hb.
  destruct Hb as [l12 [l3 Hb']].
  specialize (top_sort_before a b Hab Ha l12 l3 Hb').
  intros Ha12. apply in_split in Ha12.
  destruct Ha12 as [l1 [l2 Ha12]].
  subst l12.
  exists l1. exists l2. exists l3. rewrite Hb'. rewrite <- app_assoc.
  reflexivity.
Qed.

End topologically_sorted_fixed_list.
End topologically_sorted.

Lemma toplogically_sorted_remove_last
  {A : Type}
  (preceeds : A -> A -> bool)
  (l : list A)
  (Hts : topologically_sorted preceeds l)
  (init : list A)
  (final : A)
  (Hinit : l = init ++ [final])
  : topologically_sorted preceeds init.
Proof.
  subst l.
  intros a b Hab l1 l2 Hinit.
  specialize (Hts a b Hab l1 (l2 ++ [final])).
  rewrite Hinit in Hts. repeat rewrite <- app_assoc in Hts.
  specialize (Hts eq_refl). intro Hnin. apply Hts.
  apply in_app_iff. left. assumption.
Qed.

Definition preceeds_closed
  {A : Type}
  (preceeds : A -> A -> bool)
  (s : set A)
  : Prop
  :=
  Forall (fun (b : A) => forall (a : A) (Hmj : preceeds a b = true), In a s) s.

Lemma preceeds_closed_set_eq
  {A : Type}
  (preceeds : A -> A -> bool)
  (s1 s2 : set A)
  (Heq : set_eq s1 s2)
  : preceeds_closed preceeds s1 <-> preceeds_closed preceeds s2.
Proof.
  unfold preceeds_closed. repeat rewrite Forall_forall.
  split; intros Hpc b Hb a Hab
  ; apply Heq; apply Heq in Hb; apply (Hpc b Hb)
  ; assumption.
Qed.

Lemma topologically_sorted_preceeds_closed_remove_last
  {A : Type}
  (preceeds : A -> A -> bool)
  (P : A -> Prop)
  {Hso : StrictOrder (preceeds_P preceeds P)}
  (l : list A)
  (Hl : Forall P l)
  (Hts : topologically_sorted preceeds l)
  (init : list A)
  (final : A)
  (Hinit : l = init ++ [final])
  (Hpc : preceeds_closed preceeds l)
  : preceeds_closed preceeds init.
Proof.
  unfold preceeds_closed in *.
  rewrite Forall_forall in Hpc. rewrite Forall_forall.
  subst l.
  intros b Hb a Hab.
  assert (Hb' : In b (init ++ [final])) by (apply in_app_iff; left; assumption).
  specialize (Hpc b Hb' a Hab). apply in_app_iff in Hpc.
  destruct Hpc as [Ha | Ha]; try assumption.
  destruct Ha as [Heq | Hn]; try inversion Hn.
  subst final.
  apply in_split in Hb'.
  destruct Hb' as [l1 [l2 Heq]].
  specialize
    (topologically_sorted_occurrences_ordering preceeds
      (init ++ [a]) P Hl Hts a b Hab init [] eq_refl l1 l2 Heq
    ).
  intros [lab Hlab].
  rewrite Hlab in Heq. exfalso. clear -Heq.
  simpl in Heq. rewrite <- app_assoc in Heq. simpl in Heq.
  apply app_inv_head in Heq. inversion Heq.
  symmetry in H0. apply app_eq_nil in H0.
  destruct H0 as [_ H].
  inversion H.
Qed.

Section top_sort.
(** ** The topological sorting algorithm *)

Context
  `{EqDecision A}
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
    let l'' := set_remove decide_eq min l in
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
  remember (set_remove decide_eq min l) as l'.
  destruct (decide (min = a)); try rewrite e.
  - apply set_eq_cons. specialize (IHn l H0). subst. assumption.
  - specialize (min_predecessors_in preceeds (a :: l) l a).
    rewrite <- Heqmin. simpl. intros [Heq | Hin]; try (elim n0; assumption).
    specialize (IHn (a :: l')).
    specialize (set_remove_length min l Hin).
    rewrite <- Heql'. rewrite <- H0. intro Hlen.
    specialize (IHn Hlen).
    split; intros x [Heq | Hinx]; try (subst x).
    + right. apply IHn. left. reflexivity.
    + destruct (decide (x = min)); try subst x.
      * left. reflexivity.
      * specialize (set_remove_3 decide_eq l Hinx n1).
        rewrite <- Heql'. intro Hinx'.
        right. apply IHn. right. assumption.
    + right. assumption.
    + apply IHn in Hinx.
      destruct Hinx as [Heq | Hinx]; try (subst; left; reflexivity).
      right. subst. apply set_remove_1 in Hinx. assumption.
Qed.

Lemma top_sort_nodup
  (l : list A)
  (Hl : NoDup l)
  : NoDup (top_sort l).
Proof.
  unfold top_sort.
  remember (length l) as len.
  generalize dependent l.
  induction len; intros.
  - symmetry in Heqlen. apply length_zero_iff_nil in Heqlen. subst l.
    constructor.
  - destruct l as [| a l].
    + constructor.
    + simpl.
      assert (Hl' : NoDup l) by (inversion Hl; assumption).
      assert (Hlen : len = length l) by (inversion Heqlen; reflexivity).
      assert (Hl'' : NoDup (set_remove decide_eq (min_predecessors preceeds (a :: l) l a) l))
        by (apply set_remove_nodup; assumption).
      destruct (decide (min_predecessors preceeds (a :: l) l a = a)); constructor.
      * specialize (IHlen l Hl'  Hlen).
        rewrite e in *.
        inversion Hl; subst x l0. intro Ha. elim H1.
        apply top_sort_set_eq. subst len. assumption.
      * apply IHlen; try assumption.
      * intro Hmin.
        assert (Hlen' : len = length (a :: set_remove decide_eq (min_predecessors preceeds (a :: l) l a) l)).
        { simpl.
          rewrite <- set_remove_length; try assumption.
          pose (@min_predecessors_in _ preceeds (a :: l) l a) as Hin.
          destruct Hin as [Heq | Hin]; try assumption.
          elim n. assumption.
        }
        rewrite Hlen' in Hmin.
        apply (proj2 (top_sort_set_eq (a :: set_remove decide_eq (min_predecessors preceeds (a :: l) l a) l)))
          in Hmin.
        destruct Hmin; try (symmetry in H; elim n; assumption).
        apply set_remove_2 in H; try assumption.
        elim H. reflexivity.
      * { apply IHlen.
        - constructor; try assumption.
          intro Ha. apply set_remove_iff in Ha; try assumption.
          destruct Ha as [Ha _].
          inversion Hl. elim H1. assumption.
        - simpl.
          rewrite <- set_remove_length; try assumption.
          pose (@min_predecessors_in _ preceeds (a :: l) l a) as Hin.
          destruct Hin as [Heq | Hin]; try assumption.
          elim n. assumption.
        }
Qed.

Context
  (P : A -> Prop)
  {Hso : StrictOrder (preceeds_P preceeds P)}
  (l : list A)
  (Hl : Forall P l)
  .

(** Under the assumption that <<preceeds>> induces a [StrictOrder] on the elements of
<<l>>, [top_sort] <<l>> is [topologically_sorted].

*)
Lemma top_sort_sorted : topologically_sorted preceeds (top_sort l).
Proof.
  intro a; intros.
  intro Ha2.
  assert (Ha : In a l).
  { apply top_sort_set_eq.
    rewrite Heq. simpl. apply in_app_iff. right. right. assumption.
  }
  unfold top_sort in Heq.
  remember (length l) as n.
  generalize dependent Heq.
  generalize dependent l2.
  generalize dependent l1.
  generalize dependent Ha.
  generalize dependent Hab.
  generalize dependent b.
  generalize dependent a.
  generalize dependent l. clear Hl l.
  induction n; intros
  ; try (symmetry in Heqn;  apply length_zero_iff_nil in Heqn; subst l; inversion Ha).
  destruct l as [| a0 l0]; inversion Hl; subst; simpl in Heq.
  + inversion Ha.
  + remember (min_predecessors preceeds (a0 :: l0) l0 a0) as min.
    remember
      (match decide (min = a0) return (set A) with
      | left _ => l0
      | right _ => @cons A a0 (set_remove decide_eq min l0)
      end) as l'.
    inversion Heqn.
    assert (Hall' : Forall P l').
    { rewrite Forall_forall. intros x Hx.
      rewrite Forall_forall in H2.
      destruct (decide (min = a0)).
      - subst a0 l'. apply H2. assumption.
      - subst l'.
        destruct Hx as [Heqx | Hx]; try (subst; assumption).
        apply set_remove_1 in Hx.
        apply H2. assumption.
    }
    assert (Hlenl' : n = length l').
    { destruct (decide (min = a0)).
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
    { destruct (decide (b = min)); try assumption.
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
    destruct (in_dec decide_eq a l').
    - apply (IHn i l1 l2 Ha2 H4).
    - assert (Hmina : min = a).
      { destruct (decide (min = a0)).
      - subst a0 l'.
        inversion Ha; try assumption.
        elim n0. assumption.
      - subst l'.
        destruct Ha as [Heqa | Ha'].
        + subst a0. elim n0. left. reflexivity.
        + destruct (decide (a = min)); try (symmetry; assumption).
          apply (set_remove_3 decide_eq _ Ha') in n2.
          elim n0. right. assumption.
      }
      subst a.
      apply n0.
      apply top_sort_set_eq.
      unfold top_sort. rewrite <- Hlenl'.
      rewrite H4.
      apply in_app_iff.
      right. right. assumption.
Qed.

(** <<lts>> is a [topological_sorting] of <<l>> if it has the same elements as <<l>>
and is [toplogically_sorted].
*)
Definition topological_sorting
  (l lts : list A)
  :=
  set_eq l lts /\ topologically_sorted preceeds lts.

Corollary top_sort_correct : topological_sorting l (top_sort l).
Proof.
  split.
  - apply top_sort_set_eq.
  - apply top_sort_sorted.
Qed.

End top_sort.
