Require Import Coq.Bool.Bool.
Require Import List.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Structures.Orders.
Import ListNotations.

Require Import Casper.preamble.
Require Import Casper.ListSetExtras.

(** Sorted Lists **)

Fixpoint list_compare {A} (compare : A -> A -> comparison)
    (l1 l2 : list A) : comparison :=
  match l1,l2 with
  | [], [] => Eq
  | [], _ => Lt
  | _, [] => Gt
  | (h1 :: t1), (h2 :: t2) => 
    match compare h1 h2 with
    | Eq => @list_compare A compare t1 t2
    | cmp => cmp
    end
  end.

Fixpoint Inb {A} (compare : A -> A -> comparison) (a : A) (l : list A) : bool :=
  match l with
  | [] => false
  | h :: t =>
    match compare a h with
    | Eq => true
    | _ => Inb compare a t
    end
  end.

Lemma compare_in : forall A (compare : A -> A -> comparison),
  CompareStrictOrder compare ->
  PredicateFunction2 (@In A) (Inb compare).
Proof.
  intros A compare H a l.
  induction l; intros; split; intros.
  - inversion H0.
  - discriminate.
  - inversion H0; subst.
    + simpl. rewrite compare_eq_refl; try apply (proj1 H). reflexivity.
    + simpl. apply IHl in H1; try assumption. rewrite H1.
      destruct (compare a a0); reflexivity.
  - simpl in H0. destruct (compare a a0) eqn:Hcmp.
    + left. symmetry. apply (proj1 H). assumption.
    + right. apply IHl; try assumption.
    + right. apply IHl; try assumption.
Qed.

Lemma compare_not_in : forall A (compare : A -> A -> comparison),
  CompareStrictOrder compare ->
  forall a l, not (In a l) <-> Inb compare a l = false.
Proof.
  intros. rewrite (compare_in _ compare H a l).
  apply not_true_iff_false.
Qed.

Lemma list_compare_strict_order : forall A (compare : A -> A -> comparison),
  CompareStrictOrder compare ->
  CompareStrictOrder (@list_compare A compare).
Proof.
  intros. destruct H as [R T].
  split.
  - intro x. induction x; intros; destruct y; split; intros; try discriminate; try reflexivity.
    + simpl in H. destruct (compare a a0) eqn:Hcmp; try discriminate H.
      apply R in Hcmp; subst. apply IHx in H; subst.
      reflexivity.
    + inversion H; subst. simpl. rewrite compare_eq_refl; try assumption.
      apply IHx. reflexivity.
  - intros x y. generalize dependent x.
    induction y; intros; destruct x; destruct z; try assumption
    ; destruct comp; try discriminate
    ; inversion H; clear H; destruct (compare a0 a) eqn:Ha0; try discriminate
    ; inversion H0; clear H0; destruct (compare a a1) eqn:Ha1; try discriminate
    ; try apply (IHy _ _ _ H2) in H1; try apply (T _ _ _ _ Ha0) in Ha1
    ; try apply R in Ha0; subst
    ; try (simpl; rewrite Ha1; try rewrite H1, H2; reflexivity)
    ; try (simpl; rewrite Ha1; rewrite H2; reflexivity)
    ; try (apply R in Ha1; subst; simpl;  rewrite Ha0; rewrite H1; reflexivity)
    .
Qed.

Lemma list_compare_eq_dec : forall A (compare : A -> A -> comparison),
  CompareStrictOrder compare ->
  (forall x y : list A, {x = y} + {x <> y}).
Proof.
  intros A compare H. apply compare_eq_dec with (@list_compare A compare).
  apply list_compare_strict_order. assumption.
Qed.

Fixpoint add_in_sorted_list_fn {A} (compare : A -> A -> comparison) (x : A) (l : list A) : list A :=
  match l with
  | [] => [x]
  | h :: t =>
    match compare x h with
    | Lt => x :: h :: t
    | Eq => h :: t
    | Gt => h :: @add_in_sorted_list_fn A compare x t
    end
  end.

Lemma add_in_sorted_list_no_empty {A} (compare : A -> A -> comparison) : forall msg sigma,
  add_in_sorted_list_fn compare msg sigma <> [].
Proof.
  unfold not. intros. destruct sigma; simpl in H.
  - inversion H.
  - destruct (compare msg a); inversion H.
Qed.

Lemma add_in_sorted_list_in {A} (compare : A -> A -> comparison) : forall msg msg' sigma,
  CompareStrictOrder compare ->
  In msg' (add_in_sorted_list_fn compare msg sigma) ->
  msg = msg' \/ In msg' sigma.
Proof. 
  intros. induction sigma; simpl in H0
  ; try (destruct H0 as [H0 | H0]; subst; try inversion H0; left; reflexivity)
  .
  - destruct (compare msg a) eqn:Hcmp.
    + apply (proj1 H) in Hcmp; subst. right. assumption.
    + destruct H0 as [Heq | Hin]; subst.
      * left; reflexivity.
      * right; assumption.
    + destruct H0 as [Heq | Hin]; subst.
      * right; left; reflexivity.
      * apply IHsigma in Hin. destruct Hin; try (left; assumption).
        right. right. assumption.
Qed.

Lemma add_in_sorted_list_in_rev {A} (compare : A -> A -> comparison) : forall msg msg' sigma,
  CompareStrictOrder compare ->
  msg = msg' \/ In msg' sigma ->
  In msg' (add_in_sorted_list_fn compare msg sigma).
Proof. 
  intros. induction sigma; simpl in H0
  ; try (destruct H0 as [H0 | H0]; subst; try inversion H0; left; reflexivity)
  .
  rewrite (or_comm (a = msg')) in H0. apply or_assoc in H0.
  destruct H0 as [HI | Heq].
  - apply IHsigma in HI. apply add_in_sorted_list_in in HI; try assumption.
    destruct HI as [Heq | Hin]; simpl; destruct (compare msg a) eqn:Hcmp
    ; try apply (proj1 H) in Hcmp; subst; try (left; reflexivity).
    + right. apply IHsigma. left; reflexivity.
    + right. assumption.
    + right; right; assumption.
    + right. apply IHsigma. right; assumption.
  - subst. simpl. destruct (compare msg msg'); try (left; reflexivity).
    right; left; reflexivity.
Qed.

Lemma add_in_sorted_list_iff {A} (compare : A -> A -> comparison) :
  CompareStrictOrder compare ->
  forall msg msg' sigma,
  In msg' (add_in_sorted_list_fn compare msg sigma) <->
  msg = msg' \/ In msg' sigma.
Proof.
  intros; split.
  - apply add_in_sorted_list_in; assumption.
  - apply add_in_sorted_list_in_rev; assumption.
Qed.

Lemma add_in_sorted_list_head {A} (compare : A -> A -> comparison) :
  CompareStrictOrder compare ->
  forall msg sigma,
  In msg (add_in_sorted_list_fn compare msg sigma).
Proof.
  intros.
  apply add_in_sorted_list_iff; try assumption. left; reflexivity.
Qed.

Lemma add_in_sorted_list_tail {A} (compare : A -> A -> comparison) :
  CompareStrictOrder compare ->
  forall msg sigma,
  incl sigma (add_in_sorted_list_fn compare msg sigma).
Proof.
  intros. intros x Hin.
  apply add_in_sorted_list_iff; try assumption. right. assumption.
Qed.

Lemma add_in_sorted_list_sorted  {A} (compare : A -> A -> comparison) :
  CompareStrictOrder compare ->
  forall msg sigma,
  LocallySorted (compare_lt compare) sigma ->
  LocallySorted (compare_lt compare) (add_in_sorted_list_fn compare msg sigma).
Proof.
  intros. apply compare_asymmetric_intro in H as Hasymm.
  induction H0; simpl; try constructor; destruct (compare msg a) eqn:Hcmpa.
  - constructor.
  - constructor; try assumption. constructor.
  - apply Hasymm in Hcmpa. constructor; try assumption. constructor.
  - constructor; assumption.
  - constructor; try assumption. constructor; assumption.
  - apply Hasymm in Hcmpa.
    simpl in IHLocallySorted. destruct (compare msg b) eqn:Hcmpb.
    + apply (proj1 H) in Hcmpb. subst. constructor; assumption.
    + constructor; assumption.
    + apply Hasymm in Hcmpb. constructor; assumption.
Qed.

(** Sorted lists as sets **)
Lemma set_In {A}  (lt : relation A) :
  StrictOrder lt ->
  forall x y s,
  LocallySorted lt (y :: s) ->
  In x s ->
  lt y x.
Proof.
  intros SO x y s LS IN. generalize dependent x. generalize dependent y.
  destruct SO as [_ HT]. unfold Transitive in HT.
  induction s.
  - intros y LS x IN. inversion IN.
  - intros y LS x IN.
    inversion LS; subst.
    inversion IN; subst.
    + assumption.
    + apply (IHs a H1 x) in H.
      apply (HT y a x H3 H).
Qed.

Lemma set_eq_first_equal {A}  (lt : relation A) :
  StrictOrder lt ->
  forall x1 x2 s1 s2,
  LocallySorted lt (x1 :: s1) ->
  LocallySorted lt (x2 :: s2) ->
  set_eq (x1 :: s1) (x2 :: s2) ->
  x1 = x2 /\ set_eq s1 s2.
Proof.
  intros SO x1 x2 s1 s2 LS1 LS2 SEQ. destruct SEQ as [IN1 IN2].
  assert (SO' := SO). destruct SO' as [IR TR].
  assert (x12 : x1 = x2).
  {
    unfold incl in *. destruct (IN1 x1). { simpl. left. reflexivity. }
    - subst. reflexivity.
    - apply (set_In lt SO x1 x2 s2 LS2) in H.
      destruct (IN2 x2). { simpl. left. reflexivity. }
      * subst. apply IR in H. inversion H.
      * apply (set_In lt SO x2 x1 s1 LS1) in H0.
        apply (TR x1 x2 x1 H0) in H. apply IR in H. inversion H.
  }
  subst.
  split; try reflexivity.
  split; unfold incl.
  - intros. assert (INa1 := H).
    apply (set_In lt SO _ _ _ LS1) in H. 
    destruct (IN1 a).
    { simpl. right. assumption. }
    + subst. apply IR in H. inversion H.
    + assumption.
  - intros. assert (INa2 := H).
    apply (set_In lt SO _ _ _ LS2) in H. 
    destruct (IN2 a).
    { simpl. right. assumption. }
    + subst. apply IR in H. inversion H.
    + assumption.
Qed.

Lemma set_equality_predicate {A}  (lt : relation A) :
  StrictOrder lt ->
  forall s1 s2,
  LocallySorted lt s1 ->
  LocallySorted lt s2 ->
  set_eq s1 s2 <-> s1 = s2.
Proof.
  intros SO s1 s2 LS1 LS2 . assert (SO' := SO). destruct SO' as [IR TR].
  split. 
  - generalize dependent s2. induction s1; destruct s2.
    + intros. reflexivity.
    + intros. destruct H. exfalso. apply (H0 a). simpl. left. reflexivity.
    + intros. destruct H. exfalso. apply (H a). simpl. left. reflexivity.
    + intros. apply (set_eq_first_equal lt SO  a a0 s1 s2 LS1 LS2) in H. destruct H; subst.
      apply Sorted_LocallySorted_iff in LS1. apply Sorted_inv in LS1. destruct LS1 as [LS1 _]. apply Sorted_LocallySorted_iff in LS1.
      apply Sorted_LocallySorted_iff in LS2. apply Sorted_inv in LS2. destruct LS2 as [LS2 _]. apply Sorted_LocallySorted_iff in LS2.
      apply (IHs1 LS1 s2 LS2) in H0. subst. reflexivity.
  - intros. subst. apply set_eq_refl.
Qed.