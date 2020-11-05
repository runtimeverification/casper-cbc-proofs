Require Import Coq.Bool.Bool.
Require Import List ListSet.
Require Import Lia.
Import ListNotations.

Require Import Coq.Logic.FinFun.

From CasperCBC.Lib Require Import Preamble.

Definition last_error {S} (l : list S) : option S :=
  match l with
  | [] => None
  | a :: t => Some (last t a)
  end.

Lemma unfold_last_hd {S} : forall (random a b : S) (l : list S),
  last (a :: (b :: l)) random = last (b :: l) random.
Proof.
  intros random h1 h2 tl.
  unfold last. reflexivity.
Qed.

Lemma swap_head_last {S} : forall (random a b c : S) (l : list S),
    last (a :: b :: c :: l) random = last (b :: a :: c :: l) random.
Proof.
  intros random h1 h2 s tl.
  induction tl as [| hd tl IHl].
  - reflexivity.
  - simpl. reflexivity.
Qed.

Lemma remove_hd_last {X} :
  forall (hd1 hd2 d1 d2 : X) (tl : list X),
    last (hd1 :: hd2 :: tl) d1 = last (hd2 :: tl) d2.
Proof.
  intros. induction tl.
  simpl. reflexivity.
  rewrite unfold_last_hd.
  rewrite unfold_last_hd in IHtl.
  rewrite unfold_last_hd.
  rewrite unfold_last_hd.
  destruct tl.
  reflexivity.
  do 2 rewrite unfold_last_hd in IHtl.
  do 2 rewrite unfold_last_hd.
  assumption.
Qed.

Lemma unroll_last {S} : forall (random a : S) (l : list S),
  last (a :: l) random = last l a.
Proof.
  induction l; try reflexivity.
  destruct l; try reflexivity.
  rewrite swap_head_last. rewrite unfold_last_hd. rewrite IHl.
  rewrite unfold_last_hd. reflexivity.
Qed.

Lemma last_app
  {A}
  (l1 l2 : list A)
  (def : A)
  : last (l1 ++ l2) def = last l2 (last l1 def).
Proof.
  generalize dependent def.
  induction l1; try reflexivity; intro def.
  remember last as lst; simpl; subst lst.
  repeat rewrite unroll_last.
  apply IHl1.
Qed.

Lemma last_map
  {A B}
  (f : A -> B)
  (h : A)
  (t : list A)
  (def : B)
  : last (map f (h :: t)) def = f (last t h).
Proof.
  generalize dependent def. generalize dependent h.
  induction t; try reflexivity; intros.
  rewrite map_cons.
  repeat rewrite unroll_last.
  apply IHt.
Qed.

Lemma incl_empty : forall A (l : list A),
  incl l nil -> l = nil.
Proof.
  intros. destruct l; try reflexivity.
  exfalso. destruct (H a). left. reflexivity.
Qed.

Lemma incl_singleton {A} : forall (l : list A) (a : A),
  incl l [a] ->
  forall b, In b l -> b = a.
Proof.
  intros. induction l; inversion H0; subst.
  - clear H0. destruct (H b); try (left; reflexivity); subst; try reflexivity.
    inversion H0.
  - apply IHl; try assumption.
    apply incl_tran with (a0 :: l); try assumption.
    apply incl_tl. apply incl_refl.
Qed.

Lemma filter_in : forall A (f : A -> bool) x s,
  In x s ->
  f x = true ->
  In x (filter f s).
Proof.
  intros. apply filter_In. split; assumption.
Qed.

Lemma filter_incl {A} (f : A -> bool) : forall s1 s2,
  incl s1 s2 ->
  incl (filter f s1) (filter f s2).
Proof.
  induction s1; intros; intro x; intros.
  - inversion H0.
  - simpl in H0. destruct (f a) eqn:Hfa.
    + destruct H0.
      * subst. apply filter_in; try assumption. apply H. left. reflexivity.
      * apply IHs1; try assumption. intro y; intro. apply H. right. assumption.
    + apply IHs1; try assumption. intro y; intro. apply H. right. assumption.
Qed.

Lemma filter_incl_fn {A} : forall (f : A -> bool) (g : A -> bool),
  (forall a, f a = true -> g a = true) ->
  forall s, incl (filter f s) (filter g s).
Proof.
  induction s; simpl.
  - apply incl_refl.
  - intro x; intros. destruct (f a) eqn:Hfa.
    + apply H in Hfa. rewrite Hfa. destruct H0.
      * subst. left. reflexivity.
      * right. apply IHs. assumption.
    + apply IHs in H0. destruct (g a).
      * right; assumption.
      * assumption.
Qed.

Lemma filter_length_fn
  {A : Type}
  (f g : A -> bool)
  (s : list A)
  (Hfg : Forall (fun a => f a = true -> g a = true) s)
  : length (filter f s) <= length (filter g s).
Proof.
  induction s; simpl.
  - lia.
  - inversion Hfg; subst. specialize (IHs H2).
  destruct (f a) eqn:Hfa.
    + rewrite H1; try reflexivity. simpl. lia.
    + destruct (g a); simpl; lia.
Qed.

Lemma filter_eq_fn {A} : forall (f : A -> bool) (g : A -> bool) s,
  (forall a, In a s -> f a = true <-> g a = true) ->
  filter f s = filter g s.
Proof.
  induction s; intros; try reflexivity. simpl.
  assert (IHs' : forall a : A, In a s -> f a = true <-> g a = true).
  { intros. apply H. right. assumption. }
  apply IHs in IHs'. clear IHs.
  destruct (f a) eqn:Hf.
  - apply H in Hf as Hg; try (left; reflexivity). rewrite Hg. rewrite IHs'. reflexivity.
  - assert (Hg : g a = false).
    {  destruct (g a) eqn:Hg; try reflexivity. apply H in Hg; try (left; reflexivity).
      rewrite <- Hg. assumption.
    }
    rewrite Hg. assumption.
Qed.

Lemma filter_nil
  {A : Type}
  (f : A -> bool)
  (l : list A)
  : Forall (fun a : A => f a = false) l
  <-> filter f l = [].
Proof.
  rewrite Forall_forall.
  split; intro Hnone.
  - induction l; try reflexivity.
    assert (Hno_a := Hnone a).
    assert (Hin_a : In a (a :: l)) by (left;reflexivity).
    specialize (Hno_a Hin_a).
    simpl. rewrite Hno_a.
    apply IHl.
    intros b Hin_b.
    apply Hnone.
    right.
    assumption.
  - induction l; intros x Hx; inversion Hx; subst; clear Hx
    ; simpl in Hnone.
    + destruct (f x) eqn:Hx; try reflexivity. inversion Hnone.
    + destruct (f a) eqn:Ha.
      * inversion Hnone.
      * apply IHl; assumption.
Qed.

Lemma existsb_first
  {A : Type}
  (l : list A)
  (f : A -> bool)
  (Hsomething : existsb f l = true) :
  exists (prefix : list A)
         (suffix : list A)
         (first : A),
         (f first = true) /\
         l = prefix ++ [first] ++ suffix /\
         (existsb f prefix = false).

Proof.
  generalize dependent l.
  induction l.
  - intros.
    simpl in *.
    discriminate Hsomething.
  - intros.
    unfold existsb in Hsomething.
    destruct (f a) eqn : eq_a.
    + simpl in Hsomething.
      exists [].
      exists l.
      exists a.
      split.
      assumption.
      simpl.
      intuition.
    + simpl in *.
      specialize (IHl Hsomething).
      destruct IHl as [prefix [suffix [first [Hf [Hconcat Hnone_before]]]]].
      exists (a :: prefix).
      exists suffix.
      exists first.
      split.
      assumption.
      split.
      rewrite Hconcat.
      auto.
      unfold existsb.
      rewrite eq_a.
      simpl.
      unfold existsb in Hnone_before.
      assumption.
Qed.

Lemma in_not_in : forall A (x y : A) l,
  In x l ->
  ~ In y l ->
  x <> y.
Proof.
  intros. intro; subst. apply H0. assumption.
Qed.

Definition inb {A} (Aeq_dec : forall x y:A, {x = y} + {x <> y}) (x : A) (xs : list A) :=
  if in_dec Aeq_dec x xs then true else false.

Lemma in_function {A}  (Aeq_dec : forall x y:A, {x = y} + {x <> y}) :
  PredicateFunction2 (@In A) (inb Aeq_dec).
Proof.
  intros x xs. unfold inb. destruct (in_dec Aeq_dec x xs); split; intros
  ; try assumption; try reflexivity; try contradiction; discriminate.
Qed.

Lemma in_correct `{EqDecision X} :
  forall (l : list X) (x : X),
    In x l <-> inb decide_eq x l = true.
Proof.
  intros s msg.
  apply in_function.
Qed.

Lemma in_correct_refl `{EqDecision X} :
  forall (l : list X) (x : X),
    In x l <-> inb decide_eq x l.
Proof.
  intros s msg.
  rewrite in_correct, Is_true_iff_eq_true.
  reflexivity.
Qed.

Lemma in_correct' `{EqDecision X} :
  forall (l : list X) (x : X),
    ~ In x l <-> inb decide_eq x l = false.
Proof.
  intros s msg.
  rewrite in_correct, not_true_iff_false.
  reflexivity.
Qed.

Definition inclb
  `{EqDecision A}
  (l1 l2 : list A)
  : bool
  := forallb (fun x : A => inb decide_eq x l2) l1.

Lemma incl_function `{EqDecision A} : PredicateFunction2 (@incl A) (inclb).
Proof.
  intros l1 l2. unfold inclb. rewrite forallb_forall.
  split; intros Hincl x Hx; apply in_correct; apply Hincl; assumption.
Qed.

Definition incl_correct `{EqDecision A}
  (l1 l2 : list A)
  : incl l1 l2 <-> inclb l1 l2 = true
  := incl_function l1 l2.

Lemma map_incl {A B} (f : B -> A) : forall s s',
  incl s s' ->
  incl (map f s) (map f s').
Proof.
  intros s s' Hincl fx Hin.
  apply in_map_iff .
  apply in_map_iff in Hin.
  destruct Hin as [x [Heq Hin]].
  exists x. split; try assumption. apply Hincl. assumption.
Qed.

Lemma existsb_forall {A} (f : A -> bool):
  forall l, existsb f l = false <-> forall x, In x l -> f x = false.
Proof.
  induction l; split; intros.
  - inversion H0.
  - reflexivity.
  - inversion H. apply orb_false_iff in  H2. destruct H2 as [Hfa Hex]. rewrite Hfa.
    rewrite Hex. simpl. destruct H0 as [Heq | Hin]; subst; try assumption.
    apply IHl; try assumption.
  - simpl. rewrite H; try (left; reflexivity). rewrite IHl; try reflexivity.
    intros. apply H. right. assumption.
Qed.

Definition app_cons {A}
  (a : A)
  (l : list A)
  : [a] ++ l = a :: l
  := eq_refl.

Lemma append_nodup_left {A}:
  forall (l1 l2 : list A), NoDup (l1 ++ l2) -> NoDup l1.
Proof.
  induction l1; intros.
  - constructor.
  - inversion H. apply IHl1 in H3. constructor; try assumption. intro. apply H2.
    apply in_app_iff. left. assumption.
Qed.

Lemma append_nodup_right {A}:
  forall (l1 l2 : list A), NoDup (l1 ++ l2) -> NoDup l2.
Proof.
  induction l1; intros.
  - simpl in H. assumption.
  - simpl in H. inversion H. apply IHl1 in H3. assumption.
Qed.

Lemma nodup_append {A} : forall (l1 l2 : list A),
  NoDup l1 ->
  NoDup l2 ->
  (forall a, In a l1 -> ~ In a l2) ->
  (forall a, In a l2 -> ~ In a l1) ->
  NoDup (l1 ++ l2).
Proof.
  induction l1; simpl; intros; try assumption.
  inversion H; subst; clear H. constructor.
  - intro. apply in_app_iff in H. destruct H as [Inl1 | InL2].
    + apply H5. assumption.
    + apply (H1 a); try assumption.
      left. reflexivity.
  - apply IHl1; try assumption; intros.
    + apply H1. right. assumption.
    + apply H2 in H. intro. apply H. right. assumption.
Qed.

Lemma last_is_last {A} : forall (l : list A) (x dummy: A),
  last (l ++ [x]) dummy = x.
Proof.
  induction l; try reflexivity; intros.
  rewrite <- app_comm_cons. specialize (IHl x dummy). rewrite <- IHl at 2. simpl.
  destruct l; simpl; reflexivity.
Qed.

Lemma last_error_is_last {A} : forall (l : list A) (x : A),
  last_error (l ++ [x]) = Some x.
Proof.
  destruct l; try reflexivity; intros; simpl. apply f_equal. apply last_is_last.
Qed.

(** Polymorphic list library **)

Fixpoint is_member {W} `{StrictlyComparable W} (w : W) (l : list W) : bool :=
  match l with
  | [] => false
  | hd :: tl => match compare w hd with
              | Eq => true
              | _ => is_member w tl
              end
  end.

Definition compareb {A} `{StrictlyComparable A} (a1 a2 : A) : bool :=
  match compare a1 a2 with
  | Eq => true
  | _ => false
  end.

Lemma is_member_correct {W} `{StrictlyComparable W}
  : forall l (w : W), is_member w l = true <-> In w l.
Proof.
  intros l w.
  induction l as [|hd tl IHl].
  - split; intro H'.
    + unfold is_member in H'; inversion H'.
    + inversion H'.
  - split; intro H'.
    + simpl in H'.
      destruct (compare w hd) eqn:Hcmp;
        try (right; apply IHl; assumption ).
      apply StrictOrder_Reflexive in Hcmp.
      left. symmetry; assumption.
    + apply in_inv in H'.
      destruct H' as [eq | neq].
      rewrite eq.
      simpl.
      rewrite compare_eq_refl.
      reflexivity.
      rewrite <- IHl in neq.
      simpl. assert (H_dec := compare_eq_dec w hd).
      destruct H_dec as [Heq | Hneq].
      rewrite Heq. rewrite compare_eq_refl. reflexivity.
      destruct (compare w hd); try reflexivity;
        assumption.
Qed.

Lemma is_member_correct' {W} `{StrictlyComparable W}
  : forall l (w : W), is_member w l = false <-> ~ In w l.
Proof.
  intros.
  apply mirror_reflect.
  intros; apply is_member_correct.
Qed.

Lemma In_app_comm {X} : forall l1 l2 (x : X), In x (l1 ++ l2) <-> In x (l2 ++ l1).
Proof.
  intros l1 l2 x; split; intro H_in;
  apply in_or_app; apply in_app_or in H_in;
    destruct H_in as [cat | dog];
    tauto.
Qed.

Lemma nth_error_last
  {A : Type}
  (l : list A)
  (n : nat)
  (Hlast: S n = length l)
  (_last : A)
  : nth_error l n = Some (last l _last).
Proof.
  generalize dependent _last.
  generalize dependent l.
  induction n; intros.
  - destruct l; inversion Hlast. symmetry in H0.
    apply length_zero_iff_nil in H0. subst. reflexivity.
  - destruct l; inversion Hlast.
    specialize (IHn l H0 _last). rewrite unroll_last.
    simpl. rewrite IHn. f_equal.
    destruct l; inversion H0.
    repeat rewrite unroll_last.
    reflexivity.
Qed.

Fixpoint list_suffix
  {A : Type}
  (l : list A)
  (n : nat)
  : list A
  := match n,l with
    | 0,_ => l
    | _,[] => []
    | S n, a :: l => list_suffix l n
    end.

Lemma list_suffix_map
  {A B : Type}
  (f : A -> B)
  (l : list A)
  (n : nat)
  : List.map f (list_suffix l n) = list_suffix (List.map f l) n.
Proof.
  generalize dependent l. induction n; intros [|a l]; try reflexivity.
  simpl.
  apply IHn.
Qed.

Fixpoint list_prefix
  {A : Type}
  (l : list A)
  (n : nat)
  : list A
  := match n,l with
    | 0,_ => []
    | _,[] => []
    | S n, a :: l => a :: list_prefix l n
    end.

Lemma list_prefix_split
  {A : Type}
  (l left right: list A)
  (left_len : nat)
  (Hlen : left_len = length left)
  (Hsplit : l = left ++ right) :
  list_prefix l left_len = left.

Proof.
  generalize dependent l.
  generalize dependent left.
  generalize dependent right.
  generalize dependent left_len.
  induction left_len.
  - intros.
    symmetry in Hlen.
    rewrite length_zero_iff_nil in Hlen.
    rewrite Hlen.
    unfold list_prefix.
    destruct l;
    reflexivity.
  - intros.
    destruct left.
    + discriminate Hlen.
    + assert (left_len = length left). {
        simpl in Hlen.
        inversion Hlen.
        intuition.
      }
      specialize (IHleft_len right left H (left ++ right) eq_refl).
      rewrite Hsplit.
      simpl.
      rewrite IHleft_len.
      reflexivity.
Qed.

Lemma list_prefix_map
  {A B : Type}
  (f : A -> B)
  (l : list A)
  (n : nat)
  : List.map f (list_prefix l n) = list_prefix (List.map f l) n.
Proof.
  generalize dependent l. induction n; intros [|a l]; try reflexivity.
  simpl.
  f_equal.
  apply IHn.
Qed.

Lemma list_prefix_length
  {A : Type}
  (l : list A)
  (n : nat)
  (Hlen : n <= length l)
  : length (list_prefix l n) = n.
Proof.
  generalize dependent l. induction n; intros [|a l] Hlen; try reflexivity.
  - inversion Hlen.
  - simpl in *. f_equal.
    apply IHn.
    lia.
Qed.

Lemma list_suffix_length
  {A : Type}
  (l : list A)
  (n : nat)
  : length (list_suffix l n) = length l - n.
Proof.
  generalize dependent l. induction n; intros [|a l]; try reflexivity.
  simpl. apply IHn.
Qed.

Lemma list_prefix_prefix
  {A : Type}
  (l : list A)
  (n1 n2 : nat)
  (Hn: n1 <= n2)
  : list_prefix (list_prefix l n2) n1 = list_prefix l n1.
Proof.
  generalize dependent n1. generalize dependent n2.
  induction l; intros [|n2] [|n1] Hn; try reflexivity.
  - inversion Hn.
  - simpl. f_equal. apply IHl. lia.
Qed.

Lemma list_prefix_suffix
  {A : Type}
  (l : list A)
  (n : nat)
  : list_prefix l n ++ list_suffix l n = l.
  Proof.
   generalize dependent n. induction l; intros [|n]; try reflexivity.
   simpl.
   f_equal. apply IHl.
  Qed.

Definition list_segment
  {A : Type}
  (l : list A)
  (n1 n2 : nat)
  := list_suffix (list_prefix l n2) n1.

Lemma list_prefix_segment_suffix
  {A : Type}
  (l : list A)
  (n1 n2 : nat)
  (Hn : n1 <= n2)
  : list_prefix l n1 ++ list_segment l n1 n2 ++ list_suffix l n2 = l.
Proof.
  rewrite <- (list_prefix_suffix l n2) at 4.
  rewrite app_assoc.
  f_equal.
  unfold list_segment.
  rewrite <- (list_prefix_suffix (list_prefix l n2) n1) at 2.
  f_equal.
  symmetry.
  apply list_prefix_prefix.
  assumption.
Qed.

Definition Forall_hd
  {A : Type}
  {P : A -> Prop}
  {a : A}
  {l : list A}
  (Hs : Forall P (a :: l))
  : P a.
Proof.
  inversion Hs. subst. exact H1.
Defined.

Definition Forall_tl
  {A : Type}
  {P : A -> Prop}
  {a : A}
  {l : list A}
  (Hs : Forall P (a :: l))
  : Forall P l.
Proof.
  inversion Hs. subst. exact H2.
Defined.

Fixpoint list_annotate
  {A : Type}
  (P : A -> Prop)
  (l : list A)
  (Hs : Forall P l)
  : list (sig P).
Proof.
  destruct l as [| a l].
  - exact [].
  -
  exact ((exist P a (Forall_hd Hs)) :: list_annotate A P l (Forall_tl Hs)).
Defined.

Lemma list_annotate_unroll
  {A : Type}
  (P : A -> Prop)
  (a : A)
  (l : list A)
  (Hs : Forall P (a :: l))
  : list_annotate P (a :: l) Hs = exist P a (Forall_hd Hs) ::  list_annotate P l (Forall_tl Hs).
Proof.
  reflexivity.
Qed.

Lemma in_list_annotate_forget
  {A : Type}
  (P : A -> Prop)
  (l : list A)
  (Hs : Forall P l)
  (xP : sig P)
  (Hin : In xP (list_annotate P l Hs))
  : In (proj1_sig xP) l.
Proof.
  induction l.
  - inversion Hin.
  - rewrite list_annotate_unroll in Hin.
    destruct Hin as [Heq | Hin].
    + subst xP. left. reflexivity.
    + right. specialize (IHl (Forall_tl Hs)). apply IHl. assumption.
Qed.

Lemma nth_error_list_annotate
  {A : Type}
  (P : A -> Prop)
  (l : list A)
  (Hs : Forall P l)
  (n : nat)
  : exists (oa : option (sig P)),
    nth_error (list_annotate P l Hs) n = oa
    /\ option_map (@proj1_sig _ _) oa = nth_error l n.
Proof.
  generalize dependent l.
  induction n; intros [| a l] Hs.
  - exists None. split; reflexivity.
  - inversion Hs; subst. exists (Some (exist _ a (Forall_hd Hs))).
    rewrite list_annotate_unroll.
    split; reflexivity.
  - exists None. split; reflexivity.
  - rewrite list_annotate_unroll.
    specialize (IHn l (Forall_tl Hs)).
    destruct IHn as [oa [Hoa Hnth]].
    exists oa.
    split; assumption.
Qed.

Fixpoint nth_error_filter_index
  {A}
  (f : A -> bool)
  (l : list A)
  (n : nat)
  :=
  match l with
  | [] => None
  | a :: l =>
    match f a with
    | false => option_map S (nth_error_filter_index f l n)
    | true =>
      match n with
      | 0 => Some 0
      | S n => option_map S (nth_error_filter_index f l n)
      end
    end
  end.

Lemma nth_error_filter_index_le
  {A}
  (f : A -> bool)
  (l : list A)
  (n1 n2 : nat)
  (Hle : n1 <= n2)
  (in1 in2 : nat)
  (Hin1 : nth_error_filter_index f l n1 = Some in1)
  (Hin2 : nth_error_filter_index f l n2 = Some in2)
  : in1 <= in2.
Proof.
  generalize dependent in2.
  generalize dependent in1.
  generalize dependent n2.
  generalize dependent n1.
  induction l; intros.
  - inversion Hin1.
  - simpl in Hin1. simpl in Hin2.
    destruct (f a) eqn:fa.
    + destruct n1; destruct n2.
      * inversion Hin1; inversion Hin2; subst; assumption.
      * destruct (nth_error_filter_index f l n2)
        ; inversion Hin1; inversion Hin2; subst.
        lia.
      * inversion Hle.
      * { destruct in1, in2.
        - lia.
        - lia.
        - destruct (nth_error_filter_index f l n2); inversion Hin2.
        - assert (Hle' : n1 <= n2) by lia.
          specialize (IHl n1 n2 Hle').
          destruct (nth_error_filter_index f l n1) eqn:Hin1'; inversion Hin1;
          subst; clear Hin1.
          destruct (nth_error_filter_index f l n2) eqn:Hin2'; inversion Hin2
          ; subst; clear Hin2.
          specialize (IHl in1 eq_refl in2 eq_refl).
          lia.
        }
    + specialize (IHl n1 n2 Hle).
      destruct (nth_error_filter_index f l n1) eqn:Hin1'; inversion Hin1
      ; subst; clear Hin1.
      destruct (nth_error_filter_index f l n2) eqn:Hin2'; inversion Hin2
      ; subst; clear Hin2.
      specialize (IHl n eq_refl n0 eq_refl).
      lia.
Qed.

Lemma nth_error_filter
  {A}
  (f : A -> bool)
  (l : list A)
  (n : nat)
  (a : A)
  (Hnth : nth_error (filter f l) n = Some a)
  : exists (nth : nat),
    nth_error_filter_index f l n = Some nth
    /\ nth_error l nth = Some a.
Proof.
  generalize dependent a. generalize dependent n.
  induction l.
  - intros; simpl in Hnth. destruct n; inversion Hnth.
  - intros. simpl in Hnth. simpl . destruct (f a).
    + destruct n.
      * inversion Hnth; subst. exists 0; split; reflexivity.
      * simpl in Hnth.
        specialize (IHl n a0 Hnth).
        destruct IHl as [nth [Hnth' Ha0]].
        exists (S nth).
        split; try assumption.
        rewrite Hnth'.
        reflexivity.
    + specialize (IHl n a0 Hnth).
      destruct IHl as [nth [Hnth' Ha0]].
      exists (S nth).
      split; try assumption.
      rewrite Hnth'.
      reflexivity.
Qed.

Fixpoint filter_Forall
  `{forall a : A, Decision (P a)}
  (l : list A)
  : Forall P (filter (fun a => bool_decide (P a)) l).
Proof.
  destruct l; simpl.
  - exact (Forall_nil P).
  - specialize (filter_Forall A P _ l).
    rewrite <- decide_bool_decide.
    destruct (decide (P a)).
    + constructor; assumption.
    + assumption.
Defined.

Lemma list_prefix_nth
  {A : Type}
  (s : list A)
  (n : nat)
  (i : nat)
  (Hi : i < n)
  : nth_error (list_prefix s n) i = nth_error s i.
Proof.
  generalize dependent n. generalize dependent s.
  induction i; intros [|a s] [|n] Hi; try reflexivity.
  - inversion Hi.
  - inversion Hi.
  - simpl.
    assert (Hi': i < n) by lia.
    specialize (IHi s n Hi').
    rewrite IHi.
    reflexivity.
Qed.

Lemma nth_error_length
  {A : Type}
  (l : list A)
  (n : nat)
  (a : A)
  (Hnth : nth_error l n = Some a)
  : S n <= length l.
Proof.
  generalize dependent a. generalize dependent l.
  induction n; intros [|a l] b Hnth; simpl; inversion Hnth.
  - lia.
  - specialize (IHn l b H0).
    lia.
Qed.

Lemma list_prefix_nth_last
  {A : Type}
  (l : list A)
  (n : nat)
  (nth : A)
  (Hnth : nth_error l n = Some nth)
  (_last : A)
  : nth = last (list_prefix l (S n)) _last.
Proof.
  specialize (nth_error_length l n nth Hnth); intro Hlen.
  specialize (list_prefix_length l (S n) Hlen); intro Hpref_len.
  symmetry in Hpref_len.
  specialize (list_prefix_nth l (S n) n); intro Hpref.
  rewrite <- Hpref in Hnth.
  - specialize (nth_error_last (list_prefix l (S n)) n Hpref_len _last); intro Hlast.
    rewrite Hlast in Hnth. inversion Hnth.
    reflexivity.
  - constructor.
Qed.

Lemma list_suffix_nth
  {A : Type}
  (s : list A)
  (n : nat)
  (i : nat)
  (Hi : n <= i)
  : nth_error (list_suffix s n) (i - n) = nth_error s i.
Proof.
  generalize dependent n. generalize dependent s.
  induction i; intros [|a s] [|n] Hi; try reflexivity.
  - inversion Hi.
  - simpl. apply nth_error_None. simpl. lia.
  - simpl.
    apply IHi.
    lia.
Qed.

Lemma list_suffix_last
  {A : Type}
  (l : list A)
  (i : nat)
  (Hlt : i < length l)
  (_default : A)
  : last (list_suffix l i) _default  = last l _default.
Proof.
  generalize dependent l. induction i; intros [|a l] Hlt
  ; try reflexivity.
  simpl in Hlt.
  assert (Hlt': i < length l) by lia.
  specialize (IHi l Hlt').
  rewrite unroll_last. simpl.
  rewrite IHi.
  destruct l.
  - inversion Hlt; lia.
  - rewrite unroll_last. rewrite unroll_last. reflexivity.
Qed.

Lemma list_suffix_last_default
  {A : Type}
  (l : list A)
  (i : nat)
  (Hlast : i = length l)
  (_default : A)
  : last (list_suffix l i) _default  = _default.
Proof.
  generalize dependent l. induction i; intros [|a l] Hlast
  ; try reflexivity.
  - inversion Hlast.
  - simpl in Hlast. inversion Hlast.
  specialize (IHi l H0).
  simpl. subst.
  assumption.
Qed.

Lemma list_segment_nth
  {A : Type}
  (l : list A)
  (n1 n2 : nat)
  (Hn : n1 <= n2)
  (i : nat)
  (Hi1 : n1 <= i)
  (Hi2 : i < n2)
  : nth_error (list_segment l n1 n2) (i - n1) = nth_error l i.
Proof.
  unfold list_segment.
  rewrite list_suffix_nth; try assumption.
  apply list_prefix_nth.
  assumption.
Qed.

Lemma list_segment_app
  {A : Type}
  (l : list A)
  (n1 n2 n3 : nat)
  (H12 : n1 <= n2)
  (H23 : n2 <= n3)
  : list_segment l n1 n2 ++ list_segment l n2 n3 = list_segment l n1 n3.
Proof.
  assert (Hle : n1 <= n3) by lia.
  specialize (list_prefix_segment_suffix l n1 n3 Hle); intro Hl1.
  specialize (list_prefix_segment_suffix l n2 n3 H23); intro Hl2.
  rewrite <- Hl2 in Hl1 at 4. clear Hl2.
  repeat rewrite app_assoc in Hl1.
  apply app_inv_tail in Hl1.
  specialize (list_prefix_suffix (list_prefix l n2) n1); intro Hl2.
  specialize (list_prefix_prefix l n1 n2 H12); intro Hl3.
  rewrite Hl3 in Hl2.
  rewrite <- Hl2 in Hl1.
  rewrite <- app_assoc in Hl1.
  apply app_inv_head in Hl1.
  symmetry.
  assumption.
Qed.

Lemma list_segment_singleton
  {A : Type}
  (l : list A)
  (n : nat)
  (a : A)
  (Hnth : nth_error l n = Some a)
  : list_segment l n (S n) = [a].
Proof.
  unfold list_segment.
  assert (Hle : S n <= length l)
    by (apply nth_error_length in Hnth; assumption).
  assert (Hlt : n < length (list_prefix l (S n)))
    by (rewrite list_prefix_length; try constructor; assumption).
  specialize (list_suffix_last (list_prefix l (S n)) n Hlt a); intro Hlast1.
  specialize (list_prefix_nth_last l n a Hnth a); intro Hlast2.
  rewrite <- Hlast2 in Hlast1.
  specialize (list_suffix_length (list_prefix l (S n)) n).
  rewrite list_prefix_length; try assumption.
  intro Hlength.
  assert (Hs: S n - n = 1) by lia.
  rewrite Hs in Hlength.
  remember (list_suffix (list_prefix l (S n)) n) as x.
  clear -Hlength Hlast1.
  destruct x; inversion Hlength.
  destruct x; inversion H0.
  simpl in Hlast1; subst; reflexivity.
Qed.

Lemma nth_error_map
  {A B : Type}
  (f : A -> B)
  (l : list A)
  (n : nat)
  : nth_error (List.map f l) n = option_map f (nth_error l n).
Proof.
  generalize dependent n.
  induction l; intros [|n]; try reflexivity; simpl.
  apply IHl.
Qed.

Lemma forall_finite
  {index : Type}
  {index_listing : list index}
  (Hfinite_index : Full index_listing)
  (P : index -> Prop)
  : (forall n : index, P n) <-> Forall P index_listing.
Proof.
  split; intros.
  - apply Forall_forall; intros. apply H.
  - rewrite Forall_forall in H.
    apply H. apply Hfinite_index.
Qed.

Lemma exists_finite
  {index : Type}
  {index_listing : list index}
  (Hfinite_index : Full index_listing)
  (P : index -> Prop)
  : (exists n : index, P n) <-> List.Exists P index_listing.
Proof.
  split; intros.
  - apply Exists_exists; intros.
    destruct H as [n H].
    exists n.
    split; try assumption.
    apply Hfinite_index.
  - rewrite Exists_exists in H.
    destruct H as [n [_ H]].
    exists n. assumption.
Qed.

Instance Exists_dec `{forall (a : A), Decision (P a)} l : Decision (Exists P l).
Proof.
  induction l.
  - right. intro Hl. inversion Hl.
  - destruct (decide (P a)) as [Pa | Pna].
    + left. left. assumption.
    + destruct IHl as [Pl | Pnl].
      * left. right. assumption.
      * right. intro Hl. inversion Hl; subst; contradiction.
Qed.

Definition map_option
  {A B : Type}
  (f : A -> option B)
  : list A -> list B
  :=
  fold_right
    (fun x lb =>
      match f x with
      | None => lb
      | Some b => b :: lb
      end
    )
    [].

Lemma map_option_length
  {A B : Type}
  (f : A -> option B)
  (l : list A)
  (Hfl : Forall (fun a => f a <> None) l)
  : length (map_option f l) = length l.
Proof.
  induction l; try reflexivity.
  inversion Hfl; subst.
  spec IHl H2.
  simpl.
  destruct (f a); try (elim H1; reflexivity).
  simpl. f_equal. assumption.
Qed.

Lemma map_option_nth
  {A B : Type}
  (f : A -> option B)
  (l : list A)
  (Hfl : Forall (fun a => f a <> None) l)
  (n := length l)
  (i : nat)
  (Hi : i < n)
  (dummya : A)
  (dummyb : B)
  : Some (nth i (map_option f l) dummyb) = f (nth i l dummya).
Proof.
  generalize dependent i.
  induction l; intros; simpl in *. { lia. }
  inversion Hfl. subst. spec IHl H2.
  destruct (f a) eqn: Hfa; try (elim H1; reflexivity).
  symmetry in Hfa.
  destruct i; try assumption.
  spec IHl i.
  spec IHl. { lia. }
  assumption.
Qed.


Lemma in_map_option
  {A B : Type}
  (f : A -> option B)
  (l : list A)
  (b : B)
  : In b (map_option f l) <-> exists a : A, In a l /\ f a = Some b.
Proof.
  split.
  - intro Hin.
    induction l; try inversion Hin.
    simpl in Hin. destruct (f a) eqn:Hfa.
    + destruct Hin as [Heq | Hin]; subst.
      * exists a.
        split; try assumption.
        left. reflexivity.
      * specialize (IHl Hin). destruct IHl as [a' [Hin' Hfa']].
        exists a'. split; try assumption.
        right. assumption.
    + specialize (IHl Hin). destruct IHl as [a' [Hin' Hfa']].
      exists a'. split; try assumption.
      right. assumption.
  - induction l; intros [a' [Hin' Hfa']]; try inversion Hin'; subst; clear Hin'.
    + simpl. rewrite Hfa'. left. reflexivity.
    + simpl. destruct (f a) eqn:Hfa.
      * right. apply IHl. exists a'. split; try assumption.
      * apply IHl. exists a'. split; try assumption.
Qed.

Lemma nth_error_eq
  {A : Type}
  (l1 l2 : list A)
  (Hnth: forall n : nat, nth_error l1 n = nth_error l2 n)
  : l1 = l2.
Proof.
  generalize dependent l2.
  induction l1; intros [| a2 l2] Hnth; try reflexivity.
  - specialize (Hnth 0); simpl in Hnth. inversion Hnth.
  - specialize (Hnth 0); simpl in Hnth. inversion Hnth.
  - assert (H0 := Hnth 0). simpl in H0.
    inversion H0; subst.
    f_equal.
    apply IHl1.
    intro n.
    specialize (Hnth (S n)).
    assumption.
Qed.

Lemma occurrences_ordering
  {A : Type}
  (a b : A)
  (la1 la2 lb1 lb2 : list A)
  (Heq : la1 ++ a :: la2 = lb1 ++ b :: lb2)
  (Ha : ~In a (b :: lb2))
  : exists lab : list A, lb1 = la1 ++ a :: lab.
Proof.
  generalize dependent lb2. generalize dependent la2.
  generalize dependent b. generalize dependent lb1.
  generalize dependent a.
  induction la1; intros; destruct lb1 as [|b0 lb1]; simpl in *
  ; inversion Heq; subst.
  - elim Ha. left. reflexivity.
  - exists lb1. reflexivity.
  - elim Ha. right. apply in_app_iff. right. left. reflexivity.
  - specialize (IHla1 a0 lb1 b la2 lb2 H1 Ha).
    destruct IHla1 as [la0b Hla0b].
    exists la0b. subst. reflexivity.
Qed.

Lemma exists_first
  {A : Type}
  (l : list A)
  (P : A -> Prop)
  (Pdec : forall a : A, {P a } + {~P a})
  (Hsomething : Exists P l) :
  exists (prefix : list A)
         (suffix : list A)
         (first : A),
         (P first) /\
         l = prefix ++ [first] ++ suffix /\
         ~Exists P prefix.
Proof.
  induction l.
  - inversion Hsomething.
  - destruct (Pdec a).
    + exists []. exists l. exists a. repeat split; try assumption.
      intro H; inversion H.
    + assert (Hl : Exists P l).
      { inversion Hsomething; subst; try (elim n; assumption). assumption. }
      specialize (IHl Hl).
      destruct IHl as [prefix [suffix [first [Hfirst [Heq Hprefix]]]]].
      exists (a :: prefix). exists suffix. exists first. repeat split; try assumption.
      * simpl. subst. reflexivity.
      * intro Hprefix'. inversion Hprefix'; try (elim n; assumption).
        elim Hprefix. assumption.
Qed.

Lemma in_fast
  {A : Type}
  (l : list A)
  (a : A)
  (b : A)
  (Hin : In a (b :: l))
  (Hneq : b <> a) :
  In a l.
Proof.
  destruct Hin.
  - subst. elim Hneq. reflexivity.
  - assumption.
Qed.

Lemma union_fold
  `{EqDecision A}
  (haystack : list (list A))
  (a : A) :
  In a (fold_right (set_union decide_eq) [] haystack)
  <->
  exists (needle : list A), (In a needle) /\ (In needle haystack).
Proof.
  split.
  - generalize dependent a.
    generalize dependent haystack.
    induction haystack.
    + intros.
      simpl in H.
      intuition.
    + intros.
      unfold fold_right in H.
      rewrite set_union_iff in H.
      destruct H.
      * exists a.
        split.
        assumption.
        simpl.
        left.
        reflexivity.
      * unfold fold_right in IHhaystack.
        specialize (IHhaystack a0 H).
        destruct IHhaystack as [needle [Hin1 Hin2]].
        exists needle.
        split.
        assumption.
        intuition.
   - generalize dependent a.
     generalize dependent haystack.
     induction haystack.
     + intros.
       simpl in *.
       destruct H as [_ [_ Hfalse]].
       assumption.
     + intros.
       destruct H as [needle [Hin Hin2]].
       destruct Hin2.
       * simpl.
         rewrite set_union_iff.
         left.
         rewrite H.
         assumption.
       * simpl.
         rewrite set_union_iff.
         right.
         specialize (IHhaystack a0).
         apply IHhaystack.
         exists needle.
         split;
         assumption.
Qed.

Fixpoint one_element_decompositions
  {A : Type}
  (l : list A)
  : list (list A * A * list A)
  :=
  match l with
  | [] => []
  | a :: l' =>
    ([], a, l')
    :: map
      (fun t => match t with (l1, b, l2) => (a :: l1, b, l2) end)
      (one_element_decompositions l')
  end.

Lemma in_one_element_decompositions_iff
  {A : Type}
  (l : list A)
  (pre suf : list A)
  (x : A)
  : In (pre, x, suf) (one_element_decompositions l)
  <-> pre ++ [x] ++ suf = l.
Proof.
  revert suf. revert x. revert pre.
  induction l; intros pre x suf; split; simpl; intro H.
  - inversion H.
  - specialize (app_cons_not_nil pre suf x)
    ; intro contra; elim contra. symmetry. assumption.
  - destruct H as [Heq | Hin].
    + inversion Heq. subst. simpl. reflexivity.
    + apply in_map_iff in Hin.
      destruct Hin as [x0 [Heq Hin]].
      destruct x0 as ((prex0,x0),sufx0).
      specialize (IHl prex0 x0 sufx0).
      apply IHl in Hin.
      subst l.
      inversion Heq. reflexivity.
  - destruct pre.
    + left. inversion H. reflexivity.
    + right. apply in_map_iff.
      rewrite <- app_comm_cons in H.
      inversion H. subst. clear H.
      exists (pre, x, suf).
      split; try reflexivity.
      apply IHl. reflexivity.
Qed.

Definition two_element_decompositions
  {A : Type}
  (l : list A)
  : list (list A * A * list A * A * list A)
  :=
  flat_map
    (fun t =>
      match t with
        (l1, e1, l2) =>
        map
          (fun t => match t with (l2',e2, l3) => (l1, e1, l2', e2, l3) end)
          (one_element_decompositions l2)
      end
    )
    (one_element_decompositions l).

Lemma in_two_element_decompositions_iff
  {A : Type}
  (l : list A)
  (pre mid suf : list A)
  (x y : A)
  : In (pre, x, mid, y, suf) (two_element_decompositions l)
  <-> pre ++ [x] ++ mid ++ [y] ++ suf = l.
Proof.
  unfold two_element_decompositions.
  rewrite in_flat_map.
  split.
  - intros [((pre', x'), sufx) [Hdecx Hin]].
    apply in_map_iff in Hin.
    destruct Hin as [((mid', y'), suf') [Hdec Hin]].
    inversion Hdec. subst. clear Hdec.
    apply in_one_element_decompositions_iff in Hdecx.
    apply in_one_element_decompositions_iff in Hin.
    subst sufx l. reflexivity.
  - remember (mid ++ [y] ++ suf) as sufx.
    intro H.
    exists (pre, x, sufx). apply in_one_element_decompositions_iff in H.
    split; try assumption.
    apply in_map_iff. exists (mid, y, suf).
    split; try reflexivity.
    apply in_one_element_decompositions_iff. symmetry. assumption.
Qed.

Lemma order_decompositions
  {A : Type}
  (pre1 suf1 pre2 suf2 : list A)
  (Heq : pre1 ++ suf1 = pre2 ++ suf2)
  : pre1 = pre2
  \/ (exists suf1', pre1 = pre2 ++ suf1')
  \/ (exists suf2', pre2 = pre1 ++ suf2').
Proof.
  remember (pre1 ++ suf1) as l.
  generalize dependent Heq.
  generalize dependent Heql.
  revert pre1 suf1 pre2 suf2.
  induction l; intros.
  - left.
    symmetry in Heql. apply app_eq_nil in Heql. destruct Heql as [Hpre1 _]. subst pre1.
    symmetry in Heq. apply app_eq_nil in Heq. destruct Heq as [Hpre2 _]. subst pre2.
    reflexivity.
  - destruct pre1 as [| a1 pre1]; destruct pre2 as [|a2 pre2].
    + left. reflexivity.
    + right. right. exists (a2 :: pre2). reflexivity.
    + right. left. exists (a1 :: pre1). reflexivity.
    + inversion Heql. subst a1. clear Heql.
      inversion Heq. subst a2. clear Heq.
      specialize (IHl pre1 suf1 pre2 suf2 H1 H2).
      destruct IHl as [Heq | [Hgt | Hlt]].
      * left. f_equal. assumption.
      * destruct Hgt as [suf1' Hgt].
        right. left. exists suf1'. simpl. f_equal. assumption.
      * destruct Hlt as [suf2' Hlt].
        right. right. exists suf2'. simpl. f_equal. assumption.
Qed.
