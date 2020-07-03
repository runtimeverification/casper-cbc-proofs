Require Import Coq.Lists.ListSet.
Require Import List.
Import ListNotations.

Require Import CasperCBC.Lib.Preamble.
Require Import CasperCBC.Lib.ListExtras.


Lemma eq_dec_left {A} (Aeq_dec : forall x y:A, {x = y} + {x <> y}) : forall v,
  exists n, Aeq_dec v v = left n.
Proof.
  intros.  destruct (Aeq_dec v v) eqn:Hv.
  - exists e. reflexivity.
  - exfalso. apply n. reflexivity.
Qed.


Lemma eq_dec_right {A} (Aeq_dec : forall x y:A, {x = y} + {x <> y}) : forall x y,
  x <> y ->
  exists n, Aeq_dec x y = right n.
Proof.
  intros.  destruct (Aeq_dec x y) eqn:Hv.
  - exfalso. apply H. assumption.
  - exists n. reflexivity.
Qed.

Definition set_eq {A} (s1 s2 : set A) : Prop :=
  incl s1 s2 /\ incl s2 s1.

Lemma set_eq_empty
  {A}
  : forall (l : list A),
    set_eq l [] -> l = [].
Proof.
  intros.
  destruct l as [|hd tl].
  - reflexivity.
  - destruct H.
    spec H hd (in_eq hd tl).
    inversion H.
Qed.

Lemma set_eq_proj1 {A} : forall (s1 s2 : set A),
  set_eq s1 s2 ->
  incl s1 s2.
Proof.
  intros. destruct H. assumption.
Qed.

Lemma set_eq_proj2 {A} : forall (s1 s2 : set A),
  set_eq s1 s2 ->
  incl s2 s1.
Proof.
  intros. destruct H. assumption.
Qed.

Lemma set_eq_refl {A} : forall (s : list A), set_eq s s.
Proof.
  induction s;split; intro; intro; assumption.
Qed.

Lemma set_eq_comm {A} : forall s1 s2 : set A,
  set_eq s1 s2 <-> set_eq s2 s1.
Proof.
  intros; split; intro; destruct H; split; assumption.
Qed.

Lemma set_eq_tran {A} : forall s1 s2 s3 : set A,
  set_eq s1 s2 ->
  set_eq s2 s3 ->
  set_eq s1 s3.
Proof.
  intros. split; apply incl_tran with s2; apply H || apply H0.
Qed.

Lemma set_eq_cons {A} : forall (a : A) (s1 s2 : set A),
  set_eq s1 s2 ->
  set_eq (a :: s1) (a :: s2).
Proof.
  intros. split; intros x Hin; destruct Hin; subst
  ; (left; reflexivity) || (right; apply H; assumption).
Qed.


Fixpoint set_eq_fn_rec {A} (Aeq_dec : forall x y:A, {x = y} + {x <> y}) (s1 s2 : list A) : bool :=
  match s1 with
  | [] =>
    match s2 with
    | [] => true
    | _ => false
    end
  | h :: t => if in_dec Aeq_dec h s2 then set_eq_fn_rec Aeq_dec t (set_remove Aeq_dec h s2) else false
  end.

Definition set_eq_fn {A} (Aeq_dec : forall x y:A, {x = y} + {x <> y}) (s1 s2 : list A) : bool :=
  set_eq_fn_rec Aeq_dec (nodup Aeq_dec s1) (nodup Aeq_dec s2).

Lemma set_eq_fn_rec_iff {A} (Aeq_dec : forall x y:A, {x = y} + {x <> y}) : forall s1 s2,
  NoDup s1 ->
  NoDup s2 ->
  set_eq s1 s2 <-> set_eq_fn_rec Aeq_dec s1 s2 = true.
Proof.
  intros; split; intros.
  - generalize dependent s2. induction s1; intros; destruct s2; destruct H1.
    + reflexivity.
    + apply incl_empty in  H2. inversion H2.
    + apply incl_empty in  H1. inversion H1.
    + apply NoDup_cons_iff in H. destruct H.
      apply NoDup_cons_iff in H0. destruct H0.
      simpl. destruct (Aeq_dec a0 a); subst.
      * rewrite eq_dec_if_true; try reflexivity.
        apply IHs1; try assumption.
        { split; intros x Hin.
          - destruct (H1 x); try (right; assumption); try assumption; subst.
            exfalso. apply H; assumption.
          - destruct (H2 x); try (right; assumption); try assumption; subst.
            exfalso. apply H0; assumption.
        }
      * { destruct (in_dec Aeq_dec a s2).
          - rewrite eq_dec_if_false.
            + apply IHs1; try assumption.
              * apply NoDup_cons_iff.
                { split.
                  - intro. apply set_remove_iff in H5; try assumption.
                    apply H0. destruct H5; assumption.
                  - apply set_remove_nodup. assumption.
                }
              * { split; intros x Hin.
                  - destruct (Aeq_dec x a0); subst; try (left; reflexivity).
                    right. apply set_remove_iff; try assumption.
                    split.
                    + destruct (H1 x); try assumption; try (right; assumption); subst.
                      exfalso. apply n0; reflexivity.
                    + intro; subst. apply H; assumption.
                  - destruct Hin; subst.
                    + destruct (H2 x); try assumption; try (left; reflexivity); subst.
                      exfalso; apply n; reflexivity.
                    + apply set_remove_iff in H5; try assumption. destruct H5.
                      destruct (H2 x); try assumption; try (right; assumption); subst.
                      exfalso; apply H6; reflexivity.
                }
            + intro; subst; apply n; reflexivity.
          - exfalso. apply n0. destruct (H1 a); try assumption; try (left; reflexivity); subst.
            exfalso; apply n; reflexivity.
        }
  - generalize dependent s2. induction s1; intros; simpl in H1; destruct s2; try discriminate.
    + split; apply incl_refl.
    + destruct (in_dec Aeq_dec a (a0 :: s2)); try discriminate.
      apply IHs1 in H1; destruct H1
      ; try (split; intros x Hin; destruct Hin as [Heq | Hin]; subst; try assumption).
      * apply H1 in Hin. apply set_remove_iff in Hin; try assumption. destruct Hin; assumption.
      * destruct (Aeq_dec x a); subst; try (left; reflexivity).
        right. apply H2. apply set_remove_iff; try assumption. split; try assumption.
        left; reflexivity.
      * destruct (Aeq_dec x a); subst; try (left; reflexivity).
        right. apply H2. apply set_remove_iff; try assumption. split; try assumption.
        right; assumption.
      * apply NoDup_cons_iff in H. destruct H; assumption.
      * apply set_remove_nodup. assumption.
Qed.

Lemma set_eq_functional {A} (Aeq_dec : forall x y:A, {x = y} + {x <> y}) :
  PredicateFunction2 set_eq (set_eq_fn Aeq_dec).
Proof.
  intros s1 s2. split; intros.
  - unfold set_eq_fn. apply set_eq_fn_rec_iff; try apply NoDup_nodup.
    destruct H as [H12 H21]. split; intros x Hin; apply nodup_In; apply nodup_In in Hin
    ; apply H12 || apply H21
    ; assumption.
  - apply set_eq_fn_rec_iff in H; try apply NoDup_nodup.
    destruct H as [H12 H21].
    split; intros x Hin; rewrite <- (nodup_In Aeq_dec); rewrite <- (nodup_In Aeq_dec) in Hin
    ; apply H12 || apply H21
    ; assumption.
Qed.

Lemma set_eq_dec {A} (Aeq_dec : forall x y:A, {x = y} + {x <> y}) : forall (s1 s2 : set A),
  {set_eq s1 s2} + {~ set_eq s1 s2}.
Proof.
  intros.
  destruct (set_eq_fn Aeq_dec s1 s2) eqn:Heq.
  - left. apply (set_eq_functional Aeq_dec). assumption.
  - right. intro. apply (set_eq_functional Aeq_dec) in H. rewrite Heq in H. discriminate H.
Qed.

Lemma set_eq_singleton_iff {A} (Aeq_dec : forall x y:A, {x = y} + {x <> y}) :
  forall (s1 : list A) (a : A),
  NoDup s1 ->
  set_eq s1 [a] <-> s1 = [a].
Proof.
  intros; split; intros.
  { destruct H0 as [Hincl1a Hincla1]. destruct s1.
    - exfalso. destruct (Hincla1 a). left. reflexivity.
    - destruct (incl_singleton _ a Hincl1a a0); try (left; reflexivity) .
      destruct s1; try reflexivity.
      destruct (incl_singleton _ a0 Hincl1a a); try (right; left; reflexivity) .
      exfalso. inversion H; subst; clear H. apply H2. left. reflexivity.
  }
  subst. apply set_eq_refl.
Qed.

Lemma set_eq_singleton {A} (Aeq_dec : forall x y:A, {x = y} + {x <> y}) :
  forall (s1 : list A) (a : A),
  NoDup s1 ->
  set_eq s1 [a] -> s1 = [a].
Proof.
  intros. apply set_eq_singleton_iff; assumption.
Qed.

Lemma set_eq_singleton_rev {A} (Aeq_dec : forall x y:A, {x = y} + {x <> y}) :
  forall (s1 : list A) (a : A),
  NoDup s1 ->
  s1 = [a] -> set_eq s1 [a].
Proof.
  intros. apply set_eq_singleton_iff; assumption.
Qed.

Lemma set_union_comm {A} (Aeq_dec : forall x y:A, {x = y} + {x <> y})  : forall s1 s2,
  set_eq (set_union Aeq_dec s1 s2) (set_union Aeq_dec s2 s1).
Proof.
  intros; split; intro x; intros; apply set_union_iff in H; apply set_union_iff; destruct H;
  (left ; assumption) || (right; assumption).
Qed.

Lemma set_union_empty {A} (Aeq_dec : forall x y:A, {x = y} + {x <> y})  : forall s1 s2,
  set_union Aeq_dec s1 s2 = nil ->
  s1 = nil /\ s2 = nil
  .
Proof.
  intros.
  destruct s2.
  - destruct (set_union_comm Aeq_dec s1 nil). rewrite H in H1. destruct s1.
    + split; reflexivity.
    + simpl in H1. destruct (H1 a). apply set_add_intro. left. reflexivity.
  - simpl in H. assert (@incl A nil nil); try apply incl_refl.
    rewrite <- H in H0 at 1. destruct (H0 a). apply set_add_intro. left. reflexivity.
Qed.

Lemma set_union_incl_left {A} (Aeq_dec : forall x y:A, {x = y} + {x <> y})  : forall s1 s2,
  incl s1 (set_union Aeq_dec s1 s2).
Proof.
  intros; intros x H; apply set_union_intro.
  left; assumption.
Qed.

Lemma set_union_incl_right {A} (Aeq_dec : forall x y:A, {x = y} + {x <> y})  : forall s1 s2,
  incl s2 (set_union Aeq_dec s1 s2).
Proof.
  intros; intros x H; apply set_union_intro.
  right; assumption.
Qed.

Lemma set_union_incl_iterated {A} (Aeq_dec : forall x y:A, {x = y} + {x <> y})  : forall ss s,
  In s ss ->
  incl s (fold_right (set_union Aeq_dec) nil ss).
Proof.
  induction ss; intros.
  - inversion H.
  - simpl. destruct H.
    + subst. apply set_union_incl_left.
    + apply IHss in H. apply incl_tran with (fold_right (set_union Aeq_dec) [] ss); try assumption.
      apply set_union_incl_right.
Qed.

Lemma set_union_empty_left {A} (Aeq_dec : forall x y:A, {x = y} + {x <> y})  : forall s,
  NoDup s ->
  set_eq (set_union Aeq_dec nil s) s.
Proof.
  intros. split; intros x Hin.
  - apply set_union_elim in Hin. destruct Hin.
    + inversion H0.
    + assumption.
  - apply set_union_intro. right. assumption.
Qed.

Lemma map_set_eq {A B} (f : B -> A) : forall s s',
  set_eq s s' ->
  set_eq (map f s) (map f s').
Proof.
  split; apply map_incl; apply H.
Qed.

Lemma set_map_nodup {A B} (Aeq_dec : forall x y:A, {x = y} + {x <> y}) (f : B -> A) : forall s,
  NoDup (set_map Aeq_dec f s).
Proof.
  induction s; simpl; try constructor.
  apply set_add_nodup. assumption.
Qed.

Lemma set_map_in {A B} (Aeq_dec : forall x y:A, {x = y} + {x <> y}) (f : B -> A) : forall x s,
  In x s ->
  In (f x) (set_map Aeq_dec f s).
Proof.
  induction s; intros; inversion H; subst; clear H; simpl.
  - apply set_add_intro2. reflexivity.
  - apply set_add_intro1. apply IHs. assumption.
Qed.

Lemma set_map_exists  {A B} (Aeq_dec : forall x y:A, {x = y} + {x <> y}) (f : B -> A) : forall y s,
  In y (set_map Aeq_dec f s) <->
  exists x, In x s /\ f x = y.
Proof.
  intros.
  induction s; split; intros; simpl in H.
  - inversion H.
  - destruct H as [_ [F _]]. inversion F.
  - apply set_add_iff in H. destruct H as [Heq | Hin]; subst.
    + exists a. split; try reflexivity. left; reflexivity.
    + apply IHs in Hin. destruct Hin as [x [Hin Heq]]; subst.
      exists x. split; try reflexivity. right; assumption.
  - destruct H as [x [[Heq | Hin] Heqf]]; subst; simpl; apply set_add_iff
    ; try (left; reflexivity) .
    right. apply IHs. exists x. split.
    + assumption.
    + reflexivity.
Qed.

Lemma set_map_incl {A B} (Aeq_dec : forall x y:A, {x = y} + {x <> y}) (f : B -> A) : forall s s',
  incl s s' ->
  incl (set_map Aeq_dec f s) (set_map Aeq_dec f s').
Proof.
  induction s; intros; intro msg; intros.
  - inversion H0.
  - simpl in H0. apply set_add_elim in H0. destruct H0.
    + subst. apply set_map_in. apply H. left. reflexivity.
    + apply IHs; try assumption. intros x; intros. apply H. right. assumption.
Qed.

Lemma set_map_eq {A B} (Aeq_dec : forall x y:A, {x = y} + {x <> y}) (f : B -> A) : forall s s',
  set_eq s s' ->
  set_eq (set_map Aeq_dec f s) (set_map Aeq_dec f s').
Proof.
  intros. split; destruct H; apply set_map_incl; assumption.
Qed.

Lemma set_map_singleton {A B} (Aeq_dec : forall x y:A, {x = y} + {x <> y}) (f : B -> A) : forall s a,
  set_map Aeq_dec f s = [a] ->
  forall b, In b s -> f b = a.
Proof.
  intros. apply (set_map_in Aeq_dec f) in H0. rewrite H in H0. inversion H0.
  - subst. reflexivity.
  - exfalso. inversion H1.
Qed.

Lemma set_map_injective {A B} (Aeq_dec : forall x y:A, {x = y} + {x <> y}) (f : B -> A) :
  Injective f ->
  forall s s',
    set_eq (set_map Aeq_dec f s) (set_map Aeq_dec f s') -> set_eq s s'.
Proof.
  intros. split; intros x Hin;
    apply (set_map_in Aeq_dec f) in Hin; apply H0 in Hin; apply set_map_exists in Hin
    ; destruct Hin as [x' [Hin Heq]]; apply H in Heq; subst; assumption.
Qed.

Lemma filter_set_add {X} `{StrictlyComparable X} :
  forall (l : list X) (f : X -> bool) (x : X),
    f x = false ->
    filter f l = filter f (set_add compare_eq_dec x l).
Proof.
  induction l as [|hd tl IHl]; intros f x H_false.
  - simpl. rewrite H_false. reflexivity.
  - simpl. spec IHl f x H_false.
    destruct (compare_eq_dec x hd).
    + subst. rewrite H_false.
      simpl. rewrite H_false. reflexivity.
    + case_eq (f hd); intro H_eq;
      simpl; rewrite H_eq; rewrite <- IHl; reflexivity.
Qed.


Lemma set_add_ignore {X} `{StrictlyComparable X} :
  forall (l : list X) (x : X),
    In x l ->
    set_add compare_eq_dec x l = l.
Proof.
  induction l as [|hd tl IHl]; intros x H_in.
  - inversion H_in.
  - inversion H_in.
    + subst. simpl.
      destruct (compare_eq_dec x x).
      reflexivity.
      contradiction.
    + spec IHl x H0. simpl.
      destruct (compare_eq_dec x hd).
      reflexivity.
      rewrite IHl. reflexivity.
Qed.


Lemma set_remove_not_in {A} (Aeq_dec : forall x y:A, {x = y} + {x <> y}) : forall x s,
  ~ In x s ->
  set_remove Aeq_dec x s = s.
Proof.
  induction s; intros.
  - reflexivity.
  - simpl. apply not_in_cons in H.  destruct H.
    destruct (eq_dec_right Aeq_dec x a H). rewrite H1.
    rewrite (IHs H0). reflexivity.
Qed.

Lemma set_remove_elim {A} (Aeq_dec : forall x y:A, {x = y} + {x <> y}) : forall x s,
  NoDup s -> ~ In x (set_remove Aeq_dec x s).
Proof.
  intros. intro. apply set_remove_iff in H0; try assumption.
  destruct H0. apply H1. reflexivity.
Qed.


Lemma set_remove_first {A} (Aeq_dec : forall x y:A, {x = y} + {x <> y}) : forall x y s,
  x = y -> set_remove Aeq_dec x (y::s) = s.
Proof.
  intros. destruct (Aeq_dec x y) eqn:Hcmp; simpl; rewrite Hcmp; try reflexivity.
  exfalso. apply n. assumption.
Qed.

Lemma set_remove_nodup_1 {A} (Aeq_dec : forall x y:A, {x = y} + {x <> y}) : forall x s,
  NoDup (set_remove Aeq_dec x s) ->
  ~ In x (set_remove Aeq_dec x s) ->
  NoDup s.
Proof.
  induction s; intros.
  - constructor.
  - simpl in H0 . destruct (Aeq_dec x a).
    + subst. simpl in H. destruct (eq_dec_left Aeq_dec a). rewrite H1 in H. constructor; assumption.
    + apply not_in_cons in H0. destruct H0. simpl in H.
      destruct (eq_dec_right Aeq_dec x a H0).
    rewrite H2 in H. inversion H; subst; clear H.
    constructor; try apply IHs; try assumption.
    intro. apply H5. apply set_remove_3; try assumption. intro; subst. apply H0; reflexivity.
Qed.


Lemma set_remove_in_iff {A} (Aeq_dec : forall x y:A, {x = y} + {x <> y})
  :  forall x y s
  ,  NoDup s
  ->  In y s
  -> In x s <-> x = y \/ In x (set_remove Aeq_dec y s).
Proof.
  intros. split; intros.
  - destruct (Aeq_dec x y).
    + left. assumption.
    + right. apply set_remove_3; assumption.
  - destruct H1 as [Heq | Hin].
    + subst; assumption.
    + apply set_remove_1 in Hin. assumption.
Qed.

Lemma set_eq_remove {A} (Aeq_dec : forall x y:A, {x = y} + {x <> y}) : forall x s1 s2,
  NoDup s1 ->
  NoDup s2 ->
  set_eq s1 s2 ->
  set_eq (set_remove Aeq_dec x s1) (set_remove Aeq_dec x s2).
Proof.
  intros.
  destruct H1. split; intros a Hin
  ; apply set_remove_iff; try assumption
  ; apply set_remove_iff in Hin; try assumption; destruct Hin
  ; split; try assumption
  .
  - apply H1. assumption.
  - apply H2. assumption.
Qed.

Lemma incl_remove_union  {A} (Aeq_dec : forall x y:A, {x = y} + {x <> y}) : forall x s1 s2,
  NoDup s1 ->
  NoDup s2 ->
  incl
    (set_remove Aeq_dec x (set_union Aeq_dec s1 s2))
    (set_union Aeq_dec s1 (set_remove Aeq_dec x s2))
  .
Proof.
  intros. intros y Hin. apply set_remove_iff in Hin.
  - apply set_union_intro. destruct Hin. apply set_union_elim in H1.
    destruct H1; try (left; assumption).
    right. apply set_remove_3; assumption.
  - apply set_union_nodup; assumption.
Qed.

Lemma set_eq_remove_union_in  {A} (Aeq_dec : forall x y:A, {x = y} + {x <> y}) : forall x s1 s2,
  NoDup s1 ->
  NoDup s2 ->
  In x s1 ->
  set_eq
    (set_union Aeq_dec s1 (set_remove Aeq_dec x s2))
    (set_union Aeq_dec s1 s2)
  .
Proof.
  split; intros msg Hin; apply set_union_iff; apply set_union_iff in Hin
  ; destruct Hin; try (left; assumption)
  .
  - apply set_remove_iff in H2; try assumption. destruct H2. right. assumption.
  - destruct (Aeq_dec msg x).
    + subst. left. assumption.
    + right. apply set_remove_iff; try assumption. split; assumption.
Qed.

Lemma set_eq_remove_union_not_in  {A} (Aeq_dec : forall x y:A, {x = y} + {x <> y}) : forall x s1 s2,
  NoDup s1 ->
  NoDup s2 ->
  ~ In x s1 ->
  set_eq
    (set_union Aeq_dec s1 (set_remove Aeq_dec x s2))
    (set_remove Aeq_dec x (set_union Aeq_dec s1 s2))
  .
Proof.
  intros.
  assert (HnodupUs1s2 := H0).
  apply (set_union_nodup Aeq_dec H) in HnodupUs1s2.
  split; intros msg Hin.
  - apply set_remove_iff; try assumption.
    apply set_union_iff in Hin.
    destruct Hin; split.
    + apply set_union_iff. left. assumption.
    + intro; subst. apply H1. assumption.
    + apply set_remove_iff in H2; try assumption.
      destruct H2. apply set_union_iff. right. assumption.
    + intro; subst.
      apply set_remove_iff in H2; try assumption.
      destruct H2. apply H3. reflexivity.
  - apply set_union_iff; try assumption.
    apply set_remove_iff in Hin; try assumption.
    destruct Hin. apply set_union_iff in H2.
    destruct H2; try (left; assumption).
    right. apply set_remove_iff; try assumption.
    split; assumption.
Qed.


Lemma diff_app_nodup {A} (Aeq_dec : forall x y:A, {x = y} + {x <> y}) : forall s1 s2,
  NoDup s1 ->
  NoDup s2 ->
  NoDup ((set_diff Aeq_dec s1 s2) ++ s2).
Proof.
  intros.
  apply nodup_append; try assumption.
  - apply set_diff_nodup; try assumption.
  - intros. apply (set_diff_elim2 Aeq_dec a s1); assumption.
  - intros. intro. apply set_diff_iff in H2. destruct H2.
    apply H3. assumption.
Qed.

Lemma add_remove_inverse {X} `{StrictlyComparable X}:
  forall (lv : list X) (v : X),
    ~ In v lv ->
    set_remove compare_eq_dec v (set_add compare_eq_dec v lv) = lv.
Proof.
  induction lv as [|hd tl IHlv]; intros.
  - compute.
    destruct (compare_eq_dec v v).
    reflexivity. contradiction.
  - destruct (compare_eq_dec v hd).
    subst. exfalso; apply H0.
    apply in_eq.
    spec IHlv v. spec IHlv.
    intro Habsurd. apply H0.
    right; assumption.
    rewrite <- IHlv at 2.
    simpl.
    destruct (compare_eq_dec v hd).
    contradiction.
    simpl. destruct (compare_eq_dec v hd).
    contradiction. reflexivity.
Qed.

Unset Implicit Arguments.
