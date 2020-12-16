Require Import Coq.Lists.ListSet.
Require Import List.
Import ListNotations.

Require Import CasperCBC.Lib.Preamble.
Require Import CasperCBC.Lib.ListExtras.

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

Lemma set_eq_Forall
  {A : Type}
  (s1 s2 : set A)
  (H12 : set_eq s1 s2)
  (P : A -> Prop)
  : Forall P s1 <-> Forall P s2.
Proof.
  split; intros H; rewrite Forall_forall in *; intros x Hx
  ; apply H; apply H12; assumption
  .
Qed.


Fixpoint set_eq_fn_rec `{EqDecision A} (s1 s2 : list A) : bool :=
  match s1 with
  | [] =>
    match s2 with
    | [] => true
    | _ => false
    end
  | h :: t => if in_dec decide_eq h s2 then set_eq_fn_rec t (set_remove decide_eq h s2) else false
  end.

Definition set_eq_fn `{EqDecision A} (s1 s2 : list A) : bool :=
  set_eq_fn_rec (nodup decide_eq s1) (nodup decide_eq s2).

Lemma set_eq_fn_rec_iff `{EqDecision A} : forall (s1 s2 : list A),
  NoDup s1 ->
  NoDup s2 ->
  set_eq s1 s2 <-> set_eq_fn_rec s1 s2 = true.
Proof.
  intros; split; intros.
  - generalize dependent s2. induction s1; intros; destruct s2; destruct H1.
    + reflexivity.
    + apply incl_empty in  H2. inversion H2.
    + apply incl_empty in  H1. inversion H1.
    + apply NoDup_cons_iff in H. destruct H.
      apply NoDup_cons_iff in H0. destruct H0.
      simpl. destruct (decide (a0 = a)); subst.
      * rewrite decide_True; try reflexivity.
        apply IHs1; try assumption.
        { split; intros x Hin.
          - destruct (H1 x); try (right; assumption); try assumption; subst.
            exfalso. apply H; assumption.
          - destruct (H2 x); try (right; assumption); try assumption; subst.
            exfalso. apply H0; assumption.
        }
      * { destruct (in_dec decide_eq a s2).
          - rewrite decide_False.
            + apply IHs1; try assumption.
              * apply NoDup_cons_iff.
                { split.
                  - intro. apply set_remove_iff in H5; try assumption.
                    apply H0. destruct H5; assumption.
                  - apply set_remove_nodup. assumption.
                }
              * { split; intros x Hin.
                  - destruct (decide (x = a0)); subst; try (left; reflexivity).
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
    + destruct (in_dec decide_eq a (a0 :: s2)); try discriminate.
      apply IHs1 in H1; destruct H1
      ; try (split; intros x Hin; destruct Hin as [Heq | Hin]; subst; try assumption).
      * apply H1 in Hin. apply set_remove_iff in Hin; try assumption. destruct Hin; assumption.
      * destruct (decide (x = a)); subst; try (left; reflexivity).
        right. apply H2. apply set_remove_iff; try assumption. split; try assumption.
        left; reflexivity.
      * destruct (decide (x = a)); subst; try (left; reflexivity).
        right. apply H2. apply set_remove_iff; try assumption. split; try assumption.
        right; assumption.
      * apply NoDup_cons_iff in H. destruct H; assumption.
      * apply set_remove_nodup. assumption.
Qed.

Lemma set_eq_functional `{EqDecision A} :
  @PredicateFunction2 _ (set A) set_eq set_eq_fn.
Proof.
  intros s1 s2. split; intros.
  - unfold set_eq_fn. apply set_eq_fn_rec_iff; try apply NoDup_nodup.
    destruct H as [H12 H21]. split; intros x Hin; apply nodup_In; apply nodup_In in Hin
    ; apply H12 || apply H21
    ; assumption.
  - apply set_eq_fn_rec_iff in H; try apply NoDup_nodup.
    destruct H as [H12 H21].
    split; intros x Hin; rewrite <- (nodup_In decide_eq); rewrite <- (nodup_In decide_eq) in Hin
    ; apply H12 || apply H21
    ; assumption.
Qed.

Instance set_eq_dec `{EqDecision A} : @RelDecision (set A) (set A) set_eq.
Proof.
intros s1 s2.
destruct (set_eq_fn s1 s2) eqn:Heq.
- left. apply set_eq_functional. assumption.
- right. intro. apply set_eq_functional in H. rewrite Heq in H. discriminate H.
Defined.

Lemma set_eq_singleton_iff `{EqDecision A} :
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

Lemma set_eq_singleton `{EqDecision A} :
  forall (s1 : list A) (a : A),
  NoDup s1 ->
  set_eq s1 [a] -> s1 = [a].
Proof.
  intros. apply set_eq_singleton_iff; assumption.
Qed.

Lemma set_eq_singleton_rev `{EqDecision A} :
  forall (s1 : list A) (a : A),
  NoDup s1 ->
  s1 = [a] -> set_eq s1 [a].
Proof.
  intros. apply set_eq_singleton_iff; assumption.
Qed.

Lemma set_union_comm `{EqDecision A}  : forall (s1 s2 : list A),
  set_eq (set_union decide_eq s1 s2) (set_union decide_eq s2 s1).
Proof.
  intros; split; intro x; intros; apply set_union_iff in H; apply set_union_iff; destruct H;
  (left ; assumption) || (right; assumption).
Qed.

Lemma set_union_empty `{EqDecision A}  : forall (s1 s2 : list A),
  set_union decide_eq s1 s2 = nil ->
  s1 = nil /\ s2 = nil.
Proof.
  intros.
  destruct s2.
  - destruct (set_union_comm s1 nil). rewrite H in H1. destruct s1.
    + split; reflexivity.
    + simpl in H1. destruct (H1 a). apply set_add_intro. left. reflexivity.
  - simpl in H. assert (@incl A nil nil); try apply incl_refl.
    rewrite <- H in H0 at 1. destruct (H0 a). apply set_add_intro. left. reflexivity.
Qed.

Lemma set_union_incl_left `{EqDecision A}  : forall (s1 s2 : list A),
  incl s1 (set_union decide_eq s1 s2).
Proof.
  intros; intros x H; apply set_union_intro.
  left; assumption.
Qed.

Lemma set_union_incl_right `{EqDecision A}  : forall (s1 s2 : list A),
  incl s2 (set_union decide_eq s1 s2).
Proof.
  intros; intros x H; apply set_union_intro.
  right; assumption.
Qed.

Lemma set_union_incl_iterated `{EqDecision A}  : forall ss (s : list A),
  In s ss ->
  incl s (fold_right (set_union decide_eq) nil ss).
Proof.
  induction ss; intros.
  - inversion H.
  - simpl. destruct H.
    + subst. apply set_union_incl_left.
    + apply IHss in H. apply incl_tran with (fold_right (set_union decide_eq) [] ss); try assumption.
      apply set_union_incl_right.
Qed.

Lemma set_union_iterated_nodup `{EqDecision A}
  (ss : list (list A))
  (H : forall s, In s ss -> NoDup s) :
  NoDup (fold_right (set_union decide_eq) nil ss).
Proof.
  intros.
  generalize dependent ss.
  induction ss.
  - intros. simpl. apply NoDup_nil.
  - intros.
    simpl.
    apply set_union_nodup.
    specialize (H a).
    apply H.
    intuition.
    apply IHss.
    intros.
    specialize (H s).
    spec H.
    simpl.
    right.
    assumption.
    assumption.
Qed.

Lemma set_union_in_iterated
  `{EqDecision A}
  (ss : list (set A))
  (a : A)
  : In a (fold_right (set_union decide_eq) nil ss)
  <-> Exists (fun s => In a s) ss.
Proof.
  rewrite Exists_exists.
  induction ss; split; simpl.
  - intro H; inversion H.
  - intros [x [Hin _]]; inversion Hin.
  - intro Hin. apply set_union_iff in Hin.
    destruct Hin as [Hina0 | Hinss].
    + exists a0. split; try assumption. left. reflexivity.
    + apply IHss in Hinss. destruct Hinss as [x [Hinss Hinx]].
      exists x. split; try assumption.
      right. assumption.
  - rewrite set_union_iff.
    intros [x [[Heqa0 | Hinss] Hinx]]; subst.
    + left. assumption.
    + right. apply IHss.
      exists x. split; assumption.
Qed.

Lemma set_union_iterated_incl
  `{EqDecision A}
  (ss ss': list (set A))
  (Hincl : incl ss ss')
  :
  incl 
  (fold_right (set_union decide_eq) nil ss)
  (fold_right (set_union decide_eq) nil ss').
Proof.
  unfold incl.
  intros.
  apply set_union_in_iterated in H.
  apply set_union_in_iterated.
  rewrite Exists_exists in *.
  destruct H as [x Heqx].
  exists x.
  unfold incl in Hincl.
  intuition.
Qed.

Lemma set_union_empty_left `{EqDecision A}  : forall (s : list A),
  NoDup s ->
  set_eq (set_union decide_eq nil s) s.
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

Lemma set_map_nodup {A B} `{EqDecision A} (f : B -> A) : forall (s : set B),
  NoDup (set_map decide_eq f s).
Proof.
  induction s; simpl; try constructor.
  apply set_add_nodup. assumption.
Qed.

Lemma set_map_in {A B} `{EqDecision A} (f : B -> A) : forall x s,
  In x s ->
  In (f x) (set_map decide_eq f s).
Proof.
  induction s; intros; inversion H; subst; clear H; simpl.
  - apply set_add_intro2. reflexivity.
  - apply set_add_intro1. apply IHs. assumption.
Qed.

Lemma set_map_exists {A B} `{EqDecision A} (f : B -> A) : forall y s,
  In y (set_map decide_eq f s) <->
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

Lemma set_map_incl {A B} `{EqDecision A} (f : B -> A) : forall s s',
  incl s s' ->
  incl (set_map decide_eq f s) (set_map decide_eq f s').
Proof.
  induction s; intros; intro msg; intros.
  - inversion H0.
  - simpl in H0. apply set_add_elim in H0. destruct H0.
    + subst. apply set_map_in. apply H. left. reflexivity.
    + apply IHs; try assumption. intros x; intros. apply H. right. assumption.
Qed.

Lemma set_map_eq {A B} `{EqDecision A} (f : B -> A) : forall s s',
  set_eq s s' ->
  set_eq (set_map decide_eq f s) (set_map decide_eq f s').
Proof.
  intros. split; destruct H; apply set_map_incl; assumption.
Qed.

Lemma set_map_singleton {A B} `{EqDecision A} (f : B -> A) : forall s a,
  set_map decide_eq f s = [a] ->
  forall b, In b s -> f b = a.
Proof.
  intros. apply (set_map_in f) in H0. rewrite H in H0. inversion H0.
  - subst. reflexivity.
  - exfalso. inversion H1.
Qed.

Lemma filter_set_add `{StrictlyComparable X} :
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

Lemma set_add_ignore `{StrictlyComparable X} :
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

Lemma set_remove_not_in `{EqDecision A} : forall x (s : list A),
  ~ In x s ->
  set_remove decide_eq x s = s.
Proof.
  induction s; intros.
  - reflexivity.
  - simpl. apply not_in_cons in H.  destruct H.
    destruct (decide (x = a)); [congruence|].
    rewrite (IHs H0). reflexivity.
Qed.

Lemma set_remove_elim `{EqDecision A} : forall x (s : list A),
  NoDup s -> ~ In x (set_remove decide_eq x s).
Proof.
  intros. intro. apply set_remove_iff in H0; try assumption.
  destruct H0. apply H1. reflexivity.
Qed.

Lemma set_remove_first `{EqDecision A} : forall x y (s : list A),
  x = y -> set_remove decide_eq x (y::s) = s.
Proof.
  intros. destruct (decide (x = y)) eqn:Hcmp; simpl; rewrite Hcmp; try reflexivity.
  exfalso. apply n. assumption.
Qed.

Lemma set_remove_nodup_1 `{EqDecision A} : forall x (s : list A),
  NoDup (set_remove decide_eq x s) ->
  ~ In x (set_remove decide_eq x s) ->
  NoDup s.
Proof.
  induction s; intros.
  - constructor.
  - simpl in H0 . destruct (decide (x = a)).
    + subst. simpl in H. rewrite decide_True in H; auto. constructor; assumption.
    + apply not_in_cons in H0. destruct H0. simpl in H.
      rewrite decide_False in H; auto.
      inversion H; subst.
      specialize (IHs H5 H1).
      constructor; auto.
      intro; contradict H4.
      apply set_remove_3; congruence.
Qed.

Lemma set_remove_in_iff `{EqDecision A} :  forall x y (s : list A),
  NoDup s ->
  In y s ->
  In x s <-> x = y \/ In x (set_remove decide_eq y s).
Proof.
  intros. split; intros.
  - destruct (decide (x = y)).
    + left. assumption.
    + right. apply set_remove_3; assumption.
  - destruct H1 as [Heq | Hin].
    + subst; assumption.
    + apply set_remove_1 in Hin. assumption.
Qed.

Lemma set_remove_length
  `{EqDecision A}
  (x : A)
  (s : set A)
  (Hx : In x s)
  : length s = S (length (set_remove decide_eq x s)).
Proof.
  generalize dependent x. induction s; intros; inversion Hx; subst.
  - rewrite set_remove_first;  reflexivity.
  - simpl. f_equal.
    destruct (decide (x = a)); try reflexivity.
    apply IHs. assumption.
Qed.

Lemma set_eq_remove `{EqDecision A} : forall x (s1 s2 : list A),
  NoDup s1 ->
  NoDup s2 ->
  set_eq s1 s2 ->
  set_eq (set_remove decide_eq x s1) (set_remove decide_eq x s2).
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

Lemma incl_remove_union  `{EqDecision A} : forall x (s1 s2 : list A),
  NoDup s1 ->
  NoDup s2 ->
  incl
    (set_remove decide_eq x (set_union decide_eq s1 s2))
    (set_union decide_eq s1 (set_remove decide_eq x s2)).
Proof.
  intros. intros y Hin. apply set_remove_iff in Hin.
  - apply set_union_intro. destruct Hin. apply set_union_elim in H1.
    destruct H1; try (left; assumption).
    right. apply set_remove_3; assumption.
  - apply set_union_nodup; assumption.
Qed.

Lemma set_eq_remove_union_in  `{EqDecision A} : forall x (s1 s2 : list A),
  NoDup s1 ->
  NoDup s2 ->
  In x s1 ->
  set_eq
    (set_union decide_eq s1 (set_remove decide_eq x s2))
    (set_union decide_eq s1 s2).
Proof.
  split; intros msg Hin; apply set_union_iff; apply set_union_iff in Hin
  ; destruct Hin; try (left; assumption)
  .
  - apply set_remove_iff in H2; try assumption. destruct H2. right. assumption.
  - destruct (decide (msg = x)).
    + subst. left. assumption.
    + right. apply set_remove_iff; try assumption. split; assumption.
Qed.

Lemma set_eq_remove_union_not_in  `{EqDecision A} : forall x (s1 s2 : list A),
  NoDup s1 ->
  NoDup s2 ->
  ~ In x s1 ->
  set_eq
    (set_union decide_eq s1 (set_remove decide_eq x s2))
    (set_remove decide_eq x (set_union decide_eq s1 s2)).
Proof.
  intros.
  assert (HnodupUs1s2 := H0).
  apply (set_union_nodup decide_eq H) in HnodupUs1s2.
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

Lemma diff_app_nodup `{EqDecision A} : forall (s1 s2 : list A),
  NoDup s1 ->
  NoDup s2 ->
  NoDup ((set_diff decide_eq s1 s2) ++ s2).
Proof.
  intros.
  apply nodup_append; try assumption.
  - apply set_diff_nodup; try assumption.
  - intros. apply (set_diff_elim2 decide_eq a s1); assumption.
  - intros. intro. apply set_diff_iff in H2. destruct H2.
    apply H3. assumption.
Qed.

Lemma add_remove_inverse `{EqDecision X}:
  forall (lv : list X) (v : X),
    ~ In v lv ->
    set_remove decide_eq v (set_add decide_eq v lv) = lv.
Proof.
  induction lv as [|hd tl IHlv]; intros.
  - simpl.
    rewrite decide_True; congruence.
  - simpl. destruct (decide (v = hd)).
    subst. exfalso; apply H.
    apply in_eq.
    spec IHlv v. spec IHlv.
    intro Habsurd. apply H.
    right; assumption.
    rewrite <- IHlv at 2.
    simpl.
    destruct (decide (v = hd)).
    contradiction.
    reflexivity.
Qed.

Lemma set_union_iterated_empty `{EqDecision A} :
   forall ss,
   (forall (s : list A),
   In s ss -> s = []) -> (fold_right (set_union decide_eq) nil ss) = [].
Proof.
   intros.
   induction ss.
   - simpl.
     reflexivity.
   - simpl.
     assert (fold_right (set_union decide_eq) [] ss = []). {
        apply IHss.
        simpl in H.
        intros.
        specialize (H s).
        apply H.
        right.
        assumption.
     }
     rewrite H0.
     assert (a = []). {
      specialize (H a).
      apply H.
      intuition.
     }
  rewrite H1.
  simpl.
  reflexivity.
Qed.

Definition set_remove_list `{EqDecision A} (l1 l2 : list A) : list A :=
  fold_right (set_remove decide_eq) l2 l1.

Lemma set_remove_list_1 
  `{EqDecision A} 
  (a : A)
  (l1 l2 : list A)
  (Hin : In a (set_remove_list l1 l2)) :
  In a l2.
Proof.
  unfold set_remove_list in Hin.
  induction l1.
  - simpl in Hin; intuition.
  - simpl in Hin.
    apply set_remove_1 in Hin.
    apply IHl1 in Hin.
    assumption.
Qed. 


Definition get_maximal_elements {A}
  (preceeds : A -> A -> Prop)
  (preceeds_dec : RelDecision preceeds)
  (l : list A)
  : list A :=
  filter (fun a => forallb (fun b => negb (bool_decide (preceeds b a))) l) l.

Lemma set_prod_nodup `(s1: set A) `(s2: set B):
  NoDup s1 ->
  NoDup s2 ->
  NoDup (set_prod s1 s2).
Proof.
  intros Hs1 HS2.
  induction Hs1.
  + constructor.
  + simpl.
    apply nodup_append.
    * apply FinFun.Injective_map_NoDup;[|assumption].
      intros y1 y2.
      apply (f_equal snd).
    * assumption.
    * intros [a b].
      rewrite in_map_iff.
      intros [_ [[= <- _] _]].
      rewrite in_prod_iff.
      tauto.
    * intros [a b].
      rewrite in_prod_iff.
      intros [Ha _].
      rewrite in_map_iff.
      intros [_ [[= Hax _] _]].
      congruence.
Qed.

Require Import Setoid.

Add Parametric Relation A : (set A) (@set_eq A)
 reflexivity proved by (@set_eq_refl A)
 transitivity proved by (@set_eq_tran A) as set_eq_rel.

Add Parametric Morphism A : (@In A)
  with signature @eq A ==> @set_eq A ==> iff as In_set_eq.
Proof.
  intros a l1 l2 H.
  split;apply H.
Qed.

Add Parametric Morphism A : (@In A)
  with signature @eq A ==> @incl A ==> Basics.impl as In_incl.
Proof. firstorder. Qed.

Unset Implicit Arguments.
