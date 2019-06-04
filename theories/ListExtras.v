Require Import List.

Lemma incl_empty : forall A (l : list A),
  incl l nil -> l = nil.
Proof.
  intros. destruct l; try reflexivity.
  exfalso. destruct (H a). left. reflexivity.
Qed.

Lemma filter_in : forall A (f : A -> bool) x s,
  In x s ->
  f x = true ->
  In x (filter f s).
Proof.
  induction s; intros; inversion H; subst; clear H; simpl.
  - rewrite H0. left. reflexivity.
  - apply IHs in H1; try assumption.
    destruct (f a); try assumption.
    right. assumption.
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

Lemma in_not_in : forall A (x y : A) l,
  In x l ->
  ~ In y l ->
  x <> y.
Proof.
  intros. intro; subst. apply H0. assumption.
Qed.


(**


Lemma in_dec {A}:
  (forall x y:A, x = y \/ x <> y) ->
  forall (a:A) (l:list A), In a l \/ ~ In a l.
Proof.
  intros. induction l.
  - right. intro. inversion H0.
  - destruct (H a a0).
    + subst. left; left; reflexivity.
    + destruct IHl.
      * left; right; assumption.
      * right. intro. destruct H2; subst
      ; try (apply H0; reflexivity).
      apply H1; assumption.
Qed.

**)
