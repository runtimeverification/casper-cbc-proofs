Require Import
  List
  Coq.Lists.ListSet
  Coq.Classes.RelationClasses
  .

From CasperCBC
    Require Import
      Preamble
      SortedLists
    .

Import ListNotations.

Section FullNodeState.

Context
    (C V : Type)
    .

Inductive justification : Type :=
    | NoSent : message_set -> justification
    | LastSent : message_set -> message -> justification

  with message : Type :=
    Msg : C -> V -> justification -> message

  with message_set : Type :=
    | Empty : message_set
    | add : message -> message_set -> message_set
  .

Scheme justification_mut_ind := Induction for justification Sort Prop
with message_mut_ind := Induction for message Sort Prop
with message_set_mut_ind := Induction for message_set Sort Prop
.

Definition justification0 : justification := NoSent Empty.

Definition state : Type := set message * option message.

End FullNodeState.

Notation "( c , v , j )" :=
  (Msg _ _ c v j)
  (at level 20).

Section justification_compare_strict_order.

Context
    {C V : Type}
    {about_C : StrictlyComparable C}
    {about_V : StrictlyComparable V}
    .

Definition message_compare_helper
  (justification_compare : justification C V -> justification C V -> comparison)
  (msg1 msg2 : message C V)
  : comparison
  := 
  match msg1, msg2 with
    (c1, v1, j1), (c2, v2, j2) =>
    match compare c1 c2 with
    | Eq =>
      match compare v1 v2 with
      | Eq => justification_compare j1 j2
      | cmp_v => cmp_v
      end
    | cmp_c => cmp_c
    end
  end.

Fixpoint justification_compare
  (sigma1 sigma2 : justification C V)
  : comparison
  :=
  match sigma1, sigma2 with
    | NoSent _ _ msgs1, NoSent _ _ msgs2 =>
      message_set_compare_helper msgs1 msgs2
    | NoSent _ _ _, _ => Lt
    | _, NoSent _ _ _ => Gt
    | LastSent _ _ msgs1 last1, LastSent _ _ msgs2 last2 =>
      match message_set_compare_helper msgs1 msgs2 with
      | Eq => message_compare_helper justification_compare last1 last2
      | cmp => cmp
      end
  end

with message_set_compare_helper
  (msgs1 msgs2 : message_set C V)
  : comparison
  :=
  match msgs1, msgs2 with
  | Empty _ _, Empty _ _ => Eq
  | Empty _ _, _ => Lt
  | _, Empty _ _ => Gt
  | add _ _ m1 msgs1', add _ _ m2 msgs2' =>
    match message_compare_helper justification_compare m1 m2 with
    | Eq => message_set_compare_helper msgs1' msgs2'
    | cmp => cmp
    end
  end.

Lemma message_compare_helper_reflexive
  (scompare : justification C V -> justification C V -> comparison)
  (Hcr : CompareReflexive scompare)
  : CompareReflexive (message_compare_helper scompare).
Proof.
  intros (c1, v1, j1) (c2, v2, j2).
  split.
  - simpl. intro H.
    destruct (compare c1 c2) eqn:Hcmp; try discriminate.
    apply StrictOrder_Reflexive in Hcmp; subst.
    destruct (compare v1 v2) eqn:Hcmp; try discriminate.
    apply StrictOrder_Reflexive in Hcmp; subst.
    apply Hcr in H; subst.
    reflexivity.
  - intro H; inversion H; subst; clear H. simpl.
    rewrite (proj2 (StrictOrder_Reflexive c2 c2) eq_refl).
    rewrite (proj2 (StrictOrder_Reflexive v2 v2) eq_refl).
    apply Hcr.
    reflexivity.
Qed.

Lemma message_compare_helper_transitive
  (scompare : justification C V -> justification C V -> comparison)
  (Hcr : CompareReflexive scompare)
  (Hct : CompareTransitive scompare)
  : CompareTransitive (message_compare_helper scompare).
Proof.
  intros (c1, v1, j1) (c2, v2, j2) (c3, v3, j3) comp.
  simpl; intros H12 H23.
  destruct (compare c1 c2) eqn:Hc1; destruct (compare c2 c3) eqn:Hc3; subst
  ; try discriminate
  ; try (apply StrictOrder_Reflexive in Hc1; subst; rewrite Hc3; assumption)
  ; try (apply StrictOrder_Reflexive in Hc3; subst; rewrite Hc1; reflexivity)
  ; rewrite (StrictOrder_Transitive c1 c2 c3 _ Hc1 Hc3)
  ; try reflexivity
  .
  destruct (compare v1 v2) eqn:Hv1; destruct (compare v2 v3) eqn:Hv3; subst; try discriminate
  ; try (apply StrictOrder_Reflexive in Hv1; subst; rewrite Hv3; assumption)
  ; try (apply StrictOrder_Reflexive in Hv3; subst; rewrite Hv1; reflexivity)
  ; rewrite (StrictOrder_Transitive v1 v2 v3 _ Hv1 Hv3); try reflexivity
  .
  rewrite (Hct j1 j2 j3 (scompare j1 j2)); try assumption; reflexivity.
Qed.

Lemma message_compare_helper_strict_order
  (scompare : justification C V -> justification C V -> comparison)
  (Hcs : CompareStrictOrder scompare)
  : CompareStrictOrder (message_compare_helper scompare)
  .
Proof.
  destruct Hcs as [Hcr Hct].
  split.
  - apply message_compare_helper_reflexive. assumption.
  - apply message_compare_helper_transitive; assumption.
Qed.

Lemma justification_compare_reflexive
  : CompareReflexive justification_compare.
Proof.
  intro x.
  apply
    (justification_mut_ind C V
      (fun x : justification C V =>
        forall y : justification C V, justification_compare x y = Eq <-> x = y
      )
      (fun x : message C V =>
        forall y : message C V, message_compare_helper justification_compare x y = Eq <-> x = y
      )
      (fun x : message_set C V =>
        forall y : message_set C V, message_set_compare_helper x y = Eq <-> x = y
      )
    ); intros; simpl; split; intros.
  - destruct y; simpl in H0; try discriminate.
    f_equal. apply H. assumption.
  - subst. apply H. reflexivity.
  - destruct y; try discriminate.
    destruct (message_set_compare_helper m m1) eqn:Hset; try discriminate.
    apply H in Hset.
    apply H0 in H1.
    subst.
    reflexivity.
  - subst. rewrite (proj2 (H m) eq_refl). apply H0. reflexivity.
  - destruct y as (cy, vy, jy).
    destruct (compare c cy) eqn:Hc; try discriminate.
    apply StrictOrder_Reflexive in Hc; subst.
    destruct (compare v vy) eqn:Hv; try discriminate.
    apply StrictOrder_Reflexive in Hv; subst.
    apply H in H0. subst. reflexivity.
  - subst.
    rewrite (proj2 (StrictOrder_Reflexive c c) eq_refl).
    rewrite (proj2 (StrictOrder_Reflexive v v) eq_refl).
    apply H. reflexivity.
  - destruct y; try discriminate. reflexivity.
  - subst. reflexivity.
  - destruct y; try discriminate.
    destruct (message_compare_helper justification_compare m m1) eqn:Hmsg; try discriminate.
    apply H in Hmsg. subst.
    apply H0 in H1. subst.
    reflexivity.
  - subst.
    rewrite (proj2 (H m) eq_refl).
    apply H0.
    reflexivity.
Qed.

Lemma message_set_compare_helper_reflexive
  : CompareReflexive message_set_compare_helper.
Proof.
  intros x.
  induction x; intros; destruct y; simpl; split; intros
  ; try discriminate
  ; try reflexivity
  .
  - destruct (message_compare_helper justification_compare m m0) eqn:Hmsg; try discriminate.
    apply IHx in H. apply message_compare_helper_reflexive in Hmsg; subst; try reflexivity.
    apply justification_compare_reflexive.
  - inversion H; subst.
    specialize (message_compare_helper_reflexive justification_compare justification_compare_reflexive)
    ; intro Hmr.
    rewrite (proj2 (Hmr m0 m0) eq_refl).
    apply IHx.
    reflexivity.
Qed.

Lemma justification_compare_transitive
  : CompareTransitive justification_compare.
Proof.
  destruct (@compare_strictorder C about_C) as [Rc Tc].
  destruct (@compare_strictorder V about_V) as [Rv Tv].
  intros x y. generalize dependent x.
  apply
    (justification_mut_ind C V
      (fun y : justification C V =>
        forall (x z : justification C V) (comp : comparison)
          (Hxy : justification_compare x y = comp)
          (Hyz : justification_compare y z = comp),
          justification_compare x z = comp
      )
      (fun y : message C V =>
        forall (x z : message C V) (comp : comparison)
          (Hxy : message_compare_helper justification_compare x y = comp)
          (Hyz : message_compare_helper justification_compare y z = comp),
          message_compare_helper justification_compare x z = comp
      )
      (fun y : message_set C V =>
        forall (x z : message_set C V) (comp : comparison)
          (Hxy : message_set_compare_helper x y = comp)
          (Hyz : message_set_compare_helper y z = comp),
          message_set_compare_helper x z = comp
      )
    )
  ; intros; destruct x; destruct z; try discriminate; try assumption
  ; simpl in Hxy; simpl in Hyz; simpl
  ; subst; try discriminate.
  - apply H; try assumption. reflexivity.
  - destruct (message_set_compare_helper m m3) eqn:Hset3
    ; destruct (message_set_compare_helper m1 m) eqn:Hset1
    ; try discriminate
    ; try (apply message_set_compare_helper_reflexive in Hset3; subst; rewrite Hset1; reflexivity)
    ; try (apply message_set_compare_helper_reflexive in Hset1; subst; rewrite Hset3; assumption)
    ; rewrite (H m1 m3 _ Hset1 Hset3)
    ; try reflexivity
    .
    apply H0; try assumption.
    reflexivity.
  - destruct (compare c0 c) eqn:Hc0
    ; destruct (compare c c1) eqn:Hc1
    ; try discriminate
    ; try (apply StrictOrder_Reflexive in Hc1; subst; rewrite Hc0; reflexivity)
    ; try (apply StrictOrder_Reflexive in Hc0; subst; rewrite Hc1; assumption)
    ; rewrite (StrictOrder_Transitive c0 c c1 _ Hc0 Hc1)
    ; try reflexivity
    .
    destruct (compare v0 v) eqn:Hv0
    ; destruct (compare v v1) eqn:Hv1
    ; try discriminate
    ; try (apply StrictOrder_Reflexive in Hv1; subst; rewrite Hv0; reflexivity)
    ; try (apply StrictOrder_Reflexive in Hv0; subst; rewrite Hv1; assumption)
    ; rewrite (StrictOrder_Transitive v0 v v1 _ Hv0 Hv1)
    ; try reflexivity
    .
    apply H; try assumption.
    reflexivity.
  - destruct (message_compare_helper justification_compare m m2) eqn:Hmsg2
    ; destruct (message_compare_helper justification_compare m1 m) eqn:Hmsg1
    ; try discriminate
    ; try (apply (message_compare_helper_reflexive justification_compare justification_compare_reflexive) in Hmsg2; subst; rewrite Hmsg1; reflexivity)
    ; try (apply (message_compare_helper_reflexive justification_compare justification_compare_reflexive) in Hmsg1; subst; rewrite Hmsg2; assumption)
    ; rewrite (H m1 m2 _ Hmsg1 Hmsg2)
    ; try reflexivity
    .
    apply H0; try assumption.
    reflexivity.
Qed.

Lemma justification_compare_strict_order
  : CompareStrictOrder justification_compare.
Proof.
  split.
  - apply justification_compare_reflexive.
  - apply justification_compare_transitive.
Qed.

Instance justification_type
  : StrictlyComparable (justification C V) :=
  {
    inhabited := justification0 C V;
    compare := justification_compare;
    compare_strictorder := justification_compare_strict_order;
  }.

Definition message0
  : message C V
  :=
  (@inhabited _ about_C, @inhabited _ about_V, justification0 C V).

Definition message_compare
  : message C V -> message C V -> comparison
  := message_compare_helper justification_compare
  .

Lemma message_compare_strict_order
  : CompareStrictOrder message_compare.
Proof.
  apply message_compare_helper_strict_order.
  apply justification_compare_strict_order.
Qed.

Instance message_strictorder
  : CompareStrictOrder message_compare := message_compare_strict_order.

Instance message_type
  : StrictlyComparable (message C V) :=
  { inhabited := message0;
    compare := message_compare;
    compare_strictorder := message_compare_strict_order;
  }.

(* Constructing a StrictOrder type for message_lt *)

Definition message_lt
  : message C V -> message C V -> Prop
  :=
  compare_lt compare.

Instance message_lt_strictorder
  : StrictOrder message_lt.
split. apply compare_lt_irreflexive.
apply compare_lt_transitive.
Defined.

Fixpoint message_set_add
  (m : message C V)
  (s : message_set C V)
  : message_set C V
  :=
  match s with
  | Empty _ _ => add _ _ m (Empty _ _)
  | add _ _ m' s' =>
    match message_compare m m' with
    | Eq => s
    | Lt => add _ _ m s
    | Gt => add _ _ m' (message_set_add m s')
    end
  end.

Definition make_justification
  (s : state C V)
  : justification C V
  :=
  let (msgs, last) := s in
  let msg_set := fold_right message_set_add (Empty C V) msgs in
  match last with
  | None => NoSent C V msg_set
  | Some m => LastSent C V msg_set m
  end.



End justification_compare_strict_order.