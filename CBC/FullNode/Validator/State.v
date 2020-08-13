Require Import
  List
  Coq.Lists.ListSet
  Coq.Classes.RelationClasses
  .

From CasperCBC
    Require Import
      Preamble
      SortedLists
      ListExtras
      ListSetExtras
    .

Import ListNotations.

Section FullNodeState.

(** * Full-node state tracking sent messages *)

(** The development below defines a full-node-like state based on pointed sets,
with the distinguished element being the last message sent by the machine.
*)

Context
    (C V : Type)
    .

(**  As justifications contain sets of messages which contain justifications,
we define justifications, messages, and message sets by mutual recursion.
*)

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

(**
States are defined as pair between a (regular) set of messages and an
optional message representing the last message sent.
*)

Definition state : Type := set message * option message.

End FullNodeState.

Definition get_message_set {C V} (s : state C V) : set (message C V) := fst s.

Definition last_sent {C V} (s : state C V) : option (message C V) := snd s.

Notation "( c , v , j )" :=
  (Msg _ _ c v j)
  (at level 20).

Section FullNodeStateProperties.

(** ** Full node state properties

This section defines syntactical orders for messages and justifications.

The main purpose of these is to define canonical ways to [make_justification]s
ensuring that whenever two states <<s1>>, <<s2>> are equal as pointed sets,
[make_justification] <<s1>> = [make_justification] <<s2>>
(Lemma [make_justification_set_eq]).

*)

Context
    {C V : Type}
    {about_C : StrictlyComparable C}
    {about_V : StrictlyComparable V}
    .

Definition estimate
  (msg : message C V)
  : C
  :=
  match msg with (c,_,_) => c end.

Definition sender
  (msg : message C V)
  : V
  :=
  match msg with (_,v,_) => v end.

Definition get_justification
  (msg : message C V)
  : justification C V
  :=
  match msg with (_,_,j) => j end.

Definition justification_last_sent
  (j : justification C V)
  : option (message C V)
  :=
  match j with
  | NoSent _ _ _ => None
  | LastSent _ _ _ m => Some m
  end.

Definition justification_message_set
  (j : justification C V)
  : message_set C V
  :=
  match j with
  | NoSent _ _ msgs => msgs
  | LastSent _ _ msgs _ => msgs
  end.

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

Lemma message_compare_helper_reflexive
  : CompareReflexive (message_compare_helper justification_compare).
Proof.
  intros (c1, v1, j1) (c2, v2, j2).
  split.
  - simpl. intro H.
    destruct (compare c1 c2) eqn:Hcmp; try discriminate.
    apply StrictOrder_Reflexive in Hcmp; subst.
    destruct (compare v1 v2) eqn:Hcmp; try discriminate.
    apply StrictOrder_Reflexive in Hcmp; subst.
    apply justification_compare_reflexive in H; subst.
    reflexivity.
  - intro H; inversion H; subst; clear H. simpl.
    rewrite (proj2 (StrictOrder_Reflexive c2 c2) eq_refl).
    rewrite (proj2 (StrictOrder_Reflexive v2 v2) eq_refl).
    apply justification_compare_reflexive.
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
  - inversion H; subst.
    rewrite (proj2 (message_compare_helper_reflexive m0 m0) eq_refl).
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
    ; try (apply message_compare_helper_reflexive in Hmsg2; subst; rewrite Hmsg1; reflexivity)
    ; try (apply message_compare_helper_reflexive in Hmsg1; subst; rewrite Hmsg2; assumption)
    ; rewrite (H m1 m2 _ Hmsg1 Hmsg2)
    ; try reflexivity
    .
    apply H0; try assumption.
    reflexivity.
Qed.

Lemma message_compare_helper_transitive
  : CompareTransitive (message_compare_helper justification_compare).
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
  rewrite (justification_compare_transitive j1 j2 j3 (justification_compare j1 j2)); try assumption; reflexivity.
Qed.

Lemma justification_compare_strict_order
  : CompareStrictOrder justification_compare.
Proof.
  split.
  - apply justification_compare_reflexive.
  - apply justification_compare_transitive.
Qed.

Global Instance justification_type
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
  := message_compare_helper justification_compare.

Lemma message_compare_strict_order
  : CompareStrictOrder message_compare.
Proof.
  split.
  - apply message_compare_helper_reflexive.
  - apply message_compare_helper_transitive.
Qed.

Global Instance message_strictorder
  : CompareStrictOrder message_compare := message_compare_strict_order.

Global Instance message_type
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

Global Instance message_lt_strictorder
  : StrictOrder message_lt.
Proof.
  split. apply compare_lt_irreflexive.
  apply compare_lt_transitive.
Defined.

Fixpoint in_message_set
  (m : message C V)
  (msgs : message_set C V)
  : Prop
  :=
  match msgs with
    | Empty _ _ => False
    | add _ _ m' msgs' => m' = m \/ in_message_set m msgs'
  end.

Definition message_set_incl
  (msgs1 msgs2 : message_set C V)
  : Prop
  := forall (m : message C V), in_message_set m msgs1 -> in_message_set m msgs2.

Definition message_set_eq
  (msgs1 msgs2 : message_set C V)
  : Prop
  := message_set_incl msgs1 msgs2 /\ message_set_incl msgs2 msgs1.

Definition justification_incl
  (j1 j2 : justification C V)
  :=
  message_set_incl (justification_message_set j1) (justification_message_set j2).

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

Lemma in_message_set_add
  (m m' : message C V)
  (s : message_set C V)
  : in_message_set m (message_set_add m' s) <-> m' = m \/ in_message_set m s.
Proof.
  induction s; simpl. try (split; intros; assumption).
  destruct (message_compare m' m0) eqn:Hcmp; simpl.
  - apply StrictOrder_Reflexive in Hcmp. subst.
    split; intros.
    + right. assumption.
    + destruct H as [H | H]; try assumption.
      left. assumption.
  - split; intros; assumption.
  - rewrite IHs.
    rewrite <- or_assoc.
    rewrite (or_comm (m0 = m) (m' = m)).
    rewrite or_assoc.
    split; intros; assumption.
Qed.

Definition make_message_set
  (msgs : set (message C V))
  : message_set C V
  :=
  fold_right message_set_add (Empty C V) msgs.

Lemma in_make_message_set
  (msgs : set (message C V))
  (m : message C V)
  : In m msgs <-> in_message_set m (make_message_set msgs).
Proof.
  induction msgs; simpl; split; intros; try assumption.
  - apply in_message_set_add.
    destruct H as [H | H]; try (left; assumption).
    right.
    apply IHmsgs.
    assumption.
  - apply in_message_set_add in H.
    destruct H as [H | H]; try (left; assumption).
    right.
    apply IHmsgs.
    assumption.
Qed.

Lemma make_message_set_incl
  (msgs1 msgs2 : set (message C V))
  : incl msgs1 msgs2
  <-> message_set_incl (make_message_set msgs1) (make_message_set msgs2).
Proof.
  split; intros Hincl m Hm
  ; apply in_make_message_set; apply in_make_message_set in Hm
  ; apply Hincl
  ; assumption.
Qed.

Lemma make_message_set_eq
  (msgs1 msgs2 : set (message C V))
  : set_eq msgs1 msgs2
  <-> message_set_eq (make_message_set msgs1) (make_message_set msgs2).
Proof.
  split; intros [Heq1 Heq2]; split; apply make_message_set_incl; assumption.
Qed.

Fixpoint unmake_message_set
  (msgs : message_set C V)
  : set (message C V)
  :=
  match msgs with
  | Empty _ _ => []
  | add _ _ m msgs' => set_add compare_eq_dec m (unmake_message_set msgs')
  end.

Lemma in_unmake_message_set
  (msgs : message_set C V)
  (m : message C V)
  : in_message_set m msgs <-> In m (unmake_message_set msgs).
Proof.
  induction msgs; simpl; split; intros; try assumption.
  - apply set_add_iff.
    rewrite <- IHmsgs.
    destruct H.
    + left. symmetry. assumption.
    + right. assumption.
  - apply set_add_iff in H. rewrite <- IHmsgs in H.
    destruct H.
    + left. symmetry. assumption.
    + right. assumption.
Qed.

Lemma unmake_message_set_incl
  (msgs1 msgs2 : message_set C V)
  : message_set_incl msgs1 msgs2
  <-> incl (unmake_message_set msgs1) (unmake_message_set msgs2).
Proof.
  split; intros Hincl m Hm
  ; apply in_unmake_message_set; apply in_unmake_message_set in Hm
  ; apply Hincl
  ; assumption.
Qed.

Lemma message_set_incl_refl
  (msgs : message_set C V)
  : message_set_incl msgs msgs.
Proof.
  apply unmake_message_set_incl.
  apply incl_refl.
Qed.

Lemma message_set_incl_trans
  (msgs1 msgs2 msgs3 : message_set C V)
  (H12 : message_set_incl msgs1 msgs2)
  (H23 : message_set_incl msgs2 msgs3)
  : message_set_incl msgs1 msgs3.
Proof.
  apply unmake_message_set_incl.
  apply incl_tran with (unmake_message_set msgs2)
  ; apply unmake_message_set_incl
  ; assumption.
Qed.

Lemma justification_incl_refl
  (j : justification C V)
  : justification_incl j j.
Proof.
  destruct j; unfold justification_incl; simpl; apply message_set_incl_refl.
Qed.

Lemma in_justification_recursive
  (c : C)
  (v : V)
  (j j' : justification C V)
  (Hs : justification_incl j' j)
  : ~ in_message_set ((c,v,j)) (justification_message_set j').
Proof.
  generalize dependent j.
  revert v. revert c. revert j'.
  apply
    (justification_mut_ind C V
      (fun j' : justification C V =>
        forall c v j,
          justification_incl j' j ->
          ~ in_message_set ((c, v, j)) (justification_message_set j')
      )
      (fun m : message C V =>
        forall (msgs : message_set C V),
          message_set_incl msgs (justification_message_set (get_justification m)) ->
          ~ in_message_set m msgs
      )
      (fun msgs : message_set C V =>
        forall c v j,
          message_set_incl msgs (justification_message_set j) ->
          ~ in_message_set ((c,v,j)) msgs
      )
    ); intros; simpl; intro Hin.
  - unfold justification_incl in H0. simpl in H0.
    specialize (H c v j H0). elim H. assumption.
  - unfold justification_incl in H1. simpl in H1.
    specialize (H c v j H1). elim H. assumption.
  - simpl in H0.
    specialize (H c v j (justification_incl_refl j)).
    apply H. apply H0. assumption.
  - assumption.
  - destruct Hin as [Heq | Hin].
    + subst m. simpl in H.
      specialize (H (justification_message_set j) (message_set_incl_refl _)).
      elim H. apply H1. constructor. reflexivity.
    + specialize (H0 c v j). apply H0; try assumption.
      apply message_set_incl_trans with (add C V m m0); try assumption.
      intros msg Hmsg. right. assumption.
Qed.

Lemma in_justification_recursive'
  (m : message C V)
  (msgs : set (message C V))
  (Hmsgs : justification_message_set (get_justification m) = make_message_set msgs)
  : ~ In m msgs.
Proof.
  destruct m as (c,v, j). simpl in Hmsgs.
  rewrite in_make_message_set. rewrite <- Hmsgs.
  apply in_justification_recursive.
  apply justification_incl_refl.
Qed.

Lemma unmake_message_set_eq
  (msgs1 msgs2 : message_set C V)
  : message_set_eq msgs1 msgs2
  <-> set_eq (unmake_message_set msgs1) (unmake_message_set msgs2).
Proof.
  split; intros [Heq1 Heq2]; split; apply unmake_message_set_incl; assumption.
Qed.

Lemma make_unmake_message_set_eq
  (msgs : set (message C V))
  : set_eq (unmake_message_set (make_message_set msgs)) msgs.
Proof.
  split; intros m Hm.
  - apply in_unmake_message_set in Hm.
    apply in_make_message_set in Hm.
    assumption.
  - apply in_unmake_message_set.
    apply in_make_message_set.
    assumption.
Qed.

Lemma unmake_make_message_set_eq
  (msgs : message_set C V)
  : message_set_eq (make_message_set (unmake_message_set msgs)) msgs.
Proof.
  split; intros m Hm.
  - apply in_make_message_set in Hm.
    apply in_unmake_message_set in Hm.
    assumption.
  - apply in_make_message_set.
    apply in_unmake_message_set.
    assumption.
Qed.

Inductive message_set_locally_sorted
  : message_set C V -> Prop :=
  | LSorted_Empty : message_set_locally_sorted (Empty _ _)
  | LSorted_one : forall msg,
          message_set_locally_sorted (add _ _ msg (Empty _ _))
  | LSorted_more : forall msg msg' msgs,
          message_lt msg msg' ->
          message_set_locally_sorted (add _ _ msg' msgs) ->
          message_set_locally_sorted (add _ _  msg (add _ _ msg' msgs))
  .

Lemma message_set_locally_sorted_strong
  (msg : message C V)
  (msgs : message_set C V)
  (Hls : message_set_locally_sorted (add _ _ msg msgs))
  (msg' : message C V)
  (Hmsg' : in_message_set msg' msgs)
  : message_lt msg msg'.
Proof.
  remember (add _ _ msg msgs) as msgs'.
  generalize dependent msg'. generalize dependent msgs. generalize dependent msg.
  induction Hls; intros; inversion Heqmsgs'; subst; clear Heqmsgs'.
  - inversion Hmsg'.
  - specialize (IHHls  msg' msgs eq_refl).
    destruct Hmsg' as [Hmsg' | Hmsg']; subst; try assumption.
    specialize (IHHls msg'0 Hmsg').
    apply (compare_lt_transitive msg0 msg' msg'0); assumption.
Qed.

Lemma message_set_locally_sorted_tail
  (msg : message C V)
  (msgs : message_set C V)
  (Hls : message_set_locally_sorted (add _ _ msg msgs))
  : message_set_locally_sorted msgs.
Proof.
  inversion Hls; subst; try constructor.
  assumption.
Qed.

Lemma message_set_locally_sorted_eq
  (msgs1 msgs2 : message_set C V)
  (Hmsgs1 : message_set_locally_sorted msgs1)
  (Hmsgs2 : message_set_locally_sorted msgs2)
  (Heq : message_set_eq msgs1 msgs2)
  : msgs1 = msgs2.
Proof.
  generalize dependent msgs2.
  induction msgs1; destruct msgs2; intros; try reflexivity.
  - destruct Heq as [_ Hincl].
    specialize (Hincl m); simpl in Hincl.
    elim Hincl.
    left.
    reflexivity.
  - destruct Heq as [Hincl _].
    specialize (Hincl m); simpl in Hincl.
    elim Hincl.
    left.
    reflexivity.
  - assert (Htl1 := message_set_locally_sorted_tail _ _ Hmsgs1).
    assert (Htl2 := message_set_locally_sorted_tail _ _ Hmsgs2).
    specialize (IHmsgs1 Htl1 msgs2 Htl2). destruct Heq as [Hincl12 Hincl21].
    assert (Heqm : m = m0).
    {
      specialize (Hincl12 m). simpl in Hincl12.
      assert (Hm :  m0 = m \/ in_message_set m msgs2)
        by (apply Hincl12; left; reflexivity).
      destruct Hm as [Hm | Hm]; subst; try reflexivity.
      assert (Hlt := message_set_locally_sorted_strong _ _ Hmsgs2 _ Hm).
      specialize (Hincl21 m0). simpl in Hincl21.
      assert (Hm0 :  m = m0 \/ in_message_set m0 msgs1)
        by (apply Hincl21; left; reflexivity).
      destruct Hm0 as [Hm0 | Hm0]; subst; try reflexivity.
      assert (Hlt' := message_set_locally_sorted_strong _ _ Hmsgs1 _ Hm0).
      apply compare_asymmetric in Hlt'.
      unfold message_lt in Hlt. unfold compare_lt in Hlt.
      rewrite Hlt in Hlt'.
      discriminate Hlt'.
    }
    subst.
    f_equal.
    apply IHmsgs1.
    split; intros msg Hmsg.
    + assert (Hlt := message_set_locally_sorted_strong _ _ Hmsgs1 _ Hmsg).
      specialize (Hincl12 msg).
      assert (Hmsg' : in_message_set msg (add C V m0 msgs2))
        by (apply Hincl12; right; assumption).
      destruct Hmsg'; try assumption.
      subst.
      unfold message_lt in Hlt.
      unfold compare_lt in Hlt.
      rewrite (proj2 (StrictOrder_Reflexive msg msg) eq_refl) in Hlt.
      inversion Hlt.
    + assert (Hlt := message_set_locally_sorted_strong _ _ Hmsgs2 _ Hmsg).
      specialize (Hincl21 msg).
      assert (Hmsg' : in_message_set msg (add C V m0 msgs1))
        by (apply Hincl21; right; assumption).
      destruct Hmsg'; try assumption.
      subst.
      unfold message_lt in Hlt.
      unfold compare_lt in Hlt.
      rewrite (proj2 (StrictOrder_Reflexive msg msg) eq_refl) in Hlt.
      inversion Hlt.
Qed.

Lemma message_set_add_locally_sorted
  (m : message C V)
  (s : message_set C V)
  (Hs : message_set_locally_sorted s)
  : message_set_locally_sorted (message_set_add m s).
Proof.
  induction Hs.
  - simpl. constructor.
  - simpl.
    destruct (message_compare m msg) eqn:Hcmp
    ; constructor; try assumption
    ; try (constructor; assumption).
    apply compare_asymmetric.
    assumption.
  - simpl. simpl in IHHs.
    destruct (message_compare m msg) eqn:Hcmp.
    + constructor; assumption.
    + repeat (constructor; try assumption).
    + destruct (message_compare m msg') eqn:Hcmp'.
      * constructor; assumption.
      * constructor; try assumption.
        apply compare_asymmetric. assumption.
      * constructor; assumption.
Qed.

Lemma make_message_set_locally_sorted
  (msgs : set (message C V))
  : message_set_locally_sorted (make_message_set msgs).
Proof.
  induction msgs; try constructor.
  simpl.
  apply message_set_add_locally_sorted; assumption.
Qed.

Lemma make_message_set_equal
  (s1 s2 : set (message C V))
  : set_eq s1 s2 <-> make_message_set s1 = make_message_set s2.
Proof.
  split; intro Heq.
  - apply message_set_locally_sorted_eq
    ; try apply make_message_set_locally_sorted.
    apply make_message_set_eq.
    assumption.
  - apply set_eq_tran with (unmake_message_set (make_message_set s2))
    ; try apply make_unmake_message_set_eq.
    rewrite <- Heq. apply set_eq_comm.
    apply make_unmake_message_set_eq.
Qed.

Inductive message_set_recursively_sorted
  : message_set C V -> Prop :=
  | RSorted_Empty : message_set_recursively_sorted (Empty _ _)
  | RSorted_one
    : forall msg
      (Hmsg : message_recursively_sorted msg),
    message_set_recursively_sorted (add _ _ msg (Empty _ _))
  | RSorted_more
    : forall msg msg' msgs
      (Hmsg : message_recursively_sorted msg)
      (Hlt : message_lt msg msg')
      (Hmsgs : message_set_recursively_sorted (add _ _ msg' msgs)),
    message_set_recursively_sorted (add _ _  msg (add _ _ msg' msgs))

with message_recursively_sorted
  : message C V -> Prop :=
  | RSorted_msg : forall c v j
    (Hj : justification_recursively_sorted j),
    message_recursively_sorted (Msg _ _ c v j)

with justification_recursively_sorted
  : justification C V -> Prop :=
  | RSorted_NoSent
    : forall
      msgs
      (Hmsgs : message_set_recursively_sorted msgs),
    justification_recursively_sorted (NoSent _ _ msgs)
  | RSorted_LastSent
    : forall
      msgs
      msg
      (Hmsgs : message_set_recursively_sorted msgs)
      (Hmsg : in_message_set msg msgs),
    justification_recursively_sorted (LastSent _ _ msgs msg)
  .

Definition sorted_state_property
  (s : state C V)
  : Prop
  :=
  let (msgs, last) := s in
  Forall message_recursively_sorted msgs
  /\
  match last with
  | None => True
  | Some msg => In msg msgs
  end.

Lemma message_set_recursively_sorted_local
  (msgs : message_set C V)
  (Hrs : message_set_recursively_sorted msgs)
  : message_set_locally_sorted msgs.
Proof.
  induction Hrs; constructor; assumption.
Qed.

Lemma message_set_add_recursively_sorted
  (m : message C V)
  (s : message_set C V)
  (Hm : message_recursively_sorted m)
  (Hs : message_set_recursively_sorted s)
  : message_set_recursively_sorted (message_set_add m s).
Proof.
  induction Hs.
  - simpl. constructor. assumption.
  - simpl.
    destruct (message_compare m msg) eqn:Hcmp
    ; constructor; try assumption
    ; try (constructor; assumption).
    apply compare_asymmetric.
    assumption.
  - simpl. simpl in IHHs.
    destruct (message_compare m msg) eqn:Hcmp.
    + constructor; assumption.
    + repeat (constructor; try assumption).
    + destruct (message_compare m msg') eqn:Hcmp'.
      * constructor; assumption.
      * constructor; try assumption.
        apply compare_asymmetric. assumption.
      * constructor; assumption.
Qed.

Lemma message_set_add_recursively_sorted_iff
  (m : message C V)
  (s : message_set C V)
  : message_set_recursively_sorted (message_set_add m s)
  <-> message_recursively_sorted m /\ message_set_recursively_sorted s.
Proof.
  split.
  - intros Hrs.
    remember (message_set_add m s) as s'.
    generalize dependent s. generalize dependent m.
    induction Hrs; intros; destruct s ; inversion Heqs'; subst.
    + destruct (message_compare m m0); inversion H0.
    + split; try assumption. constructor.
    + destruct (message_compare m m0) eqn:Hcmp; inversion H0; subst; clear H0.
      * apply StrictOrder_Reflexive in Hcmp. subst.
        split; try assumption.
        constructor.
        assumption.
      * destruct s; inversion H2.
        destruct (message_compare m m1); inversion H0.
    + destruct (message_compare m m0) eqn:Hcmp; inversion H0; subst; clear H0.
      * apply StrictOrder_Reflexive in Hcmp. subst.
        split; try assumption.
        constructor; assumption.
      * split; assumption.
      * specialize (IHHrs m s H2).
        destruct IHHrs as [Hm Hs].
        split; try assumption.
        rewrite H2 in *.
        destruct s; constructor; try assumption.
        simpl in H2.
        { destruct (message_compare m m1) eqn:Hm1.
        - inversion H2; subst.
          apply StrictOrder_Reflexive in Hm1. subst.
          apply compare_asymmetric.
          assumption.
        - inversion H2; subst.
          apply compare_asymmetric in Hcmp.
          apply (compare_lt_transitive m0 m m1); assumption.
        - inversion H2; subst.
          assumption.
        }
  - intros [Hm Hs]. apply message_set_add_recursively_sorted; assumption.
Qed.

Lemma make_message_set_recursively_sorted
  (msgs : set (message C V))
  : Forall message_recursively_sorted msgs
  <-> message_set_recursively_sorted (make_message_set msgs).
Proof.
  induction msgs; split; intros Hmsgs; try constructor.
  - specialize (Forall_inv Hmsgs); intro Ha.
    apply Forall_inv_tail in Hmsgs.
    apply IHmsgs in Hmsgs.
    simpl.
    apply message_set_add_recursively_sorted; assumption.
  - simpl in Hmsgs.
    apply message_set_add_recursively_sorted_iff in Hmsgs.
    destruct Hmsgs.
    assumption.
  - simpl in Hmsgs.
    apply message_set_add_recursively_sorted_iff in Hmsgs.
    apply IHmsgs. apply Hmsgs.
Qed.

Definition make_justification
  (s : state C V)
  : justification C V
  :=
  let (msgs, last) := s in
  let msg_set := make_message_set msgs in
  match last with
  | None => NoSent C V msg_set
  | Some m => LastSent C V msg_set m
  end.

Lemma make_justification_sorted
  (s : state C V)
  : sorted_state_property s
  <-> justification_recursively_sorted (make_justification s).
Proof.
  destruct s as (msgs, [msg|]); simpl in *; split; try constructor
  ; (destruct H as [Hall Hmsg] || (inversion H; subst))
  ; try exact I
  ; try (apply make_message_set_recursively_sorted; assumption).
  - apply in_make_message_set. assumption.
  - apply in_make_message_set. assumption.
Qed.

Lemma in_make_justification
  (m : message C V)
  (s : state C V)
  : in_message_set m (justification_message_set (make_justification s))
  <-> In m (get_message_set s).
Proof.
  destruct s as [msgs [final|]]; simpl
  ; rewrite <- in_make_message_set
  ; split; intro; assumption.
Qed.

Lemma unmake_message_set_recursively_sorted
  (msgs : message_set C V)
  (Hrs : message_set_recursively_sorted  msgs)
  : Forall message_recursively_sorted (unmake_message_set msgs).
Proof.
  induction msgs; simpl; intros; try constructor.
  apply Forall_forall. intros msg Hmsg.
  apply set_add_iff in Hmsg.
  inversion Hrs; subst; destruct Hmsg; subst; try assumption.
  + inversion H.
  + apply IHmsgs in Hmsgs.
    rewrite Forall_forall in Hmsgs.
    apply Hmsgs.
    assumption.
Qed.

Definition unmake_justification
  (j : justification C V)
  : state C V
  :=
  pair (unmake_message_set (justification_message_set j)) (justification_last_sent j).

Lemma in_unmake_justification
  (m : message C V)
  (j : justification C V)
  : in_message_set m (justification_message_set j)
  <-> In m (get_message_set (unmake_justification j)).
Proof.
  destruct j; simpl
  ; rewrite <- in_unmake_message_set
  ; split; intro; assumption.
Qed.

Lemma unmake_justification_sorted
  (j : justification C V)
  (Hj : justification_recursively_sorted j)
  : sorted_state_property (unmake_justification j).
Proof.
  destruct j; simpl in *; inversion Hj; subst; split; try exact I
  ; try (apply unmake_message_set_recursively_sorted; assumption).
  apply in_unmake_message_set.
  assumption.
Qed.

Definition make_justification_set_eq
  (s1 s2 : state C V)
  : make_justification s1 = make_justification s2
  <-> set_eq (get_message_set s1) (get_message_set s2) /\ last_sent s1 = last_sent s2.
Proof.
  destruct s1 as [msgs1 [lst1|]]; destruct s2 as [msgs2 [lst2|]]
  ; unfold last_sent; unfold get_message_set; simpl; split; intros [Heqs Heq] || intro Heq
  ; inversion Heq; subst; try (split; try reflexivity)
  ; try (apply make_message_set_equal; assumption)
  ; f_equal
  ; apply make_message_set_equal; assumption
  .
Qed.

Section message_oracles.

Fixpoint sent_messages_justification
  (j : justification C V)
  : set (message C V)
  :=
  match j with
  | NoSent _ _ _ => []
  | LastSent _ _ msgs ((c,v,j)) =>
    set_add compare_eq_dec ((c,v,j)) (sent_messages_justification j)
  end.

Definition sent_messages
  (s : state C V)
  : set (message C V)
  :=
  match last_sent s with
  | None => []
  | Some ((c, v, j)) =>
    set_add compare_eq_dec ((c, v, j)) (sent_messages_justification j)
  end.

Definition has_been_sent_oracle
  (s : state C V)
  (m : message C V)
  : bool
  :=
  inb compare_eq_dec m (sent_messages s).

Definition has_been_received_oracle
  (s : state C V)
  (m : message C V)
  : bool
  :=
  inb compare_eq_dec m (get_message_set s)
  && negb (has_been_sent_oracle s m).

  Lemma has_been_sent_not_received
    (s : state C V)
    (m : message C V)
    (Hbs : has_been_sent_oracle s m = true)
    : has_been_received_oracle s m = false.
  Proof.
    unfold has_been_received_oracle.
    rewrite Hbs. apply Bool.andb_false_r.
  Qed.

  Lemma has_been_received_not_sent
    (s : state C V)
    (m : message C V)
    (Hbr : has_been_received_oracle s m = true)
    : has_been_sent_oracle s m = false.
  Proof.
    unfold has_been_received_oracle in Hbr.
    apply Bool.andb_true_iff in Hbr.
    destruct Hbr as [_ Hbr].
    apply Bool.negb_true_iff in Hbr.
    assumption.
  Qed.

End message_oracles.

End FullNodeStateProperties.
