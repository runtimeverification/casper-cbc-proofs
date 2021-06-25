Require Import Reals Bool Relations RelationClasses List ListSet EqdepFacts ProofIrrelevance Eqdep_dec.
Import ListNotations.

From CasperCBC Require Export Classes.

(** * General utility definitions, lemmas, and tactics *)

Tactic Notation "spec" hyp(H) :=
  match type of H with ?a -> _ =>
  let H1 := fresh in (assert (H1: a);
  [|generalize (H H1); clear H H1; intro H]) end.
Tactic Notation "spec_save" hyp(H) :=
  match type of H with ?a -> _ =>
  let H1 := fresh in (assert (H1: a);
  [|generalize (H H1); clear H; intro H]) end.
Tactic Notation "spec" hyp(H) constr(a) :=
  (generalize (H a); clear H; intro H).
Tactic Notation "spec" hyp(H) constr(a) constr(b) :=
  (generalize (H a b); clear H; intro H).
Tactic Notation "spec" hyp(H) constr(a) constr(b) constr(c) :=
  (generalize (H a b c); clear H; intro H).
Tactic Notation "spec" hyp(H) constr(a) constr(b) constr(c) constr(d) :=
  (generalize (H a b c d); clear H; intro H).
Tactic Notation "spec" hyp(H) constr(a) constr(b) constr(c) constr(d) constr(e) :=
  (generalize (H a b c d e); clear H; intro H).

Definition noneOrAll
  (op : option Prop)
  : Prop
  :=
  match op with
  | None => True
  | (Some p) => p
  end.

Lemma exist_eq
  {X}
  (P : X -> Prop)
  (a b : {x : X | P x})
  : a = b <-> proj1_sig a = proj1_sig b.
Proof.
  destruct a as [a Ha]; destruct b as [b Hb]; simpl.
  split; intros Heq.
  - inversion Heq. reflexivity.
  - subst. apply f_equal. apply proof_irrelevance.
Qed.

(* https://coq.discourse.group/t/writing-equality-decision-that-reduces-dec-x-x-for-opaque-x/551/2 *)

Lemma eq_dec_refl A (eq_dec : forall x y : A, {x = y} + {x <> y}) x :
  eq_dec x x = left eq_refl.
Proof.
  destruct (eq_dec x x) as [|[]]; trivial.
  f_equal.
  now apply K_dec_type with (P := fun prf => prf = eq_refl).
Qed.

Instance nat_eq_dec: EqDecision nat := eq_nat_dec.

Definition mid {X Y Z : Type} (xyz : X * Y * Z) : Y :=
  snd (fst xyz).

Lemma or_and_distr_left : forall A B C, (A /\ B) \/ C <-> (A \/ C) /\ (B \/ C).
Proof.
  intros; split; intro.
  - split; destruct H as [[HA HB] | HC]; (left; assumption) || right; assumption.
  - destruct H as [Hac Hbc].
    destruct Hac as [Ha | Hc]; try (right; assumption).
    destruct Hbc as [Hb | Hc]; try (right; assumption).
    left. split; assumption.
Qed.

Lemma and_iff_l {P Q R:Prop} : P -> (Q <-> R) -> (P /\ Q <-> P /\ R).
Proof.
  firstorder.
Qed.

Lemma not_ex_all_not
  {A : Type}
  (P : A -> Prop)
  (Hne : ~ (exists a : A, P a))
  : forall a:A, ~ P a.
Proof.
  intros a Hpa.
  apply Hne.
  exists a.
  assumption.
Qed.

Lemma forall_and_commute
  {A : Type}
  (P Q : A -> Prop)
  : ((forall a, P a) /\ (forall a, Q a)) <-> forall a, P a /\ Q a.
Proof.
  firstorder.
Qed.

Lemma mirror_reflect: forall X (f : X -> bool) (P : X -> Prop),
  (forall x : X, f x = true <-> P x) ->
  (forall x : X, f x = false <-> ~P x).
Proof.
  split; repeat intro.
  + rewrite <- H in H1. rewrite H0 in H1. discriminate.
  + specialize (H x). destruct (f x).
    exfalso. apply H0. rewrite <- H. reflexivity.
    reflexivity.
Qed.

Theorem mirror_reflect_curry :
  forall (X Y : Type) (f : X -> Y -> bool) (P : X -> Y -> Prop),
    (forall x y, f x y = true <-> P x y) ->
    (forall x y, f x y = false <-> ~ P x y).
Proof.
  intros.
  split; intros.
  intro H_absurd. apply H in H_absurd.
  rewrite H0 in H_absurd; discriminate.
  apply not_true_is_false.
  intro H_not. apply H in H_not.
  contradiction.
Qed.

Lemma dec_if_true
  {X Y B: Type}
  {P : X -> Y -> Prop}
  (dec : forall (x : X) (y : Y), {P x y} + {~P x y})
  (x : X) (y : Y) (t e : B)
  (Hp : P x y)
  : (if dec x y then t else e) = t.
Proof.
  destruct (dec x y) eqn:Hcmp; try reflexivity.
  elim n. assumption.
Qed.

Lemma dec_if_false
  {X Y B: Type}
  {P : X -> Y -> Prop}
  (dec : forall (x : X) (y : Y), {P x y} + {~P x y})
  (x : X) (y : Y) (t e : B)
  (Hnp : ~P x y)
  : (if dec x y then t else e) = e.
Proof.
  destruct (dec x y) eqn:Hcmp; try reflexivity.
  elim Hnp. assumption.
Qed.

Lemma eq_dec_if_true {A B: Type} (eq_dec : forall x y : A, {x = y} + {x <> y}) : forall (x y : A) (t e : B),
  x = y -> (if eq_dec x y then t else e) = t.
Proof.
  apply dec_if_true.
Qed.

Lemma eq_dec_if_false {A B: Type} (eq_dec : forall x y : A, {x = y} + {x <> y}) : forall (x y : A) (t e : B),
  x <> y -> (if eq_dec x y then t else e) = e.
Proof.
  apply dec_if_false.
Qed.

Lemma dec_match_left
  {X Y B: Type}
  {P : X -> Y -> Prop}
  (dec : forall (x : X) (y : Y), {P x y} + {~P x y})
  (x : X) (y : Y) (t : P x y -> B) (e : ~P x y -> B)
  (Hp : P x y)
  (Hirrelevance : forall p : P x y, p = Hp)
  : (match dec x y with | left p => t p | right np => e np end) = t Hp.
Proof.
  destruct (dec x y) eqn:Hcmp.
  - rewrite Hirrelevance at 1. reflexivity.
  - elim n. assumption.
Qed.

Lemma dec_match_right
  {X Y B: Type}
  {P : X -> Y -> Prop}
  (dec : forall (x : X) (y : Y), {P x y} + {~P x y})
  (x : X) (y : Y) (t : P x y -> B) (e : ~P x y -> B)
  (Hp : ~P x y)
  (Hirrelevance : forall p : ~P x y, p = Hp)
  : (match dec x y with | left p => t p | right np => e np end) = e Hp.
Proof.
  destruct (dec x y) eqn:Hcmp.
  - elim Hp. assumption.
  - rewrite Hirrelevance at 1. reflexivity.
Qed.

Class DecidablePred {A} (r : A -> Prop) :=
  pred_dec : forall (a : A), r a \/ ~ r a.
Hint Mode DecidablePred ! ! : typeclass_instances.

Class PredicateFunction {A} (r : A -> Prop) (r_fn : A -> bool) : Prop :=
  {
    equiv : forall a, r a <-> r_fn a = true;
    predicate_function_dec :> DecidablePred r;
  }.
Hint Mode PredicateFunction ! ! - : typeclass_instances.
Hint Mode PredicateFunction ! - ! : typeclass_instances.

Definition predicate_not {A} (p : A -> Prop) : A -> Prop :=
  fun a => ~ p a.

Lemma predicate_function_neg {A} `{PredicateFunction A} :
  forall a, ~ r a <-> r_fn a = false.
Proof.
  intro a; split; intros.
  apply not_true_iff_false. intro Hnot.
  apply equiv in Hnot. contradiction.
  intro Hnot. apply not_true_iff_false in H0.
  apply H0. apply (equiv a). assumption.
Qed.

Class PredicateFunction2 {A B} (r : A -> B -> Prop) (r_fn : A -> B -> bool) : Prop :=
  predicate_function2 : forall a b, r a b <-> r_fn a b = true.
Hint Mode PredicateFunction2 ! ! ! - : typeclass_instances.
Hint Mode PredicateFunction2 ! ! - ! : typeclass_instances.

Lemma predicate_function2_neg : forall A B (r : A -> B -> Prop) (r_fn : A -> B -> bool),
  PredicateFunction2 r r_fn ->
  forall a b, ~ r a b <-> r_fn a b = false.
Proof.  intros. rewrite (H a b).   apply not_true_iff_false. Qed.

Lemma predicate_function2_decidable : forall A B (r : A -> B -> Prop) (r_fn : A -> B -> bool),
  PredicateFunction2 r r_fn ->
  forall a b, r a b \/ ~r a b.
Proof.
  intros. destruct (r_fn a b) eqn:Hr.
  - left. apply H. assumption.
  - right. apply (predicate_function2_neg _ _ _ _ H). assumption.
Qed.

Lemma bool_decide_predicate_function2 {A B} (P : A -> B -> Prop) {P_dec : RelDecision P}:
  PredicateFunction2 P (fun a b => bool_decide (P a b)).
Proof.
  intros. intros a b. symmetry. apply bool_decide_eq_true.
Qed.

Lemma Is_true_predicate_function2: forall A B (f : A -> B -> bool),
  PredicateFunction2 (fun a b => Is_true (f a b)) f.
Proof.
  intros. intros a b. symmetry. apply Is_true_iff_eq_true.
Qed.

(* Reflexivity of comparison operators *)
Class CompareReflexive A `(Comparison A) : Prop :=
 compare_eq : forall x y, compare x y = Eq <-> x = y.
Hint Mode CompareReflexive ! ! : typeclass_instances.

(* About reflexive comparison operators *)
Lemma compare_eq_refl `{CompareReflexive A} :
  forall x, compare x x = Eq.
Proof.
intros.
apply compare_eq; reflexivity.
Qed.

Lemma compare_eq_lt `{CompareReflexive A} :
  forall x, compare x x <> Lt.
Proof.
  intros x Hnot.
  assert (compare x x = Eq) by apply compare_eq_refl.
  congruence.
Qed.

Lemma compare_lt_neq `{CompareReflexive A} :
  forall x y, compare x y = Lt -> x <> y.
Proof.
  intros x y Hcomp Hnot.
  subst. now (apply (compare_eq_lt y) in Hcomp).
Qed.

Lemma compare_eq_gt `{CompareReflexive A} :
  forall x, compare x x <> Gt.
Proof.
  intros x Hnot.
  assert (compare x x = Eq) by apply compare_eq_refl.
  congruence.
Qed.

Lemma compare_gt_neq `{CompareReflexive A} :
  forall x y, compare x y = Gt -> x <> y.
Proof.
  intros x y H_comp H_not.
  subst. now apply compare_eq_gt in H_comp.
Qed.

(* Transitivity of comparison operators *)
Class CompareTransitive A `(Comparison A) : Prop :=
  compare_transitive : forall x y z comp,
   compare x y = comp ->
   compare y z = comp ->
   compare x z = comp.
Hint Mode CompareTransitive ! ! : typeclass_instances.

(* Strict-orderedness of comparison operators *)
Class CompareStrictOrder A `(Comparison A) : Prop :=
  {
    CompareStrictOrder_Reflexive :> CompareReflexive A compare;
    CompareStrictOrder_Transitive :> CompareTransitive A compare;
  }.
Hint Mode CompareStrictOrder ! ! : typeclass_instances.

(* Strictly-ordered comparisons give decidable equality *)
Instance compare_eq_dec `{CompareStrictOrder A} : EqDecision A.
Proof.
  intros x y.
  destruct (compare x y) eqn:Hxy;
    (left; apply CompareStrictOrder_Reflexive; assumption)
    || (right; intro; subst; [now apply compare_eq_lt in Hxy || now apply compare_eq_gt in Hxy]).
Qed.

(* Asymmetry of comparison operators *)
Class CompareAsymmetric A `(Comparison A) : Prop :=
 compare_asymmetric : forall x y, compare x y = Lt <-> compare y x = Gt.
Hint Mode CompareAsymmetric ! ! : typeclass_instances.

(* Strictly-ordered comparisons give asymmetry *)
Instance CompareStrictOrder_Asymmetric `{CompareStrictOrder A} : CompareAsymmetric A compare.
Proof.
  constructor; intros.
  - destruct (compare y x) eqn:Hyx; try reflexivity; exfalso.
    + apply (compare_eq y x) in Hyx.
      subst; contradict H1.
      apply compare_eq_lt.
    + eapply compare_transitive in H1; eauto.
      contradict H1.
      apply compare_eq_lt.
  - destruct (compare x y) eqn:Hyx; try reflexivity; exfalso.
    + apply compare_eq in Hyx.
      subst; contradict H1.
      apply compare_eq_gt.
    + eapply compare_transitive in H1; eauto.
      contradict H1.
      apply compare_eq_gt.
Qed.

(* Defining a compare_lt predicate from a compare operator *)
Definition compare_lt `{Comparison A} : relation A := fun x y => compare x y = Lt.

(* A series of properties about compare_lt *)
Instance compare_lt_irreflexive `{CompareReflexive A} :
  Irreflexive compare_lt.
Proof.
  intros x Hlt.
  unfold compare_lt in Hlt.
  assert (compare x x = Eq) by apply compare_eq_refl.
  congruence.
Qed.

Instance compare_lt_transitive `{CompareTransitive A} :
  Transitive compare_lt.
Proof.
  intros x y z.
  apply compare_transitive.
Qed.

Instance compare_lt_strict_order `{CompareStrictOrder A} :
  StrictOrder compare_lt.
Proof.
  constructor; typeclasses eauto.
Qed.

Instance compare_lt_asymmetric `{CompareStrictOrder A} :
  Asymmetric compare_lt.
Proof.
  intros x y.
  assert (compare y y = Eq) by (apply compare_eq; reflexivity).
  unfold compare_lt; intros.
  eapply compare_transitive in H2; eauto.
  congruence.
Qed.

(* A generic type class for inhabited types with a strictly ordered comparison operator *)
Class StrictlyComparable X `(Comparison X) `{Inhabited X} :=
  compare_strictorder :> CompareStrictOrder X compare.
Hint Mode StrictlyComparable ! ! - : typeclass_instances.

Instance strictly_comparable_eq_dec `{StrictlyComparable M} : EqDecision M := compare_eq_dec.

Definition comparable
  {A : Type}
  (R : A -> A -> Prop)
  (a b : A)
  : Prop
  :=
  a = b \/ R a b \/ R b a.

Lemma comparable_commutative
   {A : Type}
   (R : A -> A -> Prop)
   (a b : A) :
   comparable R a b <-> comparable R b a.
Proof.
  firstorder.
Qed.

Definition comparableb
  `{EqDecision A}
  (f : A -> A -> bool)
  (a b : A)
  : bool
  :=
  if decide (a = b) then true
  else orb (f a b) (f b a).

Definition incomparableb
  `{EqDecision A}
  (f : A -> A -> bool)
  (a b : A)
  : bool
  :=
  if decide (a = b) then false
  else andb (negb (f a b)) (negb (f b a)).

Lemma negb_comparableb `{EqDecision A} (f : A -> A -> bool) (a b : A):
  incomparableb f a b = negb (comparableb f a b).
Proof.
  unfold incomparableb, comparableb.
  destruct (decide (a = b));[reflexivity|].
  rewrite negb_orb.
  reflexivity.
Qed.

Lemma comparable_function
  {A : Type}
  {eq_A : EqDecision A}
  (f : A -> A -> bool)
  (R : A -> A -> Prop)
  (HR : PredicateFunction2 R f)
  : PredicateFunction2 (comparable R) (comparableb f).
Proof.
  intros a b. unfold comparable. unfold comparableb.
  split; intro.
  - destruct H as [Heq | [Hab | Hba]]; destruct (decide (a = b)); try reflexivity.
    + elim n. assumption.
    + apply HR in Hab. rewrite Hab. reflexivity.
    + apply HR in Hba. rewrite Hba. rewrite orb_comm. reflexivity.
  - destruct (decide (a = b)); try (left; assumption).
    right.
    apply orb_true_iff in H.
    destruct H as [H | H]; apply HR in H.
    + left. assumption.
    + right. assumption.
Qed.

Instance comparable_dec
  {A : Type}
  {eq_A : EqDecision A}
  (R : A -> A -> Prop)
  {HR : RelDecision R}
  : RelDecision (comparable R).
Proof.
  intros a b.
  eapply reflect_dec.
  apply iff_reflect, comparable_function, bool_decide_predicate_function2.
Qed.

Lemma comparable_function_neg
  `{EqDecision A}
  (f : A -> A -> bool)
  (R : A -> A -> Prop)
  (HR : PredicateFunction2 R f)
  (a b : A)
  (Hnc : comparableb f a b = false)
  : a <> b /\ ~R a b /\ ~R b a.
Proof.
  unfold comparableb in Hnc.
  destruct (decide (a = b)); try discriminate Hnc.
  split; try assumption.
  destruct (f a b) eqn:Hab; try discriminate Hnc.
  destruct (f b a) eqn:Hba; try discriminate Hnc.
  apply (predicate_function2_neg _ _ _ _ HR) in Hab.
  apply (predicate_function2_neg _ _ _ _ HR) in Hba.
  split; assumption.
Qed.

Lemma comparable_function_bool
  {A : Type}
  {eq_A : EqDecision A}
  (f : A -> A -> bool)
  : PredicateFunction2 (comparable f) (comparableb f).
Proof.
  apply comparable_function.
  apply Is_true_predicate_function2.
Qed.

Lemma compare_two_cases
  `{CompareStrictOrder M}
  : forall m1 m2 : M,
    (compare m1 m2 = Eq /\ compare m2 m1 = Eq) \/
    (compare m1 m2 = Lt /\ compare m2 m1 = Gt) \/
    (compare m1 m2 = Gt /\ compare m2 m1 = Lt).
Proof.
  intros m1 m2.
  destruct (compare m1 m2) eqn:H_m.
  left. split; try reflexivity.
  rewrite compare_eq in H_m. subst.
  apply compare_eq_refl.
  right. left; split; try reflexivity.
  now apply compare_asymmetric.
  right; right; split; try reflexivity.
  now apply compare_asymmetric.
Qed.

Tactic Notation "case_pair" constr(about_M) constr(m1) constr(m2) :=
  assert (H_fresh := @compare_two_cases _ about_M m1 m2);
  destruct H_fresh as [[H_eq1 H_eq2] | [[H_lt H_gt] | [H_gt H_lt]]].

Instance sigify_eq_dec `{CompareStrictOrder X} (P : X -> Prop) :
  EqDecision {x | P x}.
Proof.
  intros x1 x2.
  destruct x1 as [x1 about_x1].
  destruct x2 as [x2 about_x2].
  destruct (compare_eq_dec x1 x2) as [left | right].
  left. apply exist_eq; assumption.
  right. intro Hnot. apply exist_eq in Hnot.
  contradiction.
Qed.

Instance sigify_compare X `(Comparison X) (P : X -> Prop) : Comparison {x | P x}.
intros [X0 P0] [X1 P1].
exact (compare X0 X1).
Defined.

(* StrictlyComparable option type *)
Instance option_compare X `(Comparison X) : Comparison (option X) :=
  fun ox oy =>
  match ox, oy with
  | None, None => Eq
  | None, _ => Lt
  | _, None => Gt
  | Some x, Some y => compare x y
  end.

Instance option_compare_reflexive `{CompareStrictOrder X} :
 CompareReflexive (option X) (option_compare X compare).
Proof.
  intros [x|] [y|]; simpl; split; intro Hxy; inversion Hxy; try reflexivity.
  - f_equal. apply compare_eq. apply H2.    
  - f_equal. rewrite <- H2 at 1. apply compare_eq in H2. apply H2.
Qed.

Instance option_compare_transitive `{CompareStrictOrder X} :
 CompareTransitive (option X) (option_compare X compare).
Proof.
  intros [x|] [y|] [z|] [| |]; simpl; intros Hxy Hyz; try discriminate; try reflexivity.
  - apply (CompareStrictOrder_Transitive x y z _); assumption.
  - apply (CompareStrictOrder_Transitive x y z _); assumption.
  - apply (CompareStrictOrder_Transitive x y z _); assumption.
Qed.

Instance strictorder_option `{CompareStrictOrder X} :
  CompareStrictOrder (option X) (option_compare X compare).
Proof.
  split; typeclasses eauto.
Qed.

(* Now we can have the following for free : *)
Program Instance OptionStrictlyComparable `{StrictlyComparable X}
  : StrictlyComparable (option X) (option_compare X compare).

(* Composing StrictlyComparable types *)
(* Constructing the compare function *)
Instance compare_compose X Y `(Comparison X) `(Comparison Y) : Comparison (X * Y) :=
  fun p1 p2 =>
    match p1, p2 with
    | (x1, y1), (x2, y2) => match compare x1 x2 with
                           | Eq => match compare y1 y2 with
                                  | Eq => Eq
                                  | _ => compare y1 y2
                                  end
                           | _ => compare x1 x2
                           end
    end.

(* Constructing the strictorder proof *)
Instance reflexive_compose `{CompareStrictOrder X} `{CompareStrictOrder Y} :
  CompareReflexive (X*Y) (compare_compose X Y compare compare).
Proof.
  intros (x1, y1) (x2, y2).
  split; intros.
  - unfold compare in H3; simpl in H3.
    destruct (compare x1 x2) eqn:H_x;
    destruct (compare y1 y2) eqn: H_y;
    try congruence.
    apply CompareStrictOrder_Reflexive in H_x;
    apply CompareStrictOrder_Reflexive in H_y.
    subst; reflexivity.
  - inversion H3; subst.
    unfold compare; simpl.
    do 2 rewrite compare_eq_refl; reflexivity.
Qed.

Lemma compare_compose_lt `{CompareStrictOrder X} `{CompareStrictOrder Y} :
  forall (x1 x2 : X) (y1 y2 : Y) (c : comparison),
  compare_compose X Y compare compare (x1, y1) (x2, y2) = c ->
  compare x1 x2 = c \/
  x1 = x2 /\ compare y1 y2 = c.
Proof.
  intros x1 x2 y1 y2 c H_12.
  simpl in H_12.
  destruct (compare x1 x2) eqn:H_x; try (left; assumption).
  right. split. now apply CompareStrictOrder_Reflexive in H_x.
  destruct (compare y1 y2) eqn:H_y; try discriminate; assumption.
Qed.

Instance transitive_compose `{CompareStrictOrder X} `{CompareStrictOrder Y} :
  CompareTransitive (X*Y) (compare_compose X Y compare compare).
Proof.
  intros (x1, y1) (x2, y2) (x3, y3) comp H12 H23.
  destruct comp eqn:H_comp; try
  (apply reflexive_compose;
   apply reflexive_compose in H12;
     apply reflexive_compose in H23;
     inversion H12; inversion H23; subst; reflexivity).
  - unfold compare in *.
    pose proof compare_compose_lt x1 x2 y1 y2 Lt H12 as H_useful.
    pose proof compare_compose_lt x2 x3 y2 y3 Lt H23 as H_useful'.      
    destruct H_useful as [left | right];
    destruct H_useful' as [left' | right'].
    * assert (Hc: compare x1 x3 = Lt) by (eapply compare_transitive; eauto).
      unfold compare_compose.
      rewrite Hc; reflexivity.
    * destruct right'; subst.
      simpl; rewrite left; reflexivity.
    * destruct right; subst.
      simpl; rewrite left'; reflexivity.
    * subst.
      destruct right.
      destruct right'.
      assert (compare y1 y3 = Lt) by (eapply compare_transitive; eauto).
      unfold compare_compose.
      rewrite H3.
      rewrite H5.
      rewrite compare_eq_refl.
      rewrite H7; reflexivity.
  - clear comp H_comp.
    unfold compare in *.
    pose proof compare_compose_lt x1 x2 y1 y2 _ H12 as H_useful.
    pose proof compare_compose_lt x2 x3 y2 y3 _ H23 as H_useful'.
    destruct H_useful as [left | right];
    destruct H_useful' as [left' | right'].
    * assert (Hc: compare x1 x3 = Gt) by (eapply compare_transitive; eauto).
      unfold compare_compose.
      rewrite Hc; reflexivity.
    * destruct right'; subst.
      simpl; rewrite left; reflexivity.
    * destruct right; subst.
      simpl; rewrite left'; reflexivity.
    * subst.
      destruct right.
      destruct right'.
      assert (compare y1 y3 = Gt) by (eapply compare_transitive; eauto).
      unfold compare_compose.
      rewrite H3.
      rewrite H5.
      rewrite compare_eq_refl.
      rewrite H7; reflexivity.
Qed.

Instance compare_strict_order_compose `{CompareStrictOrder X} `{CompareStrictOrder Y} :
  CompareStrictOrder (X*Y) (compare_compose X Y compare compare).
Proof.
  split; typeclasses eauto.
Qed.

(* Now we can have the following for free : *)
Instance ComposeStrictlyComparable `{StrictlyComparable X} `{StrictlyComparable Y} :
  StrictlyComparable (X*Y) (compare_compose X Y compare compare).
Proof.
constructor; typeclasses eauto.
Qed.

Instance TripleStrictlyComparable
  `{StrictlyComparable X} `{StrictlyComparable Y} `{StrictlyComparable Z} :
  StrictlyComparable (X*Y*Z) (compare_compose (X*Y) Z (compare_compose X Y compare compare) compare).
Proof.
  apply ComposeStrictlyComparable.
Qed.

Instance triple_strictly_comparable_proj1_inhabited `{StrictlyComparable (X * Y * Z)} : Inhabited X.
Proof.
  destruct H0 as [((x,y),z)]; constructor.
  exact x.
Defined.

Instance triple_strictly_comparable_proj1_compare
 `{StrictlyComparable (X * Y * Z)} : Comparison X.
Proof.
intros x1 x2.
destruct H0 as [((x,y),z)].
exact (compare (x1, y, z) (x2, y, z)).
Defined.

Instance triple_strictly_comparable_proj1_strictorder `{StrictlyComparable (X * Y * Z)} :
  CompareStrictOrder X triple_strictly_comparable_proj1_compare.
Proof.
  split.
  - intros x y.
    unfold compare, triple_strictly_comparable_proj1_compare.
    destruct H0 as [((x0,y0),z0)].
    split; intro.
    + apply compare_eq in H0.
      inversion H0; reflexivity.
    + subst. apply CompareStrictOrder_Reflexive. reflexivity.
  - intros x1 x2 x3 cmp.
    unfold compare, triple_strictly_comparable_proj1_compare.
    destruct H0 as [((x0,y0),z0)].
    apply compare_transitive.
Qed.

Program Instance triple_strictly_comparable_proj1
  `{StrictlyComparable (X * Y * Z)}
  : @StrictlyComparable X triple_strictly_comparable_proj1_compare triple_strictly_comparable_proj1_inhabited.

Instance triple_strictly_comparable_proj2_inhabited
  {X Y Z} `{StrictlyComparable (X * Y * Z)}
  : Inhabited Y.
Proof.
  destruct H0 as [((x,y),z)]; constructor.
  exact y.
Defined.

Instance triple_strictly_comparable_proj2_compare
 `{StrictlyComparable (X * Y * Z)} : Comparison Y.
Proof.
intros y1 y2.
destruct H0 as [((x,y),z)].
exact (compare (x, y1, z) (x, y2, z)).
Defined.

Instance triple_strictly_comparable_proj2_strictorder
   `{StrictlyComparable (X * Y * Z)} :
  CompareStrictOrder Y triple_strictly_comparable_proj2_compare.
Proof.
  split.
  - intros x y.
    unfold compare, triple_strictly_comparable_proj2_compare.
    destruct H0 as [((x0,y0),z0)].
    split; intro.
    + apply compare_eq in H0.
      inversion H0; reflexivity.
    + subst. apply compare_eq. reflexivity.
  - intros x1 x2 x3 cmp.
    unfold compare, triple_strictly_comparable_proj2_compare.
    destruct H0 as [((x0,y0),z0)].
    apply compare_transitive.
Qed.

Program Instance triple_strictly_comparable_proj2
  `{StrictlyComparable (X * Y * Z)}
  : @StrictlyComparable Y triple_strictly_comparable_proj2_compare triple_strictly_comparable_proj2_inhabited.

Instance triple_strictly_comparable_proj3_inhabited
  `{StrictlyComparable (X * Y * Z)}
  : Inhabited Z.
Proof.
  destruct H0 as [((x,y),z)]; constructor.
  exact z.
Defined.

Instance triple_strictly_comparable_proj3_compare
 `{StrictlyComparable (X * Y * Z)} : Comparison Z.
Proof.
intros z1 z2.
destruct H0 as [((x,y),z)].
exact (compare (x, y, z1) (x, y, z2)).
Defined.

Instance triple_strictly_comparable_proj3_strictorder
   `{StrictlyComparable (X * Y * Z)} :
  CompareStrictOrder Z triple_strictly_comparable_proj3_compare.
Proof.
  split.
  - intros x y.
    unfold compare, triple_strictly_comparable_proj3_compare.
    destruct H0 as [((x0,y0),z0)].
    split; intro.
    + apply compare_eq in H0.
      inversion H0; reflexivity.
    + subst. apply compare_eq. reflexivity.
  - intros x1 x2 x3 cmp.
    unfold compare, triple_strictly_comparable_proj3_compare.
    destruct H0 as [((x0,y0),z0)].
    apply compare_transitive.
Qed.

Program Instance triple_strictly_comparable_proj3
  `{StrictlyComparable (X * Y * Z)}
  : @StrictlyComparable Z triple_strictly_comparable_proj3_compare triple_strictly_comparable_proj3_inhabited.

Definition bounding (P : nat -> Prop)
  :=  {n1 : nat | forall (n2 : nat), n1 <= n2 -> ~P n2}.

Definition liveness (P : nat -> Prop)
  := forall (n1 : nat), { n2 : nat | n1 <= n2 /\ P n2}.

Definition liveness_dec (P : nat -> Prop)
  := forall (n1 : nat), { n2 : nat | n1 <= n2 /\ P n2} + {~exists n2:nat, n1 <= n2 /\ P n2}.

Definition min_liveness (P : nat -> Prop)
  := forall (n1 : nat), { n2 : nat | n1 <= n2 /\ P n2
               /\ forall (n3 : nat), n2 <= n3 /\ P n3 -> n2 <= n3}.

Lemma not_bounding_impl_liveness
  (P : nat -> Prop)
  (Hdec : liveness_dec P)
  (Hnbound : ~exists n1:nat, forall (n2:nat), n1 <= n2 -> ~P n2)
  : liveness P.
Proof.
  intros n1.
  specialize (Hdec n1).
  destruct Hdec as [Hex | Hnex]; try assumption.
  specialize (not_ex_all_not _ Hnbound); simpl; clear Hnbound; intro Hnbound.
  specialize (Hnbound n1).
  elim Hnbound.
  intros n2 Hleq HnP.
  apply Hnex.
  exists n2.
  split; assumption.
Qed.

(** optionally extracts an element belonging to first type from a sum type *)
Definition sum_project_left
  {A B : Type}
  (x : A + B)
  : option A
  :=
  match x with
  | inl a => Some a
  | inr _ => None
  end.

(** optionally extracts an element belonging to second type from a sum type *)
Definition sum_project_right
  {A B : Type}
  (x : A + B)
  : option B
  :=
  match x with
  | inl _ => None
  | inr b => Some b
  end.
