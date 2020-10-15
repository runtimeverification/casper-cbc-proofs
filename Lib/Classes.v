From Coq Require Import Relation_Definitions Morphisms RelationClasses List Bool Peano.
Import ListNotations.
From Coq.Program Require Import Basics Syntax.

Global Generalizable All Variables.

(** * General typeclasses *)

(** This typeclass hierarchy has been adapted mainly from the
#<a href="https://gitlab.mpi-sws.org/iris/stdpp">stdpp</a># library. *)

Instance: forall A, PreOrder (@eq A).
Proof. split; repeat intro; congruence. Qed.

Class Decision (P : Prop) := decide : {P} + {~P}.
Hint Mode Decision ! : typeclass_instances.
Arguments decide _ {_} : simpl never, assert.

Class RelDecision {A B} (R : A -> B -> Prop) :=
  decide_rel x y :> Decision (R x y).
Hint Mode RelDecision ! ! ! : typeclass_instances.
Arguments decide_rel {_ _} _ {_} _ _ : simpl never, assert.
Notation EqDecision A := (RelDecision (@eq A)).
Notation decide_eq := (fun x y => decide (x = y)).

Class Inhabited (A : Type) : Type := populate { inhabitant : A }.
Hint Mode Inhabited ! : typeclass_instances.
Arguments populate {_} _ : assert.

Class Inj {A B} (R : relation A) (S : relation B) (f : A -> B) : Prop :=
  inj x y : S (f x) (f y) -> R x y.
Class Inj2 {A B C} (R1 : relation A) (R2 : relation B)
    (S : relation C) (f : A -> B -> C) : Prop :=
  inj2 x1 x2 y1 y2 : S (f x1 x2) (f y1 y2) -> R1 x1 y1 /\ R2 x2 y2.
Class Cancel {A B} (S : relation B) (f : A -> B) (g : B -> A) : Prop :=
  cancel : forall x, S (f (g x)) x.
Class Surj {A B} (R : relation B) (f : A -> B) :=
  surj y : exists x, R (f x) y.
Class IdemP {A} (R : relation A) (f : A -> A -> A) : Prop :=
  idemp x : R (f x x) x.
Class Comm {A B} (R : relation A) (f : B -> B -> A) : Prop :=
  comm x y : R (f x y) (f y x).
Class LeftId {A} (R : relation A) (i : A) (f : A -> A -> A) : Prop :=
  left_id x : R (f i x) x.
Class RightId {A} (R : relation A) (i : A) (f : A -> A -> A) : Prop :=
  right_id x : R (f x i) x.
Class Assoc {A} (R : relation A) (f : A -> A -> A) : Prop :=
  assoc x y z : R (f x (f y z)) (f (f x y) z).
Class LeftAbsorb {A} (R : relation A) (i : A) (f : A -> A -> A) : Prop :=
  left_absorb x : R (f i x) i.
Class RightAbsorb {A} (R : relation A) (i : A) (f : A -> A -> A) : Prop :=
  right_absorb x : R (f x i) i.
Class AntiSymm {A} (R S : relation A) : Prop :=
  anti_symm x y : S x y -> S y x -> R x y.
Class Total {A} (R : relation A) := total x y : R x y \/ R y x.
Class Trichotomy {A} (R : relation A) :=
  trichotomy x y : R x y \/ x = y \/ R y x.
Class TrichotomyT {A} (R : relation A) :=
  trichotomyT x y : {R x y} + {x = y} + {R y x}.

Notation Involutive R f := (Cancel R f f).
Lemma involutive {A} {R : relation A} (f : A -> A) `{Involutive R f} x :
  R (f (f x)) x.
Proof. auto. Qed.

Arguments irreflexivity {_} _ {_} _ _ : assert.
Arguments inj {_ _ _ _} _ {_} _ _ _ : assert.
Arguments inj2 {_ _ _ _ _ _} _ {_} _ _ _ _ _: assert.
Arguments cancel {_ _ _} _ _ {_} _ : assert.
Arguments surj {_ _ _} _ {_} _ : assert.
Arguments idemp {_ _} _ {_} _ : assert.
Arguments comm {_ _ _} _ {_} _ _ : assert.
Arguments left_id {_ _} _ _ {_} _ : assert.
Arguments right_id {_ _} _ _ {_} _ : assert.
Arguments assoc {_ _} _ {_} _ _ _ : assert.
Arguments left_absorb {_ _} _ _ {_} _ : assert.
Arguments right_absorb {_ _} _ _ {_} _ : assert.
Arguments anti_symm {_ _} _ {_} _ _ _ _ : assert.
Arguments total {_} _ {_} _ _ : assert.
Arguments trichotomy {_} _ {_} _ _ : assert.
Arguments trichotomyT {_} _ {_} _ _ : assert.

Lemma not_symmetry `{R : relation A, !Symmetric R} x y : ~R x y -> ~R y x.
Proof. intuition. Qed.
Lemma symmetry_iff `(R : relation A) `{!Symmetric R} x y : R x y <-> R y x.
Proof. intuition. Qed.

Lemma not_inj `{Inj A B R R' f} x y : ~R x y -> ~R' (f x) (f y).
Proof. intuition. Qed.
Lemma not_inj2_1 `{Inj2 A B C R R' R'' f} x1 x2 y1 y2 :
  ~R x1 x2 -> ~R'' (f x1 y1) (f x2 y2).
Proof. intros HR HR''. destruct (inj2 f x1 y1 x2 y2); auto. Qed.
Lemma not_inj2_2 `{Inj2 A B C R R' R'' f} x1 x2 y1 y2 :
  ~R' y1 y2 -> ~R'' (f x1 y1) (f x2 y2).
Proof. intros HR' HR''. destruct (inj2 f x1 y1 x2 y2); auto. Qed.

Lemma inj_iff {A B} {R : relation A} {S : relation B} (f : A -> B)
  `{!Inj R S f} `{!Proper (R ==> S) f} x y : S (f x) (f y) <-> R x y.
Proof. firstorder. Qed.
Instance inj2_inj_1 `{Inj2 A B C R1 R2 R3 f} y : Inj R1 R3 (fun x => f x y).
Proof. repeat intro; edestruct (inj2 f); eauto. Qed.
Instance inj2_inj_2 `{Inj2 A B C R1 R2 R3 f} x : Inj R2 R3 (f x).
Proof. repeat intro; edestruct (inj2 f); eauto. Qed.

Lemma cancel_inj `{Cancel A B R1 f g, !Equivalence R1, !Proper (R2 ==> R1) f} :
  Inj R1 R2 g.
Proof.
  intros x y E. rewrite <-(cancel f g x), <-(cancel f g y), E. reflexivity.
Qed.
Lemma cancel_surj `{Cancel A B R1 f g} : Surj R1 f.
Proof. intros y. exists (g y). auto. Qed.

Lemma idemp_L {A} f `{!@IdemP A eq f} x : f x x = x.
Proof. auto. Qed.
Lemma comm_L {A B} f `{!@Comm A B eq f} x y : f x y = f y x.
Proof. auto. Qed.
Lemma left_id_L {A} i f `{!@LeftId A eq i f} x : f i x = x.
Proof. auto. Qed.
Lemma right_id_L {A} i f `{!@RightId A eq i f} x : f x i = x.
Proof. auto. Qed.
Lemma assoc_L {A} f `{!@Assoc A eq f} x y z : f x (f y z) = f (f x y) z.
Proof. auto. Qed.
Lemma left_absorb_L {A} i f `{!@LeftAbsorb A eq i f} x : f i x = i.
Proof. auto. Qed.
Lemma right_absorb_L {A} i f `{!@RightAbsorb A eq i f} x : f x i = i.
Proof. auto. Qed.

Definition strict {A} (R : relation A) : relation A := fun X Y => R X Y /\ ~R Y X.
Instance: Params (@strict) 2 := {}.
Class PartialOrder {A} (R : relation A) : Prop := {
  partial_order_pre :> PreOrder R;
  partial_order_anti_symm :> AntiSymm eq R
}.
Class TotalOrder {A} (R : relation A) : Prop := {
  total_order_partial :> PartialOrder R;
  total_order_trichotomy :> Trichotomy (strict R)
}.

Instance prop_inhabited : Inhabited Prop := populate True.
Instance list_inhabited {A} : Inhabited (list A) := populate [].
Instance bool_inhabited : Inhabited bool := populate true.
Instance unit_inhabited: Inhabited unit := populate ().

Instance: Params (@pair) 2 := {}.
Instance: Params (@fst) 2 := {}.
Instance: Params (@snd) 2 := {}.

Instance prod_inhabited {A B} (iA : Inhabited A)
    (iB : Inhabited B) : Inhabited (A * B) :=
  match iA, iB with populate x, populate y => populate (x,y) end.

Instance pair_inj : Inj2 eq eq eq (@pair A B).
Proof. injection 1; auto. Qed.

Definition prod_relation {A B} (R1 : relation A) (R2 : relation B) :
  relation (A * B) := fun x y => R1 (fst x) (fst y) /\ R2 (snd x) (snd y).

Section prod_relation.
  Context `{R1 : relation A, R2 : relation B}.
  Global Instance prod_relation_refl :
    Reflexive R1 -> Reflexive R2 -> Reflexive (prod_relation R1 R2).
  Proof. firstorder eauto. Qed.
  Global Instance prod_relation_sym :
    Symmetric R1 -> Symmetric R2 -> Symmetric (prod_relation R1 R2).
  Proof. firstorder eauto. Qed.
  Global Instance prod_relation_trans :
    Transitive R1 -> Transitive R2 -> Transitive (prod_relation R1 R2).
  Proof. firstorder eauto. Qed.
  Global Instance prod_relation_equiv :
    Equivalence R1 -> Equivalence R2 -> Equivalence (prod_relation R1 R2).
  Proof. split; apply _. Qed.

  Global Instance pair_proper' : Proper (R1 ==> R2 ==> prod_relation R1 R2) pair.
  Proof. firstorder eauto. Qed.
  Global Instance pair_inj' : Inj2 R1 R2 (prod_relation R1 R2) pair.
  Proof. inversion_clear 1; eauto. Qed.
  Global Instance fst_proper' : Proper (prod_relation R1 R2 ==> R1) fst.
  Proof. firstorder eauto. Qed.
  Global Instance snd_proper' : Proper (prod_relation R1 R2 ==> R2) snd.
  Proof. firstorder eauto. Qed.
End prod_relation.

Instance option_inhabited {A} : Inhabited (option A) := populate None.

Lemma dec_stable `{Decision P} : ~~P -> P.
Proof. firstorder. Qed.

Lemma decide_True {A} `{Decision P} (x y : A) :
  P -> (if decide P then x else y) = x.
Proof. destruct (decide P); tauto. Qed.

Lemma decide_False {A} `{Decision P} (x y : A) :
  ~P -> (if decide P then x else y) = y.
Proof. destruct (decide P); tauto. Qed.

Lemma decide_iff {A} P Q `{Decision P, Decision Q} (x y : A) :
  (P <-> Q) -> (if decide P then x else y) = (if decide Q then x else y).
Proof. intros [??]. destruct (decide P), (decide Q); tauto. Qed.

Definition bool_decide (P : Prop) {dec : Decision P} : bool :=
  if dec then true else false.

Ltac solve_trivial_decision :=
  match goal with
  | |- Decision (?P) => apply _
  | |- sumbool ?P (~?P) => change (Decision P); apply _
  end.
Ltac solve_decision :=
  unfold EqDecision; intros; first
    [ solve_trivial_decision
    | unfold Decision; decide equality; solve_trivial_decision ].

Lemma bool_decide_reflect P `{dec : Decision P} : reflect P (bool_decide P).
Proof. unfold bool_decide. destruct dec; [left|right]; assumption. Qed.

Lemma bool_decide_decide P `{!Decision P} :
  bool_decide P = if decide P then true else false.
Proof. reflexivity. Qed.
Lemma decide_bool_decide P {Hdec: Decision P} {X : Type} (x1 x2 : X):
  (if decide P then x1 else x2) = (if bool_decide P then x1 else x2).
Proof. unfold bool_decide, decide. destruct Hdec; reflexivity. Qed.

Instance comparison_eq_dec : EqDecision comparison.
Proof. solve_decision. Defined.

Instance option_eq_dec `{dec : EqDecision A} : EqDecision (option A).
Proof.
 refine (fun mx my =>
  match mx, my with
  | Some x, Some y => if (decide (x = y)) then left _ else right _
  | None, None => left _ | _, _ => right _
  end); clear dec; abstract congruence.
Defined.

Instance bool_eq_dec : EqDecision bool.
Proof. solve_decision. Defined.

Instance unit_eq_dec : EqDecision unit.
Proof. solve_decision. Defined.

Instance Empty_set_eq_dec : EqDecision Empty_set.
Proof. solve_decision. Defined.

Instance prod_eq_dec `{EqDecision A, EqDecision B} : EqDecision (A * B).
Proof. solve_decision. Defined.

Instance sum_eq_dec `{EqDecision A, EqDecision B} : EqDecision (A + B).
Proof. solve_decision. Defined.
