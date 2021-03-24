From Coq Require Import Relation_Definitions Morphisms RelationClasses List Bool Peano.
Import ListNotations.
From Coq.Program Require Import Basics Syntax.

Global Generalizable All Variables.

(** * General typeclasses *)

(** This typeclass hierarchy has been adapted mainly from the
#<a href="https://gitlab.mpi-sws.org/iris/stdpp">stdpp</a># library. *)

Instance: forall A, PreOrder (@eq A).
Proof. split; repeat intro; congruence. Qed.

(** ** Top-level classes *)

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

Lemma Decision_iff : forall {P Q}, (P <-> Q) -> Decision P -> Decision Q.
Proof. firstorder. Qed.
Lemma Decision_and : forall {P Q}, Decision P -> Decision Q -> Decision (P /\ Q).
Proof. firstorder. Qed.
Lemma Decision_or : forall {P Q}, Decision P -> Decision Q -> Decision (P \/ Q).
Proof. firstorder. Qed.
Lemma Decision_not : forall {P}, Decision P -> Decision (~P).
Proof. firstorder. Qed.

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

(** ** Boolean coercion *)

Coercion Is_true : bool >-> Sortclass.
Hint Unfold Is_true : core.
Hint Immediate Is_true_eq_left : core.
Hint Resolve orb_prop_intro andb_prop_intro : core.
Lemma Is_true_iff_eq_true: forall x: bool, x = true <-> x.
Proof.
  split. apply Is_true_eq_left. apply Is_true_eq_true.
Qed.

Instance bool_decision {b:bool} : Decision b :=
  match b return {b}+{~b} with
          | true => left I
          | false => right (fun H => H)
  end.

(** ** Basic instances *)

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

Instance option_inhabited {A} : Inhabited (option A) := populate None.

Lemma dec_stable `{Decision P} : ~~P -> P.
Proof. firstorder. Qed.

Lemma Is_true_reflect (b : bool) : reflect b b.
Proof. destruct b; [left; constructor | right; intros []]. Qed.
Instance: Inj eq iff Is_true.
Proof. intros [] []; simpl; intuition. Qed.

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

Lemma bool_decide_spec (P : Prop) {dec : Decision P} : bool_decide P <-> P.
Proof. unfold bool_decide. destruct dec; simpl; tauto. Qed.
Lemma bool_decide_unpack (P : Prop) {dec : Decision P} : bool_decide P -> P.
Proof. rewrite bool_decide_spec; trivial. Qed.
Lemma bool_decide_pack (P : Prop) {dec : Decision P} : P -> bool_decide P.
Proof. rewrite bool_decide_spec; trivial. Qed.

Lemma bool_decide_eq_true (P : Prop) `{Decision P} : bool_decide P = true <-> P.
Proof. unfold bool_decide; destruct H; intuition discriminate. Qed.
Lemma bool_decide_eq_false (P : Prop) `{Decision P} : bool_decide P = false <-> ~P.
Proof. unfold bool_decide; destruct H; intuition discriminate. Qed.
Lemma bool_decide_iff (P Q : Prop) `{Decision P, Decision Q} :
  (P <-> Q) -> bool_decide P = bool_decide Q.
Proof. unfold bool_decide; destruct H; destruct H0; tauto. Qed.

Lemma bool_decide_eq_true_1 P `{!Decision P}: bool_decide P = true -> P.
Proof. apply bool_decide_eq_true. Qed.
Lemma bool_decide_eq_true_2 P `{!Decision P}: P -> bool_decide P = true.
Proof. apply bool_decide_eq_true. Qed.

Lemma bool_decide_eq_false_1 P `{!Decision P}: bool_decide P = false -> ~P.
Proof. apply bool_decide_eq_false. Qed.
Lemma bool_decide_eq_false_2 P `{!Decision P}: ~P -> bool_decide P = false.
Proof. apply bool_decide_eq_false. Qed.

Lemma bool_decide_eq_true_proof_irrelevance
  `{!Decision P}
  (p q : bool_decide P = true)
  : p = q.
Proof.
  apply Eqdep_dec.UIP_dec.
  apply Bool.bool_dec.
Qed.

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

(* Some relation facts *)
Lemma Reflexive_reexpress_impl {A} (R S: Relation_Definitions.relation A):
  relation_equivalence R S -> Reflexive R -> Reflexive S.
Proof.
  clear;firstorder.
Qed.
Lemma complement_equivalence {A}:
  Morphisms.Proper (Morphisms.respectful relation_equivalence relation_equivalence) (@complement A).
Proof.
  clear;firstorder.
Qed.
Lemma Transitive_reexpress_impl {A} (R S: Relation_Definitions.relation A):
  relation_equivalence R S -> Transitive R -> Transitive S.
Proof.
  clear.
  unfold relation_equivalence, predicate_equivalence; simpl.
  intros Hrel HtransR x y z.
  rewrite <- !Hrel.
  apply HtransR.
Qed.
Lemma StrictOrder_reexpress_impl {A} (R S: Relation_Definitions.relation A):
  relation_equivalence R S -> StrictOrder R -> StrictOrder S.
Proof.
  clear.
  intros Hrel [Hirr Htrans]. constructor.
  revert Hirr;apply Reflexive_reexpress_impl. apply complement_equivalence. assumption.
  revert Htrans;apply Transitive_reexpress_impl. assumption.
Qed.

Definition dec_sig {A} (P : A -> Prop) {P_dec : forall x, Decision (P x)} : Type
  := sig (fun a => bool_decide (P a) = true).

Definition dec_exist {A} (P : A -> Prop) {P_dec : forall x, Decision (P x)}
  (a : A) (p : P a) : dec_sig P
  := exist _ a (decide_True true false p).

Definition dec_proj1_sig
  `{P_dec : forall x : A, Decision (P x)}
  (ap : dec_sig P) : A
  := proj1_sig ap.

Lemma dec_proj2_sig
  `{P_dec : forall x: A, Decision (P x)}
  (ap : dec_sig P) : P (dec_proj1_sig ap).
Proof.
  destruct ap;simpl.
  apply bool_decide_eq_true in e.
  assumption.
Qed.

Lemma dec_sig_eq_iff
  `{P_dec : forall x: A, Decision (P x)}
  (xp yp : dec_sig P)
  : xp = yp <-> dec_proj1_sig xp = dec_proj1_sig yp.
Proof.
  apply eq_sig_hprop_iff.
  intro x.
  apply bool_decide_eq_true_proof_irrelevance.
Qed.

(** destructs a dec_sig element into a dec_exist construct
*)

Lemma dec_sig_to_exist {A} P {P_dec: forall (x:A), Decision (P x)}
            (a: dec_sig P): exists a' (e: P a'), a = dec_exist _ a' e.
Proof.
  destruct a as (x,e).
  exists x, (bool_decide_eq_true_1 _ e).
  apply dec_sig_eq_iff.
  reflexivity.
Qed.

Ltac destruct_dec_sig  a a' e H :=
  match type of a with dec_sig ?P =>
  pose proof (dec_sig_to_exist P a) as [a' [e H]]
  end.

Lemma dec_sig_eq_dec
  `{P_dec : forall x: A, Decision (P x)}
  (EqDecA : EqDecision A)
  : EqDecision (dec_sig P).
Proof.
  intros x y.
  apply (Decision_iff (iff_sym (dec_sig_eq_iff _ _))).
  apply EqDecA.
Qed.

Lemma dec_sig_sigT_eq
  {A} (P : A -> Prop) {P_dec : forall x, Decision (P x)}
  (F : A -> Type)
  (a : A)
  (b1 b2 : F a)
  (e1 e2 : P a)
  (pa1 := dec_exist _ a e1)
  (pa2 := dec_exist _ a e2)
  (Heqb : b1 = b2)
  : existT (fun pa : dec_sig P => F (proj1_sig pa)) pa1 b1
  = existT (fun pa : dec_sig P => F (proj1_sig pa)) pa2 b2.
Proof.
  subst b2 pa1 pa2.
  unfold dec_exist.
  replace (decide_True true false e1) with (decide_True true false e2)
  ; [reflexivity|].
  apply bool_decide_eq_true_proof_irrelevance.
Qed.

Lemma ex_out (A : Type) (P : Prop) (Q : A -> Prop):
  (exists x, P /\ Q x) <-> (P /\ exists x, Q x).
Proof. firstorder. Qed.
