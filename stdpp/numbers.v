(** This file collects some trivial facts on the Coq types [nat] and [N] for
natural numbers, and the type [Z] for integers. It also declares some useful
notations. *)
From Coq Require Export EqdepFacts PArith NArith ZArith NPeano.
From Coq Require Import QArith Qcanon.
From stdpp Require Export base decidable option.
Set Default Proof Using "Type".
Local Open Scope nat_scope.

Coercion Z.of_nat : nat >-> Z.
Instance comparison_eq_dec : EqDecision comparison.
Proof. solve_decision. Defined.

(** * Notations and properties of [nat] *)
Arguments minus !_ !_ / : assert.
Arguments Nat.max : simpl nomatch.

Typeclasses Opaque lt.

Reserved Notation "x ≤ y ≤ z" (at level 70, y at next level).
Reserved Notation "x ≤ y < z" (at level 70, y at next level).
Reserved Notation "x < y < z" (at level 70, y at next level).
Reserved Notation "x < y ≤ z" (at level 70, y at next level).
Reserved Notation "x ≤ y ≤ z ≤ z'"
  (at level 70, y at next level, z at next level).

Infix "≤" := le : nat_scope.
Notation "x ≤ y ≤ z" := (x ≤ y ∧ y ≤ z)%nat : nat_scope.
Notation "x ≤ y < z" := (x ≤ y ∧ y < z)%nat : nat_scope.
Notation "x < y ≤ z" := (x < y ∧ y ≤ z)%nat : nat_scope.
Notation "x ≤ y ≤ z ≤ z'" := (x ≤ y ∧ y ≤ z ∧ z ≤ z')%nat : nat_scope.
Notation "(≤)" := le (only parsing) : nat_scope.
Notation "(<)" := lt (only parsing) : nat_scope.

Infix "`div`" := Nat.div (at level 35) : nat_scope.
Infix "`mod`" := Nat.modulo (at level 35) : nat_scope.
Infix "`max`" := Nat.max (at level 35) : nat_scope.
Infix "`min`" := Nat.min (at level 35) : nat_scope.

Instance nat_eq_dec: EqDecision nat := eq_nat_dec.
Instance nat_le_dec: RelDecision le := le_dec.
Instance nat_lt_dec: RelDecision lt := lt_dec.
Instance nat_inhabited: Inhabited nat := populate 0%nat.
Instance S_inj: Inj (=) (=) S.
Proof. by injection 1. Qed.
Instance nat_le_po: PartialOrder (≤).
Proof. repeat split; repeat intro; auto with lia. Qed.
Instance nat_le_total: Total (≤).
Proof. repeat intro; lia. Qed.

Instance nat_le_pi: ∀ x y : nat, ProofIrrel (x ≤ y).
Proof.
  assert (∀ x y (p : x ≤ y) y' (q : x ≤ y'),
    y = y' → eq_dep nat (le x) y p y' q) as aux.
  { fix FIX 3. intros x ? [|y p] ? [|y' q].
    - done.
    - clear FIX. intros; exfalso; auto with lia.
    - clear FIX. intros; exfalso; auto with lia.
    - injection 1. intros Hy. by case (FIX x y p y' q Hy). }
  intros x y p q.
  by apply (Eqdep_dec.eq_dep_eq_dec (λ x y, decide (x = y))), aux.
Qed.
Instance nat_lt_pi: ∀ x y : nat, ProofIrrel (x < y).
Proof. unfold lt. apply _. Qed.

Lemma nat_le_sum (x y : nat) : x ≤ y ↔ ∃ z, y = x + z.
Proof. split. exists (y - x); lia. intros [z ->]; lia. Qed.

Lemma Nat_lt_succ_succ n : n < S (S n).
Proof. auto with arith. Qed.
Lemma Nat_mul_split_l n x1 x2 y1 y2 :
  x2 < n → y2 < n → x1 * n + x2 = y1 * n + y2 → x1 = y1 ∧ x2 = y2.
Proof.
  intros Hx2 Hy2 E. cut (x1 = y1); [intros; subst;lia |].
  revert y1 E. induction x1; simpl; intros [|?]; simpl; auto with lia.
Qed.
Lemma Nat_mul_split_r n x1 x2 y1 y2 :
  x1 < n → y1 < n → x1 + x2 * n = y1 + y2 * n → x1 = y1 ∧ x2 = y2.
Proof. intros. destruct (Nat_mul_split_l n x2 x1 y2 y1); auto with lia. Qed.

Notation lcm := Nat.lcm.
Notation divide := Nat.divide.
Notation "( x | y )" := (divide x y) : nat_scope.
Instance Nat_divide_dec : RelDecision Nat.divide.
Proof.
  refine (λ x y, cast_if (decide (lcm x y = y))); by rewrite Nat.divide_lcm_iff.
Defined.
Instance: PartialOrder divide.
Proof.
  repeat split; try apply _. intros ??. apply Nat.divide_antisym_nonneg; lia.
Qed.
Hint Extern 0 (_ | _) => reflexivity : core.
Lemma Nat_divide_ne_0 x y : (x | y) → y ≠ 0 → x ≠ 0.
Proof. intros Hxy Hy ->. by apply Hy, Nat.divide_0_l. Qed.

Lemma Nat_iter_S {A} n (f: A → A) x : Nat.iter (S n) f x = f (Nat.iter n f x).
Proof. done. Qed.
Lemma Nat_iter_S_r {A} n (f: A → A) x : Nat.iter (S n) f x = Nat.iter n f (f x).
Proof. induction n; by f_equal/=. Qed.
Lemma Nat_iter_add {A} n1 n2 (f : A → A) x :
  Nat.iter (n1 + n2) f x = Nat.iter n1 f (Nat.iter n2 f x).
Proof. induction n1; by f_equal/=. Qed.

Lemma Nat_iter_ind {A} (P : A → Prop) f x k :
  P x → (∀ y, P y → P (f y)) → P (Nat.iter k f x).
Proof. induction k; simpl; auto. Qed.


(** * Notations and properties of [positive] *)
Local Open Scope positive_scope.

Typeclasses Opaque Pos.le.
Typeclasses Opaque Pos.lt.

Infix "≤" := Pos.le : positive_scope.
Notation "x ≤ y ≤ z" := (x ≤ y ∧ y ≤ z) : positive_scope.
Notation "x ≤ y < z" := (x ≤ y ∧ y < z) : positive_scope.
Notation "x < y ≤ z" := (x < y ∧ y ≤ z) : positive_scope.
Notation "x ≤ y ≤ z ≤ z'" := (x ≤ y ∧ y ≤ z ∧ z ≤ z') : positive_scope.
Notation "(≤)" := Pos.le (only parsing) : positive_scope.
Notation "(<)" := Pos.lt (only parsing) : positive_scope.
Notation "(~0)" := xO (only parsing) : positive_scope.
Notation "(~1)" := xI (only parsing) : positive_scope.

Arguments Pos.of_nat : simpl never.
Arguments Pmult : simpl never.

Instance positive_eq_dec: EqDecision positive := Pos.eq_dec.
Instance positive_le_dec: RelDecision Pos.le.
Proof. refine (λ x y, decide ((x ?= y) ≠ Gt)). Defined.
Instance positive_lt_dec: RelDecision Pos.lt.
Proof. refine (λ x y, decide ((x ?= y) = Lt)). Defined.
Instance positive_le_total: Total Pos.le.
Proof. repeat intro; lia. Qed.

Instance positive_inhabited: Inhabited positive := populate 1.

Instance maybe_xO : Maybe xO := λ p, match p with p~0 => Some p | _ => None end.
Instance maybe_xI : Maybe xI := λ p, match p with p~1 => Some p | _ => None end.
Instance xO_inj : Inj (=) (=) (~0).
Proof. by injection 1. Qed.
Instance xI_inj : Inj (=) (=) (~1).
Proof. by injection 1. Qed.

(** Since [positive] represents lists of bits, we define list operations
on it. These operations are in reverse, as positives are treated as snoc
lists instead of cons lists. *)
Fixpoint Papp (p1 p2 : positive) : positive :=
  match p2 with
  | 1 => p1
  | p2~0 => (Papp p1 p2)~0
  | p2~1 => (Papp p1 p2)~1
  end.
Infix "++" := Papp : positive_scope.
Notation "(++)" := Papp (only parsing) : positive_scope.
Notation "( p ++.)" := (Papp p) (only parsing) : positive_scope.
Notation "(.++ q )" := (λ p, Papp p q) (only parsing) : positive_scope.

Fixpoint Preverse_go (p1 p2 : positive) : positive :=
  match p2 with
  | 1 => p1
  | p2~0 => Preverse_go (p1~0) p2
  | p2~1 => Preverse_go (p1~1) p2
  end.
Definition Preverse : positive → positive := Preverse_go 1.

Global Instance Papp_1_l : LeftId (=) 1 (++).
Proof. intros p. by induction p; intros; f_equal/=. Qed.
Global Instance Papp_1_r : RightId (=) 1 (++).
Proof. done. Qed.
Global Instance Papp_assoc : Assoc (=) (++).
Proof. intros ?? p. by induction p; intros; f_equal/=. Qed.
Global Instance Papp_inj p : Inj (=) (=) (.++ p).
Proof. intros ???. induction p; simplify_eq; auto. Qed.

Lemma Preverse_go_app p1 p2 p3 :
  Preverse_go p1 (p2 ++ p3) = Preverse_go p1 p3 ++ Preverse_go 1 p2.
Proof.
  revert p3 p1 p2.
  cut (∀ p1 p2 p3, Preverse_go (p2 ++ p3) p1 = p2 ++ Preverse_go p3 p1).
  { by intros go p3; induction p3; intros p1 p2; simpl; auto; rewrite <-?go. }
  intros p1; induction p1 as [p1 IH|p1 IH|]; intros p2 p3; simpl; auto.
  - apply (IH _ (_~1)).
  - apply (IH _ (_~0)).
Qed.
Lemma Preverse_app p1 p2 : Preverse (p1 ++ p2) = Preverse p2 ++ Preverse p1.
Proof. unfold Preverse. by rewrite Preverse_go_app. Qed.
Lemma Preverse_xO p : Preverse (p~0) = (1~0) ++ Preverse p.
Proof Preverse_app p (1~0).
Lemma Preverse_xI p : Preverse (p~1) = (1~1) ++ Preverse p.
Proof Preverse_app p (1~1).

Lemma Preverse_involutive p :
  Preverse (Preverse p) = p.
Proof.
  induction p as [p IH|p IH|]; simpl.
  - by rewrite Preverse_xI, Preverse_app, IH.
  - by rewrite Preverse_xO, Preverse_app, IH.
  - reflexivity.
Qed.

Instance Preverse_inj : Inj (=) (=) Preverse.
Proof.
  intros p q eq.
  rewrite <- (Preverse_involutive p).
  rewrite <- (Preverse_involutive q).
  by rewrite eq.
Qed.

Fixpoint Plength (p : positive) : nat :=
  match p with 1 => 0%nat | p~0 | p~1 => S (Plength p) end.
Lemma Papp_length p1 p2 : Plength (p1 ++ p2) = (Plength p2 + Plength p1)%nat.
Proof. by induction p2; f_equal/=. Qed.

Lemma Plt_sum (x y : positive) : x < y ↔ ∃ z, y = x + z.
Proof.
  split.
  - exists (y - x)%positive. symmetry. apply Pplus_minus. lia.
  - intros [z ->]. lia.
Qed.

(** Duplicate the bits of a positive, i.e. 1~0~1 -> 1~0~0~1~1 and
    1~1~0~0 -> 1~1~1~0~0~0~0 *)
Fixpoint Pdup (p : positive) : positive :=
  match p with
  | 1 => 1
  | p'~0 => (Pdup p')~0~0
  | p'~1 => (Pdup p')~1~1
  end.

Lemma Pdup_app p q :
  Pdup (p ++ q) = Pdup p ++ Pdup q.
Proof.
  revert p.
  induction q as [p IH|p IH|]; intros q; simpl.
  - by rewrite IH.
  - by rewrite IH.
  - reflexivity.
Qed.

Lemma Pdup_suffix_eq p q s1 s2 :
  s1~1~0 ++ Pdup p = s2~1~0 ++ Pdup q → p = q.
Proof.
  revert q.
  induction p as [p IH|p IH|]; intros [q|q|] eq; simplify_eq/=.
  - by rewrite (IH q).
  - by rewrite (IH q).
  - reflexivity.
Qed.

Instance Pdup_inj : Inj (=) (=) Pdup.
Proof.
  intros p q eq.
  apply (Pdup_suffix_eq _ _ 1 1).
  by rewrite eq.
Qed.

Lemma Preverse_Pdup p :
  Preverse (Pdup p) = Pdup (Preverse p).
Proof.
  induction p as [p IH|p IH|]; simpl.
  - rewrite 3!Preverse_xI.
    rewrite (assoc_L (++)).
    rewrite IH.
    rewrite Pdup_app.
    reflexivity.
  - rewrite 3!Preverse_xO.
    rewrite (assoc_L (++)).
    rewrite IH.
    rewrite Pdup_app.
    reflexivity.
  - reflexivity.
Qed.

Local Close Scope positive_scope.

(** * Notations and properties of [N] *)
Typeclasses Opaque N.le.
Typeclasses Opaque N.lt.

Infix "≤" := N.le : N_scope.
Notation "x ≤ y ≤ z" := (x ≤ y ∧ y ≤ z)%N : N_scope.
Notation "x ≤ y < z" := (x ≤ y ∧ y < z)%N : N_scope.
Notation "x < y ≤ z" := (x < y ∧ y ≤ z)%N : N_scope.
Notation "x ≤ y ≤ z ≤ z'" := (x ≤ y ∧ y ≤ z ∧ z ≤ z')%N : N_scope.
Notation "(≤)" := N.le (only parsing) : N_scope.
Notation "(<)" := N.lt (only parsing) : N_scope.

Infix "`div`" := N.div (at level 35) : N_scope.
Infix "`mod`" := N.modulo (at level 35) : N_scope.
Infix "`max`" := N.max (at level 35) : N_scope.
Infix "`min`" := N.min (at level 35) : N_scope.

Arguments N.add : simpl never.

Instance Npos_inj : Inj (=) (=) Npos.
Proof. by injection 1. Qed.

Instance N_eq_dec: EqDecision N := N.eq_dec.
Program Instance N_le_dec : RelDecision N.le := λ x y,
  match N.compare x y with Gt => right _ | _ => left _ end.
Solve Obligations with naive_solver.
Program Instance N_lt_dec : RelDecision N.lt := λ x y,
  match N.compare x y with Lt => left _ | _ => right _ end.
Solve Obligations with naive_solver.
Instance N_inhabited: Inhabited N := populate 1%N.
Instance N_lt_pi x y : ProofIrrel (x < y)%N.
Proof. unfold N.lt. apply _. Qed.

Instance N_le_po: PartialOrder (≤)%N.
Proof.
  repeat split; red. apply N.le_refl. apply N.le_trans. apply N.le_antisymm.
Qed.
Instance N_le_total: Total (≤)%N.
Proof. repeat intro; lia. Qed.

Hint Extern 0 (_ ≤ _)%N => reflexivity : core.

(** * Notations and properties of [Z] *)
Local Open Scope Z_scope.

Typeclasses Opaque Z.le.
Typeclasses Opaque Z.lt.

Infix "≤" := Z.le : Z_scope.
Notation "x ≤ y ≤ z" := (x ≤ y ∧ y ≤ z) : Z_scope.
Notation "x ≤ y < z" := (x ≤ y ∧ y < z) : Z_scope.
Notation "x < y < z" := (x < y ∧ y < z) : Z_scope.
Notation "x < y ≤ z" := (x < y ∧ y ≤ z) : Z_scope.
Notation "x ≤ y ≤ z ≤ z'" := (x ≤ y ∧ y ≤ z ∧ z ≤ z') : Z_scope.
Notation "(≤)" := Z.le (only parsing) : Z_scope.
Notation "(<)" := Z.lt (only parsing) : Z_scope.

Infix "`div`" := Z.div (at level 35) : Z_scope.
Infix "`mod`" := Z.modulo (at level 35) : Z_scope.
Infix "`quot`" := Z.quot (at level 35) : Z_scope.
Infix "`rem`" := Z.rem (at level 35) : Z_scope.
Infix "≪" := Z.shiftl (at level 35) : Z_scope.
Infix "≫" := Z.shiftr (at level 35) : Z_scope.
Infix "`max`" := Z.max (at level 35) : Z_scope.
Infix "`min`" := Z.min (at level 35) : Z_scope.

Instance Zpos_inj : Inj (=) (=) Zpos.
Proof. by injection 1. Qed.
Instance Zneg_inj : Inj (=) (=) Zneg.
Proof. by injection 1. Qed.

Instance Z_of_nat_inj : Inj (=) (=) Z.of_nat.
Proof. intros n1 n2. apply Nat2Z.inj. Qed.

Instance Z_eq_dec: EqDecision Z := Z.eq_dec.
Instance Z_le_dec: RelDecision Z.le := Z_le_dec.
Instance Z_lt_dec: RelDecision Z.lt := Z_lt_dec.
Instance Z_ge_dec: RelDecision Z.ge := Z_ge_dec.
Instance Z_gt_dec: RelDecision Z.gt := Z_gt_dec.
Instance Z_inhabited: Inhabited Z := populate 1.
Instance Z_lt_pi x y : ProofIrrel (x < y).
Proof. unfold Z.lt. apply _. Qed.

Instance Z_le_po : PartialOrder (≤).
Proof.
  repeat split; red. apply Z.le_refl. apply Z.le_trans. apply Z.le_antisymm.
Qed.
Instance Z_le_total: Total Z.le.
Proof. repeat intro; lia. Qed.

Lemma Z_pow_pred_r n m : 0 < m → n * n ^ (Z.pred m) = n ^ m.
Proof.
  intros. rewrite <-Z.pow_succ_r, Z.succ_pred. done. by apply Z.lt_le_pred.
Qed.
Lemma Z_quot_range_nonneg k x y : 0 ≤ x < k → 0 < y → 0 ≤ x `quot` y < k.
Proof.
  intros [??] ?.
  destruct (decide (y = 1)); subst; [rewrite Z.quot_1_r; auto |].
  destruct (decide (x = 0)); subst; [rewrite Z.quot_0_l; auto with lia |].
  split. apply Z.quot_pos; lia. trans x; auto. apply Z.quot_lt; lia.
Qed.

Arguments Z.pred : simpl never.
Arguments Z.succ : simpl never.
Arguments Z.of_nat : simpl never.
Arguments Z.to_nat : simpl never.
Arguments Z.mul : simpl never.
Arguments Z.add : simpl never.
Arguments Z.sub : simpl never.
Arguments Z.opp : simpl never.
Arguments Z.pow : simpl never.
Arguments Z.div : simpl never.
Arguments Z.modulo : simpl never.
Arguments Z.quot : simpl never.
Arguments Z.rem : simpl never.
Arguments Z.shiftl : simpl never.
Arguments Z.shiftr : simpl never.
Arguments Z.gcd : simpl never.
Arguments Z.lcm : simpl never.
Arguments Z.min : simpl never.
Arguments Z.max : simpl never.
Arguments Z.lor : simpl never.
Arguments Z.land : simpl never.
Arguments Z.lxor : simpl never.
Arguments Z.lnot : simpl never.
Arguments Z.square : simpl never.
Arguments Z.abs : simpl never.

Lemma Z_to_nat_neq_0_pos x : Z.to_nat x ≠ 0%nat → 0 < x.
Proof. by destruct x. Qed.
Lemma Z_to_nat_neq_0_nonneg x : Z.to_nat x ≠ 0%nat → 0 ≤ x.
Proof. by destruct x. Qed.
Lemma Z_mod_pos x y : 0 < y → 0 ≤ x `mod` y.
Proof. apply Z.mod_pos_bound. Qed.

Hint Resolve Z.lt_le_incl : zpos.
Hint Resolve Z.add_nonneg_pos Z.add_pos_nonneg Z.add_nonneg_nonneg : zpos.
Hint Resolve Z.mul_nonneg_nonneg Z.mul_pos_pos : zpos.
Hint Resolve Z.pow_pos_nonneg Z.pow_nonneg: zpos.
Hint Resolve Z_mod_pos Z.div_pos : zpos.
Hint Extern 1000 => lia : zpos.

Lemma Z_to_nat_nonpos x : x ≤ 0 → Z.to_nat x = 0%nat.
Proof. destruct x; simpl; auto using Z2Nat.inj_neg. by intros []. Qed.
Lemma Z2Nat_inj_pow (x y : nat) : Z.of_nat (x ^ y) = x ^ y.
Proof.
  induction y as [|y IH]; [by rewrite Z.pow_0_r, Nat.pow_0_r|].
  by rewrite Nat.pow_succ_r, Nat2Z.inj_succ, Z.pow_succ_r,
    Nat2Z.inj_mul, IH by auto with zpos.
Qed.
Lemma Nat2Z_divide n m : (Z.of_nat n | Z.of_nat m) ↔ (n | m)%nat.
Proof.
  split.
  - rewrite <-(Nat2Z.id m) at 2; intros [i ->]; exists (Z.to_nat i).
    destruct (decide (0 ≤ i)%Z).
    { by rewrite Z2Nat.inj_mul, Nat2Z.id by lia. }
    by rewrite !Z_to_nat_nonpos by auto using Z.mul_nonpos_nonneg with lia.
  - intros [i ->]. exists (Z.of_nat i). by rewrite Nat2Z.inj_mul.
Qed.
Lemma Z2Nat_divide n m :
  0 ≤ n → 0 ≤ m → (Z.to_nat n | Z.to_nat m)%nat ↔ (n | m).
Proof. intros. by rewrite <-Nat2Z_divide, !Z2Nat.id by done. Qed.
Lemma Nat2Z_inj_div x y : Z.of_nat (x `div` y) = x `div` y.
Proof.
  destruct (decide (y = 0%nat)); [by subst; destruct x |].
  apply Z.div_unique with (x `mod` y)%nat.
  { left. rewrite <-(Nat2Z.inj_le 0), <-Nat2Z.inj_lt.
    apply Nat.mod_bound_pos; lia. }
  by rewrite <-Nat2Z.inj_mul, <-Nat2Z.inj_add, <-Nat.div_mod.
Qed.
Lemma Nat2Z_inj_mod x y : Z.of_nat (x `mod` y) = x `mod` y.
Proof.
  destruct (decide (y = 0%nat)); [by subst; destruct x |].
  apply Z.mod_unique with (x `div` y)%nat.
  { left. rewrite <-(Nat2Z.inj_le 0), <-Nat2Z.inj_lt.
    apply Nat.mod_bound_pos; lia. }
  by rewrite <-Nat2Z.inj_mul, <-Nat2Z.inj_add, <-Nat.div_mod.
Qed.
Lemma Z2Nat_inj_div x y :
  0 ≤ x → 0 ≤ y →
  Z.to_nat (x `div` y) = (Z.to_nat x `div` Z.to_nat y)%nat.
Proof.
  intros. destruct (decide (y = 0%nat)); [by subst; destruct x|].
  pose proof (Z.div_pos x y).
  apply (inj Z.of_nat). by rewrite Nat2Z_inj_div, !Z2Nat.id by lia.
Qed.
Lemma Z2Nat_inj_mod x y :
  0 ≤ x → 0 ≤ y →
  Z.to_nat (x `mod` y) = (Z.to_nat x `mod` Z.to_nat y)%nat.
Proof.
  intros. destruct (decide (y = 0%nat)); [by subst; destruct x|].
  pose proof (Z_mod_pos x y).
  apply (inj Z.of_nat). by rewrite Nat2Z_inj_mod, !Z2Nat.id by lia.
Qed.
Lemma Z_succ_pred_induction y (P : Z → Prop) :
  P y →
  (∀ x, y ≤ x → P x → P (Z.succ x)) →
  (∀ x, x ≤ y → P x → P (Z.pred x)) →
  (∀ x, P x).
Proof. intros H0 HS HP. by apply (Z.order_induction' _ _ y). Qed.
Lemma Zmod_in_range q a c :
  q * c ≤ a < (q + 1) * c →
  a `mod` c = a - q * c.
Proof. intros ?. symmetry. apply Z.mod_unique_pos with q; lia. Qed.

Local Close Scope Z_scope.

(** * Injectivity of casts *)
Instance N_of_nat_inj: Inj (=) (=) N.of_nat := Nat2N.inj.
Instance nat_of_N_inj: Inj (=) (=) N.to_nat := N2Nat.inj.
Instance nat_of_pos_inj: Inj (=) (=) Pos.to_nat := Pos2Nat.inj.
Instance pos_of_Snat_inj: Inj (=) (=) Pos.of_succ_nat := SuccNat2Pos.inj.
Instance Z_of_N_inj: Inj (=) (=) Z.of_N := N2Z.inj.
(* Add others here. *)

(** * Notations and properties of [Qc] *)
Typeclasses Opaque Qcle.
Typeclasses Opaque Qclt.

Local Open Scope Qc_scope.
Delimit Scope Qc_scope with Qc.
Notation "1" := (Q2Qc 1) : Qc_scope.
Notation "2" := (1+1) : Qc_scope.
Notation "- 1" := (Qcopp 1) : Qc_scope.
Notation "- 2" := (Qcopp 2) : Qc_scope.
Infix "≤" := Qcle : Qc_scope.
Notation "x ≤ y ≤ z" := (x ≤ y ∧ y ≤ z) : Qc_scope.
Notation "x ≤ y < z" := (x ≤ y ∧ y < z) : Qc_scope.
Notation "x < y < z" := (x < y ∧ y < z) : Qc_scope.
Notation "x < y ≤ z" := (x < y ∧ y ≤ z) : Qc_scope.
Notation "x ≤ y ≤ z ≤ z'" := (x ≤ y ∧ y ≤ z ∧ z ≤ z') : Qc_scope.
Notation "(≤)" := Qcle (only parsing) : Qc_scope.
Notation "(<)" := Qclt (only parsing) : Qc_scope.

Hint Extern 1 (_ ≤ _) => reflexivity || discriminate : core.
Arguments Qred : simpl never.

Instance Qc_eq_dec: EqDecision Qc := Qc_eq_dec.
Program Instance Qc_le_dec: RelDecision Qcle := λ x y,
  if Qclt_le_dec y x then right _ else left _.
Next Obligation. intros x y; apply Qclt_not_le. Qed.
Next Obligation. done. Qed.
Program Instance Qc_lt_dec: RelDecision Qclt := λ x y,
  if Qclt_le_dec x y then left _ else right _.
Next Obligation. done. Qed.
Next Obligation. intros x y; apply Qcle_not_lt. Qed.
Instance Qc_lt_pi x y : ProofIrrel (x < y).
Proof. unfold Qclt. apply _. Qed.

Instance Qc_le_po: PartialOrder (≤).
Proof.
  repeat split; red. apply Qcle_refl. apply Qcle_trans. apply Qcle_antisym.
Qed.
Instance Qc_lt_strict: StrictOrder (<).
Proof.
  split; red. intros x Hx. by destruct (Qclt_not_eq x x). apply Qclt_trans.
Qed.
Instance Qc_le_total: Total Qcle.
Proof. intros x y. destruct (Qclt_le_dec x y); auto using Qclt_le_weak. Qed.

Lemma Qcmult_0_l x : 0 * x = 0.
Proof. ring. Qed.
Lemma Qcmult_0_r x : x * 0 = 0.
Proof. ring. Qed.
Lemma Qcplus_diag x : (x + x)%Qc = (2 * x)%Qc.
Proof. ring. Qed.
Lemma Qcle_ngt (x y : Qc) : x ≤ y ↔ ¬y < x.
Proof. split; auto using Qcle_not_lt, Qcnot_lt_le. Qed.
Lemma Qclt_nge (x y : Qc) : x < y ↔ ¬y ≤ x.
Proof. split; auto using Qclt_not_le, Qcnot_le_lt. Qed.
Lemma Qcplus_le_mono_l (x y z : Qc) : x ≤ y ↔ z + x ≤ z + y.
Proof.
  split; intros.
  - by apply Qcplus_le_compat.
  - replace x with ((0 - z) + (z + x)) by ring.
    replace y with ((0 - z) + (z + y)) by ring.
    by apply Qcplus_le_compat.
Qed.
Lemma Qcplus_le_mono_r (x y z : Qc) : x ≤ y ↔ x + z ≤ y + z.
Proof. rewrite !(Qcplus_comm _ z). apply Qcplus_le_mono_l. Qed.
Lemma Qcplus_lt_mono_l (x y z : Qc) : x < y ↔ z + x < z + y.
Proof. by rewrite !Qclt_nge, <-Qcplus_le_mono_l. Qed.
Lemma Qcplus_lt_mono_r (x y z : Qc) : x < y ↔ x + z < y + z.
Proof. by rewrite !Qclt_nge, <-Qcplus_le_mono_r. Qed.
Instance Qcopp_inj : Inj (=) (=) Qcopp.
Proof.
  intros x y H. by rewrite <-(Qcopp_involutive x), H, Qcopp_involutive.
Qed.
Instance Qcplus_inj_r z : Inj (=) (=) (Qcplus z).
Proof.
  intros x y H. by apply (anti_symm (≤));rewrite (Qcplus_le_mono_l _ _ z), H.
Qed.
Instance Qcplus_inj_l z : Inj (=) (=) (λ x, x + z).
Proof.
  intros x y H. by apply (anti_symm (≤)); rewrite (Qcplus_le_mono_r _ _ z), H.
Qed.
Lemma Qcplus_pos_nonneg (x y : Qc) : 0 < x → 0 ≤ y → 0 < x + y.
Proof.
  intros. apply Qclt_le_trans with (x + 0); [by rewrite Qcplus_0_r|].
  by apply Qcplus_le_mono_l.
Qed.
Lemma Qcplus_nonneg_pos (x y : Qc) : 0 ≤ x → 0 < y → 0 < x + y.
Proof. rewrite (Qcplus_comm x). auto using Qcplus_pos_nonneg. Qed.
Lemma Qcplus_pos_pos (x y : Qc) : 0 < x → 0 < y → 0 < x + y.
Proof. auto using Qcplus_pos_nonneg, Qclt_le_weak. Qed.
Lemma Qcplus_nonneg_nonneg (x y : Qc) : 0 ≤ x → 0 ≤ y → 0 ≤ x + y.
Proof.
  intros. trans (x + 0); [by rewrite Qcplus_0_r|].
  by apply Qcplus_le_mono_l.
Qed.
Lemma Qcplus_neg_nonpos (x y : Qc) : x < 0 → y ≤ 0 → x + y < 0.
Proof.
  intros. apply Qcle_lt_trans with (x + 0); [|by rewrite Qcplus_0_r].
  by apply Qcplus_le_mono_l.
Qed.
Lemma Qcplus_nonpos_neg (x y : Qc) : x ≤ 0 → y < 0 → x + y < 0.
Proof. rewrite (Qcplus_comm x). auto using Qcplus_neg_nonpos. Qed.
Lemma Qcplus_neg_neg (x y : Qc) : x < 0 → y < 0 → x + y < 0.
Proof. auto using Qcplus_nonpos_neg, Qclt_le_weak. Qed.
Lemma Qcplus_nonpos_nonpos (x y : Qc) : x ≤ 0 → y ≤ 0 → x + y ≤ 0.
Proof.
  intros. trans (x + 0); [|by rewrite Qcplus_0_r].
  by apply Qcplus_le_mono_l.
Qed.
Lemma Qcmult_le_mono_nonneg_l x y z : 0 ≤ z → x ≤ y → z * x ≤ z * y.
Proof. intros. rewrite !(Qcmult_comm z). by apply Qcmult_le_compat_r. Qed.
Lemma Qcmult_le_mono_nonneg_r x y z : 0 ≤ z → x ≤ y → x * z ≤ y * z.
Proof. intros. by apply Qcmult_le_compat_r. Qed.
Lemma Qcmult_le_mono_pos_l x y z : 0 < z → x ≤ y ↔ z * x ≤ z * y.
Proof.
  split; auto using Qcmult_le_mono_nonneg_l, Qclt_le_weak.
  rewrite !Qcle_ngt, !(Qcmult_comm z).
  intuition auto using Qcmult_lt_compat_r.
Qed.
Lemma Qcmult_le_mono_pos_r x y z : 0 < z → x ≤ y ↔ x * z ≤ y * z.
Proof. rewrite !(Qcmult_comm _ z). by apply Qcmult_le_mono_pos_l. Qed.
Lemma Qcmult_lt_mono_pos_l x y z : 0 < z → x < y ↔ z * x < z * y.
Proof. intros. by rewrite !Qclt_nge, <-Qcmult_le_mono_pos_l. Qed.
Lemma Qcmult_lt_mono_pos_r x y z : 0 < z → x < y ↔ x * z < y * z.
Proof. intros. by rewrite !Qclt_nge, <-Qcmult_le_mono_pos_r. Qed.
Lemma Qcmult_pos_pos x y : 0 < x → 0 < y → 0 < x * y.
Proof.
  intros. apply Qcle_lt_trans with (0 * y); [by rewrite Qcmult_0_l|].
  by apply Qcmult_lt_mono_pos_r.
Qed.
Lemma Qcmult_nonneg_nonneg x y : 0 ≤ x → 0 ≤ y → 0 ≤ x * y.
Proof.
  intros. trans (0 * y); [by rewrite Qcmult_0_l|].
  by apply Qcmult_le_mono_nonneg_r.
Qed.

Lemma inject_Z_Qred n : Qred (inject_Z n) = inject_Z n.
Proof. apply Qred_identity; auto using Z.gcd_1_r. Qed.
Coercion Qc_of_Z (n : Z) : Qc := Qcmake _ (inject_Z_Qred n).
Lemma Z2Qc_inj_0 : Qc_of_Z 0 = 0.
Proof. by apply Qc_is_canon. Qed.
Lemma Z2Qc_inj_1 : Qc_of_Z 1 = 1.
Proof. by apply Qc_is_canon. Qed.
Lemma Z2Qc_inj_2 : Qc_of_Z 2 = 2.
Proof. by apply Qc_is_canon. Qed.
Lemma Z2Qc_inj n m : Qc_of_Z n = Qc_of_Z m → n = m.
Proof. by injection 1. Qed.
Lemma Z2Qc_inj_iff n m : Qc_of_Z n = Qc_of_Z m ↔ n = m.
Proof. split. auto using Z2Qc_inj. by intros ->. Qed.
Lemma Z2Qc_inj_le n m : (n ≤ m)%Z ↔ Qc_of_Z n ≤ Qc_of_Z m.
Proof. by rewrite Zle_Qle. Qed.
Lemma Z2Qc_inj_lt n m : (n < m)%Z ↔ Qc_of_Z n < Qc_of_Z m.
Proof. by rewrite Zlt_Qlt. Qed.
Lemma Z2Qc_inj_add n m : Qc_of_Z (n + m) = Qc_of_Z n + Qc_of_Z m.
Proof. apply Qc_is_canon; simpl. by rewrite Qred_correct, inject_Z_plus. Qed.
Lemma Z2Qc_inj_mul n m : Qc_of_Z (n * m) = Qc_of_Z n * Qc_of_Z m.
Proof. apply Qc_is_canon; simpl. by rewrite Qred_correct, inject_Z_mult. Qed.
Lemma Z2Qc_inj_opp n : Qc_of_Z (-n) = -Qc_of_Z n.
Proof. apply Qc_is_canon; simpl. by rewrite Qred_correct, inject_Z_opp. Qed.
Lemma Z2Qc_inj_sub n m : Qc_of_Z (n - m) = Qc_of_Z n - Qc_of_Z m.
Proof.
  apply Qc_is_canon; simpl.
  by rewrite !Qred_correct, <-inject_Z_opp, <-inject_Z_plus.
Qed.
Local Close Scope Qc_scope.

(** * Positive rationals *)
(** The theory of positive rationals is very incomplete. We merely provide
some operations and theorems that are relevant for fractional permissions. *)
Record Qp := mk_Qp { Qp_car :> Qc ; Qp_prf : (0 < Qp_car)%Qc }.
Hint Resolve Qp_prf : core.
Delimit Scope Qp_scope with Qp.
Bind Scope Qp_scope with Qp.
Arguments Qp_car _%Qp : assert.

Definition Qp_one : Qp := mk_Qp 1 eq_refl.
Program Definition Qp_plus (x y : Qp) : Qp := mk_Qp (x + y) _.
Next Obligation. by intros x y; apply Qcplus_pos_pos. Qed.
Definition Qp_minus (x y : Qp) : option Qp :=
  let z := (x - y)%Qc in
  match decide (0 < z)%Qc with left Hz => Some (mk_Qp z Hz) | _ => None end.
Program Definition Qp_mult (x y : Qp) : Qp := mk_Qp (x * y) _.
Next Obligation. intros x y. apply Qcmult_pos_pos; apply Qp_prf. Qed.

Program Definition Qp_div (x : Qp) (y : positive) : Qp := mk_Qp (x / Zpos y) _.
Next Obligation.
  intros x y. unfold Qcdiv. assert (0 < Zpos y)%Qc.
  { apply (Z2Qc_inj_lt 0%Z (Zpos y)), Pos2Z.is_pos. }
  by rewrite (Qcmult_lt_mono_pos_r _ _ (Zpos y)%Z), Qcmult_0_l,
    <-Qcmult_assoc, Qcmult_inv_l, Qcmult_1_r.
Qed.

Infix "+" := Qp_plus : Qp_scope.
Infix "-" := Qp_minus : Qp_scope.
Infix "*" := Qp_mult : Qp_scope.
Infix "/" := Qp_div : Qp_scope.
Notation "1" := Qp_one : Qp_scope.
Notation "2" := (1 + 1)%Qp : Qp_scope.
Notation "3" := (1 + 2)%Qp : Qp_scope.
Notation "4" := (1 + 3)%Qp : Qp_scope.

Lemma Qp_eq x y : x = y ↔ Qp_car x = Qp_car y.
Proof.
  split; [by intros ->|].
  destruct x, y; intros; simplify_eq/=; f_equal; apply (proof_irrel _).
Qed.

Instance Qp_inhabited : Inhabited Qp := populate 1%Qp.
Instance Qp_eq_dec : EqDecision Qp.
Proof.
 refine (λ x y, cast_if (decide (Qp_car x = Qp_car y))); by rewrite Qp_eq.
Defined.

Instance Qp_plus_assoc : Assoc (=) Qp_plus.
Proof. intros x y z; apply Qp_eq, Qcplus_assoc. Qed.
Instance Qp_plus_comm : Comm (=) Qp_plus.
Proof. intros x y; apply Qp_eq, Qcplus_comm. Qed.
Instance Qp_plus_inj_r p : Inj (=) (=) (Qp_plus p).
Proof. intros q1 q2. rewrite !Qp_eq; simpl. apply (inj (Qcplus p)). Qed.
Instance Qp_plus_inj_l p : Inj (=) (=) (λ q, q + p)%Qp.
Proof. intros q1 q2. rewrite !Qp_eq; simpl. apply (inj (λ q, q + p)%Qc). Qed.

Lemma Qp_minus_diag x : (x - x)%Qp = None.
Proof. unfold Qp_minus, Qcminus. by rewrite Qcplus_opp_r. Qed.
Lemma Qp_op_minus x y : ((x + y) - x)%Qp = Some y.
Proof.
  unfold Qp_minus, Qcminus; simpl.
  rewrite (Qcplus_comm x), <- Qcplus_assoc, Qcplus_opp_r, Qcplus_0_r.
  destruct (decide _) as [|[]]; auto. by f_equal; apply Qp_eq.
Qed.

Instance Qp_mult_assoc : Assoc (=) Qp_mult.
Proof. intros x y z; apply Qp_eq, Qcmult_assoc. Qed.
Instance Qp_mult_comm : Comm (=) Qp_mult.
Proof. intros x y; apply Qp_eq, Qcmult_comm. Qed.
Lemma Qp_mult_plus_distr_r x y z: (x * (y + z) = x * y + x * z)%Qp.
Proof. apply Qp_eq, Qcmult_plus_distr_r. Qed.
Lemma Qp_mult_plus_distr_l x y z: ((x + y) * z = x * z + y * z)%Qp.
Proof. apply Qp_eq, Qcmult_plus_distr_l. Qed.
Lemma Qp_mult_1_l x: (1 * x)%Qp = x.
Proof. apply Qp_eq, Qcmult_1_l. Qed.
Lemma Qp_mult_1_r x: (x * 1)%Qp = x.
Proof. apply Qp_eq, Qcmult_1_r. Qed.

Lemma Qp_div_1 x : (x / 1 = x)%Qp.
Proof.
  apply Qp_eq; simpl.
  rewrite <-(Qcmult_div_r x 1) at 2 by done. by rewrite Qcmult_1_l.
Qed.
Lemma Qp_div_S x y : (x / (2 * y) + x / (2 * y) = x / y)%Qp.
Proof.
  apply Qp_eq; simpl. unfold Qcdiv.
  rewrite <-Qcmult_plus_distr_l, Pos2Z.inj_mul, Z2Qc_inj_mul, Z2Qc_inj_2.
  rewrite Qcplus_diag. by field_simplify.
Qed.
Lemma Qp_div_2 x : (x / 2 + x / 2 = x)%Qp.
Proof.
  change 2%positive with (2 * 1)%positive. by rewrite Qp_div_S, Qp_div_1.
Qed.
Lemma Qp_half_half : (1 / 2 + 1 / 2 = 1)%Qp.
Proof. apply (bool_decide_unpack _); by compute. Qed.
Lemma Qp_quarter_three_quarter : (1 / 4 + 3 / 4 = 1)%Qp.
Proof. apply (bool_decide_unpack _); by compute. Qed.
Lemma Qp_three_quarter_quarter : (3 / 4 + 1 / 4 = 1)%Qp.
Proof. apply (bool_decide_unpack _); by compute. Qed.

Lemma Qp_lt_sum (x y : Qp) : (x < y)%Qc ↔ ∃ z, y = (x + z)%Qp.
Proof.
  split.
  - intros Hlt%Qclt_minus_iff. exists (mk_Qp (y - x) Hlt). apply Qp_eq; simpl.
    unfold Qcminus. by rewrite (Qcplus_comm y), Qcplus_assoc, Qcplus_opp_r, Qcplus_0_l.
  - intros [z ->]; simpl.
    rewrite <-(Qcplus_0_r x) at 1. apply Qcplus_lt_mono_l, Qp_prf.
Qed.

Lemma Qp_lower_bound q1 q2 : ∃ q q1' q2', (q1 = q + q1' ∧ q2 = q + q2')%Qp.
Proof.
  revert q1 q2. cut (∀ q1 q2 : Qp, (q1 ≤ q2)%Qc →
    ∃ q q1' q2', (q1 = q + q1' ∧ q2 = q + q2')%Qp).
  { intros help q1 q2.
    destruct (Qc_le_dec q1 q2) as [LE|LE%Qclt_nge%Qclt_le_weak]; [by eauto|].
    destruct (help q2 q1) as (q&q1'&q2'&?&?); eauto. }
  intros q1 q2 Hq. exists (q1 / 2)%Qp, (q1 / 2)%Qp.
  assert (0 < q2 +- q1 */ 2)%Qc as Hq2'.
  { eapply Qclt_le_trans; [|by apply Qcplus_le_mono_r, Hq].
    replace (q1 +- q1 */ 2)%Qc with (q1 * (1 +- 1*/2))%Qc by ring.
    replace 0%Qc with (0 * (1+-1*/2))%Qc by ring. by apply Qcmult_lt_compat_r. }
  exists (mk_Qp (q2 +- q1 */ 2%Z) Hq2'). split; [by rewrite Qp_div_2|].
  apply Qp_eq; simpl. unfold Qcdiv. ring.
Qed.

Lemma Qp_cross_split p a b c d :
  (a + b = p → c + d = p →
  ∃ ac ad bc bd, ac + ad = a ∧ bc + bd = b ∧ ac + bc = c ∧ ad + bd = d)%Qp.
Proof.
  intros H <-. revert a b c d H. cut (∀ a b c d : Qp,
    (a < c)%Qc → a + b = c + d →
    ∃ ac ad bc bd, ac + ad = a ∧ bc + bd = b ∧ ac + bc = c ∧ ad + bd = d)%Qp.
  { intros help a b c d ?.
    destruct (Qclt_le_dec a c) as [?|[?| ->%Qp_eq]%Qcle_lt_or_eq].
    - auto.
    - destruct (help c d a b); [done..|]. naive_solver.
    - apply (inj (Qp_plus a)) in H as ->. destruct (Qp_lower_bound a d) as (q&a'&d'&->&->).
      exists a', q, q, d'. repeat split; done || by rewrite (comm_L Qp_plus). }
  intros a b c d [e ->]%Qp_lt_sum. rewrite <-(assoc_L _). intros ->%(inj (Qp_plus a)).
  destruct (Qp_lower_bound a d) as (q&a'&d'&->&->).
  eexists a', q, (q + e)%Qp, d'; split_and?; [by rewrite (comm_L Qp_plus)|..|done].
  - by rewrite (assoc_L _), (comm_L Qp_plus e).
  - by rewrite (assoc_L _), (comm_L Qp_plus a').
Qed.

Lemma Qp_bounded_split (p r : Qp) : ∃ q1 q2 : Qp, (q1 ≤ r)%Qc ∧ p = (q1 + q2)%Qp.
Proof.
  destruct (Qclt_le_dec r p) as [?|?].
  - assert (0 < p +- r)%Qc as Hpos.
    { apply (Qcplus_lt_mono_r _ _ r). rewrite <-Qcplus_assoc, (Qcplus_comm (-r)).
      by rewrite Qcplus_opp_r, Qcplus_0_l, Qcplus_0_r. }
    exists r, (mk_Qp _ Hpos); simpl; split; [done|].
    apply Qp_eq; simpl. rewrite Qcplus_comm, <-Qcplus_assoc, (Qcplus_comm (-r)).
    by rewrite Qcplus_opp_r, Qcplus_0_r.
  - exists (p / 2)%Qp, (p / 2)%Qp; split.
    + trans p; [|done]. apply Qclt_le_weak, Qp_lt_sum.
      exists (p / 2)%Qp. by rewrite Qp_div_2.
    + by rewrite Qp_div_2.
Qed.

Lemma Qp_not_plus_q_ge_1 (q: Qp): ¬ ((1 + q)%Qp ≤ 1%Qp)%Qc.
Proof.
  intros Hle.
  apply (Qcplus_le_mono_l q 0 1) in Hle.
  apply Qcle_ngt in Hle. apply Hle, Qp_prf.
Qed.

Lemma Qp_ge_0 (q: Qp): (0 ≤ q)%Qc.
Proof. apply Qclt_le_weak, Qp_prf. Qed.

(** * Helper for working with accessing lists with wrap-around
    See also [rotate] and [rotate_take] in [list.v] *)
(** [rotate_nat_add base offset len] computes [(base + offset) `mod`
len]. This is useful in combination with the [rotate] function on
lists, since the index [i] of [rotate n l] corresponds to the index
[rotate_nat_add n i (length i)] of the original list. The definition
uses [Z] for consistency with [rotate_nat_sub]. **)
Definition rotate_nat_add (base offset len : nat) : nat :=
  Z.to_nat ((base + offset) `mod` len)%Z.
(** [rotate_nat_sub base offset len] is the inverse of [rotate_nat_add
base offset len]. The definition needs to use modulo on [Z] instead of
on nat since otherwise we need the sidecondition [base < len] on
[rotate_nat_sub_add]. **)
Definition rotate_nat_sub (base offset len : nat) : nat :=
  Z.to_nat ((len + offset - base) `mod` len)%Z.

Lemma rotate_nat_add_len_0 base offset:
  rotate_nat_add base offset 0 = 0.
Proof. unfold rotate_nat_add. by rewrite Zmod_0_r. Qed.
Lemma rotate_nat_sub_len_0 base offset:
  rotate_nat_sub base offset 0 = 0.
Proof. unfold rotate_nat_sub. by rewrite Zmod_0_r. Qed.

Lemma rotate_nat_add_add_mod base offset len:
  rotate_nat_add base offset len =
  rotate_nat_add (Z.to_nat (base `mod` len)%Z) offset len.
Proof.
  destruct len as [|i];[ by rewrite !rotate_nat_add_len_0|].
  pose proof (Z_mod_lt base (S i)) as Hlt. unfold rotate_nat_add.
  rewrite !Z2Nat.id by lia. by rewrite Zplus_mod_idemp_l.
Qed.

Lemma rotate_nat_add_alt base offset len:
  base < len → offset < len →
  rotate_nat_add base offset len =
  if decide (base + offset < len) then base + offset else base + offset - len.
Proof.
  unfold rotate_nat_add. intros ??. case_decide.
  - rewrite Z.mod_small by lia. by rewrite <-Nat2Z.inj_add, Nat2Z.id.
  - rewrite (Zmod_in_range 1) by lia.
    by rewrite Z.mul_1_l, <-Nat2Z.inj_add, <-Nat2Z.inj_sub,Nat2Z.id by lia.
Qed.
Lemma rotate_nat_sub_alt base offset len:
  base < len → offset < len →
  rotate_nat_sub base offset len =
  if decide (offset < base) then len + offset - base else offset - base.
Proof.
  unfold rotate_nat_sub. intros ??. case_decide.
  - rewrite Z.mod_small by lia.
    by rewrite <-Nat2Z.inj_add, <-Nat2Z.inj_sub, Nat2Z.id by lia.
  - rewrite (Zmod_in_range 1) by lia.
    rewrite Z.mul_1_l, <-Nat2Z.inj_add, <-!Nat2Z.inj_sub,Nat2Z.id; lia.
Qed.

Lemma rotate_nat_add_0 base len :
  base < len → rotate_nat_add base 0 len = base.
Proof.
  intros ?. unfold rotate_nat_add.
  rewrite Z.mod_small by lia. by rewrite Z.add_0_r, Nat2Z.id.
Qed.
Lemma rotate_nat_sub_0 base len :
  base < len → rotate_nat_sub base base len = 0.
Proof. intros ?. rewrite rotate_nat_sub_alt by done. case_decide; lia. Qed.

Lemma rotate_nat_add_lt base offset len :
  0 < len → rotate_nat_add base offset len < len.
Proof.
  unfold rotate_nat_add. intros ?.
  pose proof (Nat.mod_upper_bound (base + offset) len).
  rewrite Z2Nat_inj_mod, Z2Nat.inj_add, !Nat2Z.id; lia.
Qed.
Lemma rotate_nat_sub_lt base offset len :
  0 < len → rotate_nat_sub base offset len < len.
Proof.
  unfold rotate_nat_sub. intros ?.
  pose proof (Z_mod_lt (len + offset - base) len).
  apply Nat2Z.inj_lt. rewrite Z2Nat.id; lia.
Qed.

Lemma rotate_nat_add_sub base len offset:
  offset < len →
  rotate_nat_add base (rotate_nat_sub base offset len) len = offset.
Proof.
  intros ?. unfold rotate_nat_add, rotate_nat_sub.
  rewrite Z2Nat.id by (apply Z_mod_pos; lia). rewrite Zplus_mod_idemp_r.
  replace (base + (len + offset - base))%Z with (len + offset)%Z by lia.
  rewrite (Zmod_in_range 1) by lia.
  rewrite Z.mul_1_l, <-Nat2Z.inj_add, <-!Nat2Z.inj_sub,Nat2Z.id; lia.
Qed.

Lemma rotate_nat_sub_add base len offset:
  offset < len →
  rotate_nat_sub base (rotate_nat_add base offset len) len = offset.
Proof.
  intros ?. unfold rotate_nat_add, rotate_nat_sub.
  rewrite Z2Nat.id by (apply Z_mod_pos; lia).
  assert (∀ n, (len + n - base) = ((len - base) + n))%Z as -> by naive_solver lia.
  rewrite Zplus_mod_idemp_r.
  replace (len - base + (base + offset))%Z with (len + offset)%Z by lia.
  rewrite (Zmod_in_range 1) by lia.
  rewrite Z.mul_1_l, <-Nat2Z.inj_add, <-!Nat2Z.inj_sub,Nat2Z.id; lia.
Qed.

Lemma rotate_nat_add_add base offset len n:
  0 < len →
  rotate_nat_add base (offset + n) len =
  (rotate_nat_add base offset len + n) `mod` len.
Proof.
  intros ?. unfold rotate_nat_add.
  rewrite !Z2Nat_inj_mod, !Z2Nat.inj_add, !Nat2Z.id by lia.
  by rewrite plus_assoc, Nat.add_mod_idemp_l by lia.
Qed.

Lemma rotate_nat_add_S base offset len:
  0 < len →
  rotate_nat_add base (S offset) len =
  S (rotate_nat_add base offset len) `mod` len.
Proof. intros ?. by rewrite <-Nat.add_1_r, rotate_nat_add_add, Nat.add_1_r. Qed.
