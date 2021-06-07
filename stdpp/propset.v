(** This file implements sets as functions into Prop. *)
From stdpp Require Export sets.
Set Default Proof Using "Type".

Record propset (A : Type) : Type := PropSet { propset_car : A → Prop }.
Add Printing Constructor propset.
Arguments PropSet {_} _ : assert.
Arguments propset_car {_} _ _ : assert.
Notation "{[ x | P ]}" := (PropSet (λ x, P))
  (at level 1, format "{[  x  |  P  ]}") : stdpp_scope.

Instance propset_elem_of {A} : ElemOf A (propset A) := λ x X, propset_car X x.

Instance propset_top {A} : Top (propset A) := {[ _ | True ]}.
Instance propset_empty {A} : Empty (propset A) := {[ _ | False ]}.
Instance propset_singleton {A} : Singleton A (propset A) := λ y, {[ x | y = x ]}.
Instance propset_union {A} : Union (propset A) := λ X1 X2, {[ x | x ∈ X1 ∨ x ∈ X2 ]}.
Instance propset_intersection {A} : Intersection (propset A) := λ X1 X2,
  {[ x | x ∈ X1 ∧ x ∈ X2 ]}.
Instance propset_difference {A} : Difference (propset A) := λ X1 X2,
  {[ x | x ∈ X1 ∧ x ∉ X2 ]}.
Instance propset_top_set {A} : TopSet A (propset A).
Proof. split; [split; [split| |]|]; by repeat intro. Qed.

Lemma elem_of_PropSet {A} (P : A → Prop) x : x ∈ {[ x | P x ]} ↔ P x.
Proof. done. Qed.
Lemma not_elem_of_PropSet {A} (P : A → Prop) x : x ∉ {[ x | P x ]} ↔ ¬P x.
Proof. done. Qed.

Definition set_to_propset `{ElemOf A C} (X : C) : propset A :=
  {[ x | x ∈ X ]}.
Lemma elem_of_set_to_propset `{SemiSet A C} x (X : C) :
  x ∈ set_to_propset X ↔ x ∈ X.
Proof. done. Qed.

Instance propset_ret : MRet propset := λ A (x : A), {[ x ]}.
Instance propset_bind : MBind propset := λ A B (f : A → propset B) (X : propset A),
  PropSet (λ b, ∃ a, b ∈ f a ∧ a ∈ X).
Instance propset_fmap : FMap propset := λ A B (f : A → B) (X : propset A),
  {[ b | ∃ a, b = f a ∧ a ∈ X ]}.
Instance propset_join : MJoin propset := λ A (XX : propset (propset A)),
  {[ a | ∃ X : propset A, a ∈ X ∧ X ∈ XX ]}.
Instance propset_monad_set : MonadSet propset.
Proof. by split; try apply _. Qed.

Instance set_unfold_PropSet {A} (P : A → Prop) x Q :
  SetUnfoldSimpl (P x) Q → SetUnfoldElemOf x (PropSet P) Q.
Proof. intros HPQ. constructor. apply HPQ. Qed.

Global Opaque propset_elem_of propset_top propset_empty propset_singleton.
Global Opaque propset_union propset_intersection propset_difference.
Global Opaque propset_ret propset_bind propset_fmap propset_join.
