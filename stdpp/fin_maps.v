(** Finite maps associate data to keys. This file defines an interface for
finite maps and collects some theory on it. Most importantly, it proves useful
induction principles for finite maps and implements the tactic
[simplify_map_eq] to simplify goals involving finite maps. *)
From Coq Require Import Permutation.
From stdpp Require Export relations orders vector fin_sets.
(* FIXME: This file needs a 'Proof Using' hint, but the default we use
   everywhere makes for lots of extra ssumptions. *)

(** * Axiomatization of finite maps *)
(** We require Leibniz equality to be extensional on finite maps. This of
course limits the space of finite map implementations, but since we are mainly
interested in finite maps with numbers as indexes, we do not consider this to
be a serious limitation. The main application of finite maps is to implement
the memory, where extensionality of Leibniz equality is very important for a
convenient use in the assertions of our axiomatic semantics. *)

(** Finiteness is axiomatized by requiring that each map can be translated
to an association list. The translation to association lists is used to
prove well founded recursion on finite maps. *)

(** Finite map implementations are required to implement the [merge] function
which enables us to give a generic implementation of [union_with],
[intersection_with], and [difference_with]. *)

Class FinMapToList K A M := map_to_list: M → list (K * A).
Hint Mode FinMapToList ! - - : typeclass_instances.
Hint Mode FinMapToList - - ! : typeclass_instances.

Class FinMap K M `{FMap M, ∀ A, Lookup K A (M A), ∀ A, Empty (M A), ∀ A,
    PartialAlter K A (M A), OMap M, Merge M, ∀ A, FinMapToList K A (M A),
    EqDecision K} := {
  map_eq {A} (m1 m2 : M A) : (∀ i, m1 !! i = m2 !! i) → m1 = m2;
  lookup_empty {A} i : (∅ : M A) !! i = None;
  lookup_partial_alter {A} f (m : M A) i :
    partial_alter f i m !! i = f (m !! i);
  lookup_partial_alter_ne {A} f (m : M A) i j :
    i ≠ j → partial_alter f i m !! j = m !! j;
  lookup_fmap {A B} (f : A → B) (m : M A) i : (f <$> m) !! i = f <$> m !! i;
  NoDup_map_to_list {A} (m : M A) : NoDup (map_to_list m);
  elem_of_map_to_list {A} (m : M A) i x :
    (i,x) ∈ map_to_list m ↔ m !! i = Some x;
  lookup_omap {A B} (f : A → option B) (m : M A) i :
    omap f m !! i = m !! i ≫= f;
  lookup_merge {A B C} (f : option A → option B → option C)
      `{!DiagNone f} (m1 : M A) (m2 : M B) i :
    merge f m1 m2 !! i = f (m1 !! i) (m2 !! i)
}.

(** * Derived operations *)
(** All of the following functions are defined in a generic way for arbitrary
finite map implementations. These generic implementations do not cause a
significant performance loss, which justifies including them in the finite map
interface as primitive operations. *)
Instance map_insert `{PartialAlter K A M} : Insert K A M :=
  λ i x, partial_alter (λ _, Some x) i.
Instance map_alter `{PartialAlter K A M} : Alter K A M :=
  λ f, partial_alter (fmap f).
Instance map_delete `{PartialAlter K A M} : Delete K M :=
  partial_alter (λ _, None).
Instance map_singleton `{PartialAlter K A M, Empty M} :
  SingletonM K A M := λ i x, <[i:=x]> ∅.

Definition list_to_map `{Insert K A M, Empty M} : list (K * A) → M :=
  fold_right (λ p, <[p.1:=p.2]>) ∅.

Instance map_size `{FinMapToList K A M} : Size M := λ m, length (map_to_list m).

Definition map_to_set `{FinMapToList K A M,
    Singleton B C, Empty C, Union C} (f : K → A → B) (m : M) : C :=
  list_to_set (curry f <$> map_to_list m).
Definition set_to_map `{Elements B C, Insert K A M, Empty M}
    (f : B → K * A) (X : C) : M :=
  list_to_map (f <$> elements X).

Instance map_union_with `{Merge M} {A} : UnionWith A (M A) :=
  λ f, merge (union_with f).
Instance map_intersection_with `{Merge M} {A} : IntersectionWith A (M A) :=
  λ f, merge (intersection_with f).
Instance map_difference_with `{Merge M} {A} : DifferenceWith A (M A) :=
  λ f, merge (difference_with f).

(** Higher precedence to make sure it's not used for other types with a [Lookup]
instance, such as lists. *)
Instance map_equiv `{∀ A, Lookup K A (M A), Equiv A} : Equiv (M A) | 20 :=
  λ m1 m2, ∀ i, m1 !! i ≡ m2 !! i.

Definition map_Forall `{Lookup K A M} (P : K → A → Prop) : M → Prop :=
  λ m, ∀ i x, m !! i = Some x → P i x.

Definition map_relation `{∀ A, Lookup K A (M A)} {A B} (R : A → B → Prop)
    (P : A → Prop) (Q : B → Prop) (m1 : M A) (m2 : M B) : Prop := ∀ i,
  option_relation R P Q (m1 !! i) (m2 !! i).
Definition map_included `{∀ A, Lookup K A (M A)} {A}
  (R : relation A) : relation (M A) := map_relation R (λ _, False) (λ _, True).
Definition map_disjoint `{∀ A, Lookup K A (M A)} {A} : relation (M A) :=
  map_relation (λ _ _, False) (λ _, True) (λ _, True).
Infix "##ₘ" := map_disjoint (at level 70) : stdpp_scope.
Hint Extern 0 (_ ##ₘ _) => symmetry; eassumption : core.
Notation "( m ##ₘ.)" := (map_disjoint m) (only parsing) : stdpp_scope.
Notation "(.##ₘ m )" := (λ m2, m2 ##ₘ m) (only parsing) : stdpp_scope.
Instance map_subseteq `{∀ A, Lookup K A (M A)} {A} : SubsetEq (M A) :=
  map_included (=).

(** The union of two finite maps only has a meaningful definition for maps
that are disjoint. However, as working with partial functions is inconvenient
in Coq, we define the union as a total function. In case both finite maps
have a value at the same index, we take the value of the first map. *)
Instance map_union `{Merge M} {A} : Union (M A) := union_with (λ x _, Some x).
Instance map_intersection `{Merge M} {A} : Intersection (M A) :=
  intersection_with (λ x _, Some x).

(** The difference operation removes all values from the first map whose
index contains a value in the second map as well. *)
Instance map_difference `{Merge M} {A} : Difference (M A) :=
  difference_with (λ _ _, None).

(** A stronger variant of map that allows the mapped function to use the index
of the elements. Implemented by conversion to lists, so not very efficient. *)
Definition map_imap `{∀ A, Insert K A (M A), ∀ A, Empty (M A),
    ∀ A, FinMapToList K A (M A)} {A B} (f : K → A → option B) (m : M A) : M B :=
  list_to_map (omap (λ ix, (fst ix ,.) <$> curry f ix) (map_to_list m)).

(* The zip operation on maps combines two maps key-wise. The keys of resulting
map correspond to the keys that are in both maps. *)
Definition map_zip_with `{Merge M} {A B C} (f : A → B → C) : M A → M B → M C :=
  merge (λ mx my,
    match mx, my with Some x, Some y => Some (f x y) | _, _ => None end).
Notation map_zip := (map_zip_with pair).

(* Folds a function [f] over a map. The order in which the function is called
is unspecified. *)
Definition map_fold `{FinMapToList K A M} {B}
  (f : K → A → B → B) (b : B) : M → B := foldr (curry f) b ∘ map_to_list.

Instance map_filter `{FinMapToList K A M, Insert K A M, Empty M} : Filter (K * A) M :=
  λ P _, map_fold (λ k v m, if decide (P (k,v)) then <[k := v]>m else m) ∅.

Fixpoint map_seq `{Insert nat A M, Empty M} (start : nat) (xs : list A) : M :=
  match xs with
  | [] => ∅
  | x :: xs => <[start:=x]> (map_seq (S start) xs)
  end.

Instance finmap_lookup_total `{!Lookup K A (M A), !Inhabited A} :
  LookupTotal K A (M A) | 20 := λ i m, default inhabitant (m !! i).
Typeclasses Opaque finmap_lookup_total.

(** * Theorems *)
Section theorems.
Context `{FinMap K M}.

(** ** Setoids *)
Section setoid.
  Context `{Equiv A}.

  Lemma map_equiv_lookup_l (m1 m2 : M A) i x :
    m1 ≡ m2 → m1 !! i = Some x → ∃ y, m2 !! i = Some y ∧ x ≡ y.
  Proof. generalize (equiv_Some_inv_l (m1 !! i) (m2 !! i) x); naive_solver. Qed.

  Global Instance map_equivalence : Equivalence (≡@{A}) → Equivalence (≡@{M A}).
  Proof.
    split.
    - by intros m i.
    - by intros m1 m2 ? i.
    - by intros m1 m2 m3 ?? i; trans (m2 !! i).
  Qed.
  Global Instance lookup_proper (i : K) : Proper ((≡@{M A}) ==> (≡)) (lookup i).
  Proof. by intros m1 m2 Hm. Qed.
  Global Instance lookup_total_proper (i : K) `{!Inhabited A} :
    Proper (≡@{A}) inhabitant →
    Proper ((≡@{M A}) ==> (≡)) (lookup_total i).
  Proof.
    intros ? m1 m2 Hm. unfold lookup_total, finmap_lookup_total.
    apply from_option_proper; auto. by intros ??.
  Qed.
  Global Instance partial_alter_proper :
    Proper (((≡) ==> (≡)) ==> (=) ==> (≡) ==> (≡@{M A})) partial_alter.
  Proof.
    by intros f1 f2 Hf i ? <- m1 m2 Hm j; destruct (decide (i = j)) as [->|];
      rewrite ?lookup_partial_alter, ?lookup_partial_alter_ne by done;
      try apply Hf; apply lookup_proper.
  Qed.
  Global Instance insert_proper (i : K) :
    Proper ((≡) ==> (≡) ==> (≡@{M A})) (insert i).
  Proof. by intros ???; apply partial_alter_proper; [constructor|]. Qed.
  Global Instance singletonM_proper k : Proper ((≡) ==> (≡@{M A})) (singletonM k).
  Proof.
    intros ???; apply insert_proper; [done|].
    intros ?. rewrite lookup_empty; constructor.
  Qed.
  Global Instance delete_proper (i : K) : Proper ((≡) ==> (≡@{M A})) (delete i).
  Proof. by apply partial_alter_proper; [constructor|]. Qed.
  Global Instance alter_proper :
    Proper (((≡) ==> (≡)) ==> (=) ==> (≡) ==> (≡@{M A})) alter.
  Proof.
    intros ?? Hf; apply partial_alter_proper.
    by destruct 1; constructor; apply Hf.
  Qed.
  Lemma merge_ext `{Equiv B, Equiv C} (f g : option A → option B → option C)
      `{!DiagNone f, !DiagNone g} :
    ((≡) ==> (≡) ==> (≡))%signature f g →
    ((≡) ==> (≡) ==> (≡@{M _}))%signature (merge f) (merge g).
  Proof.
    by intros Hf ?? Hm1 ?? Hm2 i; rewrite !lookup_merge by done; apply Hf.
  Qed.
  Global Instance union_with_proper :
    Proper (((≡) ==> (≡) ==> (≡)) ==> (≡) ==> (≡) ==>(≡@{M A})) union_with.
  Proof.
    intros ?? Hf ?? Hm1 ?? Hm2 i; apply (merge_ext _ _); auto.
    by do 2 destruct 1; first [apply Hf | constructor].
  Qed.
  Global Instance map_leibniz `{!LeibnizEquiv A} : LeibnizEquiv (M A).
  Proof. intros m1 m2 Hm; apply map_eq; intros i. apply leibniz_equiv, Hm. Qed.
  Lemma map_equiv_empty (m : M A) : m ≡ ∅ ↔ m = ∅.
  Proof.
    split; [intros Hm; apply map_eq; intros i|intros ->].
    - generalize (Hm i). by rewrite lookup_empty, equiv_None.
    - intros ?. rewrite lookup_empty; constructor.
  Qed.
  Global Instance map_fmap_proper `{Equiv B} (f : A → B) :
    Proper ((≡) ==> (≡)) f → Proper ((≡) ==> (≡@{M _})) (fmap f).
  Proof.
    intros ? m m' ? k; rewrite !lookup_fmap. by apply option_fmap_proper.
  Qed.
  Global Instance map_zip_with_proper `{Equiv B, Equiv C} (f : A → B → C) :
    Proper ((≡) ==> (≡) ==> (≡)) f →
    Proper ((≡) ==> (≡) ==> (≡)) (map_zip_with (M:=M) f).
  Proof.
    intros Hf m1 m1' Hm1 m2 m2' Hm2. apply merge_ext; try done.
    destruct 1; destruct 1; repeat f_equiv; constructor || done.
  Qed.
End setoid.

(** ** General properties *)
Lemma map_eq_iff {A} (m1 m2 : M A) : m1 = m2 ↔ ∀ i, m1 !! i = m2 !! i.
Proof. split. by intros ->. apply map_eq. Qed.
Lemma map_subseteq_spec {A} (m1 m2 : M A) :
  m1 ⊆ m2 ↔ ∀ i x, m1 !! i = Some x → m2 !! i = Some x.
Proof.
  unfold subseteq, map_subseteq, map_relation. split; intros Hm i;
    specialize (Hm i); destruct (m1 !! i), (m2 !! i); naive_solver.
Qed.
Global Instance map_included_preorder {A} (R : relation A) :
  PreOrder R → PreOrder (map_included R : relation (M A)).
Proof.
  split; [intros m i; by destruct (m !! i); simpl|].
  intros m1 m2 m3 Hm12 Hm23 i; specialize (Hm12 i); specialize (Hm23 i).
  destruct (m1 !! i), (m2 !! i), (m3 !! i); simplify_eq/=;
    done || etrans; eauto.
Qed.
Global Instance map_subseteq_po : PartialOrder (⊆@{M A}).
Proof.
  split; [apply _|].
  intros m1 m2; rewrite !map_subseteq_spec.
  intros; apply map_eq; intros i; apply option_eq; naive_solver.
Qed.
Lemma lookup_total_alt `{!Inhabited A} (m : M A) i :
  m !!! i = default inhabitant (m !! i).
Proof. reflexivity. Qed.
Lemma lookup_total_correct `{!Inhabited A} (m : M A) i x :
  m !! i = Some x → m !!! i = x.
Proof. rewrite lookup_total_alt. by intros ->. Qed.
Lemma lookup_lookup_total `{!Inhabited A} (m : M A) i :
  is_Some (m !! i) → m !! i = Some (m !!! i).
Proof. intros [x Hx]. by rewrite (lookup_total_correct m i x). Qed.
Lemma lookup_weaken {A} (m1 m2 : M A) i x :
  m1 !! i = Some x → m1 ⊆ m2 → m2 !! i = Some x.
Proof. rewrite !map_subseteq_spec. auto. Qed.
Lemma lookup_weaken_is_Some {A} (m1 m2 : M A) i :
  is_Some (m1 !! i) → m1 ⊆ m2 → is_Some (m2 !! i).
Proof. inversion 1. eauto using lookup_weaken. Qed.
Lemma lookup_weaken_None {A} (m1 m2 : M A) i :
  m2 !! i = None → m1 ⊆ m2 → m1 !! i = None.
Proof.
  rewrite map_subseteq_spec, !eq_None_not_Some.
  intros Hm2 Hm [??]; destruct Hm2; eauto.
Qed.
Lemma lookup_weaken_inv {A} (m1 m2 : M A) i x y :
  m1 !! i = Some x → m1 ⊆ m2 → m2 !! i = Some y → x = y.
Proof. intros Hm1 ? Hm2. eapply lookup_weaken in Hm1; eauto. congruence. Qed.
Lemma lookup_ne {A} (m : M A) i j : m !! i ≠ m !! j → i ≠ j.
Proof. congruence. Qed.
Lemma map_empty {A} (m : M A) : (∀ i, m !! i = None) → m = ∅.
Proof. intros Hm. apply map_eq. intros. by rewrite Hm, lookup_empty. Qed.
Lemma lookup_empty_is_Some {A} i : ¬is_Some ((∅ : M A) !! i).
Proof. rewrite lookup_empty. by inversion 1. Qed.
Lemma lookup_empty_Some {A} i (x : A) : ¬(∅ : M A) !! i = Some x.
Proof. by rewrite lookup_empty. Qed.
Lemma loopup_total_empty `{!Inhabited A} i : (∅ : M A) !!! i = inhabitant.
Proof. by rewrite lookup_total_alt, lookup_empty. Qed.
Lemma map_subset_empty {A} (m : M A) : m ⊄ ∅.
Proof.
  intros [_ []]. rewrite map_subseteq_spec. intros ??. by rewrite lookup_empty.
Qed.
Lemma map_fmap_empty {A B} (f : A → B) : f <$> (∅ : M A) = ∅.
Proof. by apply map_eq; intros i; rewrite lookup_fmap, !lookup_empty. Qed.
Lemma map_fmap_empty_inv {A B} (f : A → B) m : f <$> m = ∅ → m = ∅.
Proof.
  intros Hm. apply map_eq; intros i. generalize (f_equal (lookup i) Hm).
  by rewrite lookup_fmap, !lookup_empty, fmap_None.
Qed.

Lemma map_subset_alt {A} (m1 m2 : M A) :
  m1 ⊂ m2 ↔ m1 ⊆ m2 ∧ ∃ i, m1 !! i = None ∧ is_Some (m2 !! i).
Proof.
  rewrite strict_spec_alt. split.
  - intros [? Heq]; split; [done|].
    destruct (decide (Exists (λ ix, m1 !! ix.1 = None) (map_to_list m2)))
      as [[[i x] [?%elem_of_map_to_list ?]]%Exists_exists
         |Hm%(not_Exists_Forall _)]; [eauto|].
    destruct Heq; apply (anti_symm _), map_subseteq_spec; [done|intros i x Hi].
    assert (is_Some (m1 !! i)) as [x' ?].
    { by apply not_eq_None_Some,
        (proj1 (Forall_forall _ _) Hm (i,x)), elem_of_map_to_list. }
    by rewrite <-(lookup_weaken_inv m1 m2 i x' x).
  - intros [? (i&?&x&?)]; split; [done|]. congruence.
Qed.

(** ** Properties of the [partial_alter] operation *)
Lemma partial_alter_ext {A} (f g : option A → option A) (m : M A) i :
  (∀ x, m !! i = x → f x = g x) → partial_alter f i m = partial_alter g i m.
Proof.
  intros. apply map_eq; intros j. by destruct (decide (i = j)) as [->|?];
    rewrite ?lookup_partial_alter, ?lookup_partial_alter_ne; auto.
Qed.
Lemma partial_alter_compose {A} f g (m : M A) i:
  partial_alter (f ∘ g) i m = partial_alter f i (partial_alter g i m).
Proof.
  intros. apply map_eq. intros ii. by destruct (decide (i = ii)) as [->|?];
    rewrite ?lookup_partial_alter, ?lookup_partial_alter_ne.
Qed.
Lemma partial_alter_commute {A} f g (m : M A) i j :
  i ≠ j → partial_alter f i (partial_alter g j m) =
    partial_alter g j (partial_alter f i m).
Proof.
  intros. apply map_eq; intros jj. destruct (decide (jj = j)) as [->|?].
  { by rewrite lookup_partial_alter_ne,
      !lookup_partial_alter, lookup_partial_alter_ne. }
  destruct (decide (jj = i)) as [->|?].
  - by rewrite lookup_partial_alter,
     !lookup_partial_alter_ne, lookup_partial_alter by congruence.
  - by rewrite !lookup_partial_alter_ne by congruence.
Qed.
Lemma partial_alter_self_alt {A} (m : M A) i x :
  x = m !! i → partial_alter (λ _, x) i m = m.
Proof.
  intros. apply map_eq. intros ii. by destruct (decide (i = ii)) as [->|];
    rewrite ?lookup_partial_alter, ?lookup_partial_alter_ne.
Qed.
Lemma partial_alter_self {A} (m : M A) i : partial_alter (λ _, m !! i) i m = m.
Proof. by apply partial_alter_self_alt. Qed.
Lemma partial_alter_subseteq {A} f (m : M A) i :
  m !! i = None → m ⊆ partial_alter f i m.
Proof.
  rewrite map_subseteq_spec. intros Hi j x Hj.
  rewrite lookup_partial_alter_ne; congruence.
Qed.
Lemma partial_alter_subset {A} f (m : M A) i :
  m !! i = None → is_Some (f (m !! i)) → m ⊂ partial_alter f i m.
Proof.
  intros Hi Hfi. apply map_subset_alt; split; [by apply partial_alter_subseteq|].
  exists i. by rewrite lookup_partial_alter.
Qed.

(** ** Properties of the [alter] operation *)
Lemma lookup_alter {A} (f : A → A) (m : M A) i : alter f i m !! i = f <$> m !! i.
Proof. unfold alter. apply lookup_partial_alter. Qed.
Lemma lookup_alter_ne {A} (f : A → A) (m : M A) i j :
  i ≠ j → alter f i m !! j = m !! j.
Proof. unfold alter. apply lookup_partial_alter_ne. Qed.
Lemma alter_ext {A} (f g : A → A) (m : M A) i :
  (∀ x, m !! i = Some x → f x = g x) → alter f i m = alter g i m.
Proof. intro. apply partial_alter_ext. intros [x|] ?; f_equal/=; auto. Qed.
Lemma alter_compose {A} (f g : A → A) (m : M A) i:
  alter (f ∘ g) i m = alter f i (alter g i m).
Proof.
  unfold alter, map_alter. rewrite <-partial_alter_compose.
  apply partial_alter_ext. by intros [?|].
Qed.
Lemma alter_commute {A} (f g : A → A) (m : M A) i j :
  i ≠ j → alter f i (alter g j m) = alter g j (alter f i m).
Proof. apply partial_alter_commute. Qed.
Lemma lookup_alter_Some {A} (f : A → A) (m : M A) i j y :
  alter f i m !! j = Some y ↔
    (i = j ∧ ∃ x, m !! j = Some x ∧ y = f x) ∨ (i ≠ j ∧ m !! j = Some y).
Proof.
  destruct (decide (i = j)) as [->|?].
  - rewrite lookup_alter. naive_solver (simplify_option_eq; eauto).
  - rewrite lookup_alter_ne by done. naive_solver.
Qed.
Lemma lookup_alter_None {A} (f : A → A) (m : M A) i j :
  alter f i m !! j = None ↔ m !! j = None.
Proof.
  by destruct (decide (i = j)) as [->|?];
    rewrite ?lookup_alter, ?fmap_None, ?lookup_alter_ne.
Qed.
Lemma lookup_alter_is_Some {A} (f : A → A) (m : M A) i j :
  is_Some (alter f i m !! j) ↔ is_Some (m !! j).
Proof. by rewrite <-!not_eq_None_Some, lookup_alter_None. Qed.
Lemma alter_id {A} (f : A → A) (m : M A) i :
  (∀ x, m !! i = Some x → f x = x) → alter f i m = m.
Proof.
  intros Hi; apply map_eq; intros j; destruct (decide (i = j)) as [->|?].
  { rewrite lookup_alter; destruct (m !! j); f_equal/=; auto. }
  by rewrite lookup_alter_ne by done.
Qed.
Lemma alter_mono {A} f (m1 m2 : M A) i : m1 ⊆ m2 → alter f i m1 ⊆ alter f i m2.
Proof.
  rewrite !map_subseteq_spec. intros ? j x.
  rewrite !lookup_alter_Some. naive_solver.
Qed.
Lemma alter_strict_mono {A} f (m1 m2 : M A) i :
  m1 ⊂ m2 → alter f i m1 ⊂ alter f i m2.
Proof.
  rewrite !map_subset_alt.
  intros [? (j&?&?)]; split; auto using alter_mono.
  exists j. by rewrite lookup_alter_None, lookup_alter_is_Some.
Qed.

(** ** Properties of the [delete] operation *)
Lemma lookup_delete {A} (m : M A) i : delete i m !! i = None.
Proof. apply lookup_partial_alter. Qed.
Lemma lookup_total_delete `{!Inhabited A} (m : M A) i :
  delete i m !!! i = inhabitant.
Proof. by rewrite lookup_total_alt, lookup_delete. Qed.
Lemma lookup_delete_ne {A} (m : M A) i j : i ≠ j → delete i m !! j = m !! j.
Proof. apply lookup_partial_alter_ne. Qed.
Lemma lookup_total_delete_ne `{!Inhabited A} (m : M A) i j :
  i ≠ j → delete i m !!! j = m !!! j.
Proof. intros. by rewrite lookup_total_alt, lookup_delete_ne. Qed.
Lemma lookup_delete_Some {A} (m : M A) i j y :
  delete i m !! j = Some y ↔ i ≠ j ∧ m !! j = Some y.
Proof.
  split.
  - destruct (decide (i = j)) as [->|?];
      rewrite ?lookup_delete, ?lookup_delete_ne; intuition congruence.
  - intros [??]. by rewrite lookup_delete_ne.
Qed.
Lemma lookup_delete_is_Some {A} (m : M A) i j :
  is_Some (delete i m !! j) ↔ i ≠ j ∧ is_Some (m !! j).
Proof. unfold is_Some; setoid_rewrite lookup_delete_Some; naive_solver. Qed.
Lemma lookup_delete_None {A} (m : M A) i j :
  delete i m !! j = None ↔ i = j ∨ m !! j = None.
Proof.
  destruct (decide (i = j)) as [->|?];
    rewrite ?lookup_delete, ?lookup_delete_ne; tauto.
Qed.
Lemma delete_empty {A} i : delete i (∅ : M A) = ∅.
Proof. rewrite <-(partial_alter_self ∅) at 2. by rewrite lookup_empty. Qed.
Lemma delete_commute {A} (m : M A) i j :
  delete i (delete j m) = delete j (delete i m).
Proof. destruct (decide (i = j)). by subst. by apply partial_alter_commute. Qed.
Lemma delete_insert_ne {A} (m : M A) i j x :
  i ≠ j → delete i (<[j:=x]>m) = <[j:=x]>(delete i m).
Proof. intro. by apply partial_alter_commute. Qed.
Lemma delete_notin {A} (m : M A) i : m !! i = None → delete i m = m.
Proof.
  intros. apply map_eq. intros j. by destruct (decide (i = j)) as [->|?];
    rewrite ?lookup_delete, ?lookup_delete_ne.
Qed.
Lemma delete_idemp {A} (m : M A) i :
  delete i (delete i m) = delete i m.
Proof. by setoid_rewrite <-partial_alter_compose. Qed.
Lemma delete_partial_alter {A} (m : M A) i f :
  m !! i = None → delete i (partial_alter f i m) = m.
Proof.
  intros. unfold delete, map_delete. rewrite <-partial_alter_compose.
  unfold compose. by apply partial_alter_self_alt.
Qed.
Lemma delete_insert {A} (m : M A) i x :
  m !! i = None → delete i (<[i:=x]>m) = m.
Proof. apply delete_partial_alter. Qed.
Lemma delete_insert_delete {A} (m : M A) i x :
  delete i (<[i:=x]>m) = delete i m.
Proof. by setoid_rewrite <-partial_alter_compose. Qed.
Lemma insert_delete {A} (m : M A) i x : <[i:=x]>(delete i m) = <[i:=x]> m.
Proof. symmetry; apply (partial_alter_compose (λ _, Some x)). Qed.
Lemma delete_subseteq {A} (m : M A) i : delete i m ⊆ m.
Proof.
  rewrite !map_subseteq_spec. intros j x. rewrite lookup_delete_Some. tauto.
Qed.
Lemma delete_subset {A} (m : M A) i : is_Some (m !! i) → delete i m ⊂ m.
Proof.
  intros [x ?]; apply map_subset_alt; split; [apply delete_subseteq|].
  exists i. rewrite lookup_delete; eauto.
Qed.
Lemma delete_mono {A} (m1 m2 : M A) i : m1 ⊆ m2 → delete i m1 ⊆ delete i m2.
Proof.
  rewrite !map_subseteq_spec. intros ? j x.
  rewrite !lookup_delete_Some. intuition eauto.
Qed.

(** ** Properties of the [insert] operation *)
Lemma lookup_insert {A} (m : M A) i x : <[i:=x]>m !! i = Some x.
Proof. unfold insert. apply lookup_partial_alter. Qed.
Lemma lookup_total_insert `{!Inhabited A} (m : M A) i x : <[i:=x]>m !!! i = x.
Proof. by rewrite lookup_total_alt, lookup_insert. Qed.
Lemma lookup_insert_rev {A}  (m : M A) i x y : <[i:=x]>m !! i = Some y → x = y.
Proof. rewrite lookup_insert. congruence. Qed.
Lemma lookup_insert_ne {A} (m : M A) i j x : i ≠ j → <[i:=x]>m !! j = m !! j.
Proof. unfold insert. apply lookup_partial_alter_ne. Qed.
Lemma lookup_total_insert_ne `{!Inhabited A} (m : M A) i j x :
  i ≠ j → <[i:=x]>m !!! j = m !!! j.
Proof. intros. by rewrite lookup_total_alt, lookup_insert_ne. Qed.
Lemma insert_insert {A} (m : M A) i x y : <[i:=x]>(<[i:=y]>m) = <[i:=x]>m.
Proof. unfold insert, map_insert. by rewrite <-partial_alter_compose. Qed.
Lemma insert_commute {A} (m : M A) i j x y :
  i ≠ j → <[i:=x]>(<[j:=y]>m) = <[j:=y]>(<[i:=x]>m).
Proof. apply partial_alter_commute. Qed.
Lemma lookup_insert_Some {A} (m : M A) i j x y :
  <[i:=x]>m !! j = Some y ↔ (i = j ∧ x = y) ∨ (i ≠ j ∧ m !! j = Some y).
Proof.
  split.
  - destruct (decide (i = j)) as [->|?];
      rewrite ?lookup_insert, ?lookup_insert_ne; intuition congruence.
  - intros [[-> ->]|[??]]; [apply lookup_insert|]. by rewrite lookup_insert_ne.
Qed.
Lemma lookup_insert_is_Some {A} (m : M A) i j x :
  is_Some (<[i:=x]>m !! j) ↔ i = j ∨ i ≠ j ∧ is_Some (m !! j).
Proof. unfold is_Some; setoid_rewrite lookup_insert_Some; naive_solver. Qed.
Lemma lookup_insert_is_Some' {A} (m : M A) i j x :
  is_Some (<[i:=x]>m !! j) ↔ i = j ∨ is_Some (m !! j).
Proof. rewrite lookup_insert_is_Some. destruct (decide (i=j)); naive_solver. Qed.
Lemma lookup_insert_None {A} (m : M A) i j x :
  <[i:=x]>m !! j = None ↔ m !! j = None ∧ i ≠ j.
Proof.
  split; [|by intros [??]; rewrite lookup_insert_ne].
  destruct (decide (i = j)) as [->|];
    rewrite ?lookup_insert, ?lookup_insert_ne; intuition congruence.
Qed.
Lemma insert_id {A} (m : M A) i x : m !! i = Some x → <[i:=x]>m = m.
Proof.
  intros; apply map_eq; intros j; destruct (decide (i = j)) as [->|];
    by rewrite ?lookup_insert, ?lookup_insert_ne by done.
Qed.
Lemma insert_included {A} R `{!Reflexive R} (m : M A) i x :
  (∀ y, m !! i = Some y → R y x) → map_included R m (<[i:=x]>m).
Proof.
  intros ? j; destruct (decide (i = j)) as [->|].
  - rewrite lookup_insert. destruct (m !! j); simpl; eauto.
  - rewrite lookup_insert_ne by done. by destruct (m !! j); simpl.
Qed.
Lemma insert_empty {A} i (x : A) : <[i:=x]>(∅ : M A) = {[i := x]}.
Proof. done. Qed.
Lemma insert_non_empty {A} (m : M A) i x : <[i:=x]>m ≠ ∅.
Proof.
  intros Hi%(f_equal (.!! i)). by rewrite lookup_insert, lookup_empty in Hi.
Qed.

Lemma insert_subseteq {A} (m : M A) i x : m !! i = None → m ⊆ <[i:=x]>m.
Proof. apply partial_alter_subseteq. Qed.
Lemma insert_subset {A} (m : M A) i x : m !! i = None → m ⊂ <[i:=x]>m.
Proof. intro. apply partial_alter_subset; eauto. Qed.
Lemma insert_mono {A} (m1 m2 : M A) i x : m1 ⊆ m2 → <[i:=x]> m1 ⊆ <[i:=x]>m2.
Proof.
  rewrite !map_subseteq_spec.
  intros Hm j y. rewrite !lookup_insert_Some. naive_solver.
Qed.
Lemma insert_subseteq_r {A} (m1 m2 : M A) i x :
  m1 !! i = None → m1 ⊆ m2 → m1 ⊆ <[i:=x]>m2.
Proof.
  intros. trans (<[i:=x]> m1); eauto using insert_subseteq, insert_mono.
Qed.

Lemma insert_delete_subseteq {A} (m1 m2 : M A) i x :
  m1 !! i = None → <[i:=x]> m1 ⊆ m2 → m1 ⊆ delete i m2.
Proof.
  rewrite !map_subseteq_spec. intros Hi Hix j y Hj.
  destruct (decide (i = j)) as [->|]; [congruence|].
  rewrite lookup_delete_ne by done.
  apply Hix; by rewrite lookup_insert_ne by done.
Qed.
Lemma delete_insert_subseteq {A} (m1 m2 : M A) i x :
  m1 !! i = Some x → delete i m1 ⊆ m2 → m1 ⊆ <[i:=x]> m2.
Proof.
  rewrite !map_subseteq_spec.
  intros Hix Hi j y Hj. destruct (decide (i = j)) as [->|?].
  - rewrite lookup_insert. congruence.
  - rewrite lookup_insert_ne by done. apply Hi. by rewrite lookup_delete_ne.
Qed.
Lemma insert_delete_subset {A} (m1 m2 : M A) i x :
  m1 !! i = None → <[i:=x]> m1 ⊂ m2 → m1 ⊂ delete i m2.
Proof.
  intros ? [Hm12 Hm21]; split; [eauto using insert_delete_subseteq|].
  contradict Hm21. apply delete_insert_subseteq; auto.
  eapply lookup_weaken, Hm12. by rewrite lookup_insert.
Qed.
Lemma insert_subset_inv {A} (m1 m2 : M A) i x :
  m1 !! i = None → <[i:=x]> m1 ⊂ m2 →
  ∃ m2', m2 = <[i:=x]>m2' ∧ m1 ⊂ m2' ∧ m2' !! i = None.
Proof.
  intros Hi Hm1m2. exists (delete i m2). split_and?.
  - rewrite insert_delete, insert_id. done.
    eapply lookup_weaken, strict_include; eauto. by rewrite lookup_insert.
  - eauto using insert_delete_subset.
  - by rewrite lookup_delete.
Qed.

(** ** Properties of the singleton maps *)
Lemma lookup_singleton_Some {A} i j (x y : A) :
  ({[i := x]} : M A) !! j = Some y ↔ i = j ∧ x = y.
Proof.
  rewrite <-insert_empty,lookup_insert_Some, lookup_empty; intuition congruence.
Qed.
Lemma lookup_singleton_None {A} i j (x : A) :
  ({[i := x]} : M A) !! j = None ↔ i ≠ j.
Proof. rewrite <-insert_empty,lookup_insert_None, lookup_empty; tauto. Qed.
Lemma lookup_singleton {A} i (x : A) : ({[i := x]} : M A) !! i = Some x.
Proof. by rewrite lookup_singleton_Some. Qed.
Lemma lookup_total_singleton `{!Inhabited A} i (x : A) :
  ({[i := x]} : M A) !!! i = x.
Proof. by rewrite lookup_total_alt, lookup_singleton. Qed.
Lemma lookup_singleton_ne {A} i j (x : A) :
  i ≠ j → ({[i := x]} : M A) !! j = None.
Proof. by rewrite lookup_singleton_None. Qed.
Lemma lookup_total_singleton_ne `{!Inhabited A} i j (x : A) :
  i ≠ j → ({[i := x]} : M A) !!! j = inhabitant.
Proof. intros. by rewrite lookup_total_alt, lookup_singleton_ne. Qed.
Lemma map_non_empty_singleton {A} i (x : A) : {[i := x]} ≠ (∅ : M A).
Proof.
  intros Hix. apply (f_equal (.!! i)) in Hix.
  by rewrite lookup_empty, lookup_singleton in Hix.
Qed.
Lemma insert_singleton {A} i (x y : A) : <[i:=y]>({[i := x]} : M A) = {[i := y]}.
Proof.
  unfold singletonM, map_singleton, insert, map_insert.
  by rewrite <-partial_alter_compose.
Qed.
Lemma alter_singleton {A} (f : A → A) i x :
  alter f i ({[i := x]} : M A) = {[i := f x]}.
Proof.
  intros. apply map_eq. intros i'. destruct (decide (i = i')) as [->|?].
  - by rewrite lookup_alter, !lookup_singleton.
  - by rewrite lookup_alter_ne, !lookup_singleton_ne.
Qed.
Lemma alter_singleton_ne {A} (f : A → A) i j x :
  i ≠ j → alter f i ({[j := x]} : M A) = {[j := x]}.
Proof.
  intros. apply map_eq; intros i'. by destruct (decide (i = i')) as [->|?];
    rewrite ?lookup_alter, ?lookup_singleton_ne, ?lookup_alter_ne by done.
Qed.
Lemma singleton_non_empty {A} i (x : A) : {[i:=x]} ≠ (∅ : M A).
Proof. apply insert_non_empty. Qed.
Lemma delete_singleton {A} i (x : A) : delete i {[i := x]} = (∅ : M A).
Proof. setoid_rewrite <-partial_alter_compose. apply delete_empty. Qed.
Lemma delete_singleton_ne {A} i j (x : A) :
  i ≠ j → delete i ({[j := x]} : M A) = {[j := x]}.
Proof. intro. apply delete_notin. by apply lookup_singleton_ne. Qed.

(** ** Properties of the map operations *)
Lemma fmap_empty {A B} (f : A → B) : f <$> ∅ = ∅.
Proof. apply map_empty; intros i. by rewrite lookup_fmap, lookup_empty. Qed.
Lemma omap_empty {A B} (f : A → option B) : omap f ∅ = ∅.
Proof. apply map_empty; intros i. by rewrite lookup_omap, lookup_empty. Qed.
Lemma fmap_insert {A B} (f: A → B) m i x: f <$> <[i:=x]>m = <[i:=f x]>(f <$> m).
Proof.
  apply map_eq; intros i'; destruct (decide (i' = i)) as [->|].
  - by rewrite lookup_fmap, !lookup_insert.
  - by rewrite lookup_fmap, !lookup_insert_ne, lookup_fmap by done.
Qed.
Lemma fmap_delete {A B} (f: A → B) m i: f <$> delete i m = delete i (f <$> m).
Proof.
  apply map_eq; intros i'; destruct (decide (i' = i)) as [->|].
  - by rewrite lookup_fmap, !lookup_delete.
  - by rewrite lookup_fmap, !lookup_delete_ne, lookup_fmap by done.
Qed.
Lemma omap_insert {A B} (f : A → option B) m i x y :
  f x = Some y → omap f (<[i:=x]>m) = <[i:=y]>(omap f m).
Proof.
  intros; apply map_eq; intros i'; destruct (decide (i' = i)) as [->|].
  - by rewrite lookup_omap, !lookup_insert.
  - by rewrite lookup_omap, !lookup_insert_ne, lookup_omap by done.
Qed.
Lemma map_fmap_singleton {A B} (f : A → B) i x : f <$> {[i := x]} = {[i := f x]}.
Proof.
  by unfold singletonM, map_singleton; rewrite fmap_insert, map_fmap_empty.
Qed.
Lemma omap_singleton {A B} (f : A → option B) i x y :
  f x = Some y → omap f {[ i := x ]} = {[ i := y ]}.
Proof.
  intros. unfold singletonM, map_singleton.
  by erewrite omap_insert, omap_empty by eauto.
Qed.
Lemma map_fmap_id {A} (m : M A) : id <$> m = m.
Proof. apply map_eq; intros i; by rewrite lookup_fmap, option_fmap_id. Qed.
Lemma map_fmap_compose {A B C} (f : A → B) (g : B → C) (m : M A) :
  g ∘ f <$> m = g <$> (f <$> m).
Proof. apply map_eq; intros i; by rewrite !lookup_fmap,option_fmap_compose. Qed.
Lemma map_fmap_equiv_ext {A} `{Equiv B} (f1 f2 : A → B) (m : M A) :
  (∀ i x, m !! i = Some x → f1 x ≡ f2 x) → f1 <$> m ≡ f2 <$> m.
Proof.
  intros Hi i; rewrite !lookup_fmap.
  destruct (m !! i) eqn:?; constructor; eauto.
Qed.
Lemma map_fmap_ext {A B} (f1 f2 : A → B) (m : M A) :
  (∀ i x, m !! i = Some x → f1 x = f2 x) → f1 <$> m = f2 <$> m.
Proof.
  intros Hi; apply map_eq; intros i; rewrite !lookup_fmap.
  by destruct (m !! i) eqn:?; simpl; erewrite ?Hi by eauto.
Qed.
Lemma omap_ext {A B} (f1 f2 : A → option B) (m : M A) :
  (∀ i x, m !! i = Some x → f1 x = f2 x) → omap f1 m = omap f2 m.
Proof.
  intros Hi; apply map_eq; intros i; rewrite !lookup_omap.
  by destruct (m !! i) eqn:?; simpl; erewrite ?Hi by eauto.
Qed.

Lemma map_fmap_mono {A B} (f : A → B) (m1 m2 : M A) :
  m1 ⊆ m2 → f <$> m1 ⊆ f <$> m2.
Proof.
  rewrite !map_subseteq_spec; intros Hm i x.
  rewrite !lookup_fmap, !fmap_Some. naive_solver.
Qed.
Lemma map_fmap_strict_mono {A B} (f : A → B) (m1 m2 : M A) :
  m1 ⊂ m2 → f <$> m1 ⊂ f <$> m2.
Proof.
  rewrite !map_subset_alt.
  intros [? (j&?&?)]; split; auto using map_fmap_mono.
  exists j. by rewrite !lookup_fmap, fmap_None, fmap_is_Some.
Qed.
Lemma map_omap_mono {A B} (f : A → option B) (m1 m2 : M A) :
  m1 ⊆ m2 → omap f m1 ⊆ omap f m2.
Proof.
  rewrite !map_subseteq_spec; intros Hm i x.
  rewrite !lookup_omap, !bind_Some. naive_solver.
Qed.

(** ** Properties of conversion to lists *)
Lemma elem_of_map_to_list' {A} (m : M A) ix :
  ix ∈ map_to_list m ↔ m !! ix.1 = Some (ix.2).
Proof. destruct ix as [i x]. apply elem_of_map_to_list. Qed.
Lemma map_to_list_unique {A} (m : M A) i x y :
  (i,x) ∈ map_to_list m → (i,y) ∈ map_to_list m → x = y.
Proof. rewrite !elem_of_map_to_list. congruence. Qed.
Lemma NoDup_fst_map_to_list {A} (m : M A) : NoDup ((map_to_list m).*1).
Proof. eauto using NoDup_fmap_fst, map_to_list_unique, NoDup_map_to_list. Qed.
Lemma elem_of_list_to_map_1' {A} (l : list (K * A)) i x :
  (∀ y, (i,y) ∈ l → x = y) → (i,x) ∈ l → (list_to_map l : M A) !! i = Some x.
Proof.
  induction l as [|[j y] l IH]; csimpl; [by rewrite elem_of_nil|].
  setoid_rewrite elem_of_cons.
  intros Hdup [?|?]; simplify_eq; [by rewrite lookup_insert|].
  destruct (decide (i = j)) as [->|].
  - rewrite lookup_insert; f_equal; eauto using eq_sym.
  - rewrite lookup_insert_ne by done; eauto.
Qed.
Lemma elem_of_list_to_map_1 {A} (l : list (K * A)) i x :
  NoDup (l.*1) → (i,x) ∈ l → (list_to_map l : M A) !! i = Some x.
Proof.
  intros ? Hx; apply elem_of_list_to_map_1'; eauto using NoDup_fmap_fst.
  intros y; revert Hx. rewrite !elem_of_list_lookup; intros [i' Hi'] [j' Hj'].
  cut (i' = j'); [naive_solver|]. apply NoDup_lookup with (l.*1) i;
    by rewrite ?list_lookup_fmap, ?Hi', ?Hj'.
Qed.
Lemma elem_of_list_to_map_2 {A} (l : list (K * A)) i x :
  (list_to_map l : M A) !! i = Some x → (i,x) ∈ l.
Proof.
  induction l as [|[j y] l IH]; simpl; [by rewrite lookup_empty|].
  rewrite elem_of_cons. destruct (decide (i = j)) as [->|];
    rewrite ?lookup_insert, ?lookup_insert_ne; intuition congruence.
Qed.
Lemma elem_of_list_to_map' {A} (l : list (K * A)) i x :
  (∀ x', (i,x) ∈ l → (i,x') ∈ l → x = x') →
  (i,x) ∈ l ↔ (list_to_map l : M A) !! i = Some x.
Proof. split; auto using elem_of_list_to_map_1', elem_of_list_to_map_2. Qed.
Lemma elem_of_list_to_map {A} (l : list (K * A)) i x :
  NoDup (l.*1) → (i,x) ∈ l ↔ (list_to_map l : M A) !! i = Some x.
Proof. split; auto using elem_of_list_to_map_1, elem_of_list_to_map_2. Qed.

Lemma not_elem_of_list_to_map_1 {A} (l : list (K * A)) i :
  i ∉ l.*1 → (list_to_map l : M A) !! i = None.
Proof.
  rewrite elem_of_list_fmap, eq_None_not_Some. intros Hi [x ?]; destruct Hi.
  exists (i,x); simpl; auto using elem_of_list_to_map_2.
Qed.
Lemma not_elem_of_list_to_map_2 {A} (l : list (K * A)) i :
  (list_to_map l : M A) !! i = None → i ∉ l.*1.
Proof.
  induction l as [|[j y] l IH]; csimpl; [rewrite elem_of_nil; tauto|].
  rewrite elem_of_cons. destruct (decide (i = j)); simplify_eq.
  - by rewrite lookup_insert.
  - by rewrite lookup_insert_ne; intuition.
Qed.
Lemma not_elem_of_list_to_map {A} (l : list (K * A)) i :
  i ∉ l.*1 ↔ (list_to_map l : M A) !! i = None.
Proof. red; auto using not_elem_of_list_to_map_1,not_elem_of_list_to_map_2. Qed.
Lemma list_to_map_proper {A} (l1 l2 : list (K * A)) :
  NoDup (l1.*1) → l1 ≡ₚ l2 → (list_to_map l1 : M A) = list_to_map l2.
Proof.
  intros ? Hperm. apply map_eq. intros i. apply option_eq. intros x.
  by rewrite <-!elem_of_list_to_map; rewrite <-?Hperm.
Qed.
Lemma list_to_map_inj {A} (l1 l2 : list (K * A)) :
  NoDup (l1.*1) → NoDup (l2.*1) →
  (list_to_map l1 : M A) = list_to_map l2 → l1 ≡ₚ l2.
Proof.
  intros ?? Hl1l2. apply NoDup_Permutation; [by eauto using NoDup_fmap_1..|].
  intros [i x]. by rewrite !elem_of_list_to_map, Hl1l2.
Qed.
Lemma list_to_map_to_list {A} (m : M A) : list_to_map (map_to_list m) = m.
Proof.
  apply map_eq. intros i. apply option_eq. intros x.
  by rewrite <-elem_of_list_to_map, elem_of_map_to_list
    by auto using NoDup_fst_map_to_list.
Qed.
Lemma map_to_list_to_map {A} (l : list (K * A)) :
  NoDup (l.*1) → map_to_list (list_to_map l) ≡ₚ l.
Proof. auto using list_to_map_inj, NoDup_fst_map_to_list, list_to_map_to_list. Qed.
Lemma map_to_list_inj {A} (m1 m2 : M A) :
  map_to_list m1 ≡ₚ map_to_list m2 → m1 = m2.
Proof.
  intros. rewrite <-(list_to_map_to_list m1), <-(list_to_map_to_list m2).
  auto using list_to_map_proper, NoDup_fst_map_to_list.
Qed.
Lemma list_to_map_flip {A} (m1 : M A) l2 :
  map_to_list m1 ≡ₚ l2 → m1 = list_to_map l2.
Proof.
  intros. rewrite <-(list_to_map_to_list m1).
  auto using list_to_map_proper, NoDup_fst_map_to_list.
Qed.

Lemma list_to_map_nil {A} : list_to_map [] = (∅ : M A).
Proof. done. Qed.
Lemma list_to_map_cons {A} (l : list (K * A)) i x :
  list_to_map ((i, x) :: l) = <[i:=x]>(list_to_map l : M A).
Proof. done. Qed.
Lemma list_to_map_fmap {A B} (f : A → B) l :
  list_to_map (prod_map id f <$> l) = f <$> (list_to_map l : M A).
Proof.
  induction l as [|[i x] l IH]; csimpl; rewrite ?fmap_empty; auto.
  rewrite <-list_to_map_cons; simpl. by rewrite IH, <-fmap_insert.
Qed.

Lemma map_to_list_empty {A} : map_to_list ∅ = @nil (K * A).
Proof.
  apply elem_of_nil_inv. intros [i x].
  rewrite elem_of_map_to_list. apply lookup_empty_Some.
Qed.
Lemma map_to_list_insert {A} (m : M A) i x :
  m !! i = None → map_to_list (<[i:=x]>m) ≡ₚ (i,x) :: map_to_list m.
Proof.
  intros. apply list_to_map_inj; csimpl.
  - apply NoDup_fst_map_to_list.
  - constructor; [|by auto using NoDup_fst_map_to_list].
    rewrite elem_of_list_fmap. intros [[??] [? Hlookup]]; subst; simpl in *.
    rewrite elem_of_map_to_list in Hlookup. congruence.
  - by rewrite !list_to_map_to_list.
Qed.
Lemma map_to_list_singleton {A} i (x : A) :
  map_to_list ({[i:=x]} : M A) = [(i,x)].
Proof.
  apply Permutation_singleton. unfold singletonM, map_singleton.
  by rewrite map_to_list_insert, map_to_list_empty by eauto using lookup_empty.
Qed.

Lemma map_to_list_submseteq {A} (m1 m2 : M A) :
  m1 ⊆ m2 → map_to_list m1 ⊆+ map_to_list m2.
Proof.
  intros; apply NoDup_submseteq; [by eauto using NoDup_map_to_list|].
  intros [i x]. rewrite !elem_of_map_to_list; eauto using lookup_weaken.
Qed.
Lemma map_to_list_fmap {A B} (f : A → B) (m : M A) :
  map_to_list (f <$> m) ≡ₚ prod_map id f <$> map_to_list m.
Proof.
  assert (NoDup ((prod_map id f <$> map_to_list m).*1)).
  { erewrite <-list_fmap_compose, (list_fmap_ext _ fst) by done.
    apply NoDup_fst_map_to_list. }
  rewrite <-(list_to_map_to_list m) at 1.
  by rewrite <-list_to_map_fmap, map_to_list_to_map.
Qed.

Lemma map_to_list_empty_inv_alt {A}  (m : M A) : map_to_list m ≡ₚ [] → m = ∅.
Proof. rewrite <-map_to_list_empty. apply map_to_list_inj. Qed.
Lemma map_to_list_empty_inv {A} (m : M A) : map_to_list m = [] → m = ∅.
Proof. intros Hm. apply map_to_list_empty_inv_alt. by rewrite Hm. Qed.
Lemma map_to_list_empty' {A} (m : M A) : map_to_list m = [] ↔ m = ∅.
Proof.
  split. apply map_to_list_empty_inv. intros ->. apply map_to_list_empty.
Qed.

Lemma map_to_list_insert_inv {A} (m : M A) l i x :
  map_to_list m ≡ₚ (i,x) :: l → m = <[i:=x]>(list_to_map l).
Proof.
  intros Hperm. apply map_to_list_inj.
  assert (i ∉ l.*1 ∧ NoDup (l.*1)) as [].
  { rewrite <-NoDup_cons. change (NoDup (((i,x)::l).*1)). rewrite <-Hperm.
    auto using NoDup_fst_map_to_list. }
  rewrite Hperm, map_to_list_insert, map_to_list_to_map;
    auto using not_elem_of_list_to_map_1.
Qed.

Lemma map_choose {A} (m : M A) : m ≠ ∅ → ∃ i x, m !! i = Some x.
Proof.
  intros Hemp. destruct (map_to_list m) as [|[i x] l] eqn:Hm.
  { destruct Hemp; eauto using map_to_list_empty_inv. }
  exists i, x. rewrite <-elem_of_map_to_list, Hm. by left.
Qed.

Global Instance map_eq_dec_empty {A} (m : M A) : Decision (m = ∅) | 20.
Proof.
  refine (cast_if (decide (elements m = [])));
    [apply _|by rewrite <-?map_to_list_empty' ..].
Defined.

(** Properties of the imap function *)
Lemma map_lookup_imap {A B} (f : K → A → option B) (m : M A) i :
  map_imap f m !! i = m !! i ≫= f i.
Proof.
  unfold map_imap; destruct (m !! i ≫= f i) as [y|] eqn:Hi; simpl.
  - destruct (m !! i) as [x|] eqn:?; simplify_eq/=.
    apply elem_of_list_to_map_1'.
    { intros y'; rewrite elem_of_list_omap; intros ([i' x']&Hi'&?).
      by rewrite elem_of_map_to_list in Hi'; simplify_option_eq. }
    apply elem_of_list_omap; exists (i,x); split;
      [by apply elem_of_map_to_list|by simplify_option_eq].
  - apply not_elem_of_list_to_map; rewrite elem_of_list_fmap.
    intros ([i' x]&->&Hi'); simplify_eq/=.
    rewrite elem_of_list_omap in Hi'; destruct Hi' as ([j y]&Hj&?).
    rewrite elem_of_map_to_list in Hj; simplify_option_eq.
Qed.

Lemma map_imap_Some {A} (m : M A) : map_imap (λ _, Some) m = m.
Proof.
  apply map_eq. intros i. rewrite map_lookup_imap. by destruct (m !! i).
Qed.

Lemma map_imap_insert {A B} (f : K → A → option B) (i : K) (v : A) (m : M A) :
  map_imap f (<[i:=v]> m) = match f i v with
                            | None   => delete i (map_imap f m)
                            | Some w => <[i:=w]> (map_imap f m)
                            end.
Proof.
  destruct (f i v) as [w|] eqn:Hw.
  - apply map_eq. intros k. rewrite map_lookup_imap.
    destruct (decide (k = i)) as [->|Hk_not_i].
    + by rewrite lookup_insert, lookup_insert.
    + rewrite !lookup_insert_ne by done.
      by rewrite map_lookup_imap.
  - apply map_eq. intros k. rewrite map_lookup_imap.
    destruct (decide (k = i)) as [->|Hk_not_i].
    + by rewrite lookup_insert, lookup_delete.
    + rewrite lookup_insert_ne, lookup_delete_ne by done.
      by rewrite map_lookup_imap.
Qed.

Lemma map_imap_ext {A1 A2 B} (f1 : K → A1 → option B)
    (f2 : K → A2 → option B) (m1 : M A1) (m2 : M A2) :
  (∀ k, f1 k <$> (m1 !! k) = f2 k <$> (m2 !! k)) →
  map_imap f1 m1 = map_imap f2 m2.
Proof.
  intros HExt. apply map_eq. intros i. rewrite !map_lookup_imap.
  specialize (HExt i). destruct (m1 !! i), (m2 !! i); naive_solver.
Qed.

(** ** Properties of the size operation *)
Lemma map_size_empty {A} : size (∅ : M A) = 0.
Proof. unfold size, map_size. by rewrite map_to_list_empty. Qed.
Lemma map_size_empty_inv {A} (m : M A) : size m = 0 → m = ∅.
Proof.
  unfold size, map_size. by rewrite length_zero_iff_nil, map_to_list_empty'.
Qed.
Lemma map_size_empty_iff {A} (m : M A) : size m = 0 ↔ m = ∅.
Proof. split. apply map_size_empty_inv. by intros ->; rewrite map_size_empty. Qed.
Lemma map_size_non_empty_iff {A} (m : M A) : size m ≠ 0 ↔ m ≠ ∅.
Proof. by rewrite map_size_empty_iff. Qed.

Lemma map_size_singleton {A} i (x : A) : size ({[ i := x ]} : M A) = 1.
Proof. unfold size, map_size. by rewrite map_to_list_singleton. Qed.
Lemma map_size_insert {A} i x (m : M A) :
  m !! i = None → size (<[i:=x]> m) = S (size m).
Proof. intros. unfold size, map_size. by rewrite map_to_list_insert. Qed.
Lemma map_size_fmap {A B} (f : A -> B) (m : M A) : size (f <$> m) = size m.
Proof. intros. unfold size, map_size. by rewrite map_to_list_fmap, fmap_length. Qed.

(** ** Properties of conversion from sets *)
Section set_to_map.
  Context {A : Type} `{FinSet B C}.

  Lemma lookup_set_to_map (f : B → K * A) (Y : C) i x :
    (∀ y y', y ∈ Y → y' ∈ Y → (f y).1 = (f y').1 → y = y') →
    (set_to_map f Y : M A) !! i = Some x ↔ ∃ y, y ∈ Y ∧ f y = (i,x).
  Proof.
    intros Hinj. assert (∀ x',
      (i, x) ∈ f <$> elements Y → (i, x') ∈ f <$> elements Y → x = x').
    { intros x'. intros (y&Hx&Hy)%elem_of_list_fmap (y'&Hx'&Hy')%elem_of_list_fmap.
      rewrite elem_of_elements in Hy, Hy'.
      cut (y = y'); [congruence|]. apply Hinj; auto. by rewrite <-Hx, <-Hx'. }
    unfold set_to_map; rewrite <-elem_of_list_to_map' by done.
    rewrite elem_of_list_fmap. setoid_rewrite elem_of_elements; naive_solver.
  Qed.

  Lemma elem_of_map_to_set (f : K → A → B) (m : M A) (y : B) :
    y ∈ map_to_set (C:=C) f m ↔ ∃ i x, m !! i = Some x ∧ f i x = y.
  Proof.
    unfold map_to_set; simpl.
    rewrite elem_of_list_to_set, elem_of_list_fmap. split.
    - intros ([i x] & ? & ?%elem_of_map_to_list); eauto.
    - intros (i&x&?&?). exists (i,x). by rewrite elem_of_map_to_list.
  Qed.
  Lemma map_to_set_empty (f : K → A → B) :
    map_to_set f (∅ : M A) = (∅ : C).
  Proof. unfold map_to_set; simpl. by rewrite map_to_list_empty. Qed.
  Lemma map_to_set_insert (f : K → A → B)(m : M A) i x :
    m !! i = None →
    map_to_set f (<[i:=x]>m) ≡@{C} {[f i x]} ∪ map_to_set f m.
  Proof.
    intros. unfold map_to_set; simpl. by rewrite map_to_list_insert.
  Qed.
  Lemma map_to_set_insert_L `{!LeibnizEquiv C} (f : K → A → B) (m : M A) i x :
    m !! i = None →
    map_to_set f (<[i:=x]>m) =@{C} {[f i x]} ∪ map_to_set f m.
  Proof. unfold_leibniz. apply map_to_set_insert. Qed.
End set_to_map.

Lemma lookup_set_to_map_id `{FinSet (K * A) C} (X : C) i x :
  (∀ i y y', (i,y) ∈ X → (i,y') ∈ X → y = y') →
  (set_to_map id X : M A) !! i = Some x ↔ (i,x) ∈ X.
Proof.
  intros. etrans; [apply lookup_set_to_map|naive_solver].
  intros [] [] ???; simplify_eq/=; eauto with f_equal.
Qed.

Lemma elem_of_map_to_set_pair `{FinSet (K * A) C} (m : M A) i x :
  (i,x) ∈@{C} map_to_set pair m ↔ m !! i = Some x.
Proof. rewrite elem_of_map_to_set. naive_solver. Qed.

(** ** Induction principles *)
Lemma map_ind {A} (P : M A → Prop) :
  P ∅ → (∀ i x m, m !! i = None → P m → P (<[i:=x]>m)) → ∀ m, P m.
Proof.
  intros ? Hins. cut (∀ l, NoDup (l.*1) → ∀ m, map_to_list m ≡ₚ l → P m).
  { intros help m.
    apply (help (map_to_list m)); auto using NoDup_fst_map_to_list. }
  induction l as [|[i x] l IH]; intros Hnodup m Hml.
  { apply map_to_list_empty_inv_alt in Hml. by subst. }
  inversion_clear Hnodup.
  apply map_to_list_insert_inv in Hml; subst m. apply Hins.
  - by apply not_elem_of_list_to_map_1.
  - apply IH; auto using map_to_list_to_map.
Qed.
Lemma map_to_list_length {A} (m1 m2 : M A) :
  m1 ⊂ m2 → length (map_to_list m1) < length (map_to_list m2).
Proof.
  revert m2. induction m1 as [|i x m ? IH] using map_ind.
  { intros m2 Hm2. rewrite map_to_list_empty. simpl.
    apply neq_0_lt. intros Hlen. symmetry in Hlen.
    apply nil_length_inv, map_to_list_empty_inv in Hlen.
    rewrite Hlen in Hm2. destruct (irreflexivity (⊂) ∅ Hm2). }
  intros m2 Hm2.
  destruct (insert_subset_inv m m2 i x) as (m2'&?&?&?); auto; subst.
  rewrite !map_to_list_insert; simpl; auto with arith.
Qed.
Lemma map_wf {A} : wf (⊂@{M A}).
Proof.
  apply (wf_projected (<) (length ∘ map_to_list)).
  - by apply map_to_list_length.
  - by apply lt_wf.
Qed.

(** ** The fold operation *)
Lemma map_fold_empty {A B} (f : K → A → B → B) (b : B) :
  map_fold f b ∅ = b.
Proof. unfold map_fold; simpl. by rewrite map_to_list_empty. Qed.

Lemma map_fold_insert {A B} (R : relation B) `{!PreOrder R}
    (f : K → A → B → B) (b : B) (i : K) (x : A) (m : M A) :
  (∀ j z, Proper (R ==> R) (f j z)) →
  (∀ j1 j2 z1 z2 y,
    j1 ≠ j2 → <[i:=x]> m !! j1 = Some z1 → <[i:=x]> m !! j2 = Some z2 →
    R (f j1 z1 (f j2 z2 y)) (f j2 z2 (f j1 z1 y))) →
  m !! i = None →
  R (map_fold f b (<[i:=x]> m)) (f i x (map_fold f b m)).
Proof.
  intros Hf_proper Hf Hi. unfold map_fold; simpl.
  assert (∀ kz, Proper (R ==> R) (curry f kz)) by (intros []; apply _).
  trans (foldr (curry f) b ((i, x) :: map_to_list m)); [|done].
  eapply (foldr_permutation R (curry f) b), map_to_list_insert; auto.
  intros j1 [k1 y1] j2 [k2 y2] c Hj Hj1 Hj2. apply Hf.
  - intros ->.
    eapply Hj, NoDup_lookup; [apply (NoDup_fst_map_to_list (<[i:=x]> m))| | ].
    + by rewrite list_lookup_fmap, Hj1.
    + by rewrite list_lookup_fmap, Hj2.
  - by eapply elem_of_map_to_list, elem_of_list_lookup_2.
  - by eapply elem_of_map_to_list, elem_of_list_lookup_2.
Qed.

Lemma map_fold_insert_L {A B} (f : K → A → B → B) (b : B) (i : K) (x : A) (m : M A) :
  (∀ j1 j2 z1 z2 y,
    j1 ≠ j2 → <[i:=x]> m !! j1 = Some z1 → <[i:=x]> m !! j2 = Some z2 →
    f j1 z1 (f j2 z2 y) = f j2 z2 (f j1 z1 y)) →
  m !! i = None →
  map_fold f b (<[i:=x]> m) = f i x (map_fold f b m).
Proof. apply map_fold_insert; apply _. Qed.

Lemma map_fold_ind {A B} (P : B → M A → Prop) (f : K → A → B → B) (b : B) :
  P b ∅ →
  (∀ i x m r, m !! i = None → P r m → P (f i x r) (<[i:=x]> m)) →
  ∀ m, P (map_fold f b m) m.
Proof.
  intros Hemp Hinsert.
  cut (∀ l, NoDup l →
    ∀ m, (∀ i x, m !! i = Some x ↔ (i,x) ∈ l) → P (foldr (curry f) b l) m).
  { intros help ?. apply help; [apply NoDup_map_to_list|].
    intros i x. by rewrite elem_of_map_to_list. }
  induction 1 as [|[i x] l ?? IH]; simpl.
  { intros m Hm. cut (m = ∅); [by intros ->|]. apply map_empty; intros i.
    apply eq_None_not_Some; intros [x []%Hm%elem_of_nil]. }
  intros m Hm. assert (m !! i = Some x) by (apply Hm; by left).
  rewrite <-(insert_id m i x), <-insert_delete by done.
  apply Hinsert; auto using lookup_delete.
  apply IH. intros j y. rewrite lookup_delete_Some, Hm. split.
  - by intros [? [[= ??]|?]%elem_of_cons].
  - intros ?; split; [intros ->|by right].
    assert (m !! j = Some y) by (apply Hm; by right). naive_solver.
Qed.

(** ** The filter operation *)
Section map_filter.
  Context {A} (P : K * A → Prop) `{!∀ x, Decision (P x)}.
  Implicit Types m : M A.

  Lemma map_filter_lookup_Some m i x :
    filter P m !! i = Some x ↔ m !! i = Some x ∧ P (i,x).
  Proof.
    revert m i x. apply (map_fold_ind (λ m1 m2,
      ∀ i x, m1 !! i = Some x ↔ m2 !! i = Some x ∧ P _)); intros i x.
    - rewrite lookup_empty. naive_solver.
    - intros m m' Hm Eq j y. case_decide; case (decide (j = i))as [->|?].
      + rewrite 2!lookup_insert. naive_solver.
      + rewrite !lookup_insert_ne by done. by apply Eq.
      + rewrite Eq, Hm, lookup_insert. naive_solver.
      + by rewrite lookup_insert_ne.
  Qed.

  Lemma map_filter_lookup_None m i :
    filter P m !! i = None ↔ m !! i = None ∨ ∀ x, m !! i = Some x → ¬ P (i,x).
  Proof.
    rewrite eq_None_not_Some. unfold is_Some.
    setoid_rewrite map_filter_lookup_Some. naive_solver.
  Qed.

  Lemma map_filter_lookup_eq m1 m2 :
    (∀ k x, P (k,x) → m1 !! k = Some x ↔ m2 !! k = Some x) →
    filter P m1 = filter P m2.
  Proof.
    intros HP. apply map_eq. intros i. apply option_eq; intros x.
    rewrite !map_filter_lookup_Some. naive_solver.
  Qed.

  Lemma map_filter_insert m i x :
    P (i,x) → filter P (<[i:=x]> m) = <[i:=x]> (filter P m).
  Proof.
    intros HP. apply map_eq. intros j. apply option_eq; intros y.
    destruct (decide (j = i)) as [->|?].
    - rewrite map_filter_lookup_Some, !lookup_insert. naive_solver.
    - rewrite lookup_insert_ne, !map_filter_lookup_Some, lookup_insert_ne by done.
      naive_solver.
  Qed.

  Lemma map_filter_insert_not' m i x :
    ¬ P (i, x) → (∀ y, m !! i = Some y → ¬ P (i, y)) →
    filter P (<[i:=x]> m) = filter P m.
  Proof.
    intros Hx HP. apply map_filter_lookup_eq. intros j y Hy.
    rewrite lookup_insert_Some. naive_solver.
  Qed.

  Lemma map_filter_insert_not m i x :
    (∀ y, ¬ P (i, y)) → filter P (<[i:=x]> m) = filter P m.
  Proof. intros HP. by apply map_filter_insert_not'. Qed.

  Lemma map_filter_delete m i : filter P (delete i m) = delete i (filter P m).
  Proof.
    apply map_eq. intros j. apply option_eq; intros y.
    destruct (decide (j = i)) as [->|?].
    - rewrite map_filter_lookup_Some, !lookup_delete. naive_solver.
    - rewrite lookup_delete_ne, !map_filter_lookup_Some, lookup_delete_ne by done.
      naive_solver.
  Qed.

  Lemma map_filter_delete_not m i:
    (∀ y, ¬ P (i, y)) → filter P (delete i m) = filter P m.
  Proof.
    intros HP. apply map_filter_lookup_eq; intros j y Hy.
    by rewrite lookup_delete_ne by naive_solver.
  Qed.

  Lemma map_filter_empty : filter P (∅ : M A) = ∅.
  Proof. apply map_fold_empty. Qed.

  Lemma map_filter_alt m : filter P m = list_to_map (filter P (map_to_list m)).
  Proof.
    apply list_to_map_flip. induction m as [|k x m ? IH] using map_ind.
    { by rewrite map_to_list_empty, map_filter_empty, map_to_list_empty. }
    rewrite map_to_list_insert, filter_cons by done. destruct (decide (P _)).
    - rewrite map_filter_insert by done.
      by rewrite map_to_list_insert, IH by (rewrite map_filter_lookup_None; auto).
    - by rewrite map_filter_insert_not' by naive_solver.
  Qed.
End map_filter.

(** ** Properties of the [map_Forall] predicate *)
Section map_Forall.
Context {A} (P : K → A → Prop).
Implicit Types m : M A.

Lemma map_Forall_to_list m : map_Forall P m ↔ Forall (curry P) (map_to_list m).
Proof.
  rewrite Forall_forall. split.
  - intros Hforall [i x]. rewrite elem_of_map_to_list. by apply (Hforall i x).
  - intros Hforall i x. rewrite <-elem_of_map_to_list. by apply (Hforall (i,x)).
Qed.
Lemma map_Forall_empty : map_Forall P (∅ : M A).
Proof. intros i x. by rewrite lookup_empty. Qed.
Lemma map_Forall_impl (Q : K → A → Prop) m :
  map_Forall P m → (∀ i x, P i x → Q i x) → map_Forall Q m.
Proof. unfold map_Forall; naive_solver. Qed.
Lemma map_Forall_insert_11 m i x : map_Forall P (<[i:=x]>m) → P i x.
Proof. intros Hm. by apply Hm; rewrite lookup_insert. Qed.
Lemma map_Forall_insert_12 m i x :
  m !! i = None → map_Forall P (<[i:=x]>m) → map_Forall P m.
Proof.
  intros ? Hm j y ?; apply Hm. by rewrite lookup_insert_ne by congruence.
Qed.
Lemma map_Forall_insert_2 m i x :
  P i x → map_Forall P m → map_Forall P (<[i:=x]>m).
Proof. intros ?? j y; rewrite lookup_insert_Some; naive_solver. Qed.
Lemma map_Forall_insert m i x :
  m !! i = None → map_Forall P (<[i:=x]>m) ↔ P i x ∧ map_Forall P m.
Proof.
  naive_solver eauto using map_Forall_insert_11,
    map_Forall_insert_12, map_Forall_insert_2.
Qed.
Lemma map_Forall_delete m i : map_Forall P m → map_Forall P (delete i m).
Proof. intros Hm j x; rewrite lookup_delete_Some. naive_solver. Qed.
Lemma map_Forall_lookup m :
  map_Forall P m ↔ ∀ i x, m !! i = Some x → P i x.
Proof. done. Qed.
Lemma map_Forall_lookup_1 m i x :
  map_Forall P m → m !! i = Some x → P i x.
Proof. intros ?. by apply map_Forall_lookup. Qed.
Lemma map_Forall_lookup_2 m :
  (∀ i x, m !! i = Some x → P i x) → map_Forall P m.
Proof. intros ?. by apply map_Forall_lookup. Qed.
Lemma map_Forall_foldr_delete m is :
  map_Forall P m → map_Forall P (foldr delete m is).
Proof. induction is; eauto using map_Forall_delete. Qed.
Lemma map_Forall_ind (Q : M A → Prop) :
  Q ∅ →
  (∀ m i x, m !! i = None → P i x → map_Forall P m → Q m → Q (<[i:=x]>m)) →
  ∀ m, map_Forall P m → Q m.
Proof.
  intros Hnil Hinsert m. induction m using map_ind; auto.
  rewrite map_Forall_insert by done; intros [??]; eauto.
Qed.

Context `{∀ i x, Decision (P i x)}.
Global Instance map_Forall_dec m : Decision (map_Forall P m).
Proof.
  refine (cast_if (decide (Forall (curry P) (map_to_list m))));
    by rewrite map_Forall_to_list.
Defined.
Lemma map_not_Forall (m : M A) :
  ¬map_Forall P m ↔ ∃ i x, m !! i = Some x ∧ ¬P i x.
Proof.
  split; [|intros (i&x&?&?) Hm; specialize (Hm i x); tauto].
  rewrite map_Forall_to_list. intros Hm.
  apply (not_Forall_Exists _), Exists_exists in Hm.
  destruct Hm as ([i x]&?&?). exists i, x. by rewrite <-elem_of_map_to_list.
Qed.
End map_Forall.

(** ** Properties of the [merge] operation *)
Section merge.
Context {A} (f : option A → option A → option A) `{!DiagNone f}.
Implicit Types m : M A.

Global Instance: LeftId (=) None f → LeftId (=) (∅ : M A) (merge f).
Proof.
  intros ??. apply map_eq. intros.
  by rewrite !(lookup_merge f), lookup_empty, (left_id_L None f).
Qed.
Global Instance: RightId (=) None f → RightId (=) (∅ : M A) (merge f).
Proof.
  intros ??. apply map_eq. intros.
  by rewrite !(lookup_merge f), lookup_empty, (right_id_L None f).
Qed.
Global Instance: LeftAbsorb (=) None f → LeftAbsorb (=) (∅ : M A) (merge f).
Proof.
  intros ??. apply map_eq. intros.
  by rewrite !(lookup_merge f), lookup_empty, (left_absorb_L None f).
Qed.
Global Instance: RightAbsorb (=) None f → RightAbsorb (=) (∅ : M A) (merge f).
Proof.
  intros ??. apply map_eq. intros.
  by rewrite !(lookup_merge f), lookup_empty, (right_absorb_L None f).
Qed.
Lemma merge_comm m1 m2 :
  (∀ i, f (m1 !! i) (m2 !! i) = f (m2 !! i) (m1 !! i)) →
  merge f m1 m2 = merge f m2 m1.
Proof. intros. apply map_eq. intros. by rewrite !(lookup_merge f). Qed.
Global Instance merge_comm' : Comm (=) f → Comm (=@{M _}) (merge f).
Proof. intros ???. apply merge_comm. intros. by apply (comm f). Qed.
Lemma merge_assoc m1 m2 m3 :
  (∀ i, f (m1 !! i) (f (m2 !! i) (m3 !! i)) =
        f (f (m1 !! i) (m2 !! i)) (m3 !! i)) →
  merge f m1 (merge f m2 m3) = merge f (merge f m1 m2) m3.
Proof. intros. apply map_eq. intros. by rewrite !(lookup_merge f). Qed.
Global Instance merge_assoc' : Assoc (=) f → Assoc (=@{M _}) (merge f).
Proof. intros ????. apply merge_assoc. intros. by apply (assoc_L f). Qed.
Lemma merge_idemp m1 :
  (∀ i, f (m1 !! i) (m1 !! i) = m1 !! i) → merge f m1 m1 = m1.
Proof. intros. apply map_eq. intros. by rewrite !(lookup_merge f). Qed.
Global Instance merge_idemp' : IdemP (=) f → IdemP (=@{M _}) (merge f).
Proof. intros ??. apply merge_idemp. intros. by apply (idemp f). Qed.
End merge.

Section more_merge.
Context {A B C} (f : option A → option B → option C) `{!DiagNone f}.

Lemma merge_Some (m1 : M A) (m2 : M B) (m : M C) :
  (∀ i, m !! i = f (m1 !! i) (m2 !! i)) ↔ merge f m1 m2 = m.
Proof.
  split; [|intros <-; apply (lookup_merge _) ].
  intros Hlookup. apply map_eq; intros. rewrite Hlookup. apply (lookup_merge _).
Qed.
Lemma merge_empty : merge f (∅ : M A) (∅ : M B) = ∅.
Proof. apply map_eq. intros. by rewrite !(lookup_merge f), !lookup_empty. Qed.
Lemma partial_alter_merge g g1 g2 (m1 : M A) (m2 : M B) i :
  g (f (m1 !! i) (m2 !! i)) = f (g1 (m1 !! i)) (g2 (m2 !! i)) →
  partial_alter g i (merge f m1 m2) =
    merge f (partial_alter g1 i m1) (partial_alter g2 i m2).
Proof.
  intro. apply map_eq. intros j. destruct (decide (i = j)); subst.
  - by rewrite (lookup_merge _), !lookup_partial_alter, !(lookup_merge _).
  - by rewrite (lookup_merge _), !lookup_partial_alter_ne, (lookup_merge _).
Qed.
Lemma partial_alter_merge_l g g1 (m1 : M A) (m2 : M B) i :
  g (f (m1 !! i) (m2 !! i)) = f (g1 (m1 !! i)) (m2 !! i) →
  partial_alter g i (merge f m1 m2) = merge f (partial_alter g1 i m1) m2.
Proof.
  intro. apply map_eq. intros j. destruct (decide (i = j)); subst.
  - by rewrite (lookup_merge _), !lookup_partial_alter, !(lookup_merge _).
  - by rewrite (lookup_merge _), !lookup_partial_alter_ne, (lookup_merge _).
Qed.
Lemma partial_alter_merge_r g g2 (m1 : M A) (m2 : M B) i :
  g (f (m1 !! i) (m2 !! i)) = f (m1 !! i) (g2 (m2 !! i)) →
  partial_alter g i (merge f m1 m2) = merge f m1 (partial_alter g2 i m2).
Proof.
  intro. apply map_eq. intros j. destruct (decide (i = j)); subst.
  - by rewrite (lookup_merge _), !lookup_partial_alter, !(lookup_merge _).
  - by rewrite (lookup_merge _), !lookup_partial_alter_ne, (lookup_merge _).
Qed.
Lemma insert_merge (m1 : M A) (m2 : M B) i x y z :
  f (Some y) (Some z) = Some x →
  <[i:=x]>(merge f m1 m2) = merge f (<[i:=y]>m1) (<[i:=z]>m2).
Proof. by intros; apply partial_alter_merge. Qed.
Lemma delete_merge (m1 : M A) (m2 : M B) i :
  delete i (merge f m1 m2) = merge f (delete i m1) (delete i m2).
Proof. by intros; apply partial_alter_merge. Qed.
Lemma merge_singleton i x y z :
  f (Some y) (Some z) = Some x →
  merge f ({[i := y]} : M A) ({[i := z]} : M B) = {[i := x]}.
Proof.
  intros. by erewrite <-!insert_empty, <-insert_merge, merge_empty by eauto.
Qed.
Lemma insert_merge_l (m1 : M A) (m2 : M B) i x y :
  f (Some y) (m2 !! i) = Some x →
  <[i:=x]>(merge f m1 m2) = merge f (<[i:=y]>m1) m2.
Proof. by intros; apply partial_alter_merge_l. Qed.
Lemma insert_merge_r (m1 : M A) (m2 : M B) i x z :
  f (m1 !! i) (Some z) = Some x →
  <[i:=x]>(merge f m1 m2) = merge f m1 (<[i:=z]>m2).
Proof. by intros; apply partial_alter_merge_r. Qed.
End more_merge.

(** Properties of the zip_with function *)
Lemma map_lookup_zip_with {A B C} (f : A → B → C) (m1 : M A) (m2 : M B) i :
  map_zip_with f m1 m2 !! i = (x ← m1 !! i; y ← m2 !! i; Some (f x y)).
Proof.
  unfold map_zip_with. rewrite lookup_merge by done.
  by destruct (m1 !! i), (m2 !! i).
Qed.
Lemma map_lookup_zip_with_Some {A B C} (f : A → B → C) (m1 : M A) (m2 : M B) i z :
  map_zip_with f m1 m2 !! i = Some z ↔
    ∃ x y, z = f x y ∧ m1 !! i = Some x ∧ m2 !! i = Some y.
Proof. rewrite map_lookup_zip_with. destruct (m1 !! i), (m2 !! i); naive_solver. Qed.

Lemma map_zip_with_empty {A B C} (f : A → B → C) :
  map_zip_with f (∅ : M A) (∅ : M B) = ∅.
Proof. unfold map_zip_with. by rewrite merge_empty by done. Qed.
Lemma map_insert_zip_with {A B C} (f : A → B → C) (m1 : M A) (m2 : M B) i y z :
  <[i:=f y z]>(map_zip_with f m1 m2) = map_zip_with f (<[i:=y]>m1) (<[i:=z]>m2).
Proof. unfold map_zip_with. by erewrite insert_merge by done. Qed.
Lemma map_delete_zip_with {A B C} (f : A → B → C) (m1 : M A) (m2 : M B) i :
  delete i (map_zip_with f m1 m2) = map_zip_with f (delete i m1) (delete i m2).
Proof. unfold map_zip_with. by rewrite delete_merge. Qed.
Lemma map_zip_with_singleton {A B C} (f : A → B → C) i x y :
  map_zip_with f ({[ i := x ]} : M A) ({[ i := y ]} : M B) = {[ i := f x y ]}.
Proof. unfold map_zip_with. by erewrite merge_singleton. Qed.

Lemma map_zip_with_fmap {A' A B' B C} (f : A → B → C)
    (g1 : A' → A) (g2 : B' → B) (m1 : M A') (m2 : M B') :
  map_zip_with f (g1 <$> m1) (g2 <$> m2) = map_zip_with (λ x y, f (g1 x) (g2 y)) m1 m2.
Proof.
  apply map_eq; intro i. rewrite !map_lookup_zip_with, !lookup_fmap.
  by destruct (m1 !! i), (m2 !! i).
Qed.

Lemma map_zip_with_fmap_1 {A' A B C} (f : A → B → C)
    (g : A' → A) (m1 : M A') (m2 : M B) :
  map_zip_with f (g <$> m1) m2 = map_zip_with (λ x y, f (g x) y) m1 m2.
Proof.
  rewrite <- (map_fmap_id m2) at 1. by rewrite map_zip_with_fmap.
Qed.

Lemma map_zip_with_fmap_2 {A B' B C} (f : A → B → C)
    (g : B' → B) (m1 : M A) (m2 : M B') :
  map_zip_with f m1 (g <$> m2) = map_zip_with (λ x y, f x (g y)) m1 m2.
Proof.
  rewrite <- (map_fmap_id m1) at 1. by rewrite map_zip_with_fmap.
Qed.

Lemma map_fmap_zip_with {A B C D} (f : A → B → C) (g : C → D) m1 m2 :
  g <$> map_zip_with f m1 m2 = map_zip_with (λ x y, g (f x y)) m1 m2.
Proof.
  apply map_eq; intro i. rewrite lookup_fmap, !map_lookup_zip_with.
  by destruct (m1 !! i), (m2 !! i).
Qed.

Lemma map_zip_with_flip {A B C} (f : A → B → C) (m1 : M A) (m2 : M B) :
  map_zip_with (flip f) m2 m1 = map_zip_with f m1 m2.
Proof.
  apply map_eq; intro i. rewrite !map_lookup_zip_with.
  by destruct (m1 !! i), (m2 !! i).
Qed.

Lemma map_zip_with_map_zip {A B C} (f : A → B → C) (m1 : M A) (m2 : M B) :
  map_zip_with f m1 m2 = curry f <$> map_zip m1 m2.
Proof.
  apply map_eq; intro i. rewrite lookup_fmap, !map_lookup_zip_with.
  by destruct (m1 !! i), (m2 !! i).
Qed.

Lemma map_fmap_zip {A' A B' B} (g1 : A' → A)
    (g2 : B' → B) (m1 : M A') (m2 : M B') :
  map_zip (fmap g1 m1) (fmap g2 m2) = prod_map g1 g2 <$> map_zip m1 m2.
Proof.
  rewrite map_zip_with_fmap, map_zip_with_map_zip.
  generalize (map_zip m1 m2); intro m. apply map_eq; intro i.
  by rewrite !lookup_fmap; destruct (m !! i) as [[x1 x2]|].
Qed.

(** ** Properties on the [map_relation] relation *)
Section Forall2.
Context {A B} (R : A → B → Prop) (P : A → Prop) (Q : B → Prop).
Context `{∀ x y, Decision (R x y), ∀ x, Decision (P x), ∀ y, Decision (Q y)}.

Let f (mx : option A) (my : option B) : option bool :=
  match mx, my with
  | Some x, Some y => Some (bool_decide (R x y))
  | Some x, None => Some (bool_decide (P x))
  | None, Some y => Some (bool_decide (Q y))
  | None, None => None
  end.
Lemma map_relation_alt (m1 : M A) (m2 : M B) :
  map_relation R P Q m1 m2 ↔ map_Forall (λ _, Is_true) (merge f m1 m2).
Proof.
  split.
  - intros Hm i P'; rewrite lookup_merge by done; intros.
    specialize (Hm i). destruct (m1 !! i), (m2 !! i);
      simplify_eq/=; auto using bool_decide_pack.
  - intros Hm i. specialize (Hm i). rewrite lookup_merge in Hm by done.
    destruct (m1 !! i), (m2 !! i); simplify_eq/=; auto;
      by eapply bool_decide_unpack, Hm.
Qed.
Global Instance map_relation_dec : RelDecision (map_relation (M:=M) R P Q).
Proof.
  refine (λ m1 m2, cast_if (decide (map_Forall (λ _, Is_true) (merge f m1 m2))));
    abstract by rewrite map_relation_alt.
Defined.
(** Due to the finiteness of finite maps, we can extract a witness if the
relation does not hold. *)
Lemma map_not_Forall2 (m1 : M A) (m2 : M B) :
  ¬map_relation R P Q m1 m2 ↔ ∃ i,
    (∃ x y, m1 !! i = Some x ∧ m2 !! i = Some y ∧ ¬R x y)
    ∨ (∃ x, m1 !! i = Some x ∧ m2 !! i = None ∧ ¬P x)
    ∨ (∃ y, m1 !! i = None ∧ m2 !! i = Some y ∧ ¬Q y).
Proof.
  split.
  - rewrite map_relation_alt, (map_not_Forall _). intros (i&?&Hm&?); exists i.
    rewrite lookup_merge in Hm by done.
    destruct (m1 !! i), (m2 !! i); naive_solver auto 2 using bool_decide_pack.
  - unfold map_relation, option_relation.
    by intros [i[(x&y&?&?&?)|[(x&?&?&?)|(y&?&?&?)]]] Hm;
      specialize (Hm i); simplify_option_eq.
Qed.
End Forall2.

(** ** Properties on the disjoint maps *)
Lemma map_disjoint_spec {A} (m1 m2 : M A) :
  m1 ##ₘ m2 ↔ ∀ i x y, m1 !! i = Some x → m2 !! i = Some y → False.
Proof.
  split; intros Hm i; specialize (Hm i);
    destruct (m1 !! i), (m2 !! i); naive_solver.
Qed.
Lemma map_disjoint_alt {A} (m1 m2 : M A) :
  m1 ##ₘ m2 ↔ ∀ i, m1 !! i = None ∨ m2 !! i = None.
Proof.
  split; intros Hm1m2 i; specialize (Hm1m2 i);
    destruct (m1 !! i), (m2 !! i); naive_solver.
Qed.
Lemma map_not_disjoint {A} (m1 m2 : M A) :
  ¬m1 ##ₘ m2 ↔ ∃ i x1 x2, m1 !! i = Some x1 ∧ m2 !! i = Some x2.
Proof.
  unfold disjoint, map_disjoint. rewrite map_not_Forall2 by solve_decision.
  split; [|naive_solver].
  intros [i[(x&y&?&?&?)|[(x&?&?&[])|(y&?&?&[])]]]; naive_solver.
Qed.
Global Instance map_disjoint_sym : Symmetric (map_disjoint : relation (M A)).
Proof. intros A m1 m2. rewrite !map_disjoint_spec. naive_solver. Qed.
Lemma map_disjoint_empty_l {A} (m : M A) : ∅ ##ₘ m.
Proof. rewrite !map_disjoint_spec. intros i x y. by rewrite lookup_empty. Qed.
Lemma map_disjoint_empty_r {A} (m : M A) : m ##ₘ ∅.
Proof. rewrite !map_disjoint_spec. intros i x y. by rewrite lookup_empty. Qed.
Lemma map_disjoint_weaken {A} (m1 m1' m2 m2' : M A) :
  m1' ##ₘ m2' → m1 ⊆ m1' → m2 ⊆ m2' → m1 ##ₘ m2.
Proof. rewrite !map_subseteq_spec, !map_disjoint_spec. eauto. Qed.
Lemma map_disjoint_weaken_l {A} (m1 m1' m2  : M A) :
  m1' ##ₘ m2 → m1 ⊆ m1' → m1 ##ₘ m2.
Proof. eauto using map_disjoint_weaken. Qed.
Lemma map_disjoint_weaken_r {A} (m1 m2 m2' : M A) :
  m1 ##ₘ m2' → m2 ⊆ m2' → m1 ##ₘ m2.
Proof. eauto using map_disjoint_weaken. Qed.
Lemma map_disjoint_Some_l {A} (m1 m2 : M A) i x:
  m1 ##ₘ m2 → m1 !! i = Some x → m2 !! i = None.
Proof. rewrite map_disjoint_spec, eq_None_not_Some. intros ?? [??]; eauto. Qed.
Lemma map_disjoint_Some_r {A} (m1 m2 : M A) i x:
  m1 ##ₘ m2 → m2 !! i = Some x → m1 !! i = None.
Proof. rewrite (symmetry_iff map_disjoint). apply map_disjoint_Some_l. Qed.
Lemma map_disjoint_singleton_l {A} (m: M A) i x : {[i:=x]} ##ₘ m ↔ m !! i = None.
Proof.
  split; [|rewrite !map_disjoint_spec].
  - intro. apply (map_disjoint_Some_l {[i := x]} _ _ x);
      auto using lookup_singleton.
  - intros ? j y1 y2. destruct (decide (i = j)) as [->|].
    + rewrite lookup_singleton. intuition congruence.
    + by rewrite lookup_singleton_ne.
Qed.
Lemma map_disjoint_singleton_r {A} (m : M A) i x :
  m ##ₘ {[i := x]} ↔ m !! i = None.
Proof. by rewrite (symmetry_iff map_disjoint), map_disjoint_singleton_l. Qed.
Lemma map_disjoint_singleton_l_2 {A} (m : M A) i x :
  m !! i = None → {[i := x]} ##ₘ m.
Proof. by rewrite map_disjoint_singleton_l. Qed.
Lemma map_disjoint_singleton_r_2 {A} (m : M A) i x :
  m !! i = None → m ##ₘ {[i := x]}.
Proof. by rewrite map_disjoint_singleton_r. Qed.
Lemma map_disjoint_delete_l {A} (m1 m2 : M A) i : m1 ##ₘ m2 → delete i m1 ##ₘ m2.
Proof.
  rewrite !map_disjoint_alt. intros Hdisjoint j. destruct (Hdisjoint j); auto.
  rewrite lookup_delete_None. tauto.
Qed.
Lemma map_disjoint_delete_r {A} (m1 m2 : M A) i : m1 ##ₘ m2 → m1 ##ₘ delete i m2.
Proof. symmetry. by apply map_disjoint_delete_l. Qed.
Lemma map_disjoint_filter {A} (P : K * A → Prop) `{!∀ x, Decision (P x)} (m : M A) :
  filter P m ##ₘ filter (λ v, ¬ P v) m.
Proof.
  apply map_disjoint_spec. intros i x y.
  rewrite !map_filter_lookup_Some. naive_solver.
Qed.

(** ** Properties of the [union_with] operation *)
Section union_with.
Context {A} (f : A → A → option A).
Implicit Types m : M A.

Lemma lookup_union_with m1 m2 i :
  union_with f m1 m2 !! i = union_with f (m1 !! i) (m2 !! i).
Proof. by rewrite <-(lookup_merge _). Qed.
Lemma lookup_union_with_Some m1 m2 i z :
  union_with f m1 m2 !! i = Some z ↔
    (m1 !! i = Some z ∧ m2 !! i = None) ∨
    (m1 !! i = None ∧ m2 !! i = Some z) ∨
    (∃ x y, m1 !! i = Some x ∧ m2 !! i = Some y ∧ f x y = Some z).
Proof.
  rewrite lookup_union_with.
  destruct (m1 !! i), (m2 !! i); compute; naive_solver.
Qed.
Global Instance: LeftId (=@{M A}) ∅ (union_with f).
Proof. unfold union_with, map_union_with. apply _. Qed.
Global Instance: RightId (=@{M A}) ∅ (union_with f).
Proof. unfold union_with, map_union_with. apply _. Qed.
Lemma union_with_comm m1 m2 :
  (∀ i x y, m1 !! i = Some x → m2 !! i = Some y → f x y = f y x) →
  union_with f m1 m2 = union_with f m2 m1.
Proof.
  intros. apply (merge_comm _). intros i.
  destruct (m1 !! i) eqn:?, (m2 !! i) eqn:?; simpl; eauto.
Qed.
Global Instance: Comm (=) f → Comm (=@{M A}) (union_with f).
Proof. intros ???. apply union_with_comm. eauto. Qed.
Lemma union_with_idemp m :
  (∀ i x, m !! i = Some x → f x x = Some x) → union_with f m m = m.
Proof.
  intros. apply (merge_idemp _). intros i.
  destruct (m !! i) eqn:?; simpl; eauto.
Qed.
Lemma alter_union_with (g : A → A) m1 m2 i :
  (∀ x y, m1 !! i = Some x → m2 !! i = Some y → g <$> f x y = f (g x) (g y)) →
  alter g i (union_with f m1 m2) =
    union_with f (alter g i m1) (alter g i m2).
Proof.
  intros. apply (partial_alter_merge _).
  destruct (m1 !! i) eqn:?, (m2 !! i) eqn:?; simpl; eauto.
Qed.
Lemma alter_union_with_l (g : A → A) m1 m2 i :
  (∀ x y, m1 !! i = Some x → m2 !! i = Some y → g <$> f x y = f (g x) y) →
  (∀ y, m1 !! i = None → m2 !! i = Some y → g y = y) →
  alter g i (union_with f m1 m2) = union_with f (alter g i m1) m2.
Proof.
  intros. apply (partial_alter_merge_l _).
  destruct (m1 !! i) eqn:?, (m2 !! i) eqn:?; f_equal/=; auto.
Qed.
Lemma alter_union_with_r (g : A → A) m1 m2 i :
  (∀ x y, m1 !! i = Some x → m2 !! i = Some y → g <$> f x y = f x (g y)) →
  (∀ x, m1 !! i = Some x → m2 !! i = None → g x = x) →
  alter g i (union_with f m1 m2) = union_with f m1 (alter g i m2).
Proof.
  intros. apply (partial_alter_merge_r _).
  destruct (m1 !! i) eqn:?, (m2 !! i) eqn:?; f_equal/=; auto.
Qed.
Lemma delete_union_with m1 m2 i :
  delete i (union_with f m1 m2) = union_with f (delete i m1) (delete i m2).
Proof. by apply (partial_alter_merge _). Qed.
Lemma foldr_delete_union_with (m1 m2 : M A) is :
  foldr delete (union_with f m1 m2) is =
    union_with f (foldr delete m1 is) (foldr delete m2 is).
Proof. induction is; simpl. done. by rewrite IHis, delete_union_with. Qed.
Lemma insert_union_with m1 m2 i x y z :
  f x y = Some z →
  <[i:=z]>(union_with f m1 m2) = union_with f (<[i:=x]>m1) (<[i:=y]>m2).
Proof. by intros; apply (partial_alter_merge _). Qed.
Lemma insert_union_with_l m1 m2 i x :
  m2 !! i = None → <[i:=x]>(union_with f m1 m2) = union_with f (<[i:=x]>m1) m2.
Proof.
  intros Hm2. unfold union_with, map_union_with.
  by erewrite (insert_merge_l _) by (by rewrite Hm2).
Qed.
Lemma insert_union_with_r m1 m2 i x :
  m1 !! i = None → <[i:=x]>(union_with f m1 m2) = union_with f m1 (<[i:=x]>m2).
Proof.
  intros Hm1. unfold union_with, map_union_with.
  by erewrite (insert_merge_r _) by (by rewrite Hm1).
Qed.
End union_with.

(** ** Properties of the [union] operation *)
Global Instance: LeftId (=@{M A}) ∅ (∪) := _.
Global Instance: RightId (=@{M A}) ∅ (∪) := _.
Global Instance: Assoc (=@{M A}) (∪).
Proof.
  intros A m1 m2 m3. unfold union, map_union, union_with, map_union_with.
  apply (merge_assoc _). intros i.
  by destruct (m1 !! i), (m2 !! i), (m3 !! i).
Qed.
Global Instance: IdemP (=@{M A}) (∪).
Proof. intros A ?. by apply union_with_idemp. Qed.
Lemma lookup_union {A} (m1 m2 : M A) i :
  (m1 ∪ m2) !! i = union_with (λ x _, Some x) (m1 !! i) (m2 !! i).
Proof. apply lookup_union_with. Qed.
Lemma lookup_union_r {A} (m1 m2 : M A) i :
  m1 !! i = None → (m1 ∪ m2) !! i = m2 !! i.
Proof. intros Hi. by rewrite lookup_union, Hi, (left_id_L _ _).  Qed.
Lemma lookup_union_Some_raw {A} (m1 m2 : M A) i x :
  (m1 ∪ m2) !! i = Some x ↔
    m1 !! i = Some x ∨ (m1 !! i = None ∧ m2 !! i = Some x).
Proof. rewrite lookup_union. destruct (m1 !! i), (m2 !! i); naive_solver. Qed.
Lemma lookup_union_None {A} (m1 m2 : M A) i :
  (m1 ∪ m2) !! i = None ↔ m1 !! i = None ∧ m2 !! i = None.
Proof. rewrite lookup_union.  destruct (m1 !! i), (m2 !! i); naive_solver. Qed.
Lemma map_positive_l {A} (m1 m2 : M A) : m1 ∪ m2 = ∅ → m1 = ∅.
Proof.
  intros Hm. apply map_empty. intros i. apply (f_equal (.!! i)) in Hm.
  rewrite lookup_empty, lookup_union_None in Hm; tauto.
Qed.
Lemma map_positive_l_alt {A} (m1 m2 : M A) : m1 ≠ ∅ → m1 ∪ m2 ≠ ∅.
Proof. eauto using map_positive_l. Qed.
Lemma lookup_union_Some {A} (m1 m2 : M A) i x :
  m1 ##ₘ m2 → (m1 ∪ m2) !! i = Some x ↔ m1 !! i = Some x ∨ m2 !! i = Some x.
Proof.
  intros Hdisjoint. rewrite lookup_union_Some_raw.
  intuition eauto using map_disjoint_Some_r.
Qed.
Lemma lookup_union_Some_l {A} (m1 m2 : M A) i x :
  m1 !! i = Some x → (m1 ∪ m2) !! i = Some x.
Proof. intro. rewrite lookup_union_Some_raw; intuition. Qed.
Lemma lookup_union_Some_r {A} (m1 m2 : M A) i x :
  m1 ##ₘ m2 → m2 !! i = Some x → (m1 ∪ m2) !! i = Some x.
Proof. intro. rewrite lookup_union_Some; intuition. Qed.
Lemma map_union_comm {A} (m1 m2 : M A) : m1 ##ₘ m2 → m1 ∪ m2 = m2 ∪ m1.
Proof.
  intros Hdisjoint. apply (merge_comm (union_with (λ x _, Some x))).
  intros i. specialize (Hdisjoint i).
  destruct (m1 !! i), (m2 !! i); compute; naive_solver.
Qed.
Lemma map_subseteq_union {A} (m1 m2 : M A) : m1 ⊆ m2 → m1 ∪ m2 = m2.
Proof.
  rewrite map_subseteq_spec.
  intros Hm1m2. apply map_eq. intros i. apply option_eq. intros x.
  rewrite lookup_union_Some_raw. split; [by intuition |].
  intros Hm2. specialize (Hm1m2 i). destruct (m1 !! i) as [y|]; [| by auto].
  rewrite (Hm1m2 y eq_refl) in Hm2. intuition congruence.
Qed.
Lemma map_union_subseteq_l {A} (m1 m2 : M A) : m1 ⊆ m1 ∪ m2.
Proof.
  rewrite map_subseteq_spec. intros ? i x. rewrite lookup_union_Some_raw. tauto.
Qed.
Lemma map_union_subseteq_r {A} (m1 m2 : M A) : m1 ##ₘ m2 → m2 ⊆ m1 ∪ m2.
Proof.
  intros. rewrite map_union_comm by done. by apply map_union_subseteq_l.
Qed.
Lemma map_union_subseteq_l_alt {A} (m1 m2 m3 : M A) : m1 ⊆ m2 → m1 ⊆ m2 ∪ m3.
Proof. intros. trans m2; auto using map_union_subseteq_l. Qed.
Lemma map_union_subseteq_r_alt {A} (m1 m2 m3 : M A) :
  m2 ##ₘ m3 → m1 ⊆ m3 → m1 ⊆ m2 ∪ m3.
Proof. intros. trans m3; auto using map_union_subseteq_r. Qed.
Lemma map_union_mono_l {A} (m1 m2 m3 : M A) : m1 ⊆ m2 → m3 ∪ m1 ⊆ m3 ∪ m2.
Proof.
  rewrite !map_subseteq_spec. intros ???.
  rewrite !lookup_union_Some_raw. naive_solver.
Qed.
Lemma map_union_mono_r {A} (m1 m2 m3 : M A) :
  m2 ##ₘ m3 → m1 ⊆ m2 → m1 ∪ m3 ⊆ m2 ∪ m3.
Proof.
  intros. rewrite !(map_union_comm _ m3)
    by eauto using map_disjoint_weaken_l.
  by apply map_union_mono_l.
Qed.
Lemma map_union_reflecting_l {A} (m1 m2 m3 : M A) :
  m3 ##ₘ m1 → m3 ##ₘ m2 → m3 ∪ m1 ⊆ m3 ∪ m2 → m1 ⊆ m2.
Proof.
  rewrite !map_subseteq_spec. intros Hm31 Hm32 Hm i x ?. specialize (Hm i x).
  rewrite !lookup_union_Some in Hm by done. destruct Hm; auto.
  by rewrite map_disjoint_spec in Hm31; destruct (Hm31 i x x).
Qed.
Lemma map_union_reflecting_r {A} (m1 m2 m3 : M A) :
  m1 ##ₘ m3 → m2 ##ₘ m3 → m1 ∪ m3 ⊆ m2 ∪ m3 → m1 ⊆ m2.
Proof.
  intros ??. rewrite !(map_union_comm _ m3) by done.
  by apply map_union_reflecting_l.
Qed.
Lemma map_union_cancel_l {A} (m1 m2 m3 : M A) :
  m1 ##ₘ m3 → m2 ##ₘ m3 → m3 ∪ m1 = m3 ∪ m2 → m1 = m2.
Proof.
  intros. apply (anti_symm (⊆)); apply map_union_reflecting_l with m3;
    by try apply reflexive_eq.
Qed.
Lemma map_union_cancel_r {A} (m1 m2 m3 : M A) :
  m1 ##ₘ m3 → m2 ##ₘ m3 → m1 ∪ m3 = m2 ∪ m3 → m1 = m2.
Proof.
  intros. apply (anti_symm (⊆)); apply map_union_reflecting_r with m3;
    by try apply reflexive_eq.
Qed.
Lemma map_disjoint_union_l {A} (m1 m2 m3 : M A) :
  m1 ∪ m2 ##ₘ m3 ↔ m1 ##ₘ m3 ∧ m2 ##ₘ m3.
Proof.
  rewrite !map_disjoint_alt. setoid_rewrite lookup_union_None. naive_solver.
Qed.
Lemma map_disjoint_union_r {A} (m1 m2 m3 : M A) :
  m1 ##ₘ m2 ∪ m3 ↔ m1 ##ₘ m2 ∧ m1 ##ₘ m3.
Proof.
  rewrite !map_disjoint_alt. setoid_rewrite lookup_union_None. naive_solver.
Qed.
Lemma map_disjoint_union_l_2 {A} (m1 m2 m3 : M A) :
  m1 ##ₘ m3 → m2 ##ₘ m3 → m1 ∪ m2 ##ₘ m3.
Proof. by rewrite map_disjoint_union_l. Qed.
Lemma map_disjoint_union_r_2 {A} (m1 m2 m3 : M A) :
  m1 ##ₘ m2 → m1 ##ₘ m3 → m1 ##ₘ m2 ∪ m3.
Proof. by rewrite map_disjoint_union_r. Qed.
Lemma insert_union_singleton_l {A} (m : M A) i x : <[i:=x]>m = {[i := x]} ∪ m.
Proof.
  apply map_eq. intros j. apply option_eq. intros y.
  rewrite lookup_union_Some_raw.
  destruct (decide (i = j)); subst.
  - rewrite !lookup_singleton, lookup_insert. intuition congruence.
  - rewrite !lookup_singleton_ne, lookup_insert_ne; intuition congruence.
Qed.
Lemma insert_union_singleton_r {A} (m : M A) i x :
  m !! i = None → <[i:=x]>m = m ∪ {[i := x]}.
Proof.
  intro. rewrite insert_union_singleton_l, map_union_comm; [done |].
  by apply map_disjoint_singleton_l.
Qed.
Lemma map_disjoint_insert_l {A} (m1 m2 : M A) i x :
  <[i:=x]>m1 ##ₘ m2 ↔ m2 !! i = None ∧ m1 ##ₘ m2.
Proof.
  rewrite insert_union_singleton_l.
  by rewrite map_disjoint_union_l, map_disjoint_singleton_l.
Qed.
Lemma map_disjoint_insert_r {A} (m1 m2 : M A) i x :
  m1 ##ₘ <[i:=x]>m2 ↔ m1 !! i = None ∧ m1 ##ₘ m2.
Proof.
  rewrite insert_union_singleton_l.
  by rewrite map_disjoint_union_r, map_disjoint_singleton_r.
Qed.
Lemma map_disjoint_insert_l_2 {A} (m1 m2 : M A) i x :
  m2 !! i = None → m1 ##ₘ m2 → <[i:=x]>m1 ##ₘ m2.
Proof. by rewrite map_disjoint_insert_l. Qed.
Lemma map_disjoint_insert_r_2 {A} (m1 m2 : M A) i x :
  m1 !! i = None → m1 ##ₘ m2 → m1 ##ₘ <[i:=x]>m2.
Proof. by rewrite map_disjoint_insert_r. Qed.
Lemma insert_union_l {A} (m1 m2 : M A) i x :
  <[i:=x]>(m1 ∪ m2) = <[i:=x]>m1 ∪ m2.
Proof. by rewrite !insert_union_singleton_l, (assoc_L (∪)). Qed.
Lemma insert_union_r {A} (m1 m2 : M A) i x :
  m1 !! i = None → <[i:=x]>(m1 ∪ m2) = m1 ∪ <[i:=x]>m2.
Proof.
  intro. rewrite !insert_union_singleton_l, !(assoc_L (∪)).
  rewrite (map_union_comm m1); [done |].
  by apply map_disjoint_singleton_r.
Qed.
Lemma foldr_insert_union {A} (m : M A) l :
  foldr (λ p, <[p.1:=p.2]>) m l = list_to_map l ∪ m.
Proof.
  induction l as [|i l IH]; simpl; [by rewrite (left_id_L _ _)|].
  by rewrite IH, insert_union_l.
Qed.
Lemma delete_union {A} (m1 m2 : M A) i :
  delete i (m1 ∪ m2) = delete i m1 ∪ delete i m2.
Proof. apply delete_union_with. Qed.
Lemma map_Forall_union_11 {A} (m1 m2 : M A) P :
  map_Forall P (m1 ∪ m2) → map_Forall P m1.
Proof. intros HP i x ?. apply HP, lookup_union_Some_raw; auto. Qed.
Lemma map_Forall_union_12 {A} (m1 m2 : M A) P :
  m1 ##ₘ m2 → map_Forall P (m1 ∪ m2) → map_Forall P m2.
Proof. intros ? HP i x ?. apply HP, lookup_union_Some; auto. Qed.
Lemma map_Forall_union_2 {A} (m1 m2 : M A) P :
  map_Forall P m1 → map_Forall P m2 → map_Forall P (m1 ∪ m2).
Proof. intros ???? [|[]]%lookup_union_Some_raw; eauto. Qed.
Lemma map_Forall_union {A} (m1 m2 : M A) P :
  m1 ##ₘ m2 →
  map_Forall P (m1 ∪ m2) ↔ map_Forall P m1 ∧ map_Forall P m2.
Proof.
  naive_solver eauto using map_Forall_union_11,
    map_Forall_union_12, map_Forall_union_2.
Qed.
Lemma map_union_filter {A} (P : K * A → Prop) `{!∀ x, Decision (P x)} (m : M A) :
  filter P m ∪ filter (λ v, ¬ P v) m = m.
Proof.
  apply map_eq; intros i. apply option_eq; intros x.
  rewrite lookup_union_Some, !map_filter_lookup_Some by apply map_disjoint_filter.
  destruct (decide (P (i,x))); naive_solver.
Qed.

(** ** Properties of the [union_list] operation *)
Lemma map_disjoint_union_list_l {A} (ms : list (M A)) (m : M A) :
  ⋃ ms ##ₘ m ↔ Forall (.##ₘ m) ms.
Proof.
  split.
  - induction ms; simpl; rewrite ?map_disjoint_union_l; intuition.
  - induction 1; simpl; [apply map_disjoint_empty_l |].
    by rewrite map_disjoint_union_l.
Qed.
Lemma map_disjoint_union_list_r {A} (ms : list (M A)) (m : M A) :
  m ##ₘ ⋃ ms ↔ Forall (.##ₘ m) ms.
Proof. by rewrite (symmetry_iff map_disjoint), map_disjoint_union_list_l. Qed.
Lemma map_disjoint_union_list_l_2 {A} (ms : list (M A)) (m : M A) :
  Forall (.##ₘ m) ms → ⋃ ms ##ₘ m.
Proof. by rewrite map_disjoint_union_list_l. Qed.
Lemma map_disjoint_union_list_r_2 {A} (ms : list (M A)) (m : M A) :
  Forall (.##ₘ m) ms → m ##ₘ ⋃ ms.
Proof. by rewrite map_disjoint_union_list_r. Qed.

(** ** Properties of the folding the [delete] function *)
Lemma lookup_foldr_delete {A} (m : M A) is j :
  j ∈ is → foldr delete m is !! j = None.
Proof.
  induction 1 as [|i j is]; simpl; [by rewrite lookup_delete|].
  by destruct (decide (i = j)) as [->|?];
    rewrite ?lookup_delete, ?lookup_delete_ne by done.
Qed.
Lemma lookup_foldr_delete_not_elem_of {A} (m : M A) is j :
  j ∉ is → foldr delete m is !! j = m !! j.
Proof.
  induction is; simpl; [done |]. rewrite elem_of_cons; intros.
  rewrite lookup_delete_ne; intuition.
Qed.
Lemma lookup_foldr_delete_Some {A} (m : M A) is j y :
  foldr delete m is !! j = Some y ↔ j ∉ is ∧ m !! j = Some y.
Proof. induction is; simpl; rewrite ?lookup_delete_Some; set_solver. Qed.
Lemma foldr_delete_notin {A} (m : M A) is :
  Forall (λ i, m !! i = None) is → foldr delete m is = m.
Proof. induction 1; simpl; [done |]. rewrite delete_notin; congruence. Qed.
Lemma foldr_delete_commute {A} (m : M A) is j :
  delete j (foldr delete m is) = foldr delete (delete j m) is.
Proof. induction is as [|?? IH]; [done| ]. simpl. by rewrite delete_commute, IH. Qed.
Lemma foldr_delete_insert {A} (m : M A) is j x :
  j ∈ is → foldr delete (<[j:=x]>m) is = foldr delete m is.
Proof.
  induction 1 as [i is|j i is ? IH]; simpl; [|by rewrite IH].
  by rewrite !foldr_delete_commute, delete_insert_delete.
Qed.
Lemma foldr_delete_insert_ne {A} (m : M A) is j x :
  j ∉ is → foldr delete (<[j:=x]>m) is = <[j:=x]>(foldr delete m is).
Proof.
  induction is; simpl; [done |]. rewrite elem_of_cons. intros.
  rewrite IHis, delete_insert_ne; intuition.
Qed.
Lemma map_disjoint_foldr_delete_l {A} (m1 m2 : M A) is :
  m1 ##ₘ m2 → foldr delete m1 is ##ₘ m2.
Proof. induction is; simpl; auto using map_disjoint_delete_l. Qed.
Lemma map_disjoint_foldr_delete_r {A} (m1 m2 : M A) is :
  m1 ##ₘ m2 → m1 ##ₘ foldr delete m2 is.
Proof. induction is; simpl; auto using map_disjoint_delete_r. Qed.
Lemma foldr_delete_union {A} (m1 m2 : M A) is :
  foldr delete (m1 ∪ m2) is = foldr delete m1 is ∪ foldr delete m2 is.
Proof. apply foldr_delete_union_with. Qed.

(** ** Properties on disjointness of conversion to lists *)
Lemma map_disjoint_list_to_map_l {A} (m : M A) ixs :
  list_to_map ixs ##ₘ m ↔ Forall (λ ix, m !! ix.1 = None) ixs.
Proof.
  split.
  - induction ixs; simpl; rewrite ?map_disjoint_insert_l in *; intuition.
  - induction 1; simpl; [apply map_disjoint_empty_l|].
    rewrite map_disjoint_insert_l. auto.
Qed.
Lemma map_disjoint_list_to_map_r {A} (m : M A) ixs :
  m ##ₘ list_to_map ixs ↔ Forall (λ ix, m !! ix.1 = None) ixs.
Proof. by rewrite (symmetry_iff map_disjoint), map_disjoint_list_to_map_l. Qed.
Lemma map_disjoint_list_to_map_zip_l {A} (m : M A) is xs :
  length is = length xs →
  list_to_map (zip is xs) ##ₘ m ↔ Forall (λ i, m !! i = None) is.
Proof.
  intro. rewrite map_disjoint_list_to_map_l.
  rewrite <-(fst_zip is xs) at 2 by lia. by rewrite Forall_fmap.
Qed.
Lemma map_disjoint_list_to_map_zip_r {A} (m : M A) is xs :
  length is = length xs →
  m ##ₘ list_to_map (zip is xs) ↔ Forall (λ i, m !! i = None) is.
Proof.
  intro. by rewrite (symmetry_iff map_disjoint), map_disjoint_list_to_map_zip_l.
Qed.
Lemma map_disjoint_list_to_map_zip_l_2 {A} (m : M A) is xs :
  length is = length xs → Forall (λ i, m !! i = None) is →
  list_to_map (zip is xs) ##ₘ m.
Proof. intro. by rewrite map_disjoint_list_to_map_zip_l. Qed.
Lemma map_disjoint_list_to_map_zip_r_2 {A} (m : M A) is xs :
  length is = length xs → Forall (λ i, m !! i = None) is →
  m ##ₘ list_to_map (zip is xs).
Proof. intro. by rewrite map_disjoint_list_to_map_zip_r. Qed.

(** ** Properties of the [intersection_with] operation *)
Section intersection_with.
Context {A} (f : A → A → option A).
Implicit Type (m: M A).
Global Instance : LeftAbsorb (=@{M A}) ∅ (intersection_with f).
Proof. unfold intersection_with, map_intersection_with. apply _. Qed.
Global Instance: RightAbsorb (=@{M A}) ∅ (intersection_with f).
Proof. unfold intersection_with, map_intersection_with. apply _. Qed.
Lemma lookup_intersection_with m1 m2 i :
  intersection_with f m1 m2 !! i = intersection_with f (m1 !! i) (m2 !! i).
Proof. by rewrite <-(lookup_merge _). Qed.
Lemma lookup_intersection_with_Some m1 m2 i z :
  intersection_with f m1 m2 !! i = Some z ↔
    (∃ x y, m1 !! i = Some x ∧ m2 !! i = Some y ∧ f x y = Some z).
Proof.
  rewrite lookup_intersection_with.
  destruct (m1 !! i), (m2 !! i); compute; naive_solver.
Qed.
Lemma intersection_with_comm m1 m2 :
  (∀ i x y, m1 !! i = Some x → m2 !! i = Some y → f x y = f y x) →
  intersection_with f m1 m2 = intersection_with f m2 m1.
Proof.
  intros. apply (merge_comm _). intros i.
  destruct (m1 !! i) eqn:?, (m2 !! i) eqn:?; simpl; eauto.
Qed.
Global Instance: Comm (=) f → Comm (=@{M A}) (intersection_with f).
Proof. intros ???. apply intersection_with_comm. eauto. Qed.
Lemma intersection_with_idemp m :
  (∀ i x, m !! i = Some x → f x x = Some x) → intersection_with f m m = m.
Proof.
  intros. apply (merge_idemp _). intros i.
  destruct (m !! i) eqn:?; simpl; eauto.
Qed.
Lemma alter_intersection_with (g : A → A) m1 m2 i :
  (∀ x y, m1 !! i = Some x → m2 !! i = Some y → g <$> f x y = f (g x) (g y)) →
  alter g i (intersection_with f m1 m2) =
    intersection_with f (alter g i m1) (alter g i m2).
Proof.
  intros. apply (partial_alter_merge _).
  destruct (m1 !! i) eqn:?, (m2 !! i) eqn:?; simpl; eauto.
Qed.
Lemma delete_intersection_with m1 m2 i :
  delete i (intersection_with f m1 m2) = intersection_with f (delete i m1) (delete i m2).
Proof. by apply (partial_alter_merge _). Qed.
Lemma foldr_delete_intersection_with (m1 m2 : M A) is :
  foldr delete (intersection_with f m1 m2) is =
    intersection_with f (foldr delete m1 is) (foldr delete m2 is).
Proof. induction is; simpl. done. by rewrite IHis, delete_intersection_with. Qed.
Lemma insert_intersection_with m1 m2 i x y z :
  f x y = Some z →
  <[i:=z]>(intersection_with f m1 m2) = intersection_with f (<[i:=x]>m1) (<[i:=y]>m2).
Proof. by intros; apply (partial_alter_merge _). Qed.
End intersection_with.

(** ** Properties of the [intersection] operation *)
Global Instance: LeftAbsorb (=@{M A}) ∅ (∩) := _.
Global Instance: RightAbsorb (=@{M A}) ∅ (∩) := _.
Global Instance: Assoc (=@{M A}) (∩).
Proof.
  intros A m1 m2 m3.
  unfold intersection, map_intersection, intersection_with, map_intersection_with.
  apply (merge_assoc _). intros i.
  by destruct (m1 !! i), (m2 !! i), (m3 !! i).
Qed.
Global Instance: IdemP (=@{M A}) (∩).
Proof. intros A ?. by apply intersection_with_idemp. Qed.

Lemma lookup_intersection_Some {A} (m1 m2 : M A) i x :
  (m1 ∩ m2) !! i = Some x ↔ m1 !! i = Some x ∧ is_Some (m2 !! i).
Proof.
  unfold intersection, map_intersection. rewrite lookup_intersection_with.
  destruct (m1 !! i), (m2 !! i); compute; naive_solver.
Qed.
Lemma lookup_intersection_None {A} (m1 m2 : M A) i :
  (m1 ∩ m2) !! i = None ↔ m1 !! i = None ∨ m2 !! i = None.
Proof.
  unfold intersection, map_intersection. rewrite lookup_intersection_with.
  destruct (m1 !! i), (m2 !! i); compute; naive_solver.
Qed.

(** ** Properties of the [difference_with] operation *)
Lemma lookup_difference_with {A} (f : A → A → option A) (m1 m2 : M A) i :
  difference_with f m1 m2 !! i = difference_with f (m1 !! i) (m2 !! i).
Proof. by rewrite <-lookup_merge by done. Qed.
Lemma lookup_difference_with_Some {A} (f : A → A → option A) (m1 m2 : M A) i z :
  difference_with f m1 m2 !! i = Some z ↔
    (m1 !! i = Some z ∧ m2 !! i = None) ∨
    (∃ x y, m1 !! i = Some x ∧ m2 !! i = Some y ∧ f x y = Some z).
Proof.
  rewrite lookup_difference_with.
  destruct (m1 !! i), (m2 !! i); compute; naive_solver.
Qed.

(** ** Properties of the [difference] operation *)
Lemma lookup_difference_Some {A} (m1 m2 : M A) i x :
  (m1 ∖ m2) !! i = Some x ↔ m1 !! i = Some x ∧ m2 !! i = None.
Proof.
  unfold difference, map_difference; rewrite lookup_difference_with.
  destruct (m1 !! i), (m2 !! i); compute; intuition congruence.
Qed.
Lemma lookup_difference_None {A} (m1 m2 : M A) i :
  (m1 ∖ m2) !! i = None ↔ m1 !! i = None ∨ is_Some (m2 !! i).
Proof.
  unfold difference, map_difference; rewrite lookup_difference_with.
  destruct (m1 !! i), (m2 !! i); compute; naive_solver.
Qed.
Lemma map_disjoint_difference_l {A} (m1 m2 : M A) : m1 ⊆ m2 → m2 ∖ m1 ##ₘ m1.
Proof.
  intros Hm i; specialize (Hm i).
  unfold difference, map_difference; rewrite lookup_difference_with.
  by destruct (m1 !! i), (m2 !! i).
Qed.
Lemma map_disjoint_difference_r {A} (m1 m2 : M A) : m1 ⊆ m2 → m1 ##ₘ m2 ∖ m1.
Proof. intros. symmetry. by apply map_disjoint_difference_l. Qed.
Lemma map_difference_union {A} (m1 m2 : M A) :
  m1 ⊆ m2 → m1 ∪ m2 ∖ m1 = m2.
Proof.
  rewrite map_subseteq_spec. intro Hm1m2. apply map_eq. intros i.
  apply option_eq. intros v. specialize (Hm1m2 i).
  unfold difference, map_difference, difference_with, map_difference_with.
  rewrite lookup_union_Some_raw, (lookup_merge _).
  destruct (m1 !! i) as [x'|], (m2 !! i);
    try specialize (Hm1m2 x'); compute; intuition congruence.
Qed.
Lemma map_difference_diag {A} (m : M A) : m ∖ m = ∅.
Proof.
  apply map_empty; intros i. rewrite lookup_difference_None.
  destruct (m !! i); eauto.
Qed.
End theorems.

(** ** The seq operation *)
Section map_seq.
  Context `{FinMap nat M} {A : Type}.
  Implicit Types x : A.
  Implicit Types xs : list A.

  Lemma lookup_map_seq_Some_inv start xs i x :
    xs !! i = Some x ↔ map_seq (M:=M A) start xs !! (start + i) = Some x.
  Proof.
    revert start i. induction xs as [|x' xs IH]; intros start i; simpl.
    { by rewrite lookup_empty, lookup_nil. }
    destruct i as [|i]; simpl.
    { by rewrite Nat.add_0_r, lookup_insert. }
    rewrite lookup_insert_ne by lia. by rewrite (IH (S start)), Nat.add_succ_r.
  Qed.
  Lemma lookup_map_seq_Some start xs i x :
    map_seq (M:=M A) start xs !! i = Some x ↔ start ≤ i ∧ xs !! (i - start) = Some x.
  Proof.
    destruct (decide (start ≤ i)) as [|Hsi].
    { rewrite (lookup_map_seq_Some_inv start).
      replace (start + (i - start)) with i by lia. naive_solver. }
    split; [|naive_solver]. intros Hi; destruct Hsi.
    revert start i Hi. induction xs as [|x' xs IH]; intros start i; simpl.
    { by rewrite lookup_empty. }
    rewrite lookup_insert_Some; intros [[-> ->]|[? ?%IH]]; lia.
  Qed.

  Lemma lookup_map_seq_None start xs i :
    map_seq (M:=M A) start xs !! i = None ↔ i < start ∨ start + length xs ≤ i.
  Proof.
    trans (¬start ≤ i ∨ ¬is_Some (xs !! (i - start))).
    - rewrite eq_None_not_Some, <-not_and_l. unfold is_Some.
      setoid_rewrite lookup_map_seq_Some. naive_solver.
    - rewrite lookup_lt_is_Some. lia.
  Qed.

  Lemma lookup_map_seq_0 xs i : map_seq (M:=M A) 0 xs !! i = xs !! i.
  Proof. apply option_eq; intros x. by rewrite (lookup_map_seq_Some_inv 0). Qed.

  Lemma map_seq_singleton start x :
    map_seq (M:=M A) start [x] = {[ start := x ]}.
  Proof. done. Qed.

  Lemma map_seq_app_disjoint start xs1 xs2 :
    map_seq (M:=M A) start xs1 ##ₘ map_seq (start + length xs1) xs2.
  Proof.
    apply map_disjoint_spec; intros i x1 x2. rewrite !lookup_map_seq_Some.
    intros [??%lookup_lt_Some] [??%lookup_lt_Some]; lia.
  Qed.
  Lemma map_seq_app start xs1 xs2 :
    map_seq start (xs1 ++ xs2)
    =@{M A} map_seq start xs1 ∪ map_seq (start + length xs1) xs2.
  Proof.
    revert start. induction xs1 as [|x1 xs1 IH]; intros start; simpl.
    - by rewrite (left_id_L _ _), Nat.add_0_r.
    - by rewrite IH, Nat.add_succ_r, !insert_union_singleton_l, (assoc_L _).
  Qed.

  Lemma map_seq_cons_disjoint start xs :
    map_seq (M:=M A) (S start) xs !! start = None.
  Proof. rewrite lookup_map_seq_None. lia. Qed.
  Lemma map_seq_cons start xs x :
    map_seq start (x :: xs) =@{M A} <[start:=x]> (map_seq (S start) xs).
  Proof. done. Qed.

  Lemma map_seq_snoc_disjoint start xs :
    map_seq (M:=M A) start xs !! (start+length xs) = None.
  Proof. rewrite lookup_map_seq_None. lia. Qed.
  Lemma map_seq_snoc start xs x :
    map_seq start (xs ++ [x]) =@{M A} <[start+length xs:=x]> (map_seq start xs).
  Proof.
    rewrite map_seq_app, map_seq_singleton.
    by rewrite insert_union_singleton_r by (by rewrite map_seq_snoc_disjoint).
  Qed.

  Lemma fmap_map_seq {B} (f : A → B) start xs :
    f <$> map_seq start xs = map_seq start (f <$> xs).
  Proof.
    revert start. induction xs as [|x xs IH]; intros start; csimpl.
    { by rewrite fmap_empty. }
    by rewrite fmap_insert, IH.
  Qed.
End map_seq.

(** * Tactics *)
(** The tactic [decompose_map_disjoint] simplifies occurrences of [disjoint]
in the hypotheses that involve the empty map [∅], the union [(∪)] or insert
[<[_:=_]>] operation, the singleton [{[_:= _]}] map, and disjointness of lists of
maps. This tactic does not yield any information loss as all simplifications
performed are reversible. *)
Ltac decompose_map_disjoint := repeat
  match goal with
  | H : _ ∪ _ ##ₘ _ |- _ => apply map_disjoint_union_l in H; destruct H
  | H : _ ##ₘ _ ∪ _ |- _ => apply map_disjoint_union_r in H; destruct H
  | H : {[ _ := _ ]} ##ₘ _ |- _ => apply map_disjoint_singleton_l in H
  | H : _ ##ₘ {[ _ := _ ]} |- _ =>  apply map_disjoint_singleton_r in H
  | H : <[_:=_]>_ ##ₘ _ |- _ => apply map_disjoint_insert_l in H; destruct H
  | H : _ ##ₘ <[_:=_]>_ |- _ => apply map_disjoint_insert_r in H; destruct H
  | H : ⋃ _ ##ₘ _ |- _ => apply map_disjoint_union_list_l in H
  | H : _ ##ₘ ⋃ _ |- _ => apply map_disjoint_union_list_r in H
  | H : ∅ ##ₘ _ |- _ => clear H
  | H : _ ##ₘ ∅ |- _ => clear H
  | H : Forall (.##ₘ _) _ |- _ => rewrite Forall_vlookup in H
  | H : Forall (.##ₘ _) [] |- _ => clear H
  | H : Forall (.##ₘ _) (_ :: _) |- _ => rewrite Forall_cons in H; destruct H
  | H : Forall (.##ₘ _) (_ :: _) |- _ => rewrite Forall_app in H; destruct H
  end.

(** To prove a disjointness property, we first decompose all hypotheses, and
then use an auto database to prove the required property. *)
Create HintDb map_disjoint discriminated.
Ltac solve_map_disjoint :=
  solve [decompose_map_disjoint; auto with map_disjoint].

(** We declare these hints using [Hint Extern] instead of [Hint Resolve] as
[eauto] works badly with hints parametrized by type class constraints. *)
Hint Extern 1 (_ ##ₘ _) => done : map_disjoint.
Hint Extern 2 (∅ ##ₘ _) => apply map_disjoint_empty_l : map_disjoint.
Hint Extern 2 (_ ##ₘ ∅) => apply map_disjoint_empty_r : map_disjoint.
Hint Extern 2 ({[ _ := _ ]} ##ₘ _) =>
  apply map_disjoint_singleton_l_2 : map_disjoint.
Hint Extern 2 (_ ##ₘ {[ _ := _ ]}) =>
  apply map_disjoint_singleton_r_2 : map_disjoint.
Hint Extern 2 (_ ∪ _ ##ₘ _) => apply map_disjoint_union_l_2 : map_disjoint.
Hint Extern 2 (_ ##ₘ _ ∪ _) => apply map_disjoint_union_r_2 : map_disjoint.
Hint Extern 2 ({[_:= _]} ##ₘ _) => apply map_disjoint_singleton_l : map_disjoint.
Hint Extern 2 (_ ##ₘ {[_:= _]}) => apply map_disjoint_singleton_r : map_disjoint.
Hint Extern 2 (<[_:=_]>_ ##ₘ _) => apply map_disjoint_insert_l_2 : map_disjoint.
Hint Extern 2 (_ ##ₘ <[_:=_]>_) => apply map_disjoint_insert_r_2 : map_disjoint.
Hint Extern 2 (delete _ _ ##ₘ _) => apply map_disjoint_delete_l : map_disjoint.
Hint Extern 2 (_ ##ₘ delete _ _) => apply map_disjoint_delete_r : map_disjoint.
Hint Extern 2 (list_to_map _ ##ₘ _) =>
  apply map_disjoint_list_to_map_zip_l_2 : mem_disjoint.
Hint Extern 2 (_ ##ₘ list_to_map _) =>
  apply map_disjoint_list_to_map_zip_r_2 : mem_disjoint.
Hint Extern 2 (⋃ _ ##ₘ _) => apply map_disjoint_union_list_l_2 : mem_disjoint.
Hint Extern 2 (_ ##ₘ ⋃ _) => apply map_disjoint_union_list_r_2 : mem_disjoint.
Hint Extern 2 (foldr delete _ _ ##ₘ _) =>
  apply map_disjoint_foldr_delete_l : map_disjoint.
Hint Extern 2 (_ ##ₘ foldr delete _ _) =>
  apply map_disjoint_foldr_delete_r : map_disjoint.

(** The tactic [simpl_map by tac] simplifies occurrences of finite map look
ups. It uses [tac] to discharge generated inequalities. Look ups in unions do
not have nice equational properties, hence it invokes [tac] to prove that such
look ups yield [Some]. *)
Tactic Notation "simpl_map" "by" tactic3(tac) := repeat
  match goal with
  | H : context[ ∅ !! _ ] |- _ => rewrite lookup_empty in H
  | H : context[ (<[_:=_]>_) !! _ ] |- _ =>
    rewrite lookup_insert in H || rewrite lookup_insert_ne in H by tac
  | H : context[ (alter _ _ _) !! _] |- _ =>
    rewrite lookup_alter in H || rewrite lookup_alter_ne in H by tac
  | H : context[ (delete _ _) !! _] |- _ =>
    rewrite lookup_delete in H || rewrite lookup_delete_ne in H by tac
  | H : context[ {[ _ := _ ]} !! _ ] |- _ =>
    rewrite lookup_singleton in H || rewrite lookup_singleton_ne in H by tac
  | H : context[ (_ <$> _) !! _ ] |- _ => rewrite lookup_fmap in H
  | H : context[ (omap _ _) !! _ ] |- _ => rewrite lookup_omap in H
  | H : context[ lookup (A:=?A) ?i (?m1 ∪ ?m2) ] |- _ =>
    let x := fresh in evar (x:A);
    let x' := eval unfold x in x in clear x;
    let E := fresh in
    assert ((m1 ∪ m2) !! i = Some x') as E by (clear H; by tac);
    rewrite E in H; clear E
  | |- context[ ∅ !! _ ] => rewrite lookup_empty
  | |- context[ (<[_:=_]>_) !! _ ] =>
    rewrite lookup_insert || rewrite lookup_insert_ne by tac
  | |- context[ (alter _ _ _) !! _ ] =>
    rewrite lookup_alter || rewrite lookup_alter_ne by tac
  | |- context[ (delete _ _) !! _ ] =>
    rewrite lookup_delete || rewrite lookup_delete_ne by tac
  | |- context[ {[ _ := _ ]} !! _ ] =>
    rewrite lookup_singleton || rewrite lookup_singleton_ne by tac
  | |- context[ (_ <$> _) !! _ ] => rewrite lookup_fmap
  | |- context[ (omap _ _) !! _ ] => rewrite lookup_omap
  | |- context [ lookup (A:=?A) ?i ?m ] =>
    let x := fresh in evar (x:A);
    let x' := eval unfold x in x in clear x;
    let E := fresh in
    assert (m !! i = Some x') as E by tac;
    rewrite E; clear E
  end.

Create HintDb simpl_map discriminated.
Tactic Notation "simpl_map" := simpl_map by eauto with simpl_map map_disjoint.

Hint Extern 80 ((_ ∪ _) !! _ = Some _) => apply lookup_union_Some_l : simpl_map.
Hint Extern 81 ((_ ∪ _) !! _ = Some _) => apply lookup_union_Some_r : simpl_map.
Hint Extern 80 ({[ _:=_ ]} !! _ = Some _) => apply lookup_singleton : simpl_map.
Hint Extern 80 (<[_:=_]> _ !! _ = Some _) => apply lookup_insert : simpl_map.

(** Now we take everything together and also discharge conflicting look ups,
simplify overlapping look ups, and perform cancellations of equalities
involving unions. *)
Tactic Notation "simplify_map_eq" "by" tactic3(tac) :=
  decompose_map_disjoint;
  repeat match goal with
  | _ => progress simpl_map by tac
  | _ => progress simplify_eq/=
  | _ => progress simpl_option by tac
  | H : {[ _ := _ ]} !! _ = None |- _ => rewrite lookup_singleton_None in H
  | H : {[ _ := _ ]} !! _ = Some _ |- _ =>
    rewrite lookup_singleton_Some in H; destruct H
  | H1 : ?m1 !! ?i = Some ?x, H2 : ?m2 !! ?i = Some ?y |- _ =>
    let H3 := fresh in
    feed pose proof (lookup_weaken_inv m1 m2 i x y) as H3; [done|by tac|done|];
    clear H2; symmetry in H3
  | H1 : ?m1 !! ?i = Some ?x, H2 : ?m2 !! ?i = None |- _ =>
    let H3 := fresh in
    apply (lookup_weaken _ m2) in H1; [congruence|by tac]
  | H : ?m ∪ _ = ?m ∪ _ |- _ =>
    apply map_union_cancel_l in H; [|by tac|by tac]
  | H : _ ∪ ?m = _ ∪ ?m |- _ =>
    apply map_union_cancel_r in H; [|by tac|by tac]
  | H : {[?i := ?x]} = ∅ |- _ => by destruct (map_non_empty_singleton i x)
  | H : ∅ = {[?i := ?x]} |- _ => by destruct (map_non_empty_singleton i x)
  | H : ?m !! ?i = Some _, H2 : ?m !! ?j = None |- _ =>
     unless (i ≠ j) by done;
     assert (i ≠ j) by (by intros ?; simplify_eq)
  end.
Tactic Notation "simplify_map_eq" "/=" "by" tactic3(tac) :=
  repeat (progress csimpl in * || simplify_map_eq by tac).
Tactic Notation "simplify_map_eq" :=
  simplify_map_eq by eauto with simpl_map map_disjoint.
Tactic Notation "simplify_map_eq" "/=" :=
  simplify_map_eq/= by eauto with simpl_map map_disjoint.
