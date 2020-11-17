Require Import List FinFun.
Import ListNotations.
From CasperCBC Require Import Preamble ListExtras.

Lemma map_option_listing
      {A B : Type} (f: A -> option B) (g: B -> A)
      (f_proj_inj: forall a b, f a = Some b -> a = g b)
      (f_surj: forall b, f (g b) = Some b)
      (A_listing: list A) (A_finite : Listing A_listing) : Listing (map_option f A_listing).
Proof.
  destruct A_finite as [Hnodup Hfull].
  split.
  - clear Hfull.
    induction A_listing as [|a l IHl].
    + constructor.
    + inversion_clear Hnodup as [|? ? H1 H2].
      specialize (IHl H2); clear H2.
      simpl.
      destruct (f a) eqn:Hfa;[|assumption].
      apply f_proj_inj in Hfa. subst a.
      constructor;[|assumption].
      contradict H1.
      apply in_map_option in H1.
      destruct H1 as [a [Ha Hfa]].
      apply f_proj_inj in Hfa.
      subst a.
      assumption.
  - intro b.
    specialize (Hfull (g b)).
    apply in_map_option.
    exists (g b).
    split;[assumption|].
    apply f_surj.
Qed.

Section sum_listing.
(** 'Listing' for the sum type implies 'Listing' for each projection *)

Context
  {Left Right : Type}
  {sum_listing : list (Left + Right)}
  .

Definition left_listing
  (sum_finite : Listing sum_listing)
  : list Left
  := list_sum_project_left sum_listing.

Definition right_listing
  (sum_finite : Listing sum_listing)
  : list Right
  := list_sum_project_right sum_listing.

Lemma left_finite
  (sum_finite : Listing sum_listing)
  : Listing (left_listing sum_finite).
Proof.
  revert sum_finite.
  apply map_option_listing with (g:=inl).
  destruct a;simpl;congruence.
  reflexivity.
Qed.

Lemma right_finite
  (sum_finite : Listing sum_listing)
  : Listing (right_listing sum_finite).
Proof.
  revert sum_finite.
  apply map_option_listing with (g:=inr).
  destruct a;simpl;congruence.
  reflexivity.
Qed.

End sum_listing.
