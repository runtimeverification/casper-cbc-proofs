Require Import List FinFun.
Import ListNotations.
From CasperCBC Require Import Preamble ListExtras.

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
  destruct sum_finite as [Hnodup Hfull].
  unfold left_listing.
  split.
  - clear Hfull. unfold list_sum_project_left.
    induction sum_listing.
    + constructor.
    + inversion Hnodup. subst. specialize (IHl H2).
      destruct a; try assumption.
      simpl. constructor; try assumption.
      intro contra. elim H1.
      apply in_map_option in contra.
      destruct contra as [a [Ha Hl0]].
      unfold sum_project_left in Hl0.
      destruct a; congruence.
  - intro a. specialize (Hfull (inl a)).
    apply in_map_option. exists (inl a).
    split; try assumption.
    reflexivity.
Qed.

Lemma right_finite
  (sum_finite : Listing sum_listing)
  : Listing (right_listing sum_finite).
Proof.
  destruct sum_finite as [Hnodup Hfull]. unfold right_listing.
  split.
  - clear Hfull.
    unfold right_listing. unfold list_sum_project_right.
    induction sum_listing.
    + constructor.
    + inversion Hnodup. subst. specialize (IHl H2).
      destruct a; try assumption.
      simpl. constructor; try assumption.
      intro contra. elim H1.
      apply in_map_option in contra.
      destruct contra as [a [Ha Hl0]].
      unfold sum_project_right in Hl0.
      destruct a; congruence.
  - intro a. specialize (Hfull (inr a)).
    apply in_map_option. exists (inr a).
    split; try assumption.
    reflexivity.
Qed.

End sum_listing.
