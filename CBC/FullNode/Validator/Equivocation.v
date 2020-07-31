Require Import
  Bool
  List
  Coq.Lists.ListSet
  Coq.Classes.RelationClasses
  .

From CasperCBC
    Require Import
      Preamble
      ListExtras
      Validator.State
      CBC.Common
      CBC.Equivocation
    .

Import ListNotations.

Section Equivocation.

Context
    (C V : Type)
    {about_C : StrictlyComparable C}
    {about_V : StrictlyComparable V}
    {measurable_V : Measurable V}
    {reachable_threshold : ReachableThreshold V}
    .

Definition validator_message_preceeds_fn
  (m1 m2 : State.message C V)
  : bool
  :=
  match m2 with
  | (c, v, j) => inb compare_eq_dec m1 (fst (unmake_justification j))
  end.

Definition validator_message_preceeds
  (m1 m2 : State.message C V)
  : Prop
  :=
  validator_message_preceeds_fn m1 m2 = true.

Lemma  validator_message_preceeds_irreflexive'
  (c : C)
  (v : V)
  (j1 j2 : justification C V)
  (Hincl : justification_incl j2 j1)
  : ~inb compare_eq_dec ((c, v, j1)) (fst (unmake_justification j2)) = true.
Proof.
  generalize dependent j1.
  generalize dependent v.
  generalize dependent c.
  apply
    (justification_mut_ind C V
      (fun j2 =>
        forall (c : C) (v : V) (j1 : justification C V),
        justification_incl j2 j1 ->
        inb compare_eq_dec ((c, v, j1)) (fst (unmake_justification j2)) <> true
      )
      (fun m =>
        forall (c : C) (v : V) (j1 : justification C V),
        justification_incl (get_justification m) j1 ->
        inb compare_eq_dec ((c, v, j1)) (fst (unmake_justification (get_justification m))) <> true
      )
      (fun msgs =>
        forall (c : C) (v : V) (j1 : justification C V),
        message_set_incl msgs (get_message_set j1) ->
        inb compare_eq_dec ((c, v, j1)) (unmake_message_set msgs) <> true
      )
    ); simpl; intros; intro Hin; try discriminate.
  - specialize (H c v j1 H0).
    elim H. assumption.
  - specialize (H c v j1 H1).
    elim H. assumption.
  - specialize (H c0 v0 j1 H0).
    elim H. assumption.
  - specialize
      (in_correct
        (set_add compare_eq_dec m (unmake_message_set m0))
        (Msg _ _ c v j1)
      ); intro Hin_in
    ; apply proj2 in Hin_in
    ;  apply Hin_in in Hin; clear Hin_in
    ; apply set_add_iff in Hin
    ; destruct Hin as [Hin | Hin]; subst
    .
    + simpl in *.
      elim (H c v j1); try apply justification_incl_refl.
      specialize
        (in_correct
          (unmake_message_set (get_message_set j1))
          (Msg _ _ c v j1)
        ); intro Hin_in
      ; apply proj1 in Hin_in.
      apply Hin_in.
      apply in_unmake_message_set.
      apply H1.
      left.
      reflexivity.
    + apply in_correct in Hin.
      elim (H0 c v j1); try assumption.
      intros m' Hm'.
      apply H1.
      right.
      assumption.
Qed.

Lemma validator_message_preceeds_irreflexive
  : Irreflexive validator_message_preceeds.
Proof.
  intros x.
  destruct x as (c, v, j).
  unfold complement. unfold validator_message_preceeds. simpl.
  apply validator_message_preceeds_irreflexive'.
  apply justification_incl_refl.
Qed.

Global Instance full_node_equivocation
  : HasEquivocation (State.message C V)
  :=
    {| about_message := message_type
    ; sender := State.sender
    ; message_preceeds_fn := validator_message_preceeds_fn
    |}.

End Equivocation.