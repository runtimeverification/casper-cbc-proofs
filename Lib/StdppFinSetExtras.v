From CasperCBC.stdpp Require Import base fin_sets tactics.
From CasperCBC.Lib Require Import Preamble.


Section fin_set.
Context
  `{FinSet A C}.

Section general.
  
  Lemma union_size_ge_size1
    (X Y : C) :
    size (X ∪ Y) >= size X.
  Proof.
    apply subseteq_size.
    apply subseteq_union.
    set_solver.
  Qed.
  
  Lemma union_size_ge_size2
    (X Y : C) :
    size (X ∪ Y) >= size Y.
  Proof.
    apply subseteq_size.
    apply subseteq_union.
    set_solver.
  Qed.
  
  Lemma union_size_ge_average
    (X Y : C) :
    2 * size (X ∪ Y) >= size X + size Y.
  Proof.
    specialize (union_size_ge_size1 X Y) as Hx.
    specialize (union_size_ge_size2 X Y) as Hy.
    lia.
  Qed.
  
  Lemma difference_size_le_self
    (X Y : C) :
    size (X ∖  Y) <= size X.
  Proof.
    apply subseteq_size.
    apply elem_of_subseteq.
    intros x Hx.
    apply elem_of_difference in Hx. intuition.
  Qed.
  
  Lemma union_size_le_sum
    (X Y : C) :
    size (X ∪ Y) <= size X + size Y.
  Proof.
    specialize (size_union_alt X Y) as Halt.
    rewrite Halt.
    specialize (difference_size_le_self Y X).
    lia.
  Qed.
  
  Lemma intersection_size1
    (X Y : C) :
    size (X ∩ Y) <= size X.
  Proof.
    apply subseteq_size with (X0 := X ∩ Y) (Y0 := X).
    set_solver.
  Qed.
  
  Lemma intersection_size2
    (X Y : C) :
    size (X ∩ Y) <= size Y.
  Proof.
    apply subseteq_size with (X0 := X ∩ Y) (Y0 := Y).
    set_solver.
  Qed.
  
  Lemma difference_size_subset
    (X Y : C)
    (Hsub : Y ⊆ X) :
    (Z.of_nat (size (X ∖ Y)) = size X - size Y)%Z.
  Proof.
    assert (Htemp : Y ∪ (X ∖ Y) ≡ X). {
      apply set_equiv_equivalence.
      intros a.
      split; intros Ha.
      - set_solver.
      - destruct (@decide (a ∈ Y)).
        apply elem_of_dec_slow.
        + apply elem_of_union. left. intuition.
        + apply elem_of_union. right. set_solver. 
    }
    assert (Htemp2 : size Y + size (X ∖ Y) = size X). {
      specialize (size_union Y (X ∖ Y)) as Hun. 
      spec Hun. {
        apply elem_of_disjoint.
        intros a Ha Ha2.
        apply elem_of_difference in Ha2.
        intuition.
      }
      rewrite Htemp in Hun.
      intuition.
    }
    lia.
  Qed.
  
  Lemma difference_with_intersection
    (X Y : C) :
    X ∖ Y ≡ X ∖ (X ∩ Y).
  Proof.
    set_solver.
  Qed.
  
  Lemma difference_size
    (X Y : C) :
    (Z.of_nat (size (X ∖ Y)) = size X - size (X ∩ Y))%Z.
  Proof.
    rewrite difference_with_intersection.
    specialize (difference_size_subset X (X ∩ Y)) as Hdif.
    set_solver.
  Qed.
  
  Lemma difference_size_ge_disjoint_case
    (X Y : C) :
    size (X ∖ Y) >= size X - size Y.
  Proof.
    specialize (difference_size X Y).
    specialize (intersection_size2 X Y).
    lia.
  Qed.
  
  Lemma list_to_set_size
    (l : list A) :
    size (list_to_set l (C := C)) <= length l.
  Proof.
    induction l.
    - simpl. 
      rewrite size_empty. lia.
    - simpl.
      specialize (union_size_le_sum ({[a]}) (list_to_set l)) as Hun_size.
      rewrite size_singleton in Hun_size.
      lia.
  Qed.
End general.

Section filter.
  Context (P P2 : A → Prop) 
          `{!∀ x, base.Decision (P x)} 
          `{!∀ x, base.Decision (P2 x)}
          (X Y : C).
  
  Lemma filter_subset
    (Hsub : X ⊆ Y) :
    filter P X ⊆ filter P Y.
  Proof.
    intros a HaX.
    apply elem_of_filter in HaX.
    apply elem_of_filter.
    set_solver.
  Qed.
  
  Lemma filter_subprop
    (Hsub : forall a, (P a -> P2 a)) :
    filter P X ⊆ filter P2 X.
  Proof.
    intros a HaP.
    apply elem_of_filter in HaP.
    apply elem_of_filter.
    intuition.
  Qed.
  
End filter.
End fin_set.

Section map.
  Context 
    `{FinSet A C}
    `{FinSet B D}.
  
  Lemma set_map_subset
    (f : A -> B)
    (X Y : C)
    (Hsub : X ⊆ Y) :
    set_map (D := D) f X ⊆ set_map (D := D) f Y.
  Proof.
    intros a Ha.
    apply elem_of_map in Ha.
    apply elem_of_map.
    intuition firstorder.
  Qed.
  
  Lemma set_map_size_upper_bound
    (f : A -> B)
    (X : C) :
    size (set_map (D := D) f X) <= size X.
  Proof.
    unfold set_map. 
    remember (f <$> elements X) as fX.
    specialize (list_to_set_size (A := B) fX) as Hsize.
    
    assert (length fX = size X). {
      unfold size. unfold set_size. simpl.
      subst fX.
      apply fmap_length.
    }
    lia.
  Qed.
End map.