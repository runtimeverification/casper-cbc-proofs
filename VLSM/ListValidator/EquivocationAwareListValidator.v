Require Import
  List ListSet FinFun Arith Bool
  .
Import ListNotations.
From CasperCBC
Require Import
  Lib.Preamble
  Lib.ListExtras
  CBC.Common
  CBC.Equivocation
  VLSM.Common
  VLSM.ListValidator.ListValidator
  VLSM.ListValidator.Equivocation
  .

Section EquivocationAwareValidator.

  Context
    {index : Type}
    {index_self : index}
    {index_listing : list index}
    {Hfinite : Listing index_listing}
    {idec : EqDec index}
    (X := @VLSM_list _ index_self index_listing idec)
    {Mindex : Measurable index}
    {Rindex : ReachableThreshold index}
    (eqv := @lv_basic_equivocation index index_listing Hfinite idec Mindex Rindex)
    .

  Existing Instance eqv.

  Definition get_no_equivocating_states
    (s : @state index index_listing)
    (eqv_validators : list index)
    : list state
    :=
    map (fun i: index => project s i)
      (set_diff eq_dec index_listing eqv_validators).

  Definition no_equivocating_decisions
    (s : @state index index_listing)
    (eqv_validators : list index)
    : list (option bool)
    :=
    match s with
    | Bottom => []
    | _ => List.map decision (get_no_equivocating_states s eqv_validators)
    end.
    
  Definition equivocation_aware_estimatorb (s : state) (b : bool) : bool :=
    let eqv_validators := equivocating_validators s in
    let decisions := no_equivocating_decisions s eqv_validators in
    match s with
    | Bottom => true
    | Something c some => in_mode_b (mode decisions) b 
    end.

  Definition equivocation_aware_estimator (s : state) (b : bool) : Prop :=
    let eqv_validators := equivocating_validators s in
    let decisions := no_equivocating_decisions s eqv_validators in
    match s with
    | Bottom => True
    | Something c some => in_mode_b (mode decisions) b = true 
    end.
    
  Lemma ea_estimator_total 
    (s : state)
    (b : bool)
    (Hne : no_equivocating_decisions s (equivocating_validators s) <> [])
    (Hnotb : equivocation_aware_estimatorb s b = false) :
    equivocation_aware_estimatorb s (negb b) = true.
  Proof.
    unfold equivocation_aware_estimatorb in Hnotb.
    destruct s.
    discriminate Hnotb.
    unfold in_mode_b in Hnotb.
    remember (no_equivocating_decisions (Something b0 is) (equivocating_validators (Something b0 is))) as d.
    destruct (inb (option_eq_dec bool_dec) (Some b) (mode d)) eqn : eq_b.
    discriminate Hnotb.
    assert (inb (option_eq_dec bool_dec) (Some (negb b)) (mode d) = true). {  
      apply in_correct' in eq_b.
      apply in_correct' in Hnotb.
      apply in_correct.
      assert (mode d <> []). {
        apply mode_not_empty.
        assumption.
      }
      assert (exists x, In x (mode d)). {
        destruct (mode d).
        elim H.
        reflexivity.
        exists o.
        intuition.
      }
      destruct H0 as [x Hin].
      destruct x.
      + destruct (eq_dec (negb b) b1).
        rewrite <- e in Hin.
        assumption.
        destruct b; destruct b1.
        simpl. contradiction.
        simpl. assumption.
        simpl. assumption.
        simpl. contradiction.
      + contradiction.
    }
    unfold equivocation_aware_estimatorb.
    rewrite <- Heqd.
    unfold in_mode_b.
    rewrite H.
    reflexivity.
  Qed.

  Definition VLSM_equivocation_aware_list : VLSM message
    :=
    @VLSM_list index index_self index_listing idec equivocation_aware_estimator.

End EquivocationAwareValidator.
