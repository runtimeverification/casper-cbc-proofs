Require Import
  List ListSet FinFun Arith Bool
  .
Import ListNotations.
From CasperCBC
Require Import
  Lib.Preamble
  Lib.ListExtras
  Lib.SumWeights
  CBC.Common
  CBC.Equivocation
  VLSM.Common
  VLSM.ListValidator.ListValidator
  VLSM.ListValidator.Equivocation
  VLSM.ListValidator.Observations
  .

(** This is a version of the List Validator node which uses an
   "equivocation aware" estimator. 
   
   This estimator ignores projections onto indices
   that correspond to validators that can be proven equivocating using
   the node's local observations.
   
   See [ListValidator.v] for the traditional LV estimator. *)

Section EquivocationAwareValidator.

  Context
    {index : Type}
    {index_self : index}
    {index_listing : list index}
    {Hfinite : Listing index_listing}
    {idec : EqDecision index}
    (X := @VLSM_list _ index_self index_listing idec)
    {Mindex : Measurable index}
    {Rindex : ReachableThreshold index}
    (eqv := @simp_lv_basic_equivocation index index_self index_listing Hfinite idec Mindex Rindex)
    .

  Existing Instance eqv.

  Definition get_no_equivocating_states
    (s : @state index index_listing)
    (eqv_validators : list index)
    : list state
    :=
    map (fun i: index => project s i)
      (set_diff decide_eq index_listing eqv_validators).

  Definition no_equivocating_decisions
    (s : @state index index_listing)
    (eqv_validators : list index)
    : list (option bool)
    :=
    match s with
    | Bottom => []
    | _ => List.map decision (get_no_equivocating_states s eqv_validators)
    end.

  Definition equivocation_aware_estimator (s : state) (b : bool) : Prop :=
    let eqv_validators := equivocating_validators s in
    let decisions := no_equivocating_decisions s eqv_validators in
    match s with
    | Bottom => True
    | Something c some => in_mode (mode decisions) b
    end.
  
  Global Instance equivocation_aware_estimator_dec : RelDecision equivocation_aware_estimator.
  Proof.
    unfold RelDecision. intros s b.
    unfold equivocation_aware_estimator.
    destruct s;[left; intuition|].
    apply in_mode_dec.
  Qed.
 
  (** If at least one projection is non-equivocating,
     the estimator is non-empty (it relates to either true or false). *)
     
  Lemma ea_estimator_total 
    (s : state)
    (b : bool)
    (Hne : no_equivocating_decisions s (equivocating_validators s) <> [])
    (Hnotb : ~ equivocation_aware_estimator s b) :
    equivocation_aware_estimator s (negb b).
  Proof.
    unfold equivocation_aware_estimator in *.
    destruct s;[intuition|].
    unfold in_mode in *.
    remember (mode
             (no_equivocating_decisions 
             (Something b0 is) 
             (equivocating_validators (Something b0 is))))
             as modes.
    
    destruct (inb decide_eq (Some b) modes) eqn : eq_inb; [intuition|].
   
    assert (Hsome : exists (ob : option bool), In ob (modes)). {
      assert (modes <> []) by (rewrite Heqmodes; apply mode_not_empty; intuition).
      destruct modes;[intuition congruence|].
      exists o. simpl. left. intuition.
    }
    
    destruct Hsome as [ob Hob].
    destruct ob eqn : eq_ob.
    - destruct (inb decide_eq (Some (negb b)) modes) eqn : eq_inb2;[intuition|].
      apply in_correct in Hob.
      destruct b; destruct b1; simpl in *; intuition congruence.
    - apply in_correct in Hob. intuition congruence. 
  Qed.

  Definition VLSM_equivocation_aware_list : VLSM message
    :=
    @VLSM_list index index_self index_listing idec equivocation_aware_estimator.

End EquivocationAwareValidator.
