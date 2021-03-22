Require Import Reals Bool Relations RelationClasses List ListSet Setoid Permutation EqdepFacts IndefiniteDescription Classical Sorting.
Import ListNotations.
From CasperCBC
Require Import Lib.Preamble Lib.ListExtras Lib.ListSetExtras Lib.SortedLists VLSM.Equivocation CBC.Protocol Lib.RealsExtras VLSM.Decisions Lib.Measurable.

Class InhabitedTwice V := { inhabited_twice : exists (v1 v2 : V), v1 <> v2 }.

Class DistinctChoice V `{HscV : StrictlyComparable V} `{Hit : InhabitedTwice V}.

Program Instance distinct_choice {V} `{HscV : StrictlyComparable V} `{Hit : InhabitedTwice V} : DistinctChoice V.

Lemma distinct_choice_total
  {V} `{Hdc : DistinctChoice V}
  : forall v1 : V, exists v2 : V, v1 <> v2.
Proof.
  intros.
  destruct inhabited_twice  as [v1' [v2' Hneq]].
  destruct (compare_eq_dec v1 v1') eqn:Heq.
  - subst. exists v2'. assumption.
  - exists v1'. assumption.
Qed.

Definition get_distinct_sender
  {V} `{Hdc : DistinctChoice V}
  (v : V)
  :=
  proj1_sig (constructive_indefinite_description (fun v' => v <> v') (distinct_choice_total v)).

Definition get_distinct_sender_correct
  {V} `{Hdc : DistinctChoice V}
  (v : V)
  :=
  proj2_sig (constructive_indefinite_description (fun v' => v <> v') (distinct_choice_total v)).

Lemma get_distinct_sender_correct'
  {V} `{Hdc : DistinctChoice V}
  : forall v, get_distinct_sender v <> v.
Proof.
  intros. unfold get_distinct_sender.
  assert (H_useful := get_distinct_sender_correct v).
  simpl in *.
  intro H_absurd.
  apply H_useful; symmetry; assumption.
Qed.


Lemma senders_fault_weight_eq
   `{EqDecision V} `{Hm : Measurable V}
  : forall lv1 lv2 : list V,
    NoDup lv1 ->
    NoDup lv2 ->
    set_eq lv1 lv2 ->
    sum_weights lv1 = sum_weights lv2.
Proof.
  induction lv1 as [|hd tl IHlv1]; intros lv2 H_lv1 H_lv2 H_eq.
  - destruct lv2.
    reflexivity.
    inversion H_eq.
    spec H0 v (in_eq v lv2).
    inversion H0.
  - simpl.
    (* hd must be in duplicate-free lv2 *)
    spec IHlv1 (set_remove decide_eq hd lv2).
    spec IHlv1.
    apply NoDup_cons_iff in H_lv1. tauto.
    spec IHlv1.
    now apply set_remove_nodup.
    spec IHlv1.
    replace tl with (set_remove decide_eq hd (hd :: tl)).
    apply set_eq_remove; try assumption.
    now rewrite set_remove_first.
    (* Now. *)
    rewrite IHlv1.
    symmetry.
    apply sum_weights_in. assumption.
    destruct H_eq as [H_eq _].
    spec H_eq hd (in_eq hd tl). assumption.
Qed.

Lemma pivotal_validator_extension
  `{EqDecision V} `{Hrt : ReachableThreshold V}
  : forall vsfix vss,
  NoDup vsfix ->
  (* and whose added weight does not pass the threshold *)
  (sum_weights vsfix <= proj1_sig threshold)%R ->
  NoDup (vss ++ vsfix) ->
  (sum_weights (vss ++ vsfix) > proj1_sig threshold)%R ->
  exists (vs : list V),
  NoDup vs /\
  incl vs vss /\
  (sum_weights (vs ++ vsfix) > proj1_sig threshold)%R /\
  exists v,
    In v vs /\
    (sum_weights ((set_remove decide_eq v vs) ++ vsfix) <= proj1_sig threshold)%R.
Proof.
  destruct threshold as [t about_t]; simpl in *.
  intro.  induction vss; intros.
  - simpl in H2. exfalso. apply (Rge_gt_trans t) in H2; try (apply Rle_ge; assumption).
    apply Rgt_not_eq in H2. apply H2. reflexivity.
  - simpl in H2. destruct (Rtotal_le_gt (sum_weights (vss ++ vsfix)) t).
    + exists (a :: vss). repeat split; try assumption.
      * apply append_nodup_left in H1. assumption.
      * apply incl_refl.
      * exists a. split; try (left; reflexivity).
        simpl. rewrite decide_True; try reflexivity. assumption.
    + simpl in H1. apply NoDup_cons_iff in H1. destruct H1 as [Hnin Hvss]. apply IHvss in H3; try assumption.
      destruct H3 as [vs [Hvs [Hincl Hex]]].
      exists vs. repeat (split;try assumption). apply incl_tl. assumption.
Qed.

(* From threshold.v *)
Lemma validators_pivotal_ind
  `{EqDecision V} `{Hrt : ReachableThreshold V}
  : forall vss,
  NoDup vss ->
  (sum_weights vss > proj1_sig threshold)%R ->
  exists (vs : list V),
  NoDup vs /\
  incl vs vss /\
  (sum_weights vs > proj1_sig threshold)%R /\
  exists v,
    In v vs /\
    (sum_weights (set_remove decide_eq v vs) <= proj1_sig threshold)%R.
Proof.
  intros.
  rewrite <- (app_nil_r vss) in H.   rewrite <- (app_nil_r vss) in H0.
  apply (pivotal_validator_extension [] vss) in H0; try assumption.
  - destruct H0 as [vs [NoDupvs [Inclvs [Gt [v [Inv Lt]]]]]].
    rewrite app_nil_r in Lt. rewrite app_nil_r in Gt.
    exists vs. repeat (split; try assumption).
    exists v. repeat (split; try assumption).
  - constructor.
  - destruct threshold as [t about_t]; simpl in *.
    apply Rge_le; assumption.
Qed.

Lemma sufficient_validators_pivotal
  `{EqDecision V} `{Hrt : ReachableThreshold V}
  : exists (vs : list V),
    NoDup vs /\
    (sum_weights vs > proj1_sig threshold)%R /\
    exists v,
      In v vs /\
      (sum_weights (set_remove decide_eq v vs) <= proj1_sig threshold)%R.
Proof.
  destruct reachable_threshold as [vs [Hvs Hweight]].
  apply (validators_pivotal_ind vs Hvs) in Hweight.
  destruct Hweight as [vs' [Hnd [Hincl H]]].
  destruct threshold as [t about_t]; simpl in *.
  exists vs'. repeat (split; try assumption).
Qed.

Definition potentially_pivotal
  `{Hrt : ReachableThreshold V}
  (v : V) : Prop
  :=
  exists (vs : list V),
      NoDup vs /\
      ~In v vs /\
      (sum_weights vs <= proj1_sig threshold)%R /\
      (sum_weights vs > proj1_sig threshold - (proj1_sig (weight v)))%R.

Lemma exists_pivotal_validator
  `{EqDecision V} `{Hrt : ReachableThreshold V}
  : exists v, potentially_pivotal v.
Proof.
  destruct sufficient_validators_pivotal as [vs [Hnodup [Hgt [v [Hin Hlte]]]]].
  exists v.
  subst. exists (set_remove decide_eq v vs). repeat split.
  - apply set_remove_nodup. assumption.
  - intro. apply set_remove_iff in H; try assumption. destruct H. apply H0. reflexivity.
  - assumption.
  - rewrite (sum_weights_in v) in Hgt; try assumption.
    rewrite Rplus_comm in Hgt.
    apply (Rplus_gt_compat_r (- (proj1_sig (weight v))%R)) in Hgt.
    rewrite Rplus_assoc in Hgt.
    rewrite Rplus_opp_r in Hgt.
    rewrite Rplus_0_r in Hgt.
    assumption.
Qed.

Definition get_estimate {state C} `{Estimator state C} (s : state) :=
  proj1_sig (constructive_indefinite_description (estimator s) (estimator_total s)).

Definition get_estimate_correct {state C} `{Estimator state C} (s : state) :=
  proj2_sig (constructive_indefinite_description (estimator s) (estimator_total s)).

Lemma get_estimate_consistent {state C} `{Estimator state C}
  (s : state)
  (c : C)
  (Heq : get_estimate s = c)
  : estimator s c.
Proof.
  unfold get_estimate in Heq.
  remember (constructive_indefinite_description (estimator s) (estimator_total s)) as Hchoice. destruct Hchoice as [c' Hc'].
  simpl in Heq. subst. assumption.
Qed.

(* Estimator approval condition *)
Definition valid_estimate
  {C state} `{Estimator state C}
  (c : C) (sigma : state) : Prop
  :=
    estimator sigma c.
