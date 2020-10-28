Require Import Reals Bool Relations RelationClasses List ListSet Setoid Permutation EqdepFacts.
Import ListNotations.
From CasperCBC
Require Import Lib.Preamble Lib.ListExtras Lib.ListSetExtras Lib.SortedLists CBC.Protocol.

(** Building blocks for instancing CBC_protocol_eq with a concrete binary consensus protocol **)
(** Set equality on states **)

Section States.

  Inductive C : Type :=
  | zero : C
  | one : C.

  Definition C_inhabited : C := one.

  Definition C_compare (c1 c2 : C) : comparison :=
    match c1 with
    | zero => match c2 with
             | zero => Eq
             | one => Lt
             end
    | one => match c2 with
            | zero => Gt
            | one => Eq
            end
    end.

  Lemma C_compare_reflexive : CompareReflexive C_compare.
  Proof.
    red. intros; split; intros; destruct x; destruct y; try discriminate; try reflexivity.
  Qed.

  Lemma C_compare_transitive : CompareTransitive C_compare.
  Proof. red; intros; destruct x; destruct y; destruct z; destruct comp; try discriminate; try eauto.
  Qed.

  Lemma C_compare_strictorder : CompareStrictOrder C_compare.
  Proof. split. apply C_compare_reflexive. apply C_compare_transitive. Qed.

  Instance about_C : StrictlyComparable C :=
    { inhabited := C_inhabited;
      compare := C_compare;
      compare_strictorder := C_compare_strictorder;
    }.

  Variables V H : Type.
  Context (about_V : `{StrictlyComparable V})
          (about_H : `{StrictlyComparable H}).

  Definition posR : Type := {r : R | (r > 0)%R}.
  Definition posR_proj1 (r : posR) := proj1_sig r.
  Coercion posR_proj1 : posR >-> R.

  Parameter weight : V -> posR.
  Definition sum_weights (l : list V) : R :=
    fold_right (fun v r => ((weight v) + r)%R) 0%R l.

  Parameters (t_full : {r | (r >= 0)%R})
             (suff_val_full : exists vs, NoDup vs /\ ((fold_right (fun v r => ((weight v) + r)%R) 0%R) vs > (proj1_sig t_full))%R).

  (* Additional types for defining light node states *)
  Definition justification_type : Type := list H.

  Definition justification_type_inhabited : justification_type := [].

  Definition justification_compare : (justification_type -> justification_type -> comparison) := list_compare compare.

  Instance about_justification_type : StrictlyComparable justification_type :=
    { inhabited := justification_type_inhabited;
      compare := list_compare compare;
      compare_strictorder := list_compare_strict_order;
    }.

  Definition message : Type := C * V * justification_type.

  Definition message_type := TripleStrictlyComparable C V justification_type.

  Definition estimate (msg : message) : C :=
    match msg with (c, _, _) => c end.

  Definition sender (msg : message) : V :=
    match msg with (_, v, _) => v end.

  Definition justification (msg : message) : justification_type :=
    match msg with (_, _, j) => j end.

  (* Defining new states for light node version *)
  Definition state := set message.

  Definition state0 : state := [].

  Parameter about_state : StrictlyComparable state.

  Definition state_eq (s1 s2 : state) := incl s1 s2 /\ incl s2 s1.

  Definition state_union (s1 s2 : state) : state := set_union compare_eq_dec s1 s2.

  Lemma state_union_comm : forall s1 s2, state_eq (state_union s1 s2) (state_union s2 s1).
  Proof.
    intros; unfold state_eq; split;
      intros x H_in;
      now apply set_union_comm.
  Qed.

  Definition observed (sigma:state) : list V :=
    set_map compare_eq_dec sender sigma.

  Parameters (hash : message -> H)
             (hash_injective : Inj eq eq hash).

  Definition later (msg : message) (sigma : state) : list message :=
    filter (fun msg' => inb compare_eq_dec (hash msg) (justification msg')) sigma.

  Definition from_sender (v:V) (sigma:state) : list message :=
    filter (fun msg' => compareb (sender msg') v) sigma.

  Definition later_from (msg : message) (v : V) (sigma : state) : list message :=
    filter (fun msg' => (inb compare_eq_dec (hash msg) (justification msg')) && (compareb (sender msg') v)) sigma.

  Definition is_nil_fn {A:Type} (l:list A) : bool :=
  match l with
    | nil => true
    | _ => false
  end.

  Definition latest_messages (sigma : state) : V -> list message :=
    fun v => filter (fun msg => is_nil_fn (later_from msg v sigma)) (from_sender v sigma).

  Definition latest_messages_driven (estimator : state -> C -> Prop) : Prop :=
    exists validator : (V -> list message) -> C -> Prop,
      forall sigma c, estimator sigma c <-> validator (latest_messages sigma) c.

  Definition latest_estimates (sigma : state) : V -> list C :=
    fun v => set_map compare_eq_dec estimate (latest_messages sigma v).

  Definition latest_estimates_driven (estimator : state -> C -> Prop) : Prop :=
    exists validator : (V -> list C) -> C -> Prop,
      forall sigma c, estimator sigma c <-> validator (latest_estimates sigma) c.

  Definition in_fn {A:Type} (eq_dec : forall x y : A, {x = y} + {x <> y}) (a:A) (l:list A) : bool :=
  match in_dec eq_dec a l with
  | left _ => true
  | right _ => false
  end.

  Definition validators_latest_estimates (c : C) (sigma : state) : list V :=
    filter (fun v => in_fn compare_eq_dec c (latest_estimates sigma v)) (observed sigma).

 Definition score (c : C) (sigma : state) : R :=
    fold_right Rplus R0 (map posR_proj1 (map weight (validators_latest_estimates c sigma))).

 Definition reach (s1 s2 : state) := incl s1 s2.

 Lemma reach_refl : forall s, reach s s.
 Proof. apply incl_refl. Qed.

 Lemma reach_trans : forall s1 s2 s3, reach s1 s2 -> reach s2 s3 -> reach s1 s3.
 Proof. apply incl_tran. Qed.

 Lemma reach_union : forall s1 s2, reach s1 (state_union s1 s2).
 Proof. intros s1 s2 x H_in; apply set_union_iff; left; assumption. Qed.

 Lemma reach_morphism : forall s1 s2 s3, reach s1 s2 -> state_eq s2 s3 -> reach s1 s3.
 Proof. intros s1 s2 s3 H_reach H_eq x H_in. spec H_reach x H_in.
        destruct H_eq as [H_eq _]. spec H_eq x H_reach; assumption. Qed.

 Inductive binEstimator : state -> C -> Prop :=
 | estimator_one : forall sigma,
     ((score zero sigma) < (score one sigma))%R ->
     binEstimator sigma one
 | estimator_zero : forall sigma,
     ((score zero sigma) > (score one sigma))%R ->
     binEstimator sigma zero
 | estimator_both_zero : forall sigma,
     ((score zero sigma) = (score one sigma))%R ->
     binEstimator sigma zero
 | estimator_both_one : forall sigma,
     ((score zero sigma) = (score one sigma))%R ->
     binEstimator sigma one.

 Lemma estimator_total : forall s : state, exists c : C, binEstimator s c.
 Proof.
   intros sigma.
   destruct (total_order_T (score zero sigma) (score one sigma)) as [[HLT | HEQ] | HGT].
   - exists one. apply estimator_one. assumption.
   - exists one. apply estimator_both_one. assumption.
   - exists zero. apply estimator_zero. assumption.
 Qed.

 Definition equivocating_messages (msg1 msg2 : message) : bool :=
   match compare_eq_dec msg1 msg2 with
   | left _  => false
   | _ => match msg1, msg2 with (c1,v1,j1), (c2,v2,j2) =>
                               match compare_eq_dec v1 v2 with
                               | left _  => negb (inb compare_eq_dec (hash msg1) j2) && negb (inb compare_eq_dec (hash msg2) j1)
                               | right _ => false
                               end
         end
   end.

 Definition equivocating_message_state (msg : message) : state -> bool :=
   existsb (equivocating_messages msg).

 Lemma equivocating_message_state_incl : forall sigma sigma',
     incl sigma sigma' ->
     forall msg,
       equivocating_message_state msg sigma = true -> equivocating_message_state msg sigma' = true.
 Proof.
   unfold equivocating_message_state.
   intros. rewrite existsb_exists in *.
   destruct H1 as [x [Hin Heq]]. exists x.
   split; try assumption.
   apply H0. assumption.
 Qed.

 Definition equivocating_senders (sigma : state) : set V :=
   set_map compare_eq_dec sender (filter (fun msg => equivocating_message_state msg sigma) sigma).

 Lemma equivocating_senders_nodup : forall sigma,
     NoDup (equivocating_senders sigma).
 Proof.
   intros. apply set_map_nodup.
 Qed.

 Lemma equivocating_senders_incl : forall sigma sigma',
     incl sigma sigma' ->
     incl (equivocating_senders sigma) (equivocating_senders sigma').
 Proof.
   intros.
   apply set_map_incl. apply incl_tran with (filter (fun msg : message => equivocating_message_state msg sigma) sigma').
   - apply filter_incl; assumption.
   - apply filter_incl_fn. intro. apply equivocating_message_state_incl. assumption.
 Qed.

 Definition fault_weight_state (sigma : state) : R :=
   sum_weights (equivocating_senders sigma).

 Lemma sum_weights_in : forall v vs,
     NoDup vs ->
     In v vs ->
     sum_weights vs = (weight v + sum_weights (set_remove compare_eq_dec v vs))%R.
 Proof.
   induction vs; intros; inversion H0; subst; clear H0.
   - inversion H1; subst; clear H.
   - inversion H1; subst; clear H1.
     simpl.
     destruct (compare_eq_dec v v). reflexivity.
     contradiction. simpl.
     destruct (compare_eq_dec v a). subst; reflexivity.
     simpl. spec IHvs H5 H0.
     rewrite IHvs. simpl.
     rewrite <- Rplus_assoc.
     rewrite <- (Rplus_comm (weight v) (weight a)). rewrite Rplus_assoc. reflexivity.
 Qed.

 Lemma sum_weights_incl : forall vs vs',
     NoDup vs ->
     NoDup vs' ->
     incl vs vs' ->
     (sum_weights vs <= sum_weights vs')%R.
 Proof.
   intros vs vs'. generalize dependent vs.
   induction vs'; intros.
   - apply incl_empty in H2. subst. apply Rle_refl.
   - inversion H1; subst; clear H1.
     destruct (in_dec compare_eq_dec a vs).
     + apply sum_weights_in in i. rewrite i. simpl.
       apply Rplus_le_compat_l. apply IHvs'.
       * apply (set_remove_nodup compare_eq_dec a). assumption.
       * assumption.
       * intros x Hrem. apply set_remove_iff in Hrem; try assumption.
         destruct Hrem as [Hin Hxa].
         apply H2 in Hin. destruct Hin; try assumption.
         exfalso; subst. apply Hxa. reflexivity.
       * assumption.
     + simpl. apply Rle_trans with (sum_weights vs').
       * apply IHvs'; try assumption.
         intros x Hin. apply H2 in Hin as Hin'.
         destruct Hin'; try assumption.
         exfalso; subst. apply n. assumption.
       * rewrite <- Rplus_0_l at 1. apply Rplus_le_compat_r. left. destruct (weight a). simpl; auto.
 Qed.

 Lemma fault_weight_state_incl : forall sigma sigma',
     incl sigma sigma' ->
     (fault_weight_state sigma <= fault_weight_state sigma')%R.
 Proof.
   intros. apply sum_weights_incl; try apply equivocating_senders_nodup.
   apply equivocating_senders_incl. assumption.
 Qed.

 Lemma fault_weight_max : forall sigma,
     (fault_weight_state sigma <= sum_weights (set_map compare_eq_dec sender sigma))%R.
 Proof.
   intros.
   apply sum_weights_incl; try apply set_map_nodup.
   unfold equivocating_senders.
   apply set_map_incl.
   intros x Hin.
   apply filter_In in Hin. destruct Hin; assumption.
 Qed.

 Lemma equivocation_weight_compat : forall s1 s2, (fault_weight_state s1 <= fault_weight_state (state_union s2 s1))%R.
 Proof.
   intros s1 s2.
   assert (H_useful := fault_weight_state_incl s1 (state_union s2 s1)).
   spec H_useful.
   intros x H_in. unfold state_union.
   rewrite set_union_iff. right; assumption.
   assumption.
 Qed.

 Definition valid_estimate_condition (c : C) (sigma : state) : Prop :=
   binEstimator sigma c.

 Definition fault_tolerance_condition (sigma : state) : Prop :=
   (fault_weight_state sigma <= proj1_sig t_full)%R.

 (* What if we don't need sorted hashes here either *)
 Definition hash_state (sigma : state) : justification_type := map hash sigma.

 Inductive protocol_state : state -> Prop :=
 | protocol_state_nil : protocol_state state0
 | protocol_state_cons : forall c v j sigma',
     protocol_state j ->
     valid_estimate_condition c j ->
     In (c, v, hash_state j) sigma' ->
     protocol_state (set_remove compare_eq_dec (c, v, hash_state j) sigma') ->
     NoDup sigma' ->
     fault_tolerance_condition sigma' ->
     protocol_state sigma'.

 Lemma fault_tolerance_condition_subset : forall sigma sigma',
     incl sigma sigma' ->
     fault_tolerance_condition sigma' ->
     fault_tolerance_condition sigma.
 Proof.
   unfold fault_tolerance_condition.
   intros.
   apply Rle_trans with (fault_weight_state sigma'); try assumption.
   apply fault_weight_state_incl; assumption.
 Qed.

 Lemma protocol_state_nodup : forall sigma,
     protocol_state sigma ->
     NoDup sigma.
 Proof.
   intros. inversion H0; subst.
   - constructor.
   - assumption.
 Qed.

 Lemma fault_tolerance_condition_set_eq : forall sigma sigma',
     set_eq sigma sigma' ->
     fault_tolerance_condition sigma ->
     fault_tolerance_condition sigma'.
 Proof.
   intros. destruct H0.
   apply (fault_tolerance_condition_subset _ _ H2 H1).
 Qed.

 Lemma set_eq_protocol_state : forall sigma,
     protocol_state sigma ->
     forall sigma',
       set_eq sigma sigma' ->
       NoDup sigma' ->
       protocol_state sigma'.
 Proof.
   intros sigma H'.
   induction H'; intros.
   - destruct H0. unfold state0 in *.
     apply incl_empty in H2; subst. constructor.
   - apply (@set_eq_remove _ compare_eq_dec (c, v, hash_state j)) in H4 as Hset_eq; try assumption.
     apply IHH'2 in Hset_eq.
     apply (protocol_state_cons c v j); try assumption.
     + destruct H4. now apply (H4 (c, v, hash_state j)).
     + apply (fault_tolerance_condition_set_eq _ _ H4 H3).
     + now apply set_remove_nodup.
 Qed.

 Lemma about_prot_state :
   forall (s1 s2 : state),
     protocol_state s1 ->
     protocol_state s2 ->
     (fault_weight_state (state_union s1 s2) <= proj1_sig t_full)%R ->
     protocol_state (state_union s1 s2).
 Proof.
   intros sig1 sig2 Hps1 Hps2.
   induction Hps2; intros.
   - simpl. assumption.
   - clear IHHps2_1.
     assert (protocol_state (state_union sig1 (set_remove compare_eq_dec (c, v, hash_state j) sigma'))).
     { apply IHHps2_2.
       apply fault_tolerance_condition_subset with (state_union sig1 sigma'); try assumption.
       intro msg; intro Hin.
       apply set_union_intro.
       unfold state_union in Hin; apply set_union_elim in Hin.
       destruct Hin; try (left; assumption).
       right. apply (set_remove_1 _ _ _ _ H5).
     }
     clear IHHps2_2.
     apply protocol_state_nodup in Hps1 as Hnodups1.
     assert (HnodupUs1s' := H2).
     apply (set_union_nodup compare_eq_dec Hnodups1) in HnodupUs1s'.
     destruct (in_dec compare_eq_dec (c, v, hash_state j) sig1).
     + apply set_eq_protocol_state with (state_union sig1 (set_remove compare_eq_dec (c, v, hash_state j) sigma'))
       ; try assumption.
       apply set_eq_remove_union_in; assumption.
     + apply (protocol_state_cons c v j); try assumption.
       * apply set_union_iff. right. assumption.
       * apply (set_remove_nodup compare_eq_dec (c, v, hash_state j)) in HnodupUs1s' as Hnoduprem.
         apply set_eq_protocol_state with (state_union sig1 (set_remove compare_eq_dec (c, v, hash_state j) sigma'))
         ; try assumption.
         apply set_eq_remove_union_not_in; assumption.
 Qed.

 Instance LightNode_seteq : CBC_protocol_eq :=
   { (* >> *) consensus_values := C;
     (* >> *) about_consensus_values := about_C;
     validators := V;
     about_validators := about_V;
     weight := weight;
     t := t_full;
     suff_val := suff_val_full;
     state := state;
     about_state := about_state;
     state0 := state0;
     state_eq := state_eq;
     state_union := state_union;
     state_union_comm := state_union_comm;
     reach := reach;
     reach_refl := reach_refl;
     reach_trans := reach_trans;
     reach_union := reach_union;
     reach_morphism := reach_morphism;
     (* >> *) E := binEstimator;
     estimator_total := estimator_total;
     prot_state := protocol_state;
     about_state0 := protocol_state_nil;
     equivocation_weight := fault_weight_state;
     equivocation_weight_compat := equivocation_weight_compat;
     about_prot_state := about_prot_state;
   }.


 Definition bivalent : pstate -> Prop :=
    fun (s : pstate) => not_locked_off zero s /\ not_locked_off one s.

 Definition stuck : pstate -> Prop :=
    fun (s : pstate) => locked_off zero s /\ locked_off one s.

 Lemma locked_on_off : forall s, locked_on one s -> locked_off zero s.
 Proof.
  unfold locked_on. unfold locked_off. unfold not_locked_off.
  unfold not.
  intros s Lon1.
  remember decided_on as D.
  remember (D one) as D1. remember (D zero) as D0. rewrite HeqD in *. clear HeqD; clear  D.
  induction Lon1.
  - intros Loff0; induction Loff0; subst.
    + unfold decided_on in *. unfold decided in *.
      assert (H_s : pstate_rel sigma sigma) by apply pstate_rel_refl.
      apply H0 in H_s as D1.
      apply H1 in H_s as D0.
      unfold decided_on_predicate in *.
      destruct (estimator_total (proj1_sig sigma)) as [c' H_c'].
      apply D0 in H_c' as C0.
      apply D1 in H_c' as C1.
      subst. inversion C0.
    + unfold decided_on in *.
      apply IHLoff0.
      destruct H1 as [_ [Hrel _]].
      apply forward_consistency with sigma; assumption.
  - intros Loff0. destruct Loff0; subst.
    + destruct H0 as [sigma' H_r'].
      spec H2 sigma' H_r'.
      apply H2.
      apply one_path_holds_now.
      unfold decided_on in *.
      destruct H_r' as [_ [H_r' _]].
      apply forward_consistency with sigma; assumption.
    + clear H0.
      apply H2 with sigma'; assumption.
 Qed.

End States.
