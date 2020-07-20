Require Import Reals Bool Relations RelationClasses List ListSet Setoid Permutation EqdepFacts .
Import ListNotations.
From CasperCBC
Require Import Lib.Preamble Lib.ListExtras Lib.ListSetExtras Lib.RealsExtras CBC.Protocol CBC.Common CBC.Definitions.

(* Implementation -instantiates-> Level Specific *)
(** Building blocks for instancing CBC_protocol with full node version **)
Definition sorted_state
  (C V : Type) `{about_M : StrictlyComparable (message C V)}
  : Type
  :=
  { s : @state C V| locally_sorted s }.
Definition sorted_state_proj1
  {C V} `{about_M : StrictlyComparable (message C V)}
  (s : sorted_state C V)
  :=
  proj1_sig s.
Coercion sorted_state_proj1 : sorted_state >-> state.

Definition make_sorted_state
  {C V : Type} `{about_M : StrictlyComparable (message C V)}
  (s : state)
  : sorted_state C V
  :=
  exist _ (sort_state s) (sort_state_locally_sorted s).

Lemma make_already_sorted_state
  {C V : Type} `{about_M : StrictlyComparable (message C V)}
  (s : state)
  (Hs : locally_sorted s)
  : make_sorted_state s = exist _ s Hs.
Proof.
  unfold make_sorted_state. apply exist_eq; simpl.
  apply (sort_state_idempotent s Hs).
Qed.

Definition sorted_message
  (C V : Type) `{about_M : StrictlyComparable (message C V)}
  : Type
  :=
  (C * V * sorted_state C V).

Definition sorted_message_proj1
  {C V : Type} `{about_M : StrictlyComparable (message C V)}
  (sm : sorted_message C V)
  : message C V
  :=
  match sm with
    (c, v, sj) => (c, v, proj1_sig sj)
  end.
Coercion sorted_message_proj1 : sorted_message >-> message.

Definition make_sorted_message
  {C V : Type} `{about_M : StrictlyComparable (message C V)}
  (m : sig locally_sorted_msg)
  : sorted_message C V.
  destruct m as [((c,v), j) Hs].
  apply locally_sorted_message_justification in Hs.
  exact (c, v, exist _ j Hs).
Defined.

Definition get_sorted_messages
  {C V : Type} `{about_M : StrictlyComparable (message C V)}
  (s : sorted_state C V)
  :  list (sorted_message C V)
  := 
  let (sigma, Hsigma) := s in
  let msgs := get_messages sigma in
  map make_sorted_message
    (list_annotate locally_sorted_msg msgs (locally_sorted_all sigma Hsigma)).

Definition add_message_sorted
  {C V : Type} `{about_M : StrictlyComparable (message C V)}
  (sm : sorted_message C V)
  (ss : sorted_state C V)
  :  sorted_state C V.
destruct sm as [(c,v) [j Hj]].
destruct ss as [s Hs].
exists (add_in_sorted_fn (c, v, j) s).
apply add_in_sorted_sorted; try assumption.
constructor; assumption.
Defined.

Lemma state0_neutral
  {C V} `{about_M : StrictlyComparable (message C V)}
  : forall (s : sorted_state C V),
    state_union s Empty = s.
Proof.
  intros s. unfold state_union.
  simpl. unfold messages_union.
  rewrite app_nil_r. apply list_to_state_sorted.
  destruct s. assumption.
Qed.

Definition sorted_state0
  (C V : Type) `{about_M : StrictlyComparable (message C V)}
  : sorted_state C V
  :=
  exist (fun s => locally_sorted s) Empty LSorted_Empty.

Lemma sorted_state_inhabited
  {C V} `{about_M : StrictlyComparable (message C V)}
  : { s : sorted_state C V | True }.
Proof. split; try exact I. exact (sorted_state0 C V). Qed.


Instance state_strictly_comparable
  {C V} `{about_M : StrictlyComparable (message C V)}
  : StrictlyComparable (@state C V)
  :=
  triple_strictly_comparable_proj3 about_M.

Definition sorted_state_compare
  {C V} `{about_M : StrictlyComparable (message C V)}
  : sorted_state C V -> sorted_state C V -> comparison
  := sigify_compare locally_sorted.

Lemma sorted_state_compare_reflexive
  {C V} `{about_M : StrictlyComparable (message C V)}
  : CompareReflexive (@sorted_state_compare _ _ about_M).
Proof.
  red. intros s1 s2.
  destruct s1 as [s1 about_s1];
    destruct s2 as [s2 about_s2].
  simpl. assert (about_s : CompareStrictOrder triple_strictly_comparable_proj3_compare) by apply triple_strictly_comparable_proj3_strictorder.
  destruct about_s. spec StrictOrder_Reflexive s1 s2. rewrite StrictOrder_Reflexive.
  split; intros; subst.
  - apply exist_eq. reflexivity.
  - inversion H. reflexivity.
Qed.

Lemma sorted_state_compare_transitive
  {C V} `{about_M : StrictlyComparable (message C V)}
  : CompareTransitive (@sorted_state_compare _ _ about_M).
Proof.
  red; intros s1 s2 s3 c H12 H23;
    destruct s1 as [s1 about_s1];
    destruct s2 as [s2 about_s2];
    destruct s3 as [s3 about_s3].
  simpl in *.
  now apply (@StrictOrder_Transitive _ _ triple_strictly_comparable_proj3_strictorder s1 s2 s3 c).
Qed.

Instance sorted_state_strictorder
  {C V} `{about_M : StrictlyComparable (message C V)}
  : CompareStrictOrder (@sorted_state_compare C V about_M)
  :=
  { StrictOrder_Reflexive := sorted_state_compare_reflexive;
    StrictOrder_Transitive := sorted_state_compare_transitive; }.

Instance sorted_state_type
  {C V} `{about_M : StrictlyComparable (message C V)}
  : StrictlyComparable (sorted_state C V)
  :=
  { inhabited := sorted_state_inhabited;
    compare := sigify_compare locally_sorted;
    compare_strictorder := sorted_state_strictorder;
  }.

Lemma sorted_state_union_comm
  {C V} `{about_M : StrictlyComparable (message C V)}
  : forall (s1 s2 : sorted_state C V),
    state_union s1 s2 = state_union s2 s1.
Proof.
  intros s1 s2;
  destruct s1 as [s1 about_s1];
  destruct s2 as [s2 about_s2];
  simpl.
  assert (H_useful := list_to_state_sorted s1 about_s1).
  assert (H_useful' := locally_sorted_all s1 about_s1).
  unfold state_union.
  assert (H_duh : Permutation (messages_union (get_messages s1) (get_messages s2))
                              (messages_union (get_messages s2) (get_messages s1))).
  unfold messages_union. rewrite Permutation_app_comm.
  reflexivity. now apply state_union_comm_helper_helper.
Qed.

Program Definition sorted_state_union
  {C V} `{about_M : StrictlyComparable (message C V)}
  (sigma1 sigma2 : sorted_state C V) : sorted_state C V
  :=
  exist _ (list_to_state (messages_union (get_messages sigma1) (get_messages sigma2))) _.
Next Obligation.
  apply state_union_sorted.
  destruct sigma1; assumption.
  destruct sigma2; assumption.
Defined.

Lemma sorted_state_sorted_union_comm
  {C V} `{about_M : StrictlyComparable (message C V)}
  : forall (s1 s2 : sorted_state C V),
    sorted_state_union s1 s2 = sorted_state_union s2 s1.
Proof.
  intros s1 s2.
  assert (H_useful := sorted_state_union_comm s1 s2).
  unfold sorted_state_union.
  now apply exist_eq.
Qed.

(* Defining the reachability relation *)
Definition reachable
  {C V} `{about_M : StrictlyComparable (message C V)}
  (s1 s2 : sorted_state C V) :=
  syntactic_state_inclusion (sorted_state_proj1 s1) (sorted_state_proj1 s2).

Lemma reachable_refl
  {C V} `{about_M : StrictlyComparable (message C V)}
  : forall s : sorted_state C V, reachable s s.
Proof. intros; easy. Qed.

Lemma reachable_trans
  {C V} `{about_M : StrictlyComparable (message C V)}
  : forall sigma1 sigma2 sigma3 : sorted_state C V,
  reachable sigma1 sigma2 ->
  reachable sigma2 sigma3 ->
  reachable sigma1 sigma3.
Proof.
  intros.
  repeat (split; try assumption). apply incl_tran with (get_messages sigma2); assumption.
Qed.

Lemma reach_union
  {C V} `{about_M : StrictlyComparable (message C V)}
  : forall (s1 s2 : sorted_state C V), reachable s1 (sorted_state_union s1 s2).
Proof.
  intros s1 s2. unfold state_union.
  intros x H_in.
  assert (H_incl := list_to_state_iff (messages_union (get_messages s1) (get_messages s2))).
  destruct H_incl as [_ useful].
  spec useful x. spec useful.
  apply in_app_iff. tauto.
  assumption.
Qed.

Lemma reachable_morphism
  {C V} `{about_M : StrictlyComparable (message C V)}
  : forall s1 s2 s3 : sorted_state C V,
  reachable s1 s2 ->
  s2 = s3 ->
  reachable s1 s3.
Proof. intros; subst; assumption. Qed.

(** Proof obligations from CBC_protocol **)
Lemma equivocation_weight_compat
  {C V} `{about_M : StrictlyComparable (message C V)} `{Hm : Measurable V}
  : forall (s1 s2 : sorted_state C V), (fault_weight_state s1 <= fault_weight_state (state_union s2 s1))%R.
Proof.
  intros s1 s2.
  assert (H_useful := fault_weight_state_incl s1 (state_union s1 s2)).
  spec H_useful.
  red. unfold state_union.
  assert (H_useful' := list_to_state_iff (messages_union (get_messages s1) (get_messages s2))).
  destruct H_useful' as [_ useful]. intros x H_in.
  spec useful x. spec useful. unfold messages_union.
  rewrite in_app_iff. tauto.
  assumption.
  replace (state_union s2 s1) with (state_union s1 s2) by apply sorted_state_union_comm.
  assumption.
Qed.

Lemma about_sorted_state0
  {C V} `{PS : ProtocolState C V}
  : protocol_state (sorted_state0 C V).
Proof.
  unfold sorted_state0.
  simpl. apply protocol_state_empty.
Qed.

Lemma union_protocol_states'
  {C V} `{PS : ProtocolState C V}
  : forall s1 s2 : sorted_state C V,
  protocol_state s1 ->
  protocol_state s2 ->
  (fault_weight_state (sorted_state_union s1 s2) <= proj1_sig threshold)%R ->
  protocol_state (sorted_state_union s1 s2).
Proof.
  intros [s1 about_s1] [s2 about_s2] H_prot1 H_prot2 H_weight.
  now apply union_protocol_states.
Qed.

Lemma reach_morphism
  {C V} `{about_M : StrictlyComparable (message C V)}
  : forall (s1 s2 s3 : sorted_state C V),
    reachable s1 s2 -> s2 = s3 -> reachable s1 s3.
Proof.
  intros s1 s2 s3 H_12 H_eq.
  subst. easy.
Qed.

Definition sorted_estimator
  {C V} `{about_M : StrictlyComparable (message C V)} `{He : Estimator (@state C V) C}
  (s : sorted_state C V) (c : C) : Prop
  :=
  estimator (proj1_sig s) c.

Lemma sorted_estimator_total
  {C V} `{about_M : StrictlyComparable (message C V)} `{He : Estimator (@state C V) C}
  : forall s : sorted_state C V, exists c : C, sorted_estimator s c.
Proof.
  intros. destruct He. destruct s. destruct (estimator_total x).
  exists x0. simpl. assumption.
Qed.

Instance sorted_estimator_instance
  {C V} `{about_M : StrictlyComparable (message C V)} `{He : Estimator (@state C V) C}
  : Estimator (sorted_state C V) C
  :=
  { estimator := sorted_estimator
  ; estimator_total := sorted_estimator_total
  }.

Instance FullNode_syntactic
  {C V} `{PS : ProtocolState C V} : CBC_protocol_eq :=
  { consensus_values := C;
    about_consensus_values := triple_strictly_comparable_proj1 about_M;
    validators := V;
    about_validators :=  triple_strictly_comparable_proj2 about_M;
    weight := weight;
    t := threshold;
    suff_val := reachable_threshold;
    state := sorted_state C V;
    about_state := sorted_state_type;
    state0 := sorted_state0 C V;
    state_eq := eq;
    state_union_comm := sorted_state_sorted_union_comm;
    reach := reachable;
    reach_refl := reachable_refl;
    reach_trans := reachable_trans;
    reach_union := reach_union;
    reach_morphism := reach_morphism;
    E := sorted_estimator;
    estimator_total := sorted_estimator_total;
    prot_state := protocol_state;
    about_state0 := about_sorted_state0;
    equivocation_weight := fault_weight_state;
    equivocation_weight_compat := equivocation_weight_compat;
    about_prot_state := union_protocol_states';
    }.

Definition pstate
  (C V : Type) `{PS : ProtocolState C V}
  : Type
  :=
  {s : @state C V | protocol_state s}.
Definition pstate_proj1
  {C V : Type} `{PS : ProtocolState C V}
  (p : pstate C V) : state
  :=
  proj1_sig p.
Coercion pstate_proj1 : pstate >-> state.

Definition pstate_rel
  {C V : Type} `{PS : ProtocolState C V}
  : pstate C V -> pstate C V -> Prop :=
  fun p1 p2 => syntactic_state_inclusion (pstate_proj1 p1) (pstate_proj1 p2).

Definition non_trivial_pstate
  {C V : Type} `{PS : ProtocolState C V}
  (P : pstate C V -> Prop)
  :=
  (exists (s1 : pstate C V), forall (s : pstate C V), pstate_rel s1 s -> P s)
  /\
  (exists (s2 : pstate C V), forall (s : pstate C V), pstate_rel s2 s -> (P s -> False)).

Definition exists_pivotal_validator_ps
  {C V}
  `{PS : ProtocolState C V}
  :=
  @exists_pivotal_validator V (triple_strictly_comparable_proj2 about_M) Hm Hrt.

Theorem non_triviality_decisions_on_properties_of_protocol_states
  {C V : Type} `{PS : ProtocolState C V}
  `{Hit : InhabitedTwice V}
  : exists (p : pstate C V -> Prop) , non_trivial_pstate p.
Proof.
  assert (HscV : StrictlyComparable V) by apply (triple_strictly_comparable_proj2 about_M).
  destruct (estimator_total Empty) as [c Hc].
  destruct exists_pivotal_validator_ps as [v [vs [Hnodup [Hnin [Hlt Hgt]]]]].
  destruct vs as [ | v' vs].
  - exists (in_state (c,v,Empty)).
    split.
    + assert (bleh : protocol_state (next (c,v,Empty) Empty)) by now apply protocol_state_singleton.
      exists (exist protocol_state (next (c,v,Empty) Empty) bleh).
      intros sigma H. apply H. simpl. left. reflexivity.
    + destruct (distinct_choice_total v) as [v' Hv'].
      remember (add_in_sorted_fn (c, v', Empty) Empty) as sigma0.
      assert (Hps0 : protocol_state sigma0) by (subst; now apply protocol_state_singleton).
      destruct (estimator_total sigma0) as [c0 Hc0].
      assert (bleh : protocol_state (add_in_sorted_fn (c0, v, sigma0) sigma0)) by (apply copy_protocol_state; assumption).
      exists (exist protocol_state (add_in_sorted_fn (c0, v, sigma0) sigma0) bleh).
      intros sigma' H'.
      intro.
      apply protocol_state_not_heavy in bleh as Hft'.
      assert (Hnft' : (fault_weight_state sigma' > proj1_sig threshold)%R).
      { apply Rlt_le_trans with (fault_weight_state (add (c, v, Empty) to (add (c0, v, sigma0) to Empty))).
        - unfold fault_weight_state. unfold equivocating_senders. simpl.
          assert ( Hequiv : equivocating_in_state (c, v, Empty)
                    (add (c, v, Empty)to (add (c0, v, sigma0)to Empty)) = true).
          { apply existsb_exists. exists (c0, v, sigma0).
            split.
            - right. left. reflexivity.
            - unfold equivocating_messages. rewrite eq_dec_if_false.
              + rewrite eq_dec_if_true; try reflexivity.
                apply andb_true_iff. split.
                * subst. simpl. apply negb_true_iff. unfold in_state_fn.
                  rewrite in_state_dec_if_false; try reflexivity.
                  intro. rewrite add_is_next in H0. apply in_singleton_state in H0.
                  apply Hv'. inversion H0. reflexivity.
                * apply negb_true_iff. unfold in_state_fn.
                  rewrite in_state_dec_if_false; try reflexivity.
                  apply in_empty_state.
              + intro. subst. inversion H0; subst; clear H0.
          }
          rewrite Hequiv.
          assert ( Hequiv0 : equivocating_in_state (c0, v, sigma0)
                    (add (c, v, Empty)to (add (c0, v, sigma0)to Empty)) = true).
          { apply existsb_exists. exists (c, v, Empty).
            split.
            - left. reflexivity.
            - unfold equivocating_messages. rewrite eq_dec_if_false.
              + rewrite eq_dec_if_true; try reflexivity.
                apply andb_true_iff. split.
                * apply negb_true_iff. unfold in_state_fn.
                  rewrite in_state_dec_if_false; try reflexivity.
                  apply in_empty_state.
                * subst. simpl. apply negb_true_iff. unfold in_state_fn.
                  rewrite in_state_dec_if_false; try reflexivity.
                  intro. rewrite add_is_next in H0. apply in_singleton_state in H0.
                  apply Hv'. inversion H0. reflexivity.
              + intro. subst. inversion H0; subst; clear H0.
          }
          rewrite Hequiv0. simpl. rewrite eq_dec_if_true; try reflexivity.
          simpl. simpl in Hgt. unfold Rminus in Hgt.
          apply (Rplus_gt_compat_r (proj1_sig (CBC.Common.weight v))) in Hgt. rewrite Rplus_assoc in Hgt.
          rewrite Rplus_0_r. rewrite Rplus_0_l in Hgt. rewrite Rplus_opp_l in Hgt. rewrite Rplus_0_r in Hgt.
          apply Rgt_lt. assumption.
        - apply fault_weight_state_incl. unfold syntactic_state_inclusion. simpl.
          intros x Hin. destruct Hin as [Hin | [Hin | Hcontra]]; try inversion Hcontra; subst
          ; try assumption.
          unfold pstate_rel in H'. apply H'. apply in_state_add_in_sorted_iff. left. reflexivity.
      }
      unfold Rgt in Hnft'.
      apply (Rlt_irrefl (proj1_sig threshold)).
      apply Rlt_le_trans with (fault_weight_state sigma'). assumption. destruct sigma' as [sigma' about_sigma'].
      inversion about_sigma'. subst. assumption.
      simpl in *. subst. assumption.
  - remember (add_in_sorted_fn (c, v', Empty) Empty) as sigma0.
    assert (Hps0 : protocol_state sigma0) by (subst; now apply protocol_state_singleton).
    destruct (estimator_total sigma0) as [c0 Hc0].
    exists (in_state (c0,v,sigma0)).
    split.
    + assert (bleh : protocol_state (add_in_sorted_fn (c0, v, sigma0) sigma0)) by (apply copy_protocol_state; assumption).
      exists (exist protocol_state (add_in_sorted_fn (c0, v, sigma0) sigma0) bleh).
      intros sigma' H'.
      red in H'; apply H'. apply in_state_add_in_sorted_iff. left. reflexivity.
    + remember (add_in_sorted_fn (c, v, Empty) Empty) as sigma.
      simpl in Heqsigma. rewrite add_is_next in Heqsigma.
      destruct (estimator_total sigma) as [csigma Hcsigma].
      remember (valid_protocol_state sigma csigma c (v' :: vs)) as sigma2.
      assert (Hequiv2 : set_eq (equivocating_senders sigma2) (v' :: vs)).
      { rewrite Heqsigma2. rewrite Heqsigma in *.
        apply valid_protocol_state_equivocating_senders; assumption.
      }
      assert (bleh : protocol_state sigma2) by (subst; now apply valid_protocol_state_ps).
      exists (exist protocol_state sigma2 bleh).
      intros sigma' Hfutures.
      unfold predicate_not. intro Hin.
      red in Hfutures.
      destruct sigma' as [sigma' about_sigma'].
      assert (Hps' := about_sigma').
      apply protocol_state_not_heavy in Hps'.
      { apply (not_heavy_subset (add (c0, v, sigma0) to sigma2)) in Hps'.
        - apply Rlt_irrefl with (proj1_sig threshold).
          apply Rlt_le_trans with (fault_weight_state (add (c0, v, sigma0)to sigma2)); try assumption.
          unfold fault_weight_state.
          unfold Rminus in Hgt. apply (Rplus_gt_compat_r (proj1_sig (weight v))) in Hgt.
          rewrite Rplus_assoc in Hgt. rewrite Rplus_opp_l, Rplus_0_r in Hgt.
          apply Rgt_lt. apply Rge_gt_trans with (sum_weights (v' :: vs) + (proj1_sig (weight v)))%R; try assumption.
          rewrite Rplus_comm.
          assert (Hsum : (proj1_sig (weight v) + sum_weights (v' :: vs))%R = sum_weights (v :: v' :: vs))
          ; try reflexivity; try rewrite Hsum.
          apply Rle_ge. apply sum_weights_incl; try apply set_map_nodup; try (constructor; assumption).
          intros vv Hvin. unfold equivocating_senders.
          apply set_map_exists.
          exists (c, vv, Empty).
          split; try reflexivity.
          apply filter_In.
          split; destruct Hvin as [Heq | Hvin]; subst; apply existsb_exists || right.
          + apply in_valid_protocol_state_rev_sigma. simpl. left. reflexivity.
          + apply in_valid_protocol_state_rev_cempty; assumption.
          + exists (c0, vv, add_in_sorted_fn (c, v', Empty) Empty).
            split ; try (left; reflexivity).
            simpl. unfold equivocating_messages.
            rewrite eq_dec_if_false; try rewrite eq_dec_if_true; try reflexivity
            ; try (apply andb_true_iff; split; apply negb_true_iff
                   ; unfold in_state_fn; rewrite in_state_dec_if_false; try reflexivity; intro).
            * rewrite add_is_next in H. apply in_singleton_state in H.
              inversion H; subst; clear H. apply Hnin. left. reflexivity.
            * inversion H.
            * intro. inversion H.
          + exists (csigma, vv, (next (c, v, Empty) Empty)). split
                                                        ; try (right; apply in_valid_protocol_state_rev_csigma; assumption).
            unfold equivocating_messages.
            rewrite eq_dec_if_false; try rewrite eq_dec_if_true; try reflexivity
            ; try (apply andb_true_iff; split; apply negb_true_iff
            ; unfold in_state_fn; rewrite in_state_dec_if_false; try reflexivity; intro).
            * apply in_singleton_state in H.
              inversion H; subst; clear H. apply Hnin. assumption.
            * inversion H.
            * intro. inversion H.
        - intros msg Hmin.
          destruct Hmin as [Heq | Hmin].
          * subst. assumption.
          * now apply Hfutures.
      }
Qed.

Theorem no_local_confluence_prot_state
  {C V : Type} `{PS : ProtocolState C V}
  `{Hit : InhabitedTwice V}
  : exists (a a1 a2 : pstate C V),
        pstate_rel a a1 /\ pstate_rel a a2 /\
        ~ exists (a' : pstate C V), pstate_rel a1 a' /\ pstate_rel a2 a'.
Proof.
  assert (H_useful := non_triviality_decisions_on_properties_of_protocol_states).
  destruct H_useful as [P [[ps1 about_ps1] [ps2 about_ps2]]].
  exists (exist protocol_state Empty protocol_state_empty).
  exists ps1, ps2. repeat split; try (red; simpl; easy).
  intro Habsurd. destruct Habsurd as [s [Hs1 Hs2]].
  spec about_ps1 s Hs1.
  spec about_ps2 s Hs2. contradiction.
Qed.

Lemma pstate_inhabited
  {C V : Type} `{PS : ProtocolState C V}
  : exists (p1 : pstate C V), True.
Proof. now exists (exist protocol_state Empty protocol_state_empty). Qed.

Definition pstate_compare
  {C V : Type} `{PS : ProtocolState C V}
  (ps1 ps2 : pstate C V) : comparison
  :=
  compare (proj1_sig ps1) (proj1_sig ps2).


Lemma pstate_eq_dec
  {C V : Type} `{PS : ProtocolState C V}
  : forall (p1 p2 : pstate C V), {p1 = p2} + {p1 <> p2}.
Proof.
  intros p1 p2.
  now apply sigify_eq_dec.
Qed.

Lemma pstate_rel_refl
  {C V : Type} `{PS : ProtocolState C V}
  : Reflexive (@pstate_rel C V _ _ _ _ _).
Proof.
  red. intro p.
  destruct p as [p about_p].
  red. simpl. easy. Qed.

Lemma pstate_rel_trans
  {C V : Type} `{PS : ProtocolState C V}
  : Transitive (@pstate_rel C V _ _ _ _ _).
Proof.
  red; intros p1 p2 p3 H_12 H_23.
  destruct p1 as [p1 about_p1];
    destruct p2 as [p2 about_p2];
    destruct p3 as [p3 about_p3];
    simpl in *.
  unfold pstate_rel in *; simpl in *.
  now eapply incl_tran with (get_messages p2).
Qed.

Instance level0
  {C V : Type} `{PS : ProtocolState C V}
  : PartialOrder (pstate C V) :=
  { A_eq_dec := pstate_eq_dec;
    A_inhabited := pstate_inhabited;
    A_rel := pstate_rel;
    A_rel_refl := pstate_rel_refl;
    A_rel_trans := pstate_rel_trans;
  }.

(* Instance level0 : PartialOrder := @level0 FullNode_syntactic. *)

Instance level1
  {C V : Type} `{PS : ProtocolState C V}
  `{Hit : InhabitedTwice V}
  : PartialOrderNonLCish (pstate C V)
  :=
  { no_local_confluence_ish := (@no_local_confluence_prot_state C V _ _ _ _ _ _)}.

(** Strong non-triviality **)
(* Defining reachablity in terms of message sending *)
Definition in_future {C V} (s1 s2 : @state C V) :=
  syntactic_state_inclusion s1 s2.

Definition next_future
  {C V} `{about_M : StrictlyComparable (message C V)}
  (s1 s2 : @state C V)
  :=
   exists (msg : message C V), add_in_sorted_fn msg s1 = s2.

Definition in_past
  {C V}
  (s1 s2 : @state C V)
  :=
  syntactic_state_inclusion s2 s1.

Definition in_past_trace
  {C V}
  (s1 s2 : @state C V)
  :=
  exists (msg : message C V), in_state msg s1 /\ justification msg = s2.

Definition no_common_future
  {C V : Type} `{PS : ProtocolState C V}
  (s1 s2 : pstate C V)
  :=
  forall (s : pstate C V), in_future s1 s /\ in_future s2 s -> False.

Definition yes_common_future
  {C V : Type} `{PS : ProtocolState C V}
  (s1 s2 : pstate C V)
  :=
  exists (s : pstate C V), in_future s1 s /\ in_future s2 s.

Definition strong_nontriviality
  {C V : Type} `{PS : ProtocolState C V}
  :=
  (* For every state, there exists a state *)
  forall (s1 : pstate C V),
  exists (s2 : pstate C V),
    (* That is reachable in one step *)
    next_future s1 s2 /\
    (* And there exists a third state *)
    exists (s3 : pstate C V),
      (* Such that s1 and s3 share a common future *)
      yes_common_future s1 s3
      /\
      (* But s2 and s3 don't. *)
      no_common_future s2 s3.

(* Here's how to construct an equivocation *)
Lemma about_equivocating_messages
  {C V} `{about_M : StrictlyComparable (message C V)} `{He : Estimator (@state C V) C}
  : forall (j : @state C V) v v',
      v <> v' ->
      equivocating_messages_prop (get_estimate j, v, j)
                                 (get_estimate (add_in_sorted_fn (get_estimate j, v', j) j), v, add_in_sorted_fn (get_estimate j, v', j) j).
Proof.
  intros j v v' H_neq.
  rewrite <- equivocating_messages_correct.
  unfold equivocating_messages.
  rewrite eq_dec_if_false.
  + rewrite eq_dec_if_true; try reflexivity.
    rewrite andb_true_iff.
    split; rewrite negb_true_iff
    ; unfold in_state_fn; rewrite in_state_dec_if_false; try reflexivity
    ; intro.
    * subst. apply in_state_add_in_sorted_iff in H.
      { destruct H.
        - inversion H. subst. apply H_neq. reflexivity.
        - apply (not_extx_in_x (get_estimate j) v j j); try assumption.
          apply incl_refl.
      }
    * apply (not_extx_in_x (get_estimate (add_in_sorted_fn (get_estimate j, v', j) j)) v (add_in_sorted_fn (get_estimate j, v', j) j) j); try assumption.
      subst.
      intros msg Hin. apply in_state_add_in_sorted_iff. right. assumption.
  + intro. inversion H; subst; clear H.
    apply (not_extx_in_x (get_estimate j) v' j j); try apply incl_refl.
    rewrite H2 at 3.
    apply in_state_add_in_sorted_iff. left. reflexivity.
Qed.

(* Defining the state that adds this minimal equivocation *)
Definition next_equivocation_state
  {C V} `{about_M : StrictlyComparable (message C V)} `{He : Estimator (@state C V) C}
  (j : @state C V) (v v' : V) : state :=
  add_in_sorted_fn
    (* One equivocation partner *)
    (get_estimate j, v, j)
    (* First state *)
    (add_in_sorted_fn
       (* Other equivocation partner *)
       (get_estimate (add_in_sorted_fn (get_estimate j, v', j) j), v, (add_in_sorted_fn (get_estimate j, v', j) j))
       (* Zero-th state *)
       (add_in_sorted_fn (get_estimate j, v', j) j)).

(* Explicit instances of various incl results *)
Lemma next_equivocation_state_incl
  {C V} `{about_M : StrictlyComparable (message C V)} `{He : Estimator (@state C V) C}
  : forall (j : @state C V) (v v' : V),
    syntactic_state_inclusion j (next_equivocation_state j v v').
Proof.
  intros j v v' msg H_in.
  unfold next_equivocation_state.
  do 3 (apply in_state_add_in_sorted_iff; right).
  assumption.
Qed.

Lemma next_equivocation_state_keeps_messages
  {C V} `{about_M : StrictlyComparable (message C V)} `{He : Estimator (@state C V) C}
  : forall (j : state) (v v' : V) (msg : message C V),
    in_state msg j ->
    in_state msg (next_equivocation_state j v v').
Proof.
  apply next_equivocation_state_incl.
Qed.

Lemma next_equivocation_state_keeps_equivocators
  {C V} `{about_M : StrictlyComparable (message C V)} `{He : Estimator (@state C V) C}
  : forall (j : @state C V) (v v' v0 : V),
    In v (equivocating_senders j) ->
    In v (equivocating_senders (next_equivocation_state j v v')).
Proof.
  intros.
  assert (H_incl := equivocating_senders_incl).
  spec H_incl j (next_equivocation_state j v v') (next_equivocation_state_incl j v v').
  now apply H_incl.
Qed.

Lemma next_equivocation_state_keeps_equivocating_messages
  {C V} `{about_M : StrictlyComparable (message C V)} `{He : Estimator (@state C V) C}
  : forall (j : state) (v v' : V) (msg : message C V),
    equivocating_in_state_prop msg j ->
    equivocating_in_state_prop msg (next_equivocation_state j v v').
Proof.
  intros.
  assert (H_incl := @equivocating_in_state_incl C V).
  spec H_incl j (next_equivocation_state j v v') (next_equivocation_state_incl j v v').
  now apply H_incl.
Qed.

Lemma about_equivocating_messages_in_state_l
  {C V} `{about_M : StrictlyComparable (message C V)} `{He : Estimator (@state C V) C}
  : forall (j : @state C V) v v',
      v <> v' ->
      equivocating_in_state_prop (get_estimate j, v, j)
                                 (next_equivocation_state j v v').
Proof.
  intros j v v' H_neq.
  exists (get_estimate (add_in_sorted_fn (get_estimate j, v', j) j), v, add_in_sorted_fn (get_estimate j, v', j) j).
  split.
  apply in_state_add_in_sorted_iff.
  right.
  apply in_state_add_in_sorted_iff.
  left. reflexivity.
  now apply about_equivocating_messages.
Qed.

Lemma about_equivocating_messages_in_state_r
  {C V} `{about_M : StrictlyComparable (message C V)} `{He : Estimator (@state C V) C}
  : forall j v v',
      v <> v' ->
      equivocating_in_state_prop (get_estimate (add_in_sorted_fn (get_estimate j, v', j) j), v, add_in_sorted_fn (get_estimate j, v', j) j)
                                 (next_equivocation_state j v v').
Proof.
  intros j v v' H_neq.
  exists (get_estimate j, v, j).
  split.
  apply in_state_add_in_sorted_iff.
  left. reflexivity.
  apply equivocating_messages_prop_swap.
  now apply about_equivocating_messages.
Qed.

Lemma about_equivocating_messages_add_equivocator
  {C V} `{about_M : StrictlyComparable (message C V)} `{He : Estimator (@state C V) C}
  : forall (j : @state C V) v v',
      v <> v' ->
      In v (equivocating_senders (next_equivocation_state j v v')).
Proof.
  intros j v v' H_neq.
  apply equivocating_senders_correct.
  exists (get_estimate j, v, j).
  split.
  unfold next_equivocation_state; rewrite in_state_add_in_sorted_iff.
  left; tauto.
  split. reflexivity.
  now apply about_equivocating_messages_in_state_l.
Qed.

Lemma equivocating_senders_sorted_extend
  {C V} `{about_M : StrictlyComparable (message C V)} `{He : Estimator (@state C V) C}
  : forall (s : @state C V) v,
    set_eq (equivocating_senders s)
           (equivocating_senders (add_in_sorted_fn (get_estimate s, v, s) s)).
Proof.
  intros.
  assert (H_useful := equivocating_senders_extend s (get_estimate s) v).
  rewrite <- H_useful.
  rewrite add_is_next.
  assert (H_rewrite := add_next_equivocating_senders_eq).
  spec H_rewrite (get_estimate s) v s s.
  rewrite set_eq_comm.
  eapply set_eq_tran.
  exact H_rewrite.
  apply set_eq_refl.
Qed.

Lemma add_weight_one
  {C V} `{PS : ProtocolState C V}
  : forall (j : @state C V) (v' : V),
    fault_weight_state j =
    fault_weight_state (add_in_sorted_fn (get_estimate j, v', j) j).
Proof.
  intros.
  apply equivocating_senders_fault_weight_eq.
  apply equivocating_senders_sorted_extend.
Qed.

Lemma add_weight_two
  {C V} `{PS : ProtocolState C V}
  : forall (j : @state C V) (v v' : V),
    (fault_weight_state
      (add_in_sorted_fn
         (get_estimate (add_in_sorted_fn (get_estimate j, v', j) j), v, (add_in_sorted_fn (get_estimate j, v', j) j))
         (add_in_sorted_fn (get_estimate j, v', j) j)) =
    fault_weight_state
      (add_in_sorted_fn (get_estimate j, v', j) j))%R.
Proof.
  intros.
  apply equivocating_senders_fault_weight_eq.
  apply set_eq_comm.
  apply equivocating_senders_sorted_extend.
Qed.

Lemma add_weight_three
  {C V} `{PS : ProtocolState C V}
  : forall (j : @state C V) (v v' : V),
    protocol_state j ->
    ~ In v (equivocating_senders j) ->
    v <> v' ->
    fault_weight_state (next_equivocation_state j v v') =
    (fault_weight_state
      (add_in_sorted_fn
         (get_estimate (add_in_sorted_fn (get_estimate j, v', j) j), v, (add_in_sorted_fn (get_estimate j, v', j) j))
         (add_in_sorted_fn (get_estimate j, v', j) j)) +
     proj1_sig (weight v))%R.
Proof.
  intros j v v' about_j H_notin H_neq.
  assert (H_useful := add_equivocating_sender).
  spec H_useful (add_in_sorted_fn
                   (get_estimate (add_in_sorted_fn (get_estimate j, v', j) j), v,
                    add_in_sorted_fn (get_estimate j, v', j) j)
                   (add_in_sorted_fn (get_estimate j, v', j) j)).
  spec H_useful.
  { constructor; try assumption; try apply get_estimate_correct.
    apply copy_protocol_state; try assumption; try apply get_estimate_correct.
    apply copy_protocol_state; try assumption; try apply get_estimate_correct.
    apply incl_refl.
    red.
    rewrite <- (add_weight_one (add_in_sorted_fn (get_estimate j, v', j) j) v).
    apply protocol_state_not_heavy; try assumption .
    apply protocol_state_next; try assumption.
    apply incl_refl. apply get_estimate_correct.
    red.
    rewrite <- (add_weight_one _ v').
    apply protocol_state_not_heavy in about_j.
    assumption. }
  spec H_useful (get_estimate j, v, j).
  spec H_useful.
  exists (get_estimate (add_in_sorted_fn (get_estimate j, v', j) j), v, add_in_sorted_fn (get_estimate j, v', j) j).
  split.
  rewrite in_state_add_in_sorted_iff.
  tauto. apply about_equivocating_messages; try assumption.
  assert (HscV  := @triple_strictly_comparable_proj2 _ _ _ about_M).
  (* Now. *)
  assert (H_inter := senders_fault_weight_eq (equivocating_senders
                  (add_in_sorted_fn (get_estimate j, v, j)
                     (add_in_sorted_fn
                        (get_estimate
                           (add_in_sorted_fn (get_estimate j, v', j) j), v,
                        add_in_sorted_fn (get_estimate j, v', j) j)
                        (add_in_sorted_fn (get_estimate j, v', j) j)))) (set_add (compare_eq_dec_v about_M) (sender (get_estimate j, v, j))
                  (equivocating_senders
                     (add_in_sorted_fn
                        (get_estimate
                           (add_in_sorted_fn (get_estimate j, v', j) j), v,
                        add_in_sorted_fn (get_estimate j, v', j) j)
                        (add_in_sorted_fn (get_estimate j, v', j) j))))).
  spec H_inter.
  apply set_map_nodup.
  spec H_inter.
  apply set_add_nodup.
  apply set_map_nodup.
  spec H_inter H_useful.
  clear H_useful.
  unfold fault_weight_state.
  unfold next_equivocation_state.
  rewrite H_inter.
  simpl. clear H_inter.
  assert (H_rewrite := sum_weights_in v (set_add (compare_eq_dec_v about_M) v
       (equivocating_senders
          (add_in_sorted_fn
             (get_estimate (add_in_sorted_fn (get_estimate j, v', j) j), v,
             add_in_sorted_fn (get_estimate j, v', j) j)
             (add_in_sorted_fn (get_estimate j, v', j) j))))).
  spec H_rewrite.
  apply set_add_nodup. apply set_map_nodup.
  spec H_rewrite.
  rewrite set_add_iff. tauto.
  rewrite H_rewrite. clear H_rewrite.
  rewrite Rplus_comm.
  apply Rplus_eq_compat_r.
  apply set_eq_nodup_sum_weight_eq
  ; try apply set_remove_nodup
  ; try apply set_add_nodup
  ; try apply set_map_nodup.
  split; intro x; intros.
  - apply set_remove_iff in H; try (apply set_add_nodup; apply set_map_nodup).
    destruct H as [Hin Hneq]; subst; try contradiction.
    apply set_add_iff in Hin. destruct Hin as [Heq | Hin]; try contradiction.
    assumption.
  - apply set_remove_iff; try (apply set_add_nodup; apply set_map_nodup).
    rewrite set_add_iff.
    split; try (right; assumption).
    intros H_absurd; subst.
    apply H_notin.
    apply equivocating_senders_sorted_extend in H. apply equivocating_senders_sorted_extend in H.
    assumption.
Qed.

Definition add_weight_under
  {C V} `{about_M : StrictlyComparable (message C V)} `{Hm : Measurable V} `{Hrt : ReachableThreshold V}
  (s : @state C V) (v : V)
  :=
  (fault_weight_state s + proj1_sig (weight v) <= proj1_sig threshold)%R.

Lemma equivocation_adds_fault_weight
  {C V} `{PS : ProtocolState C V}
  : forall (j : @state C V),
    protocol_state j ->
    forall (v v' : V),
      ~ In v (equivocating_senders j) ->
      v <> v' ->
      fault_weight_state (next_equivocation_state j v v') =
      (fault_weight_state j + proj1_sig (weight v))%R.
Proof.
  intros j about_j v v' H_notin about_v.
  rewrite add_weight_three; try assumption.
  rewrite add_weight_two;
  rewrite <- add_weight_one; easy.
Qed.

(* Under not-overweight conditions, the resulting state is a protocol state *)
Theorem next_equivocation_protocol_state
  {C V} `{PS : ProtocolState C V}
  : forall j : @state C V,
    protocol_state j ->
    forall v v',
      ~ In v (equivocating_senders j) ->
      v <> v' ->
      (* This is the most minimal condition we need about fault weight *)
      (add_weight_under j v ->
       protocol_state (next_equivocation_state j v v')).
Proof.
  intros j about_j v v' H_notin H_neq H_weight.
  assert (H_useful := about_equivocating_messages j v v' H_neq).
  destruct H_useful as [H2_noteq [H2_sender [H2_left H2_right]]].
  (* Now. *)
  constructor; try assumption; try apply correct_estimate.
  - apply copy_protocol_state; try assumption; try apply get_estimate_correct.
    apply copy_protocol_state; try assumption; try apply get_estimate_correct.
  - intros msg H_in.
    (* Facilitate membership peeling with helper lemma *)
    do 2 apply add_preserves_message_membership.
    assumption.
  - apply get_estimate_correct.
  - red.
    replace (add_in_sorted_fn (get_estimate j, v, j)
        (add_in_sorted_fn
           (get_estimate (add_in_sorted_fn (get_estimate j, v', j) j), v,
           add_in_sorted_fn (get_estimate j, v', j) j)
           (add_in_sorted_fn (get_estimate j, v', j) j)))
      with (next_equivocation_state j v v') by auto.
    rewrite equivocation_adds_fault_weight;
    assumption.
Qed.

(* Under additional not-already-equivocating conditions, the resulting state actually adds weight *)
Lemma next_equivocation_adds_weight
  {C V} `{PS : ProtocolState C V}
  : forall (s : @state C V),
    protocol_state s ->
    forall (v : V),
      (* If the weight is not over *)
      add_weight_under s v ->
      (* And the sender is not already equivocating *)
      ~ In v (equivocating_senders s) ->
      forall (v' : V),
        v <> v' ->
        (* Then we get a protocol state *)
        protocol_state (next_equivocation_state s v v') /\
        (* With increased weight *)
        fault_weight_state (next_equivocation_state s v v') =
        (fault_weight_state s + proj1_sig (weight v))%R.
Proof.
  intros s about_s v H_not_heavy H_notin v' H_neq.
  split.
  apply next_equivocation_protocol_state; assumption.
  rewrite equivocation_adds_fault_weight; easy.
Qed.

(* Now we want to add a series of equivocations *)
Fixpoint next_equivocation_rec
  {C V} `{PS : ProtocolState C V} `{Hit : InhabitedTwice V}
  (s : @state C V) (vs : list V) : state
  :=
  let HscV := triple_strictly_comparable_proj2 about_M in
    match vs with
    | [] => s
    | hd :: tl => next_equivocation_rec (next_equivocation_state s hd (get_distinct_sender hd)) tl
    end.

(* Tweaking this function to give an explicit distinct sender *)
Fixpoint next_equivocation_rec'
  {C V} `{PS : ProtocolState C V}
  (s : @state C V) (vs : list V) (v0 : V) : state :=
  match vs with
  | [] => s
  | hd :: tl => next_equivocation_state (next_equivocation_rec' s tl v0) hd v0
  end.

Lemma next_equivocations_keeps_messages
  {C V} `{PS : ProtocolState C V} `{Hit : InhabitedTwice V}
  : forall (s : state) (vs : list V) (v0 : V),
  forall (msg : message C V),
    in_state msg s ->
    in_state msg (next_equivocation_rec' s vs v0).
Proof.
  intros s vs v0 msg H_in.
  induction vs as [|hd tl IHvs].
  - assumption.
  - simpl.
    now apply next_equivocation_state_keeps_messages.
Qed.

Lemma next_equivocations_keeps_equivocating_senders
  {C V} `{PS : ProtocolState C V} `{Hit : InhabitedTwice V}
  : forall (s : @state C V) (vs : list V) (v0 : V),
  forall (v : V),
    In v (equivocating_senders s) ->
    In v (equivocating_senders (next_equivocation_rec' s vs v0)).
Proof.
  intros s vs v0 v H_in.
  induction vs as [|hd tl IHvs].
  - assumption.
  - simpl.
    unfold next_equivocation_state.
    do 3 (rewrite equivocating_sender_add_in_sorted_iff; right).
    assumption.
Qed.

Lemma next_equivocation_equivocating_sender_cons
  {C V} `{PS : ProtocolState C V}
  : forall (s : @state C V),
    protocol_state s ->
    forall (hd : V) (v0 v : V),
      v <> v0 ->
      In v (equivocating_senders (next_equivocation_state s hd v0)) <->
      v = hd \/ In v (equivocating_senders s).
Proof.
  intros s about_s hd v0 v H_neq.
  split; intro H.
  - unfold next_equivocation_state in H.
    apply equivocating_sender_add_in_sorted_iff in H.
    destruct H.
    tauto.
    apply equivocating_sender_add_in_sorted_iff in H.
    destruct H.
    tauto.
    apply equivocating_sender_add_in_sorted_iff in H.
    destruct H.
    simpl in H. destruct H. contradiction.
    tauto.
  - destruct H.
    subst.
    now apply about_equivocating_messages_add_equivocator.
    apply equivocating_senders_correct in H.
    destruct H as [msg [H_in [H_sender H_equiv]]].
    apply equivocating_senders_correct.
    exists msg. repeat split.
    unfold next_equivocation_state; rewrite in_state_add_in_sorted_iff. right.
    rewrite in_state_add_in_sorted_iff. right.
    rewrite in_state_add_in_sorted_iff. right.
    assumption. assumption.
    now apply next_equivocation_state_keeps_equivocating_messages.
Qed.

Lemma next_equivocations_equivocating_senders_iff
  {C V} `{PS : ProtocolState C V}
  : forall (s : @state C V) (vs : list V) (v0 v : V),
    (In v vs -> v <> v0) ->
    In v (equivocating_senders (next_equivocation_rec' s vs v0)) <->
    In v vs \/ In v (equivocating_senders s).
Proof.
  intros s vs; induction vs as [|hd tl IHvs]; intros v0 v H_neq.
  - split; intros.
    + simpl in H. tauto.
    + simpl; destruct H; tauto.
  - split; intros.
    + spec IHvs v0 v.
      spec IHvs.
      { intros.
        spec H_neq. right; assumption.
        assumption. }
      simpl in H.
      apply equivocating_sender_add_in_sorted_iff in H.
      destruct H as [[ ? ? ] | ?].
      subst. left. simpl. tauto.
      apply equivocating_sender_add_in_sorted_iff in H.
      simpl in H.
      destruct H as [[ ? ? ] | ?].
      subst. left. apply in_eq.
      apply equivocating_sender_add_in_sorted_iff in H.
      simpl in H.
      destruct H as [[ ? ? ] | ?].
      subst.
      (* Now. H0 must be false. *)
      destruct H0 as [msg_absurd [H_in H_equiv]].
      assert (H_contra := non_equivocating_messages_extend msg_absurd (next_equivocation_rec' s tl v0) (get_estimate (next_equivocation_rec' s tl v0)) v0).
      spec H_contra H_in.
      apply equivocating_messages_correct in H_equiv.
      rewrite equivocating_messages_comm in H_equiv.
      rewrite H_equiv in H_contra.
      inversion H_contra.
      rewrite IHvs in H. destruct H.
      left; apply in_cons; assumption.
      tauto.
    + (* Discharging induction hypothesis premise *)
      spec IHvs v0 v.
      spec IHvs. intros.
      apply H_neq.
      right; assumption.
      (* Case analysis on where v is *)
      destruct H as [H_in | H_equiv].
      * (* When we are looking at the hd element, *)
        inversion H_in.
        ** subst.
           spec H_neq (in_eq v tl).
           simpl.
           apply equivocating_sender_add_in_sorted_iff.
           left. simpl. split. reflexivity.
           exists (get_estimate
          (add_in_sorted_fn
             (get_estimate (next_equivocation_rec' s tl v0), v0,
             next_equivocation_rec' s tl v0)
             (next_equivocation_rec' s tl v0)), v,
       add_in_sorted_fn
         (get_estimate (next_equivocation_rec' s tl v0), v0,
         next_equivocation_rec' s tl v0)
         (next_equivocation_rec' s tl v0)).
           split.
           apply in_state_add_in_sorted_iff.
           left. reflexivity.
           now apply about_equivocating_messages.
        ** simpl. clear H_in.
           spec H_neq (in_cons hd v tl H).
           do 3 (apply equivocating_sender_add_in_sorted_iff; right).
           apply IHvs.
           tauto.
      * simpl.
        do 3 (apply equivocating_sender_add_in_sorted_iff; right).
        apply IHvs. right.
        assumption.
Qed.

Lemma next_equivocations_add_weights
  {C V} `{PS : ProtocolState C V}
  : forall (s : @state C V),
    protocol_state s ->
    forall (vs : list V) (v0 : V),
      NoDup vs ->
      (* The sum weight is not over *)
      (fault_weight_state s + sum_weights vs <= proj1_sig threshold)%R ->
      (* None of the senders are already equivocating *)
      (forall (v : V),
          In v vs -> ~ In v (equivocating_senders s) /\ v <> v0) ->
      (* Then we end up with a protocol state *)
      protocol_state (next_equivocation_rec' s vs v0) /\
      (* And s recursively adds the sums of all the weights in vs *)
      fault_weight_state (next_equivocation_rec' s vs v0) =
      (fault_weight_state s + sum_weights vs)%R.
Proof.
  intros s about_s vs v0 H_nodup H_underweight H_disjoint.
  induction vs as [|hd tl IHvs].
  - (* Base case : no validators to add *)
    split. assumption.
    rewrite Rplus_0_r. reflexivity.
  - (* Induction step *)
    (* Discharging first premise *)
    spec IHvs.
    rewrite NoDup_cons_iff in H_nodup; tauto.
    (* Discharging second premise *)
    spec IHvs.
    simpl in H_underweight.
    apply (Rplus_le_reg_pos_r (fault_weight_state s + sum_weights tl) (proj1_sig (weight hd)) (proj1_sig threshold)).
    destruct (weight hd). firstorder.
    rewrite Rplus_assoc.
    rewrite (Rplus_comm (sum_weights tl) (proj1_sig (weight hd))).
    rewrite <- Rplus_assoc.
    rewrite <- Rplus_assoc in H_underweight.
    assumption.
    (* Discharging third premise *)
    spec IHvs.
    intros. spec H_disjoint v. spec H_disjoint.
    right; assumption.
    assumption.
    (* Now. *)
    destruct IHvs as [H_prot H_weight].
    spec H_disjoint hd (in_eq hd tl).
    assert (H_notin_tl : ~ In hd tl).
    { rewrite NoDup_cons_iff in H_nodup.
      tauto. }
    destruct H_disjoint as [H_disjoint H_neq].
    assert (H_rewrite := next_equivocations_equivocating_senders_iff s tl v0 hd).
    spec H_rewrite.
    intros. assumption.
    split.
    + simpl.
      apply next_equivocation_protocol_state; try assumption.
      intros H_absurd.
      rewrite H_rewrite in H_absurd.
      tauto.
      (* Need a helper lemma about weight adding here *)
      unfold add_weight_under.
      rewrite H_weight. simpl in H_underweight.
      rewrite <- Rplus_assoc in H_underweight.
      rewrite Rplus_assoc.
      rewrite (Rplus_comm (sum_weights tl) (proj1_sig (weight hd))).
      rewrite <- Rplus_assoc.
      assumption.
    + simpl.
      rewrite (Rplus_comm (proj1_sig (weight hd)) (sum_weights tl)).
      rewrite <- Rplus_assoc.
      rewrite <- H_weight.
      apply equivocation_adds_fault_weight; try assumption.
      intro H_absurd. rewrite H_rewrite in H_absurd.
      tauto.
Qed.

Definition potentially_pivotal_state
  {C V} `{about_M : StrictlyComparable (message C V)} `{Hrt : ReachableThreshold V}
  (v : V) (s : @state C V)
  :=
  (* We say that v is a pivotal validator for some state s iff : *)
  (* v is not already equivocating in s *)
  ~ In v (equivocating_senders s) /\
  (* There is a remaining list of validators *)
  exists (vs : list V),
    (* That is duplicate-free *)
    NoDup vs /\
    (* Doesn't contain v *)
    ~ In v vs /\
    (* That are all not already equivocating in s *)
    (forall (v : V), In v vs -> ~ In v (equivocating_senders s)) /\
    (* That tip over s's fault weight but only with the help of v *)
    (sum_weights ((equivocating_senders s) ++ vs) <= proj1_sig threshold)%R /\
    (sum_weights ((equivocating_senders s) ++ vs) >
     proj1_sig threshold - proj1_sig (weight v))%R.

(* This is a critical lemma *)
Lemma all_pivotal_validator
  {C V} `{PS : ProtocolState C V}
  : forall (s : @state C V),
    protocol_state s ->
  exists (v : V),
    potentially_pivotal_state v s.
Proof.
  remember (triple_strictly_comparable_proj2 about_M) as HscV.
  remember (@compare _ HscV) as compare_v.
  intros s about_s.
  destruct suff_val as [vs [Hvs Hweight]].
  remember (equivocating_senders s) as eqv_s.
  remember (set_diff compare_eq_dec vs eqv_s) as vss.
  assert (sum_weights (vss ++ eqv_s) > proj1_sig threshold)%R.
  { apply Rge_gt_trans with (sum_weights vs); try assumption.
    apply Rle_ge. apply (@sum_weights_incl V HscV) ; try assumption.
    - rewrite Heqvss. apply diff_app_nodup; try assumption.
      subst. unfold equivocating_senders. apply set_map_nodup.
    - rewrite Heqvss. intros a Hin. apply in_app_iff.
      rewrite set_diff_iff. apply or_and_distr_left.
      split; try (left; assumption).
      destruct (in_dec compare_eq_dec a eqv_s); (left; assumption) || (right; assumption).
  }
  apply pivotal_validator_extension in H.
  - destruct H as [vs' [Hnodup_vs' [Hincl_vs' [Hgt [v [Hin_v Hlt]]]]]].
    exists v. split.
    + subst. apply Hincl_vs' in Hin_v. apply set_diff_elim2 in Hin_v. assumption.
    + exists (set_remove compare_eq_dec v vs').
      assert (NoDup (set_remove compare_eq_dec v vs')) as Hnodup_remove
      ; try apply set_remove_nodup; try assumption.
      repeat split.
      * assumption.
      * try apply set_remove_elim; try assumption.
      * intros. apply set_remove_1 in H. apply Hincl_vs' in H. subst.
        apply set_diff_elim2 in H. assumption.
      * subst. rewrite sum_weights_app in *. rewrite Rplus_comm in Hlt.
        assumption.
      * apply Rlt_gt. apply Rplus_lt_reg_r with (proj1_sig (weight v)).
        unfold Rminus. rewrite Rplus_assoc. rewrite Rplus_opp_l.
        rewrite Rplus_0_r. apply Rgt_lt.
        apply Rge_gt_trans with (sum_weights (vs' ++ eqv_s)); try assumption.
        unfold Rge. right. rewrite Rplus_comm.
        rewrite sum_weights_app. rewrite (Rplus_comm (sum_weights (equivocating_senders s))) .
        rewrite <- Rplus_assoc. rewrite sum_weights_app. subst.
        apply Rplus_eq_compat_r.
        symmetry. apply sum_weights_in; try assumption.
  - subst. apply set_map_nodup.
  - subst. apply protocol_state_not_heavy. assumption.
  - subst. apply diff_app_nodup; try assumption.
    apply set_map_nodup.
Qed.

Theorem strong_nontriviality_full
  {C V : Type} `{PS : ProtocolState C V} `{Hit : InhabitedTwice V}
  : @strong_nontriviality C V _ _ _ _ _.
Proof.
  remember (triple_strictly_comparable_proj2 about_M) as HscV.
  remember (@compare _ HscV) as compare_v.
  intros [s1 about_s1].
  destruct (all_pivotal_validator s1 about_s1) as [v [H_v [vs [H_nodup [H_v_notin [H_disjoint [H_under H_over]]]]]]].
  remember (exist protocol_state (add_in_sorted_fn (get_estimate s1,v,s1) s1) (copy_protocol_state s1 about_s1  (get_estimate s1) (get_estimate_correct s1) v)) as s2.
  (* Book-keeping *)
  assert (H_s1_s2_senders : set_eq (equivocating_senders s1) (equivocating_senders (proj1_sig s2))) by (subst; apply equivocating_senders_sorted_extend).
  assert (H_s1_s2_weight : fault_weight_state s1 = fault_weight_state (proj1_sig s2)) by (subst; apply add_weight_one).
  exists s2.
  (* Proving next-step relation is trivial. *)
  split.
  exists (get_estimate s1,v,s1); subst; easy.
  (* s3 is the state with equivocations from all the senders in vs recursively added to s1, in addition to (c,v,s1)'s equivocating partner message. *)
  (* First we add the equivocating partner message *)
  remember (add_in_sorted_fn (get_estimate (add_in_sorted_fn (get_estimate s1, get_distinct_sender v, s1) s1), v, (add_in_sorted_fn (get_estimate s1, get_distinct_sender v, s1) s1)) (add_in_sorted_fn (get_estimate s1, get_distinct_sender v, s1) s1)) as s1'.
  (* Book-keeping step *)
  assert (H_eq_senders : set_eq (equivocating_senders s1') (equivocating_senders s1)).
  { rewrite Heqs1'.
    assert (H_useful := equivocating_senders_sorted_extend (add_in_sorted_fn (get_estimate s1, get_distinct_sender v, s1) s1) v).
    eapply set_eq_tran.
    apply set_eq_comm. exact H_useful.
    apply set_eq_comm. apply equivocating_senders_sorted_extend. }
  assert (H_s_inter_weight : fault_weight_state s1' = fault_weight_state s1).
  { apply equivocating_senders_fault_weight_eq; assumption. }
  (* Now we are ready to construct s3 from s1' *)
  (* And if we have set up everything correctly, the premises at this point in the proof are sufficient. *)
  remember (next_equivocation_rec' s1' vs v) as s3.
  assert (about_s3 : protocol_state s3).
  { rewrite Heqs3. apply next_equivocations_add_weights.
    { subst.
      apply copy_protocol_state; try apply get_estimate_correct; try assumption.
      apply copy_protocol_state; try apply get_estimate_correct; try assumption. }
    assumption.
    rewrite H_s_inter_weight. rewrite sum_weights_app in H_under.
    assumption.
    intros. spec H_disjoint v0 H.
    destruct H_eq_senders as [H_left H_right].
    spec H_right v0.
    split. intro H_absurd. spec H_left v0 H_absurd.
    contradiction. intro H_absurd. subst. contradiction. }
  exists (exist protocol_state s3 about_s3).
  repeat split.
  - (* Proving that s1 and s3 share a common future *)
    red. exists (exist protocol_state s3 about_s3).
    split. simpl. red.
    red. subst.
    intros m0 H_in.
    (* Need to prove that next_equivocation_rec' doesn't drop messages *)
    apply next_equivocations_keeps_messages.
    do 2 (rewrite in_state_add_in_sorted_iff; right).
    assumption.
    apply incl_refl.
  - (* Proving that s2 and s3 don't share a common future *)
    (* Arbitrary state in both s2 and s3 leads to a contradiction *)
    red. intros [s about_s] H.
    destruct H as [H_in2 H_in3].
    assert (H_in2_copy := H_in2);
      assert (H_in3_copy := H_in3).
    unfold in_future, syntactic_state_inclusion in H_in2, H_in3.
    (* Now we show that two equivocating messages are in s *)
    (* First message *)
    spec H_in2 (get_estimate s1,v,s1).
    spec H_in2.
    subst; apply in_state_add_in_sorted_iff.
    tauto.
    (* Second message *)
    spec H_in3 (get_estimate
                (add_in_sorted_fn
                   (get_estimate s1, get_distinct_sender v, s1) s1), v,
             add_in_sorted_fn
               (get_estimate s1, get_distinct_sender v, s1) s1).
    spec H_in3.
    { (* Proving that this message is in s3 *)
      assert (H_obv : in_state (get_estimate (add_in_sorted_fn (get_estimate s1, get_distinct_sender v, s1) s1), v, add_in_sorted_fn (get_estimate s1, get_distinct_sender v, s1) s1) s1').
      { subst. rewrite in_state_add_in_sorted_iff.
        left. reflexivity. }
      apply (next_equivocations_keeps_messages s1' vs v) in H_obv.
      subst; assumption. }
    (* Now we prove that these two messages are equivocating *)
    simpl in *.
    assert (H_equiv : equivocating_messages_prop (get_estimate s1,v,s1)
                                                 (get_estimate (add_in_sorted_fn (get_estimate s1, get_distinct_sender v, s1) s1), v, add_in_sorted_fn (get_estimate s1, get_distinct_sender v, s1) s1)).
    apply about_equivocating_messages.
    apply get_distinct_sender_correct.
    (* Now we say that v will be an equivocating sender inside s *)
    assert (H_v_in : In v (equivocating_senders s)).
    { apply equivocating_senders_correct.
      exists (get_estimate s1, v, s1).
      repeat split; try assumption.
      exists (get_estimate (add_in_sorted_fn (get_estimate s1, get_distinct_sender v, s1) s1), v, add_in_sorted_fn (get_estimate s1, get_distinct_sender v, s1) s1).
      split. assumption. assumption. }
    clear H_in2 H_in3 H_equiv.
    (* Now we say that v's weight will be inside s's fault weight *)
    (* This part is a little tricky *)
    assert (H_equivocators_s : incl (v :: (equivocating_senders (proj1_sig s2) ++ vs)) (equivocating_senders s)).
    { intros v0 H_in0.
      destruct H_in0 as [H_hd | H_tl].
      + subst. assumption.
      + apply in_app_iff in H_tl.
        destruct H_tl as [H_left | H_right].
        * eapply equivocating_senders_incl.
          apply H_in2_copy.
          assumption.
        * assert (H_in_v0 : In v0 (equivocating_senders (next_equivocation_rec' s1' vs v))).
          { apply next_equivocations_equivocating_senders_iff.
            intros _ H_absurd. subst. contradiction.
            tauto. }
          rewrite <- Heqs3 in H_in_v0.
          eapply equivocating_senders_incl.
          exact H_in3_copy.
          assumption.
    }
    assert (H_s_overweight : (proj1_sig (weight v) + fault_weight_state (proj1_sig s2) + sum_weights vs <= fault_weight_state s)%R).
    { replace ((proj1_sig (weight v) + fault_weight_state (proj1_sig s2) + sum_weights vs))%R with (sum_weights ([v] ++ (equivocating_senders (proj1_sig s2)) ++ vs)).
      apply sum_weights_incl.
      { (* Proving mutual NoDup *)
        apply nodup_append.
        apply NoDup_cons. intros; inversion 1.
        constructor.
        apply nodup_append.
        apply set_map_nodup. assumption.
        { intros. intro Habsurd. spec H_disjoint a Habsurd.
          destruct H_s1_s2_senders as [_ H_useful].
          spec H_useful a H. contradiction.
        }
        { intros. intro Habsurd. spec H_disjoint a H.
          destruct H_s1_s2_senders as [_ H_useful].
          spec H_useful a Habsurd. contradiction. }
        { intros. inversion H. intro Habsurd.
          apply in_app_iff in Habsurd. destruct Habsurd.
          destruct H_s1_s2_senders as [_ H_useful];
            spec H_useful a H1.
          subst; contradiction. subst; contradiction. inversion H0. }
        { intros. intro Habsurd.
          inversion Habsurd.
          apply in_app_iff in H. destruct H.
          destruct H_s1_s2_senders as [_ H_useful];
            spec H_useful a H.
          subst; contradiction. subst; contradiction. inversion H0. }
      }
      apply set_map_nodup. assumption.
      do 2 rewrite sum_weights_app.
      unfold fault_weight_state.
      simpl. ring. }
    apply protocol_state_not_heavy in about_s.
    red in about_s.
    assert (H_finale := Rle_trans _ _ _ H_s_overweight about_s). auto.
    clear -H_finale H_over H_s1_s2_weight.
    rewrite sum_weights_app in H_over.
    unfold fault_weight_state in H_s1_s2_weight at 1.
    rewrite H_s1_s2_weight in H_over.
    apply (Rplus_gt_compat_l (proj1_sig (weight v))) in H_over.
    replace (proj1_sig (weight v) + (proj1_sig threshold - proj1_sig (weight v)))%R with (proj1_sig threshold)%R in H_over by ring.
    rewrite <- Rplus_assoc in H_over.
    apply Rgt_not_le in H_over.
    contradiction.
Qed.
