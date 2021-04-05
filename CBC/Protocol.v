From Coq Require Import Reals Bool Relations RelationClasses List ListSet Setoid Permutation EqdepFacts ProofIrrelevance.
Import ListNotations.

From CasperCBC.Lib Require Import Preamble ListExtras ListSetExtras.

(** * CBC Protocol Definitions and Lemmas *)

(* Level 0 : *)
Class PartialOrder (A : Type) :=
  { A_eq_dec : forall (a1 a2 : A), {a1 = a2} + {a1 <> a2};
    A_inhabited : exists (a0 : A), True; (* ? *)
    A_rel : A -> A -> Prop;
    A_rel_refl :> Reflexive A_rel;
    A_rel_trans :> Transitive A_rel;
  }.

(* Level 1 : *)
Class PartialOrderNonLCish (A : Type) `{PartialOrder A} :=
  { no_local_confluence_ish : exists (a a1 a2 : A),
        A_rel a a1 /\ A_rel a a2 /\
        ~ exists (a' : A), A_rel a1 a' /\ A_rel a2 a';
  }.

(* Level Specific : *)
Class CBC_protocol_eq :=
   {
      (** Consensus values equipped with reflexive transitive comparison **)
      consensus_values : Type;
      about_consensus_values : StrictlyComparable consensus_values;
      (** Validators equipped with reflexive transitive comparison **)
      validators : Type;
      about_validators : StrictlyComparable validators;
      (** Weights are positive reals **)
      weight : validators -> {r | (r > 0)%R};
      (** Threshold is a non-negative real **)
      t : {r | (r >= 0)%R};
      suff_val : exists vs, NoDup vs /\ ((fold_right (fun v r => (proj1_sig (weight v) + r)%R) 0%R) vs > (proj1_sig t))%R;
      (** States with equality and union **)
      state : Type;
      about_state : StrictlyComparable state;
      state0 : state;
      state_eq : state -> state -> Prop;
      state_union : state -> state -> state;
      state_union_comm : forall s1 s2, state_eq (state_union s1 s2) (state_union s2 s1);
      (** Reachability relation **)
      reach : state -> state -> Prop;
      reach_refl : forall s, reach s s;
      reach_trans : forall s1 s2 s3, reach s1 s2 -> reach s2 s3 -> reach s1 s3;
      reach_union : forall s1 s2, reach s1 (state_union s1 s2);
      reach_morphism : forall s1 s2 s3, reach s1 s2 -> state_eq s2 s3 -> reach s1 s3;
      (** Total estimator **)
      E : state -> consensus_values -> Prop;
      estimator_total : forall s, exists c, E s c;
      (** Protocol state definition as predicate **)
      prot_state : state -> Prop;
      about_state0 : prot_state state0;
      (** Equivocation weights from states **)
      equivocation_weight : state -> R;
      equivocation_weight_compat : forall s1 s2, (equivocation_weight s1 <= equivocation_weight (state_union s2 s1))%R;
      about_prot_state : forall s1 s2, prot_state s1 -> prot_state s2 ->
                                  (equivocation_weight (state_union s1 s2) <= proj1_sig t)%R -> prot_state (state_union s1 s2);
   }.

Theorem reach_total `{CBC_protocol_eq} :
  forall s, exists s', reach s s'.
Proof. intro s. exists (state_union s s). apply (reach_union s s). Qed.

(** Defining A **)
Definition pstate `{CBC_protocol_eq} : Type := {s : state | prot_state s}.
Definition pstate_proj1 `{CBC_protocol_eq} (p : pstate) : state :=
  proj1_sig p.
Coercion pstate_proj1 : pstate >-> state.

(** Proving A_eq_dec **)
Lemma pstate_eq_dec `{CBC_protocol_eq} : forall (p1 p2 : pstate), {p1 = p2} + {p1 <> p2}.
Proof.
  intros p1 p2.
  assert (H_useful := about_state).
  now apply sigify_eq_dec.
Qed.

(** Proving A_inhabited **)
Lemma pstate_inhabited `{CBC_protocol_eq} : exists (p1 : pstate), True.
Proof. now exists (exist prot_state state0 about_state0). Qed.

(** Defining A_rel **)
Definition pstate_rel `{CBC_protocol_eq} : pstate -> pstate -> Prop :=
  fun p1 p2 => reach (pstate_proj1 p1) (pstate_proj1 p2).

(** Proving A_rel_refl **)
Lemma pstate_rel_refl `{CBC_protocol_eq} : Reflexive pstate_rel.
Proof. red; intro p; now apply reach_refl. Qed.

(** Proving A_rel_trans **)
Lemma pstate_rel_trans `{CBC_protocol_eq} : Transitive pstate_rel.
Proof.
  red; intros p1 p2 p3 H_12 H_23.
  destruct p1 as [p1 about_p1];
    destruct p2 as [p2 about_p2];
    destruct p3 as [p3 about_p3];
    simpl in *.
  now apply reach_trans with p2.
Qed.

Instance level0 `{CBC_protocol_eq} : PartialOrder pstate :=
  { A_eq_dec := pstate_eq_dec;
    A_inhabited := pstate_inhabited;
    A_rel := pstate_rel;
    A_rel_refl := pstate_rel_refl;
    A_rel_trans := pstate_rel_trans;
  }.



Section CommonFutures.

  (* Theorem 1 *)
  Theorem pair_common_futures `{CBC_protocol_eq}:
    forall s1 s2 : pstate,
      (equivocation_weight (state_union s1 s2) <= proj1_sig t)%R ->
      exists s : pstate, pstate_rel s1 s /\ pstate_rel s2 s.
  Proof.
    intros s1 s2 H_weight. remember s1 as ps1. remember s2 as ps2.
    destruct s1 as [s1 H_s1]. destruct s2 as [s2 H_s2].
    rewrite Heqps1, Heqps2 in H_weight; simpl in H_weight.

    exists (exist _ (state_union s1 s2) (about_prot_state s1 s2 H_s1 H_s2 H_weight)).
    subst. unfold pstate_rel. simpl.
    split. apply reach_union.
    apply (reach_morphism s2 (state_union s2 s1) (state_union s1 s2)).
    apply reach_union.
    apply state_union_comm.
  Qed.

  Lemma reach_union_iter `{CBC_protocol_eq} :
    forall s ls, In s ls -> reach s (fold_right state_union state0 ls).
  Proof.
    intros s ls H_in.
    induction ls as [|hd tl IHtl].
    - inversion H_in.
    - destruct H_in as [Heq | Hneq].
      + subst.
        simpl. apply reach_union.
      + spec IHtl Hneq. simpl.
        eapply reach_trans.
        exact IHtl.
        apply (reach_morphism (fold_right state_union state0 tl)
                              (state_union (fold_right state_union state0 tl) hd)
                              (state_union hd (fold_right state_union state0 tl))).
        apply reach_union. apply state_union_comm.
  Qed.

  Lemma prot_state_union_iter `{CBC_protocol_eq} :
    forall ls, Forall prot_state ls ->
          (equivocation_weight (fold_right state_union state0 ls) <= proj1_sig t)%R ->
          prot_state (fold_right state_union state0 ls).
  Proof.
    intros ls H_ls H_weight.
    induction ls as [|hd tl IHls].
    - simpl. exact about_state0.
    - simpl. apply about_prot_state.
      apply (Forall_inv H_ls).
      spec IHls.
      apply Forall_forall. intros x H_in.
      rewrite Forall_forall in H_ls. spec H_ls x.
      spec H_ls. right; assumption. assumption.
      spec IHls.
      simpl in H_weight.
      apply (Rle_trans (equivocation_weight (fold_right state_union state0 tl))
                       (equivocation_weight (state_union hd (fold_right state_union state0 tl)))
                       (proj1_sig t)).
      apply equivocation_weight_compat.
      assumption. assumption. assumption.
  Qed.

  Lemma pstate_list `{CBC_protocol_eq} :
    forall pls : list pstate,
      Forall prot_state (map (fun ps => proj1_sig ps) pls).
  Proof.
    intros.
    apply Forall_forall.
    induction pls; intros.
    - inversion H0.
    - destruct H0 as [Heq | Hin].
      + subst. destruct a as [a H_a]. simpl. assumption.
      + apply IHpls. assumption.
  Qed.

  (* Theorem 2 *)
  Theorem n_common_futures `{CBC_protocol_eq} :
    forall ls : list pstate,
      (equivocation_weight (fold_right state_union state0 (map (fun ps => proj1_sig ps) ls)) <= proj1_sig t)%R ->
      exists ps : pstate, Forall (fun ps' => pstate_rel ps' ps) ls.
  Proof.
    intros pls H_weight.
    remember (map (fun ps => proj1_sig ps) pls) as ls.
    assert (H_ls : Forall prot_state ls) by (subst; apply pstate_list).
    exists (exist _ (fold_right state_union state0 ls) (prot_state_union_iter ls H_ls H_weight)).
    apply Forall_forall. intros. destruct x as [x H_x]. unfold pstate_rel. simpl.
    apply reach_union_iter.
    subst. apply in_map_iff.
    exists (exist (fun s : state => prot_state s) x H_x). simpl.
    split; reflexivity || assumption.
  Qed.

End CommonFutures.

(* Level Specific -refines-> Level 0 *)

Definition reach_one `{CBC_protocol_eq} (sigma1 sigma2 : pstate) : Prop :=
  sigma1 <> sigma2 /\ pstate_rel sigma1 sigma2 /\
  forall sigma
    ,  pstate_rel sigma1 sigma
    -> pstate_rel sigma sigma2
    -> sigma = sigma1 \/ sigma = sigma2.


Inductive all_path_eventually `{CBC_protocol_eq} (P : pstate -> Prop) (sigma : pstate) : Prop :=
  | all_path_holds_now
    : P sigma -> all_path_eventually P sigma
  | all_path_holds_next
    :  (exists sigma', reach_one sigma sigma')
    -> (forall sigma', reach_one sigma sigma' -> all_path_eventually P sigma')
    -> all_path_eventually P sigma
  .

Inductive one_path_eventually `{CBC_protocol_eq} (P : pstate -> Prop) (sigma : pstate) : Prop :=
  | one_path_holds_now
    : P sigma -> one_path_eventually P sigma
  | one_path_holds_next
    :  forall sigma'
    ,  reach_one sigma sigma'
    -> one_path_eventually P sigma'
    -> one_path_eventually P sigma
  .



Section Consistency.

  Definition decided `{CBC_protocol_eq} (P : pstate -> Prop) : pstate -> Prop :=
    fun (s : pstate) => forall s', pstate_rel s s' -> P s'.

  Definition decided_on_predicate `{CBC_protocol_eq} (c : consensus_values) : pstate -> Prop
    :=
    fun (future : pstate) => forall c', E (proj1_sig future) c' -> c' = c.

  Definition decided_on `{CBC_protocol_eq} (c : consensus_values) : pstate -> Prop :=
    decided (decided_on_predicate c).

  Definition locked_on `{CBC_protocol_eq} (c : consensus_values) : pstate -> Prop :=
    all_path_eventually (decided_on c).

  Definition not_locked_off `{CBC_protocol_eq} (c : consensus_values) : pstate -> Prop :=
    one_path_eventually (decided_on c).

  Definition not `{CBC_protocol_eq} (P : pstate -> Prop) : pstate -> Prop :=
    fun s => P s -> False.

  Definition locked_off `{CBC_protocol_eq} (c : consensus_values) : pstate -> Prop :=
    not (not_locked_off c).

  Lemma forward_consistency `{CBC_protocol_eq} :
    forall s P,
      decided P s ->
      forall s',
        pstate_rel s s' ->
        decided P s'.
  Proof.
    intros s P H_dec s' H_rel.
    unfold decided in *.
    intros s'' H_rel'.
    assert (pstate_rel s s'') by (apply (pstate_rel_trans s s' s''); assumption).
    spec H_dec s''; now apply H_dec.
  Qed.

  Lemma backward_consistency `{CBC_protocol_eq} :
    forall s s',
      pstate_rel s s' ->
      forall P,
      decided P s' ->
      ~ decided (not P) s.
  Proof.
    intros s s' H_rel P H_dec Hnot.
    unfold decided in *.
    spec Hnot s' H_rel.
    apply Hnot.
    apply H_dec.
    apply pstate_rel_refl.
  Qed.

  (* Theorem 3 *)
  Theorem pair_consistency_prot `{CBC_protocol_eq} :
    forall s1 s2 : pstate,
      (equivocation_weight (state_union s1 s2) <= proj1_sig t)%R ->
      forall P,
        ~ (decided P s1 /\ decided (not P) s2).
  Proof.
    intros s1 s2 H_weight P [H_dec H_dec_not].
    destruct (pair_common_futures s1 s2 H_weight) as [s [H_r1 H_r2]].
    spec H_dec s H_r1.
    spec H_dec_not s H_r2. contradiction.
  Qed.

  (* Consistency on state properties *)
  Definition state_consistency `{CBC_protocol_eq} (ls : list pstate) : Prop :=
    exists s : pstate,
      forall (P : pstate -> Prop),
        Exists (fun s => decided P s) ls ->
        P s.

  (* Theorem 4 *)
  Theorem n_consistency_prot `{CBC_protocol_eq} :
    forall ls : list pstate,
      (equivocation_weight (fold_right state_union state0 (map (fun ps => proj1_sig ps) ls)) <= proj1_sig t)%R ->
      state_consistency ls.
  Proof.
    intros ls H_weight.
    destruct (n_common_futures ls H_weight) as [s' H_reach].
    exists s'.
    intros P H_exists.
    apply Exists_exists in H_exists.
    destruct H_exists as [s'' [H_in'' H_dec'']].
    rewrite Forall_forall in H_reach.
    spec H_reach s'' H_in''.
    spec H_dec'' s' H_reach.
    assumption.
  Qed.

  (* Consistency on consensus values *)
  Definition lift `{CBC_protocol_eq} (P : consensus_values -> Prop) : pstate -> Prop :=
    fun s => forall c : consensus_values, E (proj1_sig s) c -> P c.

  Definition consensus_value_consistency `{CBC_protocol_eq} (ls : list pstate) : Prop :=
    exists c,
      forall (P : consensus_values -> Prop),
        Exists (fun s => decided (lift P) s) ls ->
        P c.

  (* Theorem 5 *)
  Theorem n_consistency_consensus `{CBC_protocol_eq} :
    forall ls : list pstate,
      (equivocation_weight (fold_right state_union state0 (map (fun ps => proj1_sig ps) ls)) <= proj1_sig t)%R ->
      consensus_value_consistency ls.
  Proof.
    intros ls H_weight.
    destruct (n_consistency_prot ls H_weight) as [s H_dec].
    destruct (estimator_total s) as [c about_c].
    exists c. intros P H_exists.
    apply Exists_exists in H_exists.
    destruct H_exists as [s' [H_in' H_dec']].
    spec H_dec (lift P).
    spec H_dec. apply Exists_exists.
    exists s'. split; assumption.
    unfold lift in H_dec.
    spec H_dec c about_c; assumption.
  Qed.

End Consistency.

(* We can either start with PartialOrderNonLCish or CBC_protocol_eq - let's do the latter for now *)

(* Level Specific-plus : *)
Class CBC_protocol_eq_plus `{CBC_protocol_eq} :=
  {
    two_validators : exists (v1 v2 : validators), v1 <> v2;
    equivocating_senders : state -> list validators;
    next_equivocation : state -> validators -> validators -> state;
    about_next_equivocation1 : forall s v v', reach s (next_equivocation s v v');
    about_next_equivocation2 : forall s, prot_state s -> forall v v', ~ In v (equivocating_senders s) -> equivocation_weight (next_equivocation s v v') = (equivocation_weight s + proj1_sig (weight v))%R;
    about_next_equivocation3 : forall s, prot_state s -> forall v v', ~ In v (equivocating_senders s) -> (equivocation_weight s + proj1_sig (weight v) <= proj1_sig t)%R -> prot_state (next_equivocation s v v') /\ (equivocation_weight (next_equivocation s v v') = equivocation_weight s + proj1_sig (weight v))%R;
  }.
