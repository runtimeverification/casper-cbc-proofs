Require Import Reals Bool Relations RelationClasses List ListSet Setoid Permutation.
Import ListNotations.  
From Casper
Require Import preamble ListExtras ListSetExtras.

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
      state0 : state;
      state_eq : state -> state -> Prop;
      state_union : state -> state -> state;
      state_union_comm : forall s1 s2, state_eq (state_union s1 s2) (state_union s2 s1);
(* Toplevel input, characters 138-144: *)
(* > Definition non_trivial_state (p : sorted_state -> Prop) :=   (exists sigma1, protocol_state sigma1 /\ decided sigma1 p)   /\   (exists sigma2, protocol_state sigma2 /\ decided sigma2 (predicate_not p)). *)
(* >                                                                                                               ^^^^^^ *)
(* Error: *)
(* In environment *)
(* C, V : Type *)
(* about_C : StrictlyComparable C *)
(* about_V : StrictlyComparable V *)
(* p : sorted_state -> Prop *)
(* sigma1 : state *)
(* The term "sigma1" has type "state" while it is expected to have type *)
(*  "protocol_eq.state". *)
      (** Reachability relation **) 
      reach : state -> state -> Prop; 
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

(*
Add Parametric Relation `{CBC_protocol_eq} : state state_eq 
  reflexivity proved by (eq_state_refl)
  symmetry proved by (eq_state_sym)
  transitivity proved by (eq_state_trans)
  as eq_state_rel.

Add Parametric Morphism `{CBC_protocol_eq} : state_union
  with signature state_eq ==> state_eq ==> state_eq as state_union_mor.
Proof. exact state_union_compat. Qed. 
 *)

Theorem reach_total `{CBC_protocol_eq} :
  forall s, exists s', reach s s'.
Proof. intro s. exists (state_union s s). apply (reach_union s s). Qed.

Section CommonFutures. 

  (* Theorem 1 *) 
  Theorem pair_common_futures `{CBC_protocol_eq}:
    forall s1 s2,
      prot_state s1 ->
      prot_state s2 ->
      (equivocation_weight (state_union s1 s2) <= proj1_sig t)%R ->
      exists s, prot_state s /\ reach s1 s /\ reach s2 s.
  Proof.
    intros s1 s2 H_s1 H_s2 H_weight.
    exists (state_union s1 s2); split.
    apply about_prot_state; assumption. 
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

  (* Theorem 2 *) 
  Theorem n_common_futures `{CBC_protocol_eq} :
    forall ls,
      Forall prot_state ls ->
      (equivocation_weight (fold_right state_union state0 ls) <= proj1_sig t)%R ->
      exists s, prot_state s /\ Forall (fun s' => reach s' s) ls. 
  Proof.
    intros ls H_ls H_weight.
    exists (fold_right state_union state0 ls); split. 
    apply prot_state_union_iter; assumption.
    apply Forall_forall. intros s H_in.
    now apply reach_union_iter.
  Qed. 

End CommonFutures.

Section Consistency.

  Definition decided `{CBC_protocol_eq} (s : state) (P : state -> Prop) :=
    forall s', reach s s' -> P s'. 

  Definition not `{CBC_protocol_eq} (P : state -> Prop) :=
    fun s => P s -> False.
  
  Lemma forward_consistency `{CBC_protocol_eq} :
    forall s P,
      decided s P ->
      forall s',
        reach s s' ->
        decided s' P.
  Proof.
    intros s P H_dec s' H_rel.
    unfold decided in *.
    intros s'' H_rel'.
    assert (reach s s'') by (apply (reach_trans s s' s''); assumption).
    spec H_dec s''; now apply H_dec. 
  Qed.

  Lemma backward_consistency `{CBC_protocol_eq} :
    forall s s',
      reach s s' ->
      forall P,
      decided s' P ->
      ~ decided s (not P).
  Proof. 
    intros s s' H_rel P H_dec Hnot.
    destruct (reach_total s') as [s'' H_rel']. 
    unfold decided in *.
    spec H_dec s'' H_rel'. spec Hnot s''.
    assert (H_r : reach s s'') by (apply (reach_trans s s' s''); assumption).
    spec Hnot H_r; contradiction.
  Qed. 

  (* Theorem 3 *) 
  Theorem pair_consistency_prot `{CBC_protocol_eq} :
    forall s1 s2,
      prot_state s1 ->
      prot_state s2 ->
      (equivocation_weight (state_union s1 s2) <= proj1_sig t)%R ->
      forall P, 
        ~ (decided s1 P /\ decided s2 (not P)).
  Proof.
    intros s1 s2 H_s1 H_s2 H_weight P [H_dec H_dec_not]. 
    destruct (pair_common_futures s1 s2 H_s1 H_s2 H_weight) as [s [H_s [H_r1 H_r2]]].
    spec H_dec s H_r1. spec H_dec_not s H_r2. contradiction.
  Qed. 

  (* Consistency on state properties *) 
  Definition state_consistency `{CBC_protocol_eq} (ls : list state) : Prop :=
    exists s,
      prot_state s /\
      forall (P : state -> Prop),
        Exists (fun s => decided s P) ls ->
        P s.
  
  (* Theorem 4 *) 
  Theorem n_consistency_prot `{CBC_protocol_eq} :
    forall ls,
      Forall prot_state ls ->
      (equivocation_weight (fold_right state_union state0 ls) <= proj1_sig t)%R ->
      state_consistency ls. 
  Proof. 
    intros ls H_ls H_weight. 
    destruct (n_common_futures ls H_ls H_weight) as [s' [H_s' H_reach]].
    exists s'; split. 
    assumption.
    intros P H_exists.
    apply Exists_exists in H_exists.
    destruct H_exists as [s'' [H_in'' H_dec'']].
    rewrite Forall_forall in H_reach. 
    spec H_reach s'' H_in''.
    spec H_dec'' s' H_reach.
    assumption.
  Qed.

  (* Consistency on consensus values *) 
  Definition lift `{CBC_protocol_eq} (P : consensus_values -> Prop) : state -> Prop :=
    fun s => forall c : consensus_values, E s c -> P c.

  Definition consensus_value_consistency `{CBC_protocol_eq} (ls : list state) : Prop :=
    exists c,
      forall (P : consensus_values -> Prop),
        Exists (fun s => decided s (lift P)) ls ->
        P c. 

  (* Theorem 5 *)
  Theorem n_consistency_consensus `{CBC_protocol_eq} :
    forall ls,
      Forall prot_state ls ->
      (equivocation_weight (fold_right state_union state0 ls) <= proj1_sig t)%R ->
      consensus_value_consistency ls. 
  Proof.
    intros ls H_ls H_weight. 
    destruct (n_consistency_prot ls H_ls H_weight) as [s [H_s H_dec]].
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

From Casper
Require Import protocol. 

Section Derivations.

  (* Proving that protocol is a special instance of protocol-eq with syntactic equality for state_eq *) 

  Variable (P : CBC_protocol).

  Instance P_syntactic : CBC_protocol_eq :=
  { consensus_values := consensus_values;  
    about_consensus_values := about_consensus_values;
    validators := validators;
    about_validators := about_validators;
    weight := weight;
    t := t;
    suff_val := suff_val;
    state := state;
    state0 := state0;
    (* >> *) state_eq := eq; 
    state_union := state_union;
    state_union_comm := state_union_comm;
    reach := reach; 
    reach_trans := reach_trans;
    reach_union := reach_union;
    (* >> *) reach_morphism := _;
    E := E;
    estimator_total := estimator_total; 
    prot_state := prot_state;
    about_state0 := about_state0;
    equivocation_weight := equivocation_weight; 
    equivocation_weight_compat := equivocation_weight_compat; 
    about_prot_state := about_prot_state;
  }.
  intros. 
  subst; assumption. 
  Defined. 

End Derivations.