Require Import Bool List Streams Logic.Epsilon Reals Fin FinFun.
Import ListNotations.
From CasperCBC
Require Import Lib.Preamble Lib.ListExtras Lib.ListSetExtras Lib.RealsExtras CBC.Definitions CBC.Common VLSM.Common VLSM.Composition VLSM.Decisions CBC.FullNode.

Section CompositeFullNode.

  Variables (C V : Type) (about_C : StrictlyComparable C) (about_V : StrictlyComparable V) (Hm : Measurable V) (Hrt : ReachableThreshold V) (He : Estimator (@sorted_state C V message_type) C).

  Definition reach (s1 s2 : @CBC.Definitions.state C V) : Prop :=
    incl (get_messages s1) (get_messages s2).

  Definition message : Type := @sorted_message C V message_type.

  (* 2.5.1 Minimal full client protocol: Client2 *)
  Definition label2 : Type := unit.

  Definition vtransition2
    (l : unit)
    (sm : @sorted_state C V message_type * option message)
    : @sorted_state C V message_type * option message
    :=
    let (s, om) := sm in
    match om with
    | None => (s, None)
    | Some msg => (add_message_sorted msg s, None)
    end.

  Inductive valid_client2 : unit -> (@sorted_state C V message_type) * option message -> Prop :=
  | client2_none
    : forall
      (s : @sorted_state C V message_type),
      valid_client2 tt (s, None)
  | client2_receive
    : forall
      (s : @sorted_state C V message_type)
      (m : @sorted_message C V message_type)
      (Hj : reach (justification m) s)
      (Hlight : not_heavy (add_in_sorted_fn m s)),
      valid_client2 tt (s, Some m)
      .

  Instance VLSM_type_full_client2 : VLSM_type message :=
    { state := @sorted_state C V message_type
    ; label := label2
    }.


  Definition initial_state_prop
    (s : @sorted_state C V message_type)
    : Prop
    :=
    s = @sorted_state0 C V message_type.

  Definition state0 : {s | initial_state_prop s} := 
    exist _ (@sorted_state0 C V message_type) eq_refl.

  Definition message0 : message := 
    let (c,_) := @Lib.Preamble.inhabited _ about_C in
    let (v,_) := @Lib.Preamble.inhabited _ about_V in
    (c,v,@sorted_state0 C V message_type)
    .

  Definition initial_message_prop (m : message) : Prop := False.


  Instance LSM_full_client2 : VLSM_sign VLSM_type_full_client2 :=
    { initial_state_prop := initial_state_prop
    ; initial_message_prop := initial_message_prop
    ; s0 := state0
    ; m0 := message0
    ; l0 := tt
    }.

  Instance VLSM_full_client2  : VLSM LSM_full_client2 :=
    { transition := vtransition2
      ; valid := valid_client2
    }.

  (* Section 2.5.2  Minimal full validator protocol for name v: Validator(v) *)
  Definition labelv : Type := option C.

  Definition vtransitionv (v : V) (l : labelv) (sm : @sorted_state C V message_type * option message) : @sorted_state C V message_type * option message :=
    match l with
    | None => match (snd sm) with
             | None => sm
             | Some msg => (add_message_sorted msg (fst sm), None)
           end
    | Some c => (add_message_sorted (c,v, fst sm) (fst sm), Some (c,v, fst sm))
    end.

  Inductive valid_validator : labelv ->  @sorted_state C V message_type * option message -> Prop :=
  | validator_none
    : forall
      (s : @sorted_state C V message_type),
      valid_validator None (s, None)
  | validator_receive
    : forall
      (s : @sorted_state C V message_type)
      (m : @sorted_message C V message_type)
      (Hj : reach (justification m) s),
      valid_validator None (s, Some m)
  | validator_send
    : forall
      (c : C)
      (s : state)
      (m : option message)
      (He : (@estimator (@sorted_state C V message_type) C He) s c),
      valid_validator (Some c) (s, m).

  Instance VLSM_type_full_validator : VLSM_type message :=
    { state := @sorted_state C V message_type
    ; label := labelv
    }.

  Instance LSM_full_validator : VLSM_sign VLSM_type_full_validator :=
    { initial_state_prop := initial_state_prop
    ; initial_message_prop := initial_message_prop
    ; s0 := state0
    ; m0 := message0
    ; l0 := None
    }.

  Instance VLSM_full_validator (v : V) : VLSM LSM_full_validator :=
    { transition := vtransitionv v
      ; valid := valid_validator
    }.

  Section Validators.
  Parameter validators : list V.
  Parameter finite_validators : Listing validators.
  Parameter v0 : V.  (* non-empty set of validators *)

  Section ClientsAndValidators.

  Parameter n' : nat. (* number of clients *)
  Let n : nat := length validators.

  Lemma n_gt_0 : n > 0.
  Proof.
    destruct finite_validators as [_ Hfull].
    specialize (Hfull v0).
    destruct validators.
    - try inversion Hfull.
    - unfold n. simpl. apply lt_0_Sn.
  Qed.


  Definition IT_index : Fin.t (n + n') -> VLSM_type message :=
    fun i =>
      match proj1_sig (Fin.to_nat i) ?= n with
      | Gt => VLSM_type_full_client2
      | _ => VLSM_type_full_validator
      end.

  Definition IS_index : forall i : Fin.t (n + n'), VLSM_sign (IT_index i).
  intros. unfold IT_index.
  destruct (proj1_sig (Fin.to_nat i) ?= n) eqn:Hi.
  - exact LSM_full_validator.
  - exact LSM_full_validator.
  - exact LSM_full_client2.
  Defined.

  Definition IM_index : forall i : Fin.t (n + n'), VLSM (IS_index i).
  intros.
  unfold IT_index. unfold IS_index.
  remember (proj1_sig (Fin.to_nat i)) as ni.
  destruct (ni ?= n) eqn:Hi.
  - exact (VLSM_full_validator (nth (ni - 1) validators v0)).
  - exact (VLSM_full_validator (nth (ni - 1) validators v0)).
  - exact VLSM_full_client2.
  Defined.

  Fixpoint fin_listing (m : nat) : list (Fin.t m) :=
    match m with
      | 0 => []
      | S n => Fin.F1 :: List.map Fin.FS (fin_listing n)
    end.

  Lemma fin_finite (m : nat) : Listing (fin_listing m).
  Proof.
    induction m.
    - split; try constructor. red. inversion a.
    - destruct IHm as [Hnodup Hfull].
      split.
      + simpl. constructor.
        * intro Hin. apply in_map_iff in Hin.
          destruct Hin as [x [Hcontra Hin]]. inversion Hcontra.
        * apply Injective_map_NoDup; try assumption.
          intros x y Heq.
          apply FS_inj.
          assumption.
      + intro a. simpl. apply (caseS'  a (fun a => F1 = a \/ In a (List.map FS (fin_listing m)))).
        * left. reflexivity.
        * intro p. right.
          apply in_map. apply Hfull.
  Qed.

  Instance fin_eq_dec : EqDec (Fin.t (n + n')) := (@Fin.eq_dec (n + n')).

  Definition nlst := n + n' - 1.

  Lemma nlst_S : S nlst = n + n'.
  Proof.
    unfold nlst.
    specialize n_gt_0; intro Hn. destruct n.
    - inversion Hn.
    - simpl. f_equal. symmetry. apply minus_n_O.
  Qed.

  Definition f1_n_plus_n' : Fin.t (n + n').
  specialize (@F1 nlst). rewrite nlst_S. intro; assumption.
  Defined.

  Definition VLSM_full_composed_free : VLSM (composite_sig f1_n_plus_n' IS_index)
    := free_composite_vlsm f1_n_plus_n' IM_index.


  End ClientsAndValidators.

  Section ValidatorsOnly.
  Parameter v_eq_dec : EqDec V.

  Definition IT_validators
    (i : V)
    : VLSM_type message
    :=
    VLSM_type_full_validator
    .

  Definition IS_validators
    (i : V)
    : VLSM_sign (IT_validators i)
    :=
    LSM_full_validator
    .

  Definition IM_validators
    (i : V)
    : VLSM (IS_validators i)
    :=
    VLSM_full_validator i
    .

  Definition state_union
    (s : @state _ (composite_type IT_validators))
    : @sorted_state C V message_type
    :=
    let state_list := List.map s validators in
    fold_right CBC.FullNode.sorted_state_union (sorted_state0 C V) state_list
    .

  Existing Instance v_eq_dec.
  
  Definition VLSM_full_constraint
    (l : composite_label IT_validators)
    (som : composite_state IT_validators * option message)
    : Prop
    := 
    let (s', om') := composite_transition IM_validators l som in
    not_heavy (state_union s')
    .
  
  Definition VLSM_full_composed : VLSM (composite_sig v0 IS_validators)
    := composite_vlsm v0 IM_validators VLSM_full_constraint.

  Definition composed_union
    (s : @state _ (composite_type IT_validators))
    (i : V)
    : @sorted_state C V message_type
    :=
    state_union s
    .

  Definition indexed_union
    (s : @state _ (composite_type IT_validators))
    : list (V * message)
    := 
    flat_map (fun i => List.map (fun x => (i,x)) (get_sorted_messages (s i))) validators
    .


  End ValidatorsOnly.

  End Validators.

End CompositeFullNode.