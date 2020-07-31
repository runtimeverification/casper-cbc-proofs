Require Import
  Bool
  List
  ListSet
  Reals
  FinFun
  Fin
  RelationClasses
  .

Import ListNotations.

From CasperCBC
  Require Import
    Lib.Preamble
    Lib.ListExtras
    Lib.ListSetExtras
    Lib.RealsExtras
    CBC.Common
    VLSM.Common
    VLSM.Composition
    VLSM.Decisions
    Validator.State
    Validator.Equivocation
    PreceedsEquivocation
    CBC.Equivocation
    .

Section CompositeFullNode.

  Context
    {C V : Type}
    {about_C : StrictlyComparable C}
    {about_V : StrictlyComparable V}
    {Hmeasurable : Measurable V}
    {Hrt : ReachableThreshold V}
    {Hestimator : Estimator (state C V) C}
    .

  Definition reach (s1 s2 : state C V) : Prop :=
    incl (fst s1) (fst s2).

  Definition message : Type := State.message C V.

  (* 2.5.1 Minimal full client protocol: Client2 *)
  Definition label2 : Type := unit.

  Definition vtransition2
    (l : unit)
    (sm : state C V * option message)
    : state C V * option message
    :=
    let (s, om) := sm in
    let (msgs, final) := s in
    match om with
    | None => pair s None
    | Some msg => pair (pair (set_add compare_eq_dec msg msgs) final)  None
    end.

  Definition not_heavy
    :=
    @CBC.Equivocation.set_not_heavy _ (full_node_equivocation C V ).

  Definition valid_client2
    (_ : unit)
    (som : state C V * option message)
    :=
    let (s, om) := som in
    match om with
    | None => True
    | Some msg =>
      reach (unmake_justification (get_justification msg)) s
      /\ not_heavy (set_add compare_eq_dec msg (fst s))
    end.

  Instance VLSM_type_full_client2 : VLSM_type message :=
    { state := state C V
    ; label := label2
    }.

  Definition initial_state_prop
    (s : state C V)
    : Prop
    :=
    s = pair [] None.

  Definition state0 : {s | initial_state_prop s} :=
    exist _ (pair [] None) eq_refl.

  Definition initial_message_prop (m : message) : Prop := False.

  Instance LSM_full_client2 : VLSM_sign VLSM_type_full_client2 :=
    { initial_state_prop := initial_state_prop
    ; initial_message_prop := initial_message_prop
    ; s0 := state0
    ; m0 := State.message0
    ; l0 := tt
    }.

  Instance VLSM_full_client2  : VLSM LSM_full_client2 :=
    { transition := vtransition2
      ; valid := valid_client2
    }.

  (* Section 2.5.2  Minimal full validator protocol for name v: Validator(v) *)
  Definition labelv : Type := option C.

  Definition vtransitionv
    (v : V)
    (l : labelv)
    (som : state C V * option message)
    : state C V * option message
    :=
    let (s, om) := som in
    let (msgs, final) := s in
    match l with
    | None => match om with
             | None => som
             | Some msg => pair (pair (set_add compare_eq_dec msg msgs) final) None
           end
    | Some c =>
      let msg := (c, v, make_justification s) in
      pair (pair (set_add compare_eq_dec msg msgs) (Some msg)) (Some msg)
    end.

  Definition valid_validator
    (l : labelv)
    (som : state C V * option message)
    : Prop
    :=
    let (s, om) := som in
    match l, om with
    | None, None => True
    | None, Some msg =>
      reach (unmake_justification (get_justification msg)) s
    | Some c, _ =>
      @estimator (state C V) C Hestimator s c
    end.

  Instance VLSM_type_full_validator : VLSM_type message :=
    { state := state C V
    ; label := labelv
    }.

  Instance LSM_full_validator : VLSM_sign VLSM_type_full_validator :=
    { initial_state_prop := initial_state_prop
    ; initial_message_prop := initial_message_prop
    ; s0 := state0
    ; m0 := State.message0
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
  Proof.
    intros. unfold IT_index.
    destruct (proj1_sig (Fin.to_nat i) ?= n) eqn:Hi.
    - exact LSM_full_validator.
    - exact LSM_full_validator.
    - exact LSM_full_client2.
  Defined.

  Definition IM_index : forall i : Fin.t (n + n'), VLSM (IS_index i).
  Proof.
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

  Instance fin_eq_dec : EqDec (Fin.t (n + n')) := @Fin.eq_dec (n + n').

  Definition nlst := n + n' - 1.

  Lemma nlst_S : S nlst = n + n'.
  Proof.
    unfold nlst.
    specialize n_gt_0; intro Hn. destruct n.
    - inversion Hn.
    - simpl. f_equal. symmetry. apply minus_n_O.
  Qed.

  Definition f1_n_plus_n' : Fin.t (n + n').
  Proof.
    specialize (@F1 nlst). rewrite nlst_S. intro; assumption.
  Defined.

  Definition VLSM_full_composed_free : VLSM (composite_sig f1_n_plus_n' IS_index)
    := free_composite_vlsm f1_n_plus_n' IM_index.


  End ClientsAndValidators.

  Section ValidatorsOnly.
  Parameter v_eq_dec : EqDec V.

  Existing Instance v_eq_dec.

  Definition IT_validators
    (i : V)
    : VLSM_type message
    :=
    VLSM_type_full_validator.

  Definition IS_validators
    (i : V)
    : VLSM_sign (IT_validators i)
    :=
    LSM_full_validator.

  Definition IM_validators
    (i : V)
    : VLSM (IS_validators i)
    :=
    VLSM_full_validator i.

  Section validators_free_composition.

  Definition validators_free_composition : VLSM (composite_sig v0 IS_validators)
    := free_composite_vlsm v0 IM_validators.

  Definition  free_validator_byzantine_message_preceeds
    (pm1 pm2 : byzantine_message validators_free_composition)
    : Prop
    := validator_message_preceeds _ _ (proj1_sig pm1) (proj1_sig pm2).

  Lemma free_validator_byzantine_message_preceeds_irreflexive
    : Irreflexive free_validator_byzantine_message_preceeds.
  Proof.
    intros (x, Hx).
    unfold complement; unfold free_validator_byzantine_message_preceeds; simpl.
    apply validator_message_preceeds_irreflexive.
  Qed.

  Lemma free_byzantine_message_justification
    (m : message)
    (Hm : byzantine_message_prop validators_free_composition m)
    (j := get_justification m)
    : exists
      (s : @VLSM.Common.state _ (composite_type IT_validators))
      (Hs : protocol_state_prop (pre_loaded_vlsm validators_free_composition) s)
      (v : V),
      make_justification (s v) = j.
  Proof.
    destruct Hm as [(s0, om0) [l [s [[[_om0 Hs0] [[_s0 Hom0] Hv]] Ht]]]].
    exists s0.
    assert (Hpsp : protocol_state_prop (pre_loaded_vlsm validators_free_composition) s0)
      by (exists _om0; assumption).
    exists Hpsp.
    simpl in Ht.
    destruct l as (v, lv).
    exists v.
    destruct (s0 v) as (msgs, final) eqn: Hsv.
    destruct lv as [c|].
    + apply pair_equal_spec in Ht. destruct Ht as [Hs Hom]; subst.
      unfold j.
      replace m with ((c, v, make_justification (msgs, final)))
      ; try reflexivity.
      inversion Hom; reflexivity.
    + destruct om0; inversion Ht.
  Qed.

  Lemma in_free_byzantine_state_justification
    (s : @VLSM.Common.state _ (composite_type IT_validators))
    (Hs : protocol_state_prop (pre_loaded_vlsm validators_free_composition) s)
    (m : message)
    (v : V)
    (Hm : In m (fst (s v)))
    : incl (fst (unmake_justification (get_justification m))) (fst (s v)).
  Proof.
    destruct  Hs as [om Hsom].
    remember (s, om) as som.
    generalize dependent v.
    generalize dependent m.
    generalize dependent om.
    generalize dependent s.
    induction Hsom; intros; inversion Heqsom; subst; clear Heqsom.
    - unfold s in *; clear s. destruct is as [is His]. simpl in *.
      specialize (His v).
      inversion His.
      rewrite H0 in Hm.
      inversion H0.
      inversion Hm.
    - unfold s in *; clear s. destruct s0 as [is His]. simpl in *.
      specialize (His v).
      inversion His.
      rewrite H0 in Hm.
      inversion H0.
      inversion Hm.
    - destruct l as (v', lv').
      destruct (s v') as (msgsv', finalv') eqn:Hsv'.
      destruct lv' as [c|].
      + apply pair_equal_spec in H0. destruct H0 as [Hs Hom]; subst.
        destruct (eq_dec v v'); subst.
        * rewrite state_update_eq in *.
          apply set_add_iff in Hm.
          { destruct Hm as [Heqm | Hinm]; subst.
          - specialize (make_unmake_message_set_eq msgsv'); intros [Hincl _].
            simpl. destruct finalv'; simpl
            ; apply incl_tran with msgsv'; try assumption
            ; intros x Hx; rewrite set_add_iff
            ; right; assumption
            .
          - specialize (IHHsom1  s _om eq_refl m v').
            rewrite Hsv' in IHHsom1.
            specialize (IHHsom1 Hinm).
            apply incl_tran with msgsv'; try assumption.
            intros x Hx. simpl. rewrite set_add_iff.
            right; assumption.
          }
        * rewrite state_update_neq in Hm; try assumption.
          rewrite state_update_neq; try assumption.
          specialize (IHHsom1  s _om eq_refl m v).
          apply IHHsom1.
          assumption.
      + destruct om as [m'|].
        * apply pair_equal_spec in H0.  destruct H0 as [Hs Hom]; subst.
          { destruct (eq_dec v v'); subst.
          - rewrite state_update_eq in Hm. rewrite state_update_eq.
            apply set_add_iff in Hm.
            destruct Hm as [Heqm | Hinm]; subst.
            + destruct Hv as [Hv _]. simpl in Hv.
              rewrite Hsv' in Hv.
              apply incl_tran with msgsv'; try assumption.
              intros x Hx. simpl. rewrite set_add_iff.
              right; assumption.
            + specialize (IHHsom1  s _om eq_refl m v').
              rewrite Hsv' in IHHsom1; simpl in IHHsom1.
              specialize (IHHsom1 Hinm).
              apply incl_tran with msgsv'; try assumption.
              intros x Hx. simpl. rewrite set_add_iff.
              right; assumption.
          - rewrite state_update_neq in Hm; try assumption.
            rewrite state_update_neq; try assumption.
            apply (IHHsom1  s _om eq_refl m v).
            assumption.
          }
        * apply pair_equal_spec in H0.  destruct H0 as [Hs Hom]; subst.
          rewrite state_update_id in Hm; try assumption.
          rewrite state_update_id; try assumption.
          apply (IHHsom1  s _om eq_refl m v).
          assumption.
  Qed.

  Lemma free_validator_byzantine_message_preceeds_justification_incl
    (y z : byzantine_message validators_free_composition)
    (Hyz : free_validator_byzantine_message_preceeds y z)
    (jy := get_justification (proj1_sig y))
    (jz := get_justification (proj1_sig z))
    : justification_incl jy jz.
  Proof.
    unfold jy; clear jy. unfold jz; clear jz.
    destruct y as (y, Hy).
    destruct z as (z, Hz).
    unfold free_validator_byzantine_message_preceeds in Hyz.
    simpl in *.
    specialize (free_byzantine_message_justification z Hz); intros [jz [Hpjz [v Hjz]]].
    unfold validator_message_preceeds in Hyz.
    destruct z as (cz, vz, jz'); simpl in Hyz.
    simpl in Hjz; subst.
    specialize
      (in_correct
        (unmake_message_set (get_message_set (make_justification (jz v))))
        y
      ); intro Hin_in
    ; apply proj2 in Hin_in
    ; apply Hin_in in Hyz; clear Hin_in.
    apply in_unmake_message_set in Hyz.
    apply in_make_justification in Hyz.
    specialize (in_free_byzantine_state_justification jz Hpjz y v Hyz)
    ; intro Hincljyjz.
    simpl.
    intros m Hm.
    apply in_make_justification.
    apply Hincljyjz.
    apply in_unmake_justification.
    assumption.
  Qed.

  Lemma free_validator_byzantine_message_preceeds_transitive
    : Transitive free_validator_byzantine_message_preceeds.
  Proof.
    intros x y z Hxy Hyz.
    specialize
      (free_validator_byzantine_message_preceeds_justification_incl
        y z Hyz
      ); simpl; intro Hinclyz.
    destruct x as ((cx, vx, jx), Hx).
    destruct y as ((cy, vy, jy), Hy).
    destruct z as ((cz, vz, jz), Hz).
    unfold free_validator_byzantine_message_preceeds in *; simpl in *.
    unfold validator_message_preceeds in *.
    unfold validator_message_preceeds_fn in *.
    specialize
      (in_correct
        (fst (unmake_justification jy))
        ((cx, vx, jx))
      ); intro Hin_in
    ; apply proj2 in Hin_in
    ; apply Hin_in in Hxy; clear Hin_in.
    apply in_unmake_justification in Hxy.
    apply Hinclyz in Hxy.
    specialize
      (in_correct
        (fst (unmake_justification jz))
        ((cx, vx, jx))
      ); intro Hin_in
    ; apply proj1 in Hin_in
    ; apply Hin_in; clear Hin_in.
    apply in_unmake_justification.
    assumption.
  Qed.

  Definition free_validator_byzantine_message_preceeds_stict_order
    : StrictOrder free_validator_byzantine_message_preceeds.
  Proof.
    split.
    apply free_validator_byzantine_message_preceeds_irreflexive.
    apply free_validator_byzantine_message_preceeds_transitive.
  Defined.

  Global Instance validators_free_composition_preceeds_equivocation
    : HasPreceedsEquivocation validators_free_composition.
  Proof.
    split.
    apply free_validator_byzantine_message_preceeds_stict_order.
  Defined.

  End validators_free_composition.

  Definition state_union
    (s : @VLSM.Common.state _ (composite_type IT_validators))
    : set message
    :=
    let state_list := List.map s validators in
    fold_right (set_union compare_eq_dec) []
      (List.map fst state_list).

  Definition validators_composition_constraint
    (l : composite_label IT_validators)
    (som : composite_state IT_validators * option message)
    : Prop
    :=
    let (s', om') := composite_transition IM_validators l som in
    not_heavy (state_union s').

  Definition validators_constrained_composition : VLSM (composite_sig v0 IS_validators)
    := composite_vlsm v0 IM_validators validators_composition_constraint.

  Global Instance validators_constrained_composition_preceeds_equivocation
    : HasPreceedsEquivocation validators_constrained_composition.
  Proof.
    apply
      (preceeds_equivocation_constrained
        v0 IM_validators validators_composition_constraint free_constraint
      ).
    - intro l; intros. exact I.
    - apply validators_free_composition_preceeds_equivocation.
  Qed.

  Lemma in_protocol_state
    (s : @VLSM.Common.state _ (composite_type IT_validators))
    (Hs : protocol_state_prop validators_constrained_composition s)
    (m : message)
    (v : V)
    (Hm : In m (fst (s v)))
    : protocol_message_prop validators_constrained_composition m.
  Proof.
    destruct  Hs as [om Hsom].
    remember (s, om) as som.
    generalize dependent v.
    generalize dependent m.
    generalize dependent om.
    generalize dependent s.
    induction Hsom; intros; inversion Heqsom; subst; clear Heqsom.
    - unfold s in *; clear s. destruct is as [is His]. simpl in *.
      specialize (His v).
      inversion His.
      rewrite H0 in Hm.
      inversion H0.
      inversion Hm.
    - unfold s in *; clear s. destruct s0 as [is His]. simpl in *.
      specialize (His v).
      inversion His.
      rewrite H0 in Hm.
      inversion H0.
      inversion Hm.
    - assert (Hpsom0 : option_protocol_message_prop validators_constrained_composition om0).
      { exists s0. replace (s0, om0) with (@transition _ _ _ validators_constrained_composition l (s, om)).
        apply protocol_generated with _om _s; assumption.
      }
      destruct l as (v', lv').
      destruct (s v') as (msgsv', finalv') eqn:Hsv'.
      destruct lv' as [c|].
      + apply pair_equal_spec in H0. destruct H0 as [Hs Hom]; subst.
        destruct (eq_dec v v'); subst.
        * rewrite state_update_eq in Hm.
          apply set_add_iff in Hm.
          destruct Hm as [Heqm | Hinm]; subst; try assumption.
          apply (IHHsom1  s _om eq_refl m v').
          rewrite Hsv'. assumption.
        * rewrite state_update_neq in Hm; try assumption.
          apply (IHHsom1  s _om eq_refl m v).
          assumption.
      + destruct om as [m'|].
        * apply pair_equal_spec in H0.  destruct H0 as [Hs Hom]; subst.
          { destruct (eq_dec v v'); subst.
          - rewrite state_update_eq in Hm.
            apply set_add_iff in Hm.
            destruct Hm as [Heqm | Hinm]; subst.
            + exists _s. assumption.
            + apply (IHHsom1  s _om eq_refl m v').
              rewrite Hsv'. assumption.
          - rewrite state_update_neq in Hm; try assumption.
            apply (IHHsom1  s _om eq_refl m v).
            assumption.
          }
        * apply pair_equal_spec in H0.  destruct H0 as [Hs Hom]; subst.
          rewrite state_update_id in Hm; try assumption.
          apply (IHHsom1  s _om eq_refl m v).
          assumption.
  Qed.

  Lemma state_union_protocol_message
    (s : @VLSM.Common.state _ (composite_type IT_validators))
    (Hs : protocol_state_prop validators_constrained_composition s)
    : Forall (protocol_message_prop validators_constrained_composition) (state_union s).
  Proof.
    apply Forall_forall.
    intros m Hm.
    apply set_union_in_iterated in Hm.
    apply Exists_exists in Hm.
    destruct Hm as [msgv [Hinv Hinsv]].
    apply in_map_iff in Hinv.
    destruct Hinv as [sv [Heq Hinv]]; subst.
    apply in_map_iff in Hinv.
    destruct Hinv as [v [Heq Hinv]]; subst.
    apply in_protocol_state with s v; assumption.
  Qed.

  Lemma state_union_byzantine_message
    (s : @VLSM.Common.state _ (composite_type IT_validators))
    (Hs : protocol_state_prop validators_constrained_composition s)
    : Forall (byzantine_message_prop validators_constrained_composition) (state_union s).
  Proof.
    apply state_union_protocol_message in Hs.
    rewrite Forall_forall in *.
    intros m Hm.
    specialize (Hs m Hm). clear -Hs.
    apply can_emit_protocol_iff in Hs.
    destruct Hs as [[v [[miv Hmiv] _]] | Hem]; try inversion Hmiv.
    apply pre_loaded_can_emit.
    assumption.
  Qed.

  Definition composed_union
    (s : @VLSM.Common.state _ (composite_type IT_validators))
    (i : V)
    : @VLSM.Common.state _ (IT_validators i)
    :=
    let (_, last) := s i in
    pair (state_union s) last.

  Definition union_state
    (s : @VLSM.Common.state _ (composite_type IT_validators))
    : @VLSM.Common.state _ (composite_type IT_validators)
    :=
    composed_union s.

  End ValidatorsOnly.

  End Validators.

End CompositeFullNode.