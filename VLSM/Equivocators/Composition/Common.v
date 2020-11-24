Require Import
  List Coq.Vectors.Fin FinFun
  Arith.Compare_dec Lia
  Program
  Coq.Logic.JMeq
  .
Import ListNotations.
From CasperCBC
  Require Import
    Preamble ListExtras FinExtras FinFunExtras
    VLSM.Common VLSM.Composition VLSM.Equivocation
    VLSM.Equivocators.Common VLSM.Equivocators.Projections
    VLSM.Equivocators.MessageProperties
    .

(** ** Equivocator composition

Given a composition <<X>> of VLSMs, we can model equivocator behavior by
creating an _equivocator composition_ which replaces each component of <<X>>
with its equivocator version and strengthens the composition constraint to
allow no (additional) equivocations, that is, all messages being received
must have been previously sent by one of the (equivocator) VLSMs in the
composition.
*)

(** ** Extracting equivocator traces from equivocator composition traces
To recover the equivocator trace for the regular composition <<X>> from
the traces of the equivocator composition, we'll assume that only the
first state copy of each machine is observable in the composition
and we ignore the activity corresponding to any other state copy,
including the forks.

This amounts to removing from the trace all transitions in which the
state copy index is not 1, forgetting the additional components of
the label, and keeping only the copy of index 1 for each machine.

*)

Section fully_equivocating_composition.

Context {message : Type}
  {equiv_index nequiv_index : Type}
  (index := sum equiv_index nequiv_index)
  {IndEqDec : EqDecision index}
  (IM : index -> VLSM message)
  (Hbs : forall i : index, has_been_sent_capability (IM i))
  (i0 : index)
  (X := free_composite_vlsm IM i0)
  .

Local Instance equiv_index_eq_dec : EqDecision equiv_index.
Proof.
  intros x y.
  destruct (decide (inl x = inl y)).
  - left. inversion e. reflexivity.
  - right. intro contra. elim n. subst. reflexivity.
Qed.

Definition equivocator_IM
  (i : index)
  : VLSM message
  :=
  match i with
  | inl _ => equivocator_vlsm (IM i)
  | inr _ => (IM i)
  end.

Lemma equivocator_Hbs
  (i : index)
  :  has_been_sent_capability (equivocator_IM i).
Proof.
  unfold equivocator_IM.
  destruct i as [eqv | neqv] eqn:Hi.
  - apply equivocator_has_been_sent_capability. apply Hbs.
  - apply Hbs.
Qed.

Context
  (index_listing : list index)
  (finite_index : Listing index_listing)
  (equiv_listing := left_listing finite_index)
  (finite_equiv := left_finite finite_index)
  .

Definition equivocators_no_equivocations_constraint
  (l : composite_label equivocator_IM)
  (som : composite_state equivocator_IM * option message)
  : Prop
  :=
  no_equivocations equivocator_IM i0 (free_constraint equivocator_IM) finite_index equivocator_Hbs l som.

Definition equivocators_constrained_vlsm
  (constraint :  composite_label equivocator_IM -> composite_state equivocator_IM * option message -> Prop)
  : VLSM message
  :=
  composite_vlsm equivocator_IM i0 constraint.

Let equivocators_free_vlsm := equivocators_constrained_vlsm (free_constraint equivocator_IM).

Definition equivocators_no_equivocations_vlsm
  : VLSM message
  :=
  equivocators_constrained_vlsm equivocators_no_equivocations_constraint.

Lemma equivocators_initial_state_size
  (is : vstate equivocators_no_equivocations_vlsm)
  (His : vinitial_state_prop equivocators_no_equivocations_vlsm is)
  (eqv : equiv_index)
  : projT1 (is (inl eqv)) = 0.
Proof.
  specialize (His (inl eqv)).
  destruct His as [Hzero His].
  assumption.
Qed.

Definition equivocators_choice : Type := forall (eqv : equiv_index), MachineDescriptor (IM (inl eqv)).

Definition proper_equivocators_choice
  (eqv_choice : equivocators_choice)
  (s : vstate equivocators_free_vlsm)
  : Prop
  := forall
    (eqv : equiv_index),
    proper_descriptor (IM (inl eqv)) (eqv_choice eqv) (s (inl eqv)).

Definition not_equivocating_equivocators_choice
  (eqv_choice : equivocators_choice)
  (s : vstate equivocators_free_vlsm)
  : Prop
  := forall
    (eqv : equiv_index),
    not_equivocating_descriptor (IM (inl eqv)) (eqv_choice eqv) (s (inl eqv)).

Lemma not_equivocating_equivocators_choice_proper
  (eqv_choice : equivocators_choice)
  (s : vstate equivocators_free_vlsm)
  (Hne : not_equivocating_equivocators_choice eqv_choice s)
  : proper_equivocators_choice eqv_choice s.
Proof.
  intro eqv. apply not_equivocating_descriptor_proper. apply Hne.
Qed.

Definition zero_choice
  (eqv : equiv_index)
  : MachineDescriptor (IM (inl eqv))
  := Existing _ 0 false.

Lemma zero_choice_not_equivocating
  (s : vstate equivocators_free_vlsm)
  : not_equivocating_equivocators_choice zero_choice s.
Proof.
  intro eqv. simpl. lia.
Qed.

Lemma zero_choice_proper
  (s : vstate equivocators_free_vlsm)
  : proper_equivocators_choice zero_choice s.
Proof.
  apply not_equivocating_equivocators_choice_proper. apply zero_choice_not_equivocating.
Qed.

Lemma proper_equivocators_choice_state_update_eqv
  (eqv_choice : equivocators_choice)
  (s : vstate equivocators_free_vlsm)
  (eqv : equiv_index)
  (si : vstate (equivocator_IM (inl eqv)))
  (Hsi_proper : proper_descriptor (IM (inl eqv)) (eqv_choice eqv) (s (inl eqv)))
  (Hproper : proper_equivocators_choice eqv_choice (state_update equivocator_IM s (inl eqv) si))
  : proper_equivocators_choice eqv_choice s.
Proof.
  intro eqv'.
  specialize (Hproper eqv').
  destruct (decide (inl eqv' = inl eqv)).
  - inversion e. subst. rewrite state_update_eq in Hproper. assumption.
  - rewrite state_update_neq in Hproper; assumption.
Qed.

Lemma proper_equivocators_choice_state_update_neqv
  (eqv_choice : equivocators_choice)
  (s : vstate equivocators_free_vlsm)
  (neqv : nequiv_index)
  (si : vstate (equivocator_IM (inr neqv)))
  (Hproper : proper_equivocators_choice eqv_choice (state_update equivocator_IM s (inr neqv) si))
  : proper_equivocators_choice eqv_choice s.
Proof.
  intro eqv.
  specialize (Hproper eqv).
  destruct (decide (inl eqv = inr neqv)); try discriminate e.
  rewrite state_update_neq in Hproper; assumption.
Qed.

Definition equivocators_state_project
  (eqv_choice : equivocators_choice)
  (s : vstate equivocators_free_vlsm)
  (i : index)
  : vstate (IM i)
  :=
  let si := s i in
  match i with
  | inl eqv =>
    match (eqv_choice eqv) with
    | NewMachine _ sn => sn
    | Existing _ j _ =>
      let (n, bs) := s (inl eqv) in
      match (le_lt_dec (S n) j) with
      | right lt_in => bs (of_nat_lt lt_in)
      | left _ => bs F1
      end
    end
  | inr neqv => s (inr neqv)
  end.

Definition lift_to_equivocators_state
  (s : vstate X)
  (i : index)
  : vstate (equivocator_IM i)
  :=
  match i with
  | inl eqv => mk_singleton_state _ (s (inl eqv))
  | inr neqv => s (inr neqv)
  end.

Lemma lift_initial_to_equivocators_state
  (s : vstate X)
  (Hs : vinitial_state_prop X s)
  : vinitial_state_prop equivocators_no_equivocations_vlsm (lift_to_equivocators_state s).
Proof.
  unfold vinitial_state_prop in *. simpl in *.
  unfold composite_initial_state_prop in *.
  intro i. spec Hs i.
  destruct i as [eqv | neqv].
  - split; try assumption. reflexivity.
  - assumption.
Qed.

(**
A very useful operation on [equivocators_choice]s is updating the state corresponding
to a component:
*)
Definition equivocators_choice_update
  (s : equivocators_choice)
  (i : equiv_index)
  (si : MachineDescriptor (IM (inl i)))
  (j : equiv_index)
  : MachineDescriptor (IM (inl j))
  :=
  match decide (j = i) with
  | left e => eq_rect_r (fun i => MachineDescriptor (IM (inl i))) si e
  | _ => s j
  end.

(**
The next few results describe several properties of the [equivocators_choice_update] operation.
*)
Lemma equivocators_choice_update_neq
  (s : equivocators_choice)
  (i : equiv_index)
  (si : MachineDescriptor (IM (inl i)))
  (j : equiv_index)
  (Hneq : j <> i)
  : equivocators_choice_update s i si j = s j.
Proof.
  unfold equivocators_choice_update. destruct (decide (j = i)); try contradiction. reflexivity.
Qed.

Lemma equivocators_choice_update_eq
  (s : equivocators_choice)
  (i : equiv_index)
  (si : MachineDescriptor (IM (inl i)))
  : equivocators_choice_update s i si i = si.
Proof.
  unfold equivocators_choice_update.
  rewrite eq_dec_refl. reflexivity.
Qed.

Lemma equivocators_choice_update_id
  (s : equivocators_choice)
  (i : equiv_index)
  (si : MachineDescriptor (IM (inl i)))
  (Heq : s i = si)
  : equivocators_choice_update s i si = s.
Proof.
  apply functional_extensionality_dep_good.
  intro j.
  destruct (decide (j = i)).
  - subst. apply equivocators_choice_update_eq.
  - apply equivocators_choice_update_neq. assumption.
Qed.

Lemma equivocators_choice_update_twice
  (s : equivocators_choice)
  (i : equiv_index)
  (si si': MachineDescriptor (IM (inl i)))
  : equivocators_choice_update (equivocators_choice_update s i si) i si'
  = equivocators_choice_update s i si'.
Proof.
  apply functional_extensionality_dep_good.
  intro j.
  destruct (decide (j = i)).
  - subst. rewrite equivocators_choice_update_eq. symmetry. apply equivocators_choice_update_eq.
  - repeat rewrite equivocators_choice_update_neq; try assumption.
    reflexivity.
Qed.

Lemma equivocators_state_project_state_update_neqv
  (eqv_choice : equivocators_choice)
  (s : vstate equivocators_free_vlsm)
  (neqv : nequiv_index)
  (sneqv : vstate (equivocator_IM (inr neqv)))
  : equivocators_state_project eqv_choice (state_update equivocator_IM s (inr neqv) sneqv)
  = state_update IM (equivocators_state_project eqv_choice s) (inr neqv) sneqv.
Proof.
  apply functional_extensionality_dep.
  intro i.
  unfold equivocators_state_project.
  unfold state_update.
  destruct i as [ieqv|ineqv]
  ; match goal with
    |- context [decide ?d] => destruct (decide d)
    end; [discriminate e|reflexivity|..|reflexivity].
  inversion e. subst.
  unfold eq_rect_r.
  elim_eq_rect.
  reflexivity.
Qed.

Lemma equivocators_state_project_state_update_eqv
  (eqv_choice : equivocators_choice)
  (s : vstate equivocators_free_vlsm)
  (eqv : equiv_index)
  (seqv : vstate (equivocator_IM (inl eqv)))
  : let si :=  match eqv_choice eqv with
    | NewMachine _ sn => sn
    | Existing _ i _ =>
      match le_lt_dec (S (projT1 seqv)) i with
      | left _ => projT2 seqv F1
      | right l => projT2 seqv (of_nat_lt l)
      end
    end in
  equivocators_state_project eqv_choice (state_update equivocator_IM s (inl eqv) seqv)
  = state_update IM (equivocators_state_project eqv_choice s) (inl eqv) si.
Proof.
  apply functional_extensionality_dep.
  intro i.
  unfold equivocators_state_project.
  unfold state_update.
  destruct i as [ieqv|ineqv]
  ; match goal with
    |- context [decide ?d] => destruct (decide d)
    end; [|reflexivity|discriminate e|reflexivity].
  inversion e. subst. unfold eq_rect_r.
  elim_eq_rect. unfold eq_rect.
  destruct seqv as (n, bs).
  reflexivity.
Qed.

Lemma equivocators_initial_state_project
  (es : vstate equivocators_free_vlsm)
  (Hes : vinitial_state_prop equivocators_free_vlsm es)
  (eqv_choice : equivocators_choice)
  (Heqv : proper_equivocators_choice eqv_choice es)
  : vinitial_state_prop X (equivocators_state_project eqv_choice es).
Proof.
  intro n. specialize (Hes n).
  unfold equivocator_IM in Hes.
  unfold equivocators_state_project.
  destruct n as [eqv|neqv]; try assumption.
  specialize (Heqv eqv).
  destruct (eqv_choice eqv) as [sn | i fi]; try assumption.
  destruct Hes as [Hzero Hes].
  destruct (es (inl eqv)) as (n, bs). simpl in Heqv.
  destruct (le_lt_dec (S n) i). { lia. }
  simpl in *.
  subst. assert (Hi: i = 0) by lia. subst.
  assumption.
Qed.

Lemma equivocators_initial_message
  (m : message)
  (Hem : vinitial_message_prop equivocators_free_vlsm m)
  : vinitial_message_prop X m.
Proof.
  destruct Hem as [i [emi Hem]].
  exists i.
  unfold equivocator_IM in emi.
  destruct i as [eqv | neqv]; exists emi; assumption.
Qed.

Local Tactic Notation "unfold_transition"  hyp(H) :=
  ( unfold transition in H; unfold equivocator_vlsm in H
  ; unfold Common.equivocator_vlsm in H
  ; unfold mk_vlsm in H; unfold machine in H
  ; unfold projT2 in H; unfold equivocator_vlsm_machine in H
  ; unfold equivocator_transition in H).

Lemma equivocators_protocol_state_project
  (es : vstate equivocators_no_equivocations_vlsm)
  (om : option message)
  (Hes : protocol_prop equivocators_no_equivocations_vlsm (es, om))
  : option_protocol_message_prop X om
  /\ forall
    (eqv_choice : equivocators_choice)
    (Heqv : proper_equivocators_choice eqv_choice es),
    protocol_state_prop X (equivocators_state_project eqv_choice es).
Proof.
  generalize_eqs Hes. intro Heq; subst.
  revert om. revert es.
  induction Hes; simplify_dep_elim.
  - split.
    + exists (proj1_sig (vs0 X)). apply (protocol_initial_state X).
    + destruct is as [is His]. unfold s. simpl.
      intros.
      specialize (equivocators_initial_state_project _ His eqv_choice Heqv) as HisX.
      remember (equivocators_state_project eqv_choice is) as isX.
      replace isX with (proj1_sig (exist _ _ HisX)); try reflexivity.
      exists None.
      apply protocol_initial_state.
  - split.
    + exists (proj1_sig (vs0 X)). unfold om0. clear om0.
      destruct im as [im Him]. simpl.
      apply equivocators_initial_message in Him.
      apply (protocol_initial_message X (exist _ im Him)).
    + destruct s0 as [is His]. unfold s. simpl. clear s.
      intros.
      specialize (equivocators_initial_state_project _ His eqv_choice Heqv) as HisX.
      remember (equivocators_state_project eqv_choice is) as isX.
      replace isX with (proj1_sig (exist _ _ HisX)); try reflexivity.
      exists None.
      apply protocol_initial_state.
  - specialize (IHHes1 s _om JMeq_refl). apply proj2 in IHHes1.
    specialize (IHHes2 _s om0 JMeq_refl). apply proj1 in IHHes2.
    simpl in x.
    destruct l as (i, li).
    destruct (vtransition (equivocator_IM i) li (s i, om0)) as (si', om') eqn:Ht.
    inversion x. subst es om. clear x.
    destruct Hv as [Hv _]. simpl in Hv.
    specialize (protocol_generated X) as Hgen.
    destruct i as [ieqv | ineqv].
    * destruct li as (li, di).
      specialize (Hgen (existT _ (inl ieqv) li)) as Hgen_om'.
      simpl in Hv. unfold vvalid in Hv. simpl in Hv.
      simpl in Ht. unfold vtransition in Ht. unfold_transition Ht.
      unfold snd in Ht.
      destruct di as [sn | i fi].
      -- destruct Hv as [Hsn Hv].
        subst om0.
        inversion Ht. subst. clear Ht.
        split; try assumption.
        intros eqv_choice Heqv.
        destruct (s (inl ieqv)) as (n, bs) eqn:Hsieqv.
        destruct (eqv_choice ieqv) as [sieqv | iieqv fieqv] eqn:Hieqv.
        ++ assert (Heqvs : proper_equivocators_choice eqv_choice s).
          { intro eqv'. specialize (Heqv eqv').
            simpl in *.
            destruct (decide (inl eqv' = inl ieqv))
            ; try (rewrite state_update_neq in Heqv; assumption).
            inversion e. subst. rewrite state_update_eq in Heqv.
            rewrite Hieqv in *. simpl in Heqv. assumption.
          }
          specialize (IHHes1 _ Heqvs).
          replace
            (equivocators_state_project eqv_choice
            (state_update equivocator_IM s (inl ieqv)
               (equivocator_state_extend (IM (inl ieqv))
                  (existT (fun n0 : nat => t (S n0) -> vstate (IM (inl ieqv))) n bs)
                  sn)))
            with (equivocators_state_project eqv_choice s)
            ; try assumption.
          apply functional_extensionality_dep.
          intros [eqv'|neqv']; unfold equivocators_state_project.
          ** destruct (eqv_choice eqv') eqn:Heqv'; try reflexivity.
            destruct (decide (inl eqv' = inl ieqv)).
            --- inversion e. subst.
              rewrite state_update_eq.
              unfold equivocator_state_extend.
              rewrite Hsieqv.
              specialize (Heqvs ieqv).
              rewrite Heqv' in Heqvs. simpl in Heqvs.
              rewrite Hsieqv in Heqvs. simpl in Heqvs.
              destruct (le_lt_dec (S n) n0). { lia. }
              destruct (le_lt_dec (S (S n)) n0). { lia. }
              rewrite to_nat_of_nat.
              destruct (nat_eq_dec n0 (S n)). { lia. }
              f_equal. apply of_nat_ext.
            --- rewrite state_update_neq; try assumption. reflexivity.
          ** rewrite state_update_neq; try reflexivity.
            intro contra. discriminate contra.
        ++ specialize (Heqv ieqv) as Heqvi. unfold proper_descriptor in Heqvi.
          rewrite Hieqv in Heqvi. rewrite state_update_eq in Heqvi.
          simpl in Heqvi.
          destruct (nat_eq_dec iieqv (S n)).
          ** subst.
            pose (equivocators_choice_update eqv_choice ieqv (NewMachine _ sn)) as eqv_choice'.
            specialize (IHHes1 eqv_choice').
            spec IHHes1.
            { intro eqv'. spec Heqv eqv'.
              destruct (decide (inl eqv' = inl ieqv)).
              - inversion e. subst.
                unfold eqv_choice'.
                rewrite equivocators_choice_update_eq.
                assumption.
              - rewrite state_update_neq in Heqv; try assumption.
                unfold eqv_choice'.
                assert (n' : eqv' <> ieqv) by (intro contra; subst; elim n0; reflexivity).
                rewrite equivocators_choice_update_neq; assumption.
            }
            replace
              (equivocators_state_project eqv_choice
              (state_update equivocator_IM s (inl ieqv)
                 (equivocator_state_extend (IM (inl ieqv))
                    (existT (fun n0 : nat => t (S n0) -> vstate (IM (inl ieqv))) n bs)
                    sn)))
              with
                (equivocators_state_project eqv_choice' s)
            ; try assumption.
            apply functional_extensionality_dep.
            intro i.
            unfold equivocators_state_project at 1. unfold eqv_choice'.
            rewrite equivocators_state_project_state_update_eqv.
            destruct (decide (i = inl ieqv)).
            --- subst. repeat rewrite state_update_eq.
              rewrite equivocators_choice_update_eq.
              rewrite Hieqv. unfold equivocator_state_extend.
              unfold projT1. unfold projT2.
              destruct (le_lt_dec (S (S n)) (S n)). { lia. }
              rewrite to_nat_of_nat.
              destruct (nat_eq_dec (S n) (S n)); congruence.
            --- repeat rewrite state_update_neq; try assumption.
              unfold equivocators_state_project.
              destruct i; try reflexivity.
              rewrite equivocators_choice_update_neq ; congruence.
          ** assert (Heqvs : proper_equivocators_choice eqv_choice s).
            { intro eqv'. specialize (Heqv eqv').
              simpl in *.
              destruct (decide (inl eqv' = inl ieqv))
              ; try (rewrite state_update_neq in Heqv; assumption).
              inversion e. subst. rewrite state_update_eq in Heqv.
              rewrite Hieqv in *. simpl in Heqv. simpl.
              rewrite Hsieqv. simpl. lia.
            }
            specialize (IHHes1 _ Heqvs).
            replace
              (equivocators_state_project eqv_choice
              (state_update equivocator_IM s (inl ieqv)
                 (equivocator_state_extend (IM (inl ieqv))
                    (existT (fun n0 : nat => t (S n0) -> vstate (IM (inl ieqv))) n bs)
                    sn)))
              with (equivocators_state_project eqv_choice s)
              ; try assumption.
            apply functional_extensionality_dep.
            intros [eqv'|neqv']; unfold equivocators_state_project.
            --- destruct (eqv_choice eqv') eqn:Heqv'; try reflexivity.
              destruct (decide (inl eqv' = inl ieqv)).
              +++ inversion e. subst.
                rewrite state_update_eq.
                unfold equivocator_state_extend.
                rewrite Hsieqv.
                specialize (Heqvs ieqv).
                rewrite Heqv' in Heqvs. simpl in Heqvs.
                rewrite Hsieqv in Heqvs. simpl in Heqvs.
                destruct (le_lt_dec (S n) n1). { lia. }
                destruct (le_lt_dec (S (S n)) n1). { lia. }
                rewrite to_nat_of_nat.
                destruct (nat_eq_dec n1 (S n)). { lia. }
                f_equal. apply of_nat_ext.
              +++ rewrite state_update_neq; try assumption. reflexivity.
            --- rewrite state_update_neq; try reflexivity.
              intro contra. discriminate contra.
      -- destruct Hv as [Hi Hv].
        destruct (le_lt_dec (S (projT1 (s (inl ieqv)))) i). { lia. }
        unfold fst in Ht.
        destruct (vtransition (IM (inl ieqv)) li (projT2 (s (inl ieqv)) (of_nat_lt l), om0))
          as (sieqv', om0') eqn:Ht'.
        destruct fi eqn:Hfi; inversion Ht; subst si' om'; clear Ht.
        ++ pose
          (equivocators_choice_update
            (fun eqv => NewMachine _ (proj1_sig (vs0 (IM (inl eqv)))))
            ieqv (Existing _ i false)
          ) as eqv_choice'.
          specialize (IHHes1 eqv_choice') as Hs_om'.
          spec Hs_om'.
          { intro eqv'. unfold eqv_choice'.
            destruct (decide (eqv' = ieqv)).
            + subst. rewrite equivocators_choice_update_eq. assumption.
            + rewrite equivocators_choice_update_neq; try assumption.
              simpl. destruct (vs0 (IM (inl eqv'))). assumption.
          }
          destruct Hs_om' as [_oms Hs_om'].
          destruct IHHes2 as [_som0 Hom0].
          specialize (Hgen_om' _ _ Hs_om' _ _ Hom0).
          spec Hgen_om'.
          { split; try exact I.
            unfold free_composite_valid.
            unfold equivocators_state_project.
            unfold eqv_choice'.
            rewrite equivocators_choice_update_eq.
            destruct (s (inl ieqv)) as (nieqv, bsieqv).
            simpl in Hi.
            destruct (le_lt_dec (S nieqv) i). { lia. }
            replace (of_nat_lt l0) with (of_nat_lt Hi); try apply of_nat_ext.
            assumption.
          }
          remember (equivocators_state_project eqv_choice' s) as sp.
          simpl in Hgen_om'.
          subst sp. unfold equivocators_state_project at 1 in Hgen_om'.
          unfold eqv_choice' at 1 in Hgen_om'.
          rewrite equivocators_choice_update_eq in Hgen_om'.
          destruct (s (inl ieqv)) as (nieqv, bsieqv) eqn:Hsieqv.
          simpl in Hi.
          destruct (le_lt_dec (S nieqv) i). { lia. }
          simpl in l. simpl in Ht'.
          replace (of_nat_lt l) with (of_nat_lt Hi) in * by apply of_nat_ext.
          clear l.
          replace (of_nat_lt l0) with (of_nat_lt Hi) in * by apply of_nat_ext.
          clear l0.
          rewrite Ht' in Hgen_om'.
          split; try (eexists _; apply Hgen_om').
          intros eqv_choice Heqv.
          unfold_transition Hgen_om'.
          destruct (eqv_choice ieqv) as [sieqv | iieqv fieqv] eqn:Hieqv.
          ** assert (Heqvs : proper_equivocators_choice eqv_choice s).
            { intro eqv'. specialize (Heqv eqv').
              simpl in *.
              destruct (decide (inl eqv' = inl ieqv))
              ; try (rewrite state_update_neq in Heqv; assumption).
              inversion e. subst. rewrite state_update_eq in Heqv.
              rewrite Hieqv in *. simpl in Heqv. assumption.
            }
            specialize (IHHes1 _ Heqvs).
            replace
              (equivocators_state_project eqv_choice
              (state_update equivocator_IM s (inl ieqv)
                 (equivocator_state_extend (IM (inl ieqv))
                    (existT (fun n : nat => t (S n) -> vstate (IM (inl ieqv))) nieqv bsieqv) sieqv')))
              with (equivocators_state_project eqv_choice s)
              ; try assumption.
            apply functional_extensionality_dep.
            intros [eqv'|neqv']; unfold equivocators_state_project.
            --- destruct (eqv_choice eqv') eqn:Heqv'; try reflexivity.
              destruct (decide (inl eqv' = inl ieqv)).
              +++ inversion e. subst.
                rewrite state_update_eq.
                unfold equivocator_state_extend.
                rewrite Hsieqv.
                specialize (Heqvs ieqv).
                rewrite Heqv' in Heqvs. simpl in Heqvs.
                rewrite Hsieqv in Heqvs. simpl in Heqvs.
                destruct (le_lt_dec (S nieqv) n). { lia. }
                destruct (le_lt_dec (S (S nieqv)) n). { lia. }
                rewrite to_nat_of_nat.
                destruct (nat_eq_dec n (S nieqv)). { lia. }
                f_equal. apply of_nat_ext.
              +++ rewrite state_update_neq; try assumption. reflexivity.
            --- rewrite state_update_neq; try reflexivity.
              intro contra. discriminate contra.
          ** specialize (Heqv ieqv) as Heqvi. unfold proper_descriptor in Heqvi.
            rewrite Hieqv in Heqvi. rewrite state_update_eq in Heqvi.
            simpl in Heqvi.
            destruct (nat_eq_dec iieqv (S nieqv)).
            --- subst.
              pose (equivocators_choice_update eqv_choice ieqv (Existing _ i false)) as eqv_choice''.
              specialize (IHHes1 eqv_choice'').
              spec IHHes1.
              { intro eqv'. spec Heqv eqv'.
                destruct (decide (inl eqv' = inl ieqv)).
                - inversion e. subst.
                  unfold eqv_choice''.
                  rewrite equivocators_choice_update_eq.
                  simpl. rewrite Hsieqv.
                  assumption.
                - rewrite state_update_neq in Heqv; try assumption.
                  unfold eqv_choice''.
                  assert (n' : eqv' <> ieqv) by (intro contra; subst; elim n; reflexivity).
                  rewrite equivocators_choice_update_neq; assumption.
              }
              specialize (Hgen (existT _ (inl ieqv) li)).
              destruct IHHes1 as [_oms' Hs].
              specialize (Hgen _ _ Hs _ _ Hom0).
              spec Hgen.
              { split; try exact I.
                unfold free_composite_valid. unfold vvalid. simpl in Hv.
                replace (equivocators_state_project eqv_choice'' s (inl ieqv)) with (bsieqv (of_nat_lt Hi)); try assumption.
                unfold eqv_choice''.
                unfold equivocators_state_project.
                rewrite equivocators_choice_update_eq.
                rewrite Hsieqv.
                destruct (le_lt_dec (S nieqv) i). { lia. }
                f_equal. apply of_nat_ext.
              }
              unfold transition in Hgen.
              unfold X in Hgen at 2. unfold free_composite_vlsm in Hgen.
              unfold composite_vlsm in Hgen.
              unfold mk_vlsm in Hgen.
              unfold machine in Hgen.
              unfold projT2 in Hgen.
              unfold composite_vlsm_machine in Hgen.
              unfold composite_transition in Hgen.
              unfold equivocators_state_project at 1 in Hgen.
              unfold eqv_choice'' in Hgen.
              rewrite equivocators_choice_update_eq in Hgen.
              rewrite Hsieqv in Hgen.
              destruct (le_lt_dec (S nieqv) i). { lia. }
              replace (of_nat_lt l) with (of_nat_lt Hi) in * by apply of_nat_ext.
              rewrite Ht' in Hgen.
              exists om0'.
              replace
                (equivocators_state_project eqv_choice
                (state_update equivocator_IM s (inl ieqv)
                   (equivocator_state_extend (IM (inl ieqv))
                      (existT (fun n : nat => t (S n) -> vstate (IM (inl ieqv))) nieqv bsieqv) sieqv')))
                with (state_update IM
                (equivocators_state_project
                   (equivocators_choice_update eqv_choice ieqv (Existing (IM (inl ieqv)) i false)) s)
                (inl ieqv) sieqv')
                ; try assumption.
              apply functional_extensionality_dep.
              intro i'.
              rewrite equivocators_state_project_state_update_eqv.
              destruct (decide (i' = inl ieqv)).
              +++ subst. repeat rewrite state_update_eq.
                rewrite Hieqv. unfold equivocator_state_extend.
                unfold projT1. unfold projT2.
                destruct (le_lt_dec (S (S nieqv)) (S nieqv)). { lia. }
                rewrite to_nat_of_nat.
                destruct (nat_eq_dec (S nieqv) (S nieqv)); try (elim n; reflexivity).
                reflexivity.
              +++ repeat rewrite state_update_neq; try assumption.
                unfold equivocators_state_project.
                destruct i'; try reflexivity.
                rewrite equivocators_choice_update_neq
                ; try (intro contra; subst; elim n; reflexivity).
                reflexivity.
            --- assert (Heqvs : proper_equivocators_choice eqv_choice s).
              { intro eqv'. specialize (Heqv eqv').
                simpl in *.
                destruct (decide (inl eqv' = inl ieqv))
                ; try (rewrite state_update_neq in Heqv; assumption).
                inversion e. subst. rewrite state_update_eq in Heqv.
                rewrite Hieqv in *. simpl in Heqv. simpl.
                rewrite Hsieqv. simpl. lia.
              }
              specialize (IHHes1 _ Heqvs).
              replace
                (equivocators_state_project eqv_choice
                (state_update equivocator_IM s (inl ieqv)
                   (equivocator_state_extend (IM (inl ieqv))
                      (existT (fun n0 : nat => t (S n0) -> vstate (IM (inl ieqv))) nieqv bsieqv) sieqv')))
                with (equivocators_state_project eqv_choice s)
                ; try assumption.
              apply functional_extensionality_dep.
              intros [eqv'|neqv']; unfold equivocators_state_project.
              +++ destruct (eqv_choice eqv') eqn:Heqv'; try reflexivity.
                destruct (decide (inl eqv' = inl ieqv)).
                *** inversion e. subst.
                  rewrite state_update_eq.
                  unfold equivocator_state_extend.
                  rewrite Hsieqv.
                  specialize (Heqvs ieqv).
                  rewrite Heqv' in Heqvs. simpl in Heqvs.
                  rewrite Hsieqv in Heqvs. simpl in Heqvs.
                  destruct (le_lt_dec (S nieqv) n0). { lia. }
                  destruct (le_lt_dec (S (S nieqv)) n0). { lia. }
                  rewrite to_nat_of_nat.
                  destruct (nat_eq_dec n0 (S nieqv)). { lia. }
                  f_equal. apply of_nat_ext.
                *** rewrite state_update_neq; try assumption. reflexivity.
              +++ rewrite state_update_neq; try reflexivity.
                intro contra. discriminate contra.
        ++ pose
          (equivocators_choice_update
            (fun eqv => NewMachine _ (proj1_sig (vs0 (IM (inl eqv)))))
            ieqv (Existing _ i false)
          ) as eqv_choice'.
          specialize (IHHes1 eqv_choice') as Hs_om'.
          spec Hs_om'.
          { intro eqv'. unfold eqv_choice'.
            destruct (decide (eqv' = ieqv)).
            + subst. rewrite equivocators_choice_update_eq. assumption.
            + rewrite equivocators_choice_update_neq; try assumption.
              simpl. destruct (vs0 (IM (inl eqv'))). assumption.
          }
          destruct Hs_om' as [_oms Hs_om'].
          destruct IHHes2 as [_som0 Hom0].
          specialize (Hgen_om' _ _ Hs_om' _ _ Hom0).
          spec Hgen_om'.
          { split; try exact I.
            unfold free_composite_valid.
            unfold equivocators_state_project.
            unfold eqv_choice'.
            rewrite equivocators_choice_update_eq.
            destruct (s (inl ieqv)) as (nieqv, bsieqv).
            simpl in Hi.
            destruct (le_lt_dec (S nieqv) i). { lia. }
            replace (of_nat_lt l0) with (of_nat_lt Hi); try apply of_nat_ext.
            assumption.
          }
          remember (equivocators_state_project eqv_choice' s) as sp.
          simpl in Hgen_om'.
          subst sp. unfold equivocators_state_project at 1 in Hgen_om'.
          unfold eqv_choice' at 1 in Hgen_om'.
          rewrite equivocators_choice_update_eq in Hgen_om'.
          destruct (s (inl ieqv)) as (nieqv, bsieqv) eqn:Hsieqv.
          simpl in Hi.
          destruct (le_lt_dec (S nieqv) i). { lia. }
          simpl in Ht'.
          replace (of_nat_lt l0) with (of_nat_lt Hi) in * by apply of_nat_ext.
          clear l0.
          simpl in l.
          replace (of_nat_lt l) with (of_nat_lt Hi) in * by apply of_nat_ext.
          rewrite Ht' in Hgen_om'.
          split; try (eexists _; apply Hgen_om').
          intros eqv_choice Heqv.
          destruct (eqv_choice ieqv) as [sieqv | iieqv fieqv] eqn:Hieqv.
          ** assert (Heqvs : proper_equivocators_choice eqv_choice s).
            { intro eqv'. specialize (Heqv eqv').
              simpl in *.
              destruct (decide (inl eqv' = inl ieqv))
              ; try (rewrite state_update_neq in Heqv; assumption).
              inversion e. subst. rewrite state_update_eq in Heqv.
              rewrite Hieqv in *. simpl in Heqv. assumption.
            }
            specialize (IHHes1 _ Heqvs).
            replace
              (equivocators_state_project eqv_choice
              (state_update equivocator_IM s (inl ieqv)
                 (equivocator_state_update (IM (inl ieqv))
                    (existT (fun n : nat => t (S n) -> vstate (IM (inl ieqv))) nieqv bsieqv)
                    (of_nat_lt l) sieqv')))
              with (equivocators_state_project eqv_choice s)
              ; try assumption.
            apply functional_extensionality_dep.
            intros [eqv'|neqv']; unfold equivocators_state_project.
            --- destruct (eqv_choice eqv') eqn:Heqv'; try reflexivity.
              destruct (decide (inl eqv' = inl ieqv)).
              +++ inversion e. subst.
                rewrite Hieqv in Heqv'. discriminate Heqv'.
              +++ rewrite state_update_neq; try assumption. reflexivity.
            --- rewrite state_update_neq; try reflexivity.
              intro contra. discriminate contra.
          ** specialize (Heqv ieqv) as Heqvi. unfold proper_descriptor in Heqvi.
            rewrite Hieqv in Heqvi. rewrite state_update_eq in Heqvi.
            simpl in Heqvi.
            destruct (nat_eq_dec iieqv i).
            --- subst.
              pose (equivocators_choice_update eqv_choice ieqv (Existing _ i false)) as eqv_choice''.
              specialize (IHHes1 eqv_choice'').
              spec IHHes1.
              { intro eqv'. spec Heqv eqv'.
                destruct (decide (inl eqv' = inl ieqv)).
                - inversion e. subst.
                  unfold eqv_choice''.
                  rewrite equivocators_choice_update_eq.
                  simpl. rewrite Hsieqv.
                  assumption.
                - rewrite state_update_neq in Heqv; try assumption.
                  unfold eqv_choice''.
                  assert (n' : eqv' <> ieqv) by (intro contra; subst; elim n; reflexivity).
                  rewrite equivocators_choice_update_neq; assumption.
              }
              specialize (Hgen (existT _ (inl ieqv) li)).
              destruct IHHes1 as [_oms' Hs].
              specialize (Hgen _ _ Hs _ _ Hom0).
              spec Hgen.
              { split; try exact I.
                unfold free_composite_valid. unfold vvalid. simpl in Hv.
                replace (equivocators_state_project eqv_choice'' s (inl ieqv)) with (bsieqv (of_nat_lt Hi)); try assumption.
                unfold eqv_choice''.
                unfold equivocators_state_project.
                rewrite equivocators_choice_update_eq.
                rewrite Hsieqv.
                destruct (le_lt_dec (S nieqv) i). { lia. }
                f_equal. apply of_nat_ext.
              }
              unfold transition in Hgen.
              unfold X in Hgen at 2. unfold free_composite_vlsm in Hgen.
              unfold composite_vlsm in Hgen.
              unfold mk_vlsm in Hgen.
              unfold machine in Hgen.
              unfold projT2 in Hgen.
              unfold composite_vlsm_machine in Hgen.
              unfold composite_transition in Hgen.
              unfold equivocators_state_project at 1 in Hgen.
              unfold eqv_choice'' in Hgen.
              rewrite equivocators_choice_update_eq in Hgen.
              rewrite Hsieqv in Hgen.
              destruct (le_lt_dec (S nieqv) i). { lia. }
              replace (of_nat_lt l0) with (of_nat_lt Hi) in * by apply of_nat_ext.
              rewrite Ht' in Hgen.
              exists om0'.
              replace
                (equivocators_state_project eqv_choice
                (state_update equivocator_IM s (inl ieqv)
                   (equivocator_state_update (IM (inl ieqv))
                      (existT (fun n : nat => t (S n) -> vstate (IM (inl ieqv))) nieqv bsieqv)
                      (of_nat_lt l) sieqv')))
                with (state_update IM
                (equivocators_state_project
                   (equivocators_choice_update eqv_choice ieqv (Existing (IM (inl ieqv)) i false)) s)
                (inl ieqv) sieqv')
                ; try assumption.
              apply functional_extensionality_dep.
              intro i'.
              rewrite equivocators_state_project_state_update_eqv.
              destruct (decide (i' = inl ieqv)).
              +++ subst. repeat rewrite state_update_eq.
                rewrite Hieqv. unfold equivocator_state_update at 1.
                unfold projT1.
                destruct (le_lt_dec (S nieqv) i). { lia. }
                unfold equivocator_state_update. unfold projT2.
                rewrite eq_dec_if_true; try reflexivity.
                apply of_nat_ext.
              +++ repeat rewrite state_update_neq; try assumption.
                unfold equivocators_state_project.
                destruct i'; try reflexivity.
                rewrite equivocators_choice_update_neq
                ; try (intro contra; subst; elim n; reflexivity).
                reflexivity.
            --- assert (Heqvs : proper_equivocators_choice eqv_choice s).
              { intro eqv'. specialize (Heqv eqv').
                simpl in *.
                destruct (decide (inl eqv' = inl ieqv))
                ; try (rewrite state_update_neq in Heqv; assumption).
                inversion e. subst. rewrite state_update_eq in Heqv.
                rewrite Hieqv in *. simpl in Heqv. simpl.
                rewrite Hsieqv. simpl. lia.
              }
              specialize (IHHes1 _ Heqvs).
              replace
                (equivocators_state_project eqv_choice
                (state_update equivocator_IM s (inl ieqv)
                   (equivocator_state_update (IM (inl ieqv))
                      (existT (fun n0 : nat => t (S n0) -> vstate (IM (inl ieqv))) nieqv bsieqv)
                      (of_nat_lt l) sieqv')))
                with (equivocators_state_project eqv_choice s)
                ; try assumption.
              apply functional_extensionality_dep.
              intros [eqv'|neqv']; unfold equivocators_state_project.
              +++ destruct (eqv_choice eqv') eqn:Heqv'; try reflexivity.
                destruct (decide (inl eqv' = inl ieqv)).
                *** inversion e. subst.
                  rewrite state_update_eq.
                  unfold equivocator_state_extend.
                  rewrite Hsieqv.
                  specialize (Heqvs ieqv).
                  rewrite Heqv' in Heqvs. simpl in Heqvs.
                  rewrite Hsieqv in Heqvs. simpl in Heqvs.
                  destruct (le_lt_dec (S nieqv) n0). { lia. }
                  destruct (le_lt_dec (S (S nieqv)) n0). { lia. }
                  unfold equivocator_state_update.
                  unfold projT1.
                  destruct (le_lt_dec (S nieqv) n0). { lia. }
                  rewrite Hieqv in Heqv'.
                  inversion Heqv'. subst n0 b. clear Heqv'.
                  unfold projT2.
                  rewrite eq_dec_if_false; try (f_equal; apply of_nat_ext).
                  intro contra. elim n.
                  apply (f_equal to_nat) in contra.
                  repeat rewrite to_nat_of_nat in contra.
                  inversion contra. reflexivity.
                *** rewrite state_update_neq; try assumption. reflexivity.
              +++ rewrite state_update_neq; try reflexivity.
                intro contra. discriminate contra.
    * specialize (Hgen (existT _ (inr ineqv) li)).
      unfold vvalid in Hv. simpl in Hv.
      unfold vtransition in Ht. simpl in Ht.
      pose (fun eqv => NewMachine _ (proj1_sig (vs0 (IM (inl eqv))))) as eqv_choice.
      specialize (IHHes1 eqv_choice) as Hs_om'.
      spec Hs_om'.
      { intro eqv'. unfold eqv_choice.
        simpl. destruct (vs0 (IM (inl eqv'))). assumption.
      }
      destruct Hs_om' as [_oms Hs_om'].
      destruct IHHes2 as [_som0 Hom0].
      specialize (Hgen _ _ Hs_om' _ _ Hom0) as Hgen_om'.
      spec Hgen_om'. { split; try exact I. assumption. }
      remember (equivocators_state_project eqv_choice s) as sp.
      simpl in Hgen_om'.
      unfold vtransition in Hgen_om'.
      subst sp. unfold equivocators_state_project at 1 in Hgen_om'.
      rewrite Ht in Hgen_om'.
      split; try (eexists _; apply Hgen_om').
      clear eqv_choice Hgen_om' Hs_om'.
      intros eqv_choice Heqv.
      assert (Heqvs : proper_equivocators_choice eqv_choice s).
      { intro eqv'. specialize (Heqv eqv').
        rewrite state_update_neq in Heqv; congruence.
      }
      specialize (IHHes1 _ Heqvs).
      destruct IHHes1 as [_oms' Hs].
      specialize (Hgen _ _ Hs _ _ Hom0).
      spec Hgen. { split; try exact I. assumption. }
      unfold transition in Hgen.
      unfold X in Hgen at 2. unfold free_composite_vlsm in Hgen.
      unfold composite_vlsm in Hgen.
      unfold mk_vlsm in Hgen.
      unfold machine in Hgen.
      unfold projT2 in Hgen.
      unfold composite_vlsm_machine in Hgen.
      unfold composite_transition in Hgen.
      unfold equivocators_state_project at 1 in Hgen.
      unfold vtransition in Hgen. rewrite Ht in Hgen.
      exists om'.
      rewrite equivocators_state_project_state_update_neqv.
      assumption.
Qed.

End fully_equivocating_composition.
