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
  {equiv_index : Type}
  (index := equiv_index)
  {IndEqDec : EqDecision index}
  (IM : index -> VLSM message)
  (Hbs : forall i : index, has_been_sent_capability (IM i))
  {i0 : Inhabited index}
  (X := free_composite_vlsm IM)
  .

Definition equivocator_IM
  (i : index)
  : VLSM message
  :=
  equivocator_vlsm (IM i).

Lemma equivocator_Hbs
  (i : index)
  :  has_been_sent_capability (equivocator_IM i).
Proof.
  unfold equivocator_IM.
  apply equivocator_has_been_sent_capability. apply Hbs.
Qed.

Existing Instance is_equivocating_state_dec.

Definition equivocating_indices
  (index_listing : list index)
  (s : composite_state equivocator_IM)
  : list index
  :=
  filter (fun i => bool_decide (is_equivocating_state (IM i) (s i))) index_listing.

(**
The statement below is obvious a transition cannot make an already equivocating
component non-equivocating.
*)
Lemma equivocators_transition_preserves_equivocating_indices
  (index_listing : list index)
  (s: composite_state equivocator_IM)
  (iom oom: option message)
  (l: _composite_label equivocator_IM)
  (s0: composite_state equivocator_IM)
  (Ht: composite_transition equivocator_IM l (s0, iom) = (s, oom))
  : incl (equivocating_indices index_listing s0) (equivocating_indices index_listing s).
Proof.
  intros i Hi.
  apply filter_In. apply filter_In in Hi.
  split; [apply Hi|]. destruct Hi as [_ Hi].
  apply bool_decide_eq_true. apply bool_decide_eq_true in Hi.
  intro Hsi. elim Hi. clear Hi. unfold is_singleton_state in *.
  simpl in *.
  destruct l as (j, lj).
  destruct (vtransition (equivocator_IM j) lj (s0 j, iom)) as (sj', om') eqn:Htj.
  inversion Ht. subst. clear Ht.
  destruct (decide (i = j)); [|rewrite state_update_neq in Hsi; assumption].
  subst. rewrite state_update_eq in Hsi.
  revert Hsi. apply equivocator_transition_reflects_singleton_state with iom oom lj.
  assumption.
Qed.

Context
  {index_listing : list index}
  (finite_index : Listing index_listing)
  (equivocators_free_vlsm := free_composite_vlsm equivocator_IM)
  (equivocators_free_Hbs : has_been_sent_capability equivocators_free_vlsm := composite_has_been_sent_capability equivocator_IM (free_constraint equivocator_IM) finite_index equivocator_Hbs)
  .

Existing Instance equivocators_free_Hbs.

Definition equivocators_no_equivocations_constraint
  :=
  no_equivocations_additional_constraint equivocator_IM (free_constraint equivocator_IM) equivocator_Hbs finite_index.

Definition equivocators_no_equivocations_vlsm
  : VLSM message
  :=
  composite_vlsm equivocator_IM equivocators_no_equivocations_constraint.

Definition seeded_equivocators_no_equivocation_vlsm
  (seed : message -> Prop)
  : VLSM message
  :=
  composite_no_equivocation_vlsm_with_pre_loaded equivocator_IM (free_constraint equivocator_IM) equivocator_Hbs finite_index seed.

Lemma equivocators_initial_state_size
  (is : vstate equivocators_no_equivocations_vlsm)
  (His : vinitial_state_prop equivocators_no_equivocations_vlsm is)
  (eqv : equiv_index)
  : projT1 (is eqv) = 0.
Proof.
  specialize (His eqv).
  destruct His as [Hzero His].
  assumption.
Qed.

(**
An indexed set of [MachineDescriptor]s, one for each equivocating machine in
the composition.

This will be used to project [composite_state]s and [composite_transition_item]s
from the composition of equivocators to the composition of their corresponding
nodes.
*)
Definition equivocator_descriptors : Type := forall (eqv : equiv_index), MachineDescriptor (IM eqv).


(**
Generalizes the [proper_descriptor] definition to [equivocator_descriptors].
Basically, an indexed set is proper w.r.t. a [composite_state] one can obtain
through it a valid projection of the [composite_state] to the non-equivocating
universe.
*)
Definition proper_equivocator_descriptors
  (eqv_descriptors : equivocator_descriptors)
  (s : vstate equivocators_free_vlsm)
  : Prop
  := forall
    (eqv : equiv_index),
    proper_descriptor (IM eqv) (eqv_descriptors eqv) (s eqv).

(** Same as above, but disallowing equivocation. *)
Definition not_equivocating_equivocator_descriptors
  (eqv_descriptors : equivocator_descriptors)
  (s : vstate equivocators_free_vlsm)
  : Prop
  := forall
    (eqv : equiv_index),
    not_equivocating_descriptor (IM eqv) (eqv_descriptors eqv) (s eqv).

Lemma not_equivocating_equivocator_descriptors_proper
  (eqv_descriptors : equivocator_descriptors)
  (s : vstate equivocators_free_vlsm)
  (Hne : not_equivocating_equivocator_descriptors eqv_descriptors s)
  : proper_equivocator_descriptors eqv_descriptors s.
Proof.
  intro eqv. apply not_equivocating_descriptor_proper. apply Hne.
Qed.

Definition zero_descriptor
  (eqv : equiv_index)
  : MachineDescriptor (IM eqv)
  := Existing _ 0 false.

Lemma zero_descriptor_not_equivocating
  (s : vstate equivocators_free_vlsm)
  : not_equivocating_equivocator_descriptors zero_descriptor s.
Proof.
  intro eqv. simpl. lia.
Qed.

Lemma zero_descriptor_proper
  (s : vstate equivocators_free_vlsm)
  : proper_equivocator_descriptors zero_descriptor s.
Proof.
  apply not_equivocating_equivocator_descriptors_proper. apply zero_descriptor_not_equivocating.
Qed.

Lemma proper_equivocator_descriptors_state_update_eqv
  (eqv_descriptors : equivocator_descriptors)
  (s : vstate equivocators_free_vlsm)
  (eqv : equiv_index)
  (si : vstate (equivocator_IM eqv))
  (Hsi_proper : proper_descriptor (IM eqv) (eqv_descriptors eqv) (s eqv))
  (Hproper : proper_equivocator_descriptors eqv_descriptors (state_update equivocator_IM s eqv si))
  : proper_equivocator_descriptors eqv_descriptors s.
Proof.
  intro eqv'.
  specialize (Hproper eqv').
  destruct (decide (eqv' = eqv)).
  - subst. rewrite state_update_eq in Hproper. assumption.
  - rewrite state_update_neq in Hproper; assumption.
Qed.

Definition equivocators_state_project
  (eqv_descriptors : equivocator_descriptors)
  (s : vstate equivocators_free_vlsm)
  (eqv : index)
  : vstate (IM eqv)
  :=
  equivocator_state_descriptor_project (IM eqv) (s eqv) (eqv_descriptors eqv).

Definition lift_to_equivocators_state
  (s : vstate X)
  (eqv : index)
  : vstate (equivocator_IM eqv)
  :=
  mk_singleton_state _ (s eqv).

Lemma lift_initial_to_equivocators_state
  (s : vstate X)
  (Hs : vinitial_state_prop X s)
  : vinitial_state_prop equivocators_no_equivocations_vlsm (lift_to_equivocators_state s).
Proof.
  unfold vinitial_state_prop in *. simpl in *.
  unfold composite_initial_state_prop in *.
  intro i. spec Hs i.
  split; [reflexivity|assumption].
Qed.

(**
A very useful operation on [equivocator_descriptors]s is updating the state corresponding
to a component:
*)
Definition equivocator_descriptors_update
  (s : equivocator_descriptors)
  (i : equiv_index)
  (si : MachineDescriptor (IM i))
  (j : equiv_index)
  : MachineDescriptor (IM j)
  :=
  match decide (j = i) with
  | left e => eq_rect_r (fun i => MachineDescriptor (IM i)) si e
  | _ => s j
  end.

(**
The next few results describe several properties of the [equivocator_descriptors_update] operation.
*)
Lemma equivocator_descriptors_update_neq
  (s : equivocator_descriptors)
  (i : equiv_index)
  (si : MachineDescriptor (IM i))
  (j : equiv_index)
  (Hneq : j <> i)
  : equivocator_descriptors_update s i si j = s j.
Proof.
  unfold equivocator_descriptors_update. destruct (decide (j = i)); congruence.
Qed.

(**
A generalized version of [equivocator_descriptors_update_eq] parametric on the
hypothesis equating the indices.
*)
Lemma equivocator_descriptors_update_eq_rew
  (s : equivocator_descriptors)
  (i : equiv_index)
  (si : MachineDescriptor (IM i))
  (j : equiv_index)
  (Heq : j = i)
  : equivocator_descriptors_update s i si j = eq_rect_r (fun i => MachineDescriptor (IM i)) si Heq.
Proof.
  unfold equivocator_descriptors_update.
  destruct (decide (j = i)); [|congruence]. subst.
  f_equal.
  apply Eqdep_dec.UIP_dec. assumption.
Qed.

Lemma equivocator_descriptors_update_eq
  (s : equivocator_descriptors)
  (i : equiv_index)
  (si : MachineDescriptor (IM i))
  : equivocator_descriptors_update s i si i = si.
Proof.
  rewrite equivocator_descriptors_update_eq_rew with (Heq := eq_refl). reflexivity.
Qed.

Lemma equivocator_descriptors_update_id
  (s : equivocator_descriptors)
  (i : equiv_index)
  (si : MachineDescriptor (IM i))
  (Heq : s i = si)
  : equivocator_descriptors_update s i si = s.
Proof.
  apply functional_extensionality_dep_good.
  intro j.
  destruct (decide (j = i)).
  - subst. apply equivocator_descriptors_update_eq.
  - apply equivocator_descriptors_update_neq. assumption.
Qed.

Lemma equivocator_descriptors_update_twice
  (s : equivocator_descriptors)
  (i : equiv_index)
  (si si': MachineDescriptor (IM i))
  : equivocator_descriptors_update (equivocator_descriptors_update s i si) i si'
  = equivocator_descriptors_update s i si'.
Proof.
  apply functional_extensionality_dep_good.
  intro j.
  destruct (decide (j = i)).
  - subst. rewrite equivocator_descriptors_update_eq. symmetry. apply equivocator_descriptors_update_eq.
  - repeat rewrite equivocator_descriptors_update_neq by assumption.
    reflexivity.
Qed.

Lemma equivocators_state_project_state_update_eqv
  (eqv_descriptors : equivocator_descriptors)
  (s : vstate equivocators_free_vlsm)
  (eqv : equiv_index)
  (seqv : vstate (equivocator_IM eqv))
  : let si :=  match eqv_descriptors eqv with
    | NewMachine _ sn => sn
    | Existing _ i _ =>
      match le_lt_dec (S (projT1 seqv)) i with
      | left _ => projT2 seqv F1
      | right l => projT2 seqv (of_nat_lt l)
      end
    end in
  equivocators_state_project eqv_descriptors (state_update equivocator_IM s eqv seqv)
  = state_update IM (equivocators_state_project eqv_descriptors s) eqv si.
Proof.
  apply functional_extensionality_dep.
  intro ieqv.
  unfold equivocators_state_project.
  unfold state_update.
  match goal with
    |- context [decide ?d] => destruct (decide d)
    end; [|reflexivity].
  subst. unfold eq_rect_r.
  elim_eq_rect. unfold eq_rect.
  unfold equivocator_state_descriptor_project.
  unfold equivocator_state_project.
  destruct seqv as (n, bs). unfold projT1. unfold projT2.
  destruct (eqv_descriptors eqv); [reflexivity|].
  destruct (le_lt_dec (S n) n0); reflexivity.
Qed.

Lemma equivocators_initial_state_project
  (es : vstate equivocators_free_vlsm)
  (Hes : vinitial_state_prop equivocators_free_vlsm es)
  (eqv_descriptors : equivocator_descriptors)
  (Heqv : proper_equivocator_descriptors eqv_descriptors es)
  : vinitial_state_prop X (equivocators_state_project eqv_descriptors es).
Proof.
  intro eqv. specialize (Hes eqv).
  unfold equivocator_IM in Hes.
  unfold equivocators_state_project.
  specialize (Heqv eqv).
  destruct (eqv_descriptors eqv) as [sn | i fi]; [assumption|].
  destruct Hes as [Hzero Hes].
  destruct (es eqv) as (n, bs). simpl in Heqv.
  destruct (le_lt_dec (S n) i); [lia|].
  simpl in *.
  subst. assert (Hi: i = 0) by lia. subst.
  assumption.
Qed.

Lemma equivocators_initial_message
  (m : message)
  (Hem : vinitial_message_prop equivocators_free_vlsm m)
  : vinitial_message_prop X m.
Proof.
  destruct Hem as [eqv [emi Hem]].
  exists eqv.
  unfold equivocator_IM in emi.
  exists emi. assumption.
Qed.
End fully_equivocating_composition.
