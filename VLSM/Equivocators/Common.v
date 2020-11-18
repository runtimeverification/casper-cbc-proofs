Require Import
  List Coq.Vectors.Fin
  Arith.Compare_dec Lia
  Program
  .
Import ListNotations.
From CasperCBC
  Require Import
    Preamble
    VLSM.Common
    .

(** * Equivocator VLSMs

An [equivocator_vlsm] for a given [VLSM] <<X>> is a VLSM which
- starts as a regular machine X
- can equivocate any of its current copies by duplicating it.
- can start a new machine in a (potentially) different initial state.
- can perform [valid] [transition]s using any of the internal machines

The state of such a machine will be abstracted using

1. A [nat]ural <<n>>, stating the number of copies of the original machine
2. A state of <<X>> for each 1..n+1

To preserve determinism we need to update the labels to indicate what copy
of the machine will be used for a transition.
To achieve this, we'll extend the labels of <<X>>, say <<L_X>> as follows

[L = <<L_X>> x MachineDescriptor]

The second component of the label tells which internal machine should be
used for performing the transition. It can be one of the following:
* [NewMachine <<s>>] where <<s>> is an state of <<X>>, will
  extend the state with a new machine initialized with <<s>>
  and will perform the transition on that machine.
* [Existing <<i>> <<is_equiv>>] perform transition on internal machine <<i>>
  but may equivocate, depending on the <<is_equiv>> as follows:

  * if <<is_equiv>> is [false], update the state of machine <<i>>
  * if <<is_equiv>> is [true], duplicate the state of machine <<i>> and
    perform transition on the copy

These changes are reflected in the validity and transition functions.
For validity we additionaly require that the machine descriptor refers
to a valid internal machine, or to an initial state of <<X>>.

*)

Section equivocator_vlsm.
  Context
    {message : Type}
    (X : VLSM message)
    .

Inductive MachineDescriptor : Type
  :=
  | NewMachine : vstate X -> MachineDescriptor
  | Existing : nat -> bool -> MachineDescriptor.


Definition equivocator_type : VLSM_type message :=
  {| state := {n : nat & Fin.t (S n) -> vstate X};
     label := vlabel X * MachineDescriptor
  |}.

Definition equivocator_state : Type := @state message equivocator_type.

Definition mk_singleton_state
  (s : vstate X)
  : equivocator_state
  :=
  existT _ 0 (fun _ => s).

Definition equivocator_label : Type := @label message equivocator_type.

Definition mk_label
  (lx : vlabel X)
  (d : MachineDescriptor)
  : equivocator_label
  := (lx, d).

(**
Attempts to obtain the state of the internal machine with index <<i>>
from an [equivocator_state]. Fails with index <<i>> does not refer to a
machine.
*)
Definition equivocator_state_project
  (bs : equivocator_state)
  (i : nat)
  : option (vstate X)
  :=
  let (n, s) := bs in
  match (le_lt_dec (S n) i) with
  | right lt_in => Some (s (of_nat_lt lt_in))
  | _ =>  None
  end.

Definition equivocator_state_update
  (bs : equivocator_state)
  (n := projT1 bs)
  (i : Fin.t (S n))
  (si : vstate X)
  : equivocator_state
  :=
  existT _ n
    (fun j => if Fin.eq_dec i j then si else projT2 bs j).

(** Some basic properties for 'equivocator_state_update' *)

Lemma equivocator_state_update_size
  (bs : equivocator_state)
  (i : Fin.t (S (projT1 bs)))
  (si : vstate X)
  : projT1 (equivocator_state_update bs i si) = projT1 bs.
Proof.
  destruct bs. reflexivity.
Qed.


Lemma equivocator_state_update_eq
  (bs : equivocator_state)
  (n := projT1 bs)
  (i : Fin.t (S n))
  (si : vstate X)
  : projT2 (equivocator_state_update bs i si) i = si.
Proof.
  simpl. rewrite eq_dec_if_true; reflexivity.
Qed.

Lemma equivocator_state_update_neq
  (bs : equivocator_state)
  (n := projT1 bs)
  (i j : Fin.t (S n))
  (si : vstate X)
  (Hij : i <> j)
  : projT2 (equivocator_state_update bs i si) j = projT2 bs j.
Proof.
  simpl. rewrite eq_dec_if_false; try reflexivity. assumption.
Qed.

(**
Extends an [equivocator_state] with a new state of the original machine.
*)
Program Definition equivocator_state_extend
  (bs : equivocator_state)
  (s : vstate X)
  : equivocator_state
  :=
  let (n, is) := bs in
  existT _ (S n)
    (fun j =>
      let (nj, Hnj) := to_nat j in
      if (nat_eq_dec nj (S n)) then s else is (@of_nat_lt nj (S n) _)
    ).
Next Obligation.
  lia.
Defined.

(** Extension preseves original state.*)
Lemma equivocator_state_extend_original_state
  (bs : equivocator_state)
  (s : vstate X)
  : projT2 (equivocator_state_extend bs s) F1 = projT2 bs F1.
Proof.
  unfold equivocator_state_extend.
  destruct bs as (n, bs). simpl.
  reflexivity.
Qed.

(** The original state index is present in any equivocator state*)
Lemma Hzero (s : equivocator_state) : 0 < S (projT1 s).
Proof. lia. Qed.

(* An [equivocator_state] has the [initial_state_prop]erty if it only
contains one state of original machine, and that state is initial.
*)
Definition equivocator_initial_state_prop
  (bs : equivocator_state)
  : Prop
  := projT1 bs = 0 /\ vinitial_state_prop X (projT2 bs (of_nat_lt (Hzero bs))).

Definition equivocator_initial_state
  := sig equivocator_initial_state_prop.

Definition equivocator_s0 : equivocator_initial_state.
Proof.
  exists (mk_singleton_state (proj1_sig (vs0 X))).
  unfold mk_singleton_state.
  unfold equivocator_initial_state_prop.
  split; try reflexivity.
  simpl. destruct (vs0 X). assumption.
Defined.

Definition equivocator_l0 : equivocator_label :=
  (vl0 X, Existing 0 false).

Definition equivocator_sig
  : VLSM_sign equivocator_type
  :=
    {|   initial_state_prop := equivocator_initial_state_prop
       ; s0 := equivocator_s0
       ; initial_message_prop := vinitial_message_prop X
       ; m0 := vm0 X
       ; l0 := equivocator_l0
    |}.

Definition equivocator_transition
  (bl : equivocator_label)
  (bsom : equivocator_state * option message)
  : equivocator_state * option message
  :=
  let (bs, om) := bsom in
  let n := projT1 bs in
  let s := projT2 bs in
  let l := fst bl in
  match snd bl with
  | NewMachine sn  => (* creating a new machine with initial state sn*)
    (equivocator_state_extend bs sn, None)
  | Existing i is_equiv => (* transition using the state of machine i *)
    match (le_lt_dec (S n) i) with
    | right lt_in =>
      let ni := of_nat_lt lt_in in
      let si := s ni in
      let (si', om') := vtransition X l (si, om) in
      match is_equiv with
      | false => (equivocator_state_update bs ni si', om') (* not equivocating *)
      | true => (equivocator_state_extend bs si', om') (* equivocating in a new copy *)
      end
    | _ =>  bsom
    end
  end.

Definition equivocator_valid
  (bl : equivocator_label)
  (bsom : equivocator_state * option message)
  : Prop
  :=
  let (bs, om) := bsom in
  let n := projT1 bs in
  let s := projT2 bs in
  let l := fst bl in
  match snd bl with
  | NewMachine sn  => (* state is initial and it's valid to transition from it *)
    vinitial_state_prop X sn /\ om = None
  | Existing i is_equiv => (* the index is good, and transition valid for it *)
    exists (Hi : i < S n), vvalid X l (s (of_nat_lt Hi), om)
  end.

Definition equivocator_vlsm_machine
  : VLSM_class equivocator_sig
  :=
  {|  transition := equivocator_transition
   ;  valid := equivocator_valid
  |}.

Definition equivocator_vlsm
  : VLSM message
  :=
  mk_vlsm equivocator_vlsm_machine.

End equivocator_vlsm.

Section equivocator_vlsm_protocol_state_projections.

Context
  {message : Type}
  (X : VLSM message)
  (equivocator_vlsm := equivocator_vlsm X)
  (MachineDescriptor := MachineDescriptor X)
  .

 (** Whether a descriptor can be used when projecting a state*)
Definition proper_descriptor
  (d : MachineDescriptor)
  (s : vstate equivocator_vlsm)
  :=
  match d with
  | NewMachine _ sn => vinitial_state_prop X sn
  | Existing _ i _ => i < S (projT1 s)
  end.

Definition not_equivocating_descriptor
  (d : MachineDescriptor)
  (s : vstate equivocator_vlsm)
  :=
  match d with
  | Existing _ i false => i < S (projT1 s)
  | _ => False
  end.

Lemma not_equivocating_descriptor_proper
  (d : MachineDescriptor)
  (s : vstate equivocator_vlsm)
  (Hned : not_equivocating_descriptor d s)
  : proper_descriptor d s.
Proof.
  destruct d; [contradict Hned|].
  destruct b; [contradict Hned|].
  assumption.
Qed.

Local Tactic Notation "unfold_transition"  hyp(H) :=
  ( unfold transition in H; unfold equivocator_vlsm in H
  ; unfold Common.equivocator_vlsm in H
  ; unfold mk_vlsm in H; unfold machine in H
  ; unfold projT2 in H; unfold equivocator_vlsm_machine in H
  ; unfold equivocator_transition in H).

(**
Protocol messages in the [equivocator_vlsm] are also protocol in the
original machine.  All components of a protocol state in the
[equivocator_vlsm] are also protocol in the original machine.
*)
Lemma equivocator_state_project_protocol
  (bs : vstate equivocator_vlsm)
  (om : option message)
  (Hbs : protocol_prop equivocator_vlsm (bs, om))
  :
  option_protocol_message_prop X om /\
  let (n, bs) := bs in
  forall (i : Fin.t (S n)), protocol_state_prop X (bs i).
Proof.
  generalize_eqs_vars Hbs.
  induction Hbs; simplify_dep_elim; split.
  - exists (proj1_sig (vs0 X)). apply protocol_initial_state.
  - destruct is as [is His]. unfold s; clear s. simpl.
    destruct His as [Hzero His].
    destruct is as (n, is). simpl in Hzero. subst n. simpl in His.
    intro i. dependent destruction i; try inversion i.
    exists None. replace (is F1) with (proj1_sig (exist _ _ His)) by reflexivity.
    apply protocol_initial_state.
  - unfold om0; clear om0.
    exists (proj1_sig (vs0 X)). apply (protocol_initial_message X).
  - unfold s; clear s. unfold s0. simpl.
    intro i. exists None. apply protocol_initial_state.
  - specialize (IHHbs1 X s _om eq_refl JMeq_refl).
    specialize (IHHbs2 X _s om0 eq_refl JMeq_refl).
    specialize (protocol_generated X) as Hgen.
    simpl in Hv.
    destruct l as (l, descriptor). simpl in Hv.
    destruct descriptor as [sn| i is_equiv].
    + destruct Hv as [Hsn Hv]. subst om0.
      simpl in x. inversion x. subst. destruct IHHbs2; try assumption.
    + unfold_transition x.
      unfold snd in x. destruct Hv as [Hi Hv].
      destruct (le_lt_dec (S (projT1 s)) i). { lia. }
      replace (of_nat_lt l0) with (of_nat_lt Hi) in *; try apply of_nat_ext.
      clear l0.
      destruct s as (n, bs').
      destruct IHHbs1 as [_ IHHbs1].
      spec IHHbs1 (of_nat_lt Hi).
      destruct IHHbs1 as [_om' Hbs't].
      destruct IHHbs2 as [Hom _].
      clear Hbs2 _s.
      destruct Hom as [_s Hom].
      specialize (Hgen l (bs' (of_nat_lt Hi)) _om' Hbs't _s om0 Hom Hv).
      replace
        (@transition message (@type message X) (@sign message X)
              (@machine message X) l
              (@pair (@state message (@type message X))
                 (option message) (bs' (of_nat_lt Hi)) om0))
        with (vtransition X l (bs' (of_nat_lt Hi), om0))
        in Hgen
        by reflexivity.
      simpl in *.
      destruct (vtransition X l (bs' (of_nat_lt Hi), om0)) as (si', om') eqn:Ht.
      exists si'.
      destruct is_equiv as [|]; inversion x; subst; assumption.
  - destruct bs as (n, bs).
    intro j.
    specialize (IHHbs1 X s _om eq_refl JMeq_refl).
    destruct IHHbs1 as [_ IHHbs1].
    specialize (IHHbs2 X _s om0 eq_refl JMeq_refl).
    specialize (protocol_generated X) as Hgen.
    unfold_transition x.
    destruct l as (l, descriptor). unfold snd in x.
    destruct descriptor as [sn | i is_equiv].
    + destruct Hv as [Hsn Hv]. subst om0.
      inversion x. subst om.
      unfold equivocator_state_extend in H0.
      destruct s as (n0, bs0).
      inversion H0. subst n.
      simpl_existT. subst.
      destruct (to_nat j) as (nj, Hnj).
      try destruct (nat_eq_dec nj (S n0)).
      * exists None. replace sn with (proj1_sig (exist _ sn Hsn)) by reflexivity.
        constructor.
      * apply IHHbs1.
    + destruct Hv as [Hi Hv].
      destruct (le_lt_dec (S (projT1 s)) i). { lia. }
      replace (of_nat_lt l0) with (of_nat_lt Hi) in *; try apply of_nat_ext.
      clear l0.
      destruct s as (n0, bs0); simpl in *.
      destruct (IHHbs1 (of_nat_lt Hi)) as [_om0 Hbs0t].
      destruct IHHbs2 as [(_som, Hom) _].
      specialize (Hgen l (bs0 (of_nat_lt Hi))  _om0 Hbs0t _som om0 Hom Hv).
      replace
        (@transition message (@type message X) (@sign message X)
              (@machine message X) l
              (@pair (@state message (@type message X))
                 (option message) (bs0 (of_nat_lt Hi)) om0))
        with (vtransition X l (bs0 (of_nat_lt Hi), om0))
        in Hgen
        by reflexivity.
      destruct (vtransition X l (bs0 (of_nat_lt Hi), om0)) as (si', om') eqn:Ht.
      destruct is_equiv as [|]; inversion x; clear x
      ; subst n om'; apply inj_pairT2 in H1; subst.
      * destruct (to_nat j) as (nj, Hnj).
        try destruct (nat_eq_dec  nj (S n0)); try (exists om; assumption).
        apply IHHbs1.
      * destruct (Fin.eq_dec (of_nat_lt Hi) j); try apply IHHbs1.
        exists om. assumption.
Qed.

Lemma equivocator_state_project_protocol_state
  (bs : vstate equivocator_vlsm)
  (Hbs : protocol_state_prop equivocator_vlsm bs)
  :
  let (n, bs) := bs in
  forall (i : Fin.t (S n)), protocol_state_prop X (bs i).
Proof.
  destruct Hbs as [om Hbs].
  apply equivocator_state_project_protocol in Hbs.
  apply proj2 in Hbs.
  assumption.
Qed.

Lemma equivocator_state_project_protocol_message
  (om : option message)
  (Hom : option_protocol_message_prop equivocator_vlsm om)
  :
  option_protocol_message_prop X om.
Proof.
  destruct Hom as [s Hom].
  apply equivocator_state_project_protocol in Hom.
  apply proj1 in Hom.
  assumption.
Qed.

(**
All components of a protocol states of the [pre_loaded_with_all_messages_vlsm] corresponding
to an [equivocator_vlsm] are also protocol for the [pre_loaded_with_all_messages_vlsm]
corresponding to the original machine.
*)
Lemma preloaded_equivocator_state_project_protocol_state
  (bs : vstate equivocator_vlsm)
  (Hbs : protocol_state_prop (pre_loaded_with_all_messages_vlsm equivocator_vlsm) bs)
  (i : Fin.t (S (projT1 bs)))
  :
  protocol_state_prop (pre_loaded_with_all_messages_vlsm X) (projT2 bs i).
Proof.
  revert i.
  pose (fun bs : vstate equivocator_vlsm => forall i : t (S (projT1 bs)), protocol_state_prop (pre_loaded_with_all_messages_vlsm X) (projT2 bs i)) as P.
  revert Hbs. revert bs.
  apply (protocol_state_prop_ind (pre_loaded_with_all_messages_vlsm equivocator_vlsm) P)
  ; try assumption; unfold P in *; clear P; intros.
  - destruct Hs as [Hzero His].
    destruct s. simpl in *. subst x. exists None.
    dependent destruction i; try inversion i.
    replace (v F1) with (proj1_sig (exist _ _ His)) by reflexivity.
     apply (protocol_initial_state (pre_loaded_with_all_messages_vlsm X)).
  - destruct Ht as [[Hps [_ Hv]] Ht].
    simpl in Ht. unfold vtransition in Ht. unfold_transition Ht.
    destruct l as (l, description).
    unfold snd in Ht.
    destruct description as [sn| j is_equiv].
    + destruct Hv as [Hsn Hv]. subst om.
      inversion Ht. subst.
      unfold equivocator_state_extend.
      destruct s as (ns, bs).
      simpl in *. destruct (to_nat i) as (ni, Hni).
      destruct (nat_eq_dec ni (S ns)); try apply Hs.
      subst. exists None.
      replace sn with (proj1_sig (exist _ sn Hsn)) by reflexivity.
      constructor.
    + destruct Hv as [Hj Hv].
      destruct (le_lt_dec (S (projT1 s)) j). { lia. }
      replace (of_nat_lt l0) with (of_nat_lt Hj) in *; try apply of_nat_ext. clear l0.
      destruct (Hs (of_nat_lt Hj)) as [_omj Hsj].
      specialize (protocol_generated (pre_loaded_with_all_messages_vlsm X) l (projT2 s (of_nat_lt Hj)) _omj Hsj)
        as Hgen.
      spec Hgen (proj1_sig (vs0 X)) om (pre_loaded_with_all_messages_message_protocol_prop X om) Hv.
      replace (transition l (projT2 s (of_nat_lt Hj), om))
        with (vtransition X l (projT2 s (of_nat_lt Hj), om))
        in Hgen by reflexivity.
      simpl in *.
      destruct (vtransition X l (projT2 s (of_nat_lt Hj), om)) as (sj', omj').
      destruct is_equiv as [|]; inversion Ht; subst; clear Ht; simpl in *.
      * destruct s as (ns, bs). simpl in *.
        destruct (to_nat i) as (ni, Hni).
        destruct (nat_eq_dec ni (S ns)); try (exists om'; assumption).
        apply Hs.
      * destruct (Fin.eq_dec (of_nat_lt Hj) i); try apply Hs.
        exists om'. assumption.
Qed.

End equivocator_vlsm_protocol_state_projections.