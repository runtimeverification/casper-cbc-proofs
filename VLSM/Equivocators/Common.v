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

Definition is_singleton_state
  (s : equivocator_state)
  : Prop
  := projT1 s = 0.

Lemma is_singleton_state_dec
  (s : equivocator_state)
  : Decision (is_singleton_state s).
Proof.
  apply nat_eq_dec.
Qed.

Definition is_equivocating_state
  (s : equivocator_state)
  : Prop
  := not (is_singleton_state s).

Lemma is_equivocating_state_dec
  (s : equivocator_state)
  : Decision (is_equivocating_state s).
Proof.
  apply Decision_not.
  apply is_singleton_state_dec.
Qed.

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

(**
Projecting an [equivocator_state] over a [MachineDescriptor].

This is extracted from the original [equivocators_state_project] to allow
factoring out the proofs by proving properties at this level.
*)
Definition equivocator_state_descriptor_project
  (s : equivocator_state)
  (descriptor : MachineDescriptor)
  : vstate X
  :=
  match descriptor with
  | NewMachine sn => sn
  | Existing j _ =>
    let (n, bs) := s in
    match (le_lt_dec (S n) j) with
    | right lt_in => bs (of_nat_lt lt_in)
    | left _ => bs F1
    end
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
  simpl. rewrite eq_dec_if_false by assumption. reflexivity.
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

Lemma equivocator_state_extend_project_last
  (bs : equivocator_state)
  (s : vstate X)
  (ns := projT1 bs)
  : let ext := equivocator_state_extend bs s in
    forall (l : S ns < S (projT1 ext)), projT2 ext (of_nat_lt l) = s.
Proof.
  unfold ns. clear ns.
  destruct bs as (ns, sbs). simpl. intro l.
  rewrite to_nat_of_nat.
  destruct (nat_eq_dec (S ns) (S ns)); [|lia].
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
  split; [reflexivity|].
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
  | NewMachine sn  => (* state is initial *)
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

(** If the state obtained after one transition has no equivocation, then
the descriptor of the label of the transition must be Existing 0 false
*)
Lemma equivocator_transition_no_equivocation_zero_descriptor
  (iom oom: option message)
  (l: vlabel equivocator_vlsm)
  (s s': vstate equivocator_vlsm)
  (Hv: vvalid equivocator_vlsm l (s, iom))
  (Ht: vtransition equivocator_vlsm l (s, iom) = (s', oom))
  (Hs' : is_singleton_state X s')
  : snd l = Existing _ 0 false.
Proof.
  unfold is_singleton_state in Hs'.
  unfold vtransition in Ht. unfold_transition Ht.
  destruct l as (l, [sn | ei ef]); unfold snd in Ht
  ; [inversion Ht; subst; destruct s; simpl; inversion Hs'|].
  destruct Hv as [Hei _].
  destruct (le_lt_dec (S (projT1 s)) ei); [lia|].
  match type of Ht with
  | (let (_, _) := ?t in _) = _ => destruct t as (_s', _om')
  end.
  destruct ef; inversion Ht; subst; clear Ht.
  - destruct s. inversion Hs'.
  - destruct s. simpl in *. assert (ei = 0) by lia. subst. reflexivity.
Qed.

(** If the state obtained after one transition has no equivocation, then
the state prior to the transition has no equivocation as well.
*)
Lemma equivocator_transition_reflects_singleton_state
  (iom oom: option message)
  (l: vlabel equivocator_vlsm)
  (s s': vstate equivocator_vlsm)
  (Ht: vtransition equivocator_vlsm l (s, iom) = (s', oom))
  : is_singleton_state X s' -> is_singleton_state X s.
Proof.
  unfold is_singleton_state.
  unfold vtransition in Ht. unfold_transition Ht.
  destruct l as (l, [sn | ei ef]); unfold snd in Ht
  ; [inversion Ht; subst; destruct s; simpl; congruence|].
  destruct (le_lt_dec (S (projT1 s)) ei)
  ; [inversion Ht; subst; exact id|].
  match type of Ht with
  | (let (_, _) := ?t in _) = _ => destruct t as (_s', _om')
  end.
  destruct ef; inversion Ht; subst; [|exact id].
  destruct s. simpl. congruence.
Qed.

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
  dependent induction Hbs; split.
  - exists (proj1_sig (vs0 X)). apply protocol_initial_state.
  - destruct is as [is His]. unfold s; clear s. simpl.
    destruct His as [Hzero His].
    destruct is as (n, is). simpl in Hzero. subst n. simpl in His.
    intro i. dependent destruction i; [|inversion i].
    exists None. change (is F1) with (proj1_sig (exist _ _ His)).
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
      simpl in x. inversion x. subst. apply IHHbs2.
    + unfold_transition x.
      unfold snd in x. destruct Hv as [Hi Hv].
      destruct (le_lt_dec (S (projT1 s)) i); [lia|].
      replace (of_nat_lt l0) with (of_nat_lt Hi) in * by apply of_nat_ext.
      clear l0.
      destruct s as (n, bs').
      destruct IHHbs1 as [_ IHHbs1].
      spec IHHbs1 (of_nat_lt Hi).
      destruct IHHbs1 as [_om' Hbs't].
      destruct IHHbs2 as [Hom _].
      clear Hbs2 _s.
      destruct Hom as [_s Hom].
      specialize (Hgen l (bs' (of_nat_lt Hi)) _om' Hbs't _s om0 Hom Hv).
      match type of Hgen with
      | protocol_prop _ ?t =>
        change t  with (vtransition X l (bs' (of_nat_lt Hi), om0))
          in Hgen
      end.
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
      * exists None. change sn with (proj1_sig (exist _ sn Hsn)).
        constructor.
      * apply IHHbs1.
    + destruct Hv as [Hi Hv].
      destruct (le_lt_dec (S (projT1 s)) i); [lia|].
      replace (of_nat_lt l0) with (of_nat_lt Hi) in * by apply of_nat_ext.
      clear l0.
      destruct s as (n0, bs0); simpl in *.
      destruct (IHHbs1 (of_nat_lt Hi)) as [_om0 Hbs0t].
      destruct IHHbs2 as [(_som, Hom) _].
      specialize (Hgen l (bs0 (of_nat_lt Hi))  _om0 Hbs0t _som om0 Hom Hv).
      match type of Hgen with
      | protocol_prop _ ?t =>
        change t  with (vtransition X l (bs0 (of_nat_lt Hi), om0))
          in Hgen
      end.
      destruct (vtransition X l (bs0 (of_nat_lt Hi), om0)) as (si', om') eqn:Ht.
      destruct is_equiv as [|]; inversion x; clear x
      ; subst n om'; apply inj_pairT2 in H1; subst.
      * destruct (to_nat j) as (nj, Hnj).
        destruct (nat_eq_dec  nj (S n0)); [exists om; assumption|].
        apply IHHbs1.
      * destruct (Fin.eq_dec (of_nat_lt Hi) j); [|apply IHHbs1].
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
  revert bs Hbs i.
  induction 1 using protocol_state_prop_ind;intros.
  - destruct Hs as [Hzero His].
    destruct s. simpl in *. subst x. exists None.
    dependent destruction i; [|inversion i].
    change (v F1) with (proj1_sig (exist _ _ His)).
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
      destruct (nat_eq_dec ni (S ns)); [|apply IHHbs].
      subst. exists None.
      change sn with (proj1_sig (exist _ sn Hsn)).
      constructor.
    + destruct Hv as [Hj Hv].
      destruct (le_lt_dec (S (projT1 s)) j); [lia|].
      replace (of_nat_lt l0) with (of_nat_lt Hj) in * by apply of_nat_ext. clear l0.
      destruct (IHHbs (of_nat_lt Hj)) as [_omj Hsj].
      specialize (protocol_generated (pre_loaded_with_all_messages_vlsm X) l (projT2 s (of_nat_lt Hj)) _omj Hsj)
        as Hgen.
      spec Hgen (proj1_sig (vs0 X)) om (pre_loaded_with_all_messages_message_protocol_prop X om) Hv.
      change (transition l (projT2 s (of_nat_lt Hj), om))
        with (vtransition X l (projT2 s (of_nat_lt Hj), om))
        in Hgen.
      simpl in *.
      destruct (vtransition X l (projT2 s (of_nat_lt Hj), om)) as (sj', omj').
      destruct is_equiv as [|]; inversion Ht; subst; clear Ht; simpl in *.
      * destruct s as (ns, bs). simpl in *.
        destruct (to_nat i) as (ni, Hni).
        destruct (nat_eq_dec ni (S ns)); [|apply IHHbs].
        exists om'. assumption.
      * destruct (Fin.eq_dec (of_nat_lt Hj) i); [|apply IHHbs].
        exists om'. assumption.
Qed.

(**
Next couple of lemmas characterize the projections of a [equivocator_state]
after taking a transition in terms of the preceeeding state.

These are simpler version of the results concerning the projection of
states from the composition of equivocators over [equivocation_choice]s.

These results are used for characterizing the projection of the [destination]
of a [transition_item] in an equivocator trace in
[equivocator_transition_item_project_proper_characterization].
*)

Lemma new_machine_label_equivocator_state_project_last
  (l : vlabel equivocator_vlsm) s oin s' oout
  (Ht : vtransition equivocator_vlsm l (s, oin) = (s', oout))
  sn
  (Hnew: snd l = NewMachine _ sn)
  fi
  : equivocator_state_descriptor_project X s' (Existing _ (projT1 s') fi) =
    equivocator_state_descriptor_project X s (NewMachine _ sn).
Proof.
  destruct l as (l, new). simpl in Hnew. subst new.
  unfold vtransition in Ht. simpl in Ht. inversion Ht. subst.
  clear Ht.
  remember (equivocator_state_extend X s sn) as ext.
  destruct ext as (n, bs).
  unfold projT1. unfold equivocator_state_descriptor_project.
  destruct (le_lt_dec (S n) n); [lia|].
  destruct s as (nsi, bsi). unfold equivocator_state_extend in Heqext.
  inversion Heqext. subst.
  simpl_existT. subst. rewrite to_nat_of_nat.
  destruct (nat_eq_dec (S nsi) (S nsi)); [|congruence].
  reflexivity.
Qed.

Lemma new_machine_label_equivocator_state_project_not_last
  (l : vlabel equivocator_vlsm) s oin s' oout
  (Ht : vtransition equivocator_vlsm l (s, oin) = (s', oout))
  sn
  (Hnew: snd l = NewMachine _ sn)
  ni fi
  (Hni : ni < projT1 s')
  fi'
  : equivocator_state_descriptor_project X s' (Existing _ ni fi) =
    equivocator_state_descriptor_project X s (Existing _ ni fi').
Proof.
  destruct l as (li, new). simpl in Hnew. subst new.
  inversion Ht. subst.
  unfold equivocator_state_descriptor_project.
  unfold equivocator_state_extend.
  unfold equivocator_state_extend in Hni.
  destruct s as (nsi', bsi').
  unfold projT1 in Hni.
  destruct (le_lt_dec (S (S nsi')) ni); [lia|].
  rewrite to_nat_of_nat.
  destruct (nat_eq_dec ni (S nsi')); [lia|].
  destruct (le_lt_dec (S nsi') ni); [lia|].
  f_equal.
  apply of_nat_ext.
Qed.

Lemma existing_true_label_equivocator_state_project_not_last
  (l : vlabel equivocator_vlsm) s oin s' oout
  (Ht : vtransition equivocator_vlsm l (s, oin) = (s', oout))
  ieqvi
  (Hex_true: snd l = Existing _ ieqvi true)
  (Hieqvi : ieqvi < S (projT1 s))
  ni fi
  (Hni : ni < projT1 s')
  fi'
  : equivocator_state_descriptor_project X s' (Existing _ ni fi)
  = equivocator_state_descriptor_project X s (Existing _ ni fi').
Proof.
  destruct l as (li, ex_true). simpl in Hex_true. subst ex_true.
  unfold vtransition in Ht. unfold_transition Ht. unfold snd in Ht.
  destruct ( le_lt_dec (S (projT1 s)) ieqvi ); [lia|].
  destruct
    (vtransition X (fst (li, Existing X ieqvi true))
    (projT2 s (of_nat_lt l), oin))
    as (si'', om'').
  inversion Ht. subst. clear Ht.
  unfold equivocator_state_descriptor_project.
  unfold equivocator_state_extend.
  unfold equivocator_state_extend in Hni.
  destruct s as (nsi', bsi').
  unfold projT1 in Hni.
  destruct (le_lt_dec (S (S nsi')) ni); [lia|].
  rewrite to_nat_of_nat.
  destruct (nat_eq_dec ni (S nsi')); [lia|].
  destruct (le_lt_dec (S nsi') ni); [lia|].
  f_equal.
  apply of_nat_ext.
Qed.

Lemma existing_false_label_equivocator_state_project_not_same
  (l : vlabel equivocator_vlsm) s oin s' oout
  (Ht : vtransition equivocator_vlsm l (s, oin) = (s', oout))
  ieqvi
  (Hex_false: snd l = Existing _ ieqvi false)
  (Hieqvi : ieqvi < S (projT1 s))
  ni fi
  (Hni : ni < S (projT1 s'))
  (Hnieqvi : ieqvi <> ni)
  fi'
  : equivocator_state_descriptor_project X s' (Existing _ ni fi)
  = equivocator_state_descriptor_project X s (Existing _ ni fi').
Proof.
  destruct l as (li, ex_false). simpl in Hex_false. subst ex_false.
  unfold vtransition in Ht. unfold_transition Ht. unfold snd in Ht.
  destruct ( le_lt_dec (S (projT1 s)) ieqvi ); [lia|].
  destruct
    (vtransition X (fst (li, Existing X ieqvi false))
    (projT2 s (of_nat_lt l), oin))
    as (si'', om'').
  inversion Ht. subst. clear Ht.
  unfold equivocator_state_descriptor_project.
  destruct s as (nsi', bsi').
  simpl in Hieqvi, l.
  unfold equivocator_state_update in *.
  unfold projT1 in *.
  destruct (le_lt_dec (S nsi') ni); [lia|].
  rewrite eq_dec_if_false; [reflexivity|].
  intro contra. elim Hnieqvi.
  apply (f_equal to_nat) in contra. repeat rewrite to_nat_of_nat in contra.
  inversion contra. reflexivity.
Qed.

End equivocator_vlsm_protocol_state_projections.
