Require Import
  List ListSet Coq.Vectors.Fin
  Arith.Compare_dec Lia Wf_nat
  Program
  FunctionalExtensionality
  .
Import ListNotations.
From CasperCBC
  Require Import
    Preamble ListExtras ListSetExtras FinExtras
    VLSM.Common VLSM.Composition VLSM.Equivocation
    VLSM.Equivocators.Common
    .

Section equivocator_vlsm_projections.

Context
  {message : Type}
  (X : VLSM message)
  (equivocator_vlsm := equivocator_vlsm X)
  (MachineDescriptor := MachineDescriptor X)
  .

Local Tactic Notation "unfold_transition"  hyp(H) :=
  ( unfold transition in H; unfold equivocator_vlsm in H
  ; unfold Common.equivocator_vlsm in H
  ; unfold mk_vlsm in H; unfold machine in H
  ; unfold projT2 in H; unfold equivocator_vlsm_machine in H
  ; unfold equivocator_transition in H).

Instance option_bool_eq : EqDec (option bool)
  := option_eq_dec Bool.bool_dec.

Definition equivocator_vlsm_transition_item_project
  (item : vtransition_item equivocator_vlsm)
  (descriptor : MachineDescriptor)
  : option (option (vtransition_item X) * MachineDescriptor)
  :=
  match descriptor with
  | NewMachine _ _ => Some (None, descriptor)
  | Existing _ j _ =>
    match item with {| l := (lx, descriptor); input := im; output := om; destination := s |} =>
      let (n, bs) := s in
      match (le_lt_dec (S n) j) with
      | right lt_jn =>
        let nj := of_nat_lt lt_jn in
        let item' := {| l := lx; input := im; output := om; destination := bs nj|} in
        match descriptor with
        | NewMachine _ s =>
          if nat_eq_dec (S j) (S n) then (* this is the first state *)
            Some ( Some item', descriptor)
          else Some (None, Existing _ j false)
        | Existing _ i is_equiv =>
          match is_equiv with
          | false => (* no forking *)
            if nat_eq_dec i j then
              Some ( Some item', descriptor)
            else Some (None, Existing _ j false)
          | true => (* forking, transition happens on forked copy *)
            if nat_eq_dec (S j) (S n) then
              Some (Some item', descriptor)
            else Some (None, Existing _ j false)
          end
        end
      | _ => None
      end
    end
  end.

Lemma equivocator_vlsm_transition_item_project_some_inj
  {item : vtransition_item equivocator_vlsm}
  {itemX itemX' : vtransition_item X}
  {i i' : nat}
  {fi fi' : bool}
  (idescriptor := Existing _ i fi)
  (idescriptor' := Existing _ i' fi')
  {odescriptor odescriptor' : MachineDescriptor}
  (HitemX : equivocator_vlsm_transition_item_project item idescriptor = Some (Some itemX, odescriptor))
  (HitemX' : equivocator_vlsm_transition_item_project item idescriptor' = Some (Some itemX', odescriptor'))
  : i = i' /\ itemX = itemX' /\ odescriptor = odescriptor'.
Proof.
  unfold equivocator_vlsm_transition_item_project in *.
  unfold idescriptor in *. clear idescriptor.
  unfold idescriptor' in *. clear idescriptor'.
  destruct item.
  destruct l as (ls, descriptor).
  destruct destination as (ndest, bdest).
  destruct (le_lt_dec (S ndest) i); try discriminate HitemX.
  destruct (le_lt_dec (S ndest) i'); try discriminate HitemX'.
  destruct descriptor as [sn | j fj].
  - destruct (nat_eq_dec (S i) (S ndest)); try discriminate HitemX.
    inversion HitemX. subst. clear HitemX.
    inversion e. subst i. clear e.
    destruct (nat_eq_dec (S i') (S ndest)); try discriminate HitemX'.
    inversion e. subst i'. inversion HitemX'. subst. clear HitemX'.
    replace (of_nat_lt l0) with (of_nat_lt l) by apply of_nat_ext.
    repeat split; reflexivity.
  - destruct fj as [|] eqn:Hfj.
    + destruct (nat_eq_dec (S i) (S ndest)); try discriminate HitemX.
      inversion HitemX; subst. clear HitemX.
      inversion e. subst i. clear e.
      destruct (nat_eq_dec (S i') (S ndest)); try discriminate HitemX'.
      inversion HitemX'; subst. clear HitemX'.
      inversion e; subst i'; clear e.
      replace (of_nat_lt l0) with (of_nat_lt l) by apply of_nat_ext.
      repeat split; reflexivity.
    + destruct (nat_eq_dec j i); try discriminate HitemX.
      destruct (nat_eq_dec j i'); try discriminate HitemX'.
      inversion HitemX. inversion HitemX'. subst.
      replace (of_nat_lt l0) with (of_nat_lt l) by apply of_nat_ext.
      repeat split; reflexivity.
Qed.

Lemma equivocator_transition_item_project_inv_none
  (item : vtransition_item equivocator_vlsm)
  (descriptor : MachineDescriptor)
  (Hitem: equivocator_vlsm_transition_item_project item descriptor = None)
  : exists
    (i : nat)
    (is_equiv : bool)
    (Hdescriptor : descriptor = Existing _ i is_equiv),
    projT1 (destination item) < i.
Proof.
  unfold equivocator_vlsm_transition_item_project in Hitem.
  destruct item.
  destruct descriptor as [s|i is_equiv]; try discriminate Hitem.
  exists i. exists is_equiv. exists eq_refl.
  destruct destination as (n, bs).
  destruct (le_lt_dec (S n) i); try assumption.
  destruct l as (ls, [is | ix [|]]).
  - destruct (nat_eq_dec (S i) (S n)); discriminate Hitem.
  - destruct (nat_eq_dec (S i) (S n)); discriminate Hitem.
  - destruct (nat_eq_dec ix i); discriminate Hitem.
Qed.

Definition equivocator_vlsm_trace_project
  (tr : list (vtransition_item equivocator_vlsm))
  (descriptor : MachineDescriptor)
  : option (list (vtransition_item X) * MachineDescriptor)
  :=
  fold_right
    (fun item result =>
      match result with
      | None => None
      | Some (r, idescriptor) =>
        match equivocator_vlsm_transition_item_project item idescriptor with
        | None => None
        | Some (None, odescriptor) => Some (r, odescriptor)
        | Some (Some item', odescriptor) => Some (item' :: r, odescriptor)
        end
      end
    )
    (Some ([], descriptor))
    tr.

Lemma equivocator_vlsm_trace_project_on_hard_fork
  (tr : list (vtransition_item equivocator_vlsm))
  (s : vstate X)
  : equivocator_vlsm_trace_project tr (NewMachine _ s) = Some ([], NewMachine _ s).
Proof.
  induction tr; try reflexivity.
  simpl. rewrite IHtr. reflexivity.
Qed.

Lemma equivocator_vlsm_trace_project_cons
  (bprefix : vtransition_item equivocator_vlsm)
  (bsuffix : list (vtransition_item equivocator_vlsm))
  (dstart dlast : MachineDescriptor)
  (tr : list (vtransition_item X))
  (Hproject : equivocator_vlsm_trace_project (bprefix :: bsuffix) dlast = Some (tr, dstart))
  : exists
    (dmiddle : MachineDescriptor)
    (prefix suffix : list (vtransition_item X))
    (Hprefix : equivocator_vlsm_trace_project [bprefix] dmiddle = Some (prefix, dstart))
    (Hsuffix : equivocator_vlsm_trace_project bsuffix dlast = Some (suffix, dmiddle)),
    tr = prefix ++ suffix.
Proof.
  simpl in Hproject.
  destruct (equivocator_vlsm_trace_project bsuffix dlast) as [(suffix, dmiddle)|]
    eqn:Hsuffix
  ; try discriminate Hproject.
  exists dmiddle.
  destruct (equivocator_vlsm_transition_item_project bprefix dmiddle) as [[[prefix|] i]|]
    eqn:Hprefix
  ; inversion Hproject; subst; clear Hproject.
  - exists [prefix]. exists suffix.
    repeat split; try reflexivity.
    simpl in *. rewrite Hprefix. reflexivity.
  -  exists []. exists tr.
    repeat split; try reflexivity.
    simpl in *. rewrite Hprefix. reflexivity.
Qed.

Lemma equivocator_vlsm_trace_project_app
  (bprefix bsuffix : list (vtransition_item equivocator_vlsm))
  (dlast dstart : MachineDescriptor)
  (tr : list (vtransition_item X))
  (Hproject : equivocator_vlsm_trace_project (bprefix ++ bsuffix) dlast = Some (tr, dstart))
  : exists
    (dmiddle : MachineDescriptor)
    (prefix suffix : list (vtransition_item X))
    (Hprefix : equivocator_vlsm_trace_project bprefix dmiddle = Some (prefix, dstart))
    (Hsuffix : equivocator_vlsm_trace_project bsuffix dlast = Some (suffix, dmiddle)),
    tr = prefix ++ suffix.
Proof.
  generalize dependent dstart. generalize dependent tr.
  induction bprefix; intros.
  - exists dstart. exists []. exists tr. exists eq_refl. exists Hproject. reflexivity.
  - rewrite <- app_comm_cons in Hproject.
    apply equivocator_vlsm_trace_project_cons in Hproject.
    destruct Hproject as [da [prefixa [tr' [Ha [Hproject Heq]]]]].
    spec IHbprefix tr' da Hproject.
    destruct IHbprefix as [dmiddle [prefix' [suffix [Hprefix [Hsuffix Htr']]]]].
    exists dmiddle.
    exists (prefixa ++ prefix'). exists suffix.
    repeat split; try assumption.
    + simpl. rewrite Hprefix.
      simpl in Ha.
      destruct (equivocator_vlsm_transition_item_project a da)
        as [(oitem', i)|]
      ; try discriminate Ha.
      destruct oitem' as [item'|]; inversion Ha; subst; reflexivity.
    + subst. rewrite app_assoc. reflexivity.
Qed.

Lemma equivocator_vlsm_trace_project_app_inv
  (bprefix bsuffix : list (vtransition_item equivocator_vlsm))
  (dlast dstart dmiddle : MachineDescriptor)
  (prefix suffix : list (vtransition_item X))
  (Hprefix : equivocator_vlsm_trace_project bprefix dmiddle = Some (prefix, dstart))
  (Hsuffix : equivocator_vlsm_trace_project bsuffix dlast = Some (suffix, dmiddle))
  : equivocator_vlsm_trace_project (bprefix ++ bsuffix) dlast = Some (prefix ++ suffix, dstart).
Proof.
  generalize dependent dstart. generalize dependent prefix.
  induction bprefix; intros.
  - inversion Hprefix. subst. assumption.
  - simpl in Hprefix.
    destruct (equivocator_vlsm_trace_project bprefix dmiddle) as [(prefix', dstart')|]
      eqn:Hprefix'
    ; try discriminate Hprefix.
    specialize (IHbprefix prefix' dstart' eq_refl).
    simpl. rewrite IHbprefix.
    destruct (equivocator_vlsm_transition_item_project a dstart')
      as [[[item'|]i]|]
    ; inversion Hprefix; subst; reflexivity.
Qed.

Lemma equivocator_protocol_transition_item_project_inv2
  (l : vlabel equivocator_vlsm)
  (s' s: vstate equivocator_vlsm)
  (iom oom : option message)
  (Hv: vvalid equivocator_vlsm l (s', iom))
  (Ht: vtransition equivocator_vlsm l (s', iom) = (s, oom))
  (item := {| l := l; input := iom; destination := s; output := oom |})
  (di di' : MachineDescriptor)
  (item' : vtransition_item X)
  (Hitem: equivocator_vlsm_transition_item_project item di = Some (Some item', di'))
  : exists
    (i : nat)
    (fi : bool)
    (Hdi : di = Existing _ i fi)
    (Hi : i < S (projT1 s))
    (sx := projT2 s (of_nat_lt Hi))
    (Hitem' : item' = {| l := fst l; input := iom; destination := sx; output := oom |}),
    match di' with
    | NewMachine _ sn =>
      vinitial_state_prop X sn /\
       vvalid X (fst l) (sn, iom) /\
       vtransition X (fst l) (sn, iom) = (sx, oom)
    | Existing _ i' fi' =>
      exists
       (Hi' : i' < S (projT1 s'))
       (s'x := projT2 s' (of_nat_lt Hi')),
       vvalid X (fst l) (s'x, iom) /\
       vtransition X (fst l) (s'x, iom) = (sx, oom)
  end.
Proof.
  unfold vvalid in Hv. unfold vtransition in Ht.
  unfold_transition Ht.
  simpl in Hv.
  unfold equivocator_vlsm_transition_item_project in Hitem.
  destruct di as [sn| i fi]; try discriminate Hitem.
  exists i. exists fi. exists eq_refl. unfold item in Hitem.
  destruct l as (lx, descriptor).
  destruct s as (ns, bs).
  destruct (le_lt_dec (S ns) i); try discriminate Hitem.
  exists l. unfold snd in Ht. unfold snd in Hv.
  destruct descriptor as [sn| j is_equiv].
  - destruct (nat_eq_dec (S i) (S ns)); try discriminate Hitem.
    inversion e. subst i. clear e.
    inversion Hitem. clear Hitem. exists eq_refl.
    destruct Hv as [Hsn Hv].
    repeat split; try assumption.
    simpl in *.
    destruct (vtransition X lx (sn, iom)) as (sn', om') eqn:Htx.
    inversion Ht. subst. clear Ht. f_equal.
    destruct s' as (ns',bs'). simpl. simpl in H2.
    inversion H2; subst.
    apply inj_pairT2 in H2. subst.
    rewrite to_nat_of_nat.
    destruct (nat_eq_dec (S ns') (S ns')); try elim n; reflexivity.
  - destruct Hv as [Hj Hv].
    destruct (le_lt_dec (S (projT1 s')) j). { lia. }
    replace (of_nat_lt l0) with (of_nat_lt Hj) in *; try apply of_nat_ext. clear l0.
    simpl in Ht.
    destruct (vtransition X lx (projT2 s' (of_nat_lt Hj), iom))
      as (si', om') eqn:Htx.
    destruct s' as (n', bs').
    destruct is_equiv as [|].
    + destruct (nat_eq_dec (S i) (S ns)); try discriminate Hitem.
      inversion Hitem. subst di' item'. clear Hitem.
      exists eq_refl.
      exists Hj. split; try assumption.
      inversion Ht. subst. clear Ht. inversion e. subst i. clear e.
      apply inj_pairT2 in H1. subst. simpl.
      rewrite to_nat_of_nat.
      destruct (nat_eq_dec (S n') (S n')); try assumption.
      elim n. reflexivity.
    + destruct (nat_eq_dec j i); try discriminate Hitem. subst.
      inversion Hitem. subst di' item'. clear Hitem.
      exists eq_refl.
      exists Hj. split; try assumption.
      inversion Ht. subst. clear Ht.
      apply inj_pairT2 in H1. subst. simpl.
      rewrite eq_dec_if_true; try apply of_nat_ext.
      assumption.
Qed.

Lemma equivocator_protocol_transition_item_project_inv3
  (l : vlabel equivocator_vlsm)
  (s s' : vstate equivocator_vlsm)
  (iom oom : option message)
  (Hv: vvalid equivocator_vlsm l (s', iom))
  (Ht: vtransition equivocator_vlsm l (s', iom) = (s, oom))
  (item := {| l := l; input := iom; destination := s; output := oom |})
  (di di' : MachineDescriptor)
  (Hitem: equivocator_vlsm_transition_item_project item di = Some (None, di'))
  : match di with
    | NewMachine _ sn => di' = di
    | Existing _ i fi =>
      exists
        (Hi : i < S (projT1 s))
        (i' : nat)
        (fi' : bool)
        (Hdi' : di' = Existing _ i' fi')
        (Hi' : i' < S (projT1 s')),
        projT2 s' (of_nat_lt Hi') = projT2 s (of_nat_lt Hi)
    end.
Proof.
  unfold vvalid in Hv. unfold vtransition in Ht.
  destruct l as (lx, d).
  simpl in Hv. unfold_transition Ht. unfold snd in Ht.
  unfold equivocator_vlsm_transition_item_project in Hitem.
  destruct di as [si | i fi]; try (inversion Hitem; reflexivity).
  simpl in Hv. unfold item in Hitem.
  destruct s as (ns, bs).
  destruct (le_lt_dec (S ns) i); try discriminate Hitem.
  destruct d as [sd | id fd].
  - destruct (nat_eq_dec (S i) (S ns)); try discriminate Hitem.
    simpl. exists l. inversion Hitem. subst. clear Hitem.
    exists i. exists false. exists eq_refl.
    simpl in *.
    destruct (vtransition X lx (sd, iom)) as (sn', om').
    destruct s' as (ns', bs'). simpl in Ht.
    inversion Ht. subst.
    apply inj_pairT2 in H1.
    simpl.
    assert (Hi' : i < S ns') by lia.
    exists Hi'.
    subst. rewrite to_nat_of_nat.
    destruct (nat_eq_dec i (S ns')). { lia. }
    f_equal. apply of_nat_ext.
  - destruct Hv as [Hj Hv].
    destruct (le_lt_dec (S (projT1 s')) id). { lia. }
    replace (of_nat_lt l0) with (of_nat_lt Hj) in *; try apply of_nat_ext. clear l0.
    destruct s' as (n', bs').
    exists l. simpl in Ht.
    destruct
      (@vtransition message X lx
      (@pair (@vstate message X) (option message)
         (bs' (@of_nat_lt id (S n') Hj)) iom))
      as (si', om') eqn:Htx.
    destruct fd as [|].
    + destruct (nat_eq_dec (S i) (S ns)); try discriminate Hitem.
      inversion Hitem. subst di'. clear Hitem.
      exists i. exists false. exists eq_refl.
      inversion Ht. subst. clear Ht.
      assert (Hi : i < (S n')) by lia.
      exists Hi.
      apply inj_pairT2 in H1. subst. simpl.
      rewrite to_nat_of_nat in *.
      destruct (nat_eq_dec i (S n')). { lia. }
      f_equal.
      apply of_nat_ext.
    + destruct (nat_eq_dec id i); try discriminate Hitem.
      inversion Hitem. subst di'. clear Hitem.
      exists i. exists false. exists eq_refl.
      inversion Ht. subst. exists l.
      apply inj_pairT2 in H1. subst. simpl.
      rewrite eq_dec_if_false; try reflexivity.
      intro contra. apply (f_equal to_nat) in contra.
      repeat rewrite to_nat_of_nat in contra.
      inversion contra. elim n. assumption.
Qed.

Lemma equivocator_protocol_transition_item_project_inv4
  (l : vlabel equivocator_vlsm)
  (s s' : vstate equivocator_vlsm)
  (iom oom : option message)
  (Hv: vvalid equivocator_vlsm l (s', iom))
  (Ht: vtransition equivocator_vlsm l (s', iom) = (s, oom))
  (i' : nat)
  (fi' : bool)
  (Hi' : i' < S (projT1 s'))
  : exists
    (Hi'' : i' < S (projT1 s))
    (fi'' : bool)
    (oitem : option (vtransition_item X))
    (item := {| l := l; input := iom; destination := s; output := oom |}),
    equivocator_vlsm_transition_item_project item (Existing _ i' fi') = Some (oitem, Existing _ i' fi'').
Proof.
  unfold vvalid in Hv. unfold vtransition in Ht.
  simpl in Hv. unfold_transition Ht. unfold equivocator_vlsm_transition_item_project.
  destruct l as (lx, descriptor). simpl in Hv. unfold snd in Ht.
  destruct s as (ns, bs).
  destruct s' as (n', bs').
  destruct descriptor as [sn | j is_equiv].
  - simpl in Ht. destruct (vtransition X lx (sn, iom)) as (sn', om') eqn:Htx.
    inversion Ht. subst. clear Ht. simpl in Hi'.
    assert (Hi'' : i' < S (S n')) by lia.
    exists Hi''.
    destruct (le_lt_dec (S (S n')) i'). { lia. }
    replace (of_nat_lt l) with (of_nat_lt Hi'') in *; try apply of_nat_ext. clear l.
    rewrite eq_dec_if_false.
    + exists false. exists None. reflexivity.
    + lia.
  - destruct Hv as [Hj Hv]. unfold projT1 in Ht. simpl in Hj.
    destruct (le_lt_dec (S n') j). { lia. }
    replace (of_nat_lt l) with (of_nat_lt Hj) in *; try apply of_nat_ext. clear l.
    simpl in Ht.
    destruct (vtransition X lx (bs' (of_nat_lt Hj), iom))
      as (si', om') eqn:Htx.
    simpl in Hi'.
    assert (Hi'' : i' < S (S n')) by lia.
    destruct is_equiv as [|] eqn:Hflag
    ; inversion Ht; subst ns om'; clear Ht
    ; apply inj_pairT2 in H1; subst bs.
    + destruct (le_lt_dec (S (S n')) i'). { lia. }
      destruct (nat_eq_dec (S i') (S (S n'))). { lia. }
      exists Hi''. exists false.
      exists None. reflexivity.
    + destruct (le_lt_dec (S n') i'). { lia. }
      destruct (nat_eq_dec j i').
      * subst j.
        rewrite eq_dec_if_true; try apply of_nat_ext.
        exists Hi'. exists false.
        exists (Some {| l := lx; input := iom; destination := si'; output := oom |}).
        reflexivity.
      * exists Hi'. exists false. exists None. reflexivity.
Qed.

Lemma equivocator_protocol_transition_item_project_inv5
  (l : vlabel equivocator_vlsm)
  (s s' : vstate equivocator_vlsm)
  (iom oom : option message)
  (Hv: vvalid equivocator_vlsm l (s', iom))
  (Ht: vtransition equivocator_vlsm l (s', iom) = (s, oom))
  (fi : bool)
  : exists
    (i : nat)
    (Hi : i < S (projT1 s))
    (d' : MachineDescriptor)
    (itemx : vtransition_item X)
    (item := {| l := l; input := iom; destination := s; output := oom |}),
    equivocator_vlsm_transition_item_project item (Existing _ i fi) = Some (Some itemx, d').
Proof.
  unfold equivocator_vlsm_transition_item_project.
  destruct s as (ns, bs).
  destruct s' as (ns', bs').
  unfold vtransition in Ht. unfold_transition Ht.
  unfold vvalid in Hv. simpl in Hv.
  destruct l as (lx, d). unfold snd in Ht. simpl in Hv.
  destruct d as [sn | i is_equiv].
  - simpl in Ht.
    destruct (vtransition X lx (sn, iom)) as (sn', om').
    inversion Ht. subst; clear Ht.
    apply inj_pairT2 in H1. subst.
    exists (S ns').  split. { simpl; lia. } exists (NewMachine _ sn).
    destruct (le_lt_dec (S (S ns')) (S ns')). { lia. }
    rewrite eq_dec_if_true; try reflexivity.
    eexists _; reflexivity.
  - destruct Hv as [Hi Hv].
    unfold projT1 in Ht.
    destruct (le_lt_dec (S ns') i). { lia. }
    replace (of_nat_lt l) with (of_nat_lt Hi) in *; try apply of_nat_ext. clear l.
    simpl in Ht.
    destruct (vtransition X lx (bs' (of_nat_lt Hi), iom)) as (sn', om').
    destruct is_equiv as [|]; inversion Ht; subst; clear Ht; apply inj_pairT2 in H1; subst.
    + exists (S ns'). split. { simpl; lia. }
      exists (Existing _ i true).
      destruct (le_lt_dec (S (S ns')) (S ns')). { lia. }
      rewrite eq_dec_if_true; try reflexivity.
      eexists _; reflexivity.
    + exists i. exists Hi. exists (Existing _ i false).
      destruct (le_lt_dec (S ns) i). { lia. }
      rewrite eq_dec_if_true; try reflexivity.
      eexists _; reflexivity.
Qed.

Lemma equivocator_vlsm_trace_project_protocol
  (bs : vstate equivocator_vlsm)
  (btr : list (vtransition_item equivocator_vlsm))
  (Hbtr : finite_protocol_trace_from equivocator_vlsm bs btr)
  (j : nat)
  (Hj : j < S (projT1 (last (map destination btr) bs)))
  (jf : bool)
  : exists
    (tr : list (vtransition_item X))
    (di : MachineDescriptor)
    (Htr : equivocator_vlsm_trace_project btr (Existing _ j jf) = Some (tr, di)),
    match di with
    | NewMachine _ sn =>
      vinitial_state_prop X sn
      /\ projT2 (last (map destination btr) bs) (of_nat_lt Hj) = last (map destination tr) sn
      /\ finite_protocol_trace_from X sn tr
    | Existing _ i fi =>
      exists
      (Hi : i < S (projT1 bs))
      (s := projT2 bs (of_nat_lt Hi))
      (Hlast : projT2 (last (map destination btr) bs) (of_nat_lt Hj) = last (map destination tr) s)
      ,
      finite_protocol_trace_from X s tr
    end.
Proof.
  induction Hbtr; intros.
  - exists []. simpl. exists (Existing _ j jf). exists eq_refl. exists Hj. exists eq_refl.
    constructor. apply equivocator_state_project_protocol_state in H.
    destruct s. simpl. apply H.
  - remember {| l := l; input := iom; destination := s; output := oom |} as item.
    destruct H as [[Hs' [Hiom Hv]] Ht].
    apply equivocator_state_project_protocol_state in Hs'.
    apply equivocator_state_project_protocol_message in Hiom.
    remember (last (map destination (item :: tl)) s') as lst.
    rewrite map_cons in Heqlst. rewrite unroll_last in Heqlst.
    rewrite Heqitem in Heqlst. simpl in Heqlst.
    subst lst.
    specialize (IHHbtr Hj).
    destruct IHHbtr as [tr [di [Htl Hdi]]].
    simpl. rewrite Htl.
    destruct di as [sn| i fi].
    + simpl. exists tr. exists (NewMachine _ sn). exists eq_refl. assumption.
    + destruct (equivocator_vlsm_transition_item_project item (Existing _ i fi)) as [[[item'|]di']|]
        eqn:Hitem.
      * exists (item' :: tr). exists di'. exists eq_refl.
        subst item.
        apply (equivocator_protocol_transition_item_project_inv2 l s' s) in Hitem
        ; try assumption.
        destruct Hitem as [_i [_fi [Heq [Hi [Heqitem' Hitem]]]]].
        inversion Heq. subst _i _fi. clear Heq.
        destruct Hdi as [_Hi Hlst].
        replace (of_nat_lt _Hi) with (of_nat_lt Hi) in *; try apply of_nat_ext. clear _Hi.
        simpl in Hlst. destruct Hlst as [Hlst Htr].
        repeat rewrite map_cons.
        { destruct di' as [sn'| i' fi'].
        - destruct Hitem as [Hsn' [Hv' Ht']].
          repeat rewrite unroll_last. subst. simpl.
          repeat split; try assumption. constructor; try assumption.
          repeat split; try assumption. exists None.
          replace sn' with (proj1_sig (exist _ sn' Hsn')) by reflexivity.
          apply protocol_initial_state.
        - destruct Hitem as [Hi' [Hv' Ht']]. exists Hi'.
          rewrite unroll_last. subst. simpl. exists Hlst.
          constructor; try assumption.
          repeat split; try assumption.
          destruct s' as (ns', bs'). apply Hs'.
        }
      * subst item.
        apply (equivocator_protocol_transition_item_project_inv3 l s s') in Hitem
        ; try assumption.
        destruct Hdi as [Hi [Hlst Htr]].
        destruct Hitem as [_Hi [i' [fi' [Hdi' [Hi' Heq]]]]].
        replace (of_nat_lt _Hi) with (of_nat_lt Hi) in *; try apply of_nat_ext. clear _Hi.
        exists tr. exists di'. exists eq_refl. subst.
        exists Hi'. rewrite Heq. exists Hlst. assumption.
      * apply equivocator_transition_item_project_inv_none in Hitem.
        destruct Hitem as [_i [_fi [Heq Hitem]]].
        destruct Hdi as [Hi Hdi].
        inversion Heq. subst _i _fi item. simpl in Hitem. lia.
Qed.

Lemma preloaded_equivocator_vlsm_trace_project_protocol
  (bs : vstate equivocator_vlsm)
  (btr : list (vtransition_item equivocator_vlsm))
  (Hbtr : finite_protocol_trace_from (pre_loaded_vlsm equivocator_vlsm) bs btr)
  (j : nat)
  (Hj : j < S (projT1 (last (map destination btr) bs)))
  (jf : bool)
  : exists
    (tr : list (vtransition_item X))
    (di : MachineDescriptor)
    (Htr : equivocator_vlsm_trace_project btr (Existing _ j jf) = Some (tr, di)),
    match di with
    | NewMachine _ sn =>
      vinitial_state_prop X sn
      /\ projT2 (last (map destination btr) bs) (of_nat_lt Hj) = last (map destination tr) sn
      /\ finite_protocol_trace_from (pre_loaded_vlsm X) sn tr
    | Existing _ i fi =>
      exists
      (Hi : i < S (projT1 bs))
      (s := projT2 bs (of_nat_lt Hi))
      (Hlast : projT2 (last (map destination btr) bs) (of_nat_lt Hj) = last (map destination tr) s)
      ,
      finite_protocol_trace_from (pre_loaded_vlsm X) s tr
    end.
Proof.
  induction Hbtr; intros.
  - exists []. simpl. exists (Existing _ j jf). exists eq_refl. exists Hj. exists eq_refl.
    constructor.
    apply (preloaded_equivocator_state_project_protocol_state _ s H (of_nat_lt Hj)).
  - remember {| l := l; input := iom; destination := s; output := oom |} as item.
    destruct H as [[Hs' [Hiom Hv]] Ht].
    specialize (preloaded_equivocator_state_project_protocol_state _ _ Hs') as Hs'X.
    remember
      (@last
      (@state message
         (@type message equivocator_vlsm))
      (@map
         (@transition_item message
            (@type message equivocator_vlsm))
         (@state message
            (@type message equivocator_vlsm))
         (@destination message
            (@type message equivocator_vlsm))
         (@cons
            (@transition_item message
               (@type message
                  (@pre_loaded_vlsm message
                     equivocator_vlsm))) item tl))
        s')
      as lst.
    rewrite map_cons in Heqlst. rewrite unroll_last in Heqlst.
    rewrite Heqitem in Heqlst. simpl in Heqlst.
    subst lst.
    specialize (IHHbtr Hj).
    destruct IHHbtr as [tr [di [Htl Hdi]]].
    simpl. rewrite Htl.
    destruct di as [sn| i fi].
    + simpl. exists tr. exists (NewMachine _ sn). exists eq_refl. assumption.
    + destruct (equivocator_vlsm_transition_item_project item (Existing _ i fi)) as [[[item'|]di']|]
        eqn:Hitem.
      * exists (item' :: tr). exists di'. exists eq_refl.
        subst item.
        apply (equivocator_protocol_transition_item_project_inv2 l s' s) in Hitem
        ; try assumption.
        destruct Hitem as [_i [_fi [Heq [Hi [Heqitem' Hitem]]]]].
        inversion Heq. subst _i _fi. clear Heq.
        destruct Hdi as [_Hi Hlst].
        replace (of_nat_lt _Hi) with (of_nat_lt Hi) in *; try apply of_nat_ext. clear _Hi.
        simpl in Hlst. destruct Hlst as [Hlst Htr].
        repeat rewrite map_cons.
        { destruct di' as [sn'| i' fi'].
        - destruct Hitem as [Hsn' [Hv' Ht']].
          repeat rewrite unroll_last. subst. simpl.
          repeat split; try assumption.
          apply (finite_ptrace_extend (pre_loaded_vlsm X)); try assumption.
          repeat split; try assumption.
          + exists None.
            replace sn' with (proj1_sig (exist _ sn' Hsn')) by reflexivity.
            apply (protocol_initial_state (pre_loaded_vlsm X)).
          + exists (proj1_sig (vs0 X)). apply (pre_loaded_message_protocol_prop X).
        - destruct Hitem as [Hi' [Hv' Ht']]. exists Hi'.
          rewrite unroll_last. subst. simpl. exists Hlst.
          apply (finite_ptrace_extend (pre_loaded_vlsm X)); try assumption.
          repeat split; try assumption; try apply Hs'X.
          exists (proj1_sig (vs0 X)). apply (pre_loaded_message_protocol_prop X).
        }
      * subst item.
        apply (equivocator_protocol_transition_item_project_inv3 l s s') in Hitem
        ; try assumption.
        destruct Hdi as [Hi [Hlst Htr]].
        destruct Hitem as [_Hi [i' [fi' [Hdi' [Hi' Heq]]]]].
        replace (of_nat_lt _Hi) with (of_nat_lt Hi) in *; try apply of_nat_ext. clear _Hi.
        exists tr. exists di'. exists eq_refl. subst.
        exists Hi'. rewrite Heq. exists Hlst. assumption.
      * apply equivocator_transition_item_project_inv_none in Hitem.
        destruct Hitem as [_i [_fi [Heq Hitem]]].
        destruct Hdi as [Hi Hdi].
        inversion Heq. subst _i _fi item. simpl in Hitem. lia.
Qed.

Lemma preloaded_equivocator_vlsm_trace_project_protocol_inv
  (bs : vstate equivocator_vlsm)
  (btr : list (vtransition_item equivocator_vlsm))
  (Hbtr : finite_protocol_trace_from (pre_loaded_vlsm equivocator_vlsm) bs btr)
  (i : nat)
  (Hi : i < S (projT1 bs))
  (fi : bool)
  : exists
    (fii : bool)
    (tr : list (vtransition_item X)),
    equivocator_vlsm_trace_project btr (Existing _ i fi) = Some (tr, Existing _ i fii).
Proof.
  revert fi.
  generalize dependent i.
  induction Hbtr; intros.
  - simpl. exists fi. exists []. reflexivity.
  - remember {| l := l; input := iom; destination := s; output := oom |} as item.
    simpl.
    destruct H as [[_ [_ Hv]] Ht].
    specialize
      (equivocator_protocol_transition_item_project_inv4 l s s' iom oom Hv Ht i)
      as Hitem.
    replace
      (@Build_transition_item message (@type message equivocator_vlsm) l iom s oom)
      with item in Hitem.
    destruct (Hitem false Hi) as [Hi' _].
    spec IHHbtr i Hi' fi.
    destruct IHHbtr as [fii' [tr Htr]].
    rewrite Htr.
    spec Hitem fii' Hi.
    destruct Hitem as [_ [fi'' [oitem Hoitem]]].
    rewrite Hoitem. exists fi''.
    destruct oitem as [itemx|].
    + exists (itemx :: tr). reflexivity.
    + exists tr. reflexivity.
Qed.

Lemma preloaded_equivocator_vlsm_project_protocol_trace
  (bs : vstate equivocator_vlsm)
  (btr : list (vtransition_item equivocator_vlsm))
  (Hbtr : finite_protocol_trace (pre_loaded_vlsm equivocator_vlsm) bs btr)
  (j : nat)
  (Hj : j < S (projT1 (last (map destination btr) bs)))
  (jf : bool)
  : exists
    (tr : list (vtransition_item X))
    (di : MachineDescriptor)
    (Htr : equivocator_vlsm_trace_project btr (Existing _ j jf) = Some (tr, di)),
    match di with
    | NewMachine _ sn =>
      exists
      (Hlast : projT2 (last (map destination btr) bs) (of_nat_lt Hj) = last (map destination tr) sn),
      finite_protocol_trace (pre_loaded_vlsm X) sn tr
    | Existing _ i fi =>
      exists
      (Hi : i < S (projT1 bs))
      (s := projT2 bs (of_nat_lt Hi))
      (Hlast : projT2 (last (map destination btr) bs) (of_nat_lt Hj) = last (map destination tr) s)
      ,
      finite_protocol_trace (pre_loaded_vlsm X) s tr
    end.
Proof.
  destruct Hbtr as [Hbtr Hinit].
  destruct (preloaded_equivocator_vlsm_trace_project_protocol bs btr Hbtr j Hj jf)
    as [tr [di [Hproject Hdi]]].
  exists tr.
  exists di.
  exists Hproject.
  destruct di as [sn | i fi].
  - destruct Hdi as [Hsn [Hlst Htr]].
    repeat split; assumption.
  - destruct Hdi as [Hi [Hlast Htr]].
    exists Hi. exists Hlast. split; try assumption.
    destruct Hinit as [Hzero Hinit].
    destruct bs as [ns bs]; simpl in *. subst ns.
    assert (Hzero : i = 0) by lia.
    subst i.
    replace (of_nat_lt Hi) with (@F1 0); try assumption.
    rewrite <- (of_nat_to_nat_inv (@F1 0)).
    apply of_nat_ext.
Qed.

Lemma equivocator_vlsm_trace_project_inv
  (tr: list transition_item)
  (Hntr : tr <> [])
  (j: nat)
  (fj : bool)
  (HtrX: equivocator_vlsm_trace_project tr (Existing _ j fj) <> None)
  (is: state)
  : j < S (projT1 (last (map destination tr) is)).
Proof.
  apply exists_last in Hntr.
  destruct Hntr as [suffix [x Heq]]. subst tr.
  destruct (equivocator_vlsm_trace_project (suffix ++ [x]) (Existing _ j fj)) eqn:Htr
  ; try (elim HtrX; reflexivity).
  clear HtrX. destruct p as (trX, d).
  apply equivocator_vlsm_trace_project_app in Htr.
  destruct Htr as [dmiddle [_ [lx [_ [Hx _]]]]].
  rewrite map_app. simpl. rewrite last_last.
  remember (Existing _ j fj) as dj.
  simpl in *.
  destruct (equivocator_vlsm_transition_item_project x dj)
    as [(_x, _dmiddle)|]
    eqn:Hx'
  ; try discriminate Hx.
  destruct _x as [itemx|]; inversion Hx; subst lx _dmiddle; clear Hx.
  - subst. destruct x. unfold equivocator_vlsm_transition_item_project in Hx'.
    destruct l. destruct destination.
    destruct (le_lt_dec (S x) j); try discriminate Hx'.
    assumption.
  - subst. unfold equivocator_vlsm_transition_item_project in Hx'. destruct x. destruct l. destruct destination.
    destruct (le_lt_dec (S x) j); try discriminate Hx'.
    assumption.
Qed.

Lemma preloaded_equivocator_vlsm_trace_project_protocol_inv2
  (is: state)
  (tr: list transition_item)
  (Hntr : tr <> [])
  (Htr: finite_protocol_trace_from (pre_loaded_vlsm equivocator_vlsm) is tr)
  (j : nat)
  (fj : bool)
  (di : MachineDescriptor)
  (trX: list (vtransition_item X))
  (HtrX: equivocator_vlsm_trace_project tr (Existing _ j fj) = Some (trX, di))
  : exists (Hj : j < S (projT1 (last (map destination tr) is))),
    match di with
    | NewMachine _ sn =>
      exists
      (Hsn : vinitial_state_prop X sn)
      (Hlst : projT2 (last (map destination tr) is) (of_nat_lt Hj) = last (map destination trX) sn),
      finite_protocol_trace_from (pre_loaded_vlsm X) sn trX
    | Existing _ i fi =>
      exists
      (Hi : i < S (projT1 is))
      (Hlst : projT2 (last (map destination tr) is) (of_nat_lt Hj) = last (map destination trX) (projT2 is (of_nat_lt Hi))),
      finite_protocol_trace_from (pre_loaded_vlsm X) (projT2 is (of_nat_lt Hi)) trX
    end.
Proof.
  specialize (equivocator_vlsm_trace_project_inv _ Hntr j fj) as Hj.
  spec Hj. { rewrite HtrX. intro contra. discriminate contra. }
  spec Hj is.
  exists Hj.
  destruct
    (preloaded_equivocator_vlsm_trace_project_protocol _ _ Htr _ Hj fj)
    as [trX' [di' [HtrX' Hdi']]].
  rewrite HtrX in HtrX'.
  inversion HtrX'. subst di' trX'.
  destruct di as [sn | i fi].
  - destruct Hdi' as [Hsn [Hlst Hptr]].
    repeat split; assumption.
  - destruct Hdi' as [Hi [Hlst Hptr]].
    exists Hi. exists Hlst. assumption.
Qed.

Lemma preloaded_equivocator_vlsm_protocol_trace_project_inv2
  (is: state)
  (tr: list transition_item)
  (Hntr : tr <> [])
  (Htr: finite_protocol_trace (pre_loaded_vlsm equivocator_vlsm) is tr)
  (j : nat)
  (fj : bool)
  (di : MachineDescriptor)
  (trX: list (vtransition_item X))
  (HtrX: equivocator_vlsm_trace_project tr (Existing _ j fj) = Some (trX, di))
  : exists
    (Hj : j < S (projT1 (last (map destination tr) is))),
    match di with
    | NewMachine _ sn =>
      exists
      (Hlast : projT2 (last (map destination tr) is) (of_nat_lt Hj) = last (map destination trX) sn),
      finite_protocol_trace (pre_loaded_vlsm X) sn trX
    | Existing _ i fi =>
      exists
      (Hi : i < S (projT1 is))
      (s := projT2 is (of_nat_lt Hi))
      (Hlast : projT2 (last (map destination tr) is) (of_nat_lt Hj) = last (map destination trX) s)
      ,
      finite_protocol_trace (pre_loaded_vlsm X) s trX
    end.
Proof.
  specialize (equivocator_vlsm_trace_project_inv _ Hntr j fj) as Hj.
  spec Hj. { rewrite HtrX. intro contra. discriminate contra. }
  spec Hj is.
  exists Hj.
  destruct
    (preloaded_equivocator_vlsm_project_protocol_trace _ _ Htr _ Hj fj)
    as [trX' [di' [HtrX' Hdi]]].
  rewrite HtrX in HtrX'.
  inversion HtrX'. subst di' trX'.  clear HtrX'.
  assumption.
Qed.

Lemma equivocator_transition_item_project_inv_messages
  (item : vtransition_item equivocator_vlsm)
  (itemX : vtransition_item X)
  (idescriptor odescriptor : MachineDescriptor)
  (Hitem : equivocator_vlsm_transition_item_project item idescriptor = Some (Some itemX, odescriptor))
  : exists
    (i : nat)
    (is_equiv : bool)
    (Hdescriptor : idescriptor = Existing _ i is_equiv),
    input item = input itemX /\ output item = output itemX.
Proof.
  unfold equivocator_vlsm_transition_item_project in Hitem.
  destruct idescriptor as [s|j fj]; try discriminate Hitem.
  exists j. exists fj. exists eq_refl.
  destruct item.
  destruct destination as (n, bs).
  destruct l as (lx, descriptorx).
  destruct (le_lt_dec (S n) j); try discriminate Hitem.
  destruct descriptorx as [s | i' [|]] eqn:Hl; simpl.
  - destruct (nat_eq_dec (S j) (S n)); try discriminate Hitem.
    inversion Hitem. subst. clear Hitem. repeat split; reflexivity.
  - destruct (nat_eq_dec (S j) (S n)); try discriminate Hitem.
    inversion Hitem. subst. repeat split; reflexivity.
  - destruct (nat_eq_dec i' j); try discriminate Hitem.
    inversion Hitem. subst. repeat split; reflexivity.
Qed.

Lemma equivocator_vlsm_trace_project_output_reflecting
  (tr: list (vtransition_item equivocator_vlsm))
  (trX: list (vtransition_item X))
  (j i : MachineDescriptor)
  (HtrX: equivocator_vlsm_trace_project tr j = Some (trX, i))
  (m : message)
  (Hjbs: Exists (fun elem : vtransition_item X => output elem = Some m) trX)
  : Exists (fun elem : transition_item => output elem = Some m) tr.
Proof.
  generalize dependent i. generalize dependent trX.
  induction tr; intros.
  - inversion HtrX. subst. inversion Hjbs.
  - simpl in HtrX.
    destruct (equivocator_vlsm_trace_project tr j) as [(trX', i')|]
      eqn:Htr; try discriminate HtrX.
    specialize (IHtr trX').
    destruct (equivocator_vlsm_transition_item_project a i') as [[[item'|] i'']|]
      eqn:Hitem'; try discriminate HtrX
    ; inversion HtrX; subst; clear HtrX.
    + apply equivocator_transition_item_project_inv_messages in Hitem'.
      destruct Hitem' as [_ [_ [_ [_ Ha]]]].
      inversion Hjbs; subst.
      * left. rewrite Ha. assumption.
      * specialize (IHtr H0 i' eq_refl). right. assumption.
    + specialize (IHtr Hjbs i' eq_refl). right. assumption.
Qed.

End equivocator_vlsm_projections.

Section equivocator_vlsm_has_been_sent.

Context
  {message : Type}
  (X : VLSM message)
  (equivocator_vlsm := equivocator_vlsm X)
  (MachineDescriptor := MachineDescriptor X)
  .

Lemma preloaded_equivocator_vlsm_trace_project_protocol_item
  (bs : vstate equivocator_vlsm)
  (btr : list (vtransition_item equivocator_vlsm))
  (Hbtr : finite_protocol_trace_from (pre_loaded_vlsm equivocator_vlsm) bs btr)
  (bitem : vtransition_item equivocator_vlsm)
  (Hitem : In bitem btr)
  (fi : bool)
  : exists
    (d d' : MachineDescriptor)
    (item : vtransition_item X)
    (Hitem : equivocator_vlsm_transition_item_project _ bitem d = Some (Some item, d'))
    (tr : list (vtransition_item X))
    (dfinal dfirst : MachineDescriptor)
    (Htr : equivocator_vlsm_trace_project _ btr dfinal = Some (tr, dfirst)),
    In item tr.
Proof.
  apply in_split in Hitem.
  destruct Hitem as [bprefix [bsuffix Heq]].
  subst btr.
  apply (finite_protocol_trace_from_app_iff (pre_loaded_vlsm equivocator_vlsm)) in Hbtr.
  destruct Hbtr as [Hbprefix Hbsuffix].
  remember
    (@last
    (@state message
       (@type message (@pre_loaded_vlsm message equivocator_vlsm)))
    (@map
       (@transition_item message
          (@type message
             (@pre_loaded_vlsm message equivocator_vlsm)))
       (@state message
          (@type message
             (@pre_loaded_vlsm message equivocator_vlsm)))
       (@Common.destination message
          (@type message
             (@pre_loaded_vlsm message equivocator_vlsm)))
       bprefix) bs)
    as lst.
  inversion Hbsuffix. subst s' tl.
  destruct H3 as [[_ [_ Hv]] Ht].
  specialize
    (equivocator_protocol_transition_item_project_inv5 _ l s lst iom oom Hv Ht) as Hpitem.
  replace (@Build_transition_item message (@type message (@Common.equivocator_vlsm message X)) l iom s oom)
    with bitem in Hpitem.
  rewrite H in *.
  destruct (Hpitem false) as [i [Hi [d' [itemx _Hitemx]]]].
  pose (dfinal := Existing X i false).
  destruct
    (preloaded_equivocator_vlsm_trace_project_protocol_inv _ _ _ H2 _ Hi false)
    as [fsuffix [suffix Hsuffix]].
  specialize (Hpitem fsuffix).
  destruct Hpitem as [_i [_Hi [_d' [_itemx Hitemx]]]].
  destruct
    (equivocator_vlsm_transition_item_project_some_inj _ Hitemx _Hitemx)
    as [H_i [H_itemx H_d']].
  subst _i _itemx _d'. clear _Hitemx. clear _Hi.
  exists (Existing _ i fsuffix). exists d'. exists itemx. exists Hitemx.
  remember (Existing _ i fsuffix) as dsuffix.
  assert (Hitem : equivocator_vlsm_trace_project _ [bitem] dsuffix = equivocator_vlsm_trace_project _ [bitem] dsuffix)
    by reflexivity.
  remember [bitem] as lbitem. rewrite Heqlbitem in Hitem at 2.
  simpl in Hitem.
  rewrite Hitemx in Hitem.
  specialize
    (equivocator_vlsm_trace_project_app_inv _ _ _ _ _ _ _ _ Hitem Hsuffix)
    as Hsuffix'.
  rewrite <- H in Hitemx.
  destruct
    (equivocator_protocol_transition_item_project_inv2 _ l lst s iom oom Hv Ht _ _ _ Hitemx)
    as [_i [_fi [_Hdsuffix [_Hi [Heqitemx Hd']]]]].
  rewrite Heqdsuffix in _Hdsuffix. inversion _Hdsuffix. subst _i _fi. clear _Hdsuffix.
  replace (of_nat_lt _Hi) with (of_nat_lt Hi) in *; try apply of_nat_ext. clear _Hi.
  destruct d' as [sn | id fd].
  - destruct Hd' as [Hsn [Hvsn Htsn]].
    assert
      (Hprefix : equivocator_vlsm_trace_project _ bprefix (NewMachine _ sn) = Some ([], NewMachine _ sn))
      by apply equivocator_vlsm_trace_project_on_hard_fork.
    specialize
      (equivocator_vlsm_trace_project_app_inv _ _ _ _ _ _ _ _ Hprefix Hsuffix')
      as Htr.
    subst lbitem.
    simpl in Htr.
    exists (itemx :: suffix).
    exists dfinal. exists (NewMachine _ sn). exists Htr. left. reflexivity.
  - destruct Hd' as [Hid [Hvs' Hts']].
    subst lst.
    destruct
      (preloaded_equivocator_vlsm_trace_project_protocol _ _ _ Hbprefix id Hid fd)
      as [prefix [dfirst [Hprefix _]]].
    specialize
      (equivocator_vlsm_trace_project_app_inv _ _ _ _ _ _ _ _ Hprefix Hsuffix')
      as Htr.
    subst lbitem.
    simpl in Htr.
    exists (prefix ++ itemx :: suffix).
    exists dfinal. exists dfirst. exists Htr.
    apply in_app_iff. right. left. reflexivity.
Qed.

Lemma equivocator_vlsm_trace_project_output_reflecting_inv
  (is: vstate equivocator_vlsm)
  (tr: list (vtransition_item equivocator_vlsm))
  (Htr: finite_protocol_trace_from (pre_loaded_vlsm equivocator_vlsm) is tr)
  (m : message)
  (Hbbs : Exists (fun elem : transition_item => output elem = Some m) tr)
  : exists
    (j i : MachineDescriptor)
    (trX: list (vtransition_item X))
    (HtrX: equivocator_vlsm_trace_project _ tr j = Some (trX, i))
    ,
    Exists (fun elem : vtransition_item X => output elem = Some m) trX.
Proof.
  apply Exists_exists in Hbbs.
  destruct Hbbs as [item [Hin Houtput]].
  destruct
    (preloaded_equivocator_vlsm_trace_project_protocol_item _ _ Htr _ Hin false)
    as [i [i' [itemx [Hitemx [trx [ifinal [ifirst [Htrx Hinx]]]]]]]].
  exists ifinal. exists ifirst. exists trx. exists Htrx.
  apply Exists_exists. exists itemx. split; try assumption.
  apply equivocator_transition_item_project_inv_messages in Hitemx.
  destruct Hitemx as [_ [_ [_ [_ Hitemx]]]].
  simpl in *.
  rewrite Hitemx in Houtput. assumption.
Qed.

Section trace_mixer.

Definition preloaded_protocol_equivocator_vlsm_trace_oproject
  (is : vstate equivocator_vlsm)
  (btr : list (vtransition_item equivocator_vlsm))
  (nj : Fin.t (S (projT1 (last (map destination btr) is))))
  : option (vstate X * list (vtransition_item X))
  :=
  let (j, _) := to_nat nj in
  match equivocator_vlsm_trace_project _ btr (Existing _ j false) with
  | Some (trx, NewMachine _ sn) => Some (sn, trx)
  | Some (trx, Existing _ i _) =>
    match (le_lt_dec (S (projT1 is)) i) with
    | left _ => None
    | right Hi => Some (projT2 is (of_nat_lt Hi), trx)
    end
  | _ => None
  end.

Definition equivocator_vlsm_projector_type
  (is : vstate equivocator_vlsm)
  (btr : list (vtransition_item equivocator_vlsm))
  : Type
  :=
  forall
    (nj : Fin.t (S (projT1 (last (map destination btr) (is))))),
    option (vstate X * list (vtransition_item X)).

Definition equivocator_projection_update
  (is : vstate equivocator_vlsm)
  (btr : list (vtransition_item equivocator_vlsm))
  (projector : equivocator_vlsm_projector_type is btr)
  (ni : Fin.t (S (projT1 (last (map destination btr) is))))
  (ni_trace : option (vstate X * list (vtransition_item X)))
  (nj : Fin.t (S (projT1 (last (map destination btr) is))))
  : option (vstate X * list (vtransition_item X))
  := 
  if Fin.eq_dec ni nj then ni_trace else projector nj.

Definition preloaded_protocol_equivocator_vlsm_trace_oproject_update
  (is : vstate equivocator_vlsm)
  (btr : list (vtransition_item equivocator_vlsm))
  (ni : Fin.t (S (projT1 (last (map destination btr) is))))
  (isi : vstate X)
  (tri : list (vtransition_item X))
  : equivocator_vlsm_projector_type is btr
  :=
  equivocator_projection_update is btr
    (preloaded_protocol_equivocator_vlsm_trace_oproject is btr)
    ni (Some (isi, tri)).

Definition projection_traces
  (is : vstate equivocator_vlsm)
  (btr : list (vtransition_item equivocator_vlsm))
  (projector : equivocator_vlsm_projector_type is btr)
  (n := projT1 (last (map destination btr) is))
  : list (vstate X * list (vtransition_item X))
  :=
  map_option projector (fin_t_listing (S n)).

Definition projection_traces_replace_one
  (is : vstate equivocator_vlsm)
  (btr : list (vtransition_item equivocator_vlsm))
  (ni : Fin.t (S (projT1 (last (map destination btr) is))))
  (isi : vstate X)
  (tri : list (vtransition_item X))
  : list (vstate X * list (vtransition_item X))
  :=
  projection_traces is btr
    (preloaded_protocol_equivocator_vlsm_trace_oproject_update is btr ni isi tri).

Lemma projection_traces_replace_one_length
  (is : vstate equivocator_vlsm)
  (btr : list (vtransition_item equivocator_vlsm))
  (Hbtr : finite_protocol_trace (pre_loaded_vlsm equivocator_vlsm) is btr)
  (n := projT1 (last (map destination btr) is))
  (ni : Fin.t (S n))
  (isi : vstate X)
  (tri : list (vtransition_item X))
  : length (projection_traces_replace_one is btr ni isi tri) = S n.
Proof.
  unfold projection_traces_replace_one.
  unfold projection_traces.
  rewrite map_option_length; try apply fin_t_listing_length.
  apply Forall_forall.
  intros nj Hnj.
  unfold preloaded_protocol_equivocator_vlsm_trace_oproject_update.
  unfold equivocator_projection_update.
  destruct (Fin.eq_dec ni nj).
  - rewrite eq_dec_if_true; try assumption.
    intro contra. discriminate contra.
  - rewrite eq_dec_if_false; try assumption.
    unfold preloaded_protocol_equivocator_vlsm_trace_oproject.
    destruct (to_nat nj) as [j Hj] eqn:Heqnj.
    destruct
      (preloaded_equivocator_vlsm_project_protocol_trace _ _ _ Hbtr _ Hj false)
      as [trX [di [Hproject Hdi]]].
    rewrite Hproject.
    destruct di as [sn | i fi].
    + intro contra. discriminate contra.
    + destruct Hdi as [Hi [HlstX [HtrX]]].
      destruct (le_lt_dec (S (projT1 is)) i). { lia. }
      intro contra. discriminate contra.
Qed.

Context
  (goal_state : vstate equivocator_vlsm)
  (n := projT1 goal_state)
  (traces : list (vstate X * list (vtransition_item X)))
  (Hn : length traces = S n)
  (Htraces : Forall
    (fun trace => 
      finite_protocol_trace (pre_loaded_vlsm X) (fst trace) (snd trace)
    )
    traces)
  (Hne_traces : Forall (fun trace => snd trace <> []) traces)
  (Hs
    : forall i : Fin.t (S n),
      let (ni, _) := to_nat i in
      match nth ni traces (proj1_sig (vs0 X), []) with (isi, tri) =>
        last (map destination tri) isi = projT2 goal_state i
      end
  )
  .

Definition lift_trace_to_equivocator
  (start : vstate equivocator_vlsm)
  (i := projT1 start)
  (isi : vstate X)
  (tri : list (vtransition_item X))
  : list (vtransition_item equivocator_vlsm)
  :=
  match tri with
  | [] => []
  | {| l := lx; input := iom; output := oom; destination := sx |} :: tri' =>
    {| l := mk_label _ lx (NewMachine _ isi); input := iom; output := oom; destination := equivocator_state_extend _ start sx |}
    :: fold_right
      (fun lab tr =>
        match lab with {| l := lx; input := iom; output := oom; destination := sx |} =>
          {| l := mk_label _ lx  (Existing _ (S i) false); input := iom; output := oom; destination := equivocator_state_extend _ start sx |}
          :: tr
        end)
      [] tri
  end.

Definition lift_traces_to_equivocator
  : list (vtransition_item equivocator_vlsm)
  :=
  fst
    (fold_left
      (fun rez tracei =>
        let isxi := fst tracei in
        let trxi := snd tracei in
        match rez with (tr, s) =>
          let tri := lift_trace_to_equivocator s isxi trxi in
          (tr ++ tri, last (map destination tri) s)
        end
      ) traces ([], proj1_sig (vs0 equivocator_vlsm))
    ).

Lemma lift_traces_to_equivocator_protocol_trace
  : finite_protocol_trace (pre_loaded_vlsm equivocator_vlsm)
          (proj1_sig (vs0 equivocator_vlsm)) lift_traces_to_equivocator.
Admitted.

Lemma lift_traces_to_equivocator_last
  : last
    (map destination lift_traces_to_equivocator)
    (mk_singleton_state _ (fst (nth 0 traces (proj1_sig (vs0 X), []))))
    = goal_state.
Admitted.

End trace_mixer.


Section has_been_sent_lifting.

Context
  {Hbs : has_been_sent_capability X}
  .

Definition equivocator_has_been_sent
  (s : vstate equivocator_vlsm)
  (m : message)
  : bool
  :=
  let (n, bs) := s in
  existsb
    (fun i => has_been_sent X (bs i) m)
    (fin_t_listing (S n)).

Lemma equivocator_has_been_sent_consistency
  (s : vstate equivocator_vlsm)
  (Hs : protocol_state_prop (pre_loaded_vlsm equivocator_vlsm) s)
  (m : message)
  : selected_messages_consistency_prop equivocator_vlsm output s m.  
Proof.
  split.
  - intros [bis [btr [Hbtr [Hlast Hsome]]]].
    destruct (equivocator_vlsm_trace_project_output_reflecting_inv _ _ (proj1 Hbtr) _ Hsome)
      as [j [i [trX [Hproject Hsomex]]]].
    destruct j as [sj | j fj]
    ; try
      (rewrite equivocator_vlsm_trace_project_on_hard_fork in Hproject
      ; inversion Hproject; subst; inversion Hsomex
      ).
    assert (Hntr : btr <> []) by (intro contra; subst; inversion Hsome).
    specialize
      (preloaded_equivocator_vlsm_protocol_trace_project_inv2 _ _ _ Hntr Hbtr _ _ _ _ Hproject)
      as HpreX.
    simpl in *.
    rewrite Hlast in HpreX. destruct HpreX as [Hj Hi].
    assert (Hsj : protocol_state_prop (pre_loaded_vlsm X) (projT2 s (of_nat_lt Hj))).
    { simpl.  simpl in *.
      specialize
        (finite_ptrace_last_pstate (pre_loaded_vlsm equivocator_vlsm) _ _  (proj1 Hbtr))
        as Hpbs.
      simpl in *.
      rewrite Hlast in Hpbs.
      apply (preloaded_equivocator_state_project_protocol_state _ _ Hpbs).
    }
    assert (Hall : selected_message_exists_in_all_traces X output (projT2 s (of_nat_lt Hj)) m).
    { apply has_been_sent_consistency; try assumption.
      destruct i as [sn | i fi].
      - destruct Hi as [Hlastx HtrX].
        symmetry in Hlastx.
        exists sn. exists trX. exists HtrX. exists Hlastx. assumption.
      - destruct Hi as [Hi [Hlastx HtrX]].
        exists (projT2 bis (of_nat_lt Hi)). exists trX. exists HtrX.
        symmetry in Hlastx. exists Hlastx.
        assumption.
    }
    clear -Hall MachineDescriptor equivocator_vlsm.
    intros bis btr Hbtr Hlast.
    subst s.
    destruct
      (preloaded_equivocator_vlsm_project_protocol_trace _ _ _ Hbtr _ Hj false)
      as [trX [di [Hproject Hdi]]].
    apply
      (equivocator_vlsm_trace_project_output_reflecting _  _ _ _ _ Hproject m).
    destruct di as [sn | i fi].
    + destruct Hdi as [Hlast HtrX].
      symmetry in Hlast.
      apply (Hall _ _ HtrX Hlast).
    + destruct Hdi as [Hi [Hlast HtrX]].
      symmetry in Hlast.
      apply (Hall _ _ HtrX Hlast).
  - intro Hall.
    destruct Hs as [om Hs].
    apply (protocol_is_trace (pre_loaded_vlsm equivocator_vlsm)) in Hs.
    destruct Hs as [Hinit | [is [tr [Htr [Hlast _]]]]]
    ; try (elim (selected_message_exists_in_all_traces_initial_state equivocator_vlsm s Hinit output m)
      ; assumption).
    exists is. exists tr. exists Htr.
    assert (Hlst := last_error_destination_last _ _ Hlast is).
    exists Hlst.
    apply (Hall _ _ Htr Hlst).
Qed.

Lemma equivocator_proper_sent
  (s : vstate equivocator_vlsm)
  (Hs : protocol_state_prop (pre_loaded_vlsm equivocator_vlsm) s)
  (m : message)
  : has_been_sent_prop equivocator_vlsm equivocator_has_been_sent s m.
Proof.
  split.
  - intro Hbbs. intro start; intros.
    destruct s as (n, bs).
    apply existsb_exists in Hbbs.
    destruct Hbbs as [j [_ Hjbs]].
    apply (proper_sent X) in Hjbs
    ; try apply (preloaded_equivocator_state_project_protocol_state _ _ Hs j).
    specialize (preloaded_equivocator_vlsm_project_protocol_trace _ start tr Htr) as Hpre.
    assert (Hj := of_nat_to_nat_inv j).
    simpl in *.
    rewrite Hlast in Hpre.
    simpl in Hpre.
    destruct (to_nat j) as [nj Hnj]. simpl in Hj.
    specialize (Hpre nj Hnj false).
    destruct Hpre as [trX [di [Hproject Hdi]]].
    destruct di as [sn | i fi].
    + destruct Hdi as [HlastX HtrX].
      symmetry in HlastX.
      rewrite Hj in HlastX.
      spec Hjbs sn trX HtrX HlastX.
      apply equivocator_vlsm_trace_project_output_reflecting with trX (Existing _ nj false) (NewMachine _ sn)
      ; assumption.
    + destruct Hdi as [Hi [HlastX HtrX]].
      symmetry in HlastX.
      rewrite Hj in HlastX.
      spec Hjbs (projT2 start (of_nat_lt Hi)) trX HtrX HlastX.
      apply equivocator_vlsm_trace_project_output_reflecting with trX (Existing _ nj false) (Existing _ i fi)
      ; assumption.
  - intro Hbbs. assert (Hbbs' := Hbbs).
    destruct Hs as [om Hs].
    apply (protocol_is_trace (pre_loaded_vlsm equivocator_vlsm)) in Hs.
    destruct Hs as [Hinit | [is [tr [Htr [Hlast _]]]]]
    ; try (elim (selected_message_exists_in_all_traces_initial_state equivocator_vlsm s Hinit output m)
      ; assumption).
    specialize (lift_traces_to_equivocator_protocol_trace s) as Hlift_protocol_trace.
    assert (Hlst := last_error_destination_last _ _ Hlast is).
    spec Hbbs is tr Htr Hlst.
    destruct
      (equivocator_vlsm_trace_project_output_reflecting_inv _ _ (proj1 Htr) _ Hbbs)
      as [j [i [trX [HtrX Hjbs]]]].
    assert (Hntr : tr <> []) by (intro contra; subst; inversion Hbbs).
    destruct j as [sj | j fj]
    ; try
      (rewrite equivocator_vlsm_trace_project_on_hard_fork in HtrX
      ; inversion HtrX; subst; inversion Hjbs
      ).
    specialize
      (preloaded_equivocator_vlsm_protocol_trace_project_inv2 _ _ _ Hntr Htr _ _ _ _ HtrX)
      as HpreX.
    simpl in *.
    rewrite Hlst in HpreX. simpl in HpreX.
    destruct HpreX as [Hj Hi].
    unfold equivocator_has_been_sent.
    destruct s as (ns, bs). simpl in Hlift_protocol_trace.
    apply existsb_exists.
    exists (of_nat_lt Hj). split; try apply fin_t_full.
    assert (Hbsj : protocol_state_prop (pre_loaded_vlsm X) (bs (of_nat_lt Hj))).
    { simpl in *.
      specialize
        (finite_ptrace_last_pstate (pre_loaded_vlsm equivocator_vlsm) _ _  (proj1 Htr))
        as Hpbs.
      simpl in *.
      rewrite Hlst in Hpbs.
      apply (preloaded_equivocator_state_project_protocol_state _ _ Hpbs).
    }
    apply (proper_sent X); try assumption.
    apply has_been_sent_consistency; try assumption.
    destruct i as [sn | i fi].
    + destruct Hi as [Hlstx Htrx].
      exists sn. exists trX. exists Htrx. symmetry in Hlstx. exists Hlstx.
      assumption.
    + destruct Hi as [Hi [Hlstx Htrx]].
      exists (projT2 is (of_nat_lt Hi)).
      exists trX. exists Htrx.
      symmetry in Hlstx. exists Hlstx.
      assumption.
Qed.

Lemma equivocator_proper_not_sent
  (s : vstate equivocator_vlsm)
  (Hs : protocol_state_prop (pre_loaded_vlsm equivocator_vlsm) s)
  (m : message)
  (equivocator_has_not_been_sent := fun s m => negb (equivocator_has_been_sent s m))
  : has_not_been_sent_prop equivocator_vlsm equivocator_has_not_been_sent s m.
Proof.
  apply has_been_sent_consistency_proper_not_sent.
  - apply equivocator_proper_sent. assumption.
  - apply equivocator_has_been_sent_consistency. assumption.
Qed.

Definition equivocator_has_been_sent_capability
  : has_been_sent_capability equivocator_vlsm
  :=
  {|
    has_been_sent := equivocator_has_been_sent;
    proper_sent := equivocator_proper_sent;
    proper_not_sent := equivocator_proper_not_sent   
  |}.

End has_been_sent_lifting.

Section computable_sent_messages_lifting.


Context
  {Hsent_messages : computable_sent_messages X}
  (message_eq : EqDec message)
  (Hbeen_sent_X := @computable_sent_messages_has_been_sent_capability message X Hsent_messages message_eq)
  .

Definition equivocator_sent_messages_fn
  (s : vstate equivocator_vlsm)
  : set message
  :=
  fold_right (set_union eq_dec) []
    (map (fun i => sent_messages_fn X (projT2 s i)) (fin_t_listing (S (projT1 s)))).

Lemma equivocator_sent_messages_full
  (s : vstate equivocator_vlsm)
  (Hs : protocol_state_prop (pre_loaded_vlsm equivocator_vlsm) s)
  (m : message)
  : In m (equivocator_sent_messages_fn s)
  <-> exists (sm : sent_messages equivocator_vlsm s), proj1_sig sm = m.
Proof.
  specialize (preloaded_equivocator_state_project_protocol_state _ _ Hs) as HpsX.
  split.
  - intro Hin. apply set_union_in_iterated in Hin. apply Exists_exists in Hin.
    destruct Hin as [msgsi [Hmsgsi Hin]]. apply in_map_iff in Hmsgsi.
    destruct Hmsgsi as [i [Heq _]]. subst.
    spec HpsX i.
    apply (sent_messages_full X) in Hin; try assumption.
    destruct Hin as [[m' Hm] Heq]. simpl in Heq. subst m'.
    apply (sent_messages_consistency X) in Hm; try assumption.
    destruct Hs as [om Hs].
    apply (protocol_is_trace (pre_loaded_vlsm equivocator_vlsm)) in Hs.
    destruct Hs as [Hs | [is [tr [Htr [Hlast _]]]]].
    + specialize (Hm (projT2 s i) []).
      spec Hm.
      { split.
        - apply (finite_ptrace_empty (pre_loaded_vlsm X)). assumption.
        - destruct Hs as [Hzero His].
          destruct s as [n s]. simpl in *. subst n.
          dependent destruction i; try inversion i.
          assumption.
      }
      specialize (Hm eq_refl). inversion Hm.
    + specialize (last_error_destination_last _ _ Hlast is) as Hlst. clear Hlast.
      assert (Hinv := of_nat_to_nat_inv i).
      destruct (to_nat i) as [ni Hi]. simpl in Hinv. subst i.
      assert (Hbm : selected_message_exists_in_some_traces equivocator_vlsm output s m)
      ; try (exists (exist _ m Hbm); reflexivity).
      exists is. exists tr. exists Htr. exists Hlst.
      subst s.
      destruct
        (preloaded_equivocator_vlsm_project_protocol_trace _ _ _ Htr _ Hi false)
        as [trX [di Hdi]].
      destruct di as [sn | i fi].
      * destruct Hdi as [Hproject [Hlast HtrX]].
        apply equivocator_vlsm_trace_project_output_reflecting with trX (Existing _ ni false) (NewMachine _ sn)
        ; try assumption.
        symmetry in Hlast.
        apply (Hm _ _ HtrX Hlast).
      * destruct Hdi as [Hproject [Hi' [Hlast HtrX]]].
        apply equivocator_vlsm_trace_project_output_reflecting with trX (Existing _ ni false) (Existing _ i fi)
        ; try assumption.
        symmetry in Hlast.
        apply (Hm _ _ HtrX Hlast).
  - intros [[m' Hm] Heq]. simpl in Heq. subst m'.
    destruct Hm as [is [tr [Htr [Hlst Hexists]]]].
    destruct
      (equivocator_vlsm_trace_project_output_reflecting_inv _ _ (proj1 Htr) _ Hexists)
      as [ifinal [istart [trX [Hproject HexistsX]]]].
    assert (Hntr : tr <> []) by (intro contra; subst; inversion Hexists).
    destruct ifinal as [sfinal | i ffinal]
    ; try (
      rewrite equivocator_vlsm_trace_project_on_hard_fork in Hproject
      ; inversion Hproject; subst; inversion HexistsX
      ).
    specialize
      (preloaded_equivocator_vlsm_protocol_trace_project_inv2 _ _ _ Hntr Htr _ _ _ _ Hproject)
      as HpreX.
    simpl in *.
    rewrite Hlst in HpreX.
    destruct HpreX as [Hi Histart].
    apply set_union_in_iterated. apply Exists_exists.
    exists (sent_messages_fn X (projT2 s (of_nat_lt Hi))).
    split.
    + apply in_map_iff. exists (of_nat_lt Hi).
      split; try reflexivity. apply fin_t_full.
    + apply (sent_messages_full X); try apply HpsX.
      assert (Hm : selected_message_exists_in_some_traces X output (projT2 s (of_nat_lt Hi)) m)
      ; try (exists (exist _ m Hm); reflexivity).
      destruct istart as [sstart | istart fstart].
      * destruct Histart as [Hlast HtrX].
        exists sstart. exists trX. exists HtrX. symmetry in Hlast. exists Hlast.
        assumption.
      * destruct Histart as [Histart [Hlast HtrX]].
        exists (projT2 is (of_nat_lt Histart)).
        exists trX. exists HtrX.
        symmetry in Hlast. exists Hlast.
        assumption.
Qed.

Definition equivocator_computable_sent_messages
  : computable_sent_messages equivocator_vlsm
  :=
  {|
    sent_messages_fn := equivocator_sent_messages_fn;
    sent_messages_full := equivocator_sent_messages_full;
    sent_messages_consistency := @equivocator_has_been_sent_consistency Hbeen_sent_X
  |}.

End computable_sent_messages_lifting.

End equivocator_vlsm_has_been_sent.

(** ** equivocator composition

Given a composition <<X>> of VLSMs, we can model equivocator behavior by
creating a _equivocator composition_ which replaces each component of <<X>>
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
  {index equiv_index nequiv_index : Type}
  (partition : index -> equiv_index + nequiv_index)
  (rpartition : equiv_index + nequiv_index -> index)
  (Hlpartition : forall i : index, rpartition (partition i) = i)
  (Hrpartition : forall i : equiv_index + nequiv_index, partition (rpartition i) = i)
  {IndEqDec : EqDec index}
  (IM : index -> VLSM message)
  (Hbs : forall i : index, has_been_sent_capability (IM i))
  (i0 : index)
  (X := free_composite_vlsm IM i0)
  .

Lemma partition_eq_dec : EqDec (equiv_index + nequiv_index).
Proof.
  intros x y.
  destruct (eq_dec (rpartition x) (rpartition y)).
  - left. apply (f_equal partition) in e.
    repeat rewrite Hrpartition in e. assumption.
  - right. intro contra; elim n. subst. reflexivity.
Qed.

Existing Instance partition_eq_dec.

Definition equivocator_IM
  (i : equiv_index + nequiv_index)
  : VLSM message
  :=
  let IMi := IM (rpartition i) in
  match i with
  | inl _ => equivocator_vlsm IMi
  | inr _ => IMi
  end.

Lemma equivocator_Hbs
  (i : equiv_index + nequiv_index)
  :  has_been_sent_capability (equivocator_IM i).
Proof.
  destruct i; simpl.
  - apply equivocator_has_been_sent_capability. apply Hbs.
  - apply Hbs.
Qed.

Definition equivocators_no_equivocations_constraint
  (l : composite_label equivocator_IM)
  (som : composite_state equivocator_IM * option message)
  : Prop
  :=
  no_equivocations equivocator_IM (partition i0) (free_constraint equivocator_IM) equivocator_Hbs l som.

Definition equivocators_no_equivocations_vlsm
  : VLSM message
  :=
  composite_vlsm equivocator_IM (partition i0) equivocators_no_equivocations_constraint.

Definition equivocators_state_project'
  (s : vstate equivocators_no_equivocations_vlsm)
  (pi : equiv_index + nequiv_index)
  : vstate (IM (rpartition pi))
  :=
  match pi with
  | inl e => projT2 (s (inl e)) (of_nat_lt (Hzero _ (s (inl e))))
  | inr n => s (inr n)
  end.

Definition equivocators_state_project
  (s : vstate equivocators_no_equivocations_vlsm)
  (i : index)
  : vstate (IM i).
Proof.
  pose (equivocators_state_project' s (partition i)) as si.
  rewrite Hlpartition in si.
  exact si.
Defined.

Definition equivocators_label_project
  (l : vlabel equivocators_no_equivocations_vlsm)
  : option (vlabel X)
:=
let (i, li) := l in
match i as s return (vlabel (equivocator_IM s) -> option (vlabel X)) with
| inl e =>
	fun li0 : vlabel (equivocator_IM (inl e)) =>
    let (lj, dj) := li0 in
    match dj with
    | Existing _ 0 false =>
      Some (existT (fun n : index => vlabel (IM n)) (rpartition (inl e)) lj)
    | _ => None
    end
| inr n =>
    fun li0 : vlabel (equivocator_IM (inr n)) =>
    Some (existT (fun n0 : index => vlabel (IM n0)) (rpartition (inr n)) li0)
end li.

Definition equivocators_transition_item_project
  (item : vtransition_item equivocators_no_equivocations_vlsm)
  : option (vtransition_item X)
  :=
  match item with {| l := el; input := iom; output := oom; destination := s |} =>
    match  equivocators_label_project el with
    | None => None
    | Some lx =>
      let sx := equivocators_state_project s in
      Some {| l := lx; input := iom; output := oom; destination := sx |}
    end
  end.

End fully_equivocating_composition.
