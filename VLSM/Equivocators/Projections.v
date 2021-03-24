From Coq Require Import List Vectors.Fin Arith.Compare_dec Lia Program.
Import ListNotations.

From CasperCBC Require Import Preamble ListExtras VLSM.Common VLSM.Equivocators.Common.

(** * VLSM Projecting Equivocator Traces *)

Section equivocator_vlsm_projections.

(**
Given an [equivocator_vlsm] trace ending in a state <<s>>, we can obtain a
trace in the original vlsm leading to the <<si>>, the  <<i>>th internal
state in <<s>>, by extracting a path leading to si.

This section is devoting to formalizing this projects studying its
properties. In particular, we show that given a [protocol_trace] for
the [equivocator_vlsm], we can always extract such a trace for any valid
index, and, furthermore, that the trace extracted is protocol for the
original machine.
*)

Context
  {message : Type}
  (X : VLSM message)
  (equivocator_vlsm := equivocator_vlsm X)
  (MachineDescriptor := MachineDescriptor X)
  .

Local Ltac unfold_transition H :=
  ( unfold transition in H; unfold equivocator_vlsm in H
  ; unfold Common.equivocator_vlsm in H
  ; unfold mk_vlsm in H; unfold machine in H
  ; unfold projT2 in H; unfold equivocator_vlsm_machine in H
  ; unfold equivocator_transition in H).

(** Given a [transition_item] <<item>> for the [equivocator_vlsm] and a
[MachineDescriptor] referring to a position in the [destination] of <<item>>,
it returns a transition item for the original machine (if the descriptor
matches the copy affected by this transition) and a new machine descriptor
referring to a position in the state prior to the transition.
*)
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
            Some ( None, descriptor)
          else Some (None, Existing _ j false)
        | Existing _ i is_equiv =>
          match is_equiv with
          | false => (* no equivocation *)
            if nat_eq_dec i j then
              Some ( Some item', descriptor)
            else Some (None, Existing _ j false)
          | true => (* equivocation: transition happens on the copy *)
            if nat_eq_dec (S j) (S n) then
              Some (Some item', descriptor)
            else Some (None, Existing _ j false)
          end
        end
      | _ => None
      end
    end
  end.

(**
Since equivocators always have machine 0, We can always project a 'valid'
equivocator 'transition item' to component 0.
*)

Lemma equivocators_vlsm_transition_item_project_zero_descriptor
  (item : vtransition_item equivocator_vlsm)
  s
  (Ht : vtransition equivocator_vlsm (l item) (s, input item) = (destination item, output item))
  (Hv : vvalid equivocator_vlsm (l item) (s, input item))
  : exists oitem, equivocator_vlsm_transition_item_project item (Existing _ 0 false) = Some (oitem, Existing _ 0 false).
Proof.
  unfold equivocator_vlsm_transition_item_project.
  destruct item.
  destruct l as (l, dl). destruct destination as (ndest, bdest).
  destruct (le_lt_dec (S ndest) 0); [lia|].
  destruct dl as [ndl | idl fdl]
  ; [destruct (nat_eq_dec 1 (S ndest))| destruct fdl; [destruct (nat_eq_dec 1 (S ndest))| destruct (nat_eq_dec idl 0)]]
  ; simpl in Ht; unfold vtransition in Ht; unfold_transition Ht; unfold snd in Ht
  ; destruct Hv as [Hidl _].
  - inversion Ht. subst. destruct s; inversion H0. lia.
  - exists None. reflexivity.
  - destruct (le_lt_dec (S (projT1 s)) idl); [lia|].
    match type of Ht with
    | (let (_, _) := ?t in _) = _ => destruct t
    end.
    inversion Ht. subst. destruct s; inversion H0. lia.
  - exists None. reflexivity.
  - subst idl. eexists _. reflexivity.
  - exists None. reflexivity.
Qed.

(**
An injectivity result for [equivocator_vlsm_transition_item_project].
*)
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
  destruct (le_lt_dec (S ndest) i); [congruence|].
  destruct (le_lt_dec (S ndest) i'); [congruence|].
  destruct descriptor as [sn | j fj].
  - destruct (nat_eq_dec (S i) (S ndest)); congruence.
  - destruct fj as [|] eqn:Hfj.
    + destruct (nat_eq_dec (S i) (S ndest)); [|congruence].
      inversion HitemX; subst. clear HitemX.
      inversion e. subst i. clear e.
      destruct (nat_eq_dec (S i') (S ndest)); [|congruence].
      inversion HitemX'; subst. clear HitemX'.
      inversion e; subst i'; clear e.
      replace (of_nat_lt l0) with (of_nat_lt l) by apply of_nat_ext.
      repeat split; reflexivity.
    + destruct (nat_eq_dec j i); [|congruence].
      destruct (nat_eq_dec j i'); [|congruence].
      inversion HitemX. inversion HitemX'. subst.
      replace (of_nat_lt l0) with (of_nat_lt l) by apply of_nat_ext.
      repeat split; reflexivity.
Qed.

(**
[equivocator_vlsm_transition_item_project] only fails for an out-of-range
descriptor.
*)
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
  destruct descriptor as [s|i is_equiv]; [congruence|].
  exists i. exists is_equiv. exists eq_refl.
  destruct destination as (n, bs).
  destruct (le_lt_dec (S n) i); [assumption|].
  destruct l as (ls, [is | ix [|]]).
  - destruct (nat_eq_dec (S i) (S n)); congruence.
  - destruct (nat_eq_dec (S i) (S n)); congruence.
  - destruct (nat_eq_dec ix i); congruence.
Qed.

Lemma equivocator_transition_item_project_proper
  (item : vtransition_item equivocator_vlsm)
  (descriptor : MachineDescriptor)
  (Hproper : proper_descriptor X descriptor (destination item))
  : equivocator_vlsm_transition_item_project item descriptor <> None.
Proof.
  intro contra.
  apply equivocator_transition_item_project_inv_none in contra.
  destruct contra as [id [fd [Heqd Hd]]].
  subst. simpl in *. lia.
Qed.

(**
If [equivocator_vlsm_transition_item_project] produces a transition item,
then that item has the same [input] and [output] as the argument item.
*)
Lemma equivocator_transition_item_project_inv_messages
  (item : vtransition_item equivocator_vlsm)
  (itemX : vtransition_item X)
  (idescriptor odescriptor : MachineDescriptor)
  (Hitem : equivocator_vlsm_transition_item_project item idescriptor = Some (Some itemX, odescriptor))
  : exists
    (i : nat)
    (is_equiv : bool),
    idescriptor = Existing _ i is_equiv /\
    proper_descriptor X idescriptor (destination item) /\
    input item = input itemX /\ output item = output itemX.
Proof.
  unfold equivocator_vlsm_transition_item_project in Hitem.
  destruct idescriptor as [s|j fj]; [congruence|].
  exists j. exists fj. split; [reflexivity|].
  destruct item.
  destruct destination as (n, bs).
  destruct l as (lx, descriptorx).
  destruct (le_lt_dec (S n) j); [congruence|].
  destruct descriptorx as [s | i' [|]] eqn:Hl; simpl.
  - destruct (nat_eq_dec (S j) (S n)); congruence.
  - destruct (nat_eq_dec (S j) (S n)); [|congruence].
    split; [assumption|].
    inversion Hitem. subst. repeat split; reflexivity.
  - destruct (nat_eq_dec i' j); [|congruence].
    split; [assumption|].
    inversion Hitem. subst. repeat split; reflexivity.
Qed.

(**
If the 'destination' of a 'valid' equivocator 'transition_item' is singleton,
then by projecting the item to component 0 we actually obtain a
'transition_item' for the original machine.
*)
Lemma no_equivocating_equivocator_transition_item_project
  (item : vtransition_item equivocator_vlsm)
  (Hno_equiv_item : is_singleton_state X (destination item))
  (s : vstate equivocator_vlsm)
  (Hv : vvalid equivocator_vlsm (l item) (s, input item))
  (Ht : vtransition equivocator_vlsm (l item) (s, input item) = (destination item, output item))
  : equivocator_vlsm_transition_item_project item (Existing _ 0 false) =
      Some (Some
        {| l := fst (l item); input := input item; output := output item; destination := equivocator_state_descriptor_project X (destination item) (Existing _ 0 false) |}
        , Existing _ 0 false).
Proof.
  destruct item.
  unfold Common.l, Common.input, Common.output, Common.destination in *.
  unfold equivocator_vlsm_transition_item_project.
  destruct l as (li, eqvi).
  destruct destination as (ni, bsi) eqn:Hdesti.
  destruct (le_lt_dec (S ni) 0); [lia|].
  specialize
    (equivocator_transition_no_equivocation_zero_descriptor X _ _ _ _ _ Hv Ht Hno_equiv_item)
    as Heq_eqvi.
  simpl in Heq_eqvi. subst eqvi.
  destruct (nat_eq_dec 0 0); [|congruence].
  reflexivity.
Qed.


Lemma equivocator_transition_item_project_proper_characterization
  (item : vtransition_item equivocator_vlsm)
  (descriptor : MachineDescriptor)
  (Hproper : proper_descriptor X descriptor (destination item))
  : exists oitem descriptor',
    equivocator_vlsm_transition_item_project item descriptor = Some (oitem, descriptor')
    /\ match oitem with
      | Some itemx =>
        l itemx = fst (l item) /\  input item = input itemx /\ output item = output itemx /\
        (equivocator_state_descriptor_project X (destination item) descriptor = destination itemx)
      | None => True
      end
    /\ forall
      (s : vstate equivocator_vlsm)
      (Hv : vvalid equivocator_vlsm (l item) (s, input item))
      (Ht : vtransition equivocator_vlsm (l item) (s, input item) = (destination item, output item)),
      proper_descriptor X descriptor' s /\
      match oitem with
      | Some itemx =>
        forall (sx : vstate X)
          (Hsx : sx = equivocator_state_descriptor_project X s descriptor'),
          vvalid X (l itemx) (sx, input itemx) /\
          vtransition X (l itemx) (sx, input itemx) = (destination itemx, output itemx)
      | None =>
        equivocator_state_descriptor_project X (destination item) descriptor = equivocator_state_descriptor_project X s descriptor'
      end.
Proof.
  destruct item. simpl. simpl in Hproper.
  unfold equivocator_vlsm_transition_item_project.
  destruct descriptor eqn:Heqvi.
  - exists None. eexists _. split; [reflexivity|].
    intros. split; [exact I|]. intros.
    split; [|reflexivity].
    assumption.
  - destruct l as (li, eqvi).
    simpl in Hproper.
    destruct destination as (ni, bsi) eqn:Hdesti.
    simpl in Hproper.
    destruct (le_lt_dec (S ni) n); [lia|].
    destruct eqvi as [nsi | ieqvi feqvi].
    + destruct (nat_eq_dec (S n) (S ni)).
      * exists None. eexists _. split; [reflexivity|]. split; [exact I|].
        intros.
        inversion e. subst. clear e.
        split; [apply Hv|].
        apply
          (new_machine_label_equivocator_state_project_last X (li, NewMachine X nsi) s input _ output Ht nsi eq_refl b).
      * exists None. eexists _. split; [reflexivity|]. split; [exact I|].
        intros.
        apply and_comm.
        split.
        { apply
          (new_machine_label_equivocator_state_project_not_last X (li, NewMachine X nsi) s input _ output Ht nsi eq_refl).
          simpl. lia.
        }
        simpl.
        unfold vtransition in Ht. unfold_transition Ht. unfold snd in Ht.
        inversion Ht. subst. clear Ht.
        destruct s as (neqv, seqv). simpl in *. inversion H0.
        subst ni. lia.
    + destruct feqvi; [destruct (nat_eq_dec (S n) (S ni))|destruct (nat_eq_dec ieqvi n)].
      * inversion e. subst ni. clear e.
        eexists _. eexists _. split; [reflexivity|]. split; [repeat split|].
        -- unfold equivocator_state_descriptor_project.
          unfold equivocator_state_project.
          destruct (le_lt_dec (S n) n); [lia|]. simpl. f_equal. apply of_nat_ext.
        -- intros.
          destruct Hv as [Heqv Hv].
          split; [assumption|].
          intros.
          unfold equivocator_state_descriptor_project in Hsx.
          unfold equivocator_state_project in Hsx.
          simpl.
          unfold fst in Hv.
          unfold vvalid in Hv.
          unfold vtransition in Ht.
          unfold_transition Ht. unfold snd in Ht.
          destruct (le_lt_dec (S (projT1 s)) ieqvi); [lia|].
          replace (of_nat_lt l0) with (of_nat_lt Heqv) in * by apply of_nat_ext.
          clear l0.
          assert (Hsxi : sx = projT2 s (of_nat_lt Heqv)).
          { subst.
            destruct s as (nsi, si). unfold projT2.
            simpl in Heqv.
            destruct (le_lt_dec (S nsi) ieqvi); [lia|].
            f_equal. apply of_nat_ext.
          }
          rewrite Hsxi. split; [assumption|].
          unfold fst in Ht.
          destruct (vtransition X li (projT2 s (of_nat_lt Heqv), input))
            as (si'', om') eqn:Ht'.
          inversion Ht.
          f_equal.
          destruct s as (ns, bs).
          inversion H0. subst n. simpl_existT. subst bsi.
          rewrite to_nat_of_nat.
          destruct (nat_eq_dec (S ns) (S ns)); [|congruence].
          reflexivity.
      * eexists _. eexists _. split; [reflexivity|]. split; [exact I|].
        intros.
        apply and_comm.
        split.
        { apply
            (existing_true_label_equivocator_state_project_not_last X (li, Existing X ieqvi true) s input _ output Ht _ eq_refl )
          ; [|simpl; lia].
          apply Hv.
        }
        destruct Hv as [Heqv Hv].
        unfold vtransition in Ht. unfold_transition Ht. unfold snd in Ht.
        destruct (le_lt_dec (S (projT1 s)) ieqvi); [lia|].
        destruct (vtransition X (fst (li, Existing X ieqvi true))
        (projT2 s (of_nat_lt l0), input))
          as (si', om').
        inversion Ht. subst.
        destruct s as (neqv, seqv). simpl in *.
        inversion H0. subst ni. lia.
      * subst ieqvi.
        eexists _. eexists _. split; [reflexivity|].
        split; [repeat split|].
        -- unfold equivocator_state_descriptor_project.
          unfold equivocator_state_project.
          destruct (le_lt_dec (S ni) n); [lia|]. simpl. f_equal. apply of_nat_ext.
        -- intros.  destruct Hv as [Heqv Hv].
          split; [assumption|].
          intros. simpl.
          unfold equivocator_state_descriptor_project in Hsx.
          unfold equivocator_state_project in Hsx.
          unfold fst in Hv.
          unfold vvalid in Hv.
          unfold vtransition in Ht. unfold_transition Ht. unfold snd in Ht.
          destruct (le_lt_dec (S (projT1 s)) n); [lia|].
          replace (of_nat_lt l0) with (of_nat_lt Heqv) in * by apply of_nat_ext.
          clear l0.
          assert (Hsxi : sx = projT2 s (of_nat_lt Heqv)).
          { subst.
            destruct s as (nsi, si). unfold projT2.
            simpl in Heqv.
            destruct (le_lt_dec (S nsi) n); [lia|].
            f_equal. apply of_nat_ext.
          }
          rewrite Hsxi. split; [assumption|].
          unfold fst in Ht.
          destruct (vtransition X li (projT2 s (of_nat_lt Heqv), input))
            as (si'', om') eqn:Ht'.
          inversion Ht. clear Ht. subst ni.
          simpl_existT. subst bsi.
          f_equal.
          rewrite eq_dec_if_true; [reflexivity|].
          apply of_nat_ext.
      * eexists _. eexists _. split; [reflexivity|]. split; [exact I|].
        intros.
        apply and_comm.
        split.
        { apply
            (existing_false_label_equivocator_state_project_not_same X (li, Existing X ieqvi false) s input _ output Ht _ eq_refl)
          ; [| simpl; lia|assumption].
          destruct Hv as [Hieqvi Hv].
          assumption.
        }
        destruct Hv as [Heqv Hv].
        unfold vtransition in Ht. unfold_transition Ht. unfold snd in Ht.
        destruct (le_lt_dec (S (projT1 s)) ieqvi); [lia|].
        unfold fst in Ht.
        destruct (vtransition X li (projT2 s (of_nat_lt l0), input))
          as (si', om').
        inversion Ht. subst. simpl. lia.
Qed.

Lemma equivocator_transition_item_project_inv_characterization
  (item : vtransition_item equivocator_vlsm)
  (itemx : vtransition_item X)
  (descriptor descriptor' : MachineDescriptor)
  (Hitem : equivocator_vlsm_transition_item_project item descriptor = Some (Some itemx, descriptor'))
  : l itemx = fst (l item) /\  input item = input itemx /\ output item = output itemx /\
    (equivocator_state_descriptor_project X (destination item) descriptor = destination itemx)
    .
Proof.
  apply equivocator_transition_item_project_inv_messages in Hitem as Hitem'.
  destruct Hitem' as [_ [_ [_ [Hproper _]]]].
  apply equivocator_transition_item_project_proper_characterization in Hproper.
  destruct Hproper as [oitem [odescriptor [Hpr' H]]].
  rewrite Hpr' in Hitem.
  inversion Hitem. subst. apply H.
Qed.

(**
The projection of an [equivocator_vlsm] trace is obtained by traversing the
trace from right to left guided by the descriptors produced by
[equivocator_vlsm_transition_item_project] and gathering all non-empty
[transition_item]s it produces.
*)
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

(**
Projecting on a [NewMachine] descriptor yields an empty trace and the same
descriptor.
*)
Lemma equivocator_vlsm_trace_project_on_new_machine
  (tr : list (vtransition_item equivocator_vlsm))
  (s : vstate X)
  : equivocator_vlsm_trace_project tr (NewMachine _ s) = Some ([], NewMachine _ s).
Proof.
  induction tr; [reflexivity|].
  simpl. rewrite IHtr. reflexivity.
Qed.

(** [equivocator_vlsm_trace_project] acts like a morphism w.r.t. concatenation
(single element in left operand case).
*)
Lemma equivocator_vlsm_trace_project_cons
  (bprefix : vtransition_item equivocator_vlsm)
  (bsuffix : list (vtransition_item equivocator_vlsm))
  (dstart dlast : MachineDescriptor)
  (tr : list (vtransition_item X))
  (Hproject : equivocator_vlsm_trace_project ([bprefix] ++ bsuffix) dlast = Some (tr, dstart))
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
  ; [|congruence].
  exists dmiddle.
  destruct (equivocator_vlsm_transition_item_project bprefix dmiddle) as [[[prefix|] i]|]
    eqn:Hprefix
  ; inversion Hproject; subst; clear Hproject.
  - exists [prefix]. exists suffix.
    repeat split.
    simpl in *. rewrite Hprefix. reflexivity.
  -  exists []. exists tr.
    repeat split.
    simpl in *. rewrite Hprefix. reflexivity.
Qed.

(** [equivocator_vlsm_trace_project] acts like a morphism w.r.t. concatenation
*)
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
    repeat split; [|assumption|].
    + simpl. rewrite Hprefix.
      simpl in Ha.
      destruct (equivocator_vlsm_transition_item_project a da)
        as [(oitem', i)|]
      ; [|congruence].
      destruct oitem' as [item'|]; inversion Ha; subst; reflexivity.
    + subst. rewrite app_assoc. reflexivity.
Qed.

(** [equivocator_vlsm_trace_project] acts like a morphism w.r.t. concatenation
(converse)
*)
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
    ; [|congruence].
    specialize (IHbprefix prefix' dstart' eq_refl).
    simpl. rewrite IHbprefix.
    destruct (equivocator_vlsm_transition_item_project a dstart')
      as [[[item'|]i]|]
    ; inversion Hprefix; subst; reflexivity.
Qed.

(**
Next we prove some inversion properties for [equivocator_vlsm_transition_item_project].
*)
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
    (Hitem' : item' = {| l := fst l; input := iom; destination := sx; output := oom |})
    (i' : nat)
    (fi' : bool)
    (Hdi' : di' = Existing _ i' fi')
    (Hi' : i' < S (projT1 s'))
    (s'x := projT2 s' (of_nat_lt Hi')),
    vvalid X (fst l) (s'x, iom) /\
    vtransition X (fst l) (s'x, iom) = (sx, oom).
Proof.
  unfold vvalid in Hv. unfold vtransition in Ht.
  unfold_transition Ht.
  simpl in Hv.
  unfold equivocator_vlsm_transition_item_project in Hitem.
  destruct di as [sn| i fi]; [congruence|].
  exists i. exists fi. exists eq_refl. unfold item in Hitem.
  destruct l as (lx, descriptor).
  destruct s as (ns, bs).
  destruct (le_lt_dec (S ns) i); [congruence|].
  exists l. unfold snd in Ht. unfold snd in Hv.
  destruct descriptor as [sn| j is_equiv].
  - destruct (nat_eq_dec (S i) (S ns)); congruence.
  - destruct Hv as [Hj Hv].
    destruct (le_lt_dec (S (projT1 s')) j); [lia|].
    replace (of_nat_lt l0) with (of_nat_lt Hj) in * by apply of_nat_ext. clear l0.
    simpl in Ht.
    destruct (vtransition X lx (projT2 s' (of_nat_lt Hj), iom))
      as (si', om') eqn:Htx.
    destruct s' as (n', bs').
    destruct is_equiv as [|].
    + destruct (nat_eq_dec (S i) (S ns)); [|congruence].
      inversion Hitem. subst di' item'. clear Hitem.
      exists eq_refl.
      exists j. exists true. exists eq_refl.
      exists Hj. split; [assumption|].
      inversion Ht. subst. clear Ht. inversion e. subst i. clear e.
      apply inj_pairT2 in H1. subst. simpl.
      rewrite to_nat_of_nat.
      destruct (nat_eq_dec (S n') (S n')); [assumption|].
      elim n. reflexivity.
    + destruct (nat_eq_dec j i); [|congruence]. subst.
      inversion Hitem. subst di' item'. clear Hitem.
      exists eq_refl. exists i. exists false. exists eq_refl.
      exists Hj. split; [assumption|].
      inversion Ht. subst. clear Ht.
      apply inj_pairT2 in H1. subst. simpl.
      rewrite eq_dec_if_true by apply of_nat_ext.
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
      match di' with
      | Existing _ i' fi' =>
        exists
          (Hi : i < S (projT1 s))
          (Hi' : i' < S (projT1 s')),
          projT2 s' (of_nat_lt Hi') = projT2 s (of_nat_lt Hi)
      | NewMachine _ sn' =>
        exists
          (Hl : snd l = NewMachine _ sn')
          (Hi : i = (projT1 s))
          (Hiom : iom = None)
          (Hoom : oom = None)
          (Hsn : projT2 s (of_nat_lt (le_n (S (projT1 s)))) = sn')
          ,
          vinitial_state_prop X sn'
      end
    end.
Proof.
  unfold vvalid in Hv. unfold vtransition in Ht.
  destruct l as (lx, d).
  simpl in Hv. unfold_transition Ht. unfold snd in Ht.
  unfold equivocator_vlsm_transition_item_project in Hitem.
  destruct di as [si | i fi]; [inversion Hitem; reflexivity|].
  simpl in Hv. unfold item in Hitem.
  destruct s as (ns, bs).
  destruct (le_lt_dec (S ns) i); [congruence|].
  destruct d as [sd | id fd].
  - destruct (nat_eq_dec (S i) (S ns)); inversion Hitem; subst; clear Hitem.
    + simpl. exists eq_refl. inversion e. exists eq_refl.
      destruct s' as (ns', bs'). inversion Ht. subst.
      simpl_existT.
      destruct Hv. repeat split; [assumption| |assumption].
      rewrite to_nat_of_nat.
      destruct (nat_eq_dec (S ns') (S ns')); [|elim n]; reflexivity.
    + simpl. exists l. inversion Ht. subst.
      destruct s' as (ns', bs').
      simpl in H0. inversion H0. subst.
      simpl_existT. simpl.
      assert (Hi : i < S ns') by lia.
      exists Hi. subst.
      rewrite to_nat_of_nat.
      destruct (nat_eq_dec i (S ns')); [lia|].
      f_equal. apply of_nat_ext.
  - destruct Hv as [Hj Hv].
    destruct (le_lt_dec (S (projT1 s')) id); [lia|].
    replace (of_nat_lt l0) with (of_nat_lt Hj) in * by apply of_nat_ext. clear l0.
    destruct s' as (n', bs'). simpl in Hv. unfold projT2 in Ht. simpl in Hj.
    simpl in Ht.
    destruct
      (@vtransition message X lx
      (@pair (@vstate message X) (option message)
         (bs' (@of_nat_lt id (S n') Hj)) iom))
      as (si', om') eqn:Htx.
    destruct fd as [|].
    + destruct (nat_eq_dec (S i) (S ns)); [congruence|].
      inversion Hitem. subst di'. clear Hitem.
      simpl. exists l. inversion Ht. subst.
      assert (Hi' : i < S n') by lia.
      exists Hi'.
      simpl_existT. subst.
      rewrite to_nat_of_nat in *.
      destruct (nat_eq_dec i (S n')); [lia|].
      f_equal.
      apply of_nat_ext.
    + destruct (nat_eq_dec id i); [congruence|].
      inversion Hitem. subst di'. clear Hitem. simpl.
      exists l. inversion Ht. subst. exists l.
      simpl_existT. subst.
      rewrite eq_dec_if_false; [reflexivity|].
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
  - simpl in Ht.
    inversion Ht. subst. clear Ht. simpl_existT.
    unfold projT1.
    simpl in Hi'.
    assert (Hi'' : i' < S (S n')) by lia.
    exists Hi''.
    destruct (le_lt_dec (S (S n')) i'). { lia. }
    replace (of_nat_lt l) with (of_nat_lt Hi'') in * by apply of_nat_ext. clear l.
    rewrite eq_dec_if_false.
    + exists false. exists None. reflexivity.
    + lia.
  - destruct Hv as [Hj Hv]. unfold projT1 in Ht. simpl in Hj.
    destruct (le_lt_dec (S n') j); [lia|].
    replace (of_nat_lt l) with (of_nat_lt Hj) in * by apply of_nat_ext. clear l.
    simpl in Ht.
    destruct (vtransition X lx (bs' (of_nat_lt Hj), iom))
      as (si', om') eqn:Htx.
    simpl in Hi'.
    assert (Hi'' : i' < S (S n')) by lia.
    destruct is_equiv as [|] eqn:Hflag
    ; inversion Ht; subst ns om'; clear Ht
    ; apply inj_pairT2 in H1; subst bs.
    + destruct (le_lt_dec (S (S n')) i'); [lia|].
      destruct (nat_eq_dec (S i') (S (S n'))); [lia|].
      exists Hi''. exists false.
      exists None. reflexivity.
    + destruct (le_lt_dec (S n') i'); [lia|].
      destruct (nat_eq_dec j i').
      * subst j.
        rewrite eq_dec_if_true by apply of_nat_ext.
        exists Hi'. exists false.
        exists (Some {| l := lx; input := iom; destination := si'; output := oom |}).
        reflexivity.
      * exists Hi'. exists false. exists None. reflexivity.
Qed.

Lemma equivocator_protocol_transition_item_project_inv5_new_machine
  (l : vlabel equivocator_vlsm)
  (s s' : vstate equivocator_vlsm)
  (iom oom : option message)
  (Hv: vvalid equivocator_vlsm l (s', iom))
  (Ht: vtransition equivocator_vlsm l (s', iom) = (s, oom))
  (item := {| l := l; input := iom; destination := s; output := oom |})
  (fi : bool)
  (sn : state)
  (Hnew : snd l = NewMachine _ sn)
  : exists
    (i : nat)
    (Hi : i < S (projT1 s)),
    equivocator_vlsm_transition_item_project item (Existing _ i fi) = Some (None, snd l).
Proof.
  unfold equivocator_vlsm_transition_item_project.
  destruct s as (ns, bs).
  destruct s' as (ns', bs').
  unfold vtransition in Ht. unfold_transition Ht.
  unfold vvalid in Hv. simpl in Hv.
  destruct l as (lx, d). unfold snd in Ht. simpl in Hv.
  simpl in Hnew. subst d.
  inversion Ht. subst; clear Ht.
  simpl_existT.
  exists (S ns').  split; [simpl; lia|].
  unfold snd. unfold item.
  destruct (le_lt_dec (S (S ns')) (S ns')); [lia|].
  rewrite eq_dec_if_true; reflexivity.
Qed.

Lemma equivocator_protocol_transition_item_project_inv5
  (l : vlabel equivocator_vlsm)
  (s s' : vstate equivocator_vlsm)
  (iom oom : option message)
  (Hv: vvalid equivocator_vlsm l (s', iom))
  (Ht: vtransition equivocator_vlsm l (s', iom) = (s, oom))
  (item := {| l := l; input := iom; destination := s; output := oom |})
  (fi : bool)
  (i : nat)
  (is_equiv : bool)
  (Hsndl : snd l = Existing _ i is_equiv)
  : exists
    (i : nat)
    (Hi : i < S (projT1 s))
    (itemx : vtransition_item X),
    equivocator_vlsm_transition_item_project item (Existing _ i fi) = Some (Some itemx, snd l).
Proof.
  unfold equivocator_vlsm_transition_item_project.
  destruct s as (ns, bs).
  destruct s' as (ns', bs').
  unfold vtransition in Ht. unfold_transition Ht.
  unfold vvalid in Hv. simpl in Hv.
  destruct l as (lx, d). unfold snd in Ht. simpl in Hv.
  simpl in Hsndl. subst d.
  unfold snd. unfold item. destruct Hv as [Hi Hv].
  unfold projT1 in Ht.
  destruct (le_lt_dec (S ns') i); [lia|].
  replace (of_nat_lt l) with (of_nat_lt Hi) in * by apply of_nat_ext. clear l.
  simpl in Ht.
  destruct (vtransition X lx (bs' (of_nat_lt Hi), iom)) as (sn', om').
  destruct is_equiv as [|]; inversion Ht; subst; clear Ht; apply inj_pairT2 in H1; subst.
  + exists (S ns'). split; [simpl; lia|].
    destruct (le_lt_dec (S (S ns')) (S ns')); [lia|].
    rewrite eq_dec_if_true by  reflexivity.
    eexists _. reflexivity.
  + exists i. exists Hi.
    destruct (le_lt_dec (S ns) i); [lia|].
    rewrite eq_dec_if_true by reflexivity.
    eexists _. reflexivity.
Qed.

(**
The projection of a segment of an [equivocator_vlsm] protocol trace
is defined and a protocol trace segment in the original vlsm.
*)
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
        ; [|assumption|assumption].
        destruct Hitem as [_i [_fi [Heq [Hi [Heqitem' Hitem]]]]].
        inversion Heq. subst _i _fi. clear Heq.
        destruct Hdi as [_Hi Hlst].
        replace (of_nat_lt _Hi) with (of_nat_lt Hi) in * by apply of_nat_ext. clear _Hi.
        simpl in Hlst. destruct Hlst as [Hlst Htr].
        repeat rewrite map_cons.
        destruct Hitem as [i' [fi' [Hdi' [Hi' [Hv' Ht']]]]].
        subst di'. exists Hi'.
        rewrite unroll_last. subst. simpl. exists Hlst.
        constructor; [assumption|].
        repeat split; [|assumption|assumption|assumption].
        destruct s' as (ns', bs'). apply Hs'.
      * subst item.
        destruct Hdi as [Hi [Hlst Htr]].
        apply (equivocator_protocol_transition_item_project_inv3 l s s') in Hitem
        ; [|assumption|assumption].
        eexists _. eexists _. exists eq_refl.
        destruct di' as [sn' | i' fi'].
        -- destruct Hitem as [Hl [Hi' [Hiom' [Hoom [Hsn'eq Hsn']]]]]. subst.
          replace (of_nat_lt (le_n (S (projT1 s)))) with (of_nat_lt Hi) in * by apply of_nat_ext.
          repeat split; assumption.
        -- destruct Hitem as [_Hi [Hi' Heq]].
          replace (of_nat_lt _Hi) with (of_nat_lt Hi) in Heq by apply of_nat_ext. clear _Hi.
          exists Hi'. rewrite Heq. exists Hlst. assumption.
      * apply equivocator_transition_item_project_inv_none in Hitem.
        destruct Hitem as [_i [_fi [Heq Hitem]]].
        destruct Hdi as [Hi Hdi].
        inversion Heq. subst _i _fi item. simpl in Hitem. lia.
Qed.

(**
The projection of a segment of a protocol trace from the [pre_loaded_with_all_messages_vlsm]
corresponding to the [equivocator_vlsm] is defined and it is a protocol
trace segment in the [pre_loaded_with_all_messages_vlsm] corresponding to the original vlsm.
*)
Lemma preloaded_equivocator_vlsm_trace_project_protocol
  (bs : vstate equivocator_vlsm)
  (btr : list (vtransition_item equivocator_vlsm))
  (Hbtr : finite_protocol_trace_from (pre_loaded_with_all_messages_vlsm equivocator_vlsm) bs btr)
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
      /\ finite_protocol_trace_from (pre_loaded_with_all_messages_vlsm X) sn tr
    | Existing _ i fi =>
      exists
      (Hi : i < S (projT1 bs))
      (s := projT2 bs (of_nat_lt Hi))
      (Hlast : projT2 (last (map destination btr) bs) (of_nat_lt Hj) = last (map destination tr) s)
      ,
      finite_protocol_trace_from (pre_loaded_with_all_messages_vlsm X) s tr
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
                  (@pre_loaded_with_all_messages_vlsm message
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
        ; [|assumption|assumption].
        destruct Hitem as [_i [_fi [Heq [Hi [Heqitem' Hitem]]]]].
        inversion Heq. subst _i _fi. clear Heq.
        destruct Hdi as [_Hi Hlst].
        replace (of_nat_lt _Hi) with (of_nat_lt Hi) in * by apply of_nat_ext. clear _Hi.
        simpl in Hlst. destruct Hlst as [Hlst Htr].
        repeat rewrite map_cons.
        destruct di' as [sn'| i' fi']
        ; [destruct Hitem as [i' [fi' [Hcontra _]]]; congruence|].
        destruct Hitem as [_i' [_fi' [Heq [Hi' [Hv' Ht']]]]].
        inversion Heq. subst _i' _fi'.
        exists Hi'.
        rewrite unroll_last. subst. simpl. exists Hlst.
        apply (finite_ptrace_extend (pre_loaded_with_all_messages_vlsm X)); [assumption|].
        repeat split; [apply Hs'X| |assumption|assumption].
        exists (proj1_sig (vs0 X)). apply (pre_loaded_with_all_messages_message_protocol_prop X).
      * subst item.
        apply (equivocator_protocol_transition_item_project_inv3 l s s') in Hitem
        ; [|assumption|assumption].
        destruct Hdi as [Hi [Hlst Htr]].
        eexists _. eexists _. exists eq_refl.
        destruct di' as [sn' | i' fi'].
        -- destruct Hitem as [Hl [_Hi [_Hiom [_Hoom [_Hsn' Hsn']]]]]. subst.
          split; [assumption|].
          destruct l as (l, dl). simpl in Hl. subst dl.
          simpl in Ht. unfold vtransition in Ht. simpl in Ht.
          inversion Ht.
          replace (of_nat_lt (le_n (S (projT1 s)))) with (of_nat_lt Hi) in * by apply of_nat_ext.
          split; assumption.
        -- destruct Hitem as [_Hi [Hi' Heq]].
          replace (of_nat_lt _Hi) with (of_nat_lt Hi) in * by apply of_nat_ext. clear _Hi.
          exists Hi'. rewrite Heq. exists Hlst. assumption.
      * apply equivocator_transition_item_project_inv_none in Hitem.
        destruct Hitem as [_i [_fi [Heq Hitem]]].
        destruct Hdi as [Hi Hdi].
        inversion Heq. subst _i _fi item. simpl in Hitem. lia.
Qed.

(**
The projection of a protocol trace from the [pre_loaded_with_all_messages_vlsm]
corresponding to the [equivocator_vlsm] is defined and it is a protocol
trace in the [pre_loaded_with_all_messages_vlsm] corresponding to the original vlsm.
*)
Lemma preloaded_equivocator_vlsm_project_protocol_trace
  (bs : vstate equivocator_vlsm)
  (btr : list (vtransition_item equivocator_vlsm))
  (Hbtr : finite_protocol_trace_from (pre_loaded_with_all_messages_vlsm equivocator_vlsm) bs btr)
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
      finite_protocol_trace (pre_loaded_with_all_messages_vlsm X) sn tr
    | Existing _ i fi =>
      exists
      (Hi : i < S (projT1 bs))
      (s := projT2 bs (of_nat_lt Hi))
      (Hlast : projT2 (last (map destination btr) bs) (of_nat_lt Hj) = last (map destination tr) s)
      ,
      finite_protocol_trace_from (pre_loaded_with_all_messages_vlsm X) s tr
      /\ (vinitial_state_prop (pre_loaded_with_all_messages_vlsm equivocator_vlsm) bs -> vinitial_state_prop (pre_loaded_with_all_messages_vlsm X) s)
    end.
Proof.
  destruct (preloaded_equivocator_vlsm_trace_project_protocol bs btr Hbtr j Hj jf)
    as [tr [di [Hproject Hdi]]].
  exists tr.
  exists di.
  exists Hproject.
  destruct di as [sn | i fi].
  - destruct Hdi as [Hsn [Hlst Htr]].
    repeat split; assumption.
  - destruct Hdi as [Hi [Hlast Htr]].
    exists Hi. exists Hlast. split; [assumption|].
    intro Hinit.
    destruct Hinit.
    cut (projT2 bs (of_nat_lt (Hzero X bs)) = projT2 bs (of_nat_lt Hi)).
    { intro R. rewrite <- R. assumption. }
    f_equal. assert (Hi0 : i = 0) by lia. subst. apply of_nat_ext.
Qed.

(**
If [equivocator_vlsm_trace_project] does not fail, then the index of the
machine descriptor is valid for the last state of the trace argument.
*)
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
  ; [|elim HtrX; reflexivity].
  clear HtrX. destruct p as (trX, d).
  apply equivocator_vlsm_trace_project_app in Htr.
  destruct Htr as [dmiddle [_ [lx [_ [Hx _]]]]].
  rewrite map_app. simpl. rewrite last_last.
  remember (Existing _ j fj) as dj.
  simpl in *.
  destruct (equivocator_vlsm_transition_item_project x dj)
    as [(_x, _dmiddle)|]
    eqn:Hx'
  ; [|congruence].
  destruct _x as [itemx|]; inversion Hx; subst lx _dmiddle; clear Hx.
  - subst. destruct x. unfold equivocator_vlsm_transition_item_project in Hx'.
    destruct l. destruct destination.
    destruct (le_lt_dec (S x) j); [congruence|].
    assumption.
  - subst. unfold equivocator_vlsm_transition_item_project in Hx'. destruct x. destruct l. destruct destination.
    destruct (le_lt_dec (S x) j); [congruence|].
    assumption.
Qed.

(**
Projecting a protocol trace segment on an index which is valid for the
first state of the trace does not fail and yields the same index.
*)
Lemma preloaded_equivocator_vlsm_trace_project_protocol_inv
  (bs : vstate equivocator_vlsm)
  (btr : list (vtransition_item equivocator_vlsm))
  (Hbtr : finite_protocol_trace_from (pre_loaded_with_all_messages_vlsm equivocator_vlsm) bs btr)
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

(**
An inversion lemma about projections of a protocol trace segment
*)
Lemma preloaded_equivocator_vlsm_trace_project_protocol_inv2
  (is: state)
  (tr: list transition_item)
  (Hntr : tr <> [])
  (Htr: finite_protocol_trace_from (pre_loaded_with_all_messages_vlsm equivocator_vlsm) is tr)
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
      finite_protocol_trace_from (pre_loaded_with_all_messages_vlsm X) sn trX
    | Existing _ i fi =>
      exists
      (Hi : i < S (projT1 is))
      (Hlst : projT2 (last (map destination tr) is) (of_nat_lt Hj) = last (map destination trX) (projT2 is (of_nat_lt Hi))),
      finite_protocol_trace_from (pre_loaded_with_all_messages_vlsm X) (projT2 is (of_nat_lt Hi)) trX
    end.
Proof.
  specialize (equivocator_vlsm_trace_project_inv _ Hntr j fj) as Hj.
  spec Hj. { rewrite HtrX. intro contra. congruence. }
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

(**
An inversion lemma about projections of a protocol trace
*)
Lemma preloaded_equivocator_vlsm_protocol_trace_project_inv2
  (is: state)
  (tr: list transition_item)
  (Hntr : tr <> [])
  (Htr: finite_protocol_trace_from (pre_loaded_with_all_messages_vlsm equivocator_vlsm) is tr)
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
      finite_protocol_trace (pre_loaded_with_all_messages_vlsm X) sn trX
    | Existing _ i fi =>
      exists
      (Hi : i < S (projT1 is))
      (s := projT2 is (of_nat_lt Hi))
      (Hlast : projT2 (last (map destination tr) is) (of_nat_lt Hj) = last (map destination trX) s)
      ,
      finite_protocol_trace_from (pre_loaded_with_all_messages_vlsm X) s trX
      /\ (vinitial_state_prop (pre_loaded_with_all_messages_vlsm equivocator_vlsm) is -> vinitial_state_prop (pre_loaded_with_all_messages_vlsm X) s)
    end.
Proof.
  specialize (equivocator_vlsm_trace_project_inv _ Hntr j fj) as Hj.
  spec Hj. { rewrite HtrX. intro contra. congruence. }
  spec Hj is.
  exists Hj.
  destruct
    (preloaded_equivocator_vlsm_project_protocol_trace _ _ Htr _ Hj fj)
    as [trX' [di' [HtrX' Hdi]]].
  rewrite HtrX in HtrX'.
  inversion HtrX'. subst di' trX'.  clear HtrX'.
  assumption.
Qed.

End equivocator_vlsm_projections.
