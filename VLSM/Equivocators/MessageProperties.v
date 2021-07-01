From Coq Require Import List ListSet Vectors.Fin Arith.Compare_dec Lia Program.
Import ListNotations.

From CasperCBC
  Require Import
    Preamble ListExtras ListSetExtras FinExtras
    VLSM.Common VLSM.Equivocation
    VLSM.Equivocators.Common VLSM.Equivocators.Projections
    .

Local Arguments le_lt_dec : simpl never.
Local Arguments nat_eq_dec : simpl never.

(** * VLSM Message Properties *)

Section equivocator_vlsm_message_properties.

(** ** Lifting properties about sent messages to the equivocators

In this section we first prove some general properties about sent messages
being preserved and reflected by the [equivocator_vlsm], and then we show
that the [has_been_sent_capability] and the [computable_sent_messages]
can be lifted (each separately) from the original machine to the
[equivocator_vlsm].
*)


Context
  {message : Type}
  (X : VLSM message)
  (equivocator_vlsm := equivocator_vlsm X)
  (MachineDescriptor := MachineDescriptor X)
  .

(**
If a projection of an [equivocator_vlsm] trace [output]s a message, then
the original trace must do so too.
*)
Lemma equivocator_vlsm_trace_project_output_reflecting
  (tr: list (vtransition_item equivocator_vlsm))
  (trX: list (vtransition_item X))
  (j i : MachineDescriptor)
  (HtrX: equivocator_vlsm_trace_project _ tr j = Some (trX, i))
  (m : message)
  (Hjbs: Exists (field_selector output m) trX)
  : Exists (field_selector output m) tr.
Proof.
  generalize dependent i. generalize dependent trX.
  induction tr; intros.
  - inversion HtrX. subst. inversion Hjbs.
  - simpl in HtrX.
    destruct (equivocator_vlsm_trace_project _ tr j) as [(trX', i')|]
      eqn:Htr; [|congruence].
    specialize (IHtr trX').
    destruct (equivocator_vlsm_transition_item_project _ a i') as [[[item'|] i'']|]
      eqn:Hitem'
    ; inversion HtrX; subst; clear HtrX.
    + apply equivocator_transition_item_project_inv_messages in Hitem'.
      destruct Hitem' as [_ [_ [_ [_ [_ Ha]]]]].
      inversion Hjbs; subst.
      * left. simpl in Ha. simpl.  rewrite Ha. assumption.
      * specialize (IHtr H0 i' eq_refl). right. assumption.
    + specialize (IHtr Hjbs i' eq_refl). right. assumption.
Qed.

Lemma preloaded_equivocator_vlsm_trace_project_protocol_item_new_machine
  (bs : vstate equivocator_vlsm)
  (btr : list (vtransition_item equivocator_vlsm))
  (Hbtr : finite_protocol_trace_from (pre_loaded_with_all_messages_vlsm equivocator_vlsm) bs btr)
  (bitem : vtransition_item equivocator_vlsm)
  (Hitem : In bitem btr)
  (sn : state)
  (Hnew : snd (l bitem) = NewMachine _ sn)
  : input bitem = None /\ output bitem = None /\
    exists
      (d : MachineDescriptor),
      equivocator_vlsm_transition_item_project _ bitem d = Some (None, snd (l bitem)).
Proof.
  apply in_split in Hitem.
  destruct Hitem as [bprefix [bsuffix Heq]].
  subst btr.
  apply (finite_protocol_trace_from_app_iff (pre_loaded_with_all_messages_vlsm equivocator_vlsm)) in Hbtr.
  destruct Hbtr as [Hbprefix Hbsuffix].
  match type of Hbsuffix with
  | finite_protocol_trace_from _ ?l _ =>
  remember l as lst
  end.
  inversion Hbsuffix. subst s' tl.
  destruct H3 as [[_ [_ Hv]] Ht].
  simpl.
  specialize
    (equivocator_protocol_transition_item_project_inv5_new_machine
      _ l s lst iom oom Hv Ht)
    as Hpitem.
  replace (@Build_transition_item message (@type message (@Common.equivocator_vlsm message X)) l iom s oom)
    with bitem in Hpitem.
  unfold Common.l in *.
  destruct l as [l dl].
  unfold snd in *.
  rewrite <- H in Hnew.
  rewrite H in *.
  subst dl.
  specialize (Hpitem false _ eq_refl). destruct Hpitem as [i [Hi Hpitem]].
  simpl in Ht. unfold vtransition in Ht. simpl in Ht.
  inversion Ht. destruct Hv as [Hsndl Hiom].
  subst.
  split; [reflexivity|].
  split; [reflexivity|].
  eexists _. exact Hpitem.
Qed.

(**
For any [transition_item] in a protocol trace segment of an
[equivocator_vlsm] there exists a projection of that trace containing
the projection of the item.
*)
Lemma preloaded_equivocator_vlsm_trace_project_protocol_item
  (bs bf : vstate equivocator_vlsm)
  (btr : list (vtransition_item equivocator_vlsm))
  (Hbtr : finite_protocol_trace_from_to (pre_loaded_with_all_messages_vlsm equivocator_vlsm) bs bf btr)
  (bitem : vtransition_item equivocator_vlsm)
  (Hitem : In bitem btr)
  (idl : nat)
  (fdl : bool)
  (Hlbitem : snd (l bitem) = Existing _ idl fdl)
  : exists (item : vtransition_item X),
      (exists (d : MachineDescriptor),
        equivocator_vlsm_transition_item_project _ bitem d = Some (Some item, snd (l bitem)))
      /\ exists (tr : list (vtransition_item X)),
        In item tr /\
        exists (dfinal dfirst : MachineDescriptor),
          proper_descriptor X dfirst bs /\
          not_equivocating_descriptor X dfinal (finite_trace_last bs btr) /\
          equivocator_vlsm_trace_project _ btr dfinal = Some (tr, dfirst).
Proof.
  specialize (preloaded_equivocator_vlsm_protocol_trace_project_inv2 X bs bf btr) as Hinv2.
  spec Hinv2. { intro contra. subst. inversion Hitem. }
  spec Hinv2 Hbtr.
  apply in_split in Hitem.
  destruct Hitem as [bprefix [bsuffix Heq]].
  subst btr.
  apply (finite_protocol_trace_from_to_app_split (pre_loaded_with_all_messages_vlsm equivocator_vlsm)) in Hbtr.
  destruct Hbtr as [Hbprefix Hbsuffix].
  match type of Hbsuffix with
  | finite_protocol_trace_from_to _ ?l _ _ =>
  remember l as lst
  end.
  inversion Hbsuffix. subst s' tl.
  destruct H4 as [[_ [_ Hv]] Ht].
  specialize
    (equivocator_protocol_transition_item_project_inv5 _ l s lst iom oom Hv Ht) as Hpitem.
  replace (@Build_transition_item message (@type message (@Common.equivocator_vlsm message X)) l iom s oom)
    with bitem in Hpitem.
  unfold Common.l in *.
  destruct l as [l dl].
  unfold snd in *.
  rewrite H in *.
  rewrite <- H in Hlbitem. subst dl.
  destruct (Hpitem false _ _ eq_refl) as [i [Hi [itemx Hitemx]]].
  pose (dfinal := Existing X i false).
  apply ptrace_forget_last in H3.
  destruct
    (preloaded_equivocator_vlsm_trace_project_protocol_inv _ _ _ H3 _ Hi false)
    as [fsuffix [suffix Hsuffix]].
  specialize (Hpitem fsuffix _ _ eq_refl).
  destruct Hpitem as [_i [_Hi [_itemx _Hitemx]]].
  destruct
    (equivocator_vlsm_transition_item_project_some_inj _ Hitemx _Hitemx)
    as [H_i [H_itemx _]].
  subst _i _itemx. clear Hitemx. clear _Hi.
  exists itemx. split; [eexists _; apply _Hitemx|].
  remember (Existing _ i fsuffix) as dsuffix.
  assert (Hitem : equivocator_vlsm_trace_project _ [bitem] dsuffix = equivocator_vlsm_trace_project _ [bitem] dsuffix)
    by reflexivity.
  remember [bitem] as lbitem. rewrite Heqlbitem in Hitem at 2.
  simpl in Hitem.
  rewrite _Hitemx in Hitem.
  specialize
    (equivocator_vlsm_trace_project_app_inv _ _ _ _ _ _ _ _ Hitem Hsuffix)
    as Hsuffix'.
  rewrite <- H in _Hitemx.
  destruct
    (equivocator_protocol_transition_item_project_inv2 _ (l, Existing _ idl fdl) lst s iom oom Hv Ht _ _ _ _Hitemx)
    as [_i [_fi [_Hdsuffix [_Hi [Heqitemx Hd']]]]].
  rewrite Heqdsuffix in _Hdsuffix. inversion _Hdsuffix. subst _i _fi. clear _Hdsuffix.
  replace (of_nat_lt _Hi) with (of_nat_lt Hi) in * by apply of_nat_ext. clear _Hi.
  destruct Hd' as [_i' [_fi' [_Heq [id [Hvs' Hts']]]]].
  inversion _Heq. subst _i' _fi'. clear _Heq.
  subst lst.
  destruct
    (preloaded_equivocator_vlsm_trace_project_protocol _ _ _ _ Hbprefix idl id fdl)
    as [prefix [dfirst [Hprefix _]]].
  specialize
    (equivocator_vlsm_trace_project_app_inv _ _ _ _ _ _ _ _ Hprefix Hsuffix')
    as Htr.
  subst lbitem.
  simpl in Htr.
  exists (prefix ++ itemx :: suffix).
  specialize (Hinv2 _ _ _ _ Htr).
  destruct Hinv2 as [Hdfinal Hdinitial].
  split.
  - apply in_app_iff. right. left. reflexivity.
  - eexists _. eexists _. repeat split; [..|apply Htr].
    2:{
      apply equivocator_vlsm_trace_project_inv with (fj:=false).
      destruct bprefix;discriminate.
      fold equivocator_vlsm in Htr.
      rewrite Htr.
      discriminate.
    }
    clear -Hdinitial.
    destruct dfirst as [sn | j fj].
    + destruct Hdinitial as [_ Hinit]. assumption.
    + destruct Hdinitial as [Hdinitial _]. assumption.
Qed.

(**
If an [equivocator_vlsm]'s protocol trace segment [output]s a message, then
one of its projections must do so too.
*)
Lemma equivocator_vlsm_trace_project_output_reflecting_inv
  (is: vstate equivocator_vlsm)
  (tr: list (vtransition_item equivocator_vlsm))
  (Htr: finite_protocol_trace_from (pre_loaded_with_all_messages_vlsm equivocator_vlsm) is tr)
  (m : message)
  (Hbbs : Exists (field_selector output m) tr)
  : exists
    (j i : MachineDescriptor)
    (Hi : proper_descriptor X i is)
    (Hj : not_equivocating_descriptor X j (finite_trace_last is tr))
    (trX: list (vtransition_item X))
    (HtrX: equivocator_vlsm_trace_project _ tr j = Some (trX, i))
    ,
    Exists (field_selector output m) trX.
Proof.
  apply Exists_exists in Hbbs.
  destruct Hbbs as [item [Hin Houtput]].
  destruct (snd (l item)) as [sn | i fi] eqn:Hsndl.
  - specialize
    (preloaded_equivocator_vlsm_trace_project_protocol_item_new_machine
       _ _ Htr _ Hin _ Hsndl)
    as Hitem.
    destruct Hitem as [_ [Hcontra _]]. congruence.
  - apply ptrace_add_last with (f:=finite_trace_last is tr) in Htr;[|reflexivity].
    specialize
    (preloaded_equivocator_vlsm_trace_project_protocol_item
       _ _ _ Htr _ Hin _ _ Hsndl)
    as Hitem.
  destruct Hitem as [itemx [[d Hitemx] [trx [Hinx [ifinal [ifirst [Hifirst [Hifinal Htrx]]]]]]]].
  exists ifinal. exists ifirst. split; [assumption|].
  split; [assumption|].
  exists trx. exists Htrx.
  apply Exists_exists. exists itemx. split; [assumption|].
  apply equivocator_transition_item_project_inv_messages in Hitemx.
  destruct Hitemx as [_ [_ [_ [_ [_ Hitemx]]]]].
  simpl in *.
  congruence.
Qed.

Section oracle_lifting.

Context
  selector
  (Hselector_None : forall l s m, ~ selector m {| l:= l; input := None; destination := s; output := None |})
  (Hselector_io : forall l1 l2 s1 s2 im om m, selector m  {| l:= l1; input := im; destination := s1; output := om |} <-> selector m  {| l:= l2; input := im; destination := s2; output := om |})
  oracle
  (Hdec : RelDecision oracle)
  (Hstepwise : oracle_stepwise_props (vlsm := X) selector oracle).

Definition equivocator_selector : message -> vtransition_item equivocator_vlsm -> Prop.
Proof.
  intros m item.
  destruct item.
  destruct l.
  destruct destination.
  exact (selector m {| l := v; destination := (v0 F1); input := input; output := output |}).
Defined.

(** We define [equivocator_oracle] for the [equivocator_vlsm] as being the oracle for any
of the internal machines.
*)
Definition equivocator_oracle
  (s : vstate equivocator_vlsm)
  (m : message)
  : Prop
  :=
  let (n, bs) := s in
  exists i: Fin.t (S n), oracle (bs i) m.

Lemma equivocator_oracle_dec
  : RelDecision equivocator_oracle.
Proof.
  intros [n bs] m.
  apply (Decision_iff
           (P:=Exists (fun i => oracle (bs i) m) (fin_t_listing (S n)))).
  - unfold equivocator_oracle. rewrite Exists_exists.
    split.
    * intros [x [_ H]];exists x;exact H.
    * intros [i H];exists i;split;[solve[apply fin_t_full]|exact H].
  - apply Exists_dec.
Qed.

Lemma equivocator_oracle_stepwise_props
  : oracle_stepwise_props (vlsm := equivocator_vlsm) equivocator_selector equivocator_oracle.
Proof.
  destruct Hstepwise.
  split; intros.
  - destruct s as (n, bs). destruct H as [Hn His]. simpl in *. subst.
    intros [j Hmbrj]. dependent destruction j; [|inversion j].
    elim (oracle_no_inits  _ His m). assumption.
  - unfold equivocator_oracle.
    destruct s as (ns,bs). destruct s' as (ns', bs'). destruct l as (l, desc).
    destruct H as [[Hs [_ Hv]] Ht].
    
    simpl in Hv. unfold vvalid in Hv. simpl in Hv.
    simpl in Ht. unfold_vtransition Ht.
    destruct desc as [sdesc | idesc fdesc].
    + inversion Ht. subst. simpl_existT. subst. clear Ht.
      simpl. destruct Hv as [Hisdesc Him]. subst im.
      split.
      * intros [ins Hir]. right.
        destruct (to_nat ins) as (i, Hi).
        destruct (nat_eq_dec i (S ns))
        ; [elim (oracle_no_inits _ Hisdesc msg); assumption|].
        assert (Hi' : i < S ns) by lia.
        exists (of_nat_lt Hi').
        replace (of_nat_lt Hi') with (of_nat_lt (Common.equivocator_state_extend_obligation_1 ns i Hi n)) by apply of_nat_ext.
        assumption.
      * intros [H | [ins Hir]]; [elim (Hselector_None l (bs F1) msg); assumption |].
        destruct (to_nat ins) as (i, Hi) eqn:Hins.
        assert (Hi' : i < S (S ns)) by lia.
        exists (of_nat_lt Hi').
        rewrite to_nat_of_nat.
        destruct (nat_eq_dec i (S ns)); [lia|].
        replace (of_nat_lt (Common.equivocator_state_extend_obligation_1 ns i Hi' n)) with ins; [assumption|].
        rewrite <- (of_nat_to_nat_inv ins). rewrite Hins.
        apply of_nat_ext.
    + destruct Hv as [Hidesc Hv].
      destruct (le_lt_dec  (S ns) idesc); [lia|].
      replace (of_nat_lt l0) with (of_nat_lt Hidesc) in Ht by apply of_nat_ext. clear l0.
      destruct (vtransition X l (bs (of_nat_lt Hidesc), im)) eqn:Htx.
      specialize
        (oracle_step_update l (bs (of_nat_lt Hidesc)) im s o).
      spec oracle_step_update.
      { repeat split
        ; [..| eexists _; apply (pre_loaded_with_all_messages_message_protocol_prop X)|assumption|assumption].
        apply (preloaded_equivocator_state_project_protocol_state X _ Hs).
      }
      spec oracle_step_update msg.
      simpl in *.
      destruct fdesc; inversion Ht; subst; clear Ht; simpl_existT; subst; split.
      * intros [i Hbri]. destruct (to_nat i) as (j, Hj) eqn:Heqi.
        destruct (nat_eq_dec j (S ns)); [|right; eexists _; apply Hbri].
        subst.
        apply oracle_step_update in Hbri.
        unfold to_nat. destruct (nat_eq_dec 0 (S ns)); [lia|].
        destruct Hbri as [H | Hbri]; [| right; eexists _; apply Hbri].
        left. revert H. apply Hselector_io.
      * apply proj2 in oracle_step_update.
        intros [Heq_im | [ins Hbri]].
        -- rewrite Hselector_io with (l2 := l) (s2 := s) in Heq_im.
          specialize (oracle_step_update (or_introl Heq_im)).
          assert (Hi' : S ns < S (S ns)) by lia.
          exists (of_nat_lt Hi').
          rewrite to_nat_of_nat.
          destruct (nat_eq_dec (S ns) (S ns)); [|lia].
          assumption.
        -- pose proof (of_nat_to_nat_inv ins) as Hins. rewrite <- Hins in *.
          destruct (eq_dec (of_nat_lt (proj2_sig (to_nat ins))) ((of_nat_lt Hidesc))).
          ++ rewrite e in *.
            specialize (oracle_step_update (or_intror Hbri)).
            assert (Hi' : S ns < S (S ns)) by lia.
            exists (of_nat_lt Hi').
            rewrite to_nat_of_nat.
            destruct (nat_eq_dec (S ns) (S ns)); [|lia].
            assumption.
          ++ destruct (to_nat ins) eqn:Heq_to_nat_ins.
            simpl in *. subst ins. clear Heq_to_nat_ins.
            assert (l0' : x < S (S ns)) by lia.
            exists (of_nat_lt l0').
            rewrite to_nat_of_nat.
            destruct (nat_eq_dec x (S ns)); [lia|].
            replace (of_nat_lt (Common.equivocator_state_extend_obligation_1 ns x l0' n0))
              with (of_nat_lt l0)
              by apply of_nat_ext.
            assumption.
      * intros [i Hbri].
        destruct (eq_dec (of_nat_lt Hidesc) i)
        ; [| right; eexists _; apply Hbri].
        apply oracle_step_update in Hbri.
        destruct Hbri as [H | Hbri]; [|right; eexists _; apply Hbri].
        left. revert H. apply Hselector_io.
      * apply proj2 in oracle_step_update.
        intros [Heq_im | [ins Hbri]].
        -- rewrite Hselector_io with (l2 := l) (s2 := s) in Heq_im.
          specialize (oracle_step_update (or_introl Heq_im)).
          exists (of_nat_lt Hidesc).
          rewrite eq_dec_if_true by reflexivity.
          assumption.
        -- pose proof (of_nat_to_nat_inv ins) as Hins. rewrite <- Hins in *.
          destruct (eq_dec ((of_nat_lt Hidesc))  (of_nat_lt (proj2_sig (to_nat ins)))).
          ++ rewrite <- e in *.
            specialize (oracle_step_update (or_intror Hbri)).
            exists (of_nat_lt Hidesc).
            rewrite eq_dec_if_true by reflexivity.
            assumption.
          ++ destruct (to_nat ins) eqn:Heq_to_nat_ins.
            simpl in *. subst ins. clear Heq_to_nat_ins.
            exists (of_nat_lt l0).
            rewrite eq_dec_if_false by assumption.
            assumption.
Qed.

End oracle_lifting.

Section has_been_received_lifting.

(** ** Lifting the [has_been_received_capability] *)

Context
  {Hbr : has_been_received_capability X}
  .

(** We define [has_been_received] for the [equivocator_vlsm] as being received by any
of the internal machines.
*)
Definition equivocator_has_been_received  := equivocator_oracle (has_been_received X).

Global Instance equivocator_has_been_received_dec
  : RelDecision equivocator_has_been_received
  := equivocator_oracle_dec (has_been_received X) _.

Lemma equivocator_has_been_received_stepwise_props
  : has_been_received_stepwise_props (vlsm := equivocator_vlsm) equivocator_has_been_received.
Proof.
  assert (Hreceived_stepwise : oracle_stepwise_props (field_selector input) (has_been_received X)).
  { destruct Hbr.  apply stepwise_props_from_trace; assumption. }
  specialize (equivocator_oracle_stepwise_props (field_selector input)) as Hlift.
  spec Hlift. { intros. simpl. intro. congruence. }
  spec Hlift. { intros. simpl. split; exact id. }
  specialize (Hlift _ Hreceived_stepwise).
  match type of Hlift with
  | oracle_stepwise_props ?s _ => replace s with (field_selector (T := type equivocator_vlsm) input) in Hlift
  end
  ; [assumption|].
  apply functional_extensionality_dep_good. intro msg.
  apply functional_extensionality_dep_good. intro item; destruct item.
  destruct l. destruct destination. simpl. reflexivity.
Qed.

(** Finally we define the [has_been_received_capability] for the [equivocator_vlsm].
*)
Definition equivocator_has_been_received_capability
  : has_been_received_capability equivocator_vlsm
  := has_been_received_capability_from_stepwise (vlsm := equivocator_vlsm)
    equivocator_has_been_received_dec
    equivocator_has_been_received_stepwise_props.

End has_been_received_lifting.

Section has_been_sent_lifting.

(** ** Lifting the [has_been_sent_capability] *)

Context
  {Hbs : has_been_sent_capability X}
  .

(** We define [has_been_sent] for the [equivocator_vlsm] as being sent by any
of the internal machines.
*)
Definition equivocator_has_been_sent  := equivocator_oracle (has_been_sent X).

Global Instance equivocator_has_been_sent_dec
  : RelDecision equivocator_has_been_sent
  := equivocator_oracle_dec (has_been_sent X) _.

Lemma equivocator_has_been_sent_stepwise_props
  : has_been_sent_stepwise_props (vlsm := equivocator_vlsm) equivocator_has_been_sent.
Proof.
  assert (Hsent_stepwise : oracle_stepwise_props (field_selector output) (has_been_sent X)).
  { destruct Hbs.  apply stepwise_props_from_trace; assumption. }
  specialize (equivocator_oracle_stepwise_props (field_selector output)) as Hlift.
  spec Hlift. { intros. simpl. intro. congruence. }
  spec Hlift. { intros. simpl. split; exact id. }
  specialize (Hlift _ Hsent_stepwise).
  match type of Hlift with
  | oracle_stepwise_props ?s _ => replace s with (field_selector (T := type equivocator_vlsm) output) in Hlift
  end
  ; [assumption|].
  apply functional_extensionality_dep_good. intro msg.
  apply functional_extensionality_dep_good. intro item; destruct item.
  destruct l. destruct destination. simpl. reflexivity.
Qed.

(** Finally we define the [has_been_received_capability] for the [equivocator_vlsm].
*)
Definition equivocator_has_been_sent_capability
  : has_been_sent_capability equivocator_vlsm
  := has_been_sent_capability_from_stepwise (vlsm := equivocator_vlsm)
    equivocator_has_been_sent_dec
    equivocator_has_been_sent_stepwise_props.

End has_been_sent_lifting.

Section computable_sent_messages_lifting.

(** ** Lifting the [computable_sent_messages] property *)

Context
  {Hsent_messages : computable_sent_messages X}
  (message_eq : EqDecision message)
  (Hbeen_sent_X := @computable_sent_messages_has_been_sent_capability message X Hsent_messages message_eq)
  .

(** We define the [sent_messages_fn] for the [equivocator_vlsm] as the
union of all [sent_messages_fn] for its internal machines.
*)
Definition equivocator_sent_messages_fn
  (s : vstate equivocator_vlsm)
  : set message
  :=
  fold_right (set_union decide_eq) []
    (map (fun i => sent_messages_fn X (projT2 s i)) (fin_t_listing (S (projT1 s)))).

(** [equivocator_sent_messages_fn] captures all [sent_messages] for that state.
*)
Lemma equivocator_sent_messages_full
  (s : vstate equivocator_vlsm)
  (Hs : protocol_state_prop (pre_loaded_with_all_messages_vlsm equivocator_vlsm) s)
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
    apply (sent_messages_full X) in Hin; [|assumption].
    destruct Hin as [[m' Hm] Heq]. simpl in Heq. subst m'.
    apply (sent_messages_consistency X) in Hm; [|assumption].
    destruct Hs as [om Hs].
    apply (protocol_is_trace (pre_loaded_with_all_messages_vlsm equivocator_vlsm)) in Hs.
    destruct Hs as [Hs | [is [tr [Htr _]]]].
    + specialize (Hm (projT2 s i) []).
      spec Hm.
      { split.
        - constructor. assumption.
        - destruct Hs as [Hzero His].
          destruct s as [n s]. simpl in *. subst n.
          dependent destruction i; [|inversion i].
          assumption.
      }
      inversion Hm.
    + apply ptrace_get_last in Htr as Hlst.
      assert (Hinv := of_nat_to_nat_inv i).
      destruct (to_nat i) as [ni Hi]. simpl in Hinv. subst i.
      assert (Hbm : selected_message_exists_in_some_preloaded_traces equivocator_vlsm (field_selector output) s m)
      ; [|exists (exist _ m Hbm); reflexivity].
      exists is. exists tr. exists Htr.
      subst s.
      destruct
        (preloaded_equivocator_vlsm_project_protocol_trace _ _ _ _ (proj1 Htr) _ Hi false)
        as [trX [di Hdi]].
      destruct di as [sn | i fi].
      * destruct Hdi as [Hproject HtrX].
        apply equivocator_vlsm_trace_project_output_reflecting with trX (Existing _ ni false) (NewMachine _ sn)
        ; [assumption|].
        apply (Hm _ _ HtrX).
      * destruct Hdi as [Hproject [Hi' [HtrX HinitX]]]. specialize (HinitX (proj2 Htr)).
        apply equivocator_vlsm_trace_project_output_reflecting with trX (Existing _ ni false) (Existing _ i fi)
        ; [assumption|].
        apply (Hm _ _ (conj HtrX HinitX)).
  - intros [[m' Hm] Heq]. simpl in Heq. subst m'.
    destruct Hm as [is [tr [Htr Hexists]]].
    destruct
      (equivocator_vlsm_trace_project_output_reflecting_inv _ _ (proj1 (ptrace_forget_last Htr)) _ Hexists)
      as [ifinal [istart [_ [_ [trX [Hproject HexistsX]]]]]].
    assert (Hntr : tr <> []) by (intro contra; subst; inversion Hexists).
    destruct ifinal as [sfinal | i ffinal]
    ; [
      rewrite equivocator_vlsm_trace_project_on_new_machine in Hproject
      ; inversion Hproject; subst; inversion HexistsX
      |].
    specialize
      (preloaded_equivocator_vlsm_protocol_trace_project_inv2 _ _ _ _ Hntr (proj1 Htr) _ _ _ _ Hproject)
      as HpreX.
    simpl in *.
    destruct HpreX as [Hi Histart].
    apply set_union_in_iterated. apply Exists_exists.
    exists (sent_messages_fn X (projT2 s (of_nat_lt Hi))).
    split.
    + apply in_map_iff. exists (of_nat_lt Hi).
      split; [reflexivity|]. apply fin_t_full.
    + apply (sent_messages_full X); [apply HpsX|].
      assert (Hm : selected_message_exists_in_some_preloaded_traces X (field_selector output) (projT2 s (of_nat_lt Hi)) m)
      ; [|exists (exist _ m Hm); reflexivity].
      destruct istart as [sstart | istart fstart].
      * exists sstart. exists trX. exists Histart. assumption.
      * destruct Histart as [Histart [HtrX HinitX]]. specialize (HinitX (proj2 Htr)).
        exists (projT2 is (of_nat_lt Histart)).
        exists trX. exists (conj HtrX HinitX).
        assumption.
Qed.

(** Finally, we define the [computable_sent_messages] instance for the
[equivocator_vlsm].
Note that we can reuse the consistency property proved above since
[computable_sent_messages] for <<X>> implies [has_been_sent_capability].
*)
Program Definition equivocator_computable_sent_messages
  : computable_sent_messages equivocator_vlsm
  :=
  {|
    sent_messages_fn := equivocator_sent_messages_fn;
    sent_messages_full := equivocator_sent_messages_full;
  |}.
Next Obligation.
  apply has_been_sent_consistency; [| assumption].
  apply (equivocator_has_been_sent_capability (Hbs := Hbeen_sent_X)).
Defined.

End computable_sent_messages_lifting.

End equivocator_vlsm_message_properties.
