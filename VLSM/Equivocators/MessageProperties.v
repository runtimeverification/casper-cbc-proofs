From Coq Require Import List ListSet Vectors.Fin Arith.Compare_dec Lia Program.
Import ListNotations.

From CasperCBC
  Require Import
    Preamble ListExtras ListSetExtras FinExtras
    VLSM.Common VLSM.Equivocation
    VLSM.Equivocators.Common VLSM.Equivocators.Projections
    .

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

Section has_been_sent_lifting.

(** ** Lifting the [has_been_sent_capability]
*)


Context
  {Hbs : has_been_sent_capability X}
  .

(** We define [has_been_sent] for the [equivocator_vlsm] as being sent by any
of the internal machines.
*)
Definition equivocator_has_been_sent
  (s : vstate equivocator_vlsm)
  (m : message)
  : Prop
  :=
  let (n, bs) := s in
  exists i: Fin.t (S n), has_been_sent X (bs i) m.

Global Instance equivocator_has_been_sent_dec
  : RelDecision equivocator_has_been_sent.
Proof.
  intros [n bs] m.
  apply (Decision_iff
           (P:=Exists (fun i => has_been_sent X (bs i) m) (fin_t_listing (S n)))).
  - unfold equivocator_has_been_sent. rewrite Exists_exists.
    split.
    * intros [x [_ H]];exists x;exact H.
    * intros [i H];exists i;split;[solve[apply fin_t_full]|exact H].
  - apply Exists_dec.
Qed.

(**
The [equivocator_vlsm] has the [selected_messages_consistency_prop]
for [output] messages, meaning that if a message is sent in a trace leading
to state s, then it must be seen in all traces.
*)
Lemma equivocator_has_been_sent_consistency
  (s : vstate equivocator_vlsm)
  (Hs : protocol_state_prop (pre_loaded_with_all_messages_vlsm equivocator_vlsm) s)
  (m : message)
  : selected_messages_consistency_prop equivocator_vlsm (field_selector output) s m.
Proof.
  split.
  - intros [bis [btr [Hbtr' Hsome]]].
    pose proof (ptrace_forget_last Hbtr') as Hbtr.
    pose proof (ptrace_get_last Hbtr') as Hlast.

    destruct (equivocator_vlsm_trace_project_output_reflecting_inv _ _ (proj1 Hbtr) _ Hsome)
      as [j [i [_ [_ [trX [Hproject Hsomex]]]]]].
    destruct j as [sj | j fj];
      [solve[rewrite equivocator_vlsm_trace_project_on_new_machine in Hproject
      ; inversion Hproject; subst; inversion Hsomex]|].
    assert (Hntr : btr <> []) by (intro contra; subst; inversion Hsome).
    specialize
      (preloaded_equivocator_vlsm_protocol_trace_project_inv2 _ _ _ _ Hntr (proj1 Hbtr') _ _ _ _ Hproject)
      as HpreX.
    simpl in *.
    destruct HpreX as [Hj Hi].
    assert (Hsj : protocol_state_prop (pre_loaded_with_all_messages_vlsm X) (projT2 s (of_nat_lt Hj))).
    { simpl.  simpl in *.
      specialize
        (finite_ptrace_last_pstate (pre_loaded_with_all_messages_vlsm equivocator_vlsm) _ _  (proj1 Hbtr))
        as Hpbs.
      simpl in *.
      rewrite Hlast in Hpbs.
      apply (preloaded_equivocator_state_project_protocol_state _ _ Hpbs).
    }
    assert (Hall : selected_message_exists_in_all_preloaded_traces X (field_selector output) (projT2 s (of_nat_lt Hj)) m).
    { apply has_been_sent_consistency; [assumption|assumption|].
      destruct i as [sn | i fi].
      - exists sn, trX.
        split;assumption.
      - destruct Hi as [Hi [HtrX HinitX]].
        exists (projT2 bis (of_nat_lt Hi)). exists trX.
        split;[|assumption].
        split;[assumption|].
        apply HinitX. apply Hbtr.
    }
    clear -Hall MachineDescriptor equivocator_vlsm.
    intros bis btr Hbtr.
    destruct
      (preloaded_equivocator_vlsm_project_protocol_trace _ _ _ _ (proj1 Hbtr) _ Hj false)
      as [trX [di [Hproject Hdi]]].
    apply
      (equivocator_vlsm_trace_project_output_reflecting  _ _ _ _ Hproject m).
    destruct di as [sn | i fi].
    + apply (Hall _ _ Hdi).
    + destruct Hdi as [Hi [HtrX HinitX]].
      specialize (HinitX (proj2 Hbtr)).
      apply (Hall _ _ (conj HtrX HinitX)).
  - intro Hall.
    destruct Hs as [om Hs].
    apply (protocol_is_trace (pre_loaded_with_all_messages_vlsm equivocator_vlsm)) in Hs.
    destruct Hs as [Hinit | [is [tr [Htr  _]]]]
    ; [elim (selected_message_exists_in_all_traces_initial_state equivocator_vlsm s Hinit (field_selector output) m)
      ; assumption|].
    exists is. exists tr. exists Htr.
    apply (Hall _ _ Htr).
Qed.

(**
[equivocator_has_been_sent] has [proper_sent] property.
*)
Lemma equivocator_proper_sent
  (s : vstate equivocator_vlsm)
  (Hs : protocol_state_prop (pre_loaded_with_all_messages_vlsm equivocator_vlsm) s)
  (m : message)
  : has_been_sent_prop equivocator_vlsm equivocator_has_been_sent s m.
Proof.
  split.
  - intro Hbbs. intro start; intros.
    destruct s as (n, bs).
    destruct Hbbs as [j Hjbs].
    apply (proper_sent X) in Hjbs
    ; [|apply (preloaded_equivocator_state_project_protocol_state _ _ Hs j)].
    specialize (preloaded_equivocator_vlsm_project_protocol_trace _ start _ tr (proj1 Htr)) as Hpre.
    assert (Hj := of_nat_to_nat_inv j).
    simpl in *.
    destruct (to_nat j) as [nj Hnj]. simpl in Hj.
    specialize (Hpre nj Hnj false).
    destruct Hpre as [trX [di [Hproject Hdi]]].
    destruct di as [sn | i fi].
    + rewrite Hj in Hdi.
      spec Hjbs sn trX Hdi.
      apply equivocator_vlsm_trace_project_output_reflecting with trX (Existing _ nj false) (NewMachine _ sn)
      ; assumption.
    + destruct Hdi as [Hi [HtrX HinitX]].
      specialize (HinitX (proj2 Htr)).
      rewrite Hj in HtrX.
      spec Hjbs (projT2 start (of_nat_lt Hi)) trX (conj HtrX HinitX).
      apply equivocator_vlsm_trace_project_output_reflecting with trX (Existing _ nj false) (Existing _ i fi)
      ; assumption.
  - intro Hbbs. assert (Hbbs' := Hbbs).
    destruct Hs as [om Hs].
    apply (protocol_is_trace (pre_loaded_with_all_messages_vlsm equivocator_vlsm)) in Hs.
    destruct Hs as [Hinit | [is [tr [Htr _]]]]
    ; [elim (selected_message_exists_in_all_traces_initial_state equivocator_vlsm s Hinit (field_selector output) m)
      ; assumption|].
    spec Hbbs is tr Htr.
    destruct
      (equivocator_vlsm_trace_project_output_reflecting_inv _ _ (ptrace_forget_last (proj1 Htr)) _ Hbbs)
      as [j [i [_ [_ [trX [HtrX Hjbs]]]]]].
    assert (Hntr : tr <> []) by (intro contra; subst; inversion Hbbs).
    destruct j as [sj | j fj]
    ; [rewrite equivocator_vlsm_trace_project_on_new_machine in HtrX
      ; inversion HtrX; subst; inversion Hjbs
      |].
    specialize
      (preloaded_equivocator_vlsm_protocol_trace_project_inv2 _ _ _ _ Hntr (proj1 Htr) _ _ _ _ HtrX)
      as HpreX.
    simpl in *.
    destruct HpreX as [Hj Hi].
    unfold equivocator_has_been_sent.
    destruct s as (ns, bs).
    exists (of_nat_lt Hj).
    assert (Hbsj : protocol_state_prop (pre_loaded_with_all_messages_vlsm X) (bs (of_nat_lt Hj))).
    { apply ptrace_last_pstate in Htr as Hpbs.
      apply (preloaded_equivocator_state_project_protocol_state _ _ Hpbs).
    }
    apply (proper_sent X); [assumption|].
    apply has_been_sent_consistency; [assumption|assumption|].
    destruct i as [sn | i fi].
    + exists sn. exists trX. exists Hi. assumption.
    + destruct Hi as [Hi [Htrx HinitX]]. specialize (HinitX (proj2 Htr)).
      exists (projT2 is (of_nat_lt Hi)).
      exists trX. exists (conj Htrx HinitX).
      assumption.
Qed.

(**
[equivocator_has_been_sent] has [proper_not_sent] property.
*)
Lemma equivocator_proper_not_sent
  (s : vstate equivocator_vlsm)
  (Hs : protocol_state_prop (pre_loaded_with_all_messages_vlsm equivocator_vlsm) s)
  (m : message)
  (equivocator_has_not_been_sent := fun s m => ~ equivocator_has_been_sent s m)
  : has_not_been_sent_prop equivocator_vlsm equivocator_has_not_been_sent s m.
Proof.
  apply has_been_sent_consistency_proper_not_sent.
  - typeclasses eauto.
  - apply equivocator_proper_sent. assumption.
  - apply equivocator_has_been_sent_consistency. assumption.
Qed.

(** Finally we define the [has_been_sent_capability] for the [equivocator_vlsm].
*)
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

(** ** Lifting the [computable_sent_messages] property
*)

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
Definition equivocator_computable_sent_messages
  : computable_sent_messages equivocator_vlsm
  :=
  {|
    sent_messages_fn := equivocator_sent_messages_fn;
    sent_messages_full := equivocator_sent_messages_full;
    sent_messages_consistency := @equivocator_has_been_sent_consistency Hbeen_sent_X
  |}.

End computable_sent_messages_lifting.

End equivocator_vlsm_message_properties.
