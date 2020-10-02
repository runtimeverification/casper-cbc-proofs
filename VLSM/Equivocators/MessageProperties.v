Require Import
  List ListSet Coq.Vectors.Fin
  Arith.Compare_dec Lia
  Program
  .
Import ListNotations.
From CasperCBC
  Require Import
    Preamble ListExtras ListSetExtras FinExtras
    VLSM.Common VLSM.Equivocation
    VLSM.Equivocators.Common VLSM.Equivocators.Projections
    .

Section equivocator_vlsm_message_properties.

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

End equivocator_vlsm_message_properties.
