Require Import List Nat Bool.
Import ListNotations.
Require Import Lia.
Require Import Logic.FunctionalExtensionality.
Require Import Program.

Require Import Coq.Logic.FinFun Coq.Logic.Eqdep.

From CasperCBC
Require Import Lib.ListExtras Lib.Preamble VLSM.Common VLSM.Composition VLSM.Equivocation.

Section sub_composition.

Context
  {message : Type}
  {index : Type}
  {IndEqDec : EqDecision index}
  (IM : index -> VLSM message)
  (sub_index_list : list index)
  (Hi0_sub : sub_index_list <> [])
  .

Definition sub_index_prop (i : index) : Prop := In i sub_index_list.

Local Instance sub_index_prop_dec
  (i : index)
  : Decision (sub_index_prop i).
Proof.
  apply in_dec. assumption.
Qed.

Definition sub_index : Type
  := dec_sig sub_index_prop.

Local Instance sub_index_i0 : Inhabited sub_index.
Proof.
  split.
  destruct (destruct_list sub_index_list) as [[x [tl Heq]]| n]
  ; [|elim Hi0_sub; assumption].
  exists x. apply bool_decide_eq_true.
  unfold sub_index_prop. subst sub_index_list. left. reflexivity.
Qed.

Local Instance sub_index_eq_dec : EqDecision sub_index.
Proof.
  apply dec_sig_eq_dec. assumption.
Qed.

Definition sub_IM
  (ei : sub_index)
  : VLSM message
  := IM (proj1_sig ei).

 Lemma sub_IM_state_update_eq
  (i : index)
  (s : composite_state sub_IM)
  (si : vstate (IM i))
  (e1 e2 : sub_index_prop i)
  : state_update sub_IM s (dec_exist _ i e1) si (dec_exist _ i e2) = si.
Proof.
  unfold dec_exist.
  assert
    (forall be1 be2, be1 = be2 -> state_update sub_IM s
      (exist _ i be1) si (exist _ i be2)
      = si).
  { intros. subst. apply state_update_eq. }
  apply H.
  apply bool_decide_eq_true_proof_irrelevance.
Qed.
 

Definition free_sub_vlsm_composition : VLSM message
  := free_composite_vlsm sub_IM.

Definition seeded_free_sub_composition
  (messageSet : message -> Prop)
  := pre_loaded_vlsm free_sub_vlsm_composition
      (fun m => messageSet m \/ composite_initial_message_prop IM m).

Local Lemma i0 : Inhabited index.
Proof.
  apply exists_last in Hi0_sub.
  destruct Hi0_sub as (_, (a, _)).
  constructor. exact a.
Qed.

Existing Instance i0.

Definition composite_state_sub_projection
  (s : composite_state IM)
  (subi : sub_index)
  : vstate (sub_IM subi)
  := s (proj1_sig subi).

Lemma composite_initial_state_sub_projection
  (s : composite_state IM)
  (Hs : composite_initial_state_prop IM s)
  : composite_initial_state_prop sub_IM (composite_state_sub_projection s).
Proof.
  intros (i, Hi). apply Hs.
Qed.

Definition composite_transition_item_sub_projection
  (item : composite_transition_item IM)
  (i := projT1 (l item))
  (e : sub_index_prop i)
  (j : sub_index := dec_exist _ i e)
  : composite_transition_item sub_IM
  :=
  @Build_transition_item _ (composite_type sub_IM) (existT _ j (projT2 (l item))) (input item) (composite_state_sub_projection (destination item)) (output item).

Lemma composite_state_transition_item_sub_projection
  (item : composite_transition_item IM)
  (i := projT1 (l item))
  (e : sub_index_prop i)
  (j : sub_index := dec_exist _ i e)
  : composite_state_sub_projection (destination item)
  = destination (composite_transition_item_sub_projection item e).
Proof.
  destruct item. destruct l. simpl in *. reflexivity.
Qed.

Definition composite_transition_item_sub_projection_proof_irrelevance
  (item : composite_transition_item IM)
  (i := projT1 (l item))
  (e1 e2 : sub_index_prop i)
  : composite_transition_item_sub_projection item e1 = composite_transition_item_sub_projection item e2.
Proof.
  destruct item. destruct l. unfold i in *. clear i.
  unfold composite_transition_item_sub_projection.
  simpl in *. f_equal.
  apply (@dec_sig_sigT_eq _ sub_index_prop sub_index_prop_dec (fun i => vlabel (IM i))).
  reflexivity.
Qed.

Definition from_sub_projection
  (a : composite_transition_item IM)
  : Prop
  := sub_index_prop (projT1 (l a)).

Fixpoint finite_trace_sub_projection
  (trx : list (composite_transition_item IM))
  : list (composite_transition_item sub_IM)
  :=
  match trx with
  | [] => []
  | item :: trx =>
    let tail := finite_trace_sub_projection trx in
    match decide (from_sub_projection item) with
    | left e => composite_transition_item_sub_projection item e :: tail
    | _ => tail
    end
  end.

Definition finite_trace_sub_projection_alt
  (trx : list (composite_transition_item IM))
  (ftrx := (filter (fun a => bool_decide (from_sub_projection a)) trx))
  (Hall: Forall from_sub_projection ftrx := filter_Forall trx)
  :=
  List.map
    (fun item : {a : composite_transition_item IM | from_sub_projection a} =>
      let (item, e) := item in
      composite_transition_item_sub_projection item e
    )
  (list_annotate from_sub_projection ftrx Hall).

Lemma finite_trace_sub_projection_alt_iff
  (trx : list (composite_transition_item IM))
  : finite_trace_sub_projection_alt trx = finite_trace_sub_projection trx.
Proof.
  unfold finite_trace_sub_projection_alt.
  match goal with
  |- context [list_annotate _ _ ?H] => generalize H as Hall
  end.
  induction trx; intros; [reflexivity|].
  simpl. unfold bool_decide at 1. unfold decide.
  simpl in Hall. unfold bool_decide in Hall at 1.
  destruct (sub_index_prop_dec (projT1 (l a))) eqn:Ha.
  - rewrite list_annotate_unroll.
    rewrite map_cons.
    f_equal.
    +  apply composite_transition_item_sub_projection_proof_irrelevance.
    + apply IHtrx.
  - apply IHtrx.
Qed.

Section sub_projection_with_no_equivocation_constraints.

Existing Instance  IndEqDec.

Context
  (constraint : composite_label IM -> composite_state IM * option message -> Prop)
  (has_been_sent_capabilities : forall i : index, (has_been_sent_capability (IM i)))
  {index_listing : list index}
  (finite_index : Listing index_listing)
  (Free := free_composite_vlsm IM)
  (Sub_Free := free_composite_vlsm sub_IM)
  (X_has_been_sent_capability : has_been_sent_capability Free := composite_has_been_sent_capability IM (free_constraint IM) finite_index has_been_sent_capabilities)
  (X := composite_vlsm IM constraint)
  (Pre := pre_loaded_with_all_messages_vlsm (free_composite_vlsm IM))
  .

Lemma sub_has_been_sent_capabilities : forall i : sub_index, (has_been_sent_capability (sub_IM i)).
Proof.
  intros [i Hi]. apply has_been_sent_capabilities.
Qed.

Fixpoint select_sub_indices
  (l : list index)
  : list sub_index
  :=
  match l with
  | [] => []
  | h :: t =>
    let t' := select_sub_indices t in
    match decide (sub_index_prop h) with
    | left e => dec_exist _ h e :: t'
    | _ => t'
    end
  end.

Definition sub_index_listing : list sub_index := select_sub_indices index_listing.

Lemma in_select_sub_indices
  (a: index)
  (s: sub_index_prop a)
  (l: list index)
  : In (dec_exist sub_index_prop a s) (select_sub_indices l) <-> In a l.
Proof.
  induction l; [simpl; intuition|].
  simpl.
  destruct (decide (sub_index_prop a0)); [|rewrite IHl].
  - split; intros [Heq | H]; [left |right; apply IHl; assumption| left |right; apply IHl; assumption].
    + apply dec_sig_eq_iff in Heq. assumption.
    + apply dec_sig_eq_iff. assumption.
  - split; [intuition|].
    intros [Heq | H]; [|assumption].
    subst. contradiction.
Qed.

Lemma finite_sub_index : Listing sub_index_listing.
Proof.
  unfold sub_index_listing.
  clear -finite_index.
  destruct finite_index as [Hnodup Hfinite].
  split.
  - clear Hfinite finite_index. induction index_listing; [constructor|].
    inversion Hnodup. subst.
    simpl. spec IHl H2.
    destruct (decide (sub_index_prop a)); [|assumption].
    constructor; [|assumption].
    intro contra. elim H1. apply in_select_sub_indices in contra. assumption.
  - intros subi. unfold sub_index in subi. destruct_dec_sig subi i Hi Heq.
    subst. apply in_select_sub_indices. apply Hfinite.
Qed.

Local Instance Sub_Free_has_been_sent_capability
  : has_been_sent_capability Sub_Free
  :=
  composite_has_been_sent_capability sub_IM (free_constraint sub_IM) finite_sub_index sub_has_been_sent_capabilities.

Lemma finite_trace_sub_projection_empty
  (s : composite_state IM)
  (trx : list (composite_transition_item IM))
  (Htr : finite_protocol_trace_from X s trx)
  (Hempty : finite_trace_sub_projection trx = [])
  (t : (vtransition_item X))
  (Hin : In t trx)
  : forall j, In j sub_index_list -> destination t j = s j.
Proof.
  generalize dependent t.
  induction Htr; simpl; intros t Hin.
  - inversion Hin.
  - destruct l as [i l].
    destruct H as [[[_om Hs'] [[_s Hiom] Hvalid]] Htransition].
    unfold transition in Htransition; simpl in Htransition.
    destruct (vtransition (IM i) l (s' i, iom)) as [si' om'] eqn:Hteq.
    inversion Htransition; subst. clear Htransition.
    match type of Hempty with
      | finite_trace_sub_projection (?i :: _) = _ => remember i as item
    end.
    simpl in Hempty.
    destruct (decide (from_sub_projection item))
    ; [inversion Hempty|].
    specialize (IHHtr Hempty).
    rewrite Heqitem in n.
    unfold from_sub_projection in n.
    simpl in n.
    destruct Hin as [Heq | Hin]; intros j Hj.
    + subst. simpl. apply state_update_neq.
      intro contra. subst. contradiction.
    + assert (Hji : j <> i).
      { intro contra. subst. contradiction. }
      specialize (IHHtr _ Hin j Hj).
      rewrite state_update_neq in IHHtr; assumption.
Qed.

Lemma finite_trace_sub_projection_app
  (tr1 tr2 : list (composite_transition_item IM))
  : finite_trace_sub_projection (tr1 ++ tr2) =
    finite_trace_sub_projection tr1 ++ finite_trace_sub_projection tr2.
Proof.
  induction tr1;[reflexivity|].
  simpl.
  match goal with
  |- context [decide ?d] => destruct (decide d)
  end
  ; [|assumption].
  simpl. rewrite IHtr1. reflexivity.
Qed.

Lemma finite_trace_sub_projection_list_in
  (tr : list (composite_transition_item IM))
  (itemX : composite_transition_item IM)
  (HitemX : In itemX tr)
  (j := projT1 (l itemX))
  (Hj : sub_index_prop j)
  : In (composite_transition_item_sub_projection itemX Hj) (finite_trace_sub_projection tr).
Proof.
  apply in_split in HitemX.
  destruct HitemX as [pre [suf HitemX]].
  subst.
  change (itemX :: suf) with ([itemX] ++ suf).
  rewrite! finite_trace_sub_projection_app.
  apply in_app_iff. right. apply in_app_iff. left.
  simpl. destruct (decide (from_sub_projection itemX)); [|contradiction].
  left. apply composite_transition_item_sub_projection_proof_irrelevance.
Qed.

Lemma finite_trace_sub_projection_list_in_rev
  (tr : list (composite_transition_item IM))
  (j : index)
  (itemj : composite_transition_item sub_IM)
  (Hitemj : In itemj  (finite_trace_sub_projection tr))
  : exists
    (itemX : composite_transition_item IM)
    (HitemX : from_sub_projection itemX),
    In itemX tr /\ composite_transition_item_sub_projection itemX HitemX = itemj.
Proof.
  rewrite <- finite_trace_sub_projection_alt_iff in Hitemj.
  apply in_map_iff in Hitemj.
  destruct Hitemj as [(itemX, HitemX) [Heq Hin]].
  exists itemX, HitemX.
  split; [|assumption].
  apply in_list_annotate_forget in Hin.
  apply filter_In in Hin. apply Hin.
Qed.

Lemma preloaded_finite_trace_sub_projection_last_state
  (start : composite_state IM)
  (transitions : list (composite_transition_item IM))
  (Htr : finite_protocol_trace_from Pre start transitions)
  (lstx := last (List.map destination transitions) start)
  (lstj := last (List.map destination (finite_trace_sub_projection transitions)) (composite_state_sub_projection start))
  : lstj = composite_state_sub_projection lstx.
Proof.
  unfold lstx. unfold lstj. clear lstx. clear lstj.
  induction Htr; [reflexivity|].
  match goal with
  |- context[finite_trace_sub_projection (?i :: _)] => remember i as item
  end.
  rewrite map_cons.
  rewrite unroll_last. simpl.
  destruct (decide (from_sub_projection item)).
  - subst. rewrite map_cons. rewrite unroll_last.
    assumption.
  - destruct H as [[[_om Hs'] [[_s Hiom] Hvalid]] Htransition].
    unfold transition in Htransition; simpl in Htransition.
    unfold vtransition in Htransition. simpl in Htransition.
    destruct l as (i, l).
    destruct (vtransition (IM i) l (s' i, iom)) as [si' om'] eqn:Hteq.
    inversion Htransition; subst. clear Htransition.
    simpl.
    unfold from_sub_projection in n. simpl in n.
    simpl in *.
    rewrite <- IHHtr. f_equal.
    apply functional_extensionality_dep_good.
    intros (j, Hj). unfold composite_state_sub_projection.
    simpl. symmetry. apply (state_update_neq _ s').
    apply bool_decide_eq_true_1 in Hj.
    intro contra. subst. contradiction. 
Qed.

Lemma X_incl_Pre : VLSM_incl X Pre.
Proof.
  apply VLSM_incl_trans with (machine (free_composite_vlsm IM)).
  - apply (constraint_free_incl IM constraint).
  - apply vlsm_incl_pre_loaded_with_all_messages_vlsm.
Qed.

Lemma finite_trace_sub_projection_last_state
  (start : composite_state IM)
  (transitions : list (composite_transition_item IM))
  (Htr : finite_protocol_trace_from X start transitions)
  (lstx := last (List.map destination transitions) start)
  (lstj := last (List.map destination (finite_trace_sub_projection transitions)) (composite_state_sub_projection start))
  : lstj = composite_state_sub_projection lstx.
Proof.
  apply preloaded_finite_trace_sub_projection_last_state.
  apply VLSM_incl_finite_protocol_trace_from with (machine X); [|assumption].
  apply X_incl_Pre.
Qed.

Lemma transition_sub_projection
  l s om s' om'
  (Ht : composite_transition IM l  (s, om) = (s', om'))
  (Hsub : sub_index_prop (projT1 l))
  : composite_transition sub_IM
    (existT (fun n : sub_index => vlabel (sub_IM n))
      (dec_exist _ (projT1 l) Hsub)
      (projT2 l)
    )
    (composite_state_sub_projection s, om)
    = (composite_state_sub_projection s', om').
Proof.
  simpl. simpl in Ht.
  destruct l as (i, li).
  unfold vtransition. simpl.
  unfold composite_state_sub_projection at 1. simpl.
  destruct (vtransition (IM i) li (s i, om)) as (si', omi') eqn:Hti.
  inversion Ht. subst omi' s'. clear Ht.
  match goal with
  |- (let (_, _) := ?t in _) = _ =>
    replace t with (si', om')
  end.
  f_equal.
  apply functional_extensionality_dep.
  intro sub_j. unfold sub_index in sub_j.
  destruct_dec_sig sub_j j Hj Heqj.
  subst sub_j. unfold composite_state_sub_projection at 2.
  destruct (decide (j = i)).
  - subst.
    simpl. rewrite state_update_eq.
    apply sub_IM_state_update_eq.
  - rewrite! state_update_neq; [reflexivity|assumption|].
    intro contra. apply dec_sig_eq_iff in contra. contradiction.
Qed.

Lemma valid_sub_projection
  l s om
  (Hv : composite_valid IM l  (s, om))
  (Hsub : sub_index_prop (projT1 l))
  : composite_valid sub_IM
    (existT (fun n : sub_index => vlabel (sub_IM n))
      (dec_exist _ (projT1 l) Hsub)
      (projT2 l)
    )
    (composite_state_sub_projection s, om).
Proof.
  simpl. simpl in Hv.
  destruct l as (i, li).
  assumption.
Qed.

Definition composite_state_sub_projection_lift
  (ss : composite_state sub_IM)
  (i : index)
  :=
  match (decide (sub_index_prop i)) with
  | left e => ss (dec_exist _ i e)
  | _ => proj1_sig (composite_s0 IM) i
  end. 

Definition sub_constraint
  (l : composite_label sub_IM)
  (som : composite_state sub_IM * option message)
  : Prop
  :=
  let i := proj1_sig (projT1 l) in
  let li := projT2 l in
  let lx : composite_label IM := (existT (fun i : index => vlabel (IM i)) i li) in
  let (ss, om) := som in
  let s := composite_state_sub_projection_lift ss in
  constraint lx (s, om).

Existing Instance X_has_been_sent_capability.

Context
  (seed : message -> Prop)
  (Hno_equiv : constraint_subsumption IM constraint (no_equivocations Free))
  (seeded_constraint : composite_label sub_IM -> composite_state sub_IM * option message -> Prop)
  (Xj := composite_no_equivocation_vlsm_with_pre_loaded sub_IM (free_constraint sub_IM) sub_has_been_sent_capabilities finite_sub_index seed)
  .


Lemma Xj_incl_Pre_Sub_Free
  : VLSM_incl Xj (pre_loaded_with_all_messages_vlsm Sub_Free).
Proof.
  subst Xj.
  unfold composite_no_equivocation_vlsm_with_pre_loaded.
  specialize
    (preloaded_constraint_subsumption_pre_loaded_with_all_messages_incl sub_IM
      (no_equivocations_additional_constraint_with_pre_loaded sub_IM
        (free_constraint sub_IM) sub_has_been_sent_capabilities
        finite_sub_index seed)
      (free_constraint sub_IM)
    ) as Hincl.
  spec Hincl; [intros s Hs l om H; exact I|].
  match goal with
  |- context [pre_loaded_vlsm ?v _] =>
    apply VLSM_incl_trans with (machine (pre_loaded_with_all_messages_vlsm v))
  end
  ; [| apply Hincl].
  clear Hincl.
  match goal with
  |- context [pre_loaded_with_all_messages_vlsm ?v] =>
    apply VLSM_incl_trans with (machine (pre_loaded_vlsm v (fun m => True)))
  end.
  - match goal with
    |- context [pre_loaded_vlsm ?v _] => 
      apply (pre_loaded_vlsm_incl v seed (fun m => True))
    end.
    intuition.
  - match goal with
    |- context [pre_loaded_with_all_messages_vlsm ?v] => 
      specialize (pre_loaded_with_all_messages_vlsm_is_pre_loaded_with_True v) as Hincl
    end.
    apply VLSM_eq_incl_iff in Hincl.
    apply proj2 in Hincl.
    assumption.
Qed.

Definition trace_sub_item_input_is_seeded_or_sub_previously_sent
  (tr : list (composite_transition_item IM))
  : Prop
  :=
  forall pre item suf m,
    tr = pre ++ [item] ++ suf ->
    input item = Some m ->
    from_sub_projection item ->
    seed m \/ exists pre_item, In pre_item pre /\ output pre_item = Some m /\ from_sub_projection pre_item.

Definition state_sub_item_input_is_seeded_or_sub_previously_sent
  (s : composite_state IM)
  : Prop
  := forall is tr,
    finite_protocol_trace Pre is tr ->
    last (map destination tr) is = s ->
    trace_sub_item_input_is_seeded_or_sub_previously_sent tr.

Lemma finite_protocol_trace_sub_projection
  (s : composite_state IM)
  (tr : list (composite_transition_item IM))
  (Hmsg :  trace_sub_item_input_is_seeded_or_sub_previously_sent tr)
  (Htr : finite_protocol_trace X s tr)
  : finite_protocol_trace Xj (composite_state_sub_projection s) (finite_trace_sub_projection tr).
Proof.
  destruct Htr as [Htr His].
  apply (composite_initial_state_sub_projection s) in His.
  split; [|assumption].
  apply (initial_is_protocol Xj) in His as Hisp.
  induction tr using rev_ind; simpl
  ; [constructor; assumption|].
  apply finite_protocol_trace_from_app_iff in Htr.
  destruct Htr as [Htr Hx].
  spec IHtr.
  { intros pre item suf m Heq Hin_m Hitem.
    subst tr.
    specialize (Hmsg pre item (suf ++ [x]) m).
    rewrite! app_assoc in Hmsg.
    specialize (Hmsg eq_refl Hin_m Hitem).
    destruct Hmsg as [Hseed | Hmsg]
    ; [left | right] ; assumption.
  }
  spec IHtr Htr.
  rewrite finite_trace_sub_projection_app.
  apply finite_protocol_trace_from_app_iff.
  split; [assumption|].
  specialize (Hmsg tr x []).
  match goal with 
  |- finite_protocol_trace_from _ ?l _ => remember l as lst
  end.
  assert (Hlst : protocol_state_prop Xj lst).
  { apply finite_ptrace_last_pstate in IHtr. subst. assumption. }
  simpl.
  destruct (decide (from_sub_projection x))
  ;[|constructor; assumption].
  apply (finite_ptrace_singleton Xj).
  inversion Hx. subst x tl. simpl in *.
  destruct H3 as [Hv Ht].
  specialize (transition_sub_projection _ _ _ _ _ Ht f)
    as Htj.
  destruct Hv as [_ [_ [Hv Hc]]].
  specialize (valid_sub_projection _ _ _ Hv f)
    as Hvj.
  rewrite <- H1 in Htj, Hvj.
  assert (Hlst' : composite_state_sub_projection s' = lst).
  { subst lst s'. symmetry.
    apply finite_trace_sub_projection_last_state. assumption.
  }
  rewrite Hlst' in Htj, Hvj.
  repeat split; [assumption | | assumption | | assumption].
  - destruct iom as [m|]; [|apply (option_protocol_message_None Xj)].
    apply (option_protocol_message_Some Xj).
    specialize (Hmsg m eq_refl eq_refl f).
    destruct Hmsg as [Hseed | [item [Hitem [Hout Hsub_item]]]]
    ; [apply (initial_message_is_protocol Xj); right; assumption|].
    specialize (finite_trace_sub_projection_list_in tr item Hitem Hsub_item)
      as Hin_sub.
    apply (protocol_trace_output_is_protocol Xj _ _ IHtr).
    apply Exists_exists. eexists _. split; [apply Hin_sub|].
    assumption.
  - apply Hno_equiv in Hc.
    destruct iom as [m|]; [|exact I].
    simpl in *.
    specialize (Hmsg m eq_refl eq_refl f).
    destruct Hmsg as [Hseed | [item [Hitem [Hout Hsub_item]]]]
    ; [right; right; assumption|].
    left.
    specialize (proper_sent Sub_Free lst) as Hproper.
    assert (Hlstp : protocol_state_prop (pre_loaded_with_all_messages_vlsm Sub_Free) lst).
    { apply VLSM_incl_protocol_state with (MX := machine Xj); [|assumption].
      apply Xj_incl_Pre_Sub_Free.
    }
    spec Hproper Hlstp.
    apply Hproper.
    apply has_been_sent_consistency; [apply Sub_Free_has_been_sent_capability| assumption| ].
    exists (composite_state_sub_projection s), (finite_trace_sub_projection tr).
    split.
    { apply (VLSM_incl_finite_protocol_trace _ _ Xj_incl_Pre_Sub_Free).
      split; assumption.
    }
    symmetry in Heqlst.
    exists Heqlst.
    apply Exists_exists. exists (composite_transition_item_sub_projection item Hsub_item).
    split; [|assumption].
    apply finite_trace_sub_projection_list_in. assumption.
Qed.

Lemma protocol_state_sub_projection
  (s : state)
  (Hs : state_sub_item_input_is_seeded_or_sub_previously_sent s)
  (Hps : protocol_state_prop X s)
  : protocol_state_prop Xj (composite_state_sub_projection s).
Proof.
  apply protocol_state_has_trace in Hps.
  destruct Hps as [is [tr [Htr Hlst]]].
  specialize (finite_trace_sub_projection_last_state _ _ (proj1 Htr)) as Hlst'.
  apply finite_protocol_trace_sub_projection in Htr as Hptr.
  - destruct Hptr as [Hptr _]. apply finite_ptrace_last_pstate in Hptr.
    simpl in *.
    rewrite Hlst' in Hptr.
    subst. assumption.
  - unfold state_sub_item_input_is_seeded_or_sub_previously_sent in Hs.
    apply Hs with is; [|assumption].
    apply VLSM_incl_finite_protocol_trace; [|assumption].
    apply X_incl_Pre.
Qed.

Lemma finite_protocol_trace_from_sub_projection
  (s : composite_state IM)
  (tr : list (composite_transition_item IM))
  (lst := last (map destination tr) s)
  (Hmsg : state_sub_item_input_is_seeded_or_sub_previously_sent lst)
  (Htr : finite_protocol_trace_from X s tr)
  : finite_protocol_trace_from Xj (composite_state_sub_projection s) (finite_trace_sub_projection tr).
Proof.
  apply finite_protocol_trace_from_complete_left in Htr.
  destruct Htr as [is [pre [Htr Hs]]].
  assert (Hpre := proj1 Htr).
  apply finite_protocol_trace_from_app_iff in Hpre.
  destruct Hpre as [Hpre _].
  specialize (finite_trace_sub_projection_last_state _ _ Hpre) as Hpre_lst.
  apply finite_protocol_trace_sub_projection in Htr.
  - destruct Htr as [Htr His].
    rewrite finite_trace_sub_projection_app in Htr.
    apply finite_protocol_trace_from_app_iff in Htr.
    destruct Htr as [_ Htr].
    subst s. simpl in *.
    rewrite Hpre_lst in Htr. assumption.
  - specialize (Hmsg is (pre ++ tr)).
    apply Hmsg.
    + apply VLSM_incl_finite_protocol_trace; [|assumption].
      apply X_incl_Pre.
    + rewrite map_app, last_app. subst lst s. reflexivity.
Qed.

Lemma in_futures_sub_projection
  (s1 s2 : state)
  (Hs2 : state_sub_item_input_is_seeded_or_sub_previously_sent s2)
  (Hfutures : in_futures X s1 s2)
  : in_futures Xj (composite_state_sub_projection s1) (composite_state_sub_projection s2).
Proof.
  destruct Hfutures as [tr [Htr Heq_s2]]. subst s2.
  specialize (finite_protocol_trace_from_sub_projection s1 tr Hs2 Htr); intros Htrj.
  exists (finite_trace_sub_projection tr).
  split; [assumption|].
  apply finite_trace_sub_projection_last_state.
  assumption.
Qed.

End sub_projection_with_no_equivocation_constraints.
End sub_composition.