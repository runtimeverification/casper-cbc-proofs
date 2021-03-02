Require Import List Streams Nat Bool.
Import ListNotations.
Require Import Lia.
Require Import Logic.FunctionalExtensionality.

Require Import Coq.Logic.FinFun Coq.Logic.Eqdep.

From CasperCBC
Require Import Lib.StreamExtras Lib.ListExtras Lib.Preamble VLSM.Common VLSM.Composition.

Section ProjectionTraces.

Context
  {message : Type}
  {index : Type}
  {IndEqDec : EqDecision index}
  (IM : index -> VLSM message)
  {i0 : Inhabited index}
  (constraint : composite_label IM -> composite_state IM * option message -> Prop)
  (X := composite_vlsm IM constraint)
  (j : index)
  (Xj := composite_vlsm_constrained_projection IM constraint j)
  .

(** Extracted common functionality for both [finite_trace_projection_list]
    and [finite_trace_projection_list_alt]. *)
Definition composite_transition_item_projection_from_eq
  (item : composite_transition_item IM)
  (i := projT1 (l item))
  j
  (e : j = i)
  : vtransition_item (IM j)
  :=
  let lj := eq_rect_r _ (projT2 (l item)) e in
  @Build_transition_item _ (type (IM j)) lj (input item) (destination item j) (output item).

Definition composite_transition_item_projection
  (item : composite_transition_item IM)
  (i := projT1 (l item))
  : vtransition_item (IM i)
  :=
  composite_transition_item_projection_from_eq item i eq_refl.

Fixpoint finite_trace_projection_list
  (trx : list (composite_transition_item IM))
  : list (vtransition_item (IM j))
  :=
  match trx with
  | [] => []
  | item :: trx =>
    let tail := finite_trace_projection_list trx in
    match decide (j = (projT1 (l item))) with
    | left e => composite_transition_item_projection_from_eq item j e :: tail
    | _ => tail
    end
  end.

Definition from_projection
  (a : composite_transition_item IM)
  : Prop
  := j = projT1 (l a).

Instance dec_from_projection (a : transition_item) : Decision (from_projection a) :=
  decide (from_projection a).

Definition finite_trace_projection_list_alt
  (trx : list (composite_transition_item IM))
  (ftrx := (filter (fun a => bool_decide (from_projection a)) trx))
  (Hall: Forall from_projection ftrx)
  :=
  List.map
    (fun item : {a : composite_transition_item IM | from_projection a} =>
      let (item, e) := item in
      let lj := eq_rect_r _ (projT2 (l item)) e in
      @Build_transition_item _ (type (IM j))
        lj
        (input item)
        (destination item j)
        (output item)
    )
  (list_annotate from_projection ftrx Hall).

Lemma finite_trace_projection_list_alt_iff
  (trx : list (composite_transition_item IM))
  (ftrx := (filter (fun a => bool_decide (from_projection a)) trx))
  (Hall: Forall from_projection ftrx)
  : finite_trace_projection_list_alt trx Hall = finite_trace_projection_list trx.
Proof.
  unfold ftrx in *. clear ftrx.
  generalize dependent Hall.
  induction trx; intros; try reflexivity.
  simpl.
  destruct
    (decide (j =
    (@projT1 index (fun n : index => @vlabel message (IM n))
       (@l message (@composite_type message index IM) a))))
    eqn:Heq.
  - assert
    (Hunroll :
      filter (fun a => bool_decide (from_projection a)) (a :: trx)
      = a :: filter (fun a => bool_decide (from_projection a)) trx
    ).
    { simpl.
      unfold bool_decide, dec_from_projection, from_projection.
      replace
        (decide (j =
        (@projT1 index (fun n : index => @vlabel message (IM n))
           (@l message (@type message X) a))))
      with
        (@left
           (@eq index j
              (@projT1 index (fun n : index => @vlabel message (IM n))
                 (@l message (@composite_type message index IM) a)))
           (not
              (@eq index j
                 (@projT1 index (fun n : index => @vlabel message (IM n))
                    (@l message (@composite_type message index IM) a)))) e)
      .
      reflexivity.
    }
    unfold finite_trace_projection_list_alt.
    generalize dependent Hall.
    rewrite Hunroll.
    intro Hall.
    rewrite list_annotate_unroll.
    specialize (IHtrx (Forall_tl Hall)).
    rewrite <- IHtrx.
    simpl.
    f_equal.
    f_equal; try reflexivity.
    replace (Forall_hd Hall) with e; try reflexivity.
    apply UIP.
  - assert
    (Hunroll :
      filter (fun a => bool_decide (from_projection a)) (a :: trx)
      = filter (fun a => bool_decide (from_projection a)) trx
    ).
    { simpl.
      unfold bool_decide, dec_from_projection, from_projection.
      replace
        (decide (j =
        (@projT1 index (fun n0 : index => @vlabel message (IM n0))
           (@l message (@type message X) a))))
      with
        (@right
          (@eq index j
             (@projT1 index (fun n : index => @vlabel message (IM n))
                (@l message (@composite_type message index IM) a)))
          (not
             (@eq index j
                (@projT1 index (fun n : index => @vlabel message (IM n))
                   (@l message (@composite_type message index IM) a)))) n)
        .
      reflexivity.
    }
    unfold finite_trace_projection_list_alt.
    generalize dependent Hall.
    rewrite Hunroll.
    intro Hall.
    specialize (IHtrx Hall).
    rewrite <- IHtrx.
    reflexivity.
Qed.

Lemma finite_trace_projection_empty
  (s : vstate X)
  (trx : list (vtransition_item X))
  (Htr : finite_protocol_trace_from X s trx)
  (Hempty : finite_trace_projection_list trx = [])
  (t : (vtransition_item X))
  (Hin : In t trx)
  : destination t j = s j.
Proof.
  generalize dependent t.
  induction Htr; simpl; intros t Hin.
  - inversion Hin.
  - destruct l as [i l].
    destruct H as [[[_om Hs'] [[_s Hiom] Hvalid]] Htransition].
    unfold transition in Htransition; simpl in Htransition.
    destruct (vtransition (IM i) l (s' i, iom)) as [si' om'] eqn:Hteq.
    inversion Htransition; subst. clear Htransition.
    destruct Hin as [Heq | Hin]; subst; simpl in *; destruct (decide (j = i)).
    + inversion Hempty.
    + apply state_update_neq. assumption.
    + inversion Hempty.
    + specialize (IHHtr Hempty t Hin). rewrite IHHtr.
      apply state_update_neq. assumption.
Qed.

Lemma finite_trace_projection_list_app
  (tr1 tr2 : list (composite_transition_item IM))
  : finite_trace_projection_list (tr1 ++ tr2) =
    finite_trace_projection_list tr1 ++ finite_trace_projection_list tr2.
Proof.
  induction tr1;[reflexivity|].
  simpl.
  match goal with
  |- context [decide ?d] => destruct (decide d)
  end
  ; [|assumption].
  simpl. rewrite IHtr1. reflexivity.
Qed.

Lemma preloaded_finite_trace_projection_last_state
  (start : vstate X)
  (transitions : list (vtransition_item X))
  (Htr : finite_protocol_trace_from (pre_loaded_with_all_messages_vlsm X) start transitions)
  (lstx := last (List.map destination transitions) start)
  (lstj := last (List.map destination (finite_trace_projection_list transitions)) (start j))
  : lstj = lstx j.
Proof.
  unfold lstx. unfold lstj. clear lstx. clear lstj.
  induction Htr; try reflexivity.
  destruct l as [i l].
  rewrite map_cons.
  rewrite unroll_last. simpl.
  destruct (decide (j = i)).
  - rewrite map_cons. rewrite unroll_last.
    assumption.
  - destruct H as [[[_om Hs'] [[_s Hiom] Hvalid]] Htransition].
    unfold transition in Htransition; simpl in Htransition.
    unfold vtransition in Htransition. simpl in Htransition.
    destruct (vtransition (IM i) l (s' i, iom)) as [si' om'] eqn:Hteq.
    inversion Htransition; subst. clear Htransition.
    specialize (state_update_neq _ s' i si' j n); intro Hupd.
    rewrite Hupd in *.
    assumption.
Qed.

Lemma finite_trace_projection_last_state
  (start : vstate X)
  (transitions : list (vtransition_item X))
  (Htr : finite_protocol_trace_from X start transitions)
  (lstx := last (List.map destination transitions) start)
  (lstj := last (List.map destination (finite_trace_projection_list transitions)) (start j))
  : lstj = lstx j.
Proof.
  apply preloaded_finite_trace_projection_last_state.
  apply VLSM_incl_finite_protocol_trace_from; [|assumption].
  apply vlsm_incl_pre_loaded_with_all_messages_vlsm.
Qed.

Local Lemma _finite_ptrace_projection
  (s : vstate X)
  (Psj : protocol_state_prop Xj (s j))
  (trx : list (vtransition_item X))
  (Htr : finite_protocol_trace_from X s trx)
   : finite_protocol_trace_from Xj (s j) (finite_trace_projection_list trx).
Proof.
  induction Htr.
  - constructor. assumption.
  - destruct l as [x lx]; simpl.
    destruct H as [[Ps' [Piom [Hv Hc]]] Ht].
    assert (Hpp : protocol_prop X (s, oom)).
    { rewrite <- Ht. destruct Ps' as [_om Ps']. destruct Piom as [_s Piom].
      apply protocol_generated with _om _s; try assumption. split; assumption.
    }
    assert (Hps : protocol_state_prop X s) by (exists oom; assumption).
    destruct (decide (j = x)).
    + subst x.
      simpl in Ht.
      destruct (vtransition (IM j) lx (s' j, iom)) as [si' om'] eqn:Hteq.
      inversion Ht; subst. unfold composite_transition_item_projection_from_eq.
      simpl.
      rewrite state_update_eq in *.
      simpl in Hv.
      apply (finite_ptrace_extend Xj).
      * apply IHHtr.
        exists oom.
        replace (@pair (@state message (@type message Xj)) (option message) si' oom)
          with (vtransition (IM j) lx (s' j, iom)).
        destruct Psj as [os'j Psj].
        specialize (protocol_message_projection IM constraint j _ Piom); intros [sj HPjiom].
        apply (protocol_generated Xj lx (s' j) os'j Psj sj iom HPjiom).
        unfold valid; simpl.
        exists s'.
        split; try reflexivity.
        split; try assumption.
        split; try assumption.
        destruct iom as [im|]
        ; repeat split; assumption.
      * assert
          (Heqlx :
            (@eq_rect_r index j (fun n : index => vlabel (IM n)) lx j (@eq_refl index j))
            = lx
          ) by reflexivity.
        rewrite Heqlx.
        specialize (protocol_message_projection IM constraint j _ Piom); intros HPjiom.
        repeat split; try assumption.
        exists s'.
        repeat split; assumption.
    + simpl in Ht. destruct (vtransition (IM x) lx (s' x, iom)) eqn:Hteq.
      inversion Ht; subst.
      rewrite state_update_neq in IHHtr; try assumption.
      apply IHHtr.
      assumption.
Qed.

Lemma protocol_state_projection
  (s : state)
  (Hps : protocol_state_prop X s)
  : protocol_state_prop Xj (s j).
Proof.
  apply protocol_state_has_trace in Hps.
  destruct Hps as [is [tr [[Htr His] Hs]]].
  specialize (finite_trace_projection_last_state _ _ Htr) as Hlst.
  apply _finite_ptrace_projection in Htr as Hptr.
  - apply finite_ptrace_last_pstate in Hptr.
    simpl in *.
    rewrite Hlst in Hptr.
    subst. assumption.
  - apply initial_is_protocol. specialize (His j). assumption.
Qed.

(* The projection of a finite protocol trace remains a protocol trace *)

Lemma finite_ptrace_projection
  (s : vstate X)
  (trx : list (vtransition_item X))
  (Htr : finite_protocol_trace_from X s trx)
   : finite_protocol_trace_from Xj (s j) (finite_trace_projection_list trx).
Proof.
  apply _finite_ptrace_projection; [|assumption].
  apply protocol_state_projection.
  apply finite_ptrace_first_pstate in Htr.
  assumption.
Qed.

(* The projection of a preloaded finite protocol trace remains a preloaded protocol trace *)

Lemma _preloaded_finite_ptrace_projection
  (s : vstate X)
  (Psj : protocol_state_prop (pre_loaded_with_all_messages_vlsm (IM j)) (s j))
  (trx : list (vtransition_item X))
  (Htr : finite_protocol_trace_from (pre_loaded_with_all_messages_vlsm X) s trx)
   : finite_protocol_trace_from (pre_loaded_with_all_messages_vlsm (IM j)) (s j) (finite_trace_projection_list trx).
Proof.
  induction Htr.
  - constructor. assumption.
  - destruct l as [x lx]; simpl.
    destruct H as [[Ps' [Piom [Hv Hc]]] Ht].
    assert (Hpp : protocol_prop (pre_loaded_with_all_messages_vlsm X) (s, oom)).
    { rewrite <- Ht. destruct Ps' as [_om Ps']. destruct Piom as [_s Piom].
      apply protocol_generated with _om _s; try assumption. split; assumption.
    }
    assert (Hps : protocol_state_prop (pre_loaded_with_all_messages_vlsm X) s) by (exists oom; assumption).
    destruct (decide (j = x)).
    + subst x.
      unfold vtransition in Ht. simpl in Ht.
      unfold vtransition in Ht. simpl in Ht.
      destruct (vtransition (IM j) lx (s' j, iom)) as [si' om'] eqn:Hteq.
      inversion Ht; subst.
      unfold composite_transition_item_projection_from_eq. simpl.
      rewrite state_update_eq in *.
      simpl in Hv.
      apply (finite_ptrace_extend (pre_loaded_with_all_messages_vlsm (IM j))).
      * apply IHHtr.
        exists oom.

        replace
          (@pair
            (@state message
              (@type message (@pre_loaded_with_all_messages_vlsm message (IM j))))
            (option message)
            si' oom)
          with (vtransition (IM j) lx (s' j, iom)).
        destruct Psj as [os'j Psj].
        specialize (protocol_generated (pre_loaded_with_all_messages_vlsm (IM j)) lx (s' j) os'j Psj)
          as Hgen.
        specialize (Hgen (proj1_sig (vs0 (IM j))) iom).
        spec Hgen; [apply (pre_loaded_with_all_messages_message_protocol_prop (IM j))|].
        spec Hgen; [| apply Hgen].
        assumption.
      * assert
          (Heqlx :
            (@eq_rect_r index j (fun n : index => vlabel (IM n)) lx j (@eq_refl index j))
            = lx
          ) by reflexivity.
        rewrite Heqlx.
        split; [|assumption].
        split; [assumption|].
        split; [|assumption].
        exists (proj1_sig (vs0 (IM j))).
        apply (pre_loaded_with_all_messages_message_protocol_prop (IM j)).
    + simpl in Ht. unfold vtransition in Ht.
      simpl in Ht.
      destruct (vtransition (IM x) lx (s' x, iom)) eqn:Hteq.
      inversion Ht; subst.
      rewrite state_update_neq in IHHtr by assumption.
      apply IHHtr.
      assumption.
Qed.

Lemma preloaded_protocol_state_projection
  (s : state)
  (Hps : protocol_state_prop (pre_loaded_with_all_messages_vlsm X) s)
  : protocol_state_prop (pre_loaded_with_all_messages_vlsm (IM j)) (s j).
Proof.
  apply protocol_state_has_trace in Hps.
  destruct Hps as [is [tr [[Htr His] Hs]]].
  specialize (preloaded_finite_trace_projection_last_state _ _ Htr) as Hlst.
  apply _preloaded_finite_ptrace_projection in Htr as Hptr.
  - apply finite_ptrace_last_pstate in Hptr.
    simpl in *.
    rewrite Hlst in Hptr.
    subst. assumption.
  - apply initial_is_protocol. specialize (His j). assumption.
Qed.

Lemma preloaded_finite_ptrace_projection
  (s : vstate X)
  (trx : list (vtransition_item X))
  (Htr : finite_protocol_trace_from (pre_loaded_with_all_messages_vlsm X) s trx)
   : finite_protocol_trace_from (pre_loaded_with_all_messages_vlsm (IM j)) (s j) (finite_trace_projection_list trx).
Proof.
  apply _preloaded_finite_ptrace_projection; [|assumption].
  apply preloaded_protocol_state_projection.
  apply finite_ptrace_first_pstate in Htr.
  assumption.
Qed.

Lemma in_futures_projection
  (s1 s2 : state)
  (Hfutures : in_futures X s1 s2)
  : in_futures Xj (s1 j) (s2 j).
Proof.
  destruct Hfutures as [tr [Htr Hs2]].
  specialize (finite_ptrace_projection s1 tr Htr); intros Htrj.
  exists (finite_trace_projection_list tr).
  split; [assumption|].
  subst s2.
  apply finite_trace_projection_last_state.
  assumption.
Qed.

Definition in_projection
   (tr : Stream (composite_transition_item IM))
   (n : nat)
   := from_projection (Str_nth n tr).

Definition in_projection_dec
  := forall (tr : Stream (composite_transition_item IM)),
       bounding (in_projection tr)
       + { ss : monotone_nat_stream
         | filtering_subsequence from_projection tr ss
         }.

Definition infinite_trace_projection_stream
  (ss: Stream (composite_transition_item IM))
  (ks: monotone_nat_stream)
  (Hfilter: filtering_subsequence from_projection ss ks)
  : Stream (vtransition_item (IM j))
  :=
  let subs := stream_subsequence ss ks in
  let HForAll := stream_filter_Forall from_projection ss ks Hfilter in
  let subsP := stream_annotate from_projection subs HForAll in
  Streams.map
    (fun item : {a : vtransition_item X | from_projection a} =>
      let (item, e) := item in
      let lj := eq_rect_r _ (projT2 (l item)) e in
      @Build_transition_item _ (type Xj) lj (input item) (destination item j) (output item)
    )
    subsP.

Lemma finite_trace_projection_stream
  (ss: Stream (composite_transition_item IM))
  (ks: monotone_nat_stream)
  (Hfilter: filtering_subsequence from_projection ss ks)
  (n : nat)
  (kn := Str_nth n (proj1_sig ks))
  (ss_to_kn := stream_prefix ss (succ kn))
  (sproj := infinite_trace_projection_stream ss ks Hfilter)
  : stream_prefix sproj (succ n) = finite_trace_projection_list ss_to_kn.
Proof.
  unfold sproj. unfold infinite_trace_projection_stream.
  rewrite <- stream_prefix_map.
  specialize
    (stream_prefix_annotate
      from_projection
      (stream_subsequence ss ks)
      (stream_filter_Forall from_projection ss ks Hfilter)
      (succ n)
    ); intros [Hall Heq].
  clear -Heq.
  match goal with
  |- List.map _ ?s = _ => replace s with
      (list_annotate from_projection (stream_prefix (stream_subsequence ss ks) (succ n)) Hall)
  end.
  specialize
    (stream_filter_prefix
       ss
       ks
       Hfilter
       n
    ); intros Hsfilter.
  remember stream_prefix as sp.
  simpl in Hsfilter. subst.
  unfold succ in *.
  generalize dependent Hall.
  rewrite Hsfilter.
  intros.
  unfold ss_to_kn. unfold kn.
  apply finite_trace_projection_list_alt_iff.
Qed.

Definition trace_projection
  (Hproj_dec : in_projection_dec)
  (tr : vTrace X)
  : vTrace (IM j).
Proof.
  destruct tr as [s ls | s ss].
  - exact (Finite (s j) (finite_trace_projection_list ls)).
  - specialize (Hproj_dec ss).
    destruct Hproj_dec as [[n1 _] | [ks Hfilter]].
    + exact (Finite (s j) (finite_trace_projection_list (stream_prefix ss n1))).
    + exact (Infinite (s j) (infinite_trace_projection_stream ss ks Hfilter)).
Defined.

Lemma trace_projection_initial_state
  (Hproj_dec : in_projection_dec)
  (tr : vTrace X)
  : trace_first (trace_projection Hproj_dec tr)
  = trace_first tr j.
Proof.
  destruct tr; try reflexivity.
  simpl.
  destruct (Hproj_dec s0).
  - destruct b; reflexivity.
  - destruct s1; reflexivity.
Qed.

Lemma infinite_ptrace_projection
  (s: vstate X)
  (ss: Stream transition_item)
  (Psj: protocol_state_prop Xj (s j))
  (Htr: infinite_protocol_trace_from X s ss)
  (fs : monotone_nat_stream)
  (Hfs: filtering_subsequence from_projection ss fs)
  : infinite_protocol_trace_from Xj (s j) (infinite_trace_projection_stream ss fs Hfs).
Proof.
  apply infinite_protocol_trace_from_prefix_rev.
  specialize (infinite_protocol_trace_from_prefix X s ss Htr); intro Hftr.
  intros [| n].
  - constructor. assumption.
  - rewrite finite_trace_projection_stream.
    apply finite_ptrace_projection; try assumption.
    apply Hftr.
Qed.

(* The projection of an protocol trace remains a protocol trace *)

Lemma ptrace_from_projection
  (Hproj_dec : in_projection_dec)
  (tr : vTrace X)
  (Psj : protocol_state_prop Xj (trace_first tr j))
  (Htr : ptrace_from_prop X tr)
   : ptrace_from_prop Xj (trace_projection Hproj_dec tr).
Proof.
  destruct tr as [s ls | s ss].
  - apply finite_ptrace_projection; assumption.
  - simpl. destruct (Hproj_dec ss) as [[n _]|Hinf].
    + apply finite_ptrace_projection; try assumption.
      apply infinite_protocol_trace_from_prefix. assumption.
    + destruct Hinf as [ks HFilter].
      apply infinite_ptrace_projection; assumption.
Qed.

Lemma protocol_trace_projection
  (Hproj_dec : in_projection_dec)
  (tr : vTrace X)
  (Htr : protocol_trace_prop X tr)
  : protocol_trace_prop Xj (trace_projection Hproj_dec tr).
Proof.
  assert (Hfrom := protocol_trace_from X tr Htr).
  assert (Hinit := protocol_trace_initial X tr Htr).
  apply protocol_trace_from_iff.
  split.
  - apply ptrace_from_projection; try assumption.
    apply protocol_state_prop_iff.
    left.
    apply (initial_state_projection IM constraint j) in Hinit.
    exists (exist _ _ Hinit).
    reflexivity.
  - rewrite trace_projection_initial_state.
    apply initial_state_projection.
    assumption.
Qed.

(* We axiomatize projection friendliness as the converse of protocol_trace_projection *)
Definition finite_projection_friendly
  := forall
    (sj : vstate (IM j))
    (trj : list (vtransition_item (IM j)))
    (Htrj : finite_protocol_trace Xj sj trj),
    exists (sx : vstate X) (trx : list (vtransition_item X)),
      finite_protocol_trace X sx trx
      /\ sx j = sj
      /\ finite_trace_projection_list trx = trj.

Definition projection_friendly
  (Hproj_dec : in_projection_dec)
  := forall
  (trj : vTrace (IM j))
  (Htrj : protocol_trace_prop Xj trj),
  exists (tr : vTrace X),
    protocol_trace_prop X tr
    /\ trace_projection Hproj_dec tr = trj.

Lemma projection_friendly_finite
  (Hproj_dec : in_projection_dec)
  (Hfr : projection_friendly Hproj_dec)
  : finite_projection_friendly.
Proof.
  unfold finite_projection_friendly;  intros.
  specialize (Hfr (Finite sj trj) Htrj).
  destruct Hfr as [[s tr| s tr] [Htr Heq]].
  + exists s. exists tr.
    split; try assumption.
    unfold trace_projection in Heq.
    inversion Heq.
    split; reflexivity.
  + unfold trace_projection in Heq.
    destruct (Hproj_dec tr) as [[n1 _] | (ks, Hfilter)]; inversion Heq.
    subst; clear Heq.
    exists s. exists (stream_prefix tr n1).
    destruct Htr as [Htr Hinit].
    repeat split; try reflexivity; try assumption.
    apply infinite_protocol_trace_from_prefix.
    assumption.
Qed.

Lemma projection_friendly_in_futures'
  (sx: state)
  (trx: list transition_item)
  (Htrx: finite_protocol_trace X sx trx)
  (sj: state)
  (Hsx: sx j = sj)
  (Hall: Forall from_projection
         (filter (fun a => bool_decide (from_projection a)) trx))
  (s1 s2: state)
  (n1 n2: nat)
  (Hle: n1 <= n2)
  (Hs1: nth_error
        (sj
         :: List.map destination (finite_trace_projection_list_alt trx Hall))
        n1 = Some s1)
  (Hs2: nth_error
        (sj
         :: List.map destination (finite_trace_projection_list_alt trx Hall))
        n2 = Some s2)
  : exists sX1 sX2 : vstate X, sX1 j = s1 /\ sX2 j = s2 /\ in_futures X sX1 sX2.
Proof.
    assert
      (HsX1 :
        exists (nX1 nX2 : nat) (sX1 sX2 : vstate X),
          nX1 <= nX2 /\ sX1 j = s1 /\ sX2 j = s2
          /\ nth_error (sx :: List.map destination trx) nX1 = Some sX1
          /\ nth_error (sx :: List.map destination trx) nX2 = Some sX2
      ).
    {
      destruct n1; destruct n2.
      - exists 0; exists 0; exists sx; exists sx
        ; inversion Hs1; inversion Hs2; subst; repeat split; assumption.
      - exists 0; inversion Hs1; clear Hs1; subst.
        simpl in Hs2.
        rewrite nth_error_map in Hs2.
        unfold finite_trace_projection_list_alt in Hs2.
        rewrite nth_error_map in Hs2.
        specialize
          (nth_error_list_annotate
            from_projection
            (filter (fun a => bool_decide (from_projection a)) trx)
            Hall
            n2
          ); intros [oitem [Hoa Hnth]].
        match type of Hs2 with
        | option_map _ (option_map _ ?n) = _ => replace n with oitem in Hs2
        end.
        clear Hoa.
        destruct oitem as [[item Hitem]|]; try inversion Hs2; subst; clear Hs2.
        simpl in Hnth.
        symmetry in Hnth.
        apply nth_error_filter in Hnth.
        destruct Hnth as [nX2 [Hindex Hnth]].
        exists (S nX2).
        exists sx.
        exists (destination item).
        repeat split.
        + lia.
        + simpl. rewrite nth_error_map.
          replace
            (@nth_error (@transition_item message (@composite_type message index IM)) trx nX2)
            with (Some item).
          reflexivity.
      - inversion Hle.
      - simpl in Hs1. simpl in Hs2.
        rewrite nth_error_map in Hs1.
        rewrite nth_error_map in Hs2.
        unfold finite_trace_projection_list_alt in Hs1.
        unfold finite_trace_projection_list_alt in Hs2.
        rewrite nth_error_map in Hs1.
        rewrite nth_error_map in Hs2.
        specialize
          (nth_error_list_annotate
            from_projection
            (filter (fun a => bool_decide (from_projection a)) trx)
            Hall
            n2
          ); intros [oitem2 [Hoa2 Hn2th]].
        specialize
          (nth_error_list_annotate
            from_projection
            (filter (fun a => bool_decide (from_projection a)) trx)
            Hall
            n1
          ); intros [oitem1 [Hoa1 Hn1th]].
        match type of Hs2 with
        | option_map _ (option_map _ ?n) = _ => replace n with oitem2 in Hs2
        end.
        match type of Hs1 with
        | option_map _ (option_map _ ?n) = _ => replace n with oitem1 in Hs1
        end.
        clear Hoa1.
        destruct oitem2 as [[item2 Hitem2]|]; try inversion Hs2; subst; clear Hs2.
        destruct oitem1 as [[item1 Hitem1]|]; try inversion Hs1; subst; clear Hs1.
        simpl in Hn1th.
        simpl in Hn2th.
        symmetry in Hn1th.
        symmetry in Hn2th.
        apply nth_error_filter in Hn1th.
        apply nth_error_filter in Hn2th.
        destruct Hn2th as [nX2 [Hindex2 Hn2th]].
        destruct Hn1th as [nX1 [Hindex1 Hn1th]].
        exists (S nX1).
        exists (S nX2).
        exists (destination item1).
        exists (destination item2).
        repeat split; try assumption.
        + assert (Hle' : n1 <= n2) by lia.
          specialize (nth_error_filter_index_le _ _ _ _ Hle' _ _ Hindex1 Hindex2).
          intro; lia.
        + simpl. rewrite nth_error_map.
          replace (@nth_error (@transition_item message (@composite_type message index IM)) trx nX1)
            with (Some item1).
          reflexivity.
        + simpl. rewrite nth_error_map.
          replace (@nth_error (@transition_item message (@composite_type message index IM)) trx nX2)
            with (Some item2).
          reflexivity.
    }
    destruct HsX1 as [nX1 [nX2 [sX1 [sX2 [HleX [Hps1 [Hps2 [HsX1 HsX2]]]]]]]].
    exists sX1. exists sX2. repeat split; try assumption.
    specialize (in_futures_witness_reverse X sX1 sX2 (exist (protocol_trace_prop X) (Finite sx trx) Htrx) nX1 nX2 HleX HsX1 HsX2).
    intros; assumption.
Qed.

Lemma projection_friendly_in_futures
  (Hfr : finite_projection_friendly)
  (s1 s2 : vstate (IM j))
  (Hfuture : in_futures Xj s1 s2)
  : exists (sX1 sX2 : vstate X),
    sX1 j = s1 /\ sX2 j = s2 /\ in_futures X sX1 sX2.
Proof.
  specialize (in_futures_witness Xj s1 s2 Hfuture)
  ; intros [trj [n1 [n2 [Hle [Hs1 Hs2]]]]].
  clear Hfuture.
  destruct trj as [trj Htrj].
  specialize (trace_prefix_fn_protocol Xj trj Htrj n2); intros Hpref.
  remember (trace_prefix_fn Xj trj n2) as trj2.
  destruct trj2 as [sj' lj' | sj' lj']; destruct trj as [sj lj | sj lj]
  ; inversion Heqtrj2
  ; subst sj' lj'.
  - specialize (Hfr sj (list_prefix lj n2) Hpref).
    destruct Hfr as [sx [trx [Htrx [Hsx Hproj]]]].
    assert (Hall : Forall from_projection
              (filter (fun a => bool_decide (from_projection a)) trx))
      by apply filter_Forall.
    specialize (finite_trace_projection_list_alt_iff trx Hall); intro Heq.
    rewrite <- Heq in Hproj.
    simpl in Hs1.
    simpl in Hs2.
    assert
      (Hs1' :
        nth_error (sj :: List.map destination lj) n1 =
        nth_error (sj :: List.map destination (list_prefix lj n2)) n1
      ).
    { destruct n1; try reflexivity. simpl.
      rewrite list_prefix_map.
      symmetry. apply list_prefix_nth. assumption.
    }
    assert
      (Hs2' :
        nth_error (sj :: List.map destination lj) n2 =
        nth_error (sj :: List.map destination (list_prefix lj n2)) n2
      ).
    { destruct n2; try reflexivity. simpl.
      rewrite list_prefix_map.
      symmetry. apply list_prefix_nth. constructor.
    }
    apply projection_friendly_in_futures' with sx trx sj Hall n1 n2; try assumption
    ; rewrite Hproj.
    + rewrite <- Hs1. symmetry. assumption.
    + rewrite <- Hs2. symmetry. assumption.
  - specialize (Hfr sj (stream_prefix lj n2) Hpref).
    destruct Hfr as [sx [trx [Htrx [Hsx Hproj]]]].
    assert (Hall : Forall from_projection
              (filter (fun a => bool_decide (from_projection a)) trx))
      by apply filter_Forall.
    specialize (finite_trace_projection_list_alt_iff trx Hall); intro Heq.
    rewrite <- Heq in Hproj.
    simpl in Hs1.
    simpl in Hs2.
    assert
      (Hs1' :
        Some (Str_nth n1 (Cons sj (map destination lj))) =
        nth_error (sj :: List.map destination (stream_prefix lj n2)) n1
      ).
    { destruct n1; try reflexivity. simpl.
      rewrite stream_prefix_map.
      rewrite stream_prefix_nth; try assumption.
      reflexivity.
    }
    assert
      (Hs2' :
      Some (Str_nth n2 (Cons sj (map destination lj))) =
        nth_error (sj :: List.map destination (stream_prefix lj n2)) n2
      ).
    { destruct n2; try reflexivity.
      rewrite stream_prefix_map.
      remember (S n2) as sn2. rewrite Heqsn2 at 3.
      simpl.
      rewrite stream_prefix_nth; subst; constructor.
    }
    apply projection_friendly_in_futures' with sx trx sj Hall n1 n2; try assumption
    ; rewrite Hproj; rewrite <- Hs1 || rewrite <- Hs2; symmetry; assumption.
Qed.

End ProjectionTraces.

Section ProjectionTraces_membership.

Context
  {message : Type}
  {index : Type}
  {IndEqDec : EqDecision index}
  (IM : index -> VLSM message)
  {i0 : Inhabited index}
  (constraint : composite_label IM -> composite_state IM * option message -> Prop)
  (X := composite_vlsm IM constraint)
  .

Lemma finite_trace_projection_list_in
  (tr : list (vtransition_item X))
  (itemX : vtransition_item X)
  (HitemX : In itemX tr)
  (j := projT1 (l itemX))
  : In (@Build_transition_item _ (type (IM j)) (projT2 (l itemX)) (input itemX) (destination itemX j) (output itemX)) (finite_trace_projection_list IM j tr).
Proof.
  induction tr; [inversion HitemX|].
  destruct HitemX as [HitemX | HitemX].
  - simpl. subst a. unfold j in *. clear j.
    match goal with
    |- context [decide ?eq] => destruct (decide eq)
    end
    ; [| elim n; reflexivity].
    left.
    f_equal.
    replace e with (@eq_refl index (projT1 (l itemX))) by apply UIP.
    reflexivity.
  - spec IHtr HitemX.
    simpl.
    match goal with
    |- context [decide ?eq] => destruct (decide eq)
    end
    ;[|assumption].
    right. assumption.
Qed.

Lemma finite_trace_projection_list_in_rev
  (tr : list (composite_transition_item IM))
  (j : index)
  (itemj : vtransition_item (IM j))
  (Hitemj : In itemj  (finite_trace_projection_list IM j tr))
  : exists
    (itemX : composite_transition_item IM)
    (Houtput : output itemX = output itemj)
    (Hinput : input itemX = input itemj)
    (Hl1 : j = projT1 (l itemX))
    (Hl2 : eq_rect_r _ (projT2 (l itemX)) Hl1 = l itemj)
    (Hdestination : destination itemX j = destination itemj),
    In itemX tr.
Proof.
  induction tr; [contradict Hitemj|].
  simpl in Hitemj.
  match type of Hitemj with
  | context [decide ?eq] => destruct (decide eq)
  end.
  - destruct Hitemj as [Hitemj | Hitemj].
    + subst itemj. simpl. exists a. exists eq_refl. exists eq_refl. exists e.
      exists eq_refl. exists eq_refl. left. reflexivity.
    + spec IHtr Hitemj.
      destruct IHtr as [itemX [Houtput [Hinput [Hl1 [Hl2 [Hdestination HitemX]]]]]].
      exists itemX. repeat split; [assumption| assumption |].
      exists Hl1. exists Hl2. exists Hdestination. right. assumption.
  - spec IHtr Hitemj.
    destruct IHtr as [itemX [Houtput [Hinput [Hl1 [Hl2 [Hdestination HitemX]]]]]].
    exists itemX. repeat split; [assumption| assumption |].
    exists Hl1. exists Hl2. exists Hdestination. right. assumption.
Qed.

End ProjectionTraces_membership.
