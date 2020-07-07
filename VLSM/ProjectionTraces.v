Require Import List Streams Nat Bool.
Import ListNotations.
Require Import Logic.FunctionalExtensionality.

Require Import Coq.Logic.FinFun Coq.Logic.Eqdep.

From CasperCBC
     Require Import Lib.StreamExtras Lib.ListExtras Lib.Preamble VLSM.Common VLSM.Composition.

Context
  {message : Type}
  {index : Type}
  {IndEqDec : EqDec index}
  (i0 : index)
  {IT : index -> VLSM_type message}
  {IS : forall i : index, VLSM_sign (IT i)}
  (IM : forall n : index, VLSM (IS n))
  (T := composite_type IT)
  (S := composite_sig i0 IS)
  (constraint : @label _ T -> @state _ T * option message -> Prop)
  (X := composite_vlsm i0 IM constraint)
  (j : index)
  (Xj := composite_vlsm_constrained_projection i0 IM constraint j)
  .

Fixpoint finite_trace_projection_list
  (trx : list (@transition_item _ T))
  : list (@transition_item _ (type Xj))
  :=
  match trx with
  | [] => []
  | item :: trx =>
    let tail := finite_trace_projection_list trx in
    let s := destination item in
    let l := l item in
    let x := projT1 l in
    match eq_dec j x with
    | left e =>
      let lj := eq_rect_r _ (projT2 l) e in
      @Build_transition_item _ (type Xj) lj (input item) (s j) (output item) :: tail
    | _ => tail
    end
  end.

Definition from_projection
  (a : @transition_item _ T)
  : Prop
  := j = projT1 (l a).

Definition dec_from_projection
  (a : transition_item)
  : {from_projection a} + {~from_projection a}
  := eq_dec j (projT1 (l a)).

Definition finite_trace_projection_list_alt
  (trx : list (@transition_item _ T))
  (ftrx := (filter (predicate_to_function dec_from_projection) trx))
  (Hall: Forall from_projection ftrx)
  :=
  List.map
    (fun item : {a : @transition_item _ T | from_projection a} =>
      let (item, e) := item in
      let lj := eq_rect_r _ (projT2 (l item)) e in
      @Build_transition_item _ (type Xj)
        lj
        (input item)
        (destination item j)
        (output item)
    )
  (list_annotate from_projection ftrx Hall).

Lemma finite_trace_projection_list_alt_iff
  (trx : list (@transition_item _ T))
  (ftrx := (filter (predicate_to_function dec_from_projection) trx))
  (Hall: Forall from_projection ftrx)
  : finite_trace_projection_list_alt trx Hall = finite_trace_projection_list trx.
Proof.
  unfold ftrx in *. clear ftrx.
  generalize dependent Hall.
  induction trx; intros; try reflexivity.
  simpl.
  destruct (eq_dec j (projT1 (l a))) eqn:Heq.
  - assert
    (Hunroll :
      filter (predicate_to_function dec_from_projection) (a :: trx)
      = a :: filter (predicate_to_function dec_from_projection) trx
    ).
    { simpl. unfold predicate_to_function at 1. unfold dec_from_projection at 1.
      rewrite Heq. reflexivity.
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
    specialize UIP_refl__Streicher_K; intro K.
    unfold UIP_refl_ in K.
    unfold UIP_refl_on_ in K.
    replace (Forall_hd Hall) with e; try reflexivity.
    apply UIP.
  -  assert
    (Hunroll :
      filter (predicate_to_function dec_from_projection) (a :: trx)
      = filter (predicate_to_function dec_from_projection) trx
    ).
    { simpl. unfold predicate_to_function at 1. unfold dec_from_projection at 1.
      rewrite Heq. reflexivity.
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
  (s : @state _ T)
  (trx : list (@transition_item _ T))
  (Htr : finite_protocol_trace_from X s trx)
  (Hempty : finite_trace_projection_list trx = [])
  (t : (@transition_item _ T))
  (Hin : In t trx)
  : destination t j = s j.
Proof.
  generalize dependent t.
  induction Htr; simpl; intros t Hin.
  - inversion Hin.
  - destruct l as [i l].
    destruct H as [[[_om Hs'] [[_s Hiom] Hvalid]] Htransition].
    unfold transition in Htransition; simpl in Htransition.
    destruct (transition l (s' i, iom)) as [si' om'] eqn:Hteq.
    inversion Htransition; subst. clear Htransition.
    destruct Hin as [Heq | Hin]; subst; simpl in *; destruct (eq_dec j i).
    + inversion Hempty.
    + apply state_update_neq. assumption.
    + inversion Hempty.
    + specialize (IHHtr Hempty t Hin). rewrite IHHtr.
      apply state_update_neq. assumption.
Qed.

Lemma finite_trace_projection_last_state
  (start : @state _ T)
  (transitions : list (@transition_item _ T))
  (Htr : finite_protocol_trace_from X start transitions)
  (lstx := last (List.map destination transitions) start)
  (lstj := last (List.map destination (finite_trace_projection_list transitions)) (start j))
  : lstj = lstx j.
Proof.
  unfold lstx. unfold lstj. clear lstx. clear lstj.
  induction Htr; try reflexivity.
  destruct l as [i l].
  rewrite map_cons.
  rewrite unroll_last. simpl.
  destruct (eq_dec j i).
  - rewrite map_cons. rewrite unroll_last.
    assumption.
  - destruct H as [[[_om Hs'] [[_s Hiom] Hvalid]] Htransition].
    unfold transition in Htransition; simpl in Htransition.
    destruct (transition l (s' i, iom)) as [si' om'] eqn:Hteq.
    inversion Htransition; subst. clear Htransition.
    specialize (state_update_neq _ s' i si' j n); intro Hupd.
    rewrite Hupd in *.
    rewrite IHHtr.
    reflexivity.
Qed.

(* The projection of a finite protocol trace remains a protocol trace *)

Lemma finite_ptrace_projection
  (s : @state _ T)
  (Psj : protocol_state_prop Xj (s j))
  (trx : list (@transition_item _ T))
  (Htr : finite_protocol_trace_from X s trx)
   : finite_protocol_trace_from Xj (s j) (finite_trace_projection_list trx).
Proof.
  induction Htr.
  - constructor. assumption.
  - destruct l as [x lx]; simpl.
    destruct H as [[Ps' [Piom [Hv Hc]]] Ht].
    assert (Hpp : protocol_prop X (s, oom)).
    { rewrite <- Ht. destruct Ps' as [_om Ps']. destruct Piom as [_s Piom].
      apply (protocol_generated _ _ _ _ Ps' _ _ Piom). split; assumption.
    }
    assert (Hps : protocol_state_prop X s) by (exists oom; assumption).
    unfold composite_valid in Hv.
    destruct (eq_dec j x).
    + subst x.
      simpl in Ht.
      destruct (transition lx (s' j, iom)) as [si' om'] eqn:Hteq.
      inversion Ht; subst. rewrite state_update_eq in *.
      simpl in Hv.
      constructor.
      * apply IHHtr.
        exists oom.
        assert (Ht' : @transition _ _ _ Xj lx (s' j, iom) = (si', oom))
          by assumption.
        rewrite <- Ht'.
        destruct Psj as [os'j Psj].
        specialize (protocol_message_projection i0 IM constraint j _ Piom); intros [sj HPjiom].
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
            (@eq_rect_r index j (fun n : index => @label message (IT n)) lx j (@eq_refl index j))
            = lx
          ) by reflexivity.
        rewrite Heqlx.
        specialize (protocol_message_projection i0 IM constraint j _ Piom); intros HPjiom.
        repeat split; try assumption.
        exists s'.
        repeat split; assumption.
    + simpl in Ht. destruct (transition lx (s' x, iom)) eqn:Hteq.
      inversion Ht; subst.
      rewrite state_update_neq in IHHtr; try assumption.
      apply IHHtr.
      assumption.
Qed.

Lemma protocol_state_projection
  (s : state)
  (Hps : protocol_state_prop X s)
  : protocol_state_prop Xj (s j)
  .
Proof.
  destruct Hps as [om Hps].
  specialize (protocol_is_run X (s, om) Hps); intros [run Heqfinal].
  specialize (run_is_trace X run); intros Htrace.
  specialize (vlsm_run_last_state X run); intros Hlast.
  destruct run as [run Hrun]; simpl in *.
  rewrite <- Heqfinal in *. simpl in Hlast.
  destruct run; simpl in *. destruct start as [start Hstart]. simpl in *.
  clear - Htrace Hlast.
  destruct Htrace as [Htrace Hinit].
  specialize (finite_ptrace_projection start); intro Hproj.
  assert (Hstartj : initial_state_prop (start j)) by apply Hinit.
  remember (exist _ (start j) Hstartj) as istartj.
  assert (Hpstartj : protocol_state_prop Xj (start j)).
  { exists None.
    specialize (protocol_initial_state Xj istartj); subst; simpl; intro Hpinit.
    assumption.
  }
  specialize (Hproj Hpstartj _ Htrace).
  specialize (trace_is_run Xj istartj (finite_trace_projection_list transitions))
  ; subst istartj; simpl; intro Hrun.
  specialize (Hrun Hproj).
  destruct Hrun as [run [Hrun [Hstart Htrans]]].
  specialize (run_is_protocol Xj (exist _ run Hrun)); simpl; intro Hps.
  specialize (vlsm_run_last_state Xj (exist _ run Hrun)); simpl; intros Hlast'.
  rewrite Htrans in Hlast'. rewrite Hstart in Hlast'. simpl in Hlast'.
  destruct (final run) as (s', om). simpl in Hlast'.
  exists om.
  subst.
  specialize (finite_trace_projection_last_state start transitions Htrace)
  ; simpl; intro Hlast.
  clear - Hlast Hps.
  unfold T in Hlast; simpl in Hlast.
  rewrite <- Hlast.
  assumption.
Qed.

Definition in_projection
   (tr : Stream (@transition_item _ T))
   (n : nat)
   := from_projection (Str_nth n tr)
   .

Definition in_projection_dec
  := forall (tr : Stream (@transition_item _ T)),
       bounding (in_projection tr)
       + { ss : monotone_nat_stream
         | filtering_subsequence from_projection tr ss
         }.

Definition infinite_trace_projection_stream
  (ss: Stream (@transition_item _ T))
  (ks: monotone_nat_stream)
  (Hfilter: filtering_subsequence from_projection ss ks)
  : Stream (@transition_item _ (IT j))
  :=
  let subs := stream_subsequence ss ks in
  let HForAll := stream_filter_Forall from_projection ss ks Hfilter in
  let subsP := stream_annotate from_projection subs HForAll in
  Streams.map
    (fun item : {a : @transition_item _ T | from_projection a} =>
      let (item, e) := item in
      let lj := eq_rect_r _ (projT2 (l item)) e in
      @Build_transition_item _ (type Xj) lj (input item) (destination item j) (output item)
    )
    subsP.

Lemma finite_trace_projection_stream
  (ss: Stream (@transition_item _ T))
  (ks: monotone_nat_stream)
  (Hfilter: filtering_subsequence from_projection ss ks)
  (n : nat)
  (kn := Str_nth n (proj1_sig ks))
  (ss_to_kn := stream_prefix ss (succ kn))
  (sproj := infinite_trace_projection_stream ss ks Hfilter)
  : stream_prefix sproj (succ n) = finite_trace_projection_list ss_to_kn
  .
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
  assert
    (Heq' :
      (@stream_prefix
        (@sig (@transition_item message T)
          (fun a : @transition_item message T => from_projection a))
        (@stream_annotate (@transition_item message T) from_projection
          (@stream_subsequence (@transition_item message T) ss ks)
          (@stream_filter_Forall (@transition_item message T) from_projection
              ss ks Hfilter)) (succ n))
      =
      (@stream_prefix
        (@sig (@transition_item message T) from_projection)
        (@stream_annotate (@transition_item message T) from_projection
          (@stream_subsequence (@transition_item message T) ss ks)
          (@stream_filter_Forall (@transition_item message T) from_projection
              ss ks Hfilter)) (succ n))
    ) by reflexivity.
    rewrite Heq'.
    rewrite Heq.
    specialize
      (stream_filter_prefix
        from_projection
        dec_from_projection
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
  (tr : @Trace _ T)
  : @Trace _ (IT j).
destruct tr as [s ls | s ss].
- exact (Finite (s j) (finite_trace_projection_list ls)).
- specialize (Hproj_dec ss).
  destruct Hproj_dec as [[n1 _] | [ks Hfilter]].
  + exact (Finite (s j) (finite_trace_projection_list (stream_prefix ss n1))).
  + exact (Infinite (s j) (infinite_trace_projection_stream ss ks Hfilter)).
Defined.

Lemma trace_projection_initial_state
  (Hproj_dec : in_projection_dec)
  (tr : @Trace _ T)
  : trace_first (trace_projection Hproj_dec tr)
  = trace_first tr j
  .
Proof.
  destruct tr; try reflexivity.
  simpl.
  destruct (Hproj_dec s0).
  - destruct b; reflexivity.
  - destruct s1; reflexivity.
Qed.

Lemma infinite_ptrace_projection
  (s: @state _ T)
  (ss: Stream transition_item)
  (Psj: protocol_state_prop Xj (s j))
  (Htr: infinite_protocol_trace_from X s ss)
  (fs : monotone_nat_stream)
  (Hfs: filtering_subsequence from_projection ss fs)
  : infinite_protocol_trace_from Xj (s j) (infinite_trace_projection_stream ss fs Hfs)
  .
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
  (tr : @Trace _ T)
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
  (tr : @Trace _ T)
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
    apply (initial_state_projection i0 IM constraint j) in Hinit.
    exists (exist _ _ Hinit).
    reflexivity.
  - rewrite trace_projection_initial_state.
    apply initial_state_projection.
    assumption.
Qed.

(* We axiomatize projection friendliness as the converse of protocol_trace_projection *)
Definition finite_projection_friendly
  := forall
    (sj : @state _ (IT j))
    (trj : list (@transition_item _ (IT j)))
    (Htrj : finite_protocol_trace Xj sj trj),
    exists (sx : @state _ T) (trx : list (@transition_item _ T)),
      finite_protocol_trace X sx trx
      /\ sx j = sj
      /\ finite_trace_projection_list trx = trj.

Definition projection_friendly
  (Hproj_dec : in_projection_dec)
  := forall
  (trj : @Trace _ (IT j))
  (Htrj : protocol_trace_prop Xj trj),
  exists (tr : @Trace _ T),
    protocol_trace_prop X tr
    /\ trace_projection Hproj_dec tr = trj.

Lemma projection_friendly_finite
  (Hproj_dec : in_projection_dec)
  (Hfr : projection_friendly Hproj_dec)
  : finite_projection_friendly
  .
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
