Require Import List Streams.
Import ListNotations.
Require Import Logic.FunctionalExtensionality.

Require Import Coq.Logic.FinFun.

From Casper
     Require Import Lib.ListExtras Lib.Preamble VLSM.Common.

(* Section 2.4 VLSM composition *)

Section indexing. 
  
  Section indexed_type.

    Context {message : Type}
            {index : Type}
            `{IndEqDec : EqDec index}
            (IT : index -> VLSM_type message).

    Definition _indexed_state : Type :=
      forall n : index, (@state _ (IT n)).

    Definition _indexed_label
      : Type
      := sigT (fun n => @label _ (IT n)).

    Definition indexed_type : VLSM_type message :=
      {| state := _indexed_state
       ; label := _indexed_label
      |}.
  
    Definition indexed_state := @state message indexed_type.
    Definition indexed_label := @label message indexed_type.

    Definition state_update
               (s : indexed_state)
               (i : index)
               (si : @state message (IT i))
               (j : index)
      : @state message (IT j)
      :=
      match eq_dec j i with
      | left e => eq_rect_r (fun i => @state message (IT i)) si e
      | _ => s j
      end.

    Lemma state_update_neq 
               (s : indexed_state)
               (i : index)
               (si : @state message (IT i))
               (j : index)
               (Hneq : j <> i)
      : state_update s i si j = s j.
    Proof.
      unfold state_update. destruct (eq_dec j i); try contradiction. reflexivity.
    Qed.

    Lemma state_update_eq 
               (s : indexed_state)
               (i : index)
               (si : @state message (IT i))
      : state_update s i si i = si.
    Proof.
      unfold state_update.
      rewrite eq_dec_refl. reflexivity.
    Qed.

  End indexed_type.
  
  Section indexed_sig.

    Context {message : Type}
            {index : Type}
            `{IndEqDec : EqDec index}
            {IT : index -> VLSM_type message}
            (i0 : index)
            (IS : forall i : index, LSM_sig (IT i)).
    
    Definition _indexed_initial_state_prop
               (s : indexed_state IT)
      : Prop
      :=
        forall n : index, @initial_state_prop _ _ (IS n) (s n).

    Definition _indexed_initial_state
      := { s : indexed_state IT | _indexed_initial_state_prop s }.

    Definition _indexed_s0 : _indexed_initial_state.
      exists (fun (n : index) => proj1_sig (@s0 _ _ (IS n))).
      intro i. destruct s0 as [s Hs]. assumption.
    Defined.

    Definition _indexed_initial_message_prop (m : message) : Prop
      :=
        exists (n : index) (mi : @initial_message _ _ (IS n)), proj1_sig mi = m.

    (* An explicit argument for the initial state witness is no longer required: *) 
    Definition _indexed_m0 : message := @m0 _ _ (IS i0).

    Definition _indexed_l0 : indexed_label IT
      := existT _ i0 (@l0 _ _ (IS i0)) .

    Definition indexed_sig
      : LSM_sig (indexed_type IT)
      :=
        {|   initial_state_prop := _indexed_initial_state_prop
           ; s0 := _indexed_s0
           ; initial_message_prop := _indexed_initial_message_prop
           ; m0 := _indexed_m0
           ; l0 := _indexed_l0 
        |}.
  
  End indexed_sig.

  Section indexed_vlsm.

    Context {message : Type}
            {index : Type}
            `{IndEqDec : EqDec index}
            {IT : index -> VLSM_type message}
            (i0 : index)
            {IS : forall i : index, LSM_sig (IT i)}
            (IM : forall n : index, VLSM (IS n)).

    Definition _indexed_transition
               (l : indexed_label IT)
               (som : indexed_state IT * option message)
      : indexed_state IT * option message
      :=
      let (s, om) := som in
      let (i, li) := l in
      let (si', om') := transition li (s i, om) in
      (state_update IT s i si',  om').

    Definition _indexed_valid
               (l : indexed_label IT)
               (som : indexed_state IT * option message)
      : Prop
      :=
      let (s, om) := som in
      let (i, li) := l in
      valid li (s i, om).

    (* Section 2.4.3 Constrained VLSM composition *)

    Definition _indexed_valid_constrained
               (constraint : indexed_label IT -> indexed_state IT  * option message -> Prop)
               (l : indexed_label IT)
               (som : indexed_state IT * option message)
      :=
        _indexed_valid l som /\ constraint l som.

    Definition indexed_vlsm_constrained
               (constraint : indexed_label IT -> indexed_state IT * option (message) -> Prop)
      : VLSM (indexed_sig i0 IS)
      :=
        {|  transition := _indexed_transition
            ;   valid := _indexed_valid_constrained constraint
        |}.

    Definition indexed_transition
      (constraint : indexed_label IT -> indexed_state IT * option (message) -> Prop)
      := @transition _ _ _ (indexed_vlsm_constrained constraint).

    Definition indexed_valid
      (constraint : indexed_label IT -> indexed_state IT * option (message) -> Prop)
      := @valid _ _ _ (indexed_vlsm_constrained constraint).

    (* Section 2.4.3 Free VLSM composition using constraint = True *)

    Definition free_constraint 
               (l : indexed_label IT)
               (som : indexed_state IT * option message)
      : Prop
      :=
        True.

    Definition indexed_vlsm_free : VLSM (indexed_sig i0 IS)
      :=
        indexed_vlsm_constrained free_constraint
    .

  End indexed_vlsm.

  Section indexed_vlsm_decidable.

    Context {message : Type}
            {index : Type}
            `{IndEqDec : EqDec index}
            {IT : index -> VLSM_type message}
            (i0 : index)
            {IS : forall i : index, LSM_sig (IT i)}
            {IM : forall n : index, VLSM (IS n)}
            (IDM : forall n : index, VLSM_vdecidable (IM n)).

    (* Composing decidable VLSMs *)

    Definition _indexed_valid_decidable
               (l : indexed_label IT)
               (som : indexed_state IT * option message)
      : {_indexed_valid IM l som} + {~_indexed_valid IM l som}.
      destruct som as [s om].
      destruct l as [i li]; simpl.
      apply (valid_decidable (IM i)).
    Defined.

    Definition _indexed_valid_constrained_decidable
               {constraint : indexed_label IT -> indexed_state IT * option message -> Prop}
               (constraint_decidable : forall (l : indexed_label IT) (som : indexed_state IT * option (message)), {constraint l som} + {~constraint l som})
               (l : indexed_label IT)
               (som : indexed_state IT * option message)
      : {indexed_valid i0 IM constraint l som} + {~indexed_valid i0 IM constraint l som}.
      intros.
      destruct (constraint_decidable l som) as [Hc | Hnc].
      - destruct (_indexed_valid_decidable l som) as [Hv | Hnv].
        + left. split; try assumption.
        + right. intros [Hv _]. contradiction.
      - right. intros [_ Hc]. contradiction.
    Defined.

    Definition indexed_vlsm_constrained_vdecidable
               {constraint : indexed_label IT -> indexed_state IT * option message -> Prop}
               (constraint_decidable : forall (l : indexed_label IT) (som : indexed_state IT * option (message)), {constraint l som} + {~constraint l som})
      : VLSM_vdecidable (indexed_vlsm_constrained i0 IM constraint)
      :=
        {|  valid_decidable := _indexed_valid_constrained_decidable constraint_decidable
        |}.
  
    Definition indexed_valid_constrained_decidable
               {constraint : indexed_label IT -> indexed_state IT * option (message) -> Prop}
               (constraint_decidable : forall (l : indexed_label IT) (som : indexed_state IT * option (message)), {constraint l som} + {~constraint l som})
      := @valid_decidable _ _ _ _ (indexed_vlsm_constrained_vdecidable constraint_decidable).

    Definition free_constraint_decidable
               (l : indexed_label IT)
               (som : indexed_state IT * option (message))
      : {free_constraint l som} + {~free_constraint l som}
      := left I.

    Definition indexed_vlsm_free_vdecidable
      : VLSM_vdecidable (indexed_vlsm_free i0 IM)
      :=
        indexed_vlsm_constrained_vdecidable free_constraint_decidable.

  End indexed_vlsm_decidable.
End indexing.

(* Section 2.4.4 Projections into VLSM compositions *)
Section projections. 

  Context {message : Type}
          {index : Type}
          `{IndEqDec : EqDec index}
          (i0 : index)
          {IT : index -> VLSM_type message}
          {IS : forall i : index, LSM_sig (IT i)}
          (IM : forall n : index, VLSM (IS n))
          (T := indexed_type IT)
          (S := indexed_sig i0 IS)
          (constraint : @label _ T -> @state _ T * option message -> Prop)
          (X := indexed_vlsm_constrained i0 IM constraint)
          .

  Definition indexed_vlsm_constrained_projection_sig (i : index) : LSM_sig (IT i)
    :=
      {|      initial_state_prop := @initial_state_prop _ _ (IS i)
          ;   initial_message_prop := fun pmi => exists xm : (@protocol_message _ _ _ X), proj1_sig xm = pmi
          ;   s0 := @s0 _ _ (IS i)
          ;   m0 := @m0 _ _ (IS i)
          ;   l0 := @l0 _ _ (IS i)
      |}.

  Definition projection_valid
    (i : index)
    (li : @label _ (IT i))
    (siomi : @state _ (IT i) * option message)
    :=
    let (si, omi) := siomi in
    exists (ps : @protocol_state _ _ _ X) (opm : option (@protocol_message _ _ _ X)),
      (proj1_sig ps) i = si /\ option_map (@proj1_sig _ _) opm = omi
      /\ protocol_valid X (existT _ i li) (ps, opm)
    .
  
  Lemma composite_protocol_valid_implies_valid
    (i : index)
    (li : @label _ (IT i))
    (siomi : @state _ (IT i) * option message)
    (Hcomposite : projection_valid i li siomi)
    : @valid _ _ _ (IM i) li siomi
    .
  Proof.
    unfold projection_valid in Hcomposite.
    destruct siomi as [si omi].
    destruct Hcomposite as [[s Hps] [opm [Hsi [Homi Hvalid]]]].
    subst; simpl in *.
    destruct Hvalid as [Hvalid Hconstraint].
    unfold _indexed_valid in Hvalid. assumption.
  Qed.

  Definition indexed_vlsm_constrained_projection
             (i : index)
    : VLSM (indexed_vlsm_constrained_projection_sig i) :=
    {|  transition :=  @transition _ _ _ (IM i)
     ;  valid := projection_valid i
    |}. 

  Section fixed_projection.

    Context
      (j : index)
      (Proj := indexed_vlsm_constrained_projection j)
      .

    Lemma transition_projection : @transition _ _ (indexed_vlsm_constrained_projection_sig j) Proj = @transition _ _ _ (IM j).
    Proof. reflexivity.  Qed.

    Lemma protocol_message_projection
      (iom : option message)
      (HpmX : exists sx : state, protocol_prop X (sx, iom))
      : exists sj : state, protocol_prop Proj (sj, iom)
      .
    Proof.
      exists (proj1_sig s0).
      destruct iom as [im|].
      - specialize (protocol_initial_message Proj ); intro Hinit.
        assert (Hpim : protocol_message_prop X im)
          by assumption.
        assert (Hini : @initial_message_prop _ _ (sign Proj) im)
          by (exists (exist _ im Hpim); reflexivity).
        specialize (Hinit (exist _ im Hini)); simpl in Hinit.
        assumption.
      - apply (protocol_initial_state Proj).
    Qed.

(** 2.4.4.1 Projection friendly composition constraints **)

(*
    Definition projection_friendly
      :=
      forall
        (lj : @label _ (IT j))
        (sj : protocol_state Proj)
        (om : option (protocol_message Proj))
      , protocol_valid Proj lj (sj, om)
      -> exists (s : protocol_state X),
        (proj1_sig s) j = proj1_sig sj
        /\
        constraint (existT _ j lj) (proj1_sig s, option_map (@proj1_sig _ _) om)
      .
*)
    (* Projects the trace of a composed vlsm to component j *)
    
    Fixpoint finite_trace_projection_list
      (trx : list (@in_state_out _ T))
      : list (@in_state_out _ (type Proj))
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
          @Build_in_state_out _ (type Proj) lj (input item) (s j) (output item) :: tail
        | _ => tail
        end
      end.
    
    Lemma finite_trace_projection_empty
      (s : @state _ T)
      (trx : list (@in_state_out _ T))
      (Htr : finite_ptrace_from X s trx)
      (Hempty : finite_trace_projection_list trx = [])
      (t : (@in_state_out _ T))
      (Hin : In t trx)
      : destination t j = s j.
    Proof.
      generalize dependent t.
      induction Htr; simpl; intros t Hin.
      - inversion Hin.
      - destruct l as [i l].
        destruct H as [[_om Hs'] [[_s Hiom] [Hvalid Htransition]]].
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
      (transitions : list (@in_state_out _ T))
      (Htr : finite_ptrace_from X start transitions)
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
      - destruct H as [[_om Hs'] [[_s Hiom] [Hvalid Htransition]]].
        unfold transition in Htransition; simpl in Htransition.
        destruct (transition l (s' i, iom)) as [si' om'] eqn:Hteq.
        inversion Htransition; subst. clear Htransition.
        specialize (state_update_neq _ s' i si' j n); intro Hupd.
        rewrite Hupd in *.
        rewrite IHHtr.
        reflexivity.
    Qed.

    (* The projection of a protocol trace remains a protocol trace *)

    Lemma finite_ptrace_projection
      (s : @state _ T)
      (Psj : protocol_state_prop Proj (s j))
      (trx : list (@in_state_out _ T))
      (Htr : finite_ptrace_from X s trx)
       : finite_ptrace_from Proj (s j) (finite_trace_projection_list trx).
    Proof.
      induction Htr.
      - constructor. assumption.
      - destruct l as [x lx]; simpl.
        destruct H as [Ps' [Piom [[Hv Hc] Ht]]].
        assert (Hpp : protocol_prop X (s, oom)).
        { rewrite <- Ht. destruct Ps' as [_om Ps']. destruct Piom as [_s Piom].
          apply (protocol_generated _ _ _ _ Ps' _ _ Piom). split; assumption.
        }
        assert (Hps : protocol_state_prop X s) by (exists oom; assumption).
        unfold indexed_valid in Hv.
        destruct (eq_dec j x).
        + subst x.
          simpl in Ht.
          destruct (transition lx (s' j, iom)) as [si' om'] eqn:Hteq.
          inversion Ht; subst. rewrite state_update_eq in *.
          simpl in Hv.
          constructor.
          * apply IHHtr.
            exists oom.
            assert (Ht' : @transition _ _ _ Proj lx (s' j, iom) = (si', oom))
              by assumption.
            rewrite <- Ht'. 
            destruct Psj as [os'j Psj].
            specialize (protocol_message_projection _ Piom); intros [sj HPjiom].
            apply (protocol_generated Proj lx (s' j) os'j Psj sj iom HPjiom).
            unfold valid; simpl.
            exists (exist _ s' Ps').
            destruct iom as [im|]
            ; (exists (Some (exist _ im Piom)) || exists None)
            ; repeat (split; try assumption).
          * assert
              (Heqlx :
                (@eq_rect_r index j (fun n : index => @label message (IT n)) lx j (@eq_refl index j))
                = lx
              ) by reflexivity.
            rewrite Heqlx.
            unfold verbose_valid_protocol_transition.
            destruct Psj as [omsj Psj].
            split; try (exists omsj; assumption).
            specialize (protocol_message_projection _ Piom); intros HPjiom.
            split; try assumption.
            simpl in Ht. simpl in Hv.
            split; try assumption.
            unfold valid; simpl.
            exists (exist _ s' Ps').
            destruct iom as [im|]
            ; (exists (Some (exist _ im Piom)) || exists None)
            ; repeat (split; try assumption).
        + simpl in Ht. destruct (transition lx (s' x, iom)) eqn:Hteq.
          inversion Ht; subst.
          rewrite state_update_neq in IHHtr; try assumption.
          apply IHHtr.
          assumption.
    Qed.

    Lemma protocol_state_projection
      (s : state)
      (Hps : protocol_state_prop X s)
      : protocol_state_prop Proj (s j)
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
      assert (Hpstartj : protocol_state_prop Proj (start j)).
      { exists None.
        specialize (protocol_initial_state Proj istartj); subst; simpl; intro Hpinit.
        assumption.
      }
      specialize (Hproj Hpstartj _ Htrace).
      specialize (trace_is_run Proj istartj (finite_trace_projection_list transitions))
      ; subst istartj; simpl; intro Hrun.
      specialize (Hrun Hproj).
      destruct Hrun as [run [Hrun [Hstart Htrans]]].
      specialize (run_is_protocol Proj (exist _ run Hrun)); simpl; intro Hps.
      specialize (vlsm_run_last_state Proj (exist _ run Hrun)); simpl; intros Hlast'.
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
      

    (* We axiomatize projection friendliness as the converse of finite_ptrace_projection *)
    Definition projection_friendly
      := forall
        (sj : @state _ (IT j))
        (trj : list (@in_state_out _ (IT j)))
        (Htrj : finite_ptrace_from Proj sj trj),
        exists (sx : @state _ T) (trx : list (@in_state_out _ T)),
          finite_ptrace_from X sx trx
          /\ sx j = sj
          /\ finite_trace_projection_list trx = trj.

    Lemma proj_message_full_protocol_prop
      (Full := message_full_vlsm (IM j))
      (s : state)
      (om : option message)
      (Hps : protocol_prop Proj (s, om))
      : protocol_prop Full (s, om).
    Proof.
      induction Hps.
      - apply (protocol_initial_state Full is).
      - destruct im as [m Him]. simpl in om0. clear Him.
        assert (Him : @initial_message_prop _ _ (message_full_vlsm_sig X) m)
          by exact I.
        apply (protocol_initial_message Full (exist _ m Him)).
      - apply (protocol_generated Full) with _om _s; try assumption.
        apply composite_protocol_valid_implies_valid. assumption.
    Qed.

    Lemma proj_message_full_verbose_valid_protocol_transition
      (Full := message_full_vlsm (IM j))
      (l : label)
      (is os : state)
      (iom oom : option message)
      (Ht : verbose_valid_protocol_transition Proj l is os iom oom)
      : verbose_valid_protocol_transition Full l is os iom oom
      .
    Proof.
      destruct Ht as [[_om Hps] [[_s Hpm] [Hv Ht]]].
      repeat (split; try assumption).
      - exists _om. apply proj_message_full_protocol_prop. assumption.
      - exists _s. apply proj_message_full_protocol_prop. assumption.
      - apply composite_protocol_valid_implies_valid. assumption.
    Qed.

    Lemma proj_message_full_finite_ptrace
      (Full := message_full_vlsm (IM j))
      (s : state)
      (ls : list in_state_out)
      (Hpxt : finite_ptrace_from Proj s ls)
      : finite_ptrace_from Full s ls
      .
    Proof.
      induction Hpxt.
      - constructor.
        destruct H as [m H].
        apply proj_message_full_protocol_prop in H.
        exists m. assumption.
      - constructor; try assumption.
        apply proj_message_full_verbose_valid_protocol_transition. assumption.
    Qed.

    Lemma proj_message_full_infinite_ptrace
      (Full := message_full_vlsm (IM j))
      (s : state)
      (ls : Stream in_state_out)
      (Hpxt : infinite_ptrace_from Proj s ls)
      : infinite_ptrace_from Full s ls
      .
    Proof.
      generalize dependent ls. generalize dependent s.
      cofix H.
      intros s [[l input destination output] ls] Hx.
      inversion Hx; subst.
      specialize (H destination ls H3).
      constructor; try assumption.
      apply proj_message_full_verbose_valid_protocol_transition.
      assumption.
    Qed.

    Lemma proj_message_full_incl
      (Full := message_full_vlsm (IM j))
      : VLSM_incl Proj Full
      .
    Proof.
      intros [s ls| s ss]; simpl; intros [Hxt Hinit].  
      - apply proj_message_full_finite_ptrace in Hxt.
        split; try assumption.
      - apply proj_message_full_infinite_ptrace in Hxt.
        split; try assumption.
    Qed.

    End fixed_projection.

End projections.

Section free_projections. 

  Context {message : Type}
          {index : Type}
          `{IndEqDec : EqDec index}
          (i0 : index)
          {IT : index -> VLSM_type message}
          {IS : forall i : index, LSM_sig (IT i)}
          (IM : forall n : index, VLSM (IS n))
          .

  Definition indexed_vlsm_free_projection_sig
             (i : index)
    : LSM_sig (IT i)
    :=
      indexed_vlsm_constrained_projection_sig i0 IM free_constraint i.

  Definition indexed_vlsm_free_projection
             (i : index)
    : VLSM (indexed_vlsm_free_projection_sig i)
    :=
      indexed_vlsm_constrained_projection i0 IM free_constraint i.
End free_projections.
