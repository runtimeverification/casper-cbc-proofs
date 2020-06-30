Require Import List Streams Nat Bool.
Import ListNotations.
Require Import Logic.FunctionalExtensionality.

Require Import Coq.Logic.FinFun Coq.Logic.Eqdep.

From CasperCBC
     Require Import Lib.StreamExtras Lib.ListExtras Lib.Preamble VLSM.Common.

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

    Lemma state_update_id
               (s : indexed_state)
               (i : index)
               (si : @state message (IT i))
               (Heq : s i = si)
      : state_update s i si = s.
    Proof.
      apply functional_extensionality_dep_good.
      intro j.
      destruct (eq_dec j i).
      - subst. apply state_update_eq.
      - apply state_update_neq. assumption.
    Qed.

    Lemma state_update_twice
               (s : indexed_state)
               (i : index)
               (si si': @state message (IT i))
      : state_update (state_update s i si) i si' = state_update s i si'.
    Proof.
      apply functional_extensionality_dep_good.
      intro j.
      destruct (eq_dec j i).
      - subst. rewrite state_update_eq. symmetry. apply state_update_eq.
      - repeat rewrite state_update_neq; try assumption.
        reflexivity.
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

    Lemma protocol_prop_indexed_free_lift
      (S := (indexed_sig i0 IS))
      (j : index)
      (sj : @state _ (IT j))
      (om : option message)
      (Hp : protocol_prop (IM j) (sj, om))
      (s0X := proj1_sig (@s0 _ _ S))
      : protocol_prop indexed_vlsm_free ((state_update IT s0X j sj), om)
      .
    Proof.
      remember (sj, om) as sjom.
      generalize dependent om. generalize dependent sj.
      induction Hp; intros; inversion Heqsjom; subst; clear Heqsjom.
      - assert (Hinit : @initial_state_prop _ _ S (state_update IT s0X j s)).
        { intro i.
          destruct (eq_dec i j).
          - subst; rewrite state_update_eq. unfold s. destruct is. assumption.
          - rewrite state_update_neq; try assumption.
            destruct (@s0 _ _ S) as [s00 Hinit].
            unfold s0X; clear s0X; simpl.
            apply Hinit.
        }
        remember (exist (@initial_state_prop _ _ S) (state_update IT s0X j s) Hinit) as six.
        replace (state_update IT s0X j s) with (proj1_sig six); try (subst; reflexivity).
        apply (protocol_initial_state indexed_vlsm_free).
      - assert (Hinit : @initial_message_prop _ _ S (proj1_sig im)).
        { exists j. exists im. reflexivity. }
        replace (state_update IT s0X j s) with s0X
        ; try (symmetry; apply state_update_id; reflexivity).
        unfold s in *; unfold om in *; clear s om.
        destruct im as [m _H]; simpl in *; clear _H.
        remember (exist (@initial_message_prop _ _ S) m Hinit) as im.
        replace m with (proj1_sig im); try (subst; reflexivity).
        apply (protocol_initial_message indexed_vlsm_free).
      - specialize (IHHp1 s _om eq_refl).
        specialize (IHHp2 _s om eq_refl).
        replace (state_update IT s0X j sj, om0) with (@transition _ _ _ indexed_vlsm_free (existT _ j l) (state_update IT s0X j s, om)).
        + apply (protocol_generated indexed_vlsm_free) with _om (state_update IT s0X j _s)
          ; try assumption.
          split; try exact I.
          simpl. rewrite state_update_eq. assumption.
        + simpl. rewrite state_update_eq. rewrite H0.
          f_equal.
          apply state_update_twice.
    Qed.

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

    Lemma initial_state_projection
      (s : @state _ T)
      (Hinit : @initial_state_prop _ _ S s)
      : @initial_state_prop _ _ (sign Proj) (s j)
      .
    Proof.
      specialize (Hinit j).
      assumption.
    Qed.

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

    Lemma projection_valid_protocol_transition
      (lj : label)
      (ps : @protocol_state _ _ _ X)
      (opm : option (@protocol_message _ _ _ X))
      (sj := (proj1_sig ps) j)
      (omj := option_map (@proj1_sig _ _) opm)
      (Hv : protocol_valid X (existT _ j lj) (ps, opm))
      : protocol_prop X (@transition _ _ _ X (existT _ j lj) (proj1_sig ps, omj))
      .
    Proof.
      destruct ps as [psX HpsX].
      simpl in sj. unfold sj in *. clear sj.
      destruct HpsX as [_omX HpsX].
      destruct opm as [[pmX [_sX HpmX]]|]
      ; simpl in omj; unfold omj in *; clear omj.
      - apply (protocol_generated X) with _omX _sX; assumption.
      - apply (protocol_generated X) with _omX (proj1_sig (@s0 _ _ S))
        ; try assumption.
        apply (protocol_initial_state X).
    Qed.

    Lemma protocol_message_projection_rev
      (iom : option message)
      (Hpmj: exists sj : state, protocol_prop Proj (sj, iom))
      : exists sx : state, protocol_prop X (sx, iom)
      .
    Proof.
      destruct Hpmj as [sj Hpmj].
      inversion Hpmj; subst.
      - exists (proj1_sig (@s0 _ _ S)).
        apply (protocol_initial_state X).
      - destruct im as [im Him].
        unfold om in *; simpl in *; clear om.
        destruct Him as [[m Hpm] Heq].
        subst; assumption.
      - destruct Hv as [psX [opm [Heqs [Heqopm Hv]]]].
        simpl in Heqs. rewrite <- Heqs in *. clear Heqs.
        specialize (projection_valid_protocol_transition l psX opm Hv)
        ; intro HpsX'.
        rewrite Heqopm in HpsX'.
        remember (@transition _ _ _ X (existT (fun n : index => label) j l) (proj1_sig psX, om)) as som'.
        destruct som' as [s' om'].
        exists s'.
        simpl in Heqsom'.
        rewrite H0 in Heqsom'.
        inversion Heqsom'; subst.
        assumption.
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

    Definition from_projection
      (a : @in_state_out _ T)
      : Prop
      := j = projT1 (l a).
    
    Definition dec_from_projection
      (a : in_state_out)
      : {from_projection a} + {~from_projection a}
      := eq_dec j (projT1 (l a)).
    
    Definition finite_trace_projection_list_alt
      (trx : list (@in_state_out _ T))
      (ftrx := (filter (predicate_to_function dec_from_projection) trx))
      (Hall: Forall from_projection ftrx)
      :=
      List.map
        (fun item : {a : @in_state_out _ T | from_projection a} =>
          let (item, e) := item in
          let lj := eq_rect_r _ (projT2 (l item)) e in
          @Build_in_state_out _ (type Proj)
            lj
            (input item)
            (destination item j)
            (output item)
        )
      (list_annotate from_projection ftrx Hall).
    
    Lemma finite_trace_projection_list_alt_iff
      (trx : list (@in_state_out _ T))
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

    (* The projection of a finite protocol trace remains a protocol trace *)

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

    Definition in_projection
       (tr : Stream (@in_state_out _ T))
       (n : nat)
       := from_projection (Str_nth n tr)
       .

    Definition in_projection_dec
      := forall (tr : Stream (@in_state_out _ T)),
           bounding (in_projection tr)
           + { ss : monotone_nat_stream
             | filtering_subsequence from_projection tr ss
             }.

    Definition infinite_trace_projection_stream
      (ss: Stream (@in_state_out _ T))
      (ks: monotone_nat_stream)
      (Hfilter: filtering_subsequence from_projection ss ks)
      : Stream (@in_state_out _ (IT j))
      :=
      let subs := stream_subsequence ss ks in
      let HForAll := stream_filter_Forall from_projection ss ks Hfilter in
      let subsP := stream_annotate from_projection subs HForAll in
      Streams.map
        (fun item : {a : @in_state_out _ T | from_projection a} =>
          let (item, e) := item in
          let lj := eq_rect_r _ (projT2 (l item)) e in
          @Build_in_state_out _ (type Proj) lj (input item) (destination item j) (output item)
        )
        subsP.

    Lemma finite_trace_projection_stream
      (ss: Stream (@in_state_out _ T))
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
            (@sig (@in_state_out message T)
              (fun a : @in_state_out message T => from_projection a))
            (@stream_annotate (@in_state_out message T) from_projection
              (@stream_subsequence (@in_state_out message T) ss ks)
              (@stream_filter_Forall (@in_state_out message T) from_projection
                  ss ks Hfilter)) (succ n))
          =
          (@stream_prefix
            (@sig (@in_state_out message T) from_projection)
            (@stream_annotate (@in_state_out message T) from_projection
              (@stream_subsequence (@in_state_out message T) ss ks)
              (@stream_filter_Forall (@in_state_out message T) from_projection
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
      : trace_initial_state (trace_projection Hproj_dec tr)
      = trace_initial_state tr j
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
      (ss: Stream in_state_out)
      (Psj: protocol_state_prop Proj (s j))
      (Htr: infinite_ptrace_from X s ss)
      (fs : monotone_nat_stream)
      (Hfs: filtering_subsequence from_projection ss fs)
      : infinite_ptrace_from Proj (s j) (infinite_trace_projection_stream ss fs Hfs)
      .
    Proof.
      apply infinite_ptrace_from_prefix_rev.
      specialize (infinite_ptrace_from_prefix X s ss Htr); intro Hftr.
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
      (Psj : protocol_state_prop Proj (trace_initial_state tr j))
      (Htr : ptrace_from_prop X tr)
       : ptrace_from_prop Proj (trace_projection Hproj_dec tr).
    Proof.
      destruct tr as [s ls | s ss].
      - apply finite_ptrace_projection; assumption.
      - simpl. destruct (Hproj_dec ss) as [[n _]|Hinf].
        + apply finite_ptrace_projection; try assumption.
          apply infinite_ptrace_from_prefix. assumption.
        + destruct Hinf as [ks HFilter].
          apply infinite_ptrace_projection; assumption.
    Qed.

    Lemma protocol_trace_projection
      (Hproj_dec : in_projection_dec)
      (tr : @Trace _ T)
      (Htr : protocol_trace_prop X tr)
      : protocol_trace_prop Proj (trace_projection Hproj_dec tr).
    Proof.
      assert (Hfrom := protocol_trace_from X tr Htr).
      assert (Hinit := protocol_trace_initial X tr Htr).
      apply protocol_trace_from_iff.
      split.
      - apply ptrace_from_projection; try assumption.
        apply protocol_state_prop_iff.
        left.
        apply initial_state_projection in Hinit.
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
        (trj : list (@in_state_out _ (IT j)))
        (Htrj : finite_ptrace Proj sj trj),
        exists (sx : @state _ T) (trx : list (@in_state_out _ T)),
          finite_ptrace X sx trx
          /\ sx j = sj
          /\ finite_trace_projection_list trx = trj.

    Definition projection_friendly
      (Hproj_dec : in_projection_dec)
      := forall
      (trj : @Trace _ (IT j))
      (Htrj : protocol_trace_prop Proj trj),
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
        apply infinite_ptrace_from_prefix.
        assumption.
    Qed.

    Lemma proj_pre_loaded_protocol_prop
      (PreLoaded := pre_loaded_vlsm (IM j))
      (s : state)
      (om : option message)
      (Hps : protocol_prop Proj (s, om))
      : protocol_prop PreLoaded (s, om).
    Proof.
      induction Hps.
      - apply (protocol_initial_state PreLoaded is).
      - destruct im as [m Him]. simpl in om0. clear Him.
        assert (Him : @initial_message_prop _ _ (pre_loaded_vlsm_sig X) m)
          by exact I.
        apply (protocol_initial_message PreLoaded (exist _ m Him)).
      - apply (protocol_generated PreLoaded) with _om _s; try assumption.
        apply composite_protocol_valid_implies_valid. assumption.
    Qed.

    Lemma proj_pre_loaded_verbose_valid_protocol_transition
      (PreLoaded := pre_loaded_vlsm (IM j))
      (l : label)
      (is os : state)
      (iom oom : option message)
      (Ht : verbose_valid_protocol_transition Proj l is os iom oom)
      : verbose_valid_protocol_transition PreLoaded l is os iom oom
      .
    Proof.
      destruct Ht as [[_om Hps] [[_s Hpm] [Hv Ht]]].
      repeat (split; try assumption).
      - exists _om. apply proj_pre_loaded_protocol_prop. assumption.
      - exists _s. apply proj_pre_loaded_protocol_prop. assumption.
      - apply composite_protocol_valid_implies_valid. assumption.
    Qed.

    Lemma proj_pre_loaded_finite_ptrace
      (PreLoaded := pre_loaded_vlsm (IM j))
      (s : state)
      (ls : list in_state_out)
      (Hpxt : finite_ptrace_from Proj s ls)
      : finite_ptrace_from PreLoaded s ls
      .
    Proof.
      induction Hpxt.
      - constructor.
        destruct H as [m H].
        apply proj_pre_loaded_protocol_prop in H.
        exists m. assumption.
      - constructor; try assumption.
        apply proj_pre_loaded_verbose_valid_protocol_transition. assumption.
    Qed.

    Lemma proj_pre_loaded_infinite_ptrace
      (PreLoaded := pre_loaded_vlsm (IM j))
      (s : state)
      (ls : Stream in_state_out)
      (Hpxt : infinite_ptrace_from Proj s ls)
      : infinite_ptrace_from PreLoaded s ls
      .
    Proof.
      generalize dependent ls. generalize dependent s.
      cofix H.
      intros s [[l input destination output] ls] Hx.
      inversion Hx; subst.
      specialize (H destination ls H3).
      constructor; try assumption.
      apply proj_pre_loaded_verbose_valid_protocol_transition.
      assumption.
    Qed.

    Lemma proj_pre_loaded_incl
      (PreLoaded := pre_loaded_vlsm (IM j))
      : VLSM_incl Proj PreLoaded
      .
    Proof.
      intros [s ls| s ss]; simpl; intros [Hxt Hinit].  
      - apply proj_pre_loaded_finite_ptrace in Hxt.
        split; try assumption.
      - apply proj_pre_loaded_infinite_ptrace in Hxt.
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
          (X := indexed_vlsm_free i0 IM)
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

Section binary_composition.
  Context
    {message : Type}
    {T1 T2 : VLSM_type message}
    {S1 : LSM_sig T1}
    {S2 : LSM_sig T2}
    (M1 : VLSM S1)
    (M2 : VLSM S2)
    .

  Definition binary_index : Set := bool.

  Definition first : binary_index := true.
  Definition second : binary_index := false.

  Program Instance binary_index_dec :  EqDec binary_index := bool_dec. 

  Definition binary_IT
    (i : binary_index)
    :=
    match i with
    | true => T1
    | false => T2
    end.
  
  Definition binary_IS (i : binary_index) : LSM_sig (binary_IT i)
    :=
    match i with
    | true => S1
    | false => S2
    end.
  
  Definition binary_IM (i : binary_index) : VLSM (binary_IS i)
    :=
    match i with
    | true => M1
    | false => M2
    end.

  Definition binary_free_composition
    : VLSM (indexed_sig first binary_IS)
    := indexed_vlsm_free first binary_IM.

  Definition binary_free_composition_fst
    := indexed_vlsm_free_projection first binary_IM  first.

  Definition binary_free_composition_snd
    := indexed_vlsm_free_projection first binary_IM  second.

End binary_composition.
