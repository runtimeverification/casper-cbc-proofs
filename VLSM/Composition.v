Require Import List Streams Nat Bool.
Import ListNotations.
Require Import Logic.FunctionalExtensionality.

Require Import Coq.Logic.FinFun Coq.Logic.Eqdep.

From CasperCBC
     Require Import Lib.StreamExtras Lib.ListExtras Lib.Preamble VLSM.Common.

(**

** VLSM compositions and projections

This section provides Coq definitions for composite VLSMs and their projections
to components.

In the sequel we will succesively define 
*)

Section indexing.

  Section composite_type.

    Context {message : Type}
            {index : Type}
            {IndEqDec : EqDec index}
            (IT : index -> VLSM_type message).

    Definition _composite_state : Type :=
      forall n : index, (@state _ (IT n)).

    Definition _composite_label
      : Type
      := sigT (fun n => @label _ (IT n)).

    Definition composite_type : VLSM_type message :=
      {| state := _composite_state
       ; label := _composite_label
      |}.

    Definition composite_state := @state message composite_type.
    Definition composite_label := @label message composite_type.

    Definition state_update
               (s : composite_state)
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
               (s : composite_state)
               (i : index)
               (si : @state message (IT i))
               (j : index)
               (Hneq : j <> i)
      : state_update s i si j = s j.
    Proof.
      unfold state_update. destruct (eq_dec j i); try contradiction. reflexivity.
    Qed.

    Lemma state_update_eq
               (s : composite_state)
               (i : index)
               (si : @state message (IT i))
      : state_update s i si i = si.
    Proof.
      unfold state_update.
      rewrite eq_dec_refl. reflexivity.
    Qed.

    Lemma state_update_id
               (s : composite_state)
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
               (s : composite_state)
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

  End composite_type.

  Section composite_sig.

    Context {message : Type}
            {index : Type}
            {IndEqDec : EqDec index}
            {IT : index -> VLSM_type message}
            (i0 : index)
            (IS : forall i : index, LSM_sig (IT i)).

    Definition _composite_initial_state_prop
               (s : composite_state IT)
      : Prop
      :=
        forall n : index, @initial_state_prop _ _ (IS n) (s n).

    Definition _composite_initial_state
      := { s : composite_state IT | _composite_initial_state_prop s }.

    Definition _composite_s0 : _composite_initial_state.
      exists (fun (n : index) => proj1_sig (@s0 _ _ (IS n))).
      intro i. destruct s0 as [s Hs]. assumption.
    Defined.

    Definition _composite_initial_message_prop (m : message) : Prop
      :=
        exists (n : index) (mi : @initial_message _ _ (IS n)), proj1_sig mi = m.

    (* An explicit argument for the initial state witness is no longer required: *)
    Definition _composite_m0 : message := @m0 _ _ (IS i0).

    Definition _composite_l0 : composite_label IT
      := existT _ i0 (@l0 _ _ (IS i0)) .

    Definition composite_sig
      : LSM_sig (composite_type IT)
      :=
        {|   initial_state_prop := _composite_initial_state_prop
           ; s0 := _composite_s0
           ; initial_message_prop := _composite_initial_message_prop
           ; m0 := _composite_m0
           ; l0 := _composite_l0
        |}.

  End composite_sig.

  Section composite_vlsm.

    Context {message : Type}
            {index : Type}
            {IndEqDec : EqDec index}
            {IT : index -> VLSM_type message}
            (i0 : index)
            {IS : forall i : index, LSM_sig (IT i)}
            (IM : forall n : index, VLSM (IS n)).

    Definition _composite_transition
               (l : composite_label IT)
               (som : composite_state IT * option message)
      : composite_state IT * option message
      :=
      let (s, om) := som in
      let (i, li) := l in
      let (si', om') := transition li (s i, om) in
      (state_update IT s i si',  om').

    Definition _composite_valid
               (l : composite_label IT)
               (som : composite_state IT * option message)
      : Prop
      :=
      let (s, om) := som in
      let (i, li) := l in
      valid li (s i, om).

    (* Section 2.4.3 Constrained VLSM composition *)

    Definition _composite_valid_constrained
               (constraint : composite_label IT -> composite_state IT  * option message -> Prop)
               (l : composite_label IT)
               (som : composite_state IT * option message)
      :=
        _composite_valid l som /\ constraint l som.

    Definition composite_vlsm_constrained
               (constraint : composite_label IT -> composite_state IT * option (message) -> Prop)
      : VLSM (composite_sig i0 IS)
      :=
        {|  transition := _composite_transition
            ;   valid := _composite_valid_constrained constraint
        |}.

    Section constraint_subsumption.

    Definition constraint_subsumption
        (constraint1 constraint2 : composite_label IT -> composite_state IT * option message -> Prop)
        :=
        forall (l : composite_label IT) (som : composite_state IT * option message),
          constraint1 l som -> constraint2 l som.

    Context
      (constraint1 constraint2 : composite_label IT -> composite_state IT * option message -> Prop)
      (Hsubsumption : constraint_subsumption constraint1 constraint2)
      (X1 := composite_vlsm_constrained constraint1)
      (X2 := composite_vlsm_constrained constraint2)
      (S := composite_sig i0 IS)
      (T := composite_type IT)
      .

    Lemma constraint_subsumption_protocol_valid
      (l : label)
      (s : state)
      (om : option message)
      (Hv : protocol_valid X1 l (s, om))
      : @valid _ _ _ X2 l (s, om)
      .
    Proof.
      destruct Hv as [Hps [Hopm [Hv Hctr]]].
      split; try assumption.
      apply Hsubsumption.
      assumption.
    Qed.

    Lemma constraint_subsumption_protocol_prop
      (s : state)
      (om : option message)
      (Hps : protocol_prop X1 (s, om))
      : protocol_prop X2 (s, om).
    Proof.
      induction Hps.
      - apply (protocol_initial_state X2 is).
      - apply (protocol_initial_message X2).
      - apply (protocol_generated X2) with _om _s; try assumption.
        apply constraint_subsumption_protocol_valid.
        apply protocol_generated_valid with _om _s; assumption.
    Qed.

    Lemma constraint_subsumption_incl
      : VLSM_incl X1 X2
      .
    Proof.
      apply (basic_VLSM_incl X1 X2)
      ; intros; try (assumption || reflexivity).
      - destruct H as [_ [[_s Hom] _]]. exists _s.
        apply constraint_subsumption_protocol_prop.
        assumption.
      - apply constraint_subsumption_protocol_valid.
        assumption.
    Qed.

    End constraint_subsumption.

    Definition composite_transition
      (constraint : composite_label IT -> composite_state IT * option (message) -> Prop)
      := @transition _ _ _ (composite_vlsm_constrained constraint).

    Definition composite_valid
      (constraint : composite_label IT -> composite_state IT * option (message) -> Prop)
      := @valid _ _ _ (composite_vlsm_constrained constraint).

    (* Section 2.4.3 Free VLSM composition using constraint = True *)

    Definition free_constraint
               (l : composite_label IT)
               (som : composite_state IT * option message)
      : Prop
      :=
        True.

    Definition composite_vlsm_free : VLSM (composite_sig i0 IS)
      :=
        composite_vlsm_constrained free_constraint
    .

    Lemma protocol_prop_composite_free_lift
      (S := (composite_sig i0 IS))
      (j : index)
      (sj : @state _ (IT j))
      (om : option message)
      (Hp : protocol_prop (IM j) (sj, om))
      (s0X := proj1_sig (@s0 _ _ S))
      : protocol_prop composite_vlsm_free ((state_update IT s0X j sj), om)
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
        apply (protocol_initial_state composite_vlsm_free).
      - assert (Hinit : @initial_message_prop _ _ S (proj1_sig im)).
        { exists j. exists im. reflexivity. }
        replace (state_update IT s0X j s) with s0X
        ; try (symmetry; apply state_update_id; reflexivity).
        unfold s in *; unfold om in *; clear s om.
        destruct im as [m _H]; simpl in *; clear _H.
        remember (exist (@initial_message_prop _ _ S) m Hinit) as im.
        replace m with (proj1_sig im); try (subst; reflexivity).
        apply (protocol_initial_message composite_vlsm_free).
      - specialize (IHHp1 s _om eq_refl).
        specialize (IHHp2 _s om eq_refl).
        replace (state_update IT s0X j sj, om0) with (@transition _ _ _ composite_vlsm_free (existT _ j l) (state_update IT s0X j s, om)).
        + apply (protocol_generated composite_vlsm_free) with _om (state_update IT s0X j _s)
          ; try assumption.
          split; try exact I.
          simpl. rewrite state_update_eq. assumption.
        + simpl. rewrite state_update_eq. rewrite H0.
          f_equal.
          apply state_update_twice.
    Qed.

  End composite_vlsm.

  Section composite_vlsm_decidable.

    Context {message : Type}
            {index : Type}
            {IndEqDec : EqDec index}
            {IT : index -> VLSM_type message}
            (i0 : index)
            {IS : forall i : index, LSM_sig (IT i)}
            {IM : forall n : index, VLSM (IS n)}
            (IDM : forall n : index, VLSM_vdecidable (IM n)).

    (* Composing decidable VLSMs *)

    Definition _composite_valid_decidable
               (l : composite_label IT)
               (som : composite_state IT * option message)
      : {_composite_valid IM l som} + {~_composite_valid IM l som}.
      destruct som as [s om].
      destruct l as [i li]; simpl.
      apply (valid_decidable (IM i)).
    Defined.

    Definition _composite_valid_constrained_decidable
               {constraint : composite_label IT -> composite_state IT * option message -> Prop}
               (constraint_decidable : forall (l : composite_label IT) (som : composite_state IT * option (message)), {constraint l som} + {~constraint l som})
               (l : composite_label IT)
               (som : composite_state IT * option message)
      : {composite_valid i0 IM constraint l som} + {~composite_valid i0 IM constraint l som}.
      intros.
      destruct (constraint_decidable l som) as [Hc | Hnc].
      - destruct (_composite_valid_decidable l som) as [Hv | Hnv].
        + left. split; try assumption.
        + right. intros [Hv _]. contradiction.
      - right. intros [_ Hc]. contradiction.
    Defined.

    Definition composite_vlsm_constrained_vdecidable
               {constraint : composite_label IT -> composite_state IT * option message -> Prop}
               (constraint_decidable : forall (l : composite_label IT) (som : composite_state IT * option (message)), {constraint l som} + {~constraint l som})
      : VLSM_vdecidable (composite_vlsm_constrained i0 IM constraint)
      :=
        {|  valid_decidable := _composite_valid_constrained_decidable constraint_decidable
        |}.

    Definition composite_valid_constrained_decidable
               {constraint : composite_label IT -> composite_state IT * option (message) -> Prop}
               (constraint_decidable : forall (l : composite_label IT) (som : composite_state IT * option (message)), {constraint l som} + {~constraint l som})
      := @valid_decidable _ _ _ _ (composite_vlsm_constrained_vdecidable constraint_decidable).

    Definition free_constraint_decidable
               (l : composite_label IT)
               (som : composite_state IT * option (message))
      : {free_constraint l som} + {~free_constraint l som}
      := left I.

    Definition composite_vlsm_free_vdecidable
      : VLSM_vdecidable (composite_vlsm_free i0 IM)
      :=
        composite_vlsm_constrained_vdecidable free_constraint_decidable.

  End composite_vlsm_decidable.
End indexing.

(* Section 2.4.4 Projections into VLSM compositions *)
Section projections.

  Context {message : Type}
          {index : Type}
          {IndEqDec : EqDec index}
          (i0 : index)
          {IT : index -> VLSM_type message}
          {IS : forall i : index, LSM_sig (IT i)}
          (IM : forall n : index, VLSM (IS n))
          (T := composite_type IT)
          (S := composite_sig i0 IS)
          (constraint : @label _ T -> @state _ T * option message -> Prop)
          (X := composite_vlsm_constrained i0 IM constraint)
          .

  Definition composite_vlsm_constrained_projection_sig (i : index) : LSM_sig (IT i)
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
    exists (s : @state _ T),
      s i = si /\ protocol_valid X (existT _ i li) (s, omi)
    .

  Lemma composite_protocol_valid_implies_valid
    (i : index)
    (li : @label _ (IT i))
    (siomi : @state _ (IT i) * option message)
    (Hcomposite : projection_valid i li siomi)
    : @valid _ _ _ (IM i) li siomi
    .
  Proof.
    destruct siomi as [si omi].
    destruct Hcomposite as [s [Hsi [_ [_ Hvalid]]]].
    subst; simpl in *.
    destruct Hvalid as [Hvalid Hconstraint].
    unfold _composite_valid in Hvalid. assumption.
  Qed.

  Definition composite_vlsm_constrained_projection
             (i : index)
    : VLSM (composite_vlsm_constrained_projection_sig i) :=
    {|  transition :=  @transition _ _ _ (IM i)
     ;  valid := projection_valid i
    |}.

  Section fixed_projection.
  
    Context
      (j : index)
      (Proj := composite_vlsm_constrained_projection j)
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
  
    Lemma transition_projection : @transition _ _ (composite_vlsm_constrained_projection_sig j) Proj = @transition _ _ _ (IM j).
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
      - destruct Hv as [sX [Heqs Hv]].
        specialize (protocol_prop_valid_out X (existT (fun n : index => label) j l) sX om Hv)
        ; intro HpsX'.
        simpl in Heqs. rewrite <- Heqs in *. clear Heqs.
        remember
          (@transition _ _ _ X
            (@existT index (fun n : index => @label message (IT n)) j l)
            (@pair (@state message (@composite_type message index IT))
               (option message) sX om))
          as som'.
        destruct som' as [s' om'].
        simpl in Heqsom'.
        rewrite H0 in Heqsom'.
        inversion Heqsom'; subst.
        exists (state_update IT sX j sj).
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
    
    Lemma proj_pre_loaded_incl
      (PreLoaded := pre_loaded_vlsm (IM j))
      : VLSM_incl Proj PreLoaded
      .
    Proof.
      apply (basic_VLSM_incl Proj PreLoaded)
      ; intros; try (assumption || reflexivity).
      - destruct H as [_ [[_s Hpm] _]]. exists _s.
        apply proj_pre_loaded_protocol_prop.
        assumption.
      - apply composite_protocol_valid_implies_valid.
        destruct H as [_ [_ Hv]].
        assumption.
    Qed.
  
  End fixed_projection.

End projections.

Section free_projections.

  Context {message : Type}
          {index : Type}
          {IndEqDec : EqDec index}
          (i0 : index)
          {IT : index -> VLSM_type message}
          {IS : forall i : index, LSM_sig (IT i)}
          (IM : forall n : index, VLSM (IS n))
          (X := composite_vlsm_free i0 IM)
          .

  Definition composite_vlsm_free_projection_sig
             (i : index)
    : LSM_sig (IT i)
    :=
      composite_vlsm_constrained_projection_sig i0 IM free_constraint i.

  Definition composite_vlsm_free_projection
             (i : index)
    : VLSM (composite_vlsm_free_projection_sig i)
    :=
      composite_vlsm_constrained_projection i0 IM free_constraint i.

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
    : VLSM (composite_sig first binary_IS)
    := composite_vlsm_free first binary_IM.

  Definition binary_free_composition_fst
    := composite_vlsm_free_projection first binary_IM  first.

  Definition binary_free_composition_snd
    := composite_vlsm_free_projection first binary_IM  second.

End binary_composition.
