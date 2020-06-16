Require Import List.
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

  Definition composite_protocol_valid
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
    (Hcomposite : composite_protocol_valid i li siomi)
    : @valid _ _ _ (IM i) li siomi
    .
  Proof.
    unfold composite_protocol_valid in Hcomposite.
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
     ;  valid := composite_protocol_valid i
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
