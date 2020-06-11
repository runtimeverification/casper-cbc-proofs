Require Import List.
Import ListNotations.
Require Import Logic.FunctionalExtensionality.

Require Import Coq.Logic.FinFun.

From Casper
     Require Import ListExtras preamble vlsm.

(*
Section 2.4 VLSM composition

Composition of indexed VLSMs.

 *)

Section indexing. 

  Context {message : Type}
          {index : Type}
          {index_listing : list index}
          (finite_index : Listing index_listing)
          `{IndEqDec : EqDec index}
          (i0 : index)
          (IT : index -> VLSM_type message)
          (IS : forall i : index, LSM_sig (IT i)).

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
    

  Definition _indexed_proto_message_prop
             (m : message)
    : Prop
    :=
      exists n : index, @proto_message_prop message (IT n) (IS n) m.

  Lemma _indexed_proto_message_decidable
    : forall m : message, {_indexed_proto_message_prop m} + {~_indexed_proto_message_prop m}.
  Proof.
    intros.
    unfold _indexed_proto_message_prop.
    specialize (Exists_dec (fun n => @proto_message_prop message (IT n) (IS n) m) index_listing); intro Hex_dec.
    assert (Hdec : (forall a : index, {@proto_message_prop _ _ (IS a) m} + {~ @proto_message_prop _ _ (IS a) m}))
      by (intro; apply proto_message_decidable).
    specialize (Hex_dec Hdec).
    destruct Hex_dec as [Hex | Hnex].
    - left. apply Exists_exists in Hex. destruct Hex as [x [_ Hpm]].
      exists x; assumption.
    - right. intro Hex. apply Hnex.  destruct Hex as [x Hpm].
      apply Exists_exists. exists x. split; try assumption.
      destruct finite_index as [_ Hfull]. apply Hfull.
  Qed.

  Definition _indexed_proto_message
    := { m : message | _indexed_proto_message_prop m }.

  Definition _indexed_initial_state_prop
             (s : indexed_state)
    : Prop
    :=
      forall n : index, @initial_state_prop _ (IT n) (IS n) (s n).

  Definition _indexed_initial_state
    := { s : indexed_state | _indexed_initial_state_prop s }.

  Definition _indexed_s0
    : _indexed_initial_state.
    exists (fun (n : index) => proj1_sig (@s0 _ (IT n) (IS n))).
    intro i. destruct s0 as [s Hs]. assumption.
  Defined.

  Definition _indexed_initial_message_prop
             (m : _indexed_proto_message)
    : Prop
    :=
      exists (n : index) (mi : @initial_message _ (IT n) (IS n)), proj1_sig (proj1_sig mi) = proj1_sig m.

  (* An explicit argument for the initial state witness is no longer required: *) 
  Definition _indexed_m0
    : _indexed_proto_message.
    destruct (@m0 _ (IT i0) (IS i0)) as [m Hpm].
    exists m. exists i0. assumption.
  Defined.

  Definition _indexed_l0
    : indexed_label
    := existT _ i0 (@l0 message (IT i0) (IS i0)) .

  Definition indexed_sig
    : LSM_sig indexed_type
    :=
      {|   proto_message_prop := _indexed_proto_message_prop
         ; proto_message_decidable := _indexed_proto_message_decidable
         ; initial_state_prop := _indexed_initial_state_prop
         ; s0 := _indexed_s0
         ; initial_message_prop := _indexed_initial_message_prop
         ; m0 := _indexed_m0
         ; l0 := _indexed_l0 
      |}.
  
  Definition indexed_proto_message_prop := @proto_message_prop message indexed_type indexed_sig.
  Definition indexed_proto_message_decidable := @proto_message_decidable message indexed_type indexed_sig.
  Definition indexed_initial_state_prop := @initial_state_prop message indexed_type indexed_sig.
  Definition indexed_s0 := @s0 message indexed_type indexed_sig.
  Definition indexed_initial_message_prop := @initial_message_prop message indexed_type indexed_sig.
  Definition indexed_m0 := @m0 message indexed_type indexed_sig.
  Definition indexed_l0 := @l0 message indexed_type indexed_sig.
  Definition indexed_proto_message := @proto_message message indexed_type indexed_sig.
  

  Definition lift_proto_messageI
             (n : index)
             (mi : @proto_message _ (IT n) (IS n))
    : indexed_proto_message.
    destruct mi as [m Hm].
    exists m. exists n. assumption.
  Defined.

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

  Definition _indexed_transition
             (IM : forall n : index, VLSM (IS n))
             (l : indexed_label)
             (som : indexed_state * option indexed_proto_message)
    : indexed_state * option indexed_proto_message.
    destruct som as [s om].
    destruct l as [i li].
    destruct om as [[m _]|].
    - destruct (@proto_message_decidable _ (IT i) (IS i) m) as [Hi | _].
      + destruct (transition li (s i, Some (exist _ m Hi))) as [si' om'].
        exact (state_update s i si', option_map (lift_proto_messageI i) om').
      + exact (s, None).
    - destruct (transition li (s i, None)) as [si' om'].
      exact (state_update s i si', option_map (lift_proto_messageI i) om').
  Defined.

  Definition _indexed_valid
             (IM : forall n : index, VLSM (IS n))
             (l : indexed_label)
             (som : indexed_state * option indexed_proto_message)
    : Prop.
    destruct som as [s om].
    destruct l as [i li].
    destruct om as [[m _]|].
    - destruct (@proto_message_decidable _ _ (IS i) m) as [Hi | _].
      + exact (valid li (s i, Some (exist _ m Hi))).
      + exact False.
    - exact (valid li (s i, None)).
  Defined.

  Definition _indexed_valid_decidable
             {IM : forall n : index, VLSM (IS n)}
             (IDM : forall n : index, VLSM_vdecidable (IM n))
             (l : indexed_label)
             (som : indexed_state * option indexed_proto_message)
    : {_indexed_valid IM l som} + {~_indexed_valid IM l som}.
    destruct som as [s om].
    destruct l as [i li]; simpl.
    destruct om as [[m _]|]; simpl.
    - destruct (@proto_message_decidable _ _ (IS i) m) as [Hi | _].
      + apply valid_decidable.
        apply IDM; assumption. 
      + right; intro; contradiction.
    - apply valid_decidable.
      apply IDM; assumption.
  Defined.

  (* Constrained VLSM composition *)

  Definition _indexed_valid_constrained
             (IM : forall n : index, VLSM (IS n))
             (constraint : indexed_label -> indexed_state * option indexed_proto_message -> Prop)
             (l : indexed_label)
             (som : indexed_state * option indexed_proto_message)
    :=
      _indexed_valid IM l som /\ constraint l som.

  Definition indexed_vlsm_constrained
             (IM : forall n : index, VLSM (IS n))
             (constraint : indexed_label -> indexed_state * option (indexed_proto_message) -> Prop)
    : VLSM indexed_sig
    :=
      {|  transition := _indexed_transition IM
          ;   valid := _indexed_valid_constrained IM constraint
      |}.
  
  Definition indexed_transition
    (IM : forall n : index, VLSM (IS n))
    (constraint : indexed_label -> indexed_state * option (indexed_proto_message) -> Prop)
    := @transition _ _ _ (indexed_vlsm_constrained IM constraint).

  Definition indexed_valid
    (IM : forall n : index, VLSM (IS n))
    (constraint : indexed_label -> indexed_state * option (indexed_proto_message) -> Prop)
    := @valid _ _ _ (indexed_vlsm_constrained IM constraint).

  Definition _indexed_valid_constrained_decidable
             {IM : forall n : index, VLSM (IS n)}
             (IDM : forall n : index, VLSM_vdecidable (IM n))
             {constraint : indexed_label -> indexed_state * option (indexed_proto_message) -> Prop}
             (constraint_decidable : forall (l : indexed_label) (som : indexed_state * option (indexed_proto_message)), {constraint l som} + {~constraint l som})
             (l : indexed_label)
             (som : indexed_state * option indexed_proto_message)
    : {indexed_valid IM constraint l som} + {~@indexed_valid  IM constraint l som}.
    intros.
    destruct (constraint_decidable l som) as [Hc | Hnc].
    - destruct (_indexed_valid_decidable IDM l som) as [Hv | Hnv].
      + left. split; try assumption.
      + right. intros [Hv _]. contradiction.
    - right. intros [_ Hc]. contradiction.
  Defined.

  Definition indexed_vlsm_constrained_vdecidable
             {IM : forall n : index, VLSM (IS n)}
             (IDM : forall n : index, VLSM_vdecidable (IM n))
             {constraint : indexed_label -> indexed_state * option (indexed_proto_message) -> Prop}
             (constraint_decidable : forall (l : indexed_label) (som : indexed_state * option (indexed_proto_message)), {constraint l som} + {~constraint l som})
    : VLSM_vdecidable (indexed_vlsm_constrained IM constraint)
    :=
      {|  valid_decidable := _indexed_valid_constrained_decidable IDM constraint_decidable
      |}.
  
  Definition indexed_valid_constrained_decidable
             {IM : forall n : index, VLSM (IS n)}
             (IDM : forall n : index, VLSM_vdecidable (IM n))
             {constraint : indexed_label -> indexed_state * option (indexed_proto_message) -> Prop}
             (constraint_decidable : forall (l : indexed_label) (som : indexed_state * option (indexed_proto_message)), {constraint l som} + {~constraint l som})
    := @valid_decidable _ _ _ _ (indexed_vlsm_constrained_vdecidable IDM constraint_decidable).

  (* Free VLSM composition *)

  Definition free_constraint 
             (l : indexed_label)
             (som : indexed_state * option (indexed_proto_message))
    : Prop
    :=
      True.

  Definition free_constraint_decidable
             (l : indexed_label)
             (som : indexed_state * option (indexed_proto_message))
    : {free_constraint l som} + {~free_constraint l som}
    := left I.

  Definition indexed_vlsm_free
             (IM : forall n : index, VLSM (IS n))
    : VLSM (indexed_sig)
    :=
      indexed_vlsm_constrained IM free_constraint
  .

  Definition indexed_vlsm_free_vdecidable
             {IM : forall n : index, VLSM  (IS n)}
             (IDM : forall n : index, VLSM_vdecidable (IM n))
    : VLSM_vdecidable (indexed_vlsm_free IM)
    :=
      indexed_vlsm_constrained_vdecidable IDM free_constraint_decidable.
End indexing.

(* From indexed_vlsm_projections.v *)
Section projections. 

  Context {message : Type}
          {index : Type}
          {index_listing : list index}
          (finite_index : Listing index_listing)
          `{IndEqDec : EqDec index}
          (i0 : index)
          (IT : index -> VLSM_type message)
          (IS : forall i : index, LSM_sig (IT i))
          (IM : forall n : index, VLSM (IS n))
          (T := indexed_type IT)
          (S := indexed_sig finite_index i0 IT IS)
          (constraint : @label _ T -> @state _ T * option (@proto_message _ _ S) -> Prop)
          (X := indexed_vlsm_constrained finite_index i0 IT IS IM constraint)
          .

  Lemma indexed_valid_message
             {l : @label _ T}
             {s : @state _ T}
             {m  : @proto_message _ _ S}
      : @valid _ _ _  X l (s, Some m)
      -> @proto_message_prop _ _ (IS (projT1 l)) (proj1_sig m)
      .
  Proof.
    intros Hv.
    inversion Hv. unfold indexed_valid in H.
    destruct l. destruct m; simpl in *.
    destruct (@proto_message_decidable message _ (IS x) x0); try assumption.
    inversion H.
  Qed.

  Lemma indexed_transition_output
             {l : @label _ T}
             {s : @state _ T}
             {om  : option (@proto_message _ _ S)}
             {s' : @state _ T}
             {m'  : @proto_message _ _ S}
      : @transition _ _ S X l (s, om) = (s', Some m')
      -> @proto_message_prop _ _ (IS (projT1 l)) (proj1_sig m')
      .
  Proof.
    unfold transition. simpl. destruct l. destruct om.
    - destruct p.
      destruct (proto_message_decidable x0).
      + destruct (transition l (s x, Some (exist proto_message_prop x0 p0))) eqn:Ht.
        destruct o; simpl; intros Heq; inversion Heq.
        destruct p1. simpl. assumption.
      + intros Heq; inversion Heq.
    - destruct (transition l (s x, None)) eqn:Ht.
      destruct o; simpl; intros Heq; inversion Heq.
      destruct p. simpl. assumption.
  Qed.

  Definition indexed_vlsm_constrained_projection_sig (i : index) : LSM_sig (IT i)
    :=
      {|      proto_message_prop := @proto_message_prop _ _ (IS i)
          ;   proto_message_decidable := @proto_message_decidable _ _ (IS i)
          ;   initial_state_prop := @initial_state_prop _ _ (IS i)
          ;   initial_message_prop := fun pmi => exists xm : (@protocol_message _ _ _ X), proj1_sig (proj1_sig xm) = proj1_sig pmi
          ;   s0 := @s0 _ _ (IS i)
          ;   m0 := @m0 _ _ (IS i)
          ;   l0 := @l0 _ _ (IS i)
      |}.


  Definition indexed_vlsm_constrained_projection
             (i : index)
    : VLSM (indexed_vlsm_constrained_projection_sig i).
    unfold indexed_vlsm_constrained_projection_sig; simpl.
    split; simpl; unfold proto_message; simpl.
    - exact (@transition _ _ _ (IM i)).
    - intros l som. destruct (@transition _ _ _ (IM i) l som) as  [si' omi']. 
      exact
        (   @valid _ _ _ (IM i) l som
            /\  exists s' : @protocol_state _ _ _ X, exists om' : option (@protocol_message _ _ _ X),
              (  (proj1_sig s') i = si'
                 /\ option_map (@proj1_sig _ _) (option_map (@proj1_sig _ _) om') = option_map (@proj1_sig _ _) omi' 
              )
        ).
  Defined.

  Section fixed_projection.

    Context
      (j : index)
      (Proj := indexed_vlsm_constrained_projection j)
      .

    Lemma transition_projection : @transition _ _ (indexed_vlsm_constrained_projection_sig j) Proj = @transition _ _ _ (IM j).
    Proof. reflexivity.  Qed.

    Lemma proto_message_projection : @proto_message _ _ (indexed_vlsm_constrained_projection_sig j) = @proto_message _ _ (IS j).
    Proof. reflexivity. Qed.

    Lemma proto_message_prop_projection : @proto_message_prop _ _ (indexed_vlsm_constrained_projection_sig j) = @proto_message_prop _ _ (IS j).
    Proof. reflexivity. Qed.


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
        constraint (existT _ j lj)
        ( proj1_sig s
        , option_map (lift_proto_messageI _ _ _ IS j) (option_map (@proj1_sig proto_message _) om)
        )
      .

    Fixpoint finite_trace_projection_list
      (trx : list (@in_state_out _ _ S))
      : list (@in_state_out _ _ (sign Proj))
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
          match input item with
          | None =>
            match output item with
            | None =>
              @Build_in_state_out _ _ (sign Proj) lj None (s j) None :: tail
            | Some (exist _ out _) =>
              match @proto_message_decidable _ _ (sign Proj) out with
              | left Pout =>
                @Build_in_state_out _ _ (sign Proj) lj None (s j) (Some (exist _ out Pout)) :: tail
              | _ => tail
              end
            end
          | Some (exist _ inp _) =>
            match @proto_message_decidable _ _ (sign Proj) inp with
            | left Pinp =>
              let inpj := Some (exist _ inp Pinp) in
              match output item with
              | None =>
                @Build_in_state_out _ _ (sign Proj) lj inpj (s j) None :: tail
              | Some (exist _ out _) =>
                match @proto_message_decidable _ _ (sign Proj) out with
                | left Pout =>
                  @Build_in_state_out _ _ (sign Proj) lj inpj (s j) (Some (exist _ out Pout)) :: tail
                | _ => tail
                end
              end
            | _ => tail
            end
          end
        | _ => tail
        end
      end.

    Lemma finite_ptrace_projection
      (s : @state _ T)
      (Psj : protocol_state_prop Proj (s j))
      (trx : list (@in_state_out _ _ S))
      (Htr : finite_ptrace_from X s trx)
       : finite_ptrace_from Proj (s j) (finite_trace_projection_list trx).
    Proof.
      assert
        ( HpairNone: forall s0,
          (@pair (@state message (IT j))
             (option (@sig message (fun m : message => @proto_message_prop message (IT j) (IS j) m))) s0
             (@None (@sig message (fun m : message => @proto_message_prop message (IT j) (IS j) m))))     
           =
          (@pair (@state message (IT j)) (option (@proto_message message (IT j) (IS j))) s0
             (@None (@proto_message message (IT j) (IS j))))
        ) by reflexivity.
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
          assert
            (Heqlx :
              (@eq_rect_r index j (fun n : index => @label message (IT n)) lx j (@eq_refl index j))
              = lx
            ) by reflexivity.
          destruct iom as [[inp Pimp]|].
          * unfold transition in  Ht. simpl in Ht. simpl in Hv.
            destruct (proto_message_decidable inp); try inversion Hv.
            assert (Hpair :
                     (@pair (@state message (IT j))
                        (option (@sig message (fun m : message => @proto_message_prop message (IT j) (IS j) m)))
                        (s' j)
                        (@Some (@sig message (@proto_message_prop message (IT j) (IS j)))
                           (@exist message (@proto_message_prop message (IT j) (IS j)) inp p)))
                    =
                     (@pair (@state message (IT j))
                        (option (@sig message (@proto_message_prop message (IT j) (IS j))))
                        (s' j)
                        (@Some (@sig message (@proto_message_prop message (IT j) (IS j)))
                           (@exist message (@proto_message_prop message (IT j) (IS j)) inp p)))
                    ) by reflexivity.
            destruct (transition lx (s' j, Some (exist proto_message_prop inp p))) eqn:Hteq.
            assert (Hini : @initial_message_prop _ _ (sign Proj) (exist proto_message_prop inp p))
              by (exists (exist _ (exist (fun m : message => proto_message_prop m) inp Pimp) Piom); reflexivity).
            remember (exist _ (exist proto_message_prop inp p) Hini) as inim.
            assert (Hinip : @protocol_prop _ _ _ Proj ((@proj1_sig (@state message (IT j)) _ (@vlsm.s0 message _ (IS j))), Some (proj1_sig inim)))
              by (apply (@protocol_initial_message _ _ _ Proj inim)).
            assert
              (Hiniproj :
                (@proj1_sig (@sig message (@proto_message_prop message _ (IS j)))
                   (@initial_message_prop message
                      _ (@sign message _ (indexed_vlsm_constrained_projection_sig j) Proj))
                   (@exist (@sig message (@proto_message_prop message _ (IS j)))
                      (@initial_message_prop message
                         _ (@sign message _ (indexed_vlsm_constrained_projection_sig j)
                            Proj))
                      (@exist message (@proto_message_prop message _ (IS j)) inp p)
                      Hini))
                =
               (@exist message (@proto_message_prop message _ (IS j)) inp p)
              ) by reflexivity.
            specialize (@protocol_generated _ _ _ Proj lx (s' j)); intro Generated.
            destruct Psj as [_om Psj]. specialize (Generated _om Psj).
            specialize (Generated  (@proj1_sig (@state message (IT j)) _ (@vlsm.s0 message _ (IS j))) (Some (proj1_sig inim)) Hinip).
            rewrite Heqinim in Generated.
            rewrite Hiniproj in Generated.
            { destruct oom as [[out Pout]|]; inversion Ht.
            - assert (Hpm : protocol_message_prop X (exist _ out Pout)) by (exists s; assumption).
              destruct o; inversion H1. destruct p0; inversion H2. subst out.
              destruct (proto_message_decidable x); try contradiction.
              constructor.
              + rewrite H0. apply IHHtr. rewrite <- H0. rewrite state_update_eq.
                exists
                  (@Some (@proto_message message _ (IS j))
                     (@exist message (fun m : message => @proto_message_prop message _ (IS j) m) x p0)).
                unfold proto_message at 1. simpl.
                unfold proto_message at 2 in Hteq; simpl in Hteq. 
                rewrite <- Hteq.
                apply Generated.
                unfold valid. simpl. 
                assert
                  (Htt : (@transition message _ _ (IM j) lx
                           (@pair (@state message (IT j))
                              (option (@proto_message message _ (indexed_vlsm_constrained_projection_sig j)))
                              (s' j)
                              (@Some (@sig message (@proto_message_prop message _ (IS j)))
                                 (@exist message (@proto_message_prop message _ (IS j)) inp p))))
                        =
                        (@transition message _ _ (IM j) lx
                          (@pair (@state message (IT j))
                             (option (@sig message (@proto_message_prop _ _ (IS j)))) 
                             (s' j)
                             (@Some (@sig message (@proto_message_prop _ _ (IS j)))
                                (@exist message (@proto_message_prop _ _ (IS j)) inp p))))
                ) by reflexivity.
                rewrite Htt. rewrite Hteq.
                split; try assumption.
                exists (exist _ s Hps).
                exists (Some (exist _ (exist proto_message_prop x Pout) Hpm)).
                simpl. split; try reflexivity. subst.  apply state_update_eq.
              + repeat split; try assumption.
                * exists _om. assumption.
                * exists (@proj1_sig (@state message (IT j)) _ (@vlsm.s0 message _ (IS j))).
                  subst. simpl in Hinip. assumption.
                * rewrite Heqlx.
                  simpl.
                  assert
                    (Hteq' :
                       @transition _ _ _ (IM j) lx
                          (@pair (@state _ (IT j))
                             (option (@proto_message _ _ (sign Proj))) 
                             (s' j)
                             (@Some (@sig message (@proto_message_prop _ _ (IS j)))
                                (@exist message (@proto_message_prop _ _ (IS j)) inp p)))                      
                     =
                      (@pair (@state _ (IT j)) (option (@proto_message _ _ (IS j))) s0
                        (@Some (@proto_message _ _ (IS j))
                           (@exist message (fun m : message => @proto_message_prop _ _ (IS j) m) x p0)))
                    ) by (rewrite <- Hteq; reflexivity).
                  rewrite Hteq'. split; try assumption.
                  exists (exist _ s Hps).
                  exists (Some (exist _ (exist proto_message_prop x Pout) Hpm)).
                  simpl. split; try reflexivity. subst.  apply state_update_eq.
                * rewrite Heqlx. unfold Proj. simpl.
                  unfold proto_message. simpl.
                  unfold proto_message in Hteq; simpl in Hteq.
                  rewrite Hpair.
                  rewrite Hteq. subst. apply injective_projections; simpl; try rewrite state_update_eq; try reflexivity.
                  apply f_equal. apply exist_eq. reflexivity.
            - rewrite Heqlx. rewrite H0. 
              apply finite_ptrace_extend; try assumption.
              + apply IHHtr. exists None. destruct o; try inversion H1.
                rewrite <- H0.
                rewrite state_update_eq.
                unfold proto_message; simpl.
                unfold proto_message in Hteq at 2. unfold proto_message in Hteq at 2.
                simpl in Hteq.
                rewrite <- Hteq.
                apply Generated. unfold valid; simpl.
                unfold proto_message at 1; simpl.
                rewrite Hpair.
                rewrite Hteq. 
                split; try assumption.
                exists (exist _ s Hps).  exists None.
                split; try reflexivity; simpl.
                subst. apply state_update_eq.
              + repeat split.
                * exists _om. assumption.
                * exists (@proj1_sig (@state message (IT j)) _ (@vlsm.s0 message _ (IS j))).
                  subst. simpl in Hinip. assumption.
                * unfold proto_message. simpl. rewrite Hpair.
                  rewrite Hteq. split; try assumption.
                  exists (exist _ s Hps). 
                  exists None. destruct o; inversion H1.
                  simpl. split; try reflexivity. subst.  apply state_update_eq.
                *  unfold proto_message. simpl. rewrite Hpair.
                  rewrite Hteq.
                  destruct o; inversion H1.
                  subst. apply injective_projections; simpl; try rewrite state_update_eq; try reflexivity.
            }
          *
            unfold transition in  Ht. simpl in Ht.
            destruct (transition lx (s' j, None)) eqn:Hteq.
            specialize (@protocol_generated _ _ _ Proj lx (s' j)); intro Generated.
            destruct Psj as [_om Psj]. specialize (Generated _om Psj).
            specialize (Generated  (@proj1_sig (@state message (IT j)) _ (@vlsm.s0 message _ (IS j))) None).
            specialize (Generated  (protocol_initial_state Proj vlsm.s0)).
            { destruct oom as [[out Pout]|]; inversion Ht.
            - assert (Hpm : protocol_message_prop X (exist _ out Pout)) by (exists s; assumption).
              destruct o; inversion H1. destruct p; inversion H2. subst out.
              destruct (proto_message_decidable x); try contradiction.
              assert
                ( HpairSome: forall s0,
                  (@pair (@state message (IT j))
                     (option (@sig message (fun m : message => @proto_message_prop message (IT j) (IS j) m))) s0
                     (@Some (@sig message (fun m : message => @proto_message_prop message (IT j) (IS j) m))
                        (@exist message (fun m : message => @proto_message_prop message (IT j) (IS j) m) x p)))     
                   =
                  (@pair (@state message (IT j)) (option (@proto_message message (IT j) (IS j))) s0
                     (@Some (@proto_message message (IT j) (IS j))
                        (@exist message (fun m : message => @proto_message_prop message (IT j) (IS j) m) x
                           p)))
                ) by reflexivity.
              constructor.
              + rewrite H0. apply IHHtr. rewrite <- H0. rewrite state_update_eq.
                exists
                 (@Some (@proto_message message _ (IS j))
                   (@exist message (fun m : message => @proto_message_prop message _ (IS j) m) x p)).
                unfold proto_message. simpl. rewrite HpairSome. rewrite <- Hteq.
                apply Generated.
                unfold valid. simpl.
                unfold proto_message. simpl. rewrite HpairNone. rewrite Hteq.
                split; try assumption.
                exists (exist _ s Hps).
                exists (Some (exist _ (exist proto_message_prop x Pout) Hpm)).
                simpl. split; try reflexivity. subst.  apply state_update_eq.
              + repeat split.
                * exists _om. assumption.
                * exists (@proj1_sig (@state message (IT j)) _ (@vlsm.s0 message _ (IS j))).
                  subst. apply (protocol_initial_state Proj vlsm.s0).
                * rewrite Heqlx. 
                  simpl.
                  unfold proto_message. simpl. rewrite HpairNone. rewrite Hteq.
                  split; try assumption.
                  exists (exist _ s Hps). 
                  exists (Some (exist _ (exist proto_message_prop x Pout) Hpm)).
                  simpl. split; try reflexivity. subst.  apply state_update_eq.
              * rewrite Heqlx.
                unfold proto_message. simpl. rewrite HpairNone. rewrite Hteq.
                subst. apply injective_projections; simpl; try rewrite state_update_eq; try reflexivity.
                apply f_equal. apply exist_eq. reflexivity.
            - rewrite Heqlx. rewrite H0. 
              apply finite_ptrace_extend.
              + apply IHHtr. exists None. destruct o; try inversion H1.
                unfold proto_message. simpl. rewrite HpairNone.
                rewrite <- H0. rewrite state_update_eq.   
                rewrite <- Hteq.
                apply Generated. unfold valid; simpl. 
                unfold proto_message. simpl. rewrite HpairNone.
                rewrite Hteq.
                split; try assumption.
                exists (exist _ s Hps).  exists None.
                split; try reflexivity; simpl.
                subst.  apply state_update_eq.
              + repeat split.
                * exists _om. assumption.
                * exists (@proj1_sig (@state message (IT j)) _ (@vlsm.s0 message _ (IS j))).
                  subst. apply (protocol_initial_state Proj vlsm.s0).
                * simpl.
                  unfold proto_message. simpl. rewrite HpairNone.
                  rewrite Hteq.
                  split; try assumption.
                  exists (exist _ s Hps). 
                  exists None. destruct o; inversion H1.
                  simpl. split; try reflexivity. subst.  apply state_update_eq.
                * unfold proto_message. simpl. rewrite HpairNone.
                  rewrite Hteq.
                  subst. apply injective_projections; simpl; try rewrite state_update_eq; try reflexivity.
                  destruct o; inversion H1. reflexivity.
            }
        + assert (Heq : s j = s' j); try (rewrite Heq in IHHtr; apply IHHtr; assumption).
          unfold transition in  Ht. simpl in Ht. simpl in Hv.
          destruct iom as [[im Pim]|].
          * destruct (proto_message_decidable im) as [Pimj | _]
            ; try inversion Hv.
            destruct (transition lx (s' x, Some (exist proto_message_prop im Pimj))).
            inversion Ht. rewrite state_update_neq; try reflexivity; assumption.
          * destruct (transition lx (s' x, None)).
            inversion Ht. rewrite state_update_neq; try reflexivity; assumption.
    Qed.

  End fixed_projection.

End projections.


Section free_projections. 


  Context {message : Type}
          {index : Type}
          `{IndEqDec : EqDec index}
          (i0 : index)
          {index_listing : list index}
          (finite_index : Listing index_listing)
          (IT : index -> VLSM_type message)
          (IS : forall i : index, LSM_sig (IT i))
          (IM : forall n : index, VLSM (IS n))
          .

  Definition indexed_vlsm_free_projection_sig
             (i : index)
    : LSM_sig (IT i)
    :=
      indexed_vlsm_constrained_projection_sig finite_index i0 _ _ IM (free_constraint _ _ _ IS) i.

  Definition indexed_vlsm_free_projection
             (i : index)
    : VLSM (indexed_vlsm_free_projection_sig i)
    :=
      indexed_vlsm_constrained_projection finite_index i0 _ _ IM (free_constraint _ _ _ IS) i.
End free_projections.
