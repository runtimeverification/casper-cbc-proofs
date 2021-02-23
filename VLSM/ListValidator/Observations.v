Require Import Bool List ListSet Reals FinFun RelationClasses Relations Relations_1 Sorting.
Require Import Lia.
Import ListNotations.
From CasperCBC
Require Import
  Lib.Preamble
  Lib.ListExtras
  Lib.ListSetExtras
  Lib.SortedLists
  VLSM.Common
  VLSM.Composition
  VLSM.Equivocation
  VLSM.ListValidator.ListValidator
  VLSM.ListValidator.Equivocation
  VLSM.ObservableEquivocation
  CBC.Common
  CBC.Equivocation.

Section Observations.

Context
  {index : Type}
  {index_self : index}
  {index_listing : list index}
  {Hfinite : Listing index_listing}
  {idec : EqDecision index}
  (est : state -> bool -> Prop)
  (X := @VLSM_list _ index_self index_listing idec est)
  (preX := pre_loaded_with_all_messages_vlsm X)
  (Xtype := type preX)
  {mdec : EqDecision (@message index index_listing)}
  {Mindex : Measurable index}
  {Rindex : ReachableThreshold index}.
  
  Local Notation get_history' := (@get_history index index_listing idec).
  Local Notation last_sent' := (@last_sent index index_self index_listing idec).
  Local Notation unfold_history_cons' := (@unfold_history_cons index index_listing Hfinite).
  
  (** Observations will consist of an observation type, an index and a state.
     When talking about "raw" observations, we refer to the underlying states.
     Raw observations regarding a certain validator <<target> 
     are extracted by traversing the state recursively and collecting
     all projections onto <<target>>, eliminating <<Bottom>> values at the end *)
  
  Fixpoint get_raw_observations' (target : index) (d : nat) (s : state) : set state :=
    match s with
    | Bottom => []
    | _ => match d with
    | 0 => set_remove decide_eq Bottom [project s target]
    | S n => let children := List.map (@project index index_listing _ s) index_listing in
             let children_res := List.map (get_raw_observations' target n) children in
             set_remove decide_eq Bottom
             (set_union decide_eq (List.fold_right (set_union decide_eq) [] children_res) [project s target])
         end
    end.
      
  Definition get_raw_observations (s : state) (target : index) : set state :=
    get_raw_observations' target (depth s) s.
      
  Remark raw_observations_consensus 
    (s : state)
    (b : bool)
    (target : index) :
    get_raw_observations s target = get_raw_observations (update_consensus s b) target.
  Proof.
    unfold get_raw_observations.
    assert (depth s = depth (update_consensus s b)) by (destruct s;intuition). 
    rewrite <- H.
    unfold get_raw_observations'.
    destruct (depth s); destruct s; intuition.
  Qed.
  
  (** It is sufficient to call [get_raw_observations'] with depth 
     to <<(depth s)>> *)
    
  Lemma get_observations_depth_redundancy
      (target : index)
      (d : nat)
      (s : state)
      (Hineq : d >= depth s) :
      get_raw_observations' target d s = get_raw_observations' target (depth s) s.
   Proof.
    remember (depth s) as dpth.
    generalize dependent s.
    generalize dependent d.
    induction dpth using (well_founded_induction lt_wf).
    intros.
    unfold get_raw_observations' at 1.
    destruct s.
    - unfold depth in Heqdpth.
      rewrite Heqdpth.
      destruct d.
      + reflexivity.
      + simpl in *.
        reflexivity.
     - unfold get_raw_observations'.
       destruct dpth eqn : eq_dpth.
       + destruct d eqn: eq_d.
         * reflexivity.
         * symmetry in Heqdpth.
           apply depth_zero_bottom in Heqdpth.
           discriminate Heqdpth.
       + destruct d.
         lia.
         simpl. 
         f_equal. f_equal. f_equal.
         apply map_ext_in.
         intros.
         rewrite in_map_iff in H0.
         destruct H0 as [j [Heq Hin]].
         assert (depth a < S n). {
           rewrite Heqdpth.
           specialize (@depth_parent_child index index_listing Hfinite decide_eq is b j).
           intros.
           unfold project in Heq.
           replace (@project_indexed index index_listing _ index_listing is j)
           with a in H0.
           lia.
         }

        assert (d >= depth a) by lia.

         assert (get_raw_observations' target (depth a) a = get_raw_observations' target n a). {
          symmetry.
          apply H; intuition lia.
         }

         specialize (H (depth a) H0 d H1 a eq_refl).
         rewrite H2 in H.
         intuition.
   Qed.
   
  Lemma get_observations_nodup
      (target : index)
      (s : state) :
      (NoDup (get_raw_observations s target)).
    Proof.
      unfold get_raw_observations.
      remember (depth s) as d.
      generalize dependent s.
       induction d using (well_founded_induction lt_wf).
       unfold get_raw_observations'.
       destruct d.
       - intros.
          simpl.
         destruct (project s target).
         + rewrite decide_True; auto.
           symmetry in Heqd.
           apply depth_zero_bottom in Heqd.
           rewrite Heqd.
           apply NoDup_nil.
         + rewrite decide_False by congruence.
           symmetry in Heqd.
           apply depth_zero_bottom in Heqd.
           rewrite Heqd.
           apply NoDup_nil.
       - intros.
         simpl.
         destruct s.
         simpl in Heqd. discriminate Heqd.
         apply set_remove_nodup.
         apply set_add_nodup.
         specialize (@set_union_iterated_nodup (@state index index_listing) decide_eq).
         intros.
         specialize (H0 (map
        ((fix get_observations (target0 : index) (d0 : nat) (s : state) {struct d0} :
              set state :=
            match s with
            | Bottom => []
            | Something _ _ =>
                match d0 with
                | 0 =>
                    if decide (Bottom = (project s target0))
                    then []
                    else project s target0 :: empty_set state
                | S n =>
                    set_remove decide_eq Bottom
                      (set_add decide_eq (project s target0)
                         (fold_right (set_union decide_eq) []
                            (map (get_observations target0 n) (map (project s) index_listing))))
                end
            end) target d) (map (project (Something b is)) index_listing))).
        apply H0.
        intros.
        rewrite in_map_iff in H1.
        destruct H1 as [x [Hleft Hright]].
        assert (depth x < S d). {
          rewrite Heqd.
          apply in_map_iff in Hright.
          destruct Hright as [i [Hi _]].
          rewrite <- Hi.
          specialize (@depth_parent_child index index_listing Hfinite decide_eq is b i).
          intros.
          unfold project.
          intuition.
        }
        rewrite <- Hleft.
        specialize H.
        rewrite get_observations_depth_redundancy.
        specialize (H (depth x) H1 x eq_refl).
        assumption.
        lia.
 Qed.

  Lemma no_bottom_in_observations
    (s s': state)
    (target : index)
    (Hins' : In s' (get_raw_observations s target)) :
    s' <> Bottom.
  Proof.
   unfold get_raw_observations in Hins'.
   unfold get_raw_observations' in Hins'.
   destruct s.
   - simpl in *.
     intuition.
   - simpl in *.
     destruct (depth (Something b is)) eqn : eq_d'.
     + apply depth_zero_bottom in eq_d'.
       discriminate eq_d'.
     + simpl in *.
       apply set_remove_2 in Hins'.
       assumption.
       clear Hins'.
       apply set_add_nodup.
       apply (set_union_iterated_nodup).
       intros.
       rewrite in_map_iff in H.
       destruct H as [child [Heq_child Hin_child]].
       rewrite in_map_iff in Hin_child.
       destruct Hin_child as [i [Heq_project _]].
       rewrite <- Heq_child.
       specialize (get_observations_nodup target child).
       intros.
       rewrite get_observations_depth_redundancy.
       apply H.
       specialize (@depth_parent_child index index_listing Hfinite idec is b i) as Hparent_child.
       rewrite eq_d' in Hparent_child.
       rewrite <- Heq_project.
       unfold project.
       lia.
  Qed.
  
  (** Some useful shortcuts for relating observations of states and their projections. *)
  
  Lemma unfold_raw_observations
    (s s': state)
    (Hnb : s <> Bottom)
    (target : index) :
    In s' (get_raw_observations s target) ->
    (project s target = s') \/
    (exists (i : index), (In s' (get_raw_observations (project s i) target))).
  Proof.
      - intros.
        unfold get_raw_observations in H.
        destruct s.
        simpl in *.
        exfalso.
        assumption.
        destruct (depth (Something b is)) eqn : eq_d.
        apply depth_zero_bottom in eq_d.
        discriminate eq_d.
        apply set_remove_1 in H.
        apply set_union_elim in H.
        destruct H.
        + apply set_union_in_iterated in H.
          rewrite Exists_exists in H.
          destruct H as [child_res [Heq_child_res Hin_child_res]].
          rewrite in_map_iff in Heq_child_res.
          destruct Heq_child_res as [child [Heq_child Hin_child]].
          rewrite in_map_iff in Hin_child.
          destruct Hin_child as [i [Hproject Hini]].
          right.
          exists i.
          rewrite get_observations_depth_redundancy in Heq_child.
          rewrite <- Heq_child in Hin_child_res.
          rewrite <- Hproject in Hin_child_res.
          assumption.
          specialize (@depth_parent_child index index_listing Hfinite idec is b i).
          intros Hdpc.
          rewrite <- Hproject.
          unfold project.
          lia.
        + simpl in H.
          left.
          intuition.
   Qed.
   
     Lemma refold_raw_observations1
      (s s': state)
      (Hnb : s <> Bottom /\ s' <> Bottom)
      (target : index) :
      (project s target = s') ->
      In s' (get_raw_observations s target).
    Proof.
      - intros.
        destruct H.
        unfold get_raw_observations.
        destruct s.
        intuition.
        destruct (depth (Something b is)) eqn : eq_d.
        apply depth_zero_bottom in eq_d.
        discriminate eq_d.
        apply set_remove_3.
        apply set_union_intro.
        right.
        simpl.
        intuition.
        intuition.
     Qed.
     
     Lemma refold_raw_observations2
      (s s': state)
      (Hnb : s <> Bottom)
      (target : index) :
      (exists (i : index), (In s' (get_raw_observations (project s i) target))) ->
      In s' (get_raw_observations s target).
     Proof.
        intros.
        unfold get_raw_observations.
        destruct s.
        intuition.
        destruct (depth (Something b is)) eqn : eq_d.
        apply depth_zero_bottom in eq_d.
        discriminate eq_d.
        apply set_remove_3.
        apply set_union_intro.
        left.
        apply set_union_in_iterated.
        rewrite Exists_exists.
        destruct H as [i Hin_i].
        exists (get_raw_observations (project (Something b is) i) target).
        split.
        rewrite in_map_iff.
        exists (project (Something b is) i).
        split.
        rewrite get_observations_depth_redundancy.
        unfold get_raw_observations'.
        reflexivity.
        specialize (@depth_parent_child index index_listing Hfinite idec is b i) as Hdpc.
        unfold project.
        lia.
        rewrite in_map_iff.
        exists i.
        split.
        reflexivity.
        apply ((proj2 Hfinite) i).
        intuition.
        destruct H as [i Hini].
        apply no_bottom_in_observations in Hini.
        intuition.
    Qed.
    
    Remark raw_observations_in_project
      (s : state)
      (Hsnb : s <> Bottom)
      (target i : index)
      : incl (get_raw_observations (project s i) target) (get_raw_observations s target).
    Proof.
      unfold incl. intros e H.
      apply refold_raw_observations2.
      intuition.
      exists i.
      intuition.
    Qed.
    
    Remark something_in_obs_nb 
      (s s' : state)
      (i : index)
      (Hin : In s' (get_raw_observations s i)) :
      s <> Bottom.
    Proof.
      destruct s.
      - simpl in Hin. intuition.
      - congruence.
    Qed.
    
    Lemma cross_observations
      (s s1 s2: state)
      (i j : index)
      (Hin1 : In s1 (get_raw_observations s i))
      (Hin2 : In s2 (get_raw_observations s1 j)) :
      In s2 (get_raw_observations s j).
    Proof.
      remember (depth s) as dpth.
      generalize dependent s.
      generalize dependent s1.
      generalize dependent s2.
      induction dpth using (well_founded_induction lt_wf).
      intros.
      assert (Hsnb : s <> Bottom). {
        apply something_in_obs_nb in Hin1.
        intuition.
      }
      apply unfold_raw_observations in Hin1.
      2 : intuition.

      destruct Hin1 as [Hin1 | Hin1].
      - rewrite <- Hin1 in Hin2.
        apply raw_observations_in_project in Hin2.
        all : intuition.
      - destruct Hin1 as [k Hink].
        specialize (H (depth (project s k))) as Hproj.
        spec Hproj. {
          unfold project.
          rewrite Heqdpth.
          destruct s; [intuition|].
          apply (@depth_parent_child index index_listing).
          intuition.
        }
        
        specialize (Hproj s2 s1 Hin2 (project s k) Hink eq_refl).
        apply raw_observations_in_project in Hproj.
        intuition.
        intuition.
    Qed.
    
    (** The simplified observation model (or event) has two types of observations:
       - Message observations (we do not distinguish between Sent and Received *
       - State observations (in practice, these will be observations of the 
         current state of a certain validator) *)
    
    Inductive simp_lv_event_type : Type :=
    | State'
    | Message'.
    
    Global Instance simp_event_type_eq_dec : EqDecision simp_lv_event_type.
      solve_decision.
    Defined.
    
    Record simp_lv_event : Type := SimpObs {
      get_simp_event_type : simp_lv_event_type;
      get_simp_event_subject : index;
      get_simp_event_state : (@state index index_listing);
    }.
    
    Global Instance simp_event_eq_dec : EqDecision simp_lv_event.
      solve_decision.
    Defined. 
    
    Definition simp_lv_event_comp_eq 
      (e : simp_lv_event) :
      e = SimpObs (get_simp_event_type e) (get_simp_event_subject e) (get_simp_event_state e).
    Proof.
      destruct e.
      simpl.
      reflexivity.
    Qed.
    
    (** Comparing two events defaults to comparing their underlying states
       using the [state_lt'] relation defined in [Equivocation.v], except
       for the case in which the lhs is a state observation and the
       rhs is a message observation, which returns False. This is done because
       in practice the only way the current state of a validator compares less
       than one of its messages is that said message is an equivocation. *) 
    
    Definition simp_lv_event_lt (e1 e2 : simp_lv_event) : Prop :=
    match e1, e2 with
      SimpObs type1 subject1 state1, SimpObs type2 subject2 state2 =>
        match decide_eq subject1 subject2 with
        | right _ => False
        | _ => match type1, type2 with
               | State', Message' => False
               | _, _ => state_lt' subject1 state1 state2
               end  
        end
    end.
    
    Lemma simp_lv_event_lt_dec : RelDecision simp_lv_event_lt.
    Proof.
      unfold RelDecision. intros.
      unfold Decision.
      unfold simp_lv_event_lt.
      destruct x as [type1 subject1 state1]; destruct y as [type2 subject2 state2].
      destruct (decide (subject1 = subject2)).
      - destruct type1 eqn : eq1; destruct type2 eqn : eq2.
        + exact (state_lt'_dec subject1 state1 state2).
        + right; auto.
        + exact (state_lt'_dec subject1 state1 state2). 
        + exact (state_lt'_dec subject1 state1 state2).
      - right. auto.
    Qed.
    
    (** State observations concerning target can only be provided by <<target>> itself *)
      
    Definition simp_lv_state_observations (s : state) (target : index) : set simp_lv_event :=
      match decide_eq target index_self with
      | left _ => [SimpObs State' index_self s]
      | right _ => []
      end.
    
    (** Message observations consist simply of all the raw observations in the state, tagged
       with the appropriate type and subject *)
    
    Definition simp_lv_message_observations (s : state) (target : index) : set simp_lv_event :=
      List.map (SimpObs Message' target) (get_raw_observations s target).
    
    Definition simp_lv_observations (s : state) (target : index) : set simp_lv_event :=
      set_union decide_eq (simp_lv_message_observations s target) (simp_lv_state_observations s target).
    
    Remark cons_clean_message_obs 
      (s : state)
      (target : index)
      (b : bool) : 
      simp_lv_message_observations s target = simp_lv_message_observations (update_consensus s b) target.
    Proof.
      unfold simp_lv_message_observations.
      rewrite raw_observations_consensus with (b := b).
      intuition.
    Qed.
    
    (** A variety of shortcuts. *)
    
    Remark in_simp_lv_message_observations
      (s : state)
      (target : index)
      (e : simp_lv_event)
      (Hin : In e (simp_lv_message_observations s target)) :
      get_simp_event_type e = Message' /\ get_simp_event_subject e = target.
    Proof.
      unfold simp_lv_message_observations in *.
      apply in_map_iff in Hin.
      destruct Hin as [x [Heqx Hinx]].
      rewrite <- Heqx; intuition.
    Qed.
    
    Remark in_simp_lv_state_observations
      (s : state)
      (target : index)
      (e : simp_lv_event)
      (Hin : In e (simp_lv_state_observations s target)) :
      get_simp_event_type e = State' /\ get_simp_event_subject e = target.
    Proof.
      unfold simp_lv_state_observations in *.
      destruct (decide (target = index_self)).
      - simpl in Hin.
        destruct Hin.
        rewrite <- H.
        all : intuition.
      - intuition.
    Qed.
    
    Remark in_simp_lv_message_observations'
      (s : state)
      (target : index)
      (e : simp_lv_event)
      (Hin : In e (simp_lv_message_observations s target)) :
      In e (simp_lv_observations s target).
    Proof.
      unfold simp_lv_observations.
      apply set_union_iff.
      left. intuition.
    Qed.
    
    Remark in_simp_lv_state_observations'
      (s : state)
      (target : index)
      (e : simp_lv_event)
      (Hin : In e (simp_lv_state_observations s target)) :
      In e (simp_lv_observations s target).
    Proof.
      unfold simp_lv_observations.
      apply set_union_iff.
      right. intuition.
    Qed.
    
    Remark in_simp_lv_observations
      (s : state)
      (target : index)
      (e : simp_lv_event)
      (Hin : In e (simp_lv_observations s target)) :
      get_simp_event_subject e = target.
    Proof.
      unfold simp_lv_observations in Hin.
      apply set_union_iff in Hin.
      destruct Hin.
      - apply in_simp_lv_message_observations in H. intuition.
      - apply in_simp_lv_state_observations in H. intuition.
    Qed.
       
   Remark in_and_message
    (s : state)
    (target : index)
    (e : simp_lv_event)
    (Hin : In e (simp_lv_observations s target))
    (Hm : get_simp_event_type e = Message') :
    In e (simp_lv_message_observations s target).
  Proof.
    unfold simp_lv_observations in Hin.
    apply set_union_iff in Hin.
    destruct Hin.
    - intuition.
    - apply in_simp_lv_state_observations in H.
      destruct H as [H _].
      congruence. 
  Qed.
  
  Remark in_and_state
    (s : state)
    (target : index)
    (e : simp_lv_event)
    (Hin : In e (simp_lv_observations s target))
    (Hm : get_simp_event_type e = State') :
    In e (simp_lv_state_observations s target).
  Proof.
    unfold simp_lv_observations in Hin.
    apply set_union_iff in Hin.
    destruct Hin.
    - apply in_simp_lv_message_observations in H.
      destruct H as [H _].
      congruence.
    - intuition. 
  Qed.
    
    Remark simp_lv_observations_other 
      (s : state)
      (target : index)
      (Hdif : target <> index_self) :
      simp_lv_observations s target = simp_lv_message_observations s target.
    Proof.
      unfold simp_lv_observations.
      unfold simp_lv_state_observations.
      rewrite decide_False by intuition.
      simpl; reflexivity.
    Qed.
    
    Definition get_simp_event_subject_some 
      (e : simp_lv_event) :=
      Some (get_simp_event_subject e).
    
    (** Instantiation of the observable equivocation typeclasses
       using our newly defined observation type. *)
    
    Program Instance simp_lv_observable_events :
      observable_events (@state index index_listing) simp_lv_event := 
      state_observable_events_instance 
      (@state index index_listing)
      index
      simp_lv_event
      decide_eq
      simp_lv_observations
      (fun (s : state) => index_listing).
      
    Program Instance simp_observable_full :
      (observation_based_equivocation_evidence
       (@state index index_listing)
       index
       simp_lv_event
       simp_lv_observable_events
       decide_eq 
       simp_lv_event_lt
       simp_lv_event_lt_dec 
       get_simp_event_subject_some).
   
   Existing Instance simp_observable_full.

   Definition get_validators {State : Type} (s : State) : list index := index_listing.

   Remark get_validators_nodup
    {State : Type}
    (s : State) :
    NoDup (get_validators s).
   Proof.
    unfold get_validators.
    apply Hfinite.
   Qed.

  Program Definition simp_lv_basic_equivocation : basic_equivocation state index :=
      @basic_observable_equivocation
      (@state index index_listing)
      index
      simp_lv_event
      decide_eq
      simp_lv_event_lt
      simp_lv_event_lt_dec
      simp_lv_observable_events
      (fun (e : simp_lv_event) => Some (get_simp_event_subject e))
      simp_observable_full
      _
      Mindex
      Rindex
      get_validators
      get_validators_nodup.
  Next Obligation.
    apply observable_events_equivocation_evidence_dec.
    apply idec.
  Defined.

  Existing Instance simp_lv_basic_equivocation.  
  
    Lemma message_cross_observations
      (s : state)
      (e1 e2 : simp_lv_event)
      (i j : index)
      (Hin1 : In e1 (simp_lv_message_observations s i))
      (Hin2 : In e2 (simp_lv_message_observations (get_simp_event_state e1) j)) :
      In e2 (simp_lv_message_observations s j).
    Proof.
      destruct e1 as [et1 ev1 es1].
      destruct e2 as [et2 ev2 es2].
      unfold simp_lv_message_observations in *.
      apply in_map_iff in Hin1.
      destruct Hin1 as [s1 [Heq1 Hraw1]].
      apply in_map_iff in Hin2.
      destruct Hin2 as [s2 [Heq2 Hraw2]].
      inversion Heq1.
      inversion Heq2.
      subst et1. subst ev1. subst es1.
      subst et2. subst ev2. subst es2.
      simpl in *.
      apply in_map_iff.
      exists s2.
      split;[intuition|]. 
      apply cross_observations with (s1 := s1) (i := i).
      intuition.
      intuition.
    Qed.
    
    Remark raw_message
      (s s' : state)
      (target : index) :
      In (SimpObs Message' target s') (simp_lv_message_observations s target) <-> In s' (get_raw_observations s target).
    Proof.
      split; intros; unfold simp_lv_message_observations in *. 
      - apply in_map_iff in H.
        destruct H as [x [Heqx Hinx]].
        inversion Heqx.
        rewrite <- H0; intuition.
      - apply in_map_iff.
        exists s'.
        intuition.
    Qed.
   
   Remark in_message_observations_nb
    (s : state)
    (target : index)
    (e : simp_lv_event) 
    (Hin : In e (simp_lv_message_observations s target)) :
    get_simp_event_state e <> Bottom.
    Proof.
      unfold simp_lv_message_observations in Hin.
      apply in_map_iff in Hin.
      destruct Hin as [es [Hes Hines]].
      apply no_bottom_in_observations in Hines.
      rewrite <- Hes.
      intuition.
    Qed.
   
   (** Similar shortcuts as done for raw observations. *)
   
   Lemma unfold_simp_lv_observations
      (s : state)
      (Hnb : s <> Bottom)
      (target : index)
      (e : simp_lv_event)  :
      In e (simp_lv_message_observations s target) ->
      (e = SimpObs Message' target (project s target)) \/
      (exists (i : index), (In e (simp_lv_message_observations (project s i) target))).
   Proof.
      destruct e as [et ev es].
      intros.
      apply in_simp_lv_message_observations in H as H'.
      assert (et = Message') by intuition.
      assert (ev = target) by intuition.
      subst et. subst ev.
      apply raw_message in H as Hraw. 
      apply unfold_raw_observations in Hraw.
      2 : {
        intuition.
      }
      destruct Hraw.
        - left. rewrite H0. intuition.
        - right.
          destruct H0 as [i Hini].
          exists i.
          apply raw_message in Hini.
          intuition.
   Qed.
   
    Lemma refold_simp_lv_observations1
      (s : state)
      (Hprs : s <> Bottom)
      (target : index)
      (Hnb : project s target <> Bottom)
      (e : simp_lv_event)  :
      (e = SimpObs Message' target (project s target)) ->
      In e (simp_lv_message_observations s target).
    Proof.
      intros.
      unfold simp_lv_message_observations.
      apply in_map_iff.
      exists (project s target).
      rewrite H.
      intuition.
      apply refold_raw_observations1.
      all : intuition.
    Qed.
    
    Lemma refold_simp_lv_observations2
      (s : state)
      (Hnb : s <> Bottom)
      (target : index)
      (e : simp_lv_event) :
      (exists (i : index), (In e (simp_lv_message_observations (project s i) target))) ->
      In e (simp_lv_message_observations s target).
   Proof.
     intros.
     destruct H as [i Hine].
     unfold simp_lv_message_observations in *.
     apply in_map_iff.
     apply in_map_iff in Hine.
     destruct Hine as [x Hinx].
     exists x.
     intuition.
     apply refold_raw_observations2.
     intuition.
     exists i; intuition.
   Qed.
  
  (** [get_history] is the backbone of our [has_been_sent] and [has_been_received] capabilities,
     so the following is a simple way of showing that send/received messages
     are present as observations *)
  
  Lemma in_history_in_observations
    (s es : state)
    (target : index)
    (Hin : In es (get_history' s target)) :
    In (SimpObs Message' target es) (simp_lv_message_observations s target).
  Proof.
    remember (get_history' s target) as l.
    generalize dependent s.
    induction l.
    - intros. intuition.
    - intros.
      
      assert (Hnb : s <> Bottom /\ (project s target) <> Bottom). {
        rewrite Heql in Hin.
        split.
        - destruct s; simpl in Hin;[intuition|congruence].
        - destruct (project s target) eqn : eq.
          + unfold get_history' in Hin. destruct s. intuition. unfold last_recorded in Hin.
          unfold project in eq. rewrite eq in Hin. intuition.
          + congruence.
      }
    
      rewrite unfold_history_cons' in Heql by intuition.
      inversion Heql.
      simpl in Hin.
      destruct Hin as [Hin|Hin].
      + subst a.
        subst es.
        apply in_map_iff.
        exists (project s target).
        split.
        * intuition.
        * apply refold_raw_observations1.
          all : intuition.
      + specialize (IHl Hin (project s target) H1).
         apply refold_simp_lv_observations2.
         intuition.
         exists target.
         intuition.
  Qed.
  
  (** The following lemmas describes what happens to observations in a given state <<s>>
     when it undergoes an update. We will be talking mostly about message observations,
     because they are persistent, while state observations are transient. *)
  
  (** Doing a valid update keeps all the existing observations. *)
  
  Lemma old_incl_new
    (s so : state)
    (Hnb : s <> Bottom /\ so <> Bottom)
    (i j : index)
    (Hfull : project s i = project so i)
    (s' := (update_state s so i)) :
    incl (simp_lv_message_observations s j) (simp_lv_message_observations s' j).
  Proof.
    assert (Hs'nb : s' <> Bottom). {
      unfold s'.
      unfold update_state.
      destruct s; intuition congruence.
    }
  
    unfold incl.
    intros e H.
    unfold simp_lv_message_observations in *.
    apply in_map_iff in H.
    destruct H as [es' Hinx].
      
    destruct Hinx as [Heqe Hines'].
    
    assert (Hes'nb : es' <> Bottom). {
      apply no_bottom_in_observations in Hines'.
      intuition.
    }  
    
    apply in_map_iff.
    exists es'.
    split. intuition.
    unfold s'.
    destruct (decide(i = j)).
    - subst i.
      apply unfold_raw_observations in Hines' as Hraw'.
      2 : intuition.
      destruct Hraw'.
      + apply refold_raw_observations2.
        intuition.
        exists j.
        rewrite (@project_same index index_listing Hfinite) by intuition.
        apply refold_raw_observations1.
        intuition.
        rewrite <- Hfull.
        intuition.
      + destruct H as [k Hink].
        apply refold_raw_observations2.
        intuition.
        exists k.
        destruct (decide (k = j)).
        * subst k.
          rewrite (@project_same index index_listing Hfinite) by intuition.
          apply refold_raw_observations2.
          intuition.
          exists j.
          rewrite <- Hfull.
          intuition.
        * rewrite (@project_different index index_listing Hfinite) by intuition.
          intuition.
    - apply unfold_raw_observations in Hines'.
      2 : intuition.
      destruct Hines'.
      + apply refold_raw_observations1.
        intuition.
        rewrite (@project_different index index_listing) by intuition.
        intuition.
      + destruct H as [k Hink].
        apply refold_raw_observations2.
        intuition.
        destruct (decide (k = i)).
        * subst k.
          exists i.
          rewrite (@project_same index index_listing) by intuition.
          apply refold_raw_observations2.
          intuition.
          exists i.
          rewrite <- Hfull.
          intuition.
        * exists k.
          rewrite (@project_different index index_listing) by intuition.
          intuition.
    Qed.
    
   (** The message observations present in the update value <<so>> will
      end up in the message observations of the updated state (<<s'>>*)
    
   Lemma received_incl_new
    (s so : state)
    (Hnb : s <> Bottom /\ so <> Bottom)
    (i j : index)
    (Hfull : project s i = project so i)
    (s' := (update_state s so i)) :
    incl (simp_lv_message_observations so j) (simp_lv_message_observations s' j).
   Proof.
    assert (Hs'nb : s' <> Bottom). {
      unfold s'.
      unfold update_state.
      destruct s; intuition congruence.
    }
   
    unfold incl. intros e H.
    unfold s'.
    unfold simp_lv_message_observations in *.
    apply in_map_iff in H.
    destruct H as [es' Hines'].
    destruct Hines' as [Heqe Hines'].
    
    assert (es' <> Bottom). {
      apply no_bottom_in_observations in Hines'.
      intuition.
    }
    
    apply in_map_iff.
    exists es'. 
    split; [intuition|].
    apply refold_raw_observations2.
    intuition.
    exists i.
    rewrite (@project_same index index_listing Hfinite) by intuition.
    intuition.
   Qed.
   
   (** A message observation of the updated state <<s'>> is either
      - an observation of the old state <<s>>
      - an observation of the update value <<so>>
      
      IF the update occurs on a projection that is NOT the subject
      of the observations *) 
      
   Lemma new_incl_rest_diff
    (s so : state)
    (Hnb : s <> Bottom /\ so <> Bottom)
    (i j : index)
    (Hdif : i <> j)
    (Hfull : project s i = project so i)
    (s' := (update_state s so i)) :
    let s1 := simp_lv_message_observations s j in
    let all := set_union decide_eq s1 (simp_lv_message_observations so j) in
    incl (simp_lv_message_observations s' j) all.
   Proof.
    unfold incl. intros e H.
    unfold s' in H.
    apply in_message_observations_nb in H as Hesnb.
    apply unfold_simp_lv_observations in H as Hraw.
    2 : {
      unfold update_state; destruct s; intuition congruence.
    }
    apply set_union_iff.
    destruct Hraw.
    - destruct (decide (i = j)).
      + congruence.
      + rewrite (@project_different index index_listing Hfinite) in H0 by intuition.
        left.
        apply refold_simp_lv_observations1;[intuition|..].
        rewrite H0 in Hesnb; simpl in Hesnb.
        all : intuition.
    - destruct H0 as [k Hink].
       destruct (decide (k = i)).
       + subst k.
          rewrite (@project_same index index_listing Hfinite) in Hink by intuition.
          right.
          intuition.
       +  rewrite (@project_different index index_listing Hfinite) in Hink by intuition.
          left.
          apply refold_simp_lv_observations2;[intuition|..].
          exists k. 
          intuition.
   Qed.
   
   (** A message observation of the updated state <<s'>> is either
      - an observation of the old state <<s>>
      - an observation of the update value <<so>>
      - the observation (Message' i so)
      
      IF the update occurs on the projection that IS the subject
      of the observations *) 
  
  Lemma new_incl_rest_same
    (s so : state)
    (Hnb : s <> Bottom /\ so <> Bottom)
    (i : index)
    (Hfull : project s i = project so i)
    (s' := (update_state s so i)) :
    let s1 := simp_lv_message_observations s i in
    let s2 := set_union decide_eq s1 (simp_lv_message_observations so i) in
    let all := set_union decide_eq s2 [SimpObs Message' i so] in
    incl (simp_lv_message_observations s' i) all.
   Proof.
    unfold incl. intros e H.
    unfold s' in H.
    apply in_message_observations_nb in H as Hesnb.
    apply unfold_simp_lv_observations in H as Hraw.
    2 : {
      unfold update_state; destruct s; intuition congruence.
    }
    apply set_union_iff.
    destruct Hraw.
    - rewrite (@project_same index index_listing Hfinite) in H0 by intuition.
      right. rewrite H0. intuition.
    - destruct H0 as [k Hink].
       destruct (decide (k = i)).
       + subst k.
          rewrite (@project_same index index_listing Hfinite) in Hink by intuition.
          left.
          apply set_union_iff.
          right. intuition.
       +  rewrite (@project_different index index_listing Hfinite) in Hink by intuition.
          left.
          apply set_union_iff.
          left.
          apply refold_simp_lv_observations2;[intuition|..].
          exists k. 
          intuition.
  Qed. 
   
   (** The above holds in general regardless of relation between
      <<i>> and <<j>>. *)
   
   Lemma new_incl_rest
    (s so : state)
    (Hnb : s <> Bottom /\ so <> Bottom)
    (i j : index)
    (Hfull : project s i = project so i)
    (s' := (update_state s so i)) :
    let s1 := simp_lv_message_observations s j in
    let s2 := set_union decide_eq s1 (simp_lv_message_observations so j) in
    let all := set_union decide_eq s2 [SimpObs Message' j so] in
    incl (simp_lv_message_observations s' j) all.
   Proof.
    unfold incl. intros e H.
    unfold s' in H.
    apply in_message_observations_nb in H as Hesnb.
    apply unfold_simp_lv_observations in H as Hraw.
    2 : {
      unfold update_state; destruct s; intuition congruence.
    }
    apply set_union_iff.
    destruct Hraw.
    - destruct (decide (i = j)).
      + subst j.
        rewrite (@project_same index index_listing Hfinite) in H0 by intuition.
        right. rewrite H0. intuition.
      + rewrite (@project_different index index_listing Hfinite) in H0 by intuition.
        left.
        apply set_union_iff.
        left.
        apply refold_simp_lv_observations1;[intuition|..].
        rewrite H0 in Hesnb; simpl in Hesnb.
        all : intuition.
    - destruct H0 as [k Hink].
       destruct (decide (k = i)).
       + subst k.
          rewrite (@project_same index index_listing Hfinite) in Hink by intuition.
          left.
          apply set_union_iff. 
          right.
          intuition.
       + rewrite (@project_different index index_listing Hfinite) in Hink by intuition.
          left.
          apply set_union_iff.
          left.
          apply refold_simp_lv_observations2;[intuition|..].
          exists k. intuition.
  Qed.
  
  (** If a message observation <<e>> compares with a state observation
     <(State' index_self s)>, it will also compare to the state
     observation of its updated version,
     <(State' index_self s'> *)
  
  Lemma state_obs_stuff
    (s so : state)
    (Hnb : s <> Bottom /\ so <> Bottom)
    (i : index)
    (Hfull : project s i = project so i)
    (s' := update_state s so i)
    (s_obs := (SimpObs State' index_self s))
    (s'_obs := (SimpObs State' index_self s')) 
    (e : simp_lv_event)
    (Hns : get_simp_event_type e <> State') 
    (Hsubj : get_simp_event_subject e = index_self)
    (Hcomp: comparable simp_lv_event_lt e s_obs) :
    comparable simp_lv_event_lt e s'_obs.
  Proof.
    simpl in *.
    unfold s' in *.
    unfold s'_obs in *.
    unfold s_obs in *.
    destruct e as [et ev es].
    unfold comparable in *.
    destruct Hcomp.
    - simpl in *.
      inversion H.
      congruence.
    - right.
      destruct H.
      + left.
        unfold simp_lv_event_lt in *.
        rewrite decide_True in * by intuition.
        destruct et eqn : eq_et.
        * simpl in Hns. congruence. 
        * unfold state_lt' in *.
          destruct (decide (i = ev)).
          -- subst i.
             rewrite unfold_history_cons'; rewrite (@project_same index index_listing Hfinite) by intuition.
             rewrite <- (@eq_history_eq_project index index_listing Hfinite) in Hfull.
             rewrite <- Hfull.
             simpl. right. intuition.
             intuition.
          -- rewrite unfold_history_cons'; rewrite (@project_different index index_listing Hfinite) by intuition.
             rewrite unfold_history_cons' in H.
             intuition.
             apply non_empty_history_nb_project with (so0 := es).
             intuition.
             apply non_empty_history_nb_project with (so0 := es).
             intuition.
      + right.
        unfold simp_lv_event_lt in *.
        rewrite decide_True in * by intuition.
        destruct et eqn : eq_et.
        * simpl in Hns.
          congruence.
        * intuition. 
  Qed.
  
  (** Same with an update_consensus inserted.
     The silly duplication will be taken care of shortly. :) *)
  
  Lemma state_obs_stuff_cons
    (s so : state)
    (Hnb : s <> Bottom /\ so <> Bottom)
    (i : index)
    (Hfull : project s i = project so i)
    (b : bool)
    (s' := update_consensus (update_state s so i) b)
    (s_obs := (SimpObs State' index_self s))
    (s'_obs := (SimpObs State' index_self s')) 
    (e : simp_lv_event)
    (Hns : get_simp_event_type e <> State') 
    (Hsubj : get_simp_event_subject e = index_self)
    (Hcomp: comparable simp_lv_event_lt e s_obs) :
    comparable simp_lv_event_lt e s'_obs.
  Proof.
    simpl in *.
    unfold s' in *.
    unfold s'_obs in *.
    unfold s_obs in *.
    destruct e as [et ev es].
    unfold comparable in *.
    destruct Hcomp.
    - simpl in *.
      inversion H.
      congruence.
    - right.
      destruct H.
      + left.
        unfold simp_lv_event_lt in *.
        rewrite decide_True in * by intuition.
        destruct et eqn : eq_et.
        * simpl in Hns. congruence. 
        * unfold state_lt' in *.
          destruct (decide (i = ev)).
          -- subst i.
             rewrite history_disregards_cv.
             rewrite unfold_history_cons'; rewrite (@project_same index index_listing Hfinite) by intuition.
             rewrite <- (@eq_history_eq_project index index_listing Hfinite) in Hfull.
             rewrite <- Hfull.
             simpl. right. intuition.
             intuition.
          -- rewrite history_disregards_cv.
             rewrite unfold_history_cons'; rewrite (@project_different index index_listing Hfinite) by intuition.
             rewrite unfold_history_cons' in H.
             intuition.
             apply non_empty_history_nb_project with (so0 := es).
             intuition.
             apply non_empty_history_nb_project with (so0 := es).
             intuition.
      + right.
        unfold simp_lv_event_lt in *.
        rewrite decide_True in * by intuition.
        destruct et eqn : eq_et.
        * simpl in Hns.
          congruence.
        * intuition. 
  Qed.
  
  (** The following concerns the complete observation model, which distinguishes between sent
     and received message observations. It was written before we decided to opt for the
     simplified type in the common futures theorem. *)
     
  Inductive lv_event_type : Type :=
    | State
    | Sent
    | Received.
    
    Instance event_type_eq_dec : EqDecision lv_event_type.
      solve_decision.
    Defined. 
    
    Inductive lv_event : Type :=
      Obs: lv_event_type -> index -> (@state index index_listing) -> lv_event.
    
    Global Instance event_eq_dec : EqDecision lv_event.
      solve_decision.
    Defined. 
    
    Definition get_event_subject (e : lv_event) : index :=
    match e with 
      Obs type subject state => subject
    end.
        
    Definition get_event_subject_some 
      (e : lv_event) :=
      Some (get_event_subject e).
    
    Definition get_event_type (e : lv_event) :=
      match e with
       Obs type subject state => type
      end.
      
    Definition get_event_state (e : lv_event) :=
      match e with
        Obs type subject state => state
      end.
      
    Definition lv_event_comp_eq 
      (e : lv_event) :
      e = Obs (get_event_type e) (get_event_subject e) (get_event_state e).
    Proof.
      destruct e.
      simpl.
      reflexivity.
    Qed.
    
    Definition lv_event_lt (e1 e2 : lv_event) : Prop :=
    match e1, e2 with
      Obs type1 subject1 state1, Obs type2 subject2 state2 =>
        match decide_eq subject1 subject2 with
        | right _ => False
        | _ => match type1, type2 with
               | State, State => False
               | State, Sent => False
               | State, Received => False
               | _, _ => state_lt' subject1 state1 state2
               end  
        end
    end.
    
    Lemma lv_event_trans
      (e1 e2 e3 : lv_event)
      (Hlt : lv_event_lt e1 e2 /\ lv_event_lt e2 e3) :
      lv_event_lt e1 e3.
    Proof.
      destruct Hlt as [Hlt1 Hlt2].
      unfold lv_event_lt in Hlt1, Hlt2.
      destruct e1 as [et1 ev1 es1].
      destruct e2 as [et2 ev2 es2].
      destruct e3 as [et3 ev3 es3].
      assert (ev1 = ev2) by (destruct(decide(ev1 = ev2)); intuition).
      assert (ev2 = ev3) by (destruct(decide(ev2 = ev3)); intuition).
      rewrite decide_True in Hlt1 by intuition.
      rewrite decide_True in Hlt2 by intuition.
      
      assert (ev1 = ev3). {
        apply eq_trans with (y := ev2); intuition.
      }
      
      assert (et1 <> State). {
        intros contra. rewrite contra in Hlt1.
        destruct et2; intuition.
      }
      
      assert (et2 <> State). {
        intros contra. rewrite contra in Hlt2.
        destruct et3; intuition.
      }
      
      destruct et1 eqn : eq_et1.
      - intuition.
      - destruct et2 eqn : eq_et2.
        + intuition.
        + unfold lv_event_lt.
          rewrite decide_True by intuition.
          apply (@state_lt'_trans index index_listing Hfinite) with (s2 := es2).
          rewrite <- H in Hlt2. intuition.
        + unfold lv_event_lt.
          rewrite decide_True by intuition.
          apply (@state_lt'_trans index index_listing Hfinite) with (s2 := es2).
          rewrite <- H in Hlt2. intuition.
      - destruct et2 eqn : eq_et2.
        + intuition.
        + unfold lv_event_lt.
          rewrite decide_True by intuition.
          apply (@state_lt'_trans index index_listing Hfinite) with (s2 := es2).
          rewrite <- H in Hlt2. intuition.
        + unfold lv_event_lt.
          rewrite decide_True by intuition.
          apply (@state_lt'_trans index index_listing Hfinite) with (s2 := es2).
          rewrite <- H in Hlt2. intuition.
    Qed.
    
    Lemma lv_event_lt_dec : RelDecision lv_event_lt.
    Proof.
      unfold RelDecision. intros.
      unfold Decision.
      unfold lv_event_lt.
      destruct x as [type1 subject1 state1]; destruct y as [type2 subject2 state2].
      destruct (decide (subject1 = subject2)).
      - destruct type1 eqn : eq1.
        + right. destruct type2; auto.
        + exact (state_lt'_dec subject1 state1 state2).
        + exact (state_lt'_dec subject1 state1 state2).
      - right. auto.
    Qed.
    
    Definition lv_sent_states (s : state) (target : index) : set (@state index index_listing) :=
      match decide_eq target index_self with
      | left _ => get_history s index_self
      | right _ => []
      end.
    
    Definition lv_sent_observations (s : state) (target : index) : set lv_event :=
      match decide_eq target index_self with
      | left _ => List.map (Obs Sent index_self) (lv_sent_states s target)
      | right _ => []
      end.
      
    Lemma in_lv_sent 
      (s : state)
      (target : index)
      (e : lv_event)
      (Hin : In e (lv_sent_observations s target)) :
      get_event_type e = Sent /\ get_event_subject e = target.
    Proof.
      unfold lv_sent_observations in Hin.
      destruct (decide (target = index_self)).
      - unfold lv_sent_states in Hin.
        rewrite decide_True in Hin.
        apply in_map_iff in Hin.
        destruct Hin as [x [Hsent _]].
        rewrite <- Hsent; simpl.
        rewrite e0.
        all : intuition.
      - intuition.
    Qed.
      
    Definition lv_received_observations (s : state) (target : index) : set lv_event :=
      let obs := (get_raw_observations s target) in
      let sent_obs := lv_sent_states s target in
      match decide_eq target index_self with
      | left _ => []
      | right _ => List.map (Obs Received target) (set_remove_list sent_obs obs)
      end.
      
    Lemma in_lv_received 
      (s : state)
      (target : index)
      (e : lv_event)
      (Hin : In e (lv_received_observations s target)) :
      get_event_type e = Received /\ get_event_subject e = target.
    Proof.
      unfold lv_received_observations in Hin.
      destruct (decide (target = index_self)).
      - intuition.
      - apply in_map_iff in Hin.
        destruct Hin as [x [Hobs _]].
        rewrite <- Hobs; simpl.
        intuition.
    Qed.
      
    Definition lv_state_observations (s : state) (target : index) : set lv_event :=
      match decide_eq target index_self with
      | left _ => [Obs State index_self s]
      | right _ => []
      end.
    
    Lemma in_lv_state 
      (s : state)
      (target : index)
      (e : lv_event)
      (Hin : In e (lv_state_observations s target)) :
      get_event_type e = State /\ get_event_subject e = target.
    Proof.
      unfold lv_state_observations in Hin.
      destruct (decide (target = index_self)).
      - simpl in Hin.
        destruct Hin.
        rewrite <- H; simpl.
        rewrite e0.
        all : intuition.
      - intuition.
    Qed.
        
    Lemma raw_received
      (s s' : state)
      (target : index)
      (Hdif : target <> index_self) :
      In (Obs Received target s') (lv_received_observations s target) <-> In s' (get_raw_observations s target).
    Proof.
      split; intros; unfold lv_received_observations in *.
      - rewrite decide_False in H by intuition.
        apply in_map_iff in H.
        destruct H as [s'' [Hobs Hins'']].
        apply set_remove_list_1 in Hins''.
        unfold get_raw_observations.
        inversion Hobs.
        rewrite <- H0.
        intuition.
      - rewrite decide_False by intuition.
        apply in_map_iff.
        exists s'.
        split;[reflexivity|].
        unfold lv_sent_states.
        rewrite decide_False by intuition.
        intuition.
    Qed.
      
    Definition lv_message_observations (s : state) (target : index) : set lv_event :=
      set_union decide_eq (lv_sent_observations s target) (lv_received_observations s target).
      
    Definition lv_observations (s : state) (target : index) : set lv_event :=
      set_union decide_eq (lv_state_observations s target) (lv_message_observations s target).
    
        Lemma get_event_state_nb
      (s s': state)
      (i : index)
      (e : lv_event)
      (He : e = (Obs Received i s') \/ e = (Obs Sent i s'))
      (Hin : In e (lv_observations s i)) :
      s' <> Bottom.
    Proof.
      assert (Hse : get_event_state e = s'). {
        destruct He; rewrite H; intuition.
      }
      unfold lv_observations in Hin.
      apply set_union_elim in Hin.
      destruct Hin.
      - apply in_lv_state in H.
        destruct He as [He|He]; rewrite He in H; simpl in H; destruct H; congruence.
      - unfold lv_message_observations in H.
        apply set_union_elim in H.
        destruct H.
        + unfold lv_sent_observations in H.
          destruct (decide (i = index_self)).
          * unfold lv_sent_states in H.
            rewrite decide_True in H.
            apply in_map_iff in H.
            destruct H as [x [Hobs Hinx]].
            apply (@no_bottom_in_history index index_listing Hfinite) in Hinx.
            rewrite <- Hobs in Hse; simpl in Hse.
            rewrite <- Hse.
            all : intuition.
          * simpl in H; intuition.
        + unfold lv_received_observations in H.
          destruct (decide (i = index_self)).
          * simpl in H; intuition.
          * apply in_map_iff in H.
          destruct H as [x [Hobs Hinx]].
          apply set_remove_list_1 in Hinx.
          apply no_bottom_in_observations in Hinx.
          rewrite <- Hobs in Hse; simpl in Hse.
          rewrite <- Hse.
          intuition.
    Qed.
End Observations.
