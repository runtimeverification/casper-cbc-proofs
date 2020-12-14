Require Import Bool List ListSet Reals FinFun RelationClasses Relations Relations_1 Sorting Basics.
Require Import Lia.
Import ListNotations.
From CasperCBC
Require Import
  Lib.Preamble
  Lib.ListExtras
  Lib.ListSetExtras
  Lib.SortedLists
  VLSM.Common
  VLSM.Actions
  VLSM.Composition
  VLSM.Equivocation
  VLSM.ListValidator.ListValidator
  VLSM.ListValidator.Equivocation
  VLSM.ListValidator.EquivocationAwareListValidator
  VLSM.ListValidator.GeneralComposition
  VLSM.ObservableEquivocation
  CBC.Common
  CBC.Equivocation.

Section Composition.

Context
  {index : Type}
  {i0 : index}
  {index_listing : list index}
  {Hfinite : Listing index_listing}
  {idec : EqDecision index}
  {Mindex : Measurable index}
  {Rindex : ReachableThreshold index}
  (Rtemp := fun (i : index) => RelDecision (@state_lt' index index_listing _ i))
  (est' := fun (i : index) => (@EquivocationAwareListValidator.equivocation_aware_estimator _ i _ Hfinite _ _ _ ))
  (IM_index := fun (i : index) => @VLSM_list index i index_listing idec (est' i))
  (has_been_sent_capabilities := fun i : index => @has_been_sent_lv index i index_listing Hfinite idec (est' i))
  (has_been_received_capabilities := fun i : index => @has_been_received_lv index i index_listing Hfinite idec (est' i))
  (X := composite_vlsm IM_index i0 (free_constraint IM_index))
  (preX := pre_loaded_with_all_messages_vlsm X)
  (complete_observations := @complete_observations index i0 index_listing decide_eq)
  (Hevidence := fun (i : index) => @observable_full index i index_listing idec)
  (Hbasic := fun (i : index) => @lv_basic_equivocation index i index_listing Hfinite idec Mindex Rindex)
  (ce := @composed_observation_based_equivocation_evidence
    message index lv_event
    decide_eq 
    lv_event_lt
    lv_event_lt_dec
    get_event_subject
    index index_listing IM_index Hevidence).
  
  Check complete_observations.
  
        
    Definition others (i : index) := 
      set_remove idec i index_listing.
      
    Lemma NoDup_others
      (i : index) :
      NoDup (others i).
    Proof.
      unfold others.
      apply set_remove_nodup.
      apply (proj1 Hfinite).
    Qed.
    
    Lemma others_correct
      (i : index) :
      ~ In i (others i).
    Proof.
      unfold others.
      intros contra.
      assert (NoDup index_listing) by (apply (proj1 Hfinite)).
      apply set_remove_2 in contra.
      all : intuition.
    Qed.
    
    Lemma others_correct2
      (i j : index)
      (Hdif : j <> i) :
      In j (others i).
    Proof.
      unfold others.
      apply set_remove_3.
      apply Hfinite.
      assumption.
    Qed.
  
  Definition get_message_providers_from_action
   (a : vaction X) : list index :=
    List.map fst (messages_a X a).
  
  Definition component_list (s : vstate X) (li : list index) :=
    List.map s li.
  
  Definition unite_observations (ls : list state) : set lv_event := 
    fold_right (set_union decide_eq) [] (List.map (complete_observations) ls).
  
  Definition GH (s : vstate X) : set index := 
    List.filter (fun i : index => negb (
    @bool_decide _ (@equivocation_evidence_dec (vstate X) index lv_event _ lv_event_lt lv_event_lt_dec get_event_subject ce s i))) index_listing.
  
  Definition GE (s : vstate X) : set index :=
    set_diff idec index_listing (GH s).
 
  Definition ce' (s : vstate X) := @composed_witness_observation_based_equivocation_evidence
    message index lv_event
    decide_eq 
    lv_event_lt
    lv_event_lt_dec
    get_event_subject
    index IM_index Hevidence (GH s).
 
  Definition LH (s : vstate X) : set index :=
    List.filter (fun i : index => negb (
    @bool_decide _ (@equivocation_evidence_dec (vstate X) index lv_event _ lv_event_lt lv_event_lt_dec get_event_subject (ce' s) s i))) index_listing.
  
  Definition LE (s : vstate X) : set index :=
    set_diff idec index_listing (LH s).
  
  Lemma GH_incl_all
    (s : vstate X) :
    incl (GH s) index_listing.
  Proof.
    unfold incl.
    simpl.
    intros.
    apply ((proj2 Hfinite) a).
  Qed.
  
  Definition cobs := @observable_events (composite_state IM_index) index lv_event
    decide_eq 
    lv_event_lt
    lv_event_lt_dec
    get_event_subject ce.
    
  Definition obs 
    (i : index) := 
    @observable_events (@state index index_listing) index lv_event
    decide_eq 
    lv_event_lt
    lv_event_lt_dec
    get_event_subject (Hevidence i).
  
  Definition cequiv_evidence
    := (@equivocation_evidence (vstate X) index lv_event _ lv_event_lt lv_event_lt_dec get_event_subject ce).
  
  Lemma GE_direct 
    (s : vstate X)
    (i : index) :
    In i (GE s) <-> (cequiv_evidence s i).
  Proof.
  Admitted.
  
  Lemma GE_existing_update
    (s : vstate X)
    (so : state)
    (i j : index)
    (s' := state_update IM_index s i (update_state (s i) so j))
    (Hhave : In (Obs Sent j so) (cobs s j) \/
             In (Obs Received j so) (cobs s j)) :
    incl (GE s') (GE s).
  Proof.
    unfold incl; intros.
    apply GE_direct in H as Hev.
    apply GE_direct.
    unfold cequiv_evidence in *.
    unfold equivocation_evidence in *.
    destruct Hev as [e1 [Hine1 Hrem]].
    destruct Hrem as [e2 [Hine2 Hcomp]].
    destruct (inb decide_eq e1 (observable_events s a)) eqn : eq_1;
    destruct (inb decide_eq e2 (observable_events s a)) eqn : eq_2.
    - rewrite <- in_correct in eq_1, eq_2.
      exists e1.
      split. 
      + assumption.
      + exists e2. 
        split. assumption.
        assumption.
  Admitted.
  
  Lemma cobs_update_different
    (s : vstate X)
    (i j : index)
    (Hdif : i <> j)
    (b : bool)
    (s' := state_update IM_index s i (update_consensus (update_state (s i) (s i) i) b)) :
    set_eq (cobs s' j) (cobs s j).
  Proof.
    unfold set_eq.
    split; (unfold incl; 
      intros e He; 
      unfold cobs in *; 
      unfold observable_events in *; 
      simpl in *; 
      unfold composed_witness_observable_events in *).
    - apply set_union_in_iterated in He; rewrite Exists_exists in He.
      destruct He as [x [Hinx Hine]].
      apply in_map_iff in Hinx.
      destruct Hinx as [k [Hobs _]].
      apply set_union_in_iterated; rewrite Exists_exists.
      destruct (decide (k = i)).
      + exists (obs k (s k) j).
        split.
        * apply in_map_iff.
          exists k; simpl.
          unfold obs.
          unfold observable_events; simpl.
          intuition. 
          apply ((proj2 Hfinite) k).
        * unfold obs.
          unfold observable_events in *; simpl in *.
          admit.
      + assert (s' k = s k). {
          unfold s'.
          rewrite state_update_neq.
          all : intuition.
        }
        exists (obs k (s k) j).
        split.
        * apply in_map_iff.
          exists k; simpl.
          unfold obs.
          unfold observable_events; simpl.
          intuition. 
          apply ((proj2 Hfinite) k).
        * rewrite H in Hobs.
          unfold obs.
          unfold observable_events in *.
          simpl in *.
          rewrite Hobs.
          assumption.
  Admitted.
  
  Lemma GE_existing_update'
    (s : vstate X)
    (i : index)
    (b : bool)
    (s' := state_update IM_index s i (update_consensus (update_state (s i) (s i) i) b)) :
    incl (GE s') (GE s).
  Proof.
    unfold incl; intros v H.
    apply GE_direct in H as Hev.
    apply GE_direct.
    unfold cequiv_evidence in *.
    unfold equivocation_evidence in *.
    destruct Hev as [e1 [Hine1 Hrem]].
    destruct Hrem as [e2 [Hine2 Hcomp]].
    destruct (decide (v = i)).
    - admit. 
    - assert (set_eq (cobs s' v) (cobs s v)). {
         apply cobs_update_different.
         intuition.
      }
      unfold cobs in H0.
      unfold observable_events in Hine1, Hine2, H0; simpl in Hine1, Hine2, H0.
      setoid_rewrite H0 in Hine1.
      setoid_rewrite H0 in Hine2.
      exists e1.
      split; [intuition|].
      exists e2.
      split; [intuition|].
      assumption.
  Admitted.
    
  Definition feasible_update_value (s : (@state index index_listing)) (who : index) : bool :=
    match s with
    | Bottom => false
    | Something c is => match (@equivocation_aware_estimatorb index who index_listing Hfinite decide_eq _ _ s false) with
                        | true => false
                        | false => true
                        end
    end.
  
  Definition not_all_equivocating
    (s : (@state index index_listing))
    (who : index) 
    : Prop
    := @no_equivocating_decisions index index_listing idec s 
      (@equivocating_validators (@state index index_listing) index Mindex Rindex (Hbasic who) s) <> [].
  
  Definition no_component_fully_equivocating
    (s : vstate X)
    (li : list index) : Prop
    := forall (i : index), In i li -> not_all_equivocating (s i) i.
  
  Lemma feasible_update_value_correct 
    (s : (@state index index_listing))
    (who : index)
    (Hne : not_all_equivocating s who) :
    (@equivocation_aware_estimator index who index_listing Hfinite decide_eq _ _ s (feasible_update_value s who)).
  Proof.
   destruct (feasible_update_value s who) eqn : eq_fv.
   - unfold feasible_update_value in eq_fv.
     destruct s.
     discriminate eq_fv.
     destruct (equivocation_aware_estimatorb (Something b is)) eqn : eq_ewb.
     discriminate eq_fv.
     apply ea_estimator_total in eq_ewb.
     assumption.
     assumption.
   - unfold feasible_update_value in eq_fv.
     destruct s.
     simpl.
     apply I.
     destruct (equivocation_aware_estimatorb (Something b is) false) eqn : eq_ewb.
     unfold equivocation_aware_estimator. 
     assumption.
     discriminate eq_fv.
  Qed.
  
  Definition feasible_update_single (s : (@state index index_listing)) (who : index) : action_item :=
    let cv := feasible_update_value s who in
    let res := @list_transition index who _ _ (update cv) (s, None) in
    @Build_action_item _ (type (IM_index who)) (update cv) None.
  
  Definition feasible_update_composite (s : vstate X) (who : index) : vaction_item X :=
    lift_to_composite_action_item IM_index who (feasible_update_single (s who) who).
  
  Lemma feasible_update_protocol 
    (s : vstate X)
    (Hprs : protocol_state_prop _ s)
    (who : index) 
    (Hne : not_all_equivocating (s who) who)
    (item := feasible_update_composite s who) :
    protocol_valid X (label_a item) (s, input_a item).
  Proof.
    unfold protocol_transition.
    repeat split.
    assumption.
    simpl.
    apply option_protocol_message_None.
    apply feasible_update_value_correct with (s := s who) (who := who).
    assumption.
  Qed.
  
  (* pair (stare, transition_item) *)
  
  Definition chain_updates (li : list index) (s : vstate X) : vaction X :=
    List.map (feasible_update_composite s) li.
  
  Definition phase_one_action (s : vstate X) : vaction X :=
    chain_updates index_listing s.
 
  Definition phase_one (s : vstate X) : list (vtransition_item X) * vstate X :=
    apply_action X s (phase_one_action s).
  
  Definition phase_one_res 
    (s : vstate X) :=
    snd (phase_one s).
 
  Definition phase_one_transitions
    (s : vstate X) :=
    fst (phase_one s).
  
  Lemma chain_updates_projections_out 
    (s : vstate X)
    (li : list index)
    (i : index)
    (Hi : ~In i li)
    (s' := snd (apply_action X s (chain_updates li s))) :
    (s' i) = (s i).
  Proof.
    apply irrelevant_components.
    intros contra.
    apply in_map_iff in contra.
    destruct contra as [x [Heqproj contra]].
    apply in_map_iff in contra.
    destruct contra as [a [Heqlabel contra]].
    unfold chain_updates in contra.
    apply in_map_iff in contra.
    destruct contra as [j [Hfease Hj]].
    rewrite <- Heqlabel in Heqproj.
    rewrite <- Hfease in Heqproj.
    unfold feasible_update_composite in Heqproj.
    simpl in Heqproj.
    rewrite Heqproj in Hj.
    intuition.
  Qed.
  
  Lemma chain_updates_protocol 
    (s : vstate X)
    (Hspr : protocol_state_prop _ s)
    (li : list index)
    (Hnodup : NoDup li)
    (Hnf : no_component_fully_equivocating s li) :
    let res := snd (apply_action X s (chain_updates li s)) in
    finite_protocol_action_from _ s (chain_updates li s) /\
    (forall (i : index), In i li -> project (res i) i = s i) /\ 
    incl (GE res) (GE s).
  Proof.
    unfold no_component_fully_equivocating in Hnf.
    generalize dependent s.
    induction li as [|i li].
    - intros.
      simpl.
      split.
      + apply finite_ptrace_empty.
        assumption.
      + intuition.
    - intros.
      remember (feasible_update_composite s i) as a.
      specialize (Hnf i) as Hnfi.
      spec Hnfi. {
        intuition.
      }
      remember (vtransition X (label_a a) (s, input_a a)) as res_a.
      
      assert (protocol_transition X (label_a a) (s, input_a a) res_a). {
        rewrite Heqa.
        unfold protocol_transition.
        split.
        - apply feasible_update_protocol.
          all : assumption.
        - rewrite Heqres_a.
          unfold vtransition.
          rewrite Heqa.
          reflexivity.
      }
       
      unfold chain_updates.
      replace (i :: li) with ([i] ++ li) by intuition.
      rewrite map_app.
      
      remember (snd (apply_action X s (map (feasible_update_composite s) [i]))) as s'.
      
      apply NoDup_cons_iff in Hnodup.
      destruct Hnodup as [Hnoa Hnoli].
      specialize (IHli Hnoli s').
      
      spec IHli. {
        rewrite Heqs'.
        apply apply_action_last_protocol.
        assumption.
        simpl.
        apply finite_protocol_action_from_one.
        unfold protocol_transition in H.
        rewrite <- Heqa.
        unfold protocol_transition.
        intuition.
      }
      
      assert (Hindif : forall (i : index), In i li -> s' i = s i). {
        intros.
        rewrite Heqs'.
        apply irrelevant_components_one.
        simpl.
        intros contra.
        rewrite contra in H0.
        intuition.
      }
        
      spec IHli. {
        intros.
        destruct (decide (i1 = i)).
        - rewrite e in H0; intuition.
        - specialize (Hindif i1 H0).
          rewrite Hindif.
          apply Hnf.
          simpl.
          right; intuition.
      }
      
      assert (Hchain : (map (feasible_update_composite s) li) = (map (feasible_update_composite s') li)). {
        apply map_ext_in; intros j Hjli.
        unfold feasible_update_composite.
        replace (s' j) with (s j). 
        reflexivity.
        symmetry.
        apply Hindif.
        intuition.
      }
      
      simpl in IHli.
      
      split.
      + apply finite_protocol_action_from_app_iff.
        split.
        * unfold feasible_update_composite; simpl.
          apply finite_protocol_action_from_one.
          unfold protocol_transition.
          split.
          apply feasible_update_protocol.
          all : intuition.
        * rewrite Heqs' in IHli at 1.
          unfold chain_updates in IHli.
          rewrite Hchain; intuition.
      +
        unfold res; simpl.
        replace (feasible_update_composite s i :: chain_updates li s) with 
                ([feasible_update_composite s i] ++ chain_updates li s) by intuition.
        rewrite apply_action_app.
        destruct (apply_action X s [feasible_update_composite s i]) as (tr_short, res_short) eqn : eq_short.
        assert (res_short = snd (apply_action X s [feasible_update_composite s i])) by (rewrite eq_short; intuition).
        destruct (apply_action X res_short (chain_updates li s)) as (tr_long, res_long) eqn : eq_long.
        assert (res_long = snd (apply_action X res_short (chain_updates li s))) by (rewrite eq_long; intuition).

        assert (s' = res_short). {
          rewrite Heqs'.
          rewrite H0.
          simpl.
          reflexivity.
        }
        
        assert (Hsame : res_long i = res_short i). {
          rewrite H1.
          unfold chain_updates.
          rewrite Hchain.
          rewrite H2.
          apply chain_updates_projections_out.
          assumption.
        }
        
        split.
        intros j Hjli.
        * destruct (decide (j = i)).
          -- simpl.
             rewrite e.
             rewrite Hsame.
             rewrite H0.
             unfold apply_action.
             unfold apply_action_folder; simpl. 
             rewrite state_update_eq.
             rewrite <- update_consensus_clean with (value := (feasible_update_value (s i) i)).
             rewrite (@project_same index index_listing).
             reflexivity.
             apply Hfinite.
             apply protocol_state_component_no_bottom.
             assumption.
          -- destruct IHli as [_ [IHli _]].
             specialize (IHli j).
             spec IHli save. {
               destruct Hjli.
               simpl in H0.
               simpl in H3.
               intuition.
               assumption.
             }
             specialize (Hindif j H3).
             rewrite <- Hindif.
             rewrite <- IHli.
             simpl.
             f_equal.
             unfold chain_updates.
             rewrite <- Hchain.
             rewrite H2.
             rewrite H1.
             unfold chain_updates.
             reflexivity.
        * simpl.
          assert (Hge_short : incl (GE res_short) (GE s)). {
            remember (update_consensus (update_state (s i) (s i) i) (feasible_update_value (s i) i)) as new_si.
            remember (state_update IM_index s i new_si) as new_s.
            specialize (GE_existing_update' s i) as Hexist.
            simpl in Hexist.
            assert (Hu: res_short = new_s). {
              rewrite H0.
              rewrite Heqnew_s.
              unfold apply_action.
              unfold feasible_update_composite; simpl.
              rewrite Heqnew_si.
              reflexivity.
            }
            rewrite Hu.
            rewrite Heqnew_s.
            rewrite Heqnew_si.
            apply Hexist.
          }
          
          assert (Hge_long : incl (GE res_long) (GE res_short)). {
            destruct IHli as [_ [_ IHli]].
            unfold chain_updates in IHli.
            rewrite <- Hchain in IHli.
            rewrite H2 in IHli.
            unfold chain_updates in H1.
            rewrite H1.
            apply IHli.
          }
          apply incl_tran with (m := (GE res_short)).
          assumption.
          assumption.
  Qed.
  
  Lemma phase_one_protocol
    (s : vstate X)
    (Hprs : protocol_state_prop X s)
    (Hnf : no_component_fully_equivocating s index_listing) :
    finite_protocol_action_from X s (phase_one_action s).
  Proof.
    unfold phase_one_action.
    apply chain_updates_protocol.
    assumption.
    apply (proj1 Hfinite).
    assumption.
  Qed.
  
  Lemma phase_one_future 
    (s : vstate X)
    (Hnf : no_component_fully_equivocating s index_listing)
    (Hspr : protocol_state_prop _ s) :
    in_futures _ s (phase_one_res s).
  Proof.
    unfold in_futures.
    exists (phase_one_transitions s).
    split.
    apply phase_one_protocol.
    assumption.
    assumption.
    unfold phase_one_transitions.
    unfold phase_one_res.
    apply apply_action_last.
  Qed.
  
  Lemma phase_one_projections 
    (s : vstate X)
    (Hprss : protocol_state_prop _ s)
    (Hnf : no_component_fully_equivocating s index_listing)
    (i : index)
    (s' := phase_one_res s) :
    project (s' i) i = (s i).
  Proof.
    apply chain_updates_protocol.
    intuition.
    apply (proj1 Hfinite).
    intuition.
    apply ((proj2 Hfinite) i).
  Qed. 
  
  Lemma everything_in_projections 
    (s : vstate X)
    (Hprs : protocol_state_prop _ s)
    (Hnf : no_component_fully_equivocating s index_listing)
    (li : list index)
    (s' := phase_one_res s) :
    set_eq 
    (unite_observations (component_list s li))
    (unite_observations (zip_apply (List.map project (component_list s' li)) li)).
  Proof.
    split.
    - unfold incl.
      intros.
      unfold unite_observations in H.
      apply set_union_in_iterated in H.
      apply set_union_in_iterated.
      rewrite Exists_exists in *.
      destruct H as [x [Hinx Hinax]].
      rewrite in_map_iff in Hinx.
      destruct Hinx as [si [Heq Hinsi]].
      unfold component_list in Hinsi.
      rewrite in_map_iff in Hinsi.
      destruct Hinsi as [i [Heqi Hini]].
      exists (complete_observations (project (s' i) i)).
      split.
      rewrite in_map_iff.
      exists (project (s' i) i).
      split.
      reflexivity.
      apply In_nth_error in Hini.
      destruct Hini as [n Hn].
      apply in_zip_apply_if with (n0 := n).
      remember (component_list s' li) as f.
      rewrite nth_error_map.
      rewrite Heqf.
      unfold component_list.
      rewrite nth_error_map.
      rewrite Hn.
      simpl.
      reflexivity.
      assumption.
      unfold s'.
      rewrite phase_one_projections.
      rewrite Heqi.
      rewrite Heq.
      all : assumption.
    - unfold incl.
      intros.
      unfold unite_observations in *.
      apply set_union_in_iterated in H.
      apply set_union_in_iterated.
      rewrite Exists_exists in H.
      destruct H as [x [Hinx Hina]].
      rewrite in_map_iff in Hinx.
      destruct Hinx as [x0 [Heqx Hinx]].
      rewrite Exists_exists.
      apply in_zip_apply_if2 in Hinx.
      destruct Hinx as [pr [i [n H]]].
      exists (complete_observations (s i)).
      split.
      rewrite in_map_iff.
      exists (s i).
      intuition.
      unfold component_list.
      rewrite in_map_iff.
      exists i.
      intuition.
      apply nth_error_In in H.
      assumption.
      rewrite <- Heqx in Hina.
      assert (x0 = (s i)). {
        destruct H as [alfa [beta caroten]].
        rewrite nth_error_map in alfa.
        unfold component_list in alfa.
        rewrite nth_error_map in alfa.
        rewrite beta in alfa.
        simpl in alfa.
        inversion alfa.
        rewrite <- H0 in caroten.
        rewrite <- caroten.
        apply phase_one_projections.
        assumption.
        assumption.
      }
      rewrite H0 in Hina.
      assumption.
  Qed.
  
  Definition lift_to_receive_item (to from : index) (s : state): vaction_item (IM_index to) :=
    @Build_action_item _ (type (IM_index to)) receive (Some (from, s)).
  
  Definition sync_action (to from : index) (ls : list state) : (vaction X) := 
    let tmp := List.map (lift_to_receive_item to from) ls in
    List.map (lift_to_composite_action_item IM_index to) tmp.
  
  Definition sync (s : vstate X) (s': state) (to from : index) : option (vaction X) :=
    let history_s := get_history (s to) from in
    let history_s' := get_history s' from in
    let rem_states := complete_suffix history_s' history_s in
    match rem_states with
    | None => None
    | Some ss => let rem_action := sync_action to from (rev ss) in
                 Some rem_action
    end.
    
   Lemma one_sender_receive_protocol
    (s s': vstate X)
    (Hpr : protocol_state_prop X s)
    (Hpr' : protocol_state_prop X s')
    (to inter from :index)
    (Hdif : to <> from)
    (a : vaction X)
    (Hsync : sync s (s' inter) to from = Some a) :
    let res := snd (apply_action X s a) in
    finite_protocol_action_from X s a /\
    (project (res to) from = project (s' inter) from).
   Proof. 
    generalize dependent s.
    induction a.
    - intros. simpl in *.
      unfold finite_protocol_action_from. simpl.
      split.
        + apply finite_ptrace_empty.
          assumption. 
        + unfold res.
          unfold sync in Hsync.
          destruct (complete_suffix (get_history (s' inter) from) (get_history (s to) from)) eqn : eq_cs.
          2 : discriminate Hsync.
          apply complete_suffix_correct in eq_cs.
          assert (l = []). {
            inversion Hsync.
            assert (length l = 0). {
              assert (length (sync_action to from (rev l)) = 0). {
                apply length_zero_iff_nil. assumption.
              }
              unfold sync_action in H.
              rewrite map_length in H.
              rewrite map_length in H.
              rewrite rev_length in H.
              assumption.
            }
            apply length_zero_iff_nil. assumption.
          }
          rewrite H in eq_cs.
          simpl in eq_cs.
          symmetry in eq_cs.
          apply (@eq_history_eq_project index index_listing Hfinite) in eq_cs.
          assumption.
    - intros. simpl in *.
      
      replace (a :: a0) with ([a] ++ a0). 2: auto.
      rewrite <- finite_protocol_action_from_app_iff.
      
      unfold sync in Hsync.
      destruct (complete_suffix (get_history (s' inter) from) (get_history (s to) from)) eqn : eq_cs. 2: discriminate Hsync.
      
      inversion Hsync.
      unfold sync_action in H0.
      apply map_eq_cons in H0.
      destruct H0 as [a1 [tl [H0 [Hh Htl]]]].
      apply map_eq_cons in H0.
      destruct H0 as [sa [tls [H0 [Hh' Htl']]]].
      assert (eq_cs_orig := eq_cs).
      apply complete_suffix_correct in eq_cs.
      replace (sa :: tls) with ([sa] ++ tls) in H0. 2: auto.
      apply rev_eq_app in H0. simpl in H0.
      
      rewrite H0 in eq_cs.
      assert (eq_cs' := eq_cs).
      rewrite <- app_assoc in eq_cs.
      apply (@unfold_history index index_listing Hfinite) in eq_cs.
      
      assert (Hecs: project (s to) from = project sa from). {
        apply (@eq_history_eq_project index index_listing Hfinite _ (s to) sa from).
        assumption.
      }
      
      assert (Hinsa: In sa (get_history (s' inter) from)). {
        rewrite eq_cs'.
        rewrite <- app_assoc.
        apply in_elt.
      }
      
      destruct a.
      destruct (vtransition X label_a (s, input_a)) eqn : eq_vtrans. simpl.
      
      unfold lift_to_receive_item in Hh'.
      rewrite <- Hh' in Hh.
      unfold lift_to_composite_action_item in Hh.
      
      assert (Hinp: input_a = Some (from, sa)). {
        inversion Hh.
        reflexivity.
      }
      
      assert (protocol_transition X label_a (s, input_a) (s0, o)). {
        unfold protocol_transition.
        repeat split.
        - assumption.
        - subst input_a.
          apply option_protocol_message_Some.
          destruct (decide (inter = from)).
          + specialize (sent_component_protocol_composed IM_index i0 (free_constraint IM_index) has_been_sent_capabilities (fun m => Some (fst m)) s') as Hope.
            spec Hope. assumption.
            specialize (Hope inter (from, sa)).
            apply Hope.
            unfold has_been_sent.
            unfold has_been_sent_capabilities.
            unfold has_been_sent_lv.
            unfold send_oracle; simpl.
            rewrite decide_True.
            apply Is_true_eq_left. 
            rewrite existsb_exists.
            exists sa.
            split.
            rewrite <- e in Hinsa.
            rewrite <- e.
            assumption.
            unfold state_eqb. rewrite eq_dec_if_true. all : auto.
          + specialize (received_component_protocol_composed IM_index i0 (free_constraint IM_index) (fun m => Some (fst m)) has_been_received_capabilities s') as Hope.
            spec Hope. assumption.
            specialize (Hope inter (from, sa)).
            apply Hope.
            unfold has_been_received.
            unfold has_been_received_capabilities.
            unfold has_been_received_lv.
            unfold receive_oracle; simpl.
            rewrite decide_False.
            apply Is_true_eq_left.
            apply existsb_exists.
            exists sa.
            split.
            assumption.
            unfold state_eqb. rewrite eq_dec_if_true. all : auto.
        - simpl in *.
          inversion Hh.
          unfold vvalid.
          apply (@no_bottom_in_history index index_listing Hfinite) in Hinsa.
          unfold valid. simpl.
          repeat split.
          assumption.
          assumption.
          assumption.
        - assumption.
      }
      
      subst input_a.
      unfold res.
      
      specialize (IHa s0).
      spec IHa.
      apply protocol_transition_destination in H.
      assumption.
      
      assert (Honefold: get_history (s0 to) from = [sa] ++ get_history (s to) from). {
          assert (project (s0 to) from = sa). {
              unfold protocol_transition in H.
              unfold vtransition in eq_vtrans.
              unfold transition in eq_vtrans.
              inversion Hh.
              rewrite <- H2 in eq_vtrans.
              simpl in eq_vtrans.
              unfold vtransition in eq_vtrans.
              unfold transition in eq_vtrans.
              simpl in eq_vtrans.
              inversion eq_vtrans.
              rewrite state_update_eq.
              apply (@project_same index index_listing Hfinite).
              apply protocol_state_component_no_bottom.
              assumption.
          }
            rewrite <- H1. simpl.
            rewrite eq_cs.
            rewrite <- H1.
            apply (@unfold_history_cons index index_listing Hfinite).
            rewrite H1.
            apply (@no_bottom_in_history index index_listing Hfinite) in Hinsa.
            assumption.
        }
        
      spec IHa. {
        unfold sync.
        destruct (complete_suffix (get_history (s' inter) from) (get_history (s0 to) from)) eqn : eq_cs2.
        f_equal.
          unfold sync_action.
          rewrite <- Htl.
          rewrite <- Htl'.
          repeat f_equal.
          apply complete_suffix_correct in eq_cs2.
          rewrite Honefold in eq_cs2.
          rewrite eq_cs' in eq_cs2.
          rewrite app_assoc in eq_cs2.
          apply app_inv_tail in eq_cs2.
          apply app_inj_tail in eq_cs2.
          destruct eq_cs2.
          rewrite <- H1.
          apply rev_involutive.
        + rewrite Honefold in eq_cs2.
          rewrite eq_cs' in eq_cs2.
          rewrite <- app_assoc in eq_cs2.
          assert (complete_suffix (rev tls ++ [sa] ++ get_history (s to) from)
           ([sa] ++ get_history (s to) from) = Some (rev tls)). {
            apply complete_suffix_correct.
            reflexivity.  
          }
          rewrite H1 in eq_cs2.
          discriminate eq_cs2.
      }
    
      repeat split.
      + unfold finite_protocol_action_from.
        unfold apply_action. simpl in *.
        rewrite eq_vtrans. simpl.
        apply finite_ptrace_extend.
        apply finite_ptrace_empty.
        apply protocol_transition_destination in H. 
        assumption.
        assumption.
      + unfold apply_action. simpl.
        rewrite eq_vtrans. simpl.
        apply IHa.
      + destruct IHa as [_ IHa].
        rewrite <- IHa.
        f_equal.
        unfold apply_action. simpl.
        rewrite fold_right_app. simpl.
        rewrite eq_vtrans. simpl.
        specialize (@apply_action_folder_additive _ X s0 (rev a0) [{| l := label_a; input := Some (from, sa); destination := s0; output := o |}]) as Hadd.
        destruct (@fold_right
         (prod (@vstate (@message index index_listing) X)
            (list (@vtransition_item (@message index index_listing) X)))
         (@vaction_item (@message index index_listing) X)
         (@apply_action_folder (@message index index_listing) X)
         (@pair (@_composite_state (@message index index_listing) index IM_index)
            (list
               (@transition_item (@message index index_listing)
                  (@composite_type (@message index index_listing) index IM_index))) s0
            (@cons
               (@transition_item (@message index index_listing)
                  (@composite_type (@message index index_listing) index IM_index))
               (@Build_transition_item (@message index index_listing)
                  (@composite_type (@message index index_listing) index IM_index) label_a
                  (@Some (prod index (@state index index_listing))
                     (@pair index (@state index index_listing) from sa)) s0 o)
               (@nil (@vtransition_item (@message index index_listing) X))))
         (@rev (@vaction_item (@message index index_listing) X) a0)) as (tr, dest) eqn : eqf1.
         destruct (@fold_right
         (prod (@vstate (@message index index_listing) X)
            (list (@vtransition_item (@message index index_listing) X)))
         (@vaction_item (@message index index_listing) X)
         (@apply_action_folder (@message index index_listing) X)
         (@pair (@vstate (@message index index_listing) X)
            (list (@vtransition_item (@message index index_listing) X)) s0
            (@nil (@vtransition_item (@message index index_listing) X)))
         (@rev (@vaction_item (@message index index_listing) X) a0)) as (tr', dest') eqn : eqf2.
         simpl.
         replace (@fold_right
            (prod (@vstate (@message index index_listing) X)
               (list (@vtransition_item (@message index index_listing) X)))
            (@vaction_item (@message index index_listing) X)
            (@apply_action_folder (@message index index_listing) X)
            (@pair (@_composite_state (@message index index_listing) index IM_index)
               (list
                  (@transition_item (@message index index_listing)
                     (@composite_type (@message index index_listing) index IM_index))) s0
               (@cons
                  (@transition_item (@message index index_listing)
                     (@composite_type (@message index index_listing) index IM_index))
                  (@Build_transition_item (@message index index_listing)
                     (@composite_type (@message index index_listing) index IM_index) label_a
                     (@Some (prod index (@state index index_listing))
                        (@pair index (@state index index_listing) from sa)) s0 o)
                  (@nil (@vtransition_item (@message index index_listing) X))))
            (@rev (@vaction_item (@message index index_listing) X) a0)) with 
            (@pair (@vstate (@message index index_listing) X)
            (list (@vtransition_item (@message index index_listing) X)) tr'
            (@app (@vtransition_item (@message index index_listing) X) dest'
               (@cons
                  (@transition_item (@message index index_listing)
                     (@type (@message index index_listing) X))
                  (@Build_transition_item (@message index index_listing)
                     (@type (@message index index_listing) X) label_a
                     (@Some (prod index (@state index index_listing))
                        (@pair index (@state index index_listing) from sa)) s0 o)
                  (@nil
                     (@transition_item (@message index index_listing)
                        (@type (@message index index_listing) X)))))) in eqf1.
            inversion eqf1.
            reflexivity.
    Qed.
   
    Definition get_candidates 
      (s : vstate X) :
      list state 
      :=
    component_list s index_listing.
    
    Definition get_topmost_candidates
      (s : vstate X)
      (target : index) :
      list state 
      :=
      get_maximal_elements (fun s s' => state_ltb' target (project s target) (project s' target)) (get_candidates s).
      
    Definition get_matching_state
      (s : vstate X)
      (to from : index) : state :=
      let candidates := (get_topmost_candidates s from) in
      let found := List.find (fun s' => state_ltb' from (project (s to) from) s') candidates in
      match found with
      | Some s' => s'
      | None => (s to)
      end.
      
    Definition get_matching_action
      (s : vstate X)
      (from to : index) : vaction X :=
      let s' := get_matching_state s to from in
      match (sync s s' to from) with
      | None => []
      | Some a => a
      end.
      
    Lemma sync_some 
      (s : vstate X)
      (from to : index) :
      sync s (get_matching_state s to from) to from <> None.
    Proof.
      intros contra.
      unfold get_matching_state in contra.
      destruct (find (fun s' : state => state_ltb' from (project (s to) from) s')
               (get_topmost_candidates s from)) eqn : eq_find.
      - apply find_some in eq_find.
        destruct eq_find as [_ eq_find].
        unfold sync in contra.
        destruct (complete_suffix (get_history s0 from) (get_history (s to) from)) eqn : eq_suf.
        discriminate contra.
        unfold state_ltb' in eq_find.
        apply in_correct in eq_find.
        assert (eq_find' := eq_find).
        apply in_split in eq_find.
        destruct eq_find as [pref [suff Heq]].
        apply (@unfold_history index index_listing) in Heq as Hsufhist.
        rewrite Hsufhist in Heq.
        apply complete_suffix_correct in Heq.
        assert ((project (s to) from :: get_history (project (s to) from) from) = get_history (s to) from). {
          symmetry.
          apply (@unfold_history_cons index index_listing).
          assumption.
          apply (@no_bottom_in_history index index_listing Hfinite idec s0 _ from).
          intuition.
        }
        rewrite H in Heq.
        rewrite Heq in eq_suf.
        discriminate eq_suf.
        intuition.
       - unfold sync in contra.
         destruct (complete_suffix (get_history (s to) from) (get_history (s to) from)) eqn : eq_suf.
         + discriminate contra.
         + assert (get_history (s to) from = [] ++ (get_history (s to) from)). {
            intuition.
           }
           apply complete_suffix_correct in H.
           rewrite H in eq_suf.
           discriminate eq_suf. 
    Qed.
    
    Lemma get_matching_action_effect 
      (s : vstate X)
      (Hprs : protocol_state_prop X s)
      (s' : state)
      (from to : index)
      (Hdif : from <> to)
      (Hmatch : get_matching_state s to from = s') :
      let res := snd (apply_action X s (get_matching_action s from to)) in
      finite_protocol_action_from X s (get_matching_action s from to) /\
      project (res to) from = project s' from.
    Proof.
      simpl.
      unfold get_matching_action.
      rewrite Hmatch.
      destruct (sync s s' to from) eqn : eq_sync.
      - unfold sync in eq_sync.
        destruct (complete_suffix (get_history s' from) (get_history (s to) from)) eqn : eq_suf.
        2 : discriminate eq_sync.
        assert (eq_suf_original := eq_suf).
        apply complete_suffix_correct in eq_suf.
        inversion eq_sync.
        specialize (one_sender_receive_protocol s s Hprs Hprs to) as Hone.
        unfold get_matching_state in Hmatch.
        destruct (find (fun s' : state => state_ltb' from (project (s to) from) s')
             (get_topmost_candidates s from)) eqn : eq_find.
        + apply find_some in eq_find.
          destruct eq_find as [eq_find _].
          unfold get_topmost_candidates in eq_find.
          unfold get_maximal_elements in eq_find.
          apply filter_In in eq_find.
          destruct eq_find as [eq_find _].
          unfold get_candidates in eq_find.
          unfold component_list in eq_find.
          apply in_map_iff in eq_find.
          destruct eq_find as [inter [Hinter _]].
          
          specialize (Hone inter from).
          spec Hone. {
            intuition.
          }
          
          specialize (Hone (sync_action to from (rev l))).
          
          spec Hone. {
             unfold sync.
             rewrite <- Hmatch in eq_suf_original.
             rewrite <- Hinter in eq_suf_original.
             rewrite eq_suf_original.
             reflexivity.
          }
          simpl in Hone.
          rewrite <- Hmatch.
          rewrite <- Hinter.
          apply Hone.
        + rewrite <- Hmatch.
          rewrite <- Hmatch in eq_suf.
          assert (Hempty: l = []). {
            replace (get_history (s to) from) with ([] ++ (get_history (s to) from)) in eq_suf at 1.
            apply app_inv_tail in eq_suf.
            all : intuition.
          }
          rewrite Hempty.
          simpl.
          unfold sync_action; simpl.
          intuition.
          apply finite_protocol_action_empty.
          assumption.
      - rewrite <- Hmatch in eq_sync.
        apply sync_some in eq_sync.
        intuition. 
    Qed.
    
    Lemma get_matching_action_index
      (s : vstate X)
      (from to : index)
      (ai : action_item)
      (Hin : In ai (get_matching_action s from to)) :
      (projT1 (label_a ai) = to).
    Proof.
      unfold get_matching_action in Hin.
      remember (get_matching_state s to from) as s0.
      destruct (sync s s0 to from) eqn : eq_sync.
        + unfold sync in eq_sync.
          destruct (complete_suffix (get_history s0 from) (get_history (s to) from)).
          inversion eq_sync.
          unfold sync_action in H0.
          rewrite <- H0 in Hin.
          apply in_map_iff in Hin.
          destruct Hin as [x [Hlift Hinx]].
          unfold lift_to_composite_action_item in Hlift.
          rewrite <- Hlift.
          destruct x. simpl. reflexivity.
          discriminate eq_sync.
        + contradict Hin.
    Qed.
    
    Definition get_receives_for
      (s : vstate X)
      (li : list index)
      (from : index) : vaction X :=
      let matching_actions := List.map (get_matching_action s from) li in
      List.concat matching_actions.
      
    Lemma get_receives_for_correct
        (s : vstate X)
        (Hpr : protocol_state_prop X s)
        (li : list index)
        (from : index)
        (Hnodup : NoDup li)
        (Hnf : ~ In from li) :
        let res := snd (apply_action X s (get_receives_for s li from)) in
        finite_protocol_action_from X s (get_receives_for s li from) /\
        forall (i : index), In i li -> project (res i) from = project (get_matching_state s i from) from. 
    Proof.
      induction li; intros.
      - unfold get_receives_for. simpl.
        split.
        apply finite_protocol_action_empty.
        assumption.
        intuition.
      - unfold get_receives_for.
        rewrite map_cons. simpl.
        unfold get_receives_for in IHli.
        apply not_in_cons in Hnf.
        destruct Hnf as [Hnfa Hnfli].
        apply NoDup_cons_iff in Hnodup as Hnodup'.
        
        specialize (@action_independence _ X (get_matching_action s from a) (concat (map (get_matching_action s from) li))) as Hind.
        
        remember (fun s' => forall (i : index), In i li -> (s' i) = (s i)) as Pb.
        
        specialize (Hind Pb s).
        
        spec Hind. {
          assumption.
        }
        
        assert (Hfrs : finite_protocol_action_from X s (get_matching_action s from a)). {
          apply get_matching_action_effect with (s' := (get_matching_state s a from)).
          all : intuition.
        }
        
        spec Hind. { 
          auto.
        }
        
        spec Hind. {
          rewrite HeqPb. intros.
          reflexivity.
        }
        
        specialize (@relevant_components (@message index index_listing) index idec IM_index) as Hrel.
        specialize (Hrel i0 s).
        
        assert (Hincl: incl
               (map (projT1 (P:=fun n : index => vlabel (IM_index n)))
               (map label_a (concat (map (get_matching_action s from) li)))) li). {
          unfold incl. intros.
          rewrite in_map_iff in H.
          destruct H as [x [Hproj Hinx]].
          apply in_map_iff in Hinx.
          destruct Hinx as [x0 [H_label Hincon]].
          apply in_concat in Hincon.
          destruct Hincon as [y [Hiny Hinx0]].
          rewrite in_map_iff in Hiny.
          destruct Hiny as [z [Hmatching Hindex]].
          rewrite <- H_label in Hproj.
          unfold free_composite_vlsm.
          assert (a0 = z). {
            rewrite <- Hproj.
            apply get_matching_action_index with (s := s) (from := from).
            rewrite <- Hmatching in Hinx0.
            assumption.
          }
          rewrite H.
          assumption.
       }
        
        (* ensures *)
        
        spec Hind save. {
          unfold ensures. intros.
          rewrite HeqPb in H0.
          apply Hrel with (li := li).
          assumption.
          assumption.
          unfold incl. intros.
          rewrite in_map_iff in H1.
          destruct H1 as [x [Hproj Hinx]].
          rewrite in_map_iff in Hinx.
          destruct Hinx as [x0 [H_label Hincon]].
          apply in_concat in Hincon.
          destruct Hincon as [y [Hiny Hinx0]].
          rewrite in_map_iff in Hiny.
          destruct Hiny as [z [Hmatching Hindex]].
          rewrite <- H_label in Hproj.
          unfold free_composite_vlsm.
          assert (a0 = z). {
            rewrite <- Hproj.
            apply get_matching_action_index with (s := s) (from := from).
            rewrite <- Hmatching in Hinx0.
            assumption.
          }
          rewrite H1.
          assumption.
          apply IHli.
          all : intuition.
        }
        
        (* preserves *)
        
        spec Hind save. {
          rewrite HeqPb.
          unfold preserves.
          intros.
          specialize (Hrel s0).
          specialize (H0 i H3).
          rewrite <- H0.
          apply irrelevant_components.
          intros contra.
          rewrite in_map_iff in contra.
          destruct contra as [x [Hproj Hinx]].
          rewrite in_map_iff in Hinx.
          destruct Hinx as [x0 [Hlabel Hinx0]].
          apply get_matching_action_index in Hinx0.
          rewrite <- Hlabel in Hproj.
          assert (a = i). {
            rewrite <- Hproj.
            rewrite <- Hinx0.
            intuition.
          }
          rewrite <- H4 in H3.
          intuition.
        }
        split. 
        + intuition.
        + intros.
          unfold res.
          unfold get_receives_for.
          simpl.
          rewrite apply_action_app.
          destruct (apply_action X s (get_matching_action s from a)) as (tr0, res0) eqn : eq_first.
          destruct (apply_action X res0 (concat (map (get_matching_action s from) li))) as (tr, res') eqn : eq_second.
          simpl.
          destruct H1.
          rewrite <- H1.
          * assert (project (res0 a) from = project (get_matching_state s a from) from). {
              specialize (get_matching_action_effect s Hpr (get_matching_state s a from) from a) as Heff.
              spec Heff. {
                intuition.
              }
              spec Heff. {
                intuition.
              }
              simpl in Heff.
              replace res0 with (snd (apply_action X s (get_matching_action s from a))).
              apply Heff.
              rewrite eq_first; intuition.
            }
            rewrite <- H2.
            
            assert ((res' a) = (res0 a)). {
              replace res' with (snd (apply_action X res0 (concat (map (get_matching_action s from) li)))).
              apply irrelevant_components.
              intros contra.
              rewrite in_map_iff in contra.
              destruct contra as [x [Hproj Hinx]].
              rewrite in_map_iff in Hinx.
              destruct Hinx as [x0 [Hl Hinx0]].
              apply in_concat in Hinx0.
              destruct Hinx0 as [x' [Hinx' Hinx0']].
              rewrite in_map_iff in Hinx'.
              destruct Hinx' as [j [Hmatch Hli]].
              rewrite <- Hl in Hproj.
              rewrite <- Hmatch in Hinx0'.
              apply get_matching_action_index in Hinx0'.
              replace (@projT1 index (fun n : index => @vlabel (@message index index_listing) (IM_index n))
              (@label_a (@message index index_listing) (@type (@message index index_listing) X)
                 x0)) with a in Hinx0'.
              rewrite <- Hinx0' in Hli.
              intuition.
              rewrite eq_second.
              intuition.
            }
            rewrite H3; intuition.
         * clear Hind.
           replace res' with (snd (apply_action X res0 (concat (map (get_matching_action s from) li)))).
           spec IHli. { intuition. }
           spec IHli. { intuition. }
           destruct IHli as [left IHli].
           specialize (IHli i H1).
           rewrite <- IHli.
           assert (forall (i : index), In i li -> res0 i = s i). {
            intros.
            replace res0 with (snd (apply_action X s (get_matching_action s from a))).
            apply irrelevant_components.
            intros contra. 
            apply in_map_iff in contra.
            destruct contra as [x [y contra]].
            apply in_map_iff in contra.
            destruct contra as [x0 [Hl Hinx0]].
            apply get_matching_action_index in Hinx0.
            rewrite <- Hl in y.
            replace (@projT1 index (fun n : index => @vlabel (@message index index_listing) (IM_index n))
             (@label_a (@message index index_listing) (@type (@message index index_listing) X) x0))
             with i1 in Hinx0.
             rewrite Hinx0 in H2.
             intuition.
             rewrite eq_first; intuition.
           }
           
           f_equal.
           specialize (Hrel res0).
           spec Hrel. {
             replace res0 with (snd (apply_action X s (get_matching_action s from a))).
             apply apply_action_last_protocol.
             assumption.
             assumption.
             rewrite eq_first; intuition.
           }
           
           specialize (Hrel (concat (map (get_matching_action s from) li))).
           simpl in Hrel.
           specialize (Hrel li).
           spec Hrel. {
             assumption.
           }
           
           spec Hrel. {
            assumption.
           }
           
           spec Hrel. {
            assumption.
           }
           
           simpl in Hrel.
           destruct Hrel as [_ Hrel].
           specialize (Hrel i).
           spec Hrel. {
            intuition.
           }
           apply Hrel.
           rewrite eq_second; intuition.
    Qed.
    
    Definition is_receive_action
      (a : vaction X) : Prop := 
      let labels_a := List.map label_a a in
      let label_types := List.map (fun (l : vlabel X) => let (i, li) := l in li) labels_a in
      forall (l : label_list), In l label_types -> l = receive.
    
    Definition is_receive_action_app
      (a b : vaction X) :
      is_receive_action (a ++ b) <-> is_receive_action a /\ is_receive_action b.
    Proof.
    Admitted.
    
    Lemma message_providers_receive
      (s : vstate X)
      (i : index) :
      get_message_providers_from_action (get_receives_for s (others i) i) = [i].
    Proof.
    Admitted.
    
    Lemma get_matching_action_is_receive_action
      (s : vstate X)
      (from to : index) :
      is_receive_action (get_matching_action s from to).
    Proof.
      unfold is_receive_action; intros.
      apply in_map_iff in H.
      destruct H as [x [Hlabel Hinx]].
      destruct x as [i x].
      apply in_map_iff in Hinx.
      destruct Hinx as [x0 [Hlabel_a Hinx0]].
      destruct x0 as [lable_x0 input_x0] eqn : eq_x0.
      
      unfold get_matching_action in Hinx0.
      destruct (sync s (get_matching_state s to from) to from) eqn : eq_sync.
      - unfold sync in eq_sync.
        destruct (complete_suffix (get_history (get_matching_state s to from) from) (get_history (s to) from)) eqn : eq_c.
        + inversion eq_sync.
          admit.
       + discriminate eq_sync.
    - simpl in Hinx0.
      intuition.
    Admitted.
    
    Lemma receive_for_is_receive_action 
      (s : vstate X)
      (from : index)
      (li : list index) :
      is_receive_action (get_receives_for s li from).
    Proof.
      unfold is_receive_action.
      unfold get_receives_for.
      intros.
      rewrite in_map_iff in H.
      destruct H as [x [Hlabel Hinx]].
      rewrite in_map_iff in Hinx.
      destruct Hinx as [x0 [Heqlabel Hinx0]].
      destruct x0.
      destruct x.
      apply in_concat in Hinx0.
      destruct Hinx0 as [x1 [Hinx1 Hinx1']].
      rewrite in_map_iff in Hinx1.
      destruct Hinx1 as [x2 [Heqmatch Hinx2]].
      
      unfold get_matching_action in Heqmatch.
    Admitted.
    
    Lemma receives_neq
      (s : vstate X)
      (Hpr : protocol_state_prop X s)
      (a : vaction X) 
      (Hpra : finite_protocol_action_from X s a)
      (i j : index)
      (providers := get_message_providers_from_action a)
      (Hreceive : is_receive_action a)
      (Hj : ~ In j providers) 
      (res := snd (apply_action X s a)) :
      project (res i) j = project (s i) j.
    Proof.
      induction a using rev_ind.
      - intuition.
      - apply finite_protocol_action_from_app_iff in Hpra.
      
        destruct Hpra as [Hpra_long Hpra_short].
        specialize (IHa Hpra_long); simpl in *.
        apply is_receive_action_app in Hreceive.
        
        destruct Hreceive as [Hreceive_long Hreceive_short].
        specialize (IHa Hreceive_long); simpl.
        
        spec IHa. {
          clear -Hj.
          intros contra.
          contradict Hj.
          unfold providers.
          unfold get_message_providers_from_action in *.
          unfold messages_a in *.
          rewrite map_app.
          rewrite cat_option_app.
          rewrite map_app.
          apply in_app_iff.
          left. intuition.
        }
        
        rewrite <- IHa.
        unfold res.
        rewrite apply_action_app.
        destruct (apply_action X s a) as [tr_long res_long].
        simpl in *.
        unfold apply_action.
        unfold apply_action_folder.
        destruct x. simpl.
        destruct (vtransition X label_a (res_long, input_a)) eqn : eq_trans.
        simpl.
        
        unfold finite_protocol_action_from in Hpra_short.
        unfold apply_action in Hpra_short.
        unfold apply_action_folder in Hpra_short.
        simpl in Hpra_short.
        rewrite eq_trans in Hpra_short.
        simpl in Hpra_short.
        inversion Hpra_short.
        
        unfold protocol_transition in H6.
        destruct H6 as [Hprtr Htrans].
        
        unfold vtransition in eq_trans.
        unfold transition in eq_trans.
        simpl in eq_trans.
        unfold vtransition in eq_trans.
        unfold transition in eq_trans.
        simpl in eq_trans.
        remember label_a as label_a'.
        destruct label_a as [idx li].
        
        destruct li eqn : eq_li.
        + unfold is_receive_action in Hreceive_short.
          specialize (Hreceive_short li).
          spec Hreceive_short. {
            apply in_map_iff.
            exists label_a'. simpl. intuition.
            rewrite Heqlabel_a'.
            intuition.
          }
          rewrite eq_li in Hreceive_short.
          discriminate Hreceive_short.
        + destruct input_a eqn : eq_input.
          * rewrite Heqlabel_a' in eq_trans.
            inversion eq_trans.
            destruct (decide (i = idx)).
            -- rewrite e. rewrite state_update_eq.
              rewrite (@project_different index index_listing).
              reflexivity.
              intuition.
              intros contra. {
                clear -Hj contra.
                unfold providers in Hj.
                unfold get_message_providers_from_action in Hj.
                rewrite contra in Hj.
                contradict Hj.
                apply in_map_iff.
                exists m. intuition.
                unfold messages_a.
                rewrite map_app.
                rewrite cat_option_app.
                rewrite in_app_iff.
                right; simpl; intuition.
              }
              clear -Hprtr.
              apply protocol_state_component_no_bottom.
              unfold protocol_valid in Hprtr.
              intuition.
          -- rewrite state_update_neq.
             reflexivity.
             assumption.
         * unfold protocol_valid in Hprtr.
           unfold valid in Hprtr.
           rewrite Heqlabel_a' in Hprtr.
           simpl in Hprtr.
           unfold constrained_composite_valid in Hprtr.
           unfold free_constraint in Hprtr.
           unfold free_composite_valid in Hprtr.
           unfold vvalid in Hprtr.
           unfold valid in Hprtr.
           simpl in Hprtr.
           intuition.
    Qed.
    
    Lemma relevant_component_transition_lv
      (s s' : vstate X)
      (Hprs : protocol_state_prop X s)
      (Hprs' : protocol_state_prop X s') 
      (l : vlabel X)
      (input : message)
      (i := projT1 l)
      (Hsame : project (s i) (fst input) = project (s' i) (fst input))
      (Hvalid: protocol_valid X l (s, Some input)) :
      protocol_valid X l (s', Some input).
    Proof.
      unfold protocol_valid in *.
      intuition.
      clear X0 X1.
      unfold valid in *.
      simpl in *.
      unfold constrained_composite_valid in *.
      unfold free_composite_valid in *.
      unfold vvalid in *.
      intuition.
      unfold valid in *.
      unfold machine in *.
      simpl in *.
      destruct l as [j lj].
      destruct lj eqn : eq_lj.
      - destruct H0 as [_ Hd].
        discriminate Hd.
      - intuition.
        simpl in i.
        subst i.
        rewrite <- Hsame.
        assumption.
    Qed.
    
    Lemma relevant_components_lv
      (s s' : vstate X)
      (Hprs : protocol_state_prop X s)
      (Hprs' : protocol_state_prop X s')
      (a : vaction X)
      (Hrec : is_receive_action a)
      (Hpr : finite_protocol_action_from X s a)
      (f : index)
      (Hli : incl (get_message_providers_from_action a) [f])
      (Hsame : forall (i : index), project (s i) f = project (s' i) f) :
      let res' := snd (apply_action X s' a) in
      let res := snd (apply_action X s a) in 
      finite_protocol_action_from X s' a /\ 
      forall (i : index), project (res' i) f = project (res i) f.
    Proof.
      induction a using rev_ind.
      - simpl. 
        split. apply finite_protocol_action_empty.
        assumption.
        intros.
        specialize (Hsame i).
        intuition.
      - simpl.
        
        apply is_receive_action_app in Hrec.
        destruct Hrec as [Hrec_long Hrec_short].
        apply finite_protocol_action_from_app_iff in Hpr.
        destruct Hpr as [Hpr_long Hpr_short].
        
        rewrite apply_action_app.
        destruct (apply_action X s' a) as (tr_long', res_long') eqn : eq_long'.
        destruct (apply_action X res_long' [x]) as (tr_short', res_short') eqn : eq_short'.
        simpl.
        
        spec IHa. {
          assumption.
        }
        
        spec IHa. {
          assumption.
        }
        
        spec IHa. {
          clear -Hli.
          unfold get_message_providers_from_action in *.
          unfold messages_a in *.
          unfold incl in *.
          rewrite map_app in Hli.
          rewrite cat_option_app in Hli.
          rewrite map_app in Hli.
          intros.
          specialize (Hli a0).
          apply Hli.
          apply in_app_iff; left; intuition.
        }
        
        simpl in IHa.
        destruct IHa as [Iha_pr Iha_proj].
        
        rewrite apply_action_app.
        destruct (apply_action X s a) as (tr_long, res_long) eqn : eq_long.
        destruct (apply_action X res_long [x]) as (tr_short, res_short) eqn : eq_short.
        simpl in *.
        
        assert (res_long = snd (apply_action X s a)). {
          rewrite eq_long.
          intuition.
        }
        
        assert (res_short = snd (apply_action X res_long [x])). {
          rewrite eq_short.
          intuition.
        }
        
        assert (res_long' = snd (apply_action X s' a)). {
          rewrite eq_long'.
          intuition.
        }
        
        assert (res_short' = snd (apply_action X res_long' [x])). {
          rewrite eq_short'.
          intuition.
        }
          
        replace res_short' with (snd (apply_action X res_long' [x])).
        replace res_short with (snd (apply_action X res_long [x])).
        
        unfold apply_action.
        unfold apply_action_folder.
        destruct x as [label_x input_x].
        simpl.
       
        
        assert (Hprs_long : protocol_state_prop X res_long). {
          rewrite H.
          apply apply_action_last_protocol.
          assumption.
          assumption.
        }
        
        assert (Hprs'_long : protocol_state_prop X res_long'). {
          rewrite H1.
          apply apply_action_last_protocol.
          assumption.
          assumption.
        } 
        
        destruct (vtransition X label_x (res_long', input_x)) eqn : trans'.
        destruct (vtransition X label_x (res_long, input_x)) eqn : trans.
        simpl.
        
        unfold finite_protocol_action_from in Hpr_short.
        unfold apply_action in Hpr_short.
        unfold apply_action_folder in Hpr_short.
        simpl in Hpr_short.
        rewrite trans in Hpr_short.
          
        inversion Hpr_short.
        remember H10 as Hprotocol_trans.
        unfold protocol_transition in H10.
        destruct H10 as [Hprotocol_valid Htrans].
        
        unfold vtransition in trans, trans'.
        unfold transition in trans, trans'.
        simpl in *.
        unfold vtransition in trans, trans'.
        destruct label_x as [j label_x].
        simpl in trans, trans'.
        
        destruct label_x eqn : eq_label.
        { 
          clear -Hrec_short eq_label.
            unfold is_receive_action in Hrec_short.
            simpl in Hrec_short.
            specialize (Hrec_short label_x).
            spec Hrec_short. {
              intuition.
            }
          rewrite eq_label in Hrec_short.
          discriminate Hrec_short.
       }
       
        destruct input_x eqn : eq_input.
        2 : {
          unfold protocol_valid in Hprotocol_valid.
          unfold constrained_composite_valid in Hprotocol_valid.
          unfold free_composite_valid in Hprotocol_valid. 
          unfold vvalid in Hprotocol_valid.
          unfold valid in Hprotocol_valid.
          simpl in Hprotocol_valid.
          destruct Hprotocol_valid as [e [b [c d]]].
          intuition. 
        }
       
       assert (Hm : fst m = f). {
          clear -Hli eq_input.
          unfold incl in Hli.
          unfold get_message_providers_from_action in Hli.
          unfold messages_a in Hli.
          rewrite map_app in Hli.
          rewrite cat_option_app in Hli.
          rewrite map_app in Hli.
          specialize (Hli (fst m)).
          spec Hli. {
            simpl.
            apply in_app_iff.
            right.
            intuition.
          }
          simpl in Hli.
          intuition.
       }
       
        split.
        + apply finite_protocol_action_from_app_iff.
          split.
          * assumption.
          * unfold finite_protocol_action_from.
            assert (protocol_transition X (existT (fun n : index => vlabel (IM_index n)) j receive)
                    (snd (apply_action X s' a), Some m)
                    (state_update IM_index (snd (apply_action X s' a)) j
                    (update_state (snd (apply_action X s' a) j) (snd m) (fst m)), None)). {
             split.
             - destruct Hprotocol_trans as [Hprotocol_trans tmp].
               specialize (relevant_component_transition_lv res_long res_long') as Hrel.
               specialize (Hrel Hprs_long Hprs'_long (existT (fun n : index => vlabel (IM_index n)) j receive)).
               specialize (Hrel m).
               rewrite H1 in Hrel.
               apply Hrel.
               simpl.
               specialize (Iha_proj j).
               move Iha_proj at bottom.
               rewrite Hm.
               symmetry.
               rewrite <- H1.
               assumption.
               assumption.
            - unfold transition.
              unfold vlabel.
              unfold machine.
              simpl.
              reflexivity.
            }
            
            apply finite_ptrace_extend.
            apply finite_ptrace_empty.
            apply protocol_transition_destination in H10.
            assumption.
            assumption.
        + intros.
          specialize (Iha_proj i).
         * inversion trans.
           inversion trans'.
           destruct (decide (i = j)).
           -- rewrite e.
              rewrite state_update_eq.
              rewrite state_update_eq.
              rewrite e in Iha_proj.
              clear -Iha_proj Hprs_long Hprs'_long.
              destruct (decide ((fst m) = f)).
              ** rewrite e.
                 rewrite (@project_same index index_listing Hfinite).
                 rewrite (@project_same index index_listing Hfinite).
                 reflexivity.
                 all : (apply protocol_state_component_no_bottom; assumption).
              ** rewrite (@project_different index index_listing Hfinite).
                 rewrite (@project_different index index_listing Hfinite).
                 assumption.
                 intuition.
                 (apply protocol_state_component_no_bottom; assumption).
                 intuition.
                 (apply protocol_state_component_no_bottom; assumption).
          -- rewrite state_update_neq.
             rewrite state_update_neq.
             all : intuition.
    Qed.
    
    Definition get_receives_all
      (s : vstate X)
      (lfrom : set index) : vaction X :=
      let lis := (List.map others lfrom) in
      let receive_fors := zip_apply (List.map (get_receives_for s) lis) lfrom in
      List.concat receive_fors.
    
    Lemma get_receives_all_protocol
      (s : vstate X)
      (lfrom : set index)
      (Hnodup : NoDup lfrom)
      (Hprs : protocol_state_prop X s) :
      let res := snd (apply_action X s (get_receives_all s lfrom)) in 
      finite_protocol_action_from X s (get_receives_all s lfrom) /\
      forall (f i : index), In f lfrom -> i <> f -> project (res i) f = project (get_matching_state s i f) f.
    Proof.
      induction lfrom using rev_ind; unfold get_receives_all.
      - split; simpl. 
        + apply finite_protocol_action_empty. assumption.
        + intuition.
      - simpl.
      
        apply NoDup_rev in Hnodup.
        rewrite rev_unit in Hnodup.
        apply NoDup_cons_iff in Hnodup.
        destruct Hnodup as [notX Hnodup].
        apply NoDup_rev in Hnodup.
        rewrite rev_involutive in Hnodup.
        
        specialize (IHlfrom Hnodup).
        simpl in IHlfrom.
        
        destruct IHlfrom as [IHprotocol IHproject].
        rewrite map_app.
        rewrite map_app.
        rewrite zip_apply_app; simpl.
        
        2 : {
          repeat rewrite map_length.
          intuition.
        }
        
        rewrite concat_app; simpl.
        rewrite apply_action_app; simpl.
        
        destruct (@apply_action (@message index index_listing) X s
            (@concat (@vaction_item (@message index index_listing) X)
               (@zip_apply index (@vaction (@message index index_listing) X)
                  (@map (set index) (forall _ : index, @vaction (@message index index_listing) X)
                     (get_receives_for s) (@map index (set index) others lfrom)) lfrom))) as [tr_long res_long] eqn : eq_long.
        
        destruct (@apply_action (@message index index_listing) X res_long
            (@app (@vaction_item (@message index index_listing) X) (get_receives_for s (others x) x)
               (@nil (@vaction_item (@message index index_listing) X)))) as [tr_short res_short] eqn : eq_short.
        
        rewrite app_nil_r in *.
        simpl.
        
        assert (res_short = snd (apply_action X res_long (get_receives_for s (others x) x))). {
          rewrite eq_short.
          intuition.
        }
        
        assert (res_long = snd (apply_action X s (concat (zip_apply (map (get_receives_for s) (map others lfrom)) lfrom)))). {
          replace (@apply_action (@message index index_listing) X s
        (@concat (@vaction_item (@message index index_listing) X)
           (@zip_apply index (@vaction (@message index index_listing) X)
              (@map (list index) (forall _ : index, @vaction (@message index index_listing) X)
                 (get_receives_for s) (@map index (set index) others lfrom)) lfrom))) with (tr_long, res_long).
          intuition.
        }
        
        assert (Hrec_long : is_receive_action (concat (zip_apply (map (get_receives_for s) (map others lfrom)) lfrom))). {
          admit.
        }
        
        assert (Hrec_short : is_receive_action (get_receives_for s (others x) x)). {
          apply receive_for_is_receive_action.
        }
        
        assert (Hprs_long : protocol_state_prop X res_long). {
          rewrite H0.
          apply apply_action_last_protocol.
          assumption.
          assumption.
        }
        
        assert (Hx_after_long : forall (i : index), project (res_long i) x = project (s i) x). {
          intros.
          replace res_long with 
            (snd (apply_action X s (concat (zip_apply (map (get_receives_for s) (map others lfrom)) lfrom)))).
          apply receives_neq.
          assumption.
          assumption.
          assumption.
          
          intros contra.
          clear -contra.
          unfold get_message_providers_from_action in contra.
          rewrite in_map_iff in contra.
          destruct contra as [m [Hfs Hinm]].
          unfold messages_a in Hinm.
          apply in_cat_option in Hinm.
          destruct Hinm as [Hom [Hinom Hsome]].
          rewrite in_map_iff in Hinom.
          destruct Hinom as [ai [Hinput Hinconcat]].
          rewrite in_concat in Hinconcat.
          destruct Hinconcat as [a [Hina Hina2]].
          apply in_zip_apply_if2 in Hina.
          destruct Hina as [f [a0 [n Heq]]].
          destruct Heq as [H1 [H2 H3]].
          apply nth_error_In in H1.
          apply nth_error_In in H2.
          rewrite in_map_iff in H1.
          destruct H1 as [li [Hrec Hinx]].
          rewrite in_map_iff in Hinx.
          destruct Hinx as [idx [Hothers Hidxfrom]].
          rewrite <- Hrec in H3.
          admit.
        }
        
        assert (Hsource: finite_protocol_action_from X s (get_receives_for s (others x) x)). {
          apply get_receives_for_correct.
          assumption.
          apply NoDup_others.
          apply others_correct.
        }
        
        specialize (relevant_components_lv s res_long Hprs Hprs_long (get_receives_for s (others x) x)) as Hrel.
        specialize (Hrel Hrec_short Hsource x).
        
        spec Hrel. {
          rewrite message_providers_receive.
          intuition.
        }
        
        spec Hrel. {
          intros.
          specialize (Hx_after_long i).
          symmetry.
          assumption.
        }
        
        simpl in Hrel.
        
        assert (Hfinite_short : finite_protocol_action_from X res_long (get_receives_for s (others x) x)). {
          intuition.
        }
        
        split.
        + apply finite_protocol_action_from_app_iff.
          split.
          * unfold finite_protocol_action_from in IHprotocol.
            replace tr_long with (fst (apply_action X s (get_receives_all s lfrom))).
            assumption.
            unfold get_receives_all.
            replace (apply_action X s (concat (zip_apply (map (get_receives_for s) (map others lfrom)) lfrom))) with
            (tr_long, res_long). 
            intuition.
          * rewrite H0 in Hfinite_short.
            apply Hfinite_short.
        + intros.
          destruct (decide (f = x)).
          * rewrite H.
            destruct Hrel as [_ Hrel].
            specialize (Hrel i).
            rewrite e.
            rewrite Hrel.
            apply get_receives_for_correct.
            assumption.
            apply NoDup_others.
            apply others_correct.
            apply others_correct2.
            rewrite e in H2.
            assumption.
          * apply in_app_iff in H1.
            simpl in H1.
            destruct H1.
            specialize (IHproject f i H1).
            rewrite <- IHproject.
            unfold get_receives_all.
            replace (snd (apply_action X s (concat (zip_apply (map (get_receives_for s) (map others lfrom)) lfrom)))) with res_long.
            rewrite H.
            apply receives_neq.
            assumption.
            assumption.
            assumption.
            rewrite message_providers_receive.
            intros contra.
            simpl in contra.
            all : intuition.
    Admitted.
    
    Definition phase_two (s : vstate X) := snd (apply_action X s (get_receives_all s index_listing)).
    Definition common_future (s : vstate X) := phase_two (phase_one_res s).
    
    Lemma common_future_in_futures
      (s : vstate X)
      (Hpr : protocol_state_prop X s)
      (Hnf : no_component_fully_equivocating s index_listing) :
      in_futures X s (common_future s).
    Proof.
      specialize (@in_futures_trans message X s (phase_one_res s) (common_future s)) as Htrans.
      apply Htrans.
      apply phase_one_future.
      assumption.
      assumption.
      unfold common_future.
      unfold phase_two.
      unfold in_futures.
      remember (phase_one_res s) as s'.
      exists (fst (apply_action X (phase_one_res s) (get_receives_all s' index_listing))).
      split.
      - specialize (get_receives_all_protocol s' index_listing (proj1 Hfinite)) as Hrec.
        spec Hrec. {
          rewrite Heqs'.
          unfold phase_one_res.
          unfold phase_one.
          apply apply_action_last_protocol.
          assumption.
          apply phase_one_protocol.
          assumption.
          assumption.
        }
        simpl in Hrec.
        destruct Hrec as [Hrec _].
        unfold finite_protocol_action_from in Hrec.
        rewrite Heqs' in *.
        assumption.
      - rewrite Heqs'.
        apply apply_action_last.
    Qed.
    
    Lemma common_future_no_extra_equivocation
      (s : vstate X)
      (Hpr : protocol_state_prop X s)
      (Hnf : no_component_fully_equivocating s index_listing) :
      incl (GE (common_future s)) (GE s).
    Proof.
      intros.
    Admitted.
End Composition.