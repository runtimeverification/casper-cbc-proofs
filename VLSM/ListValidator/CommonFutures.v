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
  (est' := fun (i : index) => (@EquivocationAwareListValidator.equivocation_aware_estimator _ i _ Hfinite _ _ _ ))
  (IM_index := fun (i : index) => @VLSM_list index i index_listing idec (est' i))
  (has_been_sent_capabilities := fun i : index => @has_been_sent_lv index i index_listing Hfinite idec (est' i))
  (has_been_received_capabilities := fun i : index => @has_been_received_lv index i index_listing Hfinite idec (est' i))
  (X := composite_vlsm IM_index i0 (free_constraint IM_index))
  (preX := pre_loaded_with_all_messages_vlsm X)
  (Hevidence := fun (i : index) => @observable_full index i index_listing idec)
  (ce := @composed_observation_based_equivocation_evidence
    message index lv_event
    decide_eq 
    comparable_lv_events
    get_event_subject
    index index_listing IM_index Hevidence).
  
  Definition component_list (s : vstate X) (li : list index) :=
    List.map s li.
  (*
  Definition unite_observations (ls : list state) : set lv_event := 
    fold_right (set_union decide_eq) [] (List.map (@complete_observations) ls). *)
  
  Definition GH (s : vstate X) : list index := 
    List.filter (fun i : index => negb (@equivocation_evidence (vstate X) index lv_event _ comparable_lv_events get_event_subject ce s i)) index_listing.
  
  Definition GE (s : vstate X) : list index :=
    set_diff idec index_listing (GH s).
    
  Definition can_receive_prop (to : index) (s : state) (m : message) :=
    @list_valid index to index_listing decide_eq (ListValidator.estimator) receive (s, (Some m)).
  
  Definition can_receive (to : index) (s : (@state index index_listing)) (m : message) : bool :=
    let s' := snd m in
    let from := fst m in 
    match decide_eq from to with
    | left _ => false
    | right _ => match decide_eq s' Bottom with
                 | left _ => false
                 | right _ => match decide_eq (project s from) (project s' from) with
                              | left _ => true
                              | right _ => false
                              end
                 end
    end.
  
  (*
  Lemma can_receive_function (to : index) : PredicateFunction2 (can_receive_prop to) (can_receive to).
  Proof.
    unfold PredicateFunction2.
    intros.
    split.
    - intros.
      unfold can_receive_prop in H.
      unfold can_receive.
      unfold list_valid in H.
      destruct H as [Hproject [Hnb Hnself]]; try
      rewrite decide_False.
      rewrite decide_False.
      rewrite decide_False.
      reflexivity.
      assumption.
      assumption.
      intuition.
    - intros.
      unfold can_receive in H.
      unfold can_receive_prop.
      unfold list_valid.
      destruct (eq_dec (project a (fst b)) (project (snd b) (fst b))).
      destruct (eq_dec (fst b) to).
      discriminate H.
      destruct (eq_dec (snd b) Bottom).
      discriminate H.
      intuition.
      destruct (eq_dec (fst b) to); destruct (eq_dec (snd b) Bottom); discriminate H.
  Qed. *)
  
  Definition can_receive_extended (to : index) (s : (@state index index_listing)) (m : message) : bool :=
    let s' := snd m in
    let from := fst m in
    match decide_eq s Bottom with
    | left _ => true 
    | right _ => state_ltb (project s from) s'
    end.
  
  Definition feasible_update_value (s : (@state index index_listing)) (who : index) : bool :=
    match s with
    | Bottom => false
    | Something c is => match (@equivocation_aware_estimatorb index who index_listing Hfinite decide_eq _ _ s false) with
                        | true => false
                        | false => true
                        end
    end.
  
  Lemma feasible_update_value_correct 
    (s : (@state index index_listing))
    (who : index) :
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
     admit.
   - unfold feasible_update_value in eq_fv.
     destruct s.
     simpl.
     apply I.
     destruct (equivocation_aware_estimatorb (Something b is) false) eqn : eq_ewb.
     unfold equivocation_aware_estimator. 
     assumption.
     discriminate eq_fv.
  Admitted.
  
  Definition feasible_update_single (s : (@state index index_listing)) (who : index) : transition_item :=
    let cv := feasible_update_value s who in
    let res := @list_transition index who _ _ (update cv) (s, None) in
    @Build_transition_item _ (type (IM_index who)) (update cv) None (fst res) (snd res).
  
  Definition feasible_update_composite (s : vstate X) (who : index) : (@transition_item _ (type X)) :=
    lift_to_composite_transition_item' IM_index s who (feasible_update_single (s who) who).
  
  Lemma feasible_update_protocol 
    (s : vstate X)
    (Hprs : protocol_state_prop _ s)
    (who : index) 
    (item := feasible_update_composite s who) :
    protocol_transition X (l item) (s, input item) (destination item, output item).
  Proof.
    unfold protocol_transition.
    repeat split.
    assumption.
    simpl.
    apply option_protocol_message_None.
    apply feasible_update_value_correct with (s := s who) (who := who).
  Qed.
  (* pair (stare, transition_item) *)
  
  Fixpoint chain_updates (li : list index) (s : vstate X) : (list (@transition_item _ (type X))) :=
    match li with
    | [] => []
    | (h :: tl) => let new_transition := feasible_update_composite s h in
                   let new_s := destination new_transition in
                   let res_tl := chain_updates tl new_s in
                   new_transition :: res_tl
    end.
  
  Definition phase_one_transitions (s : vstate X) : list transition_item :=
    chain_updates index_listing s.
    
  Definition resulting_state (s : vstate X) (l : list transition_item) :=
    last (List.map destination l) s.
 
  Definition phase_one (s : vstate X) :=
    resulting_state s (phase_one_transitions s).
  
  Lemma chain_updates_protocol 
    (s : vstate X)
    (Hspr : protocol_state_prop _ s)
    (li : list index) :
    finite_protocol_trace_from _ s (chain_updates li s).
  Proof.
    generalize dependent s.
    induction li.
    - intros.
      simpl.
      apply finite_ptrace_empty.
      assumption.
    - intros.
      remember (feasible_update_composite s a) as item.
      assert (protocol_transition X (l item) (s, input item) (destination item, output item)). {
        unfold protocol_transition.
        unfold protocol_valid.
        repeat split.
        assumption.
        rewrite Heqitem.
        simpl.
        apply option_protocol_message_None.
        unfold free_composite_valid.
        unfold vvalid.
        unfold valid.
        simpl.
        rewrite Heqitem.
        simpl.
        split.
        apply feasible_update_value_correct with (s := s a) (who := a).
        reflexivity.
        rewrite Heqitem.
        simpl.
        reflexivity.
      }
      apply finite_ptrace_extend.
      + specialize (IHli (destination item)).
        rewrite <- Heqitem.
        spec IHli.
        apply protocol_transition_destination with (l := (l item)) (s0 := s) (om := input item) (om' := output item).
        assumption.
        unfold chain_updates in IHli.
        rewrite Heqitem in IHli.
        unfold feasible_update_composite in IHli.
        simpl in IHli.
        simpl.
        rewrite Heqitem.
        assumption.
      + rewrite Heqitem in H.
        assumption.
  Qed.
  
  Lemma phase_one_future 
    (s : vstate X)
    (Hspr : protocol_state_prop _ s) :
    in_futures _ s (phase_one s).
  Proof.
    unfold in_futures.
    exists (phase_one_transitions s).
    split.
    - unfold phase_one_transitions.
      apply chain_updates_protocol.
      assumption.
    - unfold phase_one_transitions.
      reflexivity.
  Qed.
  
  Lemma chain_updates_projections_out 
    (s : vstate X)
    (li : list index)
    (i : index)
    (Hi : ~In i li)
    (s' := resulting_state s (chain_updates li s)) :
    (s' i) = (s i).
  Proof.
    generalize dependent s.
    induction li.
    - intros. 
      unfold resulting_state in *.
      simpl in *.
      unfold s'.
      reflexivity.
    - intros.
      spec IHli.
      apply not_in_cons in Hi.
      intuition.
      simpl in IHli.
      unfold chain_updates in s'.
      unfold resulting_state in s'.
      remember ((fix chain_updates (li : list index) (s : vstate X) {struct li} :
                    list transition_item :=
                  match li with
                  | [] => []
                  | h :: tl =>
                      feasible_update_composite s h
                      :: chain_updates tl (destination (feasible_update_composite s h))
                  end) li (destination (feasible_update_composite s a))) as y.
      remember (feasible_update_composite s a) as x.
      unfold s'.
      rewrite map_cons.
      rewrite unroll_last.
      unfold resulting_state in IHli.
      unfold chain_updates in IHli.
      rewrite Heqy.
      
      assert ((destination x) i = (s i)). {
        rewrite Heqx.
        apply not_in_cons in Hi.
        destruct Hi as [Hi1 Hi2].
        unfold feasible_update_composite.
        unfold lift_to_composite_transition_item'.
        unfold feasible_update_single.
        simpl.
        unfold lift_to_composite_state'.
        rewrite state_update_neq.
        reflexivity.
        assumption.
      }
      simpl.
      specialize (IHli (destination x)).
      rewrite H in IHli.
      assumption.
  Qed.
  
  Lemma chain_updates_projections_in 
    (s : vstate X)
    (Hprs : protocol_state_prop _ s)
    (li : list index)
    (Hnodup: NoDup li)
    (i : index)
    (Hi : In i li)
    (s' := resulting_state s (chain_updates li s)) :
    project (s' i) i = (s i).
  Proof.
    generalize dependent s.
    induction li.
    - simpl in *.
      intuition.
    - simpl in IHli.
      destruct (decide (i = a)).
      + intros. 
        unfold s'.
        unfold resulting_state.
        unfold chain_updates.
        rewrite map_cons.
        rewrite unroll_last.
        remember (feasible_update_composite s a) as x.
        assert (project ((destination x) i) i = s i). {
          rewrite Heqx.
          unfold feasible_update_composite.
          unfold lift_to_composite_transition_item'.
          simpl.
          unfold lift_to_composite_state'.
          remember (update_consensus (update_state (s a) (s a) a) (feasible_update_value (s a) a)) as su.
          rewrite e.
          rewrite state_update_eq.
          rewrite Heqsu.
          rewrite <- update_consensus_clean with (value := (feasible_update_value (s a) a)).
          rewrite (@project_same index index_listing Hfinite).
          reflexivity.
          apply protocol_state_component_no_bottom.
          assumption.
        }
        assert (~In i li /\ NoDup li). {
          rewrite e.
          apply NoDup_cons_iff in Hnodup.
          intuition.
        }
        destruct H0 as [H0 H0'].
        specialize (chain_updates_projections_out (destination x) li i H0) as Hno_i.
        simpl in Hno_i.
        unfold resulting_state in Hno_i.
        unfold chain_updates in Hno_i.
        replace (last
     (map destination
        ((fix chain_updates (li0 : list index) (s0 : vstate X) {struct li0} :
              list transition_item :=
            match li0 with
            | [] => []
            | h :: tl =>
                feasible_update_composite s0 h
                :: chain_updates tl (destination (feasible_update_composite s0 h))
            end) li (destination x))) (destination x) i) with (destination x i).
         assumption.
      + intros.
        spec IHli.
        apply NoDup_cons_iff in Hnodup.
        intuition.
        simpl in Hi.
        destruct Hi.
        elim n. symmetry. assumption.
        unfold s'.
        unfold resulting_state.
        unfold chain_updates.
        remember (feasible_update_composite s a) as x.
        specialize (IHli H (destination x)).
        assert ((destination x i) = s i). {
          rewrite Heqx.
          simpl.
          unfold lift_to_composite_state'.
          rewrite state_update_neq.
          reflexivity.
          assumption.
        }
        rewrite map_cons.
        rewrite unroll_last.
        unfold resulting_state in IHli.
        unfold chain_updates in IHli.
        rewrite H0 in IHli.
        spec IHli.
        assert (protocol_transition X (l x) (s, input x) (destination x, output x)). {
          rewrite Heqx.
          apply feasible_update_protocol.
          assumption.
        }
        apply protocol_transition_destination with (l := (l x)) (s0 := s) (om := input x) (om' := output x).
        assumption.
        assumption.
  Qed.
  
  Lemma phase_one_projections 
    (s : vstate X)
    (Hprss : protocol_state_prop _ s)
    (i : index)
    (s' := phase_one s) :
    project (s' i) i = (s i).
  Proof.
    apply chain_updates_projections_in.
    assumption.
    apply (proj1 Hfinite).
    apply ((proj2 Hfinite) i).
  Qed.
  
  (*
  Lemma everything_in_projections 
    (s : vstate X)
    (Hprs : protocol_state_prop _ s)
    (li : list index)
    (s' := phase_one s) :
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
      assumption.
      assumption.
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
      }
      rewrite H0 in Hina.
      assumption.
  Qed. *)
  
  Definition latest_versions (s : vstate X) (i : index) : list state :=
    let sc := List.map s index_listing in
    List.map ((flip project) i) sc.
  
  Definition pick_version (s : vstate X) (from to : index) : option message :=
    let latest_messages := List.map (pair from) (latest_versions s from) in
    find (can_receive_extended to (s to)) latest_messages.
  
  (* 
  Definition sync_component'
    (s target : (@state index index_listing))
    (i : index) : list (@transition_item message (type X)) := [].
  
  Definition sync_to_from 
    (s : vstate X) 
    (to from : index) 
    (target : (@state index index_listing)) :
    option (list (@transition_item message (type X))) :=
    Some [].
    
  Definition sync_all_from
    (s : vstate X)
    (to from : index)
  *)
  
  (* 
  Definition sync_action' (to from : index) (ls : state) : (@action _ (type (IM_index t *)
  
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
    
   Lemma something
    (s s': vstate X)
    (Hpr : protocol_state_prop X s)
    (Hpr' : protocol_state_prop X s')
    (to from :index)
    (Hdif : to <> from)
    (a : vaction X)
    (Hsync : sync s (s' from) to from = Some a) :
    let res := snd (apply_action X s a) in
    finite_protocol_action_from X s a.
   Proof.
    generalize dependent s.
    
    induction a.
    - intros. simpl in *.
      unfold finite_protocol_action_from. simpl.
      apply finite_ptrace_empty. 
      assumption.
    - intros. simpl in *.
      
      replace (a :: a0) with ([a] ++ a0). 2: auto.
      rewrite <- finite_protocol_action_from_app_iff.
      
      unfold sync in Hsync.
      destruct (complete_suffix (get_history (s' from) from) (get_history (s to) from)) eqn : eq_cs. 2: discriminate Hsync.
      
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
      
      assert (Hinsa: In sa (get_history (s' from) from)). {
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
          specialize (sent_component_protocol_composed IM_index i0 (free_constraint IM_index) has_been_sent_capabilities (fun m => Some (fst m)) s') as Hope.
          spec Hope. assumption.
          specialize (Hope from (from, sa)).
          apply Hope.
          unfold has_been_sent.
          unfold has_been_sent_capabilities.
          unfold has_been_sent_lv.
          unfold send_oracle.
          simpl.
          rewrite decide_True.
          apply existsb_exists.
          exists sa.
          split. assumption.
          unfold state_eqb. rewrite decide_True. all : reflexivity. 
        - simpl in *.
          inversion Hh.
          unfold vvalid.
          apply (@no_bottom_in_history index index_listing Hfinite) in Hinsa.
          unfold valid. simpl.
          repeat split; assumption.
        - assumption.
      }
      
      subst input_a.
      split.
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
        specialize (IHa s0).
        spec IHa.
        apply protocol_transition_destination in H.
        assumption.
        apply IHa.
        
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
        
        unfold sync.
        
        destruct (complete_suffix (get_history (s' from) from) (get_history (s0 to) from)) eqn : eq_cs2.
        * f_equal.
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
        * rewrite Honefold in eq_cs2.
          rewrite eq_cs' in eq_cs2.
          rewrite <- app_assoc in eq_cs2.
          assert (complete_suffix (rev tls ++ [sa] ++ get_history (s to) from)
           ([sa] ++ get_history (s to) from) = Some (rev tls)). {
            apply complete_suffix_correct.
            reflexivity.  
          }
          rewrite H1 in eq_cs2.
          discriminate eq_cs2.
   Qed.
   
    Definition get_candidates 
      (s : vstate X)
      (target : index) :
      list state 
      :=
      List.map ((flip project) target) (component_list s index_listing).
    
    Definition get_topmost_candidates
      (s : vstate X)
      (target : index) :
      list state 
      :=
      get_maximal_elements (state_lt' target) _ (get_candidates s target).
      
End Composition.