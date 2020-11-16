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
    comparable_lv_events
    get_event_subject
    index index_listing IM_index Hevidence).
  
  Check complete_observations.
  
  Definition component_list (s : vstate X) (li : list index) :=
    List.map s li.
  
  Definition unite_observations (ls : list state) : set lv_event := 
    fold_right (set_union decide_eq) [] (List.map (complete_observations) ls).
  
  Definition GH (s : vstate X) : set index := 
    List.filter (fun i : index => negb (@equivocation_evidence (vstate X) index lv_event _ comparable_lv_events get_event_subject ce s i)) index_listing.
  
  Definition GE (s : vstate X) : set index :=
    set_diff idec index_listing (GH s).
 
  Definition ce' (s : vstate X) := @composed_witness_observation_based_equivocation_evidence
    message index lv_event
    decide_eq 
    comparable_lv_events
    get_event_subject
    index IM_index Hevidence (GH s).
 
  Definition LH (s : vstate X) : set index :=
    List.filter (fun i : index => negb (@equivocation_evidence (vstate X) index lv_event _ comparable_lv_events get_event_subject (ce' s) s i)) index_listing.
  
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
  
  Lemma GH_incl_LH 
    (s : vstate X) :
    incl (GH s) (LH s).
  Proof.
    unfold incl; intros.
    unfold GH in H.
    unfold LH.
    apply filter_In in H.
    apply filter_in.
    apply ((proj2 Hfinite) a).
    destruct H as [_ H].
    unfold equivocation_evidence in *.
    unfold observable_events in *.
    unfold ce'; unfold ce in H.
    simpl in *.
    rewrite negb_true_iff in *.
    rewrite existsb_forall in *.
    intros.
    specialize (H x).
    
    spec H save. {
      unfold composed_witness_observable_events in *.
      rewrite set_union_in_iterated.
      rewrite set_union_in_iterated in H0.
      rewrite Exists_exists in *.
      destruct H0 as [e [Hine Hinx]].
      exists e.
      split.
      apply in_map_iff in Hine.
      apply in_map_iff.
      destruct Hine as [j [Hobj Hinj]].
      exists j; intuition.
      apply ((proj2 Hfinite) j).
      assumption.
    }
    
    rewrite existsb_forall in *.
    intros.
    specialize (H x0).
    apply H.
    unfold composed_witness_observable_events in *.
    unfold observable_events. simpl.
    eapply set_union_iterated_incl with (ss' :=  (map (fun i : index => lv_observations (s i) a) index_listing)) in H2.
    unfold lv_observations in *. simpl in *.
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
    (Hne : not_all_equivocating (s who) who)
    (item := feasible_update_composite s who) :
    protocol_transition X (l item) (s, input item) (destination item, output item).
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
    (li : list index)
    (Hnodup : NoDup li)
    (Hnf : no_component_fully_equivocating s li) :
    finite_protocol_trace_from _ s (chain_updates li s).
  Proof.
    unfold no_component_fully_equivocating in Hnf.
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
        specialize (Hnf a).
        spec Hnf; intuition; assumption.
        reflexivity.
        rewrite Heqitem.
        simpl.
        reflexivity.
      }
      apply finite_ptrace_extend.
      + apply NoDup_cons_iff in Hnodup.
        destruct Hnodup as [Hnoa Hnoli].
        specialize (IHli Hnoli (destination item)).
        rewrite <- Heqitem.
        spec IHli.
        apply protocol_transition_destination with (l := (l item)) (s0 := s) (om := input item) (om' := output item).
        assumption.
        unfold chain_updates in IHli.
        rewrite Heqitem in IHli.
        unfold feasible_update_composite in IHli.
        simpl in IHli.
        simpl.
        spec IHli. {
          intros.
          destruct (decide (i = a)).
          - rewrite e.
            congruence.
          - unfold lift_to_composite_state'.
            rewrite state_update_neq.
            specialize (Hnf i).
            spec Hnf. intuition. assumption.
            assumption.
        }
        rewrite Heqitem.
        assumption.
      + rewrite Heqitem in H.
        assumption.
  Qed.
  
  Lemma phase_one_future 
    (s : vstate X)
    (Hnf : no_component_fully_equivocating s index_listing)
    (Hspr : protocol_state_prop _ s) :
    in_futures _ s (phase_one s).
  Proof.
    unfold in_futures.
    exists (phase_one_transitions s).
    split.
    - unfold phase_one_transitions.
      apply chain_updates_protocol.
      assumption.
      apply (proj1 Hfinite).
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
    (Hnf : no_component_fully_equivocating s li)
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
          specialize (Hnf a).
          spec Hnf; intuition.
        }
        apply protocol_transition_destination with (l := (l x)) (s0 := s) (om := input x) (om' := output x).
        assumption.
        spec IHli. {
          unfold no_component_fully_equivocating.
          intros.
          apply NoDup_cons_iff in Hnodup.
          destruct Hnodup as [Hnoa Hnoli].
          destruct (decide (i1 = a)).
            - congruence.
            - rewrite Heqx.
              unfold feasible_update_composite.
              unfold lift_to_composite_transition_item'.
              unfold lift_to_composite_state'; simpl.
              rewrite state_update_neq.
              unfold no_component_fully_equivocating in Hnf.
              specialize (Hnf i1). 
              spec Hnf. intuition.
              assumption.
              assumption.
        }
        assumption.
  Qed.
  
  Lemma phase_one_projections 
    (s : vstate X)
    (Hprss : protocol_state_prop _ s)
    (Hnf : no_component_fully_equivocating s index_listing)
    (i : index)
    (s' := phase_one s) :
    project (s' i) i = (s i).
  Proof.
    apply chain_updates_projections_in.
    assumption.
    assumption.
    apply (proj1 Hfinite).
    apply ((proj2 Hfinite) i).
  Qed.
  
  Lemma everything_in_projections 
    (s : vstate X)
    (Hprs : protocol_state_prop _ s)
    (Hnf : no_component_fully_equivocating s index_listing)
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
            apply existsb_exists.
            exists sa.
            split.
            rewrite <- e in Hinsa.
            rewrite <- e.
            assumption.
            unfold state_eqb. rewrite decide_True. all : auto.
          + specialize (received_component_protocol_composed IM_index i0 (free_constraint IM_index) has_been_received_capabilities (fun m => Some (fst m)) s') as Hope.
            spec Hope. assumption.
            specialize (Hope inter (from, sa)).
            apply Hope.
            unfold has_been_received.
            unfold has_been_received_capabilities.
            unfold has_been_received_lv.
            unfold receive_oracle; simpl.
            rewrite decide_False.
            apply existsb_exists.
            exists sa.
            split.
            assumption.
            unfold state_eqb. rewrite decide_True. all : auto.
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
        specialize (@apply_action_folder_additive _ X s0 (rev a0) s0 [{| l := label_a; input := Some (from, sa); destination := s0; output := o |}]) as Hadd.
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
      
    Lemma get_receives_correct
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
      
End Composition.