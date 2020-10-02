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
  {idec : EqDec index}
  {Mindex : Measurable index}
  {Rindex : ReachableThreshold index}
  (est' := (@EquivocationAwareListValidator.equivocation_aware_estimator _ _ Hfinite _ _ _ ))
  (IM_index := fun (i : index) => @VLSM_list index i index_listing idec est')
  (has_been_sent_capabilities := fun i : index => @has_been_sent_lv index i index_listing Hfinite idec ListValidator.estimator)
  (X := free_composite_vlsm IM_index i0)
  (preX := pre_loaded_vlsm X)
  (Hevidence := fun (i : index) => @observable_full index index_listing idec)
  (ce := @composed_computable_observable_equivocation_evidence
    message index state
    state_eq_dec comparable_states
    index idec index_listing IM_index Hevidence i0 (free_constraint IM_index)).
  
  (* 
  (ce := @composed_eqv_evidence index i0 index_listing _ est' (free_constraint IM_index)) 
  (Hc := @Hcomposite index i0 index_listing Hfinite _ est' (free_constraint IM_index))
  (cvcgel := @composite_vlsm_comparable_generated_events_lv index i0 index_listing Hfinite _ est' (free_constraint IM_index)).
  *)
  
  Definition component_list (s : vstate X) (li : list index) :=
    List.map s li.
  
  Definition unite_observations (ls : list state) : list (@state index index_listing) := 
    fold_right (set_union eq_dec) [] (List.map complete_observations ls).
  
  Definition GH (s : vstate X) : list index := 
    List.filter (fun i : index => negb (@equivocation_evidence (vstate X) index state _ comparable_states ce s i)) index_listing.
  
  Definition GE (s : vstate X) : list index :=
    set_diff idec index_listing (GH s).
    
  Definition can_receive_prop (to : index) (s : state) (m : message) :=
    @list_valid index to index_listing eq_dec (ListValidator.estimator) receive (s, (Some m)).
  
  Definition can_receive (to : index) (s : (@state index index_listing)) (m : message) : bool :=
    let s' := snd m in
    let from := fst m in 
    match eq_dec from to with
    | left _ => false
    | right _ => match eq_dec s' Bottom with
                 | left _ => false
                 | right _ => match eq_dec (project s from) (project s' from) with
                              | left _ => true
                              | right _ => false
                              end
                 end
    end.
  
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
      rewrite eq_dec_if_false.
      rewrite eq_dec_if_false.
      rewrite eq_dec_if_true.
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
  Qed.
  
  Definition can_receive_extended (to : index) (s : (@state index index_listing)) (m : message) : bool :=
    let s' := snd m in
    let from := fst m in
    match eq_dec s Bottom with
    | left _ => true 
    | right _ => state_ltb (project s from) s'
    end.
  
  Definition feasible_update_value (s : (@state index index_listing)) : bool :=
    match s with
    | Bottom => false
    | Something c is => match (@equivocation_aware_estimatorb index index_listing Hfinite eq_dec _ _ s false) with
                        | true => false
                        | false => true
                        end
    end.
  
  Lemma feasible_update_value_correct 
    (s : (@state index index_listing)) :
    (@equivocation_aware_estimator index index_listing Hfinite eq_dec _ _ s (feasible_update_value s)).
  Proof.
   destruct (feasible_update_value s) eqn : eq_fv.
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
    let cv := feasible_update_value s in
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
    apply feasible_update_value_correct.
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
        apply feasible_update_value_correct.
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
      destruct (eq_dec i a).
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
          remember (update_consensus (update_state (s a) (s a) a) (feasible_update_value (s a))) as su.
          rewrite e.
          rewrite state_update_eq.
          rewrite Heqsu.
          rewrite <- update_consensus_clean with (value := (feasible_update_value (s a))).
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
  Qed.
  
  Definition latest_versions (s : vstate X) (i : index) : list state :=
    let sc := List.map s index_listing in
    List.map ((flip project) i) sc.
  
  Definition pick_version (s : vstate X) (from to : index) : option message :=
    let latest_messages := List.map (pair from) (latest_versions s from) in
    find (can_receive_extended to (s to)) latest_messages.
  
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
    
  Definition sync (s : vstate X) (from to : index) : list (@transition_item message (type X)) :=
    let candidates := latest_versions s from in
    let goal := (pick_version s from to) in 
    match goal with
    | None => []
    | Some goal' => []
    end. 
 
End Composition.