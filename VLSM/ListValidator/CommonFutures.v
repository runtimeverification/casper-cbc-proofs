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
  (IM_index := fun (i : index) => @VLSM_list index i index_listing idec ListValidator.estimator)
  (has_been_sent_capabilities := fun i : index => @has_been_sent_lv index i index_listing Hfinite idec ListValidator.estimator)
  (X := composite_vlsm IM_index i0 True)
  (preX := pre_loaded_vlsm X)
  {Mindex : Measurable index}
  {Rindex : ReachableThreshold index}.
  
  Definition component_list (s : vstate X) :=
    List.map s index_listing.
  
  Definition unite_observations (ls : list state) : list (@state index index_listing) := 
    fold_right (set_union eq_dec) [] (List.map complete_observations ls).
  
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
    match eq_dec s' Bottom with
    | left _ => false
    | right _ => match eq_dec s Bottom with
                 | left _ => true 
                 | right _ => inb eq_dec (project s from) (get_history s' from)
                 end
    end. 

  Definition latest_versions (s : vstate X) (i : index) : list state :=
    let sc := List.map s index_listing in
    List.map ((flip project) i) sc.
  
  Definition pick_version (s : vstate X) (from to : index) : option message :=
    let latest_messages := List.map (pair from) (latest_versions s from) in
    find (can_receive_extended to (s to)) latest_messages.
  
  Definition sync_with (s : vstate X) (from to : index) : list (@transition_item message (type X)) :=
    let candidates := latest_versions s from in
    let goal := (pick_version s from to) in 
    match goal with
    | None => []
    | Some goal' => []
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
    lift_to_composite_transition_item IM_index who (feasible_update_single (s who) who).
  
  (* pair (stare, transition_item) *)
  
  Fixpoint chain_updates (li : list index) (s : vstate X) : list (@transition_item _ (type X)) :=
    match li with
    | [] => []
    | (h :: tl) => let tmp_lst := chain_updates tl s in
                   let tmp_s := match tmp_lst with 
                               | [] => s
                               | h' :: tl' => (destination h')
                               end in
                   (feasible_update_composite tmp_s h :: tmp_lst)
    end.
  
  Definition phase_one_transitions (s : vstate X) : list transition_item :=
    chain_updates index_listing s.
 
  Definition phase_one (s : vstate X) :=
    last (List.map destination (phase_one_transitions s)) s. 
  
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
      unfold chain_updates.
      admit.
  Admitted.
  
  Lemma phase_one_future 
    (s : vstate X)
    (Hspr : protocol_state_prop _ s)
    (s' := phase_one s) :
    in_futures _ s s'.
  Proof.
    unfold in_futures.
    unfold phase_one in s'.
    exists (phase_one_transitions s).
    split.
    - unfold phase_one_transitions.
      unfold s'.
      apply chain_updates_protocol.
      assumption.
    - unfold s'.
      reflexivity.
  Qed.
  
  Lemma everything_in_projections 
    (s : vstate X) :
    set_eq 
    (unite_observations (component_list s))
    (unite_observations (zip_apply (List.map project (component_list s)) index_listing)).
  Proof.
  Admitted.
    
End Composition.