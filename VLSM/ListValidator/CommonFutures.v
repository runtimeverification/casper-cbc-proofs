Require Import Bool List ListSet Reals FinFun RelationClasses Relations Relations_1 Sorting Basics.
Require Import Lia.
Import ListNotations.
From CasperCBC
Require Import
  Lib.Preamble
  Lib.ListExtras
  Lib.ListSetExtras
  Lib.SortedLists
  Lib.Measurable
  VLSM.Common
  VLSM.Plans
  VLSM.ProjectionTraces
  VLSM.Composition
  VLSM.Equivocation
  VLSM.ListValidator.ListValidator
  VLSM.ListValidator.Equivocation
  VLSM.ListValidator.Observations
  VLSM.ListValidator.EquivocationAwareListValidator
  VLSM.ListValidator.EquivocationAwareComposition
  VLSM.ObservableEquivocation
  .

(**
Also see:
   - [Observations.v] for the observation model used here
   - [EquivocationAwareListValidator.v] for the used estimators
   - [EquivocationAwareComposition.v] for results concerning this type of composition
   - [Equivocation.v] and [ListValidator.v] for some general
     facts about List Validators. *)


Section CommonFutures.

(**
   ** The Common Futures Theorem for List Validators.

   The following is an informal sketch of the Common Futures Theorem for List Validators.

   Consider a composition <<X>> of List Validator nodes, each using an [equivocation_aware_estimator].
   The aim is to prove that for any given protocol [vstate X] <<s>>, there exists a [vstate X] <<s'>>
   such that:
   (1) <<s'>> is a future state of <<s>>.
   (2) The set of honest nodes in <<s'>> is identical to the set of honest nodes in <<s>>.
       Formally, we have <<set_eq (GH s') (GH s)>>.
   (3) All honest nodes have the same estimator in <<s'>>.

   We will focus on the strategy for achieving (3), noting along the way that we're not breaking (1)
   or (2). We achieve (3) by making sure that all estimators of honest nodes take the same input
   in <<s'>>. Given that they are [equivocation_aware_estimator]s and, thus, ignore projections onto
   nodes which they can locally prove equivocating, we can further split this goal in two:
   (3.1) The honest nodes should see the same set of equivocating nodes locally.
   (3.2) For each locally-honest-appearing node <<h>>, all honest nodes have identical projections onto
       <<h>>

   The most natural way to achieve (3.1) is to ensure that for all honest nodes <<i>>,
   << set_eq (LH [i] s') (HH s') >>, i.e the set of locally-honest-looking nodes for each node
   is equal to the set of nodes which would seem honest if we were to unite all observations
   from honest nodes. << incl (HH s') (LH [i] s') >> holds trivially for any <<s'>>. For the other
   direction, we will require honest nodes to share observations among themselves. This gives an initial
   structure of our common future-finding algorithm:

   Send Phase : All nodes in <<GH s>> do a send/update operation.
   Receive Phase' : All nodes in <<GH s>> receive all messages sent in the Send Phase.

   The point is that by sending and receiving these messages, honest nodes will be up-to-date
   regarding each other, hence knowing what state everyone had back in <<s>> and thus obtaining
   the observations held at that point as well. We can show that this process is protocol and
   that the new observations introduced into the pool can't really contain new information and thus
   do not alter <<GH s>> (or even <<HH s>>).

   What about (3.2)? Our current algorithm doesn't necessarily solve (3.2), because there
   may exist nodes in <<(HH s)>> which are outside of <<(GH s)>> and projections onto
   these indices remain unaffected by our algorithm (so if they weren't precisely equal
   in the beginning, we have a problem).

   The solution is to generalize the Receive Phase as such:

   Receive Phase : For all <<i>> in <<GH s>>, for all <<j>>, <<i>> will receive the message
                   <<(j, top_s)>> where <<top_s>> is a state satisfying the following:
                   - there exists <<k>> in <<GH s>> such that <<project (s k) j = top_s>>.
                   - there is no other projection of this form which is greater than <<top_s>>
                   - it is valid for <<i>> to receive <<top_s>>.

   In other words, each honest <<i>> tries to update its <<j>> component to the freshest/most advanced
   projection any honest validator has onto <<j>>. If there are several different maximal projections
   (which can happen if <<j>> is equivocating), we select an arbitrary one that we can receive.
   Note that it can happen that <<i>> sticks to its own projection onto <<j>>.

   In the end what happens is that if <<j>> is in <<HH s'>>, then there can be a single topmost
   projection, so everyone received the same thing. So if these projections should differ, we
   can obtain a contradiction. Note also that our new Receive Phase still does what it did
   initially for the honest validators: if <<j>> is in <<GH s>>, the topmost projection is simply
   the message sent in the sending phase.
*)


Context
  {index : Type}
  {i0 : Inhabited index}
  {index_listing : list index}
  {Hfinite : Listing index_listing}
  {idec : EqDecision index}
  {Mindex : Measurable index}
  {Rindex : ReachableThreshold index}
  (est' := fun (i : index) => (@EquivocationAwareListValidator.equivocation_aware_estimator _ i _ Hfinite _ _ _ ))
  (IM_index := fun (i : index) => @VLSM_list index i index_listing idec (est' i))
  (has_been_sent_capabilities := fun i : index => @lv_sent_capability index i index_listing Hfinite idec (est' i) _)
  (has_been_received_capabilities := fun i : index => @lv_received_capability index i index_listing Hfinite idec (est' i))
  (X := composite_vlsm IM_index (free_constraint IM_index))
  (preX := pre_loaded_with_all_messages_vlsm X)
  (Hevents_set' := fun (i : index) => @simp_lv_observable_events index i index_listing _)
  (Hstate_events_set := fun (i : index) => @simp_lv_state_observations index i index_listing _)
  (Hevidence := fun (i : index) => @simp_observable_full index i index_listing idec)
  (Hstate_events_fn := fun (i : index) => (@simp_lv_observations index i index_listing _))
  (Hbasic := fun (i : index) => @simp_lv_basic_equivocation index i index_listing Hfinite idec Mindex Rindex).

  Local Notation hbo_cobs' := (@hbo_cobs index i0 index_listing Hfinite idec Mindex Rindex).
  Local Notation in_listing := (proj2 Hfinite).
  Local Notation component_list s li := (List.map s li).

  (* TODO: Delete this when possible. *)
  Local Lemma protocol_state_component_no_bottom
    (s : vstate X)
    (i : index)
    (Hprs : protocol_state_prop X s) :
    (s i) <> Bottom.
  Proof.
    apply (@protocol_prop_no_bottom index i _ _ (est' i)).
    apply protocol_state_projection with (j := i) in Hprs.
    unfold protocol_state_prop in Hprs.
    destruct Hprs as [om Hprs] in Hprs.
    apply proj_pre_loaded_with_all_messages_protocol_prop in Hprs.
    unfold protocol_state_prop.
    exists om.
    assumption.
  Qed.

  (* Returns a boolean <<b>> such that it is valid to perform an update transition
     using <<b>> in state <<s who>> *)

  Definition feasible_update_value (s : (@state index index_listing)) (who : index) : bool :=
    match s with
    | Bottom => false
    | Something c is => match @bool_decide (@equivocation_aware_estimator index who index_listing Hfinite decide_eq _ _ s false)
                                           (equivocation_aware_estimator_dec s false) with
                        | true => false
                        | false => true
                        end
    end.

  (* Such a boolean doesn't exist if a node sees everyone as equivocating, so we need a hypothesis
     to exclude this possibility. *)

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
     destruct s;[intuition congruence|].
     destruct (bool_decide (equivocation_aware_estimator (Something b is) false)) eqn : eq_ewb.
     + intuition congruence.
     + rewrite bool_decide_eq_false in eq_ewb.
       apply ea_estimator_total in eq_ewb.
       all : intuition.
   - unfold feasible_update_value in eq_fv.
     destruct s;[intuition|].
     destruct (bool_decide (equivocation_aware_estimator (Something b is) false)) eqn : eq_ewb.
     rewrite bool_decide_eq_true in eq_ewb. intuition.
     intuition congruence.
  Qed.

  Definition feasible_update_single (s : (@state index index_listing)) (who : index) : plan_item :=
    let cv := feasible_update_value s who in
    let res := @list_transition index who _ _ (update cv) (s, None) in
    @Build_plan_item _ (type (IM_index who)) (update cv) None.

  Definition feasible_update_composite (s : vstate X) (who : index) : vplan_item X :=
    lift_to_composite_plan_item IM_index who (feasible_update_single (s who) who).

  (* Updates using the feasible value are protocol. *)

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

  Definition chain_updates (li : list index) (s : vstate X) : plan X :=
    List.map (feasible_update_composite s) li.

  Lemma chain_updates_projections_out
    (s : vstate X)
    (li : list index)
    (i : index)
    (Hi : ~In i li)
    (s' := snd (apply_plan X s (chain_updates li s))) :
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

  (* Main lemma about the sending phase. *)

  Lemma chain_updates_protocol
    (s : vstate X)
    (Hprs : protocol_state_prop _ s)
    (li : list index)
    (Hnodup : NoDup li)
    (Hhonest : incl li (GH s))
    (Hnf : no_component_fully_equivocating s li) :
    let res := snd (apply_plan X s (chain_updates li s)) in
    finite_protocol_plan_from _ s (chain_updates li s) /\
    (forall (i : index), In i li -> project (res i) i = s i) /\
    set_eq (GE res) (GE s).
  Proof.
    unfold no_component_fully_equivocating in Hnf.
    generalize dependent s.
    induction li as [|i li].
    - intros.
      simpl.
      split.
      + apply finite_ptrace_empty.
        assumption.
      + split; [intuition|].
        simpl in res.
        unfold res. intuition.
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

      remember (snd (apply_plan X s (map (feasible_update_composite s) [i]))) as s'.

      apply NoDup_cons_iff in Hnodup.
      destruct Hnodup as [Hnoa Hnoli].
      specialize (IHli Hnoli s').

      spec IHli. {
        rewrite Heqs'.
        apply apply_plan_last_protocol.
        assumption.
        simpl.
        apply finite_protocol_plan_from_one.
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

      assert (HGEs' : set_eq (GE s') (GE s)). {
        unfold set_eq.
        simpl in Heqs'.
        rewrite Heqs'.
        split.
        + apply @GE_existing_same.
          intuition.
        + apply @GE_existing_same_rev.
          intuition.
          unfold GE.
          rewrite <- wH_wE'.
          apply Hhonest. intuition.
      }

      spec IHli. {
        unfold incl in *.
        intros idx Hidx.
        unfold GE.
        apply wH_wE'.
        specialize (Hhonest idx).
        setoid_rewrite HGEs'.
        apply wH_wE'.
        apply Hhonest.
        intuition.
      }

      spec IHli. {
        intros.
        destruct (decide (i1 = i)).
        + rewrite e in H0; intuition.
        + specialize (Hindif i1 H0).
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
      + apply finite_protocol_plan_from_app_iff.
        split.
        * unfold feasible_update_composite; simpl.
          apply finite_protocol_plan_from_one.
          unfold protocol_transition.
          split.
          apply feasible_update_protocol.
          all : intuition.
        * rewrite Heqs' in IHli at 1.
          unfold chain_updates in IHli.
          rewrite Hchain; intuition.
      + unfold res; simpl.
        change (feasible_update_composite s i :: chain_updates li s) with
                ([feasible_update_composite s i] ++ chain_updates li s).
        rewrite (apply_plan_app X).
        destruct (apply_plan X s [feasible_update_composite s i]) as (tr_short, res_short) eqn : eq_short.
        assert (res_short = snd (apply_plan X s [feasible_update_composite s i])) by (rewrite eq_short; intuition).
        destruct (apply_plan X res_short (chain_updates li s)) as (tr_long, res_long) eqn : eq_long.
        assert (res_long = snd (apply_plan X res_short (chain_updates li s))) by (rewrite eq_long; intuition).

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
             subst j.
             rewrite Hsame.
             rewrite H0.
             unfold apply_plan.
             unfold _apply_plan_folder; simpl.
             rewrite state_update_eq.
             rewrite <- update_consensus_clean with (value := (feasible_update_value (s i) i)).
             rewrite (@project_same index index_listing Hfinite).
             reflexivity.
             apply protocol_state_component_no_bottom; intuition.
          -- destruct IHli as [_ [IHli _]].
             specialize (IHli j).
             spec_save IHli. {
               destruct Hjli;[intuition congruence|intuition].
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
          assert (Hge_short : set_eq (GE res_short) (GE s)). {
            remember (update_consensus (update_state (s i) (s i) i) (feasible_update_value (s i) i)) as new_si.
            remember (state_update IM_index s i new_si) as new_s.
            assert (Hu: res_short = new_s). {
              rewrite H0.
              rewrite Heqnew_s.
              unfold apply_plan.
              unfold feasible_update_composite; simpl.
              rewrite Heqnew_si.
              reflexivity.
            }
            specialize (GE_existing_same s Hprs (feasible_update_value (s i) i) i) as Hexist.
            specialize (GE_existing_same_rev s Hprs (feasible_update_value (s i) i) i) as Hexist'.

            spec Hexist'. {
              unfold GE.
              apply wH_wE'.
              intuition.
            }
            simpl in Hexist, Hexist'.

            rewrite Hu.
            rewrite Heqnew_s.
            rewrite Heqnew_si.
            unfold set_eq.
            split;[apply Hexist|apply Hexist'].
          }

          assert (Hge_long : set_eq (GE res_long) (GE res_short)). {
            destruct IHli as [_ [_ IHli]].
            unfold chain_updates in IHli.
            rewrite <- Hchain in IHli.
            rewrite H2 in IHli.
            unfold chain_updates in H1.
            rewrite H1.
            apply IHli.
          }

          apply set_eq_tran with (s2 := (GE res_short)).
          assumption.
          assumption.
  Qed.

  (** Some wrappers for clarity of expoisition going forward. *)

  Definition send_phase_plan (s : vstate X) : plan X :=
    chain_updates (GH s) s.

  Definition send_phase (s : vstate X) : list (vtransition_item X) * vstate X :=
    apply_plan X s (send_phase_plan s).

  Definition send_phase_result
    (s : vstate X) :=
    snd (send_phase s).

  Definition send_phase_transitions
    (s : vstate X) :=
    fst (send_phase s).

  Remark send_phase_protocol
    (s : vstate X)
    (Hprs : protocol_state_prop X s)
    (Hnf : no_component_fully_equivocating s (GH s)) :
    finite_protocol_plan_from X s (send_phase_plan s).
  Proof.
    unfold send_phase_plan.
    specialize (chain_updates_protocol s Hprs (GH s) (GH_NoDup s)) as Hchain.
    spec Hchain. intuition.
    specialize (Hchain Hnf). simpl in Hchain.
    unfold send_phase_result.
    destruct Hchain as [Hchain1 [Hchain2 Hchain3]].
    intuition.
  Qed.

  Corollary send_phase_result_protocol
    (s : vstate X)
    (Hprs : protocol_state_prop X s)
    (Hnf : no_component_fully_equivocating s (GH s))
    (res_send := send_phase_result s) :
    protocol_state_prop X res_send.
  Proof.
    apply apply_plan_last_protocol.
    intuition.
    apply send_phase_protocol.
    all : intuition.
  Qed.

  Remark send_phase_GE
    (s : vstate X)
    (Hprs : protocol_state_prop X s)
    (Hnf : no_component_fully_equivocating s (GH s)) :
    set_eq (GE (send_phase_result s)) (GE s).
  Proof.
    unfold send_phase_plan.
    specialize (chain_updates_protocol s Hprs (GH s) (GH_NoDup s)) as Hchain.
    spec Hchain. intuition.
    specialize (Hchain Hnf). simpl in Hchain.
    unfold send_phase_result.
    destruct Hchain as [Hchain1 [Hchain2 Hchain3]].
    unfold send_phase. intuition.
  Qed.

  Remark send_phase_future
    (s : vstate X)
    (Hnf : no_component_fully_equivocating s (GH s))
    (Hspr : protocol_state_prop _ s) :
    in_futures _ s (send_phase_result s).
  Proof.
    unfold in_futures.
    exists (send_phase_transitions s).
    split.
    apply send_phase_protocol.
    assumption.
    assumption.
    unfold send_phase_transitions.
    unfold send_phase_result.
    apply (apply_plan_last X).
  Qed.

  Remark send_phase_result_projections
    (s : vstate X)
    (Hprss : protocol_state_prop _ s)
    (Hnf : no_component_fully_equivocating s (GH s))
    (i : index)
    (Hin : In i (GH s))
    (s' := send_phase_result s) :
    project (s' i) i = (s i).
  Proof.
    apply chain_updates_protocol.
    intuition.
    apply GH_NoDup.
    all : intuition.
  Qed.

  Remark non_self_projections_same_after_send_phase
    (s : vstate X)
    (Hpr : protocol_state_prop X s)
    (Hnf : no_component_fully_equivocating s (GH s))
    (res_send := send_phase_result s) :
    forall (i j : index), i <> j -> project (res_send i) j = project (s i) j.
  Proof.
    intros.
    specialize (non_self_projections_same_after_sends s Hpr (send_phase_plan s)) as Hsame.
    spec Hsame. {
      apply send_phase_protocol.
      intuition.
      intuition.
    }
    spec Hsame. {
      intros.
      apply in_map_iff in H0.
      destruct H0 as [k [Heq Hink]].
      unfold feasible_update_composite in Heq.
      unfold feasible_update_single in Heq.
      simpl in Heq.
      rewrite <- Heq.
      simpl.
      exists (feasible_update_value (s k) k).
      intuition.
    }
    specialize (Hsame i j H).
    intuition.
  Qed.

  Definition lift_to_receive_item (to from : index) (s : state): vplan_item (IM_index to) :=
    @Build_plan_item _ (type (IM_index to)) receive (Some (from, s)).

  (** Construct a [plan X] such that <s to> will receive the messages
     in <ls>. *)

  Definition sync_plan (to from : index) (ls : list state) : (plan X) :=
    let tmp := List.map (lift_to_receive_item to from) ls in
    List.map (lift_to_composite_plan_item IM_index to) tmp.

  (** Construct a plan which syncs up <<project (s to) from>> with
     <<project s' from>> via receiving messages. If the states' <<from>> histories
     don't match, None is returned.
     See [Lib/ListExtras.v] for [complete_suffix]. *)

  Definition sync (s : vstate X) (s': state) (to from : index) : option (plan X) :=
    let history_s := get_history (s to) from in
    let history_s' := get_history s' from in
    let rem_states := complete_suffix history_s' history_s in
    match rem_states with
    | None => None
    | Some ss => let rem_plan := sync_plan to from (rev ss) in
                 Some rem_plan
    end.

  (** The syncing plan is protocol and it does what is expected.
    Note the index <<inter>>, which denotes the validator which
    owns the projection we will choose to sync to. *)

  Lemma one_sender_receive_protocol
    (s s': vstate X)
    (Hpr : protocol_state_prop X s)
    (Hpr' : protocol_state_prop X s')
    (to inter from : index)
    (Hhist : get_history (s inter) from = get_history (s' inter) from)
    (Hdif : to <> from)
    (a : plan X)
    (Hsync : sync s (s' inter) to from = Some a) :
    let res := snd (apply_plan X s a) in
    finite_protocol_plan_from X s a /\
    (project (res to) from = project (s' inter) from).
   Proof.
    generalize dependent s.
    induction a.
    - intros. simpl in *.
      unfold finite_protocol_plan_from. simpl.
      repeat split.
        + apply finite_ptrace_empty.
          assumption.
        + unfold res.
          unfold sync in Hsync.
          destruct (complete_suffix (get_history (s' inter) from) (get_history (s to) from)) eqn : eq_cs.
          2 : discriminate Hsync.
          apply complete_suffix_correct in eq_cs.
          assert (l = []). {
            inversion Hsync.
            unfold sync_plan in H0.
            apply map_eq_nil in H0.
            apply map_eq_nil in H0.
            destruct (decide (length l = 0)).
            - apply length_zero_iff_nil in e. intuition.
            - apply length_zero_iff_nil in H0. rewrite rev_length in H0. congruence.
          }
          rewrite H in eq_cs. simpl in eq_cs.
          symmetry in eq_cs.
          apply (@eq_history_eq_project index index_listing Hfinite) in eq_cs.
          assumption.
    - intros. simpl in *.

      change (a :: a0) with ([a] ++ a0).
      rewrite <- finite_protocol_plan_from_app_iff.

      unfold sync in Hsync.
      destruct (complete_suffix (get_history (s' inter) from) (get_history (s to) from)) eqn : eq_cs. 2: discriminate Hsync.

      inversion Hsync.
      unfold sync_plan in H0.
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
      unfold lift_to_composite_plan_item in Hh.

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
          + specialize (sent_component_protocol_composed IM_index (free_constraint IM_index) Hfinite has_been_sent_capabilities (fun m => Some (fst m)) s') as Hope.
            spec Hope. assumption.
            specialize (Hope inter (from, sa)).
            apply Hope.
            unfold has_been_sent.
            simpl.
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
          + specialize (received_component_protocol_composed IM_index (free_constraint IM_index) Hfinite (fun m => Some (fst m)) has_been_received_capabilities s') as Hope.
            spec Hope. assumption.
            specialize (Hope inter (from, sa)).
            apply Hope.
            unfold has_been_received.
            simpl.
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
          all : intuition.
        - intuition.
      }

      subst input_a.
      unfold res.

      specialize (IHa s0).
      spec IHa.
      apply protocol_transition_destination in H.
      assumption.

      assert (Hs0 : s0 = (state_update IM_index s to (update_state (s to) sa from))). {
        destruct H as [_ H].
        unfold transition in H.
        simpl in H. unfold vtransition in H. unfold transition in H. simpl in H.
        inversion Hh.
        rewrite <- H2 in H.
        inversion H.
        intuition.
      }

      assert (Honefold: get_history (s0 to) from = [sa] ++ get_history (s to) from). {
          assert (project (s0 to) from = sa). {
              rewrite Hs0. rewrite state_update_eq.
              apply (@project_same index index_listing Hfinite).
              apply protocol_state_component_no_bottom. intuition.
          }
            subst sa.
            rewrite eq_cs.
            apply (@unfold_history_cons index index_listing Hfinite).
            apply (@no_bottom_in_history index index_listing Hfinite) in Hinsa.
            assumption.
        }

      assert (Hneed : s0 inter = s inter). {
        rewrite Hs0.
        destruct (decide(to = inter)).
        - subst inter.
          rewrite Hhist in eq_cs'.
          clear -eq_cs'.
          remember (length (get_history (s' to) from)) as len.
          assert (length (get_history (s' to) from) = length ((rev tls ++ [sa]) ++ get_history (s' to) from)). {
            rewrite <- eq_cs'.
            intuition.
          }
          rewrite <- Heqlen in H.
          rewrite app_length in H.
          rewrite <- Heqlen in H.
          rewrite app_length in H.
          simpl in H.
          lia.
        - rewrite state_update_neq.
          all : intuition.
      }

      spec IHa. {
        rewrite Hneed.
        intuition.
      }

      spec IHa. {
        unfold sync.
        destruct (complete_suffix (get_history (s' inter) from) (get_history (s0 to) from)) eqn : eq_cs2.
        f_equal.
          unfold sync_plan.
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
      unfold finite_protocol_plan_from at 1.
      unfold apply_plan, _apply_plan. simpl in *.
      rewrite fold_right_app. simpl.
      match goal with
      |- context [let (_,_) := let (_,_) := ?t in _ in _] =>
        replace t with (s0, o)
      end.
      simpl in *.
      repeat split.
      + apply first_transition_valid. assumption.
      + apply IHa.
      + destruct IHa as [_ IHa].
        rewrite <- IHa.
        unfold apply_plan, _apply_plan. simpl.
        f_equal.
        specialize (@_apply_plan_folder_additive _ (type X) (vtransition X) s0 (rev a0) ) as Hadd.

        match goal with
        |- context[[?item]] => specialize (Hadd [item])
        end.
        simpl in Hadd. simpl.
        match goal with
        |- _ = snd (let (final, items) := ?f in _) to =>
          destruct f as (tr', dest') eqn : eqf2
        end.
        match type of Hadd with
        | let (_,_) := ?f in _ => replace f with (tr', dest') in Hadd
        end.
        simpl in *.
        match goal with
        |- snd (let (final, items) := ?f in _) to = _ =>
          match type of Hadd with _ = ?r =>
            replace f  with r
          end
        end.
        reflexivity.
    Qed.

   (** We look for suitable projections among the honest validators *)

    Definition get_candidates
      (s : vstate X) :
      list state
      :=
    component_list s (GH s).

    Existing Instance state_lt'_dec.
    Existing Instance state_lt_ext_dec.

    (** Retain only projections which are maximal, i.e, no other projections
       compare greater to them. *)

    Definition get_topmost_candidates
      (s : vstate X)
      (target : index) :
      list state
      :=
      get_maximal_elements (fun s s' => bool_decide (state_lt_ext target (project s target) (project s' target))) (get_candidates s).

    (** If <<i>> is honest, all candidate projections onto <<i>> compare less than
       <<(s i)>> *)

    Lemma honest_self_projections_maximal1
      (s : vstate X)
      (Hpr : protocol_state_prop X s)
      (i j : index)
      (Hhonest : In i (GH s)) :
      state_lt_ext i (project (s j) i) (s i).
    Proof.
      assert (Hsnb : forall (i : index), (s i) <> Bottom). {
        intros.
        apply protocol_state_component_no_bottom.
        intuition.
      }
    unfold state_lt_ext.
    destruct (s i) eqn : eq_si;[specialize (Hsnb i);congruence|].
    destruct (project (s j) i) eqn : eq_pji;[left; intuition congruence|].
    destruct (decide (state_lt' i (project (s j) i) (s i)));right; rewrite <- eq_si; rewrite <- eq_pji.
    - intuition.
    - assert (He : In i (GE s)). {
        apply GE_direct.
        unfold cequiv_evidence.
        unfold equivocation_evidence.
        setoid_rewrite hbo_cobs'.
        exists (SimpObs State' i (s i)).
        unfold get_simp_event_subject_some. simpl.
        split.
        - apply in_cobs_states'.
          apply state_obs_present. apply in_listing.
        - split;[intuition|].
          exists (SimpObs Message' i (project (s j) i)). simpl.
          split.
          + apply in_cobs_messages'.
            apply cobs_single_m.
            exists j. split;[apply in_listing|].
            apply refold_simp_lv_observations1.
            apply Hsnb.
            rewrite eq_pji. congruence.
            intuition.
          + split;[intuition|].
            unfold simp_lv_event_lt.
            unfold comparable.
            rewrite decide_True by intuition.
            intros contra.
            destruct contra.
            * congruence.
            * rewrite decide_True in H by intuition.
              destruct H;[intuition|].
              intuition.
      }
      unfold GH in Hhonest.
      apply wH_wE' in Hhonest. intuition.
  Qed.

  (** Similar statement, stating a <= relation with <<project (s i) i>>. *)

  Lemma honest_self_projections_maximal2
    (s : vstate X)
    (Hpr : protocol_state_prop X s)
    (i j : index)
    (Hhonest : In i (GH s)) :
    project (s j) i = project (s i) i \/ state_lt_ext i (project (s j) i) (project (s i) i).
  Proof.
    assert (Hsnb : forall (i : index), (s i) <> Bottom). {
      intros.
      apply protocol_state_component_no_bottom.
      intuition.
    }
    unfold state_lt_ext.
    destruct (s i) eqn : eq_si;[specialize (Hsnb i);congruence|]. rewrite <- eq_si.

    specialize (honest_self_projections_maximal1 s Hpr i j Hhonest) as Hh.
    destruct (project (s i) i) eqn : eq_pii.
    - destruct (project (s j) i) eqn : eq_pji.
      + left. intuition.
      + rewrite <- eq_pji in *.
        unfold state_lt_ext in Hh.
        destruct Hh;[intuition congruence|].
        unfold state_lt' in H.
        rewrite unfold_history_bottom in H by intuition.
        intuition.
    - unfold state_lt_ext in Hh.
      destruct Hh;[intuition congruence|].
      rewrite <- eq_pii in *.
      destruct (project (s j) i) eqn : eq_pji;[right;left;intuition congruence|].
      rewrite <- eq_pji in *.
      destruct (decide (project (s j) i = project (s i) i));[left;intuition|].
      right. right.

      unfold state_lt' in H.
      apply in_split in H as H2.
      destruct H2 as [left1 [right1 Heq1]].
      apply (@unfold_history index index_listing Hfinite) in Heq1 as Heq1'.
      rewrite Heq1' in Heq1.
      rewrite (@unfold_history_cons index index_listing Hfinite) in Heq1 by (intuition congruence).
      destruct left1.
      + simpl in Heq1. inversion Heq1. congruence.
      + inversion Heq1.
        unfold state_lt'.
        rewrite H2.
        apply in_app_iff. right. intuition.
  Qed.

  Lemma honest_always_candidate_for_self
      (s : vstate X)
      (Hpr : protocol_state_prop X s)
      (i : index)
      (Hhonest : In i (GH s)) :
      In (s i) (get_topmost_candidates s i).
  Proof.
     - unfold get_topmost_candidates.
      unfold get_maximal_elements.
      apply filter_In.
      split.
      + unfold get_candidates. apply in_map_iff. exists i. intuition.
      + rewrite forallb_forall. intros.
        rewrite negb_true_iff.
        rewrite bool_decide_eq_false.
        apply in_map_iff in H.
        destruct H as [j [Heqj Hinj]]. subst x.
        specialize (honest_self_projections_maximal2 s Hpr i j Hhonest) as Hh.
        intros contra.
        destruct Hh.
        * unfold state_lt_ext in contra.
          destruct contra;[intuition congruence|].
          rewrite H in H0.
          unfold state_lt' in H0.
          apply (@history_no_self_reference index index_listing Hfinite) in H0.
          intuition.
        * apply (@state_lt_ext_antisymmetric index index_listing Hfinite) in H.
          intuition.
  Qed.

  Lemma all_candidates_for_honest_equiv
    (s : vstate X)
    (Hpr : protocol_state_prop X s)
    (i : index)
    (Hhonest : In i (GH s)) :
    forall (s' : (@state index index_listing)),
    In s' (get_topmost_candidates s i) -> project s' i = project (s i) i.
  Proof.
    intros.
    unfold get_topmost_candidates in H.
    unfold get_maximal_elements in H.
    apply filter_In in H.
    destruct H as [Hin H].
    rewrite forallb_forall in H.
    specialize (H (s i)).
    spec H. {
      apply in_map_iff. exists i. intuition.
    }
    rewrite negb_true_iff in H.
    rewrite bool_decide_eq_false in H.
    destruct (decide (project (s i) i = project s' i));[intuition|].

    apply in_map_iff in Hin.
    destruct Hin as [j [Heqj Hj]].
    subst s'.
    specialize (honest_self_projections_maximal2 s Hpr i j Hhonest) as Hh.
    destruct Hh;[intuition congruence|].
    intuition.
  Qed.

  (** Find the state we want to sync to.
     Choose a candidate for which syncing is valid. If none exists, default to your
     own projection. *)

    Definition get_matching_state
      (s : vstate X)
      (to from : index) : state :=
      let candidates := (get_topmost_candidates s from) in
      let found := List.find (fun s' => bool_decide (state_lt_ext from (project (s to) from) s')) candidates in
      match found with
      | Some s' => s'
      | None => (s to)
      end.

    Remark get_matching_state_correct1
      (s : vstate X)
      (to from : index) :
      exists (inter : index), (get_matching_state s to from) = (s inter) /\
      (inter = to \/ (In inter (GH s))).
    Proof.
      unfold get_matching_state.
      destruct (find (fun s' : state => bool_decide (state_lt_ext from (project (s to) from) s'))
      (get_topmost_candidates s from)) eqn : eq_find.
      - apply find_some in eq_find.
        destruct eq_find as [eq_find _].
        unfold get_topmost_candidates in eq_find.
        unfold get_maximal_elements in eq_find.
        apply filter_In in eq_find.
        destruct eq_find as [eq_find _].
        unfold get_candidates in eq_find.
        unfold component_list in eq_find.
        apply in_map_iff in eq_find.
        destruct eq_find as [inter Hinter].
        exists inter. intuition.
      - exists to. intuition.
    Qed.

    Remark get_matching_state_correct2
      (s : vstate X)
      (to from : index)
      (Hin : In to (GH s)) :
      exists (inter : index), In inter (GH s) /\ (get_matching_state s to from) = (s inter).
    Proof.
      specialize (get_matching_state_correct1 s to from) as H1.
      destruct H1 as [inter Hinter].
      exists inter.
      destruct Hinter as [Hmatch Hinter].
      destruct Hinter;[subst to;intuition|intuition].
    Qed.

    (** The following results are used to show that there exists at least
       one maximal candidate. We do this by relating the comparison operator
       to comparing history lengths between candidates. The maximal candidate
       will have the longest <<from>> history. *)

    Definition top_history
      (s : vstate X)
      (from : index) :=
      let history_lengths := List.map (fun s' : state => length (get_history s' from)) (get_candidates s) in
      let max_length := list_max history_lengths in
      filter (fun s' : state => beq_nat (length (get_history s' from)) max_length) (get_candidates s).

    Lemma top_history_something
      (s : vstate X)
      (H : GH s <> [])
      (from : index) :
      exists (s' : state), In s' (top_history s from).
    Proof.
      unfold top_history.
      specialize (list_max_exists2 (List.map (fun s' : state => length (get_history s' from)) (get_candidates s))) as Hmax.
      spec Hmax. {
        destruct (map (fun s' : state => length (get_history s' from)) (get_candidates s)) eqn : eq.
        apply map_eq_nil in eq.
        unfold get_candidates in eq.
        apply map_eq_nil in eq. intuition congruence.
        intuition congruence.
      }
      apply in_map_iff in Hmax.
      destruct Hmax.
      exists x. apply filter_In. split;[intuition|].
      rewrite beq_nat_true_iff. intuition.
    Qed.

    Lemma topmost_candidates_nonempty
      (s : vstate X)
      (from : index)
      (Hne : GH s <> []) :
      exists (s' : state), In s' (get_topmost_candidates s from).
    Proof.
      specialize (top_history_something s Hne from) as Htop_hist.
      destruct Htop_hist as [s' Htop].
      exists s'.
      unfold get_topmost_candidates.
      apply filter_In.
      unfold top_history in Htop.
      apply filter_In in Htop.
      split;[intuition|].
      destruct Htop as [_ Htop].
      rewrite beq_nat_true_iff in Htop.
      rewrite forallb_forall.
      intros.
      rewrite negb_true_iff.
      rewrite bool_decide_eq_false.
      intros contra.
      specialize (list_max_le (map (fun s'0 : state => length (get_history s'0 from)) (get_candidates s))) as Hmax.
      specialize (Hmax (length (get_history s' from))).
      rewrite Htop in Hmax.
      destruct Hmax as [Hmax _]. spec Hmax. lia.
      rewrite Forall_forall in Hmax.
      specialize (Hmax (length (get_history x from))).
      spec Hmax. {
        apply in_map_iff.
        exists x. intuition.
      }
      rewrite <- Htop in Hmax.
      unfold state_lt_ext in contra.
      destruct contra.
      - assert (get_history s' from = []) by (apply unfold_history_bottom;intuition).
        rewrite H1 in Hmax. simpl in Hmax.
        rewrite (@unfold_history_cons index index_listing Hfinite) in Hmax.
        simpl in Hmax. lia. intuition.
      - unfold state_lt' in H0.
        apply in_split in H0.
        destruct H0 as [left [right Hhist]].
        replace (left ++ project s' from :: right) with (left ++ [project s' from] ++ right) in Hhist.
        2 : intuition.
        specialize (@unfold_history index index_listing Hfinite _ (project x from) (project s' from) from) as Hunf.
        specialize (Hunf left right Hhist).
        rewrite Hunf in Hhist.
        assert (length (get_history (project x from) from) > length (get_history (project s' from) from)). {
          rewrite Hhist.
          simpl.
          rewrite app_length. simpl. lia.
        }

        destruct (project x from) eqn : eq_b;[simpl in *;lia|].
        rewrite (@unfold_history_cons index index_listing Hfinite) in Hmax by (intuition congruence).
        simpl in Hmax.
        destruct (project s' from) eqn : eq_b2.
        + assert (get_history s' from = []) by (apply unfold_history_bottom;intuition).
          rewrite H1 in Hmax. simpl in Hmax. lia.
        + assert (get_history s' from = (project s' from) :: get_history (project s' from) from). {
            apply (@unfold_history_cons index index_listing Hfinite). intuition congruence.
          }
          rewrite H1 in Hmax.
          simpl in Hmax.
          rewrite eq_b in Hmax. rewrite eq_b2 in Hmax.
          lia.
    Qed.

    Remark get_matching_state_correct3
      (s : vstate X)
      (to from : index)
      (Hin : In to (GH s))
      (Hcomp : forall (i j : index),
               In i (GH s) ->
               In j (GH s) ->
               comparable (state_lt_ext from) (project (s i) from) (project (s j) from)) :
      In (get_matching_state s to from) (get_topmost_candidates s from).
    Proof.
      unfold get_matching_state.
      destruct (find (fun s' : state => bool_decide (state_lt_ext from (project (s to) from) s'))
      (get_topmost_candidates s from)) eqn : eq_find.
      - apply find_some in eq_find. intuition.
      - unfold get_topmost_candidates.
        unfold get_maximal_elements.
        apply filter_In.
        split.
        + apply in_map_iff. exists to. intuition.
        + rewrite forallb_forall. intros.
          rewrite negb_true_iff.
          rewrite bool_decide_eq_false.
          intros contra.
          specialize (find_none (fun s' : state => bool_decide (state_lt_ext from (project (s to) from) s'))) as Hnone.
          specialize (Hnone (get_topmost_candidates s from) eq_find).

          apply in_map_iff in H.
          destruct H as [k [Hk Hk']].

          specialize (topmost_candidates_nonempty s from) as Htop.
          spec Htop. destruct (GH s); intuition congruence.
          destruct Htop as [s' Htop].
          specialize (Hnone s' Htop).
          simpl in Hnone. rewrite bool_decide_eq_false in Hnone.

          unfold get_topmost_candidates in Htop.
          unfold get_maximal_elements in Htop.

          apply filter_In in Htop.
          destruct Htop as [Hins' Htop].
          rewrite forallb_forall in Htop.

          apply in_map_iff in Hins'.
          destruct Hins' as [l [Heql Hinl]].
          specialize (Hcomp k l Hk' Hinl).
          subst x. subst s'.
          specialize (Htop (s k)).
          spec Htop. apply in_map_iff. exists k; intuition.
          rewrite negb_true_iff in Htop.
          rewrite bool_decide_eq_false in Htop.
          unfold comparable in Hcomp.
          destruct Hcomp as [Hcomp|Hcomp].
          * rewrite Hcomp in contra.
            apply (@state_lt_ext_proj index index_listing Hfinite) in contra.
            intuition.
          * destruct Hcomp as [Hcomp|Hcomp].
            -- assert (state_lt_ext from (project (s to) from) (project (s l) from)). {
                apply (@state_lt_ext_tran index index_listing Hfinite) with (s2 := (project (s k) from)); intuition.
              }
              apply (@state_lt_ext_proj index index_listing Hfinite) in H.
              intuition.
            -- intuition.
   Qed.

   Lemma get_matching_state_for_honest
    (s : vstate X)
    (Hpr : protocol_state_prop X s)
    (i j : index)
    (Hhonest : In i (GH s)) :
    project (get_matching_state s j i) i = project (s i) i.
  Proof.
    unfold get_matching_state.
    destruct (find (fun s' : state => bool_decide (state_lt_ext i (project (s j) i) s'))
    (get_topmost_candidates s i)) eqn : eq_find.
    - apply find_some in eq_find.
      destruct eq_find as [Hin Hcomp].
      rewrite bool_decide_eq_true in Hcomp.
      specialize (all_candidates_for_honest_equiv s Hpr i Hhonest).
      intros.
      specialize (H s0 Hin).
      intuition.
    - specialize (find_none (fun s' : state => bool_decide (state_lt_ext i (project (s j) i) s'))) as Hnone.
      specialize (Hnone (get_topmost_candidates s i) eq_find).
      specialize (Hnone (s i)).

      assert (In (s i) (get_topmost_candidates s i)). {
         apply honest_always_candidate_for_self.
         intuition.
         intuition.
      }

      specialize (Hnone H).
      simpl in Hnone.
      rewrite bool_decide_eq_false in Hnone.
      specialize (honest_self_projections_maximal1 s Hpr i j Hhonest) as Hh.
      intuition.
  Qed.

    Definition get_matching_plan
      (s : vstate X)
      (from to : index) : plan X :=
      match (sync s (get_matching_state s to from) to from) with
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
      destruct (find (fun s' : state => bool_decide (state_lt_ext from (project (s to) from) s'))
               (get_topmost_candidates s from)) eqn : eq_find.
      - apply find_some in eq_find.
        destruct eq_find as [_ eq_find].
        unfold sync in contra.
        destruct (complete_suffix (get_history s0 from) (get_history (s to) from)) eqn : eq_suf.
        discriminate contra.
        unfold state_ltb' in eq_find.
        rewrite bool_decide_eq_true in eq_find.
        unfold state_lt_ext in eq_find.
        destruct eq_find as [eq_find|eq_find].
        + destruct eq_find as [Hb _].
          apply unfold_history_bottom in Hb.
          rewrite Hb in eq_suf.
          rewrite complete_suffix_empty in eq_suf.
          congruence.
        + unfold state_lt' in eq_find.
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

    Lemma get_matching_plan_effect
      (s : vstate X)
      (Hprs : protocol_state_prop X s)
      (s' : state)
      (from to : index)
      (Hdif : from <> to)
      (Hmatch : get_matching_state s to from = s') :
      let res := snd (apply_plan X s (get_matching_plan s from to)) in
      finite_protocol_plan_from X s (get_matching_plan s from to) /\
      project (res to) from = project s' from.
    Proof.
      simpl.
      unfold get_matching_plan.
      rewrite Hmatch.
      destruct (sync s s' to from) eqn : eq_sync.
      - unfold sync in eq_sync.
        destruct (complete_suffix (get_history s' from) (get_history (s to) from)) eqn : eq_suf;[|congruence].
        assert (eq_suf_original := eq_suf).
        apply complete_suffix_correct in eq_suf.
        inversion eq_sync.
        specialize (one_sender_receive_protocol s s Hprs Hprs to) as Hone.
        unfold get_matching_state in Hmatch.
        destruct (find (fun s'0 : state => bool_decide (state_lt_ext from (project (s to) from) s'0))
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

          specialize (Hone inter from eq_refl).
          spec Hone. {
            intuition.
          }

          specialize (Hone (sync_plan to from (rev l))).

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
          intuition.
        + rewrite <- Hmatch.
          rewrite <- Hmatch in eq_suf.
          assert (Hempty: l = []). {
            replace (get_history (s to) from) with ([] ++ (get_history (s to) from)) in eq_suf at 1.
            apply app_inv_tail in eq_suf.
            all : intuition.
          }
          rewrite Hempty.
          simpl.
          unfold sync_plan; simpl.
          intuition.
          apply finite_protocol_plan_empty.
          assumption.
      - rewrite <- Hmatch in eq_sync.
        apply sync_some in eq_sync.
        intuition.
    Qed.

    (** Results of this type are useful for quickly unpacking
       information about the constructed plan. *)

    Remark get_matching_plan_info
      (s : vstate X)
      (from to : index)
      (ai : plan_item)
      (Hin : In ai (get_matching_plan s from to)) :
      let component := projT1 (label_a ai) in
      let label := projT2 (label_a ai) in
      label = receive /\
      component = to /\
      (exists (so : state), (input_a ai = Some (from, so)) /\ In (SimpObs Message' from so) (cobs_messages s from)).
    Proof.
      unfold get_matching_plan in Hin.
      remember (get_matching_state s to from) as s0.
      destruct (sync s s0 to from) eqn : eq_sync.
        + unfold sync in eq_sync.
          destruct (complete_suffix (get_history s0 from) (get_history (s to) from)) eqn : eq_hist;[|congruence].
          inversion eq_sync.
          unfold sync_plan in H0.
          rewrite <- H0 in Hin.
          apply in_map_iff in Hin.
          destruct Hin as [x [Hlift Hinx]].

          apply in_map_iff in Hinx.
          destruct Hinx as [so [Hlift_rec Hinso]].
          unfold lift_to_receive_item in Hlift_rec.
          subst x.
          unfold lift_to_composite_plan_item in Hlift.
          rewrite <- Hlift. simpl.
          split;[intuition|].
          split;[intuition|].
          exists so. split;[intuition|].
          apply in_rev in Hinso.
          apply complete_suffix_correct in eq_hist.
          assert (In so (get_history s0 from)). {
            rewrite eq_hist.
            apply in_app_iff. left.
            intuition.
          }
          rewrite Heqs0 in H.
          specialize (get_matching_state_correct1 s to from) as Hinter.
          destruct Hinter as [inter [Heq_inter _]].
          rewrite Heq_inter in H.
          apply (@in_history_in_observations index index_listing Hfinite) in H.
          apply cobs_single_m.
          exists inter. intuition.
          apply in_listing.
        + contradict Hin.
    Qed.

    (** Construct a plan in which indices in <<li>> sync their
       <<from>> projections. *)

    Definition get_receives_for
      (s : vstate X)
      (li : list index)
      (from : index) : plan X :=
      let matching_plans := List.map (get_matching_plan s from) li in
      List.concat matching_plans.

    Remark get_receives_for_info
      (s : vstate X)
      (li : list index)
      (from : index)
      (ai : vplan_item X)
      (Hin : In ai (get_receives_for s li from)) :
      let component := projT1 (label_a ai) in
      let label := projT2 (label_a ai) in
      label = receive /\
      In component li /\
      (exists (so : state), (input_a ai = Some (from, so)) /\ In (SimpObs Message' from so) (cobs_messages s from)).
    Proof.
      unfold get_receives_for in Hin.
      apply in_concat in Hin.
      destruct Hin as [smaller [Hin_smaller Hin_ai]].

      apply in_map_iff in Hin_smaller.
      destruct Hin_smaller as [i [Heq_matching Hini]].

      rewrite <- Heq_matching in Hin_ai.
      apply get_matching_plan_info in Hin_ai.
      simpl in *.
      split;[intuition|].
      split.
      - destruct Hin_ai as [_ [Hin_ai]].
        rewrite Hin_ai. intuition.
      - destruct Hin_ai as [_ [_ Hin_ai]].
        destruct Hin_ai as [so Hso].
        exists so. intuition.
    Qed.

    Lemma get_receives_for_correct
        (s : vstate X)
        (Hpr : protocol_state_prop X s)
        (li : list index)
        (from : index)
        (Hnodup : NoDup li)
        (Hnf : ~ In from li) :
        let res := snd (apply_plan X s (get_receives_for s li from)) in
        finite_protocol_plan_from X s (get_receives_for s li from) /\
        forall (i : index), In i li -> project (res i) from = project (get_matching_state s i from) from.
    Proof.
      induction li using rev_ind; intros.
      - unfold get_receives_for. simpl.
        split.
        apply finite_protocol_plan_empty.
        assumption.
        intuition.
      - unfold res.
        unfold get_receives_for.
        rewrite map_app.
        rewrite concat_app. simpl in *.
        rewrite app_nil_r.

        rewrite apply_plan_app.

        destruct (apply_plan X s (concat (map (get_matching_plan s from) li))) as (tr_long, res_long) eqn : eq_long.
        destruct (apply_plan X res_long (get_matching_plan s from x)) as (tr_short, res_short) eqn : eq_short.
        simpl.

        assert (Hres_long : res_long = snd (apply_plan X s (concat (map (get_matching_plan s from) li)))). {
          rewrite eq_long. intuition.
        }

        assert (Hres_short : res_short = snd ((apply_plan X res_long (get_matching_plan s from x)))). {
          rewrite eq_short. intuition.
        }

        assert (Hnodup_li : NoDup li). {
          apply NoDup_rev in Hnodup.
          rewrite rev_app_distr in Hnodup.
          simpl in Hnodup.
          apply NoDup_cons_iff in Hnodup.
          destruct Hnodup as [_ Hnodup].
          apply NoDup_rev in Hnodup.
          rewrite rev_involutive in Hnodup.
          intuition.
        }

        assert (Hnf_li : ~In from li). {
          intros contra.
          contradict Hnf.
          apply in_app_iff.
          left. intuition.
        }

        assert (Hnxf : x <> from). {
          intros contra.
          rewrite contra in Hnf.
          intuition.
        }

        assert (Hnx_li : ~In x li). {
          intros contra.
          apply in_split in contra.
          destruct contra as [lf [rt Heq]].
          rewrite Heq in Hnodup.
          apply NoDup_remove_2 in Hnodup.
          contradict Hnodup.
          rewrite app_nil_r.
          apply in_app_iff.
          right. intuition.
        }

        specialize (IHli Hnodup_li Hnf_li).

        assert (Hrem : forall (i : index), ~In i li -> res_long i = s i). {
          intros.
          rewrite Hres_long.
          apply irrelevant_components.
          intros contra.
          apply in_map_iff in contra.
          destruct contra as [some [Hproj Hinsome]].

          apply in_map_iff in Hinsome.
          destruct Hinsome as [pi [Hlabel Inpi]].
          apply in_concat in Inpi.
          destruct Inpi as [lpi [Hlpi Hinlpi]].
          apply in_map_iff in Hlpi.
          destruct Hlpi as [j [Hmatch Hwhat]].
          rewrite <- Hmatch in Hinlpi.
          apply get_matching_plan_info in Hinlpi.
          rewrite <- Hlabel in Hproj.
          assert (i = j). {
            rewrite <- Hproj.
            intuition.
          }
          clear Hproj. clear Hinlpi.
          subst i.
          intuition.
        }

        destruct IHli as [IHli_proto IHli_proj].

        assert (Hpr_long : protocol_state_prop X res_long). {
          apply apply_plan_last_protocol in IHli_proto.
          subst res_long.
          all : intuition.
        }

        assert (Hmatch_idx : incl (map (projT1 (P:=fun n : index => vlabel (IM_index n)))
               (map label_a (get_matching_plan s from x))) [x]). {
           unfold incl.
           intros.
           apply in_map_iff in H.
           destruct H as [smth [Hproj Hinsmth]].
           apply in_map_iff in Hinsmth.
           destruct Hinsmth as [pi [Hlabel Hinpi]].
           apply get_matching_plan_info in Hinpi.
           rewrite <- Hlabel in Hproj.
           destruct Hinpi as [_ [Hinpi _]].
           subst a. subst x.
           intuition.
        }

        assert (Hrem2 : forall (i : index), In i li -> res_long i = res_short i). {
          intros.
          assert (~In i [x]). {
            intros contra.
            destruct contra; [|intuition]. subst i.
            intuition.
          }
          subst res_long. subst res_short.
          symmetry.
          apply irrelevant_components.
          intros contra.
          assert (In i [x]). {
            unfold incl in Hmatch_idx.
            specialize (Hmatch_idx i contra).
            intuition.
          }
          intuition.
        }

        specialize (get_matching_plan_effect s Hpr (get_matching_state s x from) from x) as Heff.
        spec Heff. intuition.
        specialize (Heff eq_refl).

        simpl in Heff.
        destruct Heff as [Heff Heff2].

        apply relevant_components with (s' := res_long) (li0 := [x]) in Heff.

        2, 4 : intuition.
        2 : {
          intros.
          simpl in H. destruct H;[|intuition].
          subst i.
          specialize (Hrem x Hnx_li). intuition.
        }

        rewrite Hres_long in Heff.
        destruct Heff as [Heff_proto Heff_proj].

        split.
        + apply finite_protocol_plan_from_app_iff.
          split.
          * unfold get_receives_for in IHli_proto. intuition.
          * intuition.
        + intros.
          apply in_app_iff in H.
          destruct H as [H|H].
          * specialize (IHli_proj i H).
            rewrite <- IHli_proj.
            specialize (Hrem2 i H).
            rewrite <- Hrem2.
            rewrite Hres_long.
            intuition.
          * simpl in H. destruct H; [|intuition].
            subst i.
            subst res_short. subst res_long.
            specialize (Heff_proj x).
            spec Heff_proj. intuition. simpl in Heff_proj.
            rewrite <- Heff2.
            f_equal. simpl. assumption.
    Qed.

    Definition is_receive_plan
      (a : plan X) : Prop :=
      forall (ai : vplan_item X),
        In ai a -> projT2 (label_a ai) = receive.

    Definition is_receive_plan_app
      (a b : plan X) :
      is_receive_plan a /\ is_receive_plan b <-> is_receive_plan (a ++ b).
    Proof.
      unfold is_receive_plan.
      split; intros.
      - destruct H as [Hl Hr].
        apply in_app_iff in H0.
        destruct H0.
        + specialize (Hl ai). intuition.
        + specialize (Hr ai). intuition.
      - split; intros.
        + specialize (H ai).
          spec H. apply in_app_iff. left. intuition.
          intuition.
        + specialize (H ai).
          spec H. apply in_app_iff. right. intuition.
          intuition.
    Qed.

    Lemma receive_for_is_receive_plan
      (s : vstate X)
      (from : index)
      (li : list index) :
      is_receive_plan (get_receives_for s li from).
    Proof.
      unfold is_receive_plan. intros.
      apply get_receives_for_info in H.
      intuition.
    Qed.
    (** Receiving plans which don't involve the <<j>>'th components of nodes
       leave them unaffected. *)

    Lemma receives_neq
      (s : vstate X)
      (Hpr : protocol_state_prop X s)
      (a : plan X)
      (Hpra : finite_protocol_plan_from X s a)
      (i j : index)
      (Hreceive : is_receive_plan a)
      (Hj : forall (ai : vplan_item X),
            In ai a ->
            (exists (m : message), (input_a ai = Some m) /\ (fst m) <> j))
      (res := snd (apply_plan X s a)) :
      project (res i) j = project (s i) j.
    Proof.
      induction a using rev_ind.
      - intuition.
      - apply finite_protocol_plan_from_app_iff in Hpra.

        destruct Hpra as [Hpra_long Hpra_short].
        specialize (IHa Hpra_long); simpl in *.
        apply is_receive_plan_app in Hreceive.

        destruct Hreceive as [Hreceive_long Hreceive_short].
        specialize (IHa Hreceive_long); simpl.

        spec IHa. {
          intros.
          specialize (Hj ai).
          spec Hj. apply in_app_iff. left. intuition.
          intuition.
        }

        rewrite <- IHa.
        unfold res.
        rewrite apply_plan_app.
        destruct (apply_plan X s a) as [tr_long res_long].
        simpl in *.
        unfold apply_plan, _apply_plan, _apply_plan_folder.
        destruct x. simpl.

        unfold finite_protocol_plan_from in Hpra_short.
        unfold apply_plan,_apply_plan, _apply_plan_folder in Hpra_short.
        simpl in Hpra_short.
        destruct (vtransition X label_a (res_long, input_a)) eqn : eq_trans.
        simpl.
        simpl in Hpra_short.
        apply first_transition_valid in Hpra_short. simpl in Hpra_short.

        destruct Hpra_short as [Hprtr Htrans].

        unfold vtransition in eq_trans.
        unfold transition in eq_trans.
        simpl in eq_trans.
        unfold vtransition in eq_trans.
        unfold transition in eq_trans.
        simpl in eq_trans.
        remember label_a as label_a'.
        destruct label_a as [idx li].

        destruct li eqn : eq_li.
        + unfold is_receive_plan in Hreceive_short.
          specialize (Hreceive_short {| label_a := label_a'; input_a := input_a |}).
          move Hreceive_short at bottom.
          simpl in Hreceive_short.
          spec Hreceive_short. intuition.
          subst label_a'. simpl in Hreceive_short.
          congruence.
        + destruct input_a eqn : eq_input.
          * rewrite Heqlabel_a' in eq_trans.
            inversion eq_trans.
            destruct (decide (i = idx)).
            -- rewrite e. rewrite state_update_eq.
              rewrite (@project_different index index_listing).
              reflexivity.
              intuition.
              intros contra. {
                specialize (Hj {| label_a := label_a'; input_a := Some m |}).
                simpl in Hj.
                spec Hj. apply in_app_iff. right. intuition.
                destruct Hj as [m' [Hsome Hdif]].
                inversion Hsome. subst m'. intuition.
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
           unfold composite_valid in Hprtr.
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
      unfold composite_valid in *.
      unfold vvalid in *.
      intuition.
      unfold valid in *.
      unfold machine in *.
      simpl in *.
      destruct l as [j lj].
      destruct lj eqn : eq_lj.
      - destruct H0 as [_ Hd].
        discriminate Hd.
      - split ;[|intuition].
        simpl in i.
        subst i.
        rewrite <- Hsame.
        intuition.
    Qed.

    Lemma relevant_components_lv
      (s s' : vstate X)
      (Hprs : protocol_state_prop X s)
      (Hprs' : protocol_state_prop X s')
      (a : plan X)
      (Hrec : is_receive_plan a)
      (Hpr : finite_protocol_plan_from X s a)
      (f : index)
      (Hli : forall (ai : vplan_item X),
             In ai a -> (exists (m : message),
             input_a ai = Some m /\ fst m = f))
      (Hsame : forall (i : index), project (s i) f = project (s' i) f) :
      let res' := snd (apply_plan X s' a) in
      let res := snd (apply_plan X s a) in
      finite_protocol_plan_from X s' a /\
      forall (i : index), project (res' i) f = project (res i) f.
    Proof.
      induction a using rev_ind.
      - simpl.
        split. apply finite_protocol_plan_empty.
        assumption.
        intros.
        specialize (Hsame i).
        intuition.
      - simpl.

        apply is_receive_plan_app in Hrec.
        destruct Hrec as [Hrec_long Hrec_short].
        apply finite_protocol_plan_from_app_iff in Hpr.
        destruct Hpr as [Hpr_long Hpr_short].

        rewrite apply_plan_app.
        destruct (apply_plan X s' a) as (tr_long', res_long') eqn : eq_long'.
        destruct (apply_plan X res_long' [x]) as (tr_short', res_short') eqn : eq_short'.
        simpl.

        spec IHa. intuition.
        spec IHa. intuition.

        spec IHa. {
          clear -Hli.
          intros. specialize (Hli ai).
          spec Hli. apply in_app_iff. left. intuition.
          intuition.
        }

        simpl in IHa.
        destruct IHa as [Iha_pr Iha_proj].

        rewrite apply_plan_app.
        destruct (apply_plan X s a) as (tr_long, res_long) eqn : eq_long.
        destruct (apply_plan X res_long [x]) as (tr_short, res_short) eqn : eq_short.
        simpl in *.

        assert (res_long = snd (apply_plan X s a)). {
          rewrite eq_long.
          intuition.
        }

        assert (res_short = snd (apply_plan X res_long [x])). {
          rewrite eq_short.
          intuition.
        }

        assert (res_long' = snd (apply_plan X s' a)). {
          rewrite eq_long'.
          intuition.
        }

        assert (res_short' = snd (apply_plan X res_long' [x])). {
          rewrite eq_short'.
          intuition.
        }

        replace res_short' with (snd (apply_plan X res_long' [x])).
        replace res_short with (snd (apply_plan X res_long [x])).

        unfold apply_plan, _apply_plan, _apply_plan_folder.
        specialize (Hrec_short x).
        remember x as x'.
        destruct x as [label_x input_x].
        simpl.

        assert (Hprs_long : protocol_state_prop X res_long). {
          rewrite H.
          apply apply_plan_last_protocol.
          assumption.
          assumption.
        }

        assert (Hprs'_long : protocol_state_prop X res_long'). {
          rewrite H1.
          apply apply_plan_last_protocol.
          assumption.
          assumption.
        }

        unfold finite_protocol_plan_from in Hpr_short.
        unfold apply_plan, _apply_plan, _apply_plan_folder in Hpr_short.
        simpl in Hpr_short.
        rewrite Heqx' in Hpr_short.
        rewrite Heqx'.

        destruct (vtransition X label_x (res_long, input_x)) eqn : trans.

        apply first_transition_valid in Hpr_short. simpl in Hpr_short.

        simpl in *.
        destruct (vtransition X label_x (res_long', input_x)) eqn : trans'.
        simpl.

        remember Hpr_short as Hprotocol_trans.
        destruct Hpr_short as [Hprotocol_valid Htrans].

        unfold vtransition in trans, trans'.
        unfold transition in trans, trans'.
        simpl in *.
        unfold vtransition in trans, trans'.
        destruct label_x as [j label_x].
        simpl in trans, trans'.

        destruct label_x eqn : eq_label.
        {
          subst x'.
          unfold is_receive_plan in Hrec_short.
          simpl in Hrec_short.
          spec Hrec_short. intuition.
          congruence.
       }

        destruct input_x eqn : eq_input.
        2 : {
          unfold protocol_valid in Hprotocol_valid.
          unfold constrained_composite_valid in Hprotocol_valid.
          unfold composite_valid in Hprotocol_valid.
          unfold vvalid in Hprotocol_valid.
          unfold valid in Hprotocol_valid.
          simpl in Hprotocol_valid.
          destruct Hprotocol_valid as [e [b [c d]]].
          intuition.
        }

       assert (Hm : fst m = f). {
          simpl in *.
          specialize (Hli x').
          move Hli at bottom.
          spec Hli. apply in_app_iff. right. intuition.
          destruct Hli as [m' [Heqm' Heqf]].
          rewrite Heqx' in Heqm'.
          simpl in Heqm'. inversion Heqm'.
          intuition.
       }

        split.
        + apply finite_protocol_plan_from_app_iff.
          split.
          * assumption.
          * unfold finite_protocol_plan_from.
            simpl. rewrite eq_long'. simpl.
            apply first_transition_valid. simpl.
            split;[|intuition].
            destruct Hprotocol_trans as [Hprotocol_trans tmp].
            specialize (relevant_component_transition_lv res_long res_long') as Hrel.
            specialize (Hrel Hprs_long Hprs'_long (existT (fun n : index => vlabel (IM_index n)) j receive) m).
            rewrite H1 in Hrel.
            rewrite eq_long' in Hrel. simpl in Hrel.
            apply Hrel; [|assumption]. simpl.
            specialize (Iha_proj j).
            rewrite Hm.
            symmetry.
            intuition.
        + intros.
          subst x'. simpl in *.
          specialize (Iha_proj i).
         * inversion trans.
           inversion trans'.
           destruct (decide (i = j)).
           -- rewrite e.
              rewrite state_update_eq.
              rewrite state_update_eq.
              rewrite e in Iha_proj.
              clear -Iha_proj Hprs_long Hprs'_long.
              destruct (decide (f = (fst m))).
              ** rewrite <- e.
                 rewrite (@project_same index index_listing Hfinite).
                 rewrite (@project_same index index_listing Hfinite).
                 reflexivity.
                 all : (apply protocol_state_component_no_bottom; assumption).
              ** rewrite !(@project_different index index_listing Hfinite); [assumption| assumption | | assumption |].
                 (apply protocol_state_component_no_bottom; assumption).
                 (apply protocol_state_component_no_bottom; assumption).
          -- rewrite state_update_neq by assumption.
             rewrite state_update_neq by assumption.
             intuition.
    Qed.

    Definition others (i : index) (s : vstate X) :=
      set_remove idec i (GH s).

    Remark NoDup_others
      (i : index) (s : vstate X) :
      NoDup (others i s).
    Proof.
      unfold others.
      apply set_remove_nodup.
      apply GH_NoDup.
    Qed.

    Remark others_correct
      (i : index)
      (s : vstate X) :
      ~ In i (others i s).
    Proof.
      unfold others.
      intros contra.
      apply set_remove_2 in contra.
      intuition.
      apply GH_NoDup.
    Qed.

    Definition get_receives_all
      (s : vstate X)
      (lfrom : set index) : plan X :=
      let receive_fors := List.map (fun (i : index) => get_receives_for s (others i s) i) lfrom in
      List.concat receive_fors.

    Remark get_receives_all_info
      (s : vstate X)
      (lfrom : list index)
      (ai : vplan_item X)
      (Hin : In ai (get_receives_all s lfrom)) :
      let label := projT2 (label_a ai) in
      label = receive /\
      (exists (so : state) (from : index), (input_a ai = Some (from, so)) /\ In from lfrom /\ In (SimpObs Message' from so) (cobs_messages s from)).
    Proof.
      unfold get_receives_all in Hin.
      apply in_concat in Hin.
      destruct Hin as [smaller [Hin_smaller Hin_ai]].

      apply in_map_iff in Hin_smaller.
      destruct Hin_smaller as [from [Hrec Hinfrom]].
      rewrite <- Hrec in Hin_ai.
      apply get_receives_for_info in Hin_ai.
      simpl in *.
      split;[intuition|].
      destruct Hin_ai as [_ [_ Hin_ai]].
      destruct Hin_ai as [so Hso].
      exists so. exists from.
      intuition.
    Qed.

    Lemma get_receives_all_protocol
      (s : vstate X)
      (lfrom : set index)
      (Hnodup : NoDup lfrom)
      (Hprs : protocol_state_prop X s) :
      let res := snd (apply_plan X s (get_receives_all s lfrom)) in
      finite_protocol_plan_from X s (get_receives_all s lfrom) /\
      forall (f i : index),
      In f lfrom ->
      i <> f ->
      In i (GH s) ->
      project (res i) f = project (get_matching_state s i f) f.
    Proof.
      induction lfrom using rev_ind; unfold get_receives_all.
      - split; simpl.
        + apply finite_protocol_plan_empty. assumption.
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
        rewrite concat_app.
        rewrite apply_plan_app.

        match goal with
        |- context[apply_plan X s ?a] =>
           destruct (apply_plan X s a) as [tr_long res_long] eqn : eq_long
        end.

        match goal with
        |- context [apply_plan X res_long ?a] =>
           destruct (apply_plan X res_long a) as [tr_short res_short] eqn : eq_short
        end.
        simpl in *.

        rewrite app_nil_r in *.

        assert (res_short = snd (apply_plan X res_long (get_receives_for s (others x s) x))). {
          simpl.
          rewrite eq_short.
          intuition.
        }

        assert (res_long = snd (apply_plan X s (concat (map (fun i : index => get_receives_for s (others i s) i) lfrom)))). {
          match goal with
          |- context[apply_plan X s ?a] =>
             replace (apply_plan X s a) with (tr_long, res_long)
          end.
          intuition.
        }

        assert (Hrec_long':  is_receive_plan (get_receives_all s lfrom)). {
          unfold is_receive_plan. intros.
          apply get_receives_all_info in H1.
          intuition.
        }

        assert (Hrec_short : is_receive_plan (get_receives_for s (others x s) x)). {
          apply receive_for_is_receive_plan.
        }

        assert (Hprs_long : protocol_state_prop X res_long). {
          rewrite H0.
          apply apply_plan_last_protocol.
          assumption.
          assumption.
        }

        assert (Hx_after_long : forall (i : index), project (res_long i) x = project (s i) x). {
          intros.
          replace res_long with
            (snd (apply_plan X s (concat (map (fun i : index => get_receives_for s (others i s) i) lfrom)))).
          apply receives_neq.
          assumption.
          assumption.
          assumption.
          intros.
          apply in_concat in H1.
          destruct H1 as [le [Hinle Hinai]].
          apply in_map_iff in Hinle.
          destruct Hinle as [k [Hgr Hink]].
          rewrite <- Hgr in Hinai.
          apply get_receives_for_info in Hinai.
          destruct Hinai as [_ [_ Hinai]].
          destruct Hinai as [so [Hinso Hinso']].
          exists (k, so). split;[intuition|].
          simpl.
          destruct (decide (k = x));[|intuition].
          subst x. apply in_rev in Hink. intuition.
        }

        assert (Hsource: finite_protocol_plan_from X s (get_receives_for s (others x s) x)). {
          apply get_receives_for_correct.
          assumption.
          apply NoDup_others.
          apply others_correct.
        }

        specialize (relevant_components_lv s res_long Hprs Hprs_long (get_receives_for s (others x s) x)) as Hrel.
        specialize (Hrel Hrec_short Hsource x).

        spec Hrel. {
          intros.
          apply get_receives_for_info in H1.
          destruct H1 as [_ [_ H1]].
          destruct H1 as [so [Heqso Heqso']].
          exists (x, so). intuition.
        }

        spec Hrel. {
          intros.
          specialize (Hx_after_long i).
          symmetry.
          assumption.
        }

        simpl in Hrel.
        rewrite eq_short in Hrel.

        assert (Hfinite_short : finite_protocol_plan_from X res_long (get_receives_for s (others x s) x)). {
          intuition.
        }

        split.
        + apply finite_protocol_plan_from_app_iff.
          unfold finite_protocol_plan_from. simpl. rewrite eq_long.
          split.
          * unfold finite_protocol_plan_from in IHprotocol.
            replace tr_long with (fst (apply_plan X s (get_receives_all s lfrom))).
            assumption.
            unfold get_receives_all.
            simpl. rewrite eq_long. reflexivity.
          * rewrite H0 in Hfinite_short. simpl. simpl in Hfinite_short.
            rewrite eq_long in Hfinite_short.
            apply Hfinite_short.
        +
             intros.
             destruct (decide (f = x)).
              -- rewrite H.
                destruct Hrel as [_ Hrel].
                specialize (Hrel i).
                rewrite e.
                simpl. rewrite eq_short.
                rewrite Hrel.
                apply get_receives_for_correct.
                assumption.
                apply NoDup_others.
                apply others_correct.
                unfold others.
                apply set_remove_3.
                intuition.
                subst f. intuition.
              -- apply in_app_iff in H1.
                simpl in H1.
                destruct H1.
                specialize (IHproject f i H1).
                spec IHproject. {
                  intuition.
                }
                spec IHproject. {
                  intuition.
                }
                rewrite <- IHproject.
                unfold get_receives_all.
                replace (snd (apply_plan X s (concat (map (fun i1 : index => get_receives_for s (others i1 s) i1) lfrom)))) with res_long by intuition.
                rewrite H.
                simpl. rewrite eq_long. simpl.
                apply receives_neq.
                assumption.
                assumption.
                assumption.
                intros.
                apply get_receives_for_info in H4.
                destruct H4 as [_ [_ H4]].
                destruct H4 as [so [Heqso Heqso']].
                exists (x, so). intuition.
                intuition.
    Qed.

    Definition receive_phase_plan (s : vstate X) := (get_receives_all s index_listing).
    Definition receive_phase (s : vstate X) := apply_plan X s (receive_phase_plan s).
    Definition receive_phase_result (s : vstate X) := snd (receive_phase s).
    Definition receive_phase_transitions (s : vstate X) := fst (receive_phase s).

    Lemma receive_phase_protocol
      (s : vstate X)
      (Hprs : protocol_state_prop X s):
      finite_protocol_plan_from X s (receive_phase_plan s).
    Proof.
      unfold receive_phase_plan.
      apply get_receives_all_protocol.
      apply (proj1 Hfinite).
      intuition.
    Qed.

    Remark receive_phase_result_protocol
      (s : vstate X)
      (Hprs : protocol_state_prop X s)
      (res_receive := receive_phase_result s) :
      protocol_state_prop X res_receive.
    Proof.
      apply apply_plan_last_protocol.
      intuition.
      apply receive_phase_protocol.
      all : intuition.
    Qed.

    Lemma receive_phase_GE
      (s : vstate X)
      (Hprs : protocol_state_prop X s)
      (res_receive := receive_phase_result s) :
      set_eq (GE res_receive) (GE s).
    Proof.
      specialize (receive_plan_preserves_equivocation s Hprs (receive_phase_plan s)) as Hep.
      spec Hep. apply receive_phase_protocol. intuition.
      spec Hep. {
        intros.
        unfold receive_phase_plan in H.
        apply get_receives_all_info in H.
        split;[intuition|].
        destruct H as [_ H].
        destruct H as [so [from H]].
        exists so. exists from. intuition.
      }
      simpl in Hep.
      apply set_eq_comm.
      intuition.
    Qed.

    Remark receive_phase_future
      (s : vstate X)
      (Hspr : protocol_state_prop _ s) :
      in_futures _ s (receive_phase_result s).
    Proof.
      unfold in_futures.
      exists (receive_phase_transitions s).
      split.
      apply receive_phase_protocol.
      assumption.
      unfold receive_phase_transitions.
      unfold receive_phase_result.
      apply apply_plan_last.
    Qed.

    Remark self_projections_same_after_receive_phase
      (s : vstate X)
      (Hpr : protocol_state_prop X s)
      (res_receive := receive_phase_result s) :
      forall (i : index), project (res_receive i) i = project (s i) i.
    Proof.
      intros.
      specialize (self_projections_same_after_receives s Hpr) as Hsame.
      specialize (Hsame (receive_phase_plan s)).
      spec Hsame. apply receive_phase_protocol. intuition.

      spec Hsame. {
        intros.
        unfold receive_phase_plan in H.
        apply get_receives_all_info in H.
        intuition.
      }
      specialize (Hsame i).
      intuition.
    Qed.

    Definition common_future (s : vstate X) := receive_phase_result (send_phase_result s).

    Lemma common_future_in_futures
      (s : vstate X)
      (Hpr : protocol_state_prop X s)
      (Hnf : no_component_fully_equivocating s (GH s)) :
      in_futures X s (common_future s).
    Proof.
      specialize (@in_futures_trans message X s (send_phase_result s) (common_future s)) as Htrans.
      apply Htrans.
      apply send_phase_future.
      intuition.
      intuition.
      unfold common_future.
      apply receive_phase_future.
      apply send_phase_result_protocol.
      all : intuition.
    Qed.

    Lemma common_future_no_extra_equivocation
      (s : vstate X)
      (Hpr : protocol_state_prop X s)
      (Hnf : no_component_fully_equivocating s (GH s)) :
      set_eq (GE (common_future s)) (GE s).
    Proof.
      apply set_eq_tran with (s2 := GE (send_phase_result s)).
      apply receive_phase_GE.
      apply send_phase_result_protocol.
      intuition. intuition.
      apply send_phase_GE.
      intuition. intuition.
    Qed.

    Remark common_future_result_protocol
      (s : vstate X)
      (Hpr : protocol_state_prop X s)
      (Hnf : no_component_fully_equivocating s (GH s))
      (res := common_future s) :
      protocol_state_prop X res.
    Proof.
      unfold res.
      unfold common_future.
      apply receive_phase_result_protocol.
      apply send_phase_result_protocol.
      all : intuition.
    Qed.

    Corollary GH_eq1
      (s : vstate X)
      (Hpr : protocol_state_prop X s)
      (Hnf : no_component_fully_equivocating s (GH s))
      (res_send := send_phase_result s)
      (res := common_future s) :
      (GH s) = (GH res_send).
    Proof.
      apply HE_eq_equiv.
      specialize (send_phase_GE s Hpr Hnf) as He.
      unfold GE in He.
      apply wE_eq_equality in He.
      intuition.
    Qed.

    Corollary GH_eq2
      (s : vstate X)
      (Hpr : protocol_state_prop X s)
      (Hnf : no_component_fully_equivocating s (GH s))
      (res_send := send_phase_result s)
      (res := common_future s) :
      (GH s) = (GH res).
    Proof.
      apply HE_eq_equiv.
      specialize (common_future_no_extra_equivocation s Hpr Hnf) as He.
      unfold GE in He.
      apply wE_eq_equality in He.
      intuition.
    Qed.

    Corollary GH_eq3
      (s : vstate X)
      (Hpr : protocol_state_prop X s)
      (Hnf : no_component_fully_equivocating s (GH s))
      (res_send := send_phase_result s)
      (res := common_future s) :
      (GH res_send) = (GH res).
    Proof.
      apply HE_eq_equiv.
      specialize (receive_phase_GE res_send) as He.
      spec He. apply send_phase_result_protocol; intuition.
      unfold GE in He.
      apply wE_eq_equality in He.
      intuition.
    Qed.

    Lemma hh_something
      (s : vstate X)
      (Hpr : protocol_state_prop X s)
      (res := receive_phase_result s) :
      incl (HH res) (HH s).
    Proof.
      unfold incl. intros.
      assert (HsameGH : GH res = GH s). {
        unfold res.
        specialize (receive_phase_GE s Hpr) as Hseteq.
        simpl in Hseteq.
        apply filter_set_eq in Hseteq.
        apply HE_eq_equiv.
        intuition.
      }

      assert (~ In a (HE s)). {
        intros contra.
        assert (contra' := contra).
        unfold HE in contra.
        apply GE_direct in contra.
        unfold cequiv_evidence in contra.
        unfold equivocation_evidence in contra.
        setoid_rewrite hbo_cobs' in contra.

        destruct contra as [e1 [He1 [He1' [e2 [He2 [He2' Hcomp]]]]]].
        specialize (@in_future_message_obs _ _ _ _ _ _ _ (GH s) s res Hpr a) as Hfuture.
        spec Hfuture. {
          unfold res.
          apply receive_phase_future.
          intuition.
        }

        assert (In a (HE res)). {
          unfold HE.
          apply GE_direct.
          unfold cequiv_evidence.
          unfold equivocation_evidence.
          setoid_rewrite hbo_cobs'.
          unfold get_simp_event_subject_some in He1'.
          inversion He1'.
          exists e1.
          split.
          - setoid_rewrite cobs_messages_states in He1.
            apply set_union_iff in He1.
            destruct He1 as [He1|He1].
            + apply cobs_single_s in He1.
              destruct He1 as [k [Hk Hk']].
              unfold simp_lv_state_observations in Hk'.
              rewrite H1 in Hk'.
              rewrite decide_False in Hk'.
              intuition.
              specialize (ws_incl_wE s index_listing (GH s)) as Hincl.
              spec Hincl. unfold incl. intros. apply in_listing.
              destruct (decide (a = k)).
              * subst k. unfold GH in Hk. apply wH_wE' in Hk. intuition.
              * intuition.
            + setoid_rewrite cobs_messages_states.
              apply set_union_iff.
              right.
              specialize (Hfuture e1).
              inversion He1'. rewrite H1.
              rewrite H1 in He1.
              specialize (Hfuture He1).
              unfold wcobs_messages.
              rewrite HsameGH.
              intuition.
          - split;[intuition|].
            exists e2.
            split.
            unfold get_simp_event_subject_some in He2'.
            inversion He2'.
            + setoid_rewrite cobs_messages_states in He2.
            apply set_union_iff in He2.
            destruct He2 as [He2|He2].
            * apply cobs_single_s in He2.
              destruct He2 as [k [Hk Hk']].
              unfold simp_lv_state_observations in Hk'.
              rewrite H2 in Hk'.
              rewrite decide_False in Hk'.
              intuition.
              specialize (ws_incl_wE s index_listing (GH s)) as Hincl.
              spec Hincl. unfold incl. intros. apply in_listing.
              destruct (decide (a = k)).
              -- subst k. unfold GH in Hk. apply wH_wE' in Hk. intuition.
              -- intuition.
            * setoid_rewrite cobs_messages_states.
              apply set_union_iff.
              right.
              specialize (Hfuture e2).
              rewrite H2.
              rewrite H2 in He2.
              specialize (Hfuture He2).
              unfold wcobs_messages.
              rewrite HsameGH.
              intuition.
            + split.
              -- unfold get_simp_event_subject_some.
                 f_equal.
                 inversion He2'.
                 rewrite H2, H1. intuition.
              -- intuition.
        }
        unfold HH in H.
        apply wH_wE' in H.
        intuition.
      }
      unfold HH.
      apply wH_wE'.
      intuition.
    Qed.

  Lemma honest_receive_honest
    (s : vstate X)
    (Hpr : protocol_state_prop X s)
    (Hnf : no_component_fully_equivocating s (GH s))
    (res_send := send_phase_result s)
    (res := common_future s) :
    forall (i j : index), In i (GH res) -> In j (GH res) -> project (res i) j = project (res j) j.
  Proof.
    intros.
    destruct (decide (i = j));[subst i;intuition|].

    assert (Hsend_pr : protocol_state_prop X res_send). {
      apply send_phase_result_protocol.
      all : intuition.
    }

    assert (In i (GH s) /\ In j (GH s)) by (setoid_rewrite GH_eq2;intuition).
    assert (HiGH : In i (GH (send_phase_result s))) by (setoid_rewrite <- GH_eq1;intuition).

    specialize (get_receives_all_protocol (send_phase_result s) index_listing (proj1 Hfinite) Hsend_pr) as Hrec.
    simpl in Hrec. destruct Hrec as [Hrec_pr Hrec].
    specialize (Hrec j i).
    spec Hrec. apply in_listing.
    specialize (Hrec n).
    unfold res in H.

    specialize (Hrec HiGH).
    unfold res at 1.
    unfold common_future.
    unfold receive_phase_result.
    unfold receive_phase.
    unfold receive_phase_plan.
    simpl. rewrite Hrec.
    rewrite get_matching_state_for_honest.
    rewrite <- self_projections_same_after_receive_phase.
    intuition.
    1, 2 : intuition.
    setoid_rewrite <- GH_eq1; intuition.
  Qed.

  Lemma all_projections_old1
    (s : vstate X)
    (Hpr : protocol_state_prop X s)
    (Hnf : no_component_fully_equivocating s (GH s))
    (res_send := send_phase_result s)
    (res := common_future s)
    (i j : index)
    (Hdif : i <> j)
    (Hi : In i (GH res)) :
    (project (res i) j = (s j) /\ (In j (GH res))) \/
    (exists (inter : index), In inter (GH res) /\
    project (s inter) j = project (res i) j).
  Proof.
    assert (Hspr: protocol_state_prop X res_send) by (apply send_phase_result_protocol;intuition).
    assert (In i (GH res_send)). {
      unfold res_send.
      rewrite GH_eq3; intuition.
    }

    assert (project (res i) j = project (get_matching_state (res_send) i j) j). {
      unfold res.
      unfold common_future.
      specialize (get_receives_all_protocol res_send index_listing (proj1 Hfinite) Hspr) as Hrec.
      destruct Hrec as [_ Hrec].
      specialize (Hrec j i (in_listing j)).
      spec Hrec. intuition.
      specialize (Hrec H).
      apply Hrec.
    }
    specialize (get_matching_state_correct2 res_send i j H) as Hinter.
    destruct Hinter as [inter [HinterGH Hmatch]].

    destruct (decide (inter = j)).
    - subst inter.
      left.
      rewrite Hmatch in H0.
      unfold res_send in H0.
      rewrite send_phase_result_projections in H0.
      2 , 3 : intuition.
      2 : {
        rewrite GH_eq1; intuition.
      }
      split.
      + intuition.
      + unfold res. rewrite <- GH_eq3; intuition.
    - right.
      exists inter.
      split.
      + unfold res. rewrite <- GH_eq3; intuition.
      + assert (project (s inter) j = project (res_send inter) j). {
          specialize (non_self_projections_same_after_send_phase s Hpr Hnf inter j n).
          intuition.
        }
        rewrite Hmatch in H0.
        rewrite H0.
        intuition.
  Qed.

  Lemma all_projections_old2
    (s : vstate X)
    (Hpr : protocol_state_prop X s)
    (Hnf : no_component_fully_equivocating s (GH s))
    (res_send := send_phase_result s)
    (res := common_future s)
    (i j : index)
    (Hi : In i (GH res))
    (Hk : ~ In j (GH res)) :
    exists (inter : index), In inter (GH res) /\
    project (s inter) j = project (res i) j.
  Proof.

    assert (Hdif : i <> j). {
      destruct (decide (i = j));[subst i;intuition|intuition].
    }

    assert (Hspr: protocol_state_prop X res_send) by (apply send_phase_result_protocol;intuition).
    assert (In i (GH res_send)). {
      unfold res_send.
      rewrite GH_eq3; intuition.
    }

    assert (project (res i) j = project (get_matching_state (res_send) i j) j). {
      unfold res.
      unfold common_future.
      specialize (get_receives_all_protocol res_send index_listing (proj1 Hfinite) Hspr) as Hrec.
      destruct Hrec as [_ Hrec].
      specialize (Hrec j i (in_listing j)).
      spec Hrec. intuition.
      specialize (Hrec H).
      apply Hrec.
    }
    specialize (get_matching_state_correct2 res_send i j H) as Hinter.
    destruct Hinter as [inter [HinterGH Hmatch]].

    assert (inter <> j). {
      destruct (decide (inter = j)).
      - subst inter.
        unfold res_send in HinterGH.
        rewrite GH_eq3 in HinterGH; intuition.
      - intuition.
    }

    exists inter.
    split.
    + unfold res. rewrite <- GH_eq3; intuition.
    + assert (project (s inter) j = project (res_send inter) j). {
        specialize (non_self_projections_same_after_send_phase s Hpr Hnf inter j H1).
        intuition.
      }
      rewrite Hmatch in H0.
      rewrite H0.
      intuition.
  Qed.

  Lemma all_message_observations_old
    (s : vstate X)
    (Hpr : protocol_state_prop X s)
    (Hnf : no_component_fully_equivocating s (GH s))
    (res_send := send_phase_result s)
    (res := common_future s)
    (target : index)
    (Htarget : ~In target (GH res))
    (e : simp_lv_event) :
    In e (hcobs_messages res target) ->
    In e (hcobs_messages s target).
  Proof.
    intros.
    assert (H' := H).
    apply (@cobs_single_m _ _ index_listing Hfinite _ _ _ _) in H.
    destruct H as [k [Hink Hine]].

    assert (Hspr : protocol_state_prop X res_send). {
      apply send_phase_result_protocol; intuition.
    }

    assert (In k (GH res_send)). {
      unfold res_send.
      rewrite GH_eq3; intuition.
    }

    assert (Hdif : target <> k). {
      destruct (decide (k = target)).
      - subst k. intuition.
      - intuition.
    }

    apply (@unfold_simp_lv_observations index index_listing Hfinite) in Hine.
    2 : {
      apply protocol_state_component_no_bottom.
      apply common_future_result_protocol; intuition.
    }
    apply cobs_single_m.

    destruct Hine as [Hine|Hine].
    - specialize (all_projections_old2 s Hpr Hnf k target Hink Htarget) as Hinter.
      destruct Hinter as [inter [HinterGH Hproject]].
      exists inter.
      split.
      + rewrite GH_eq2; intuition.
      + unfold res in Hine.
        rewrite <- Hproject in Hine.
        apply refold_simp_lv_observations1.
        apply protocol_state_component_no_bottom; intuition.
        apply (@cobs_single_m _ _ index_listing Hfinite _ _ _ _) in H'.
        destruct H' as [inter2 Hrest].
        destruct Hrest as [_ Hrest].
        apply (@in_message_observations_nb index index_listing Hfinite) in Hrest.
        rewrite Hine in Hrest. simpl in Hrest.
        intuition.
        intuition.
    - destruct Hine as [l Hinel].
      destruct (decide (k = l)).
      + subst l.
        unfold res in Hinel.
        unfold common_future in Hinel.
        rewrite self_projections_same_after_receive_phase in Hinel by intuition.
        rewrite send_phase_result_projections in Hinel.
        2, 3 : intuition.
        2 : (rewrite GH_eq2; intuition).
        exists k.
        split.
        * rewrite GH_eq1; intuition.
        * intuition.
      + specialize (all_projections_old1 s Hpr Hnf k l n Hink) as Hinter.
        destruct Hinter.
        * unfold res in Hinel.
          destruct H0 as [H0 HlGH].
          rewrite H0 in Hinel.
          exists l.
          rewrite GH_eq2; intuition.
        * destruct H0 as [inter2 [Hinter2GH Hproj]].
          unfold res in Hinel.
          rewrite <- Hproj in Hinel.
          exists inter2.
          split.
          -- rewrite GH_eq2; intuition.
          -- apply (@refold_simp_lv_observations2 index index_listing Hfinite).
             apply protocol_state_component_no_bottom.
             intuition.
             exists l. intuition.
  Qed.

  Lemma all_message_observations_in_new_projections
    (s : vstate X)
    (Hpr : protocol_state_prop X s)
    (Hnf : no_component_fully_equivocating s (GH s))
    (res_send := send_phase_result s)
    (res := common_future s)
    (i target : index)
    (Hi : In i (GH res))
    (Htarget : ~In target (GH res))
    (e : simp_lv_event) :
    In e (hcobs_messages s target) ->
    In e (simp_lv_message_observations (res i) target).
  Proof.
    intros.
    apply (@cobs_single_m _ _ index_listing Hfinite _ _ _ _) in H.
    destruct H as [j [HjGH Hine]].
    apply (@refold_simp_lv_observations2 index index_listing Hfinite).
    apply protocol_state_component_no_bottom; apply common_future_result_protocol; intuition.
    exists j.
    specialize (honest_receive_honest s Hpr Hnf i j Hi) as Hhonest.
    spec Hhonest. rewrite <- GH_eq2; intuition.
    unfold res. rewrite Hhonest.
    unfold common_future.
    rewrite self_projections_same_after_receive_phase by (apply send_phase_result_protocol;intuition).
    rewrite send_phase_result_projections; intuition.
  Qed.

  Lemma local_and_honest
    (s : vstate X)
    (Hpr : protocol_state_prop X s)
    (Hnf : no_component_fully_equivocating s (GH s))
    (res_send := send_phase_result s)
    (res := common_future s)
    (i : index)
    (Hi : In i (GH res)) :
    set_eq (HE res) (LE i res).
  Proof.
    apply set_eq_extract_forall.
    intros v.
    split; intros.
    - assert (Hdif : ~ In v (GH res)). {
        intros contra.
        specialize (ws_incl_wE res index_listing (GH res)) as Hincl.
        spec Hincl. unfold incl. intros. apply in_listing.
        specialize (Hincl v).
        unfold HE in H.
        specialize (Hincl H).
        unfold GH in contra.
        apply wH_wE' in contra.
        intuition.
      }
      unfold HE in H.
      unfold LE.
      apply GE_direct in H.
      unfold cequiv_evidence in H.
      unfold equivocation_evidence in H.
      setoid_rewrite hbo_cobs' in H.

      destruct H as [e1 [He1 [He1' [e2 [He2 [He2']]]]]].
      setoid_rewrite cobs_messages_states in He1.
      setoid_rewrite cobs_messages_states in He2.

      apply set_union_iff in He1.
      apply set_union_iff in He2.

      destruct He1 as [He1|He1].
      + unfold wcobs_states in He1.
        apply set_union_in_iterated in He1.
        rewrite Exists_exists in He1.
        destruct He1 as [le [Heq_le Hin_e1]].
        apply in_map_iff in Heq_le.
        destruct Heq_le as [j [Heqj Hinj]].
        unfold simp_lv_state_observations in Heqj.
        inversion He1'.
        rewrite H1 in Heqj.
        destruct (decide (v = j));[subst v;intuition|].
        subst le. intuition.
     + destruct He2 as [He2|He2].
       * unfold wcobs_states in He2.
         apply set_union_in_iterated in He2.
         rewrite Exists_exists in He2.
         destruct He2 as [le [Heq_le Hin_e2]].
         apply in_map_iff in Heq_le.
         destruct Heq_le as [j [Heqj Hinj]].
         unfold simp_lv_state_observations in Heqj.
         inversion He2'.
         rewrite H1 in Heqj.
         destruct (decide (v = j));[subst v;intuition|].
         subst le. intuition.
       * apply GE_direct.
         unfold cequiv_evidence.
         unfold equivocation_evidence.
         setoid_rewrite hbo_cobs'.
         inversion He1'.
         inversion He2'.
         exists e1.
         split.
         -- apply all_message_observations_old in He1.
            apply all_message_observations_in_new_projections with (i := i) in He1.
            unfold wcobs. unfold composite_state_events_fn. simpl. unfold Hstate_events_fn.
            unfold res. apply in_simp_lv_message_observations'. intuition.
            intuition. intuition. intuition. rewrite H1.
            intuition. intuition. intuition. rewrite H1. intuition.
         -- split;[intuition|].
            exists e2.
            split.
            ++ apply all_message_observations_old in He2.
               apply all_message_observations_in_new_projections with (i := i) in He2.
               unfold wcobs. unfold composite_state_events_fn. simpl. unfold Hstate_events_fn.
               unfold res. apply in_simp_lv_message_observations'. intuition.
               intuition. intuition. intuition. rewrite H2.
               intuition. intuition. intuition. rewrite H2. intuition.
            ++ rewrite He2'. rewrite H1. intuition.
    - specialize (ws_incl_wE res (GH res) [i]) as Hincl.
      spec Hincl. {
        unfold incl. intros.
        destruct H0;[|intuition]. subst a. intuition.
      }
      specialize (Hincl v).
      specialize (Hincl H).
      intuition.
  Qed.

  Corollary local_and_honest_equal
    (s : vstate X)
    (Hpr : protocol_state_prop X s)
    (Hnf : no_component_fully_equivocating s (GH s))
    (res_send := send_phase_result s)
    (res := common_future s)
    (i : index)
    (Hi : In i (GH res)) :
    (HE res) = (LE i res).
  Proof.
    apply filter_set_eq.
    specialize (local_and_honest s Hpr Hnf i Hi).
    intuition.
  Qed.

  Lemma honest_hh_projections_comparable
    (s : vstate X)
    (Hpr : protocol_state_prop X s)
    (h1 h2 hh : index)
    (Hgh : In h1 (GH s) /\ In h2 (GH s))
    (Hhh : In hh (HH s)) :
    comparable (state_lt_ext hh) (project (s h1) hh) (project (s h2) hh).
  Proof.
    unfold comparable.
    destruct (decide (project (s h1) hh = project (s h2) hh));[left;intuition|].
    right.

    destruct (project (s h1) hh) eqn : eq1.
    - left. unfold state_lt_ext. intuition.
    - destruct (project (s h2) hh) eqn : eq2.
      + right. unfold state_lt_ext. intuition.
      + rewrite <- eq1. rewrite <- eq2.

        assert (Hcomp : comparable (state_lt' hh) (project (s h1) hh) (project (s h2) hh)). {
          destruct (decide (comparable (state_lt' hh) (project (s h1) hh) (project (s h2) hh)));[intuition|].
          assert (In hh (HE s)). {
            unfold HE.
            apply GE_direct.
            unfold cequiv_evidence.
            unfold equivocation_evidence.
            setoid_rewrite hbo_cobs'.

            exists (SimpObs Message' hh (project (s h1) hh)).
            simpl. split.
            - apply in_cobs_messages'.
              apply cobs_single_m.
              exists h1. split;[intuition|].
              apply refold_simp_lv_observations1.
              apply protocol_state_component_no_bottom; intuition.
              intuition congruence. intuition.
            - split;[simpl;intuition|].
              exists (SimpObs Message' hh (project (s h2) hh)).
              simpl. split.
              + apply in_cobs_messages'.
                apply cobs_single_m.
                exists h2. split;[intuition|].
                apply refold_simp_lv_observations1.
                apply protocol_state_component_no_bottom; intuition.
                intuition congruence. intuition.
              + split;[simpl;intuition|].
                intros contra.
                unfold comparable in contra.
                unfold simp_lv_event_lt in contra.
                rewrite decide_True in contra by intuition.
                rewrite decide_True in contra by intuition.
                destruct contra.
                * inversion H. intuition congruence.
                * unfold comparable in n0.
                  contradict n0.
                  right. intuition.
          }
          unfold HH in Hhh.
          apply wH_wE' in Hhh.
          unfold HE in H. intuition.
        }

        unfold comparable in Hcomp.
        destruct Hcomp;[intuition congruence|].
        destruct H.
        * left. unfold state_lt_ext. intuition.
        * right. unfold state_lt_ext. intuition.
  Qed.

  Lemma comparable_projections_match
    (s : vstate X)
    (Hpr : protocol_state_prop X s)
    (h1 h2 hh : index)
    (Hgh : In h1 (GH s) /\ In h2 (GH s))
    (Hhh : In hh (HH s))
    (projh1 := project (get_matching_state s h1 hh) hh)
    (projh2 := project (get_matching_state s h2 hh) hh) :
    projh1 = projh2.
  Proof.
    specialize (get_matching_state_correct2 s h1 hh) as Hmatch1.
    specialize (get_matching_state_correct2 s h2 hh) as Hmatch2.
    spec Hmatch1. intuition. spec Hmatch2. intuition.
    destruct Hmatch1 as [i [GHi Hmatch1]].
    destruct Hmatch2 as [j [GHj Hmatch2]].

    assert (Hcomp': comparable (state_lt_ext hh) projh1 projh2). {
      unfold projh1, projh2.
      rewrite Hmatch1. rewrite Hmatch2.
      apply honest_hh_projections_comparable; intuition.
    }

    unfold projh1 in *.
    unfold projh2 in *.
    specialize (get_matching_state_correct3 s h1 hh) as Htop1.
    specialize (get_matching_state_correct3 s h2 hh) as Htop2.
    spec Htop1. intuition. spec Htop2. intuition.

    unfold comparable in Hcomp'.
    destruct Hcomp' as [|Hcomp'];[intuition|].
    destruct Hcomp'.
    - unfold get_topmost_candidates in Htop1.
      unfold get_maximal_elements in Htop1.
      apply filter_In in Htop1.
      destruct Htop1 as [_ Htop1].
      rewrite forallb_forall in Htop1.
      specialize (Htop1 (s j)).
      spec Htop1.
      apply in_map_iff. exists j. intuition.
      rewrite negb_true_iff in Htop1.
      rewrite bool_decide_eq_false in Htop1.
      rewrite Hmatch2 in H.
      intuition.
      intros. apply honest_hh_projections_comparable; intuition.
    - unfold get_topmost_candidates in Htop2.
      unfold get_maximal_elements in Htop2.
      apply filter_In in Htop2.
      destruct Htop2 as [_ Htop2].
      rewrite forallb_forall in Htop2.
      specialize (Htop2 (s i)).
      spec Htop2.
      apply in_map_iff. exists i. intuition.
      rewrite negb_true_iff in Htop2.
      rewrite bool_decide_eq_false in Htop2.
      rewrite Hmatch1 in H.
      intuition.
      intros. apply honest_hh_projections_comparable; intuition.
   Qed.

  Lemma honest_equiv_proj_same
    (s : vstate X)
    (Hpr : protocol_state_prop X s)
    (Hnf : no_component_fully_equivocating s (GH s))
    (res_send := send_phase_result s)
    (res := common_future s) :
    forall (h1 h2 hh : index),
    In h1 (GH res) ->
    In h2 (GH res) ->
    In hh (HH res) ->
    project (res h1) hh = project (res h2) hh.
  Proof.
    intros.

    destruct (decide (h1 = hh)).
    subst hh.
    specialize (honest_receive_honest s Hpr Hnf h2 h1).
    intuition.
    destruct (decide (h2 = hh)).
    subst hh.
    specialize (honest_receive_honest s Hpr Hnf h1 h2).
    intuition.

    destruct (decide (project (res h1) hh = project (res h2) hh));[intuition|].
    exfalso.

    specialize (get_receives_all_protocol res_send index_listing (proj1 Hfinite)) as Hmatch.
    spec Hmatch. apply send_phase_result_protocol. intuition. intuition.
    destruct Hmatch as [_ Hmatch].

    specialize (Hmatch hh h1) as Hmatch1.
    spec Hmatch1. apply in_listing. spec Hmatch1. intuition.
    spec Hmatch1. unfold res_send. rewrite GH_eq3 by intuition. intuition.
    specialize (Hmatch hh h2) as Hmatch2.
    spec Hmatch2. apply in_listing. spec Hmatch2. intuition.
    spec Hmatch2. unfold res_send. rewrite GH_eq3 by intuition. intuition.

    unfold res in n1. unfold common_future in n1. unfold receive_phase_result in n1.
    unfold res_send in Hmatch1, Hmatch2.
    unfold receive_phase in n1.
    unfold receive_phase_plan in n1.
    rewrite Hmatch1 in n1.
    rewrite Hmatch2 in n1.

    specialize (comparable_projections_match res_send) as Hcomp.
    spec Hcomp. apply send_phase_result_protocol; intuition.
    specialize (Hcomp h1 h2 hh).
    spec Hcomp. {
      unfold res_send.
      rewrite GH_eq3 by intuition.
      unfold res in H, H0. intuition.
    }
    spec Hcomp. {
      apply hh_something.
      apply send_phase_result_protocol; intuition.
      intuition.
    }
    intuition.
  Qed.

  Lemma eqv_aware_something
    (s : vstate X)
    (Hpr : protocol_state_prop X s)
    (i : index) :
    LE i s = (@equivocating_validators _ _ _ _ (Hbasic i) (s i)).
  Proof.
    unfold equivocating_validators.
    unfold LE. unfold wE.
    unfold state_validators. simpl. unfold get_validators.
    apply filter_ext_in. intros.

    unfold equivocation_evidence.
    rewrite bool_decide_decide.
    rewrite bool_decide_decide.
    apply decide_iff.
    split; intros.
    - destruct H0 as [e1 [He1 [He1' [e2 [He2 [He2' Hcomp]]]]]].
      exists e1.
      split.
      + unfold has_been_observed. simpl.
        unfold observable_events_has_been_observed.
        unfold state_observable_events_fn.
        setoid_rewrite hbo_cobs' in He1.
        apply cobs_single in He1.
        destruct He1 as [j [Heqj]].
        destruct Heqj;[|intuition]. subst j.
        apply set_union_in_iterated.
        rewrite Exists_exists.
        exists ((@simp_lv_observations index i index_listing _) (s i) (get_simp_event_subject e1)).
        split.
        * apply in_map_iff. exists (get_simp_event_subject e1). split;[intuition|apply in_listing].
        * intuition.
      + split;[intuition|].
        exists e2.
        split.
        * unfold has_been_observed. simpl.
        unfold observable_events_has_been_observed.
        unfold state_observable_events_fn.
        setoid_rewrite hbo_cobs' in He2.
        apply cobs_single in He2.
        destruct He2 as [j [Heqj]].
        destruct Heqj;[|intuition]. subst j.
        apply set_union_in_iterated.
        rewrite Exists_exists.
        exists ((@simp_lv_observations index i index_listing _) (s i) (get_simp_event_subject e2)).
        split.
        -- apply in_map_iff. exists (get_simp_event_subject e2). split;[intuition|apply in_listing].
        -- intuition.
        * split;intuition.
    - destruct H0 as [e1 [He1 [He1' [e2 [He2 [He2' Hcomp]]]]]].
      exists e1.
      setoid_rewrite hbo_cobs'.
      split.
      + unfold has_been_observed in He1.
        simpl in He1.
        unfold observable_events_has_been_observed in He1.
        unfold state_observable_events_fn in He1.
        apply set_union_in_iterated in He1.
        rewrite Exists_exists in He1.
        destruct He1 as [le [Hle Hine1]].
        apply in_map_iff in Hle.
        destruct Hle as [j [Hsimp Hinj]].
        rewrite <- Hsimp in Hine1.
        apply in_simp_lv_observations in Hine1 as Hine1'.
        subst j.
        apply cobs_single. exists i. intuition.
      + split;[intuition|].
        exists e2.
        split.
        * unfold has_been_observed in He2.
          simpl in He2.
          unfold observable_events_has_been_observed in He2.
          unfold state_observable_events_fn in He2.
          apply set_union_in_iterated in He2.
          rewrite Exists_exists in He2.
          destruct He2 as [le [Hle Hine2]].
          apply in_map_iff in Hle.
          destruct Hle as [j [Hsimp Hinj]].
          rewrite <- Hsimp in Hine2.
          apply in_simp_lv_observations in Hine2 as Hine2'.
          subst j.
          apply cobs_single. exists i. intuition.
        * split;intuition.
    Qed.

  Lemma eqv_aware_something2
    (s : vstate X)
    (Hpr : protocol_state_prop X s)
    (Hnf : no_component_fully_equivocating s (GH s))
    (res_send := send_phase_result s)
    (res := common_future s)
    (i j : index)
    (Hin : In i (GH res) /\ In j (GH res)) :
    no_equivocating_decisions (res i) (HE res) =
    no_equivocating_decisions (res j) (HE res).
  Proof.
    unfold no_equivocating_decisions.
    assert (res i <> Bottom /\ res j <> Bottom). {
      split;apply protocol_state_component_no_bottom;
      apply common_future_result_protocol; intuition.
     }
     destruct (res i) eqn : eq_resi;[intuition congruence|].
     destruct (res j) eqn : eq_resj;[intuition congruence|].
     rewrite <- eq_resi. rewrite <- eq_resj.
     f_equal.
     unfold get_no_equivocating_states.
     apply map_ext_in.
     intros.
     - specialize (@wH_wE _ _ _ _ _ _ _ (GH res) res) as Hdiff.
       unfold HE in H0.
       destruct Hdiff as [_ Hdiff].
       specialize (Hdiff a H0).
       apply honest_equiv_proj_same.
       all : intuition.
  Qed.

  Lemma honest_nodes_same_estimators
    (s : vstate X)
    (Hpr : protocol_state_prop X s)
    (Hnf : no_component_fully_equivocating s (GH s))
    (res_send := send_phase_result s)
    (res := common_future s) :
    forall (i j : index) (b : bool),
    In i (GH res) ->
    In j (GH res) ->
    (est' i (res i) b) <-> (est' j (res j) b).
  Proof.
    intros.
    unfold est'.
    unfold equivocation_aware_estimator.
    assert (res i <> Bottom /\ res j <> Bottom). {
      split; apply protocol_state_component_no_bottom; apply common_future_result_protocol; intuition.
    }
    destruct (res i) eqn : resi;[intuition congruence|].
    destruct (res j) eqn : resj;[intuition congruence|].

    rewrite <- resi. rewrite <- resj.

    specialize (local_and_honest s Hpr Hnf) as Hlocal. simpl in Hlocal.
    specialize (Hlocal i H) as Hlocali.
    specialize (Hlocal j H0) as Hlocalj.
    unfold res.

    replace (equivocating_validators (common_future s i)) with (LE i res).
    replace (equivocating_validators (common_future s j)) with (LE j res).
    2, 3 : (apply eqv_aware_something; apply common_future_result_protocol; intuition).

    unfold res.
    rewrite <- local_and_honest_equal by intuition.
    rewrite <- local_and_honest_equal by intuition.

    unfold res in resi. unfold res in resj.
    rewrite resi. rewrite resj. rewrite <- resi. rewrite <- resj.
    rewrite eqv_aware_something2 with (j := j) by intuition.
    intuition.
  Qed.

  Lemma ncfe
    (s : vstate X)
    (Hpr : protocol_state_prop X s) :
    no_component_fully_equivocating s (GH s).
  Proof.
    unfold no_component_fully_equivocating.
    intros.
    unfold not_all_equivocating.
    unfold no_equivocating_decisions.
    destruct (s i) eqn : eq_si.
    - apply protocol_state_component_no_bottom in eq_si; intuition.
    - destruct (map decision
      (get_no_equivocating_states (Something b is) (equivocating_validators (Something b is)))) eqn : eq_m.
      + apply map_eq_nil in eq_m.
        unfold get_no_equivocating_states in eq_m.
        apply map_eq_nil in eq_m.
        rewrite <- eq_si in eq_m.
        rewrite <- eqv_aware_something in eq_m.
        2 : intuition.
        assert (forall (j : index), In j (LE i s)). {
          intros.
          apply wE_wH'.
          intros contra.
          setoid_rewrite wH_wE in contra.
          unfold LE in eq_m.
          rewrite eq_m in contra.
          intuition.
        }
        specialize (ws_incl_wE s index_listing [i]) as Hincl.
        spec Hincl. {
          unfold incl. intros.
          apply in_listing.
        }
        unfold LE in H0.
        assert (forall (j : index), In j (GE s)). {
          unfold GE. intros.
          specialize (H0 j).
          specialize (Hincl j H0).
          intuition.
        }
        specialize (H1 i).
        unfold GH in H.
        apply wH_wE' in H.
        intuition.
      + congruence.
  Qed.

  Theorem common_futures
    (s : vstate X)
    (Hpr : protocol_state_prop X s) :
    exists (s' : vstate X),
    in_futures X s s' /\
    GH s = GH s' /\
    (forall (i j : index) (b : bool),
     In i (GH s') ->
     In j (GH s') ->
     (est' i (s' i) b) <-> (est' j (s' j) b)).
  Proof.
    specialize (ncfe s Hpr) as Hncfe.
    exists (common_future s).
    split.
    - apply common_future_in_futures; intuition.
    - split.
      + apply GH_eq2; intuition.
      + apply honest_nodes_same_estimators; intuition.
  Qed.

End CommonFutures.
