Require Import Bool List ListSet Reals FinFun Program RelationClasses Relations Relations_1 Sorting Basics ZArith.
Require Import Lia.
Require Import ZArith.BinInt.
Require Import ZArith.Zpow_facts.
Import ListNotations.

From CasperCBC
  Require Import
    Lib.Preamble Lib.ListExtras Lib.ListSetExtras Lib.RealsExtras Lib.TopSort Lib.StdppFinSetExtras
    CBC.Protocol CBC.Common CBC.Definitions
    VLSM.Common VLSM.Composition VLSM.Decisions VLSM.Equivocation VLSM.ProjectionTraces.

From stdpp Require Import base fin_sets tactics.

Section FullNodeLike.

Context
  {CV : consensus_values}
  {CV_eq_dec : Classes.EqDecision C}
  {Cm Ci : Type}
  {message : Type}
  {index : Type}
  (vote : message -> option C)
  `{HfinSetMessage : FinSet message Cm}
  `{HfinSetIndex : FinSet index Ci}
  {mdec : Classes.EqDecision message}
  (happens_before : message -> message -> Prop)
  (happens_before' := clos_trans _ happens_before)
  (Hstrict : StrictOrder happens_before')
  (happens_before_dec : RelDecision happens_before)
  (happens_before'_dec : RelDecision happens_before')
  (predSet : message -> Cm)
  (HpredSetCorrect : forall (m1 m2 : message), happens_before m1 m2 <->  m1 ∈ (predSet m2))
  (downSet : message -> Cm)
  (downSet' := fun (m : message) => (downSet m) ∪ {[ m ]})
  (HdownSetCorrect : forall (m1 m2 : message), happens_before' m1 m2 <-> m1 ∈ (downSet m2))
  {index_listing : list index}
  {Hfinite : Listing index_listing}
  {idec : Classes.EqDecision index}
  {i0 : Classes.Inhabited index}
  (sender : message -> index)
  {IM : index -> VLSM message}
  (computable_sent : forall (i : index), computable_sent_messages (IM i))
  (computable_received : forall (i : index), computable_received_messages (IM i)). 
  
  Local Ltac split_prune_and := split_and?;(try solve[intuition]).
  Local Ltac feed_specialize_prune H := feed specialize H; (try solve[intuition]).
  
  Lemma hb_subseteq 
    (m1 m2 : message)
    (Hhb : happens_before' m1 m2) :
    downSet m1 ⊆ downSet m2.
  Proof.
    intros m'.
    rewrite <- !HdownSetCorrect.
    intros Hm1.
    apply t_trans with (y := m1); intuition. 
  Qed.
  
  Lemma something_pretentious : 
    StrictOrder (preceeds_P happens_before' (fun _ : message => True)).
  Proof.
    unfold preceeds_P.
    simpl.
    split.
    - unfold Irreflexive. unfold RelationClasses.Reflexive. intros.
      unfold complement. apply StrictOrder_Irreflexive.
    - unfold RelationClasses.Transitive. intros.
      apply (RelationClasses.StrictOrder_Transitive (` x) (` y) (` z)); intuition.
  Qed.
  
  Definition is_minimal_wrt_P
    (m : message)
    (P : message -> Prop) :=
    P m /\ (forall m', P m' -> ~happens_before' m' m).
  
  Lemma minimal_element_P
    (P : message -> Prop)
    (Pdec : forall m, Decision (P m))
    (m : message)
    (Hm : P m) :
    ∃ m_min : message, is_minimal_wrt_P m_min P.
  Proof.
    unfold is_minimal_wrt_P.
    remember (downSet m) as d.
    remember (filter (fun m => bool_decide (P m)) (elements d)) as dP.
    destruct dP eqn : eq_dP.
    - exists m.
      split;[intuition|].
      intros.
      intros contra.
      specialize (HdownSetCorrect m' m) as Hdown.
      apply Hdown in contra.
      assert (Hm' : m' ∈ (set_filter (fun m => bool_decide (P m)) _ d)). {
        apply elem_of_filter.
        rewrite Heqd. 
        split;[intuition|].
        intuition.
      }
      unfold set_filter in Hm'.
      rewrite <- HeqdP in Hm'.
      simpl in Hm'. 
      apply elem_of_empty in Hm'. intuition. 
    - remember (@min_predecessors _ happens_before' happens_before'_dec (m0 :: dP) dP m0) as m_min.
      assert (Hmin_inf : In m_min (m0 :: dP)). {
        specialize (@min_predecessors_in _ happens_before' happens_before'_dec (m0 :: dP) dP m0) as Hin'.
        destruct Hin' as [Hin'|Hin'].
        + rewrite Heqm_min. rewrite Hin'. simpl. intuition.
        + rewrite Heqm_min. simpl. intuition.
      }
      
      assert (Hmin : m_min ∈ d /\ P m_min). {
        rewrite eq_dP in Hmin_inf.
        rewrite HeqdP in Hmin_inf.
        destruct Hmin_inf as [Hmin_f|Hmin_f].
        + rewrite Hmin_f in HeqdP.
          assert (Hmin : m_min ∈ set_filter (λ m1 : message, bool_decide (P m1)) _ d). {
            unfold set_filter.
            rewrite <- HeqdP.
            apply elem_of_list_to_set.
            apply elem_of_list_In. simpl. intuition.
          }
          apply elem_of_filter in Hmin.
          set_solver.
        + assert (Hmin : m_min ∈ set_filter (λ m1 : message, bool_decide (P m1)) _ d). {
            unfold set_filter.
            apply elem_of_list_to_set.
            rewrite elem_of_list_In.
            intuition.
          }
          apply elem_of_filter in Hmin.
          set_solver.
      }
      destruct Hmin as [Hmind HminP].
      exists m_min.
      split.
      + intuition.
      + intros.
        specialize (@min_predecessors_zero _ happens_before' happens_before'_dec (m0 :: dP) (fun m => True)) as Hzero.
        spec Hzero. {
          rewrite Forall_forall.
          intros. intuition.
        }
        
        spec Hzero. apply something_pretentious.
        
        specialize (Hzero dP m0 eq_refl).
        
        (*destruct (@bool_decide (In m' (elements d)) (in_dec decide_eq m' (elements d))) eqn : eq. *)
        destruct (@decide (m' ∈ d) (elem_of_dec_slow m' d)).
        * assert (Hm' : m' ∈ (set_filter (fun m1 : message => bool_decide (P m1)) _ d)). {
            apply elem_of_filter.
            set_solver.
          }
          
          intros contra.
          apply zero_predecessors in Hzero.
          rewrite Forall_forall in Hzero.
          specialize (Hzero m').
          spec Hzero. {
            rewrite eq_dP.
            rewrite HeqdP.
            (* rewrite elem_of_list_In. *)
            simpl. right.
            unfold set_filter in Hm'.
            apply elem_of_list_to_set in Hm'.
            apply elem_of_list_In.
            intuition.
          }
          rewrite bool_decide_eq_false in Hzero.
          rewrite Heqm_min in contra.
          intuition.
        * intros contra.
          assert (~ happens_before' m' m). {
            intros contra'.
            apply HdownSetCorrect in contra'.
            intuition set_solver.
          }
          assert (happens_before' m' m). {
            move Hstrict at bottom.
            unfold happens_before'.
            apply t_trans with (y := m_min).
            intuition.
            rewrite Heqd in Hmind.
            apply HdownSetCorrect in Hmind.
            intuition.
          }
          intuition.
  Qed.
  
  Definition senders 
      (s : Cm) : Ci := 
      set_map sender s.
  
  Definition sent_set 
    (i : index) 
    (s : vstate (IM i)) : Cm := list_to_set (@sent_messages_fn message (IM i) _ s).
  
  Definition received_set
    (i : index)
    (s : vstate (IM i)) : Cm := list_to_set (@received_messages_fn message (IM i) _ s).
  
  Definition observed_set
    (i : index)
    (s : vstate (IM i)) : Cm := (sent_set i s) ∪ (received_set i s).
    
  Definition has_justification 
    (i : index)
    (s : vstate (IM i))
    (m : message) :=
    (predSet m) ⊆ (received_set i s).
  
  Definition has_justification_option
    (i : index)
    (s : vstate (IM i))
    (om : option message) :=
    match om with
    | None => True
    | Some m => has_justification i s m
    end.
  
  Definition fullnode_constraint
    (l : composite_label IM)
    (siom : composite_state IM * option message) :=
    let (s, iom) := siom in
    let i := projT1 l in
    let (s', oom) := vtransition (IM i) (projT2 l) ((s i), iom) in
    has_justification_option i (s i) iom /\ has_justification_option i (s i) oom.
    
  
  Definition equivocating_pair
    (m1 m2 : message)
    (i : index) := 
    sender m1 = i /\
    sender m2 = i /\
    ~comparable happens_before' m1 m2.  
  
  Definition is_equivocating_from_set
    (sm : Cm)
    (i : index) :=
    exists (m1 m2 : message), 
    m1 ∈ sm /\
    sender m1 = i /\
    m2 ∈ sm /\ 
    sender m2 = i /\
    ~comparable happens_before' m1 m2.
  
  Lemma is_equivocating_from_set_subseteq
    (sm1 sm2: Cm)
    (i : index)
    (Hsub : sm1 ⊆ sm2) :
    is_equivocating_from_set sm1 i ->
    is_equivocating_from_set sm2 i.
  Proof.
    intros Hi.
    unfold is_equivocating_from_set in *.
    clear -Hi Hsub.
    firstorder.
  Qed.
  
  Lemma is_equivocating_from_set_union
    (sm1 sm2 : Cm)
    (i : index) 
    (Hsm1 : ~is_equivocating_from_set sm1 i)
    (Hsm2 : ~is_equivocating_from_set sm2 i) 
    (Hunion : is_equivocating_from_set (sm1 ∪ sm2) i) : 
    exists a b, a ∈ sm1 /\ b ∈ sm2 /\ 
                sender a = i /\ sender b = i /\ 
                ~comparable happens_before' a b.
  Proof.
    unfold is_equivocating_from_set in Hunion.
    destruct Hunion as [a [b Hab]].
    destruct Hab as [Ha_in [Ha_sender [Hb_in [Hb_sender Hcomp]]]].
    
    rewrite elem_of_union in Ha_in, Hb_in.
    destruct Ha_in as [Ha_in|Ha_in]; destruct Hb_in as [Hb_in|Hb_in].
    - contradict Hsm1.
      exists a, b. intuition.
    - exists a, b. intuition.
    - exists b, a.
      unfold comparable in *.
      intuition congruence.
    - contradict Hsm2.
      exists a, b. intuition.
  Qed.
  
  Local Instance is_equivocating_from_set_dec : RelDecision is_equivocating_from_set.
  Proof.
  Admitted.
  
  Definition index_set : Ci := (list_to_set index_listing).
  
  Definition n := size index_set.
  
  Remark index_set_listing
    (ci : Ci) :
    ci ⊆ index_set.
  Proof.
    intros i Hi.
    apply elem_of_list_to_set.
    apply elem_of_list_In.
    apply Hfinite.
  Qed.
  
  Remark index_set_one
    (i : index) :
    i ∈ index_set.
  Proof.
    apply elem_of_list_to_set.
    apply elem_of_list_In.
    apply Hfinite.
  Qed.
  
  Definition equivocators_from_set 
    (sm : Cm) :=
    set_filter (fun i => bool_decide (is_equivocating_from_set sm i)) _ index_set.
  
  Definition equivocators_from_set_subset
    (sm1 sm2 : Cm)
    (Hincl : sm1 ⊆ sm2) :
    equivocators_from_set sm1 ⊆ equivocators_from_set sm2.
  Proof.
    apply elem_of_subseteq. intros i Hi.
    apply elem_of_filter.
    apply elem_of_filter in Hi.
    specialize (is_equivocating_from_set_subseteq).
    set_solver.
  Qed.
  
  Definition is_equivocating_from_message
     (m : message) :=
     is_equivocating_from_set (downSet m).
  
  Definition is_equivocating_from_message_hb
    (m1 m2 : message) 
    (i : index)
    (Hhb : happens_before' m1 m2) :
    is_equivocating_from_message m1 i->
    is_equivocating_from_message m2 i.
  Proof.
    intros Hm1.
    unfold is_equivocating_from_message in *.
    apply is_equivocating_from_set_subseteq with (sm1 := downSet m1).
    apply hb_subseteq. all : intuition.
  Qed.
    
  Local Instance is_equivocating_from_message_dec : RelDecision is_equivocating_from_message.
  Proof.
    unfold is_equivocating_from_message.
    unfold RelDecision. intros m i.
    apply is_equivocating_from_set_dec.
  Qed.
  
  Definition equivocators_from_message
    (m : message) : Ci := 
    set_filter (fun (i : index) => (bool_decide (is_equivocating_from_message m i))) _ index_set.
    
  Remark equivocators_from_equiv
    (m : message)
    (i : index) :
    ~is_equivocating_from_message m i <-> ~ i ∈ equivocators_from_message m.
  Proof.
    split; intros H'.
    - intros contra.
      apply elem_of_filter in contra.
      rewrite bool_decide_spec in contra.
      intuition.
    - intros contra.
      contradict H'.
      apply elem_of_filter.
      rewrite bool_decide_spec.
      split;[intuition|].
      apply index_set_one.
  Qed.
  
  Lemma lift_equivocating_pair
    (u v u' : message)
    (i : index)
    (Hequiv : equivocating_pair u v i)
    (Hu_u' : happens_before' u u')
    (Hsender_u' : sender u' = i)
    (Hi : ~is_equivocating_from_message u' i) : 
    equivocating_pair u' v i.
  Proof.
    unfold equivocating_pair in *.
    split_prune_and.
    destruct Hequiv as [Hsender_u [Hsender_v Hcomp]].
    intros contra.
    destruct contra as [contra|contra].
    - contradict Hcomp.
      right. left. subst u'. intuition.
    - destruct contra as [contra|contra].
      + contradict Hcomp.
        right. left. 
        apply t_trans with (y := u'); intuition.
      + contradict Hi.
        exists u, v.
        rewrite <- !HdownSetCorrect.
        intuition. 
  Qed.
  
  Definition honest_validators_from_message
    (m : message) : Ci := 
    set_filter (fun (i : index) => negb (bool_decide (is_equivocating_from_message m i))) _ index_set.
    
  Definition honest_votes_count 
    (m : message) : nat :=
    size (honest_validators_from_message m).
    
  Definition messages_from
    (m : message) 
    (i : index) : Cm :=
    set_filter (fun (m' : message) => bool_decide (sender m' = i)) _ (downSet m).
    
  Print messages_from.
  
  Definition latest_message_from
    (m : message)
    (i : index) : option message :=
  (@TopSort.get_maximal_element _ mdec happens_before' happens_before'_dec (elements (messages_from m i))).
  
  Definition latest_message_from_strict
    (m : message)
    (i : index) : option message :=
    match bool_decide (is_equivocating_from_message m i) with
    | true => None
    | false => latest_message_from m i
    end.
  
  Lemma latest_message_in_messages_from
    (m m' : message)
    (i : index) 
    (Hlatest : latest_message_from m i = Some m') :
    m' ∈ (messages_from m i).
  Proof.
    unfold latest_message_from in Hlatest.
    apply maximal_element_in with (P := fun x => True) in Hlatest.
    apply elem_of_list_In in Hlatest. set_solver.
    apply something_pretentious.
    rewrite Forall_forall;intuition.
  Qed.
  
  Lemma latest_message_from_compares
    (m m' : message)
    (i : index)
    (Hlatest : latest_message_from m i = Some m') :
    happens_before' m' m.
  Proof.
    unfold latest_message_from in Hlatest.
    apply latest_message_in_messages_from in Hlatest.
    unfold messages_from in Hlatest.
    apply elem_of_filter in Hlatest.
    rewrite <- HdownSetCorrect in Hlatest.
    intuition.
  Qed.
  
  Lemma latest_message_from_exists
    (m : message)
    (i : index)
    (Hsome : exists mi, mi ∈ (messages_from m i)) :
    exists mi', latest_message_from m i = Some mi'.
  Proof.
    apply get_maximal_element_some with (P := fun x => True).
    apply Forall_forall. intuition.
    destruct Hsome as [mi Hmi].
    
    destruct (elements (messages_from m i)) eqn : eq.
    - apply elements_empty' in eq.
      rewrite eq in Hmi. apply elem_of_empty in Hmi; intuition. 
    - intuition congruence.
  Qed. 
  
  Definition latest_messages
    (m : message) : Cm :=
  list_to_set (ListExtras.cat_option (List.map (latest_message_from m) (elements (honest_validators_from_message m)))).
  
  Lemma honest_validators_size
    (m : message) :
    (Z.of_nat (size (honest_validators_from_message m)) = n - size (equivocators_from_message m))%Z.
  Proof.
    assert (Htemp : (honest_validators_from_message m) ≡ index_set ∖ (equivocators_from_message m)). {
      apply set_equiv. intros i.
      split; intros Hi.
      - apply elem_of_difference.
        apply elem_of_filter in Hi.
        split;[intuition|].
        rewrite <- Is_true_iff_eq_true in Hi. rewrite negb_true_iff in Hi.
        rewrite bool_decide_eq_false in Hi.
        destruct Hi as [Hi _].
        intros contra.
        contradict Hi.
        apply elem_of_filter in contra.
        rewrite bool_decide_spec in contra. intuition. 
     - apply elem_of_difference in Hi.
       apply elem_of_filter.
       rewrite <- Is_true_iff_eq_true. rewrite negb_true_iff. rewrite bool_decide_eq_false.
       split;[|intuition].
       intros contra.
       destruct Hi as [_ Hi].
       contradict Hi.
       apply elem_of_filter.
       rewrite bool_decide_spec.
       split;[intuition|].
       apply index_set_one.
      }
      rewrite Htemp.
      specialize (difference_size_subset index_set (equivocators_from_message m)) as Hdifsub.
      spec Hdifsub. apply index_set_listing.
      intuition.
  Qed.
  
  Lemma latest_messages_size
    (m : message) : 
    (size (latest_messages m) <= n - size (equivocators_from_message m))%Z.
  Proof.
    specialize (honest_validators_size m) as Hhonest_size.
    unfold latest_messages.
    remember (map (latest_message_from m) (elements (honest_validators_from_message m))) as mmap.
    remember (cat_option mmap) as ccat.
    specialize (list_to_set_size ccat) as Hlength_cat.
    assert (Htemp : (length ccat <= n - size (equivocators_from_message m))%Z). {
      specialize (cat_option_length_le mmap) as Hcat_length.
      rewrite Heqccat.
      assert (Htemp': (Z.of_nat (length mmap) = n - size (equivocators_from_message m))%Z). {
        rewrite Heqmmap.
        rewrite map_length.
        specialize (honest_validators_size m).
        intuition.
      }
      rewrite <- Htemp'.
      lia.
    }
    lia. 
  Qed.
  
  Lemma latest_message_in_latest_messages
    (m m' : message)
    (Hlatest : latest_message_from m (sender m') = Some m') 
    (Hne : ~ is_equivocating_from_message m (sender m')):
    m' ∈ (latest_messages m).
  Proof.
    unfold latest_messages.
    apply elem_of_list_to_set.
    apply elem_of_list_In.
    apply in_cat_option.
    exists (Some m').
    split;[|intuition].
    apply in_map_iff.
    exists (sender m').
    split;[intuition|].
    apply elem_of_list_In.
    apply elem_of_elements.
    apply elem_of_filter.
    split.
    - apply Is_true_iff_eq_true.
      rewrite negb_true_iff.
      rewrite bool_decide_eq_false.
      intuition.
    - unfold index_set.
      apply elem_of_list_to_set.
      apply elem_of_list_In.
      apply Hfinite.
  Qed.
  
  Lemma latest_message_sender
    (m m' : message)
    (i : index)
    (Hlatest : latest_message_from m i = Some m') :
    i = sender m'.
  Proof.
     unfold latest_message_from in Hlatest.
     apply maximal_element_in with (P := (fun x => True)) in Hlatest.
     - apply elem_of_list_In in Hlatest.
       apply elem_of_elements in Hlatest.
       apply elem_of_filter in Hlatest.
       rewrite bool_decide_spec in Hlatest.
       intuition.
     - apply something_pretentious.
     - rewrite Forall_forall; intuition.
  Qed.
  
  Lemma latest_message_sender_info
    (m m' : message)
    (Hinm' : m' ∈ (latest_messages m)) : 
    ~ is_equivocating_from_message m (sender m')
    /\ latest_message_from m (sender m') = Some m'.
  Proof.
    unfold latest_messages in Hinm'.
    apply elem_of_list_to_set in Hinm'.
    apply elem_of_list_In in Hinm'.
    apply in_cat_option in Hinm'.
    destruct Hinm' as [om [Hom Heqom]].
    apply in_map_iff in Hom.
    destruct Hom as [omi [Hlatest Hhonest]].
    unfold honest_validators_from_message in Hhonest.
    apply elem_of_list_In in Hhonest.
    apply elem_of_elements in Hhonest.
    apply elem_of_filter in Hhonest.
    rewrite <- Is_true_iff_eq_true in Hhonest.
    destruct Hhonest as [Hhonest Hhonest'].
    rewrite negb_true_iff in Hhonest.
    rewrite bool_decide_eq_false in Hhonest.
    
    assert (Homi : omi = sender m'). {
      rewrite Heqom in Hlatest.
      apply latest_message_sender in Hlatest.
      intuition.
    }
    rewrite <- Homi at 1.
    rewrite Homi in Hlatest.
    rewrite Heqom in Hlatest.
    intuition.
  Qed.
  
  Lemma latest_message_some
    (m m': message)
    (i : index)
    (Hi_nequiv : ~is_equivocating_from_message m i)
    (Hm' : m' ∈ downSet m /\ sender m' = i) :
    i ∈ senders (latest_messages m).
  Proof.
    apply elem_of_map.
    specialize (latest_message_from_exists m i) as Hex.
    spec Hex. {
      exists m'.
      apply elem_of_filter.
      rewrite bool_decide_spec.
      intuition.
    }
    destruct Hex as [mi' Hmi'].
    exists mi'.
    apply latest_message_sender in Hmi' as Hmi''.
    split;[intuition|].
    subst i.
    apply latest_message_in_latest_messages.
    destruct Hm' as [_ Hm'].
    all : intuition.
  Qed.
  
  Lemma non_equiv_compare 
    (u v w: message)
    (Hsenders : sender v = sender w)
    (Hless : happens_before' v u /\ happens_before' w u) 
    (Hnon_equiv : ~ (is_equivocating_from_message u (sender v))) :
    comparable happens_before' v w.
  Proof.
    unfold is_equivocating_from_message in Hnon_equiv.
    unfold is_equivocating_from_set in Hnon_equiv.
    destruct (bool_decide (comparable happens_before' v w)) eqn : eqb.
    - rewrite bool_decide_eq_true in eqb. intuition.
    - rewrite bool_decide_eq_false in eqb.
      contradict Hnon_equiv.
      exists v. exists w.
      split_prune_and.
      + apply HdownSetCorrect;intuition.
      + apply HdownSetCorrect;intuition.
  Qed.
  
  Lemma compare_messages1
    (u v v_dif: message)
    (Hsenders : sender v = sender v_dif)
    (Hlatest : v_dif ∈ (latest_messages u))
    (Hdif : v <> v_dif)
    (Hv_less : happens_before' v u) :
    happens_before' v v_dif.
  Proof.
    apply latest_message_sender_info in Hlatest as Hlatest'.
    
    assert (Hcomp : comparable happens_before' v v_dif). {
      apply non_equiv_compare with (u := u).
      intuition.
      split;[intuition|].
      apply latest_message_from_compares with (i := sender v_dif).
      intuition.
      rewrite Hsenders. intuition.
    }
    
    destruct Hcomp as [|Hcomp];[intuition congruence|].
    destruct Hcomp as [Hcomp|Hcomp].
    - intuition.
    - apply latest_message_sender_info in Hlatest.
      destruct Hlatest as [_ Hlatest].
      apply TopSort.get_maximal_element_correct with (a := v) (P := fun x => true) in Hlatest.
      intuition.
      apply something_pretentious.
      rewrite Forall_forall. intros. intuition.
      apply elem_of_list_In.
      apply elem_of_elements.
      apply elem_of_filter.
      rewrite <- HdownSetCorrect.
      rewrite bool_decide_spec.
      intuition.
  Qed. 
  
      Program Definition divergent_last_messages 
      (m : message)
      (v : option C) :=
    set_filter (fun m' => negb (@bool_decide (vote m' = v) _)) _ (latest_messages m).
    Next Obligation.
      intros.
      apply decide_eq.
    Defined.
    Next Obligation.
      intros.
      solve_decision.
    Defined.
    
    Program Definition concurrent_last_messages 
      (m : message)
      (v : option C) :=
    set_filter (fun m' => @bool_decide (vote m' = v) _) _ (latest_messages m).
    Next Obligation.
      intros.
      apply decide_eq.
    Defined.
    Next Obligation.
      intros.
      solve_decision.
    Qed.
    
 
Section Inspector.

Context
    (X := composite_vlsm IM fullnode_constraint)
    (Hvote : forall (m : message) (oc : option C),
             vote m = oc ->
             (forall (oc' : option C),
             size (concurrent_last_messages m oc) >= 
             size (concurrent_last_messages m oc'))). 
   
    Definition count_votes_for
      (m : message)
      (oc : option C) :=
    List.count_occ decide_eq (List.map vote (elements (latest_messages m))) oc.
    
    Check downSet'.
    
    Definition set_downSet'
      (cm : Cm) : Cm := ⋃ List.map downSet' (elements cm). 
      
    Remark set_downSet'_self
      (cm : Cm) :
      cm ⊆ set_downSet' cm.
    Proof.
      unfold subseteq.
      unfold set_subseteq_instance.
      intros m Hm.
      apply elem_of_union_list.
      exists (downSet' m).
      split.
      - apply elem_of_list_In.
        apply in_map_iff.
        exists m.
        split;[intuition|].
        apply elem_of_list_In; set_solver.
      - apply elem_of_union.
        right. apply elem_of_singleton. 
        reflexivity.
    Qed.
    
    Definition composite_sent
      (s : vstate X) : Cm := ⋃ (List.map (fun i : index => sent_set i (s i)) index_listing).
    
    Definition composite_received
      (s : vstate X) : Cm := ⋃ (List.map (fun i : index => received_set i (s i)) index_listing).
      
    Definition composite_observed
      (s : vstate X) := ⋃ (List.map (fun i : index => received_set i (s i)) index_listing).
    
    Lemma protocol_state_closed
      (s : vstate X)
      (Hpr : protocol_state_prop X s)
      (u v : message)
      (Hcomp : happens_before' v u)
      (Hinu : u ∈ (composite_observed s)) :
      v ∈ (composite_observed s).
    Proof.
    Admitted.
    
    Definition is_equivocating_from_state
      (s : vstate X) :=
      is_equivocating_from_set (composite_observed s).
    
    Local Instance is_equivocating_from_state_dec : RelDecision is_equivocating_from_state.
    Proof.
    Admitted.
    
    Definition equivocators_from_state
      (s : vstate X) :=
      set_filter (fun i => negb (bool_decide (is_equivocating_from_state s i))) _ index_set.
    
    Definition A
      (m : message)
      (v : option C)
      (carrier : Cm) :=
      let divergent_senders := senders (divergent_last_messages m v) in
      (equivocators_from_message m) ∪ (equivocators_from_set (carrier ∪ (downSet m)) ∩ divergent_senders).
    
    Record committee_skeleton : Type := {
      value : C;
      relSet : Cm;
      c0 : Cm;
      com : list Cm;
      q : nat;
      k := length com - 1;
      Hc0 : last_error com = Some c0;
      get_top := hd_error com;
    }.
    
    Definition unanimity 
      (value : C)
      (sm : Cm) :=
      forall (m : message), m ∈ sm -> vote m = Some value.
      
    Definition honesty
      (sm relSet : Cm) :=
      forall (i : index), i ∈ (senders sm) -> i ∉ (equivocators_from_set relSet).
      
    Definition convexity 
      (sm : Cm) :=
      forall (m1 m2 m3 : message),
      m1 ∈ sm /\ m3 ∈ sm ->
      sender m1 = sender m2 /\ sender m3 = sender m2 ->
      happens_before' m1 m2 /\ happens_before' m2 m3 ->
      m2 ∈ sm.
      
    (* Definition of Ci' *)
    Definition relevant_messages
      (sm1 sm2 : Cm) :=
      set_filter (fun m => inb decide_eq (sender m) (elements (senders sm1))) _ sm2. 
    
    Definition density
      (sm1 sm2 : Cm)
      (q : nat) :=
      forall (m : message),
      m ∈ sm1 ->
      size (senders (set_filter (fun v => bool_decide (happens_before' v m)) _ (relevant_messages sm1 sm2))) >= q.
    
    Inductive valid_com_prop : Cm -> Cm -> C -> nat -> list Cm -> Prop :=
    | valid_com_base 
      (relSet : Cm)
      (c0 : Cm)
      (value : C)
      (q : nat)
      (H : unanimity value c0 /\ honesty c0 relSet /\ convexity c0) : valid_com_prop relSet c0 value q [c0]
    | valid_com_ind 
        (relSet : Cm)
        (c0 : Cm)
        (value : C)
        (q : nat)
        (sm1 sm2 : Cm) 
        (l : list Cm)
        (Hincl : sm1 ⊆ sm2)
        (Hdensity : density sm1 sm2 q)
        (Hconv : convexity sm1)
        (Hgood : valid_com_prop relSet c0 value q (sm2 :: l)) : valid_com_prop relSet c0 value q (sm1 :: (sm2 :: l)).
    
    Definition committee : Type := {
      comskel : committee_skeleton | valid_com_prop (relSet comskel) (c0 comskel) (value comskel) (q comskel) (com comskel)
    }.
    
    Lemma committee_info
      (skel : committee_skeleton)
      (Hvalid : valid_com_prop (relSet skel) (c0 skel) (value skel) (q skel) (com skel)) :
        convexity (c0 skel) /\
        unanimity (value skel) (c0 skel) /\
        honesty (c0 skel) (relSet skel) /\        
        (forall (c : Cm), In c (com skel) -> c ⊆ (c0 skel)).
    Proof.
      simpl in skel.
      
      remember (relSet skel) as com_relSet.
      remember (c0 skel) as com_c0.
      remember (value skel) as com_value'.
      remember (q skel) as com_q.
      remember (com skel) as com_com.
      remember (Hc0 skel) as com_Hc0.
      generalize dependent skel.
      
      induction Hvalid.
      - intros.
        split_prune_and.
        intros c Hc.
        destruct Hc; set_solver.
      - intros.
        assert (Hbase : last_error (sm2 :: l) = Some c1). {
          move com_Hc0 at bottom.
          clear Heqcom_Hc0.
          rewrite <- Heqcom_com in com_Hc0.
          rewrite <- Heqcom_c0 in com_Hc0.
          simpl in *.
          destruct l.
          + intuition.
          + rewrite <- com_Hc0.
            f_equal.
            rewrite !unroll_last.
            intuition.
        }
        remember (@Build_committee_skeleton value0 relSet0 c1 (sm2 :: l) q0 Hbase)  as new_skel.
        simpl in new_skel. 

        specialize (IHHvalid new_skel).
        subst new_skel.
        feed_specialize_prune IHHvalid.
        simpl in IHHvalid.
        specialize (IHHvalid Hbase eq_refl).
        destruct IHHvalid as [base IHHvcom].
        split_prune_and.
        intros c Hc.
        destruct IHHvcom as [_ [_ IHH]].
        simpl in Hc.
        assert (Hsm2 : sm2 ⊆ c1) by (specialize (IHH sm2); intuition).
        destruct Hc as [Hc|Hc]; (clear -Hsm2 Hc IHH Hincl; set_solver). 
    Qed.
    
    Local Open Scope Z_scope.
    
    (* Local Coercion Z_of_nat : nat >-> Z. *)
    
    Theorem main
      (s : vstate X)
      (Hpr : protocol_state_prop X s)
      (Com : committee)
      (skel := proj1_sig Com)
      (relSet := relSet skel)
      (q := q skel)
      (k := k skel)
      (value := value skel)
      (c0 := c0 skel)
      (top : Cm)
      (Htop : get_top skel = Some top)
      (HrelSet : relSet = set_downSet' c0)
      (Hs : relSet ⊆ composite_observed s)
      (fake_u : message)
      (Pdown := fun m' =>
        (happens_before' m' fake_u \/ m' = fake_u) /\ 
        m' ∈ (composite_observed s) /\
        vote m' <> Some value /\
        (exists m'',  
        m'' ∈ (downSet m') /\ 
        m'' ∈ top))
      (u : message)
      (Hu_P : Pdown u)
      (Hu_minimal : is_minimal_wrt_P u Pdown)
      (Au := A u (Some value) c0) :
      (size Au) * (2 ^ k) >=  
      (2 * q - n) * (2 ^ k - 1).
    Proof.
      destruct Com as [skel' Hcom]. simpl in *.
      subst skel.
      simpl in *.
      remember (Inspector.value skel') as value'.
      remember (Inspector.q skel') as q'.
      remember (com skel') as com'.
      remember (Inspector.relSet skel') as relSet'.
      remember (Inspector.c0 skel') as c0'.
      remember (Hc0 skel') as Hc0'.
    
      generalize dependent fake_u.
      generalize dependent u.
      generalize dependent top. 
      generalize dependent skel'.

      induction Hcom.
      - intros.
        simpl in *.
        unfold k0. unfold Inspector.k.
        rewrite <- Heqcom'. simpl. lia.
      - intros.
        
        unfold Pdown in Hu_P.
        destruct Hu_P as [_ Hu_P].
        apply and_assoc in Hu_P.
        
        destruct Hu_P as [Hu_P Huc].
        destruct Huc as [uk Huk].
        
        assert (Hlast_temp : last_error (com skel') = Some c1). {
          rewrite Heqc0'. intuition.
        }
        
        remember (@Build_committee_skeleton value relSet c1 (com skel') q Hlast_temp) as current. simpl in current.
        
        specialize (committee_info current) as Hinfo.
        spec Hinfo. {
          simpl. subst current. simpl in *.
          rewrite <- Heqcom'.
          apply valid_com_ind; intuition.
        }
        
        subst current. simpl in *.
        
        assert (Hc0_honest : honesty c0 relSet) by intuition.
        assert (Hc0_convex : convexity c0) by intuition.
        
        assert (Hc0_vote : forall m, m ∈ c1 -> vote m = Some value). {
          destruct Hinfo as [_ [Hinfo _]].
          intuition.
        }
        
        assert (Hsm1_in_c0 : sm1 ⊆ c1). {
          destruct Hinfo as [_ [_ [_ Hinfo]]].
          apply Hinfo. rewrite <- Heqcom'.
          simpl. intuition.
        }
        
        assert (Hsm2_in_c0 : sm2 ⊆ c1). {
          destruct Hinfo as [_ [_ [_ Hinfo]]].
          apply Hinfo. rewrite <- Heqcom'.
          simpl. intuition.
        }
        
        assert (Hcomp_in_c1 : forall m1 m2, 
                              m1 ∈ c1 /\ m2 ∈ c1 /\ sender m1 = sender m2 -> 
                              comparable happens_before' m1 m2). {
          intros m1 m2 Hm.
          destruct (decide (comparable happens_before' m1 m2)).
          - intuition.
          - contradict Hc0_honest.
            intros contra_honest.
            unfold honesty in contra_honest.
            specialize (contra_honest (sender m1)).
            spec contra_honest. {
              apply elem_of_map.
              exists m1.
              intuition.
            }
            contradict contra_honest.
            apply elem_of_filter.
            split;[|apply index_set_one].
            rewrite bool_decide_spec.
            exists m1, m2.
            split_prune_and;rewrite HrelSet.
            + apply elem_of_subseteq with (X0 := c0).
              apply set_downSet'_self.
              intuition.
            + apply elem_of_subseteq with (X0 := c0).
              apply set_downSet'_self.
              intuition.
        }
        
        assert (Huk_u : forall m', happens_before' m' uk -> happens_before' m' u). {
          intros.
          apply t_trans with (y := uk).
          intuition.
          destruct Huk as [Huk _].
          apply HdownSetCorrect in Huk.
          intuition.
        }
        
        clear Hinfo.
        
        assert (Htop_sm1 : top = sm1). {
               unfold get_top in Htop.
               rewrite <- Heqcom' in Htop.
               simpl in Htop.
               inversion Htop.
               reflexivity.
        }
        
        remember (equivocators_from_message u) as Eu.
        
        remember (senders (set_filter (fun v => bool_decide (happens_before' v u)) _ (relevant_messages sm1 sm2))) as Vk_1.
        
        assert (Hin_Vk : forall i, i ∈ Vk_1 -> exists mi, mi ∈ (messages_from u i)). {
          intros i Hi.
          rewrite HeqVk_1 in Hi.
          apply elem_of_map in Hi.
          destruct Hi as [mi [Hsender Hinmi]].
          exists mi.
          apply elem_of_filter.
          rewrite bool_decide_spec.
          split;[intuition congruence|].
          apply elem_of_filter in Hinmi.
          destruct Hinmi as [Hinmi _].
          rewrite <- Is_true_iff_eq_true in Hinmi.
          rewrite bool_decide_eq_true in Hinmi.
          apply HdownSetCorrect in Hinmi.
          intuition congruence.
        }
        
        assert (Hinvk2 : forall i, i ∈ Vk_1 -> exists mi, sender mi = i /\ mi ∈ sm2 /\ happens_before' mi u). {
          intros i Hi.
          rewrite HeqVk_1 in Hi.
          apply elem_of_map in Hi.
          destruct Hi as [mi [Hsender Hinmi]].
          apply elem_of_filter in Hinmi.
          rewrite bool_decide_spec in Hinmi.
          unfold relevant_messages in Hinmi.
          destruct Hinmi as [Hinmi Hinmi'].
          apply elem_of_filter in Hinmi'.
          exists mi; intuition.
        }
        
        assert (Hinvk3 : forall i, i ∈ Vk_1 -> exists mi, sender mi = i /\ mi ∈ sm1). {
          intros i Hi.
          rewrite HeqVk_1 in Hi.
          apply elem_of_map in Hi.
          destruct Hi as [mi [Hsender Hinmi]].
          apply elem_of_filter in Hinmi.
          destruct Hinmi as [Hinmi Hinmi'].
          apply elem_of_filter in Hinmi'.
          destruct Hinmi' as [Hinmi' _].
          rewrite <- Is_true_iff_eq_true in Hinmi'.
          rewrite <-in_correct in Hinmi'.
          apply elem_of_list_In in Hinmi'.
          apply elem_of_elements in Hinmi'.
          apply elem_of_map in Hinmi'.
          destruct Hinmi' as [mi' Hneed].
          exists mi'. intuition congruence.
        }
        
        assert (Hinvk4 : forall i, i ∈ Vk_1 -> ~ is_equivocating_from_set c1 i). {
          intros v Hv.
          specialize (Hc0_honest v).
          spec Hc0_honest. {
            specialize (Hinvk3 v Hv).
            destruct Hinvk3 as [v' Hinvk3].
            apply elem_of_map. exists v'.
            split;[intuition|].
            apply Hsm1_in_c0; intuition.
          }
          intros contra.
          contradict Hc0_honest.
          apply elem_of_filter.
          rewrite bool_decide_spec.
          split;[|apply index_set_one].
          apply is_equivocating_from_set_subseteq with (sm1 := c1).
          rewrite HrelSet.
          apply set_downSet'_self.
          intuition.
        }
        
        assert (HVk1_sz : size Vk_1 >= q). {
          rewrite HeqVk_1.
          move Hdensity at bottom.
          unfold density in Hdensity.
          unfold Pdown in Hu_P.
          specialize (Hdensity uk).
          spec Hdensity. {
            destruct Hu_P as [_ Hu_P].
            move Htop at bottom.
            unfold get_top in Htop.
            rewrite <- Heqcom' in Htop.
            simpl in Htop.
            inversion Htop.
            intuition.
          }
          unfold q.
          unfold senders.
          unfold senders in Hdensity.
          remember (set_filter (λ v : message, bool_decide (happens_before' v uk))
                   (λ x : message, Is_true_dec (bool_decide (happens_before' x uk)))
                   (relevant_messages sm1 sm2)) as fm1.
          remember (set_filter (λ v : message, bool_decide (happens_before' v u))
                   (λ x : message, Is_true_dec (bool_decide (happens_before' x u)))
                   (relevant_messages sm1 sm2)) as fm2.
          
          assert (fm_incl : fm1 ⊆ fm2). {
            rewrite Heqfm1.
            rewrite Heqfm2.
            apply filter_subprop.
            intros m.
            rewrite !bool_decide_spec.
            intuition.
          }

          assert (map_fm_incl : set_map (D := Ci) sender fm1 ⊆ set_map (D := Ci) sender fm2). {
            apply set_map_subset; intuition.
          }
          
          assert (size (set_map (D := Ci) sender fm1) <= size (set_map (D := Ci) sender fm2)). {
            apply inj_le.
            apply subseteq_size.
            intuition.
          }
          lia.
        }
        
        remember (set_filter (fun i => bool_decide (is_equivocating_from_message u i)) _ Vk_1) as Veq.
        remember (divergent_last_messages u (Some value)) as latest_divergent.
        remember ((senders latest_divergent) ∩ Vk_1) as Vchange.
        
        remember (senders (concurrent_last_messages u (Some value)) ∖ Vk_1) as extra_voters.
        
        assert (Hin_veq1 : forall i, i ∈ Veq -> is_equivocating_from_message u i). {
          intros i Hi. rewrite HeqVeq in Hi.
          apply elem_of_filter in Hi.
          rewrite bool_decide_spec in Hi.
          intuition.
        }
        
        assert (Hin_veq2 : forall i, i ∈ Vk_1 /\ i ∉ Veq -> ~ is_equivocating_from_message u i). {
          intros i Hi. rewrite HeqVeq in Hi.
          intros contra.
          destruct Hi as [Hini Hi].
          contradict Hi; apply elem_of_filter; rewrite bool_decide_spec; intuition.
        }
        
        assert (Hin_veq3 : forall i, i ∈ Vk_1 /\ i ∉ Veq -> exists mi, latest_message_from u i = Some mi). {
          intros i Hi.
          assert (H' := Hi).
          apply Hin_veq2 in H'.
          destruct Hi as [Hi _].
          apply latest_message_from_exists.
          apply Hin_Vk in Hi.
          intuition.
        }
        
        assert (Hin_vchange : forall i, i ∈ Vchange -> ~ is_equivocating_from_message u i /\
                                        (exists mi, latest_message_from u i = Some mi /\ 
                                        vote mi <> Some value)). {
          intros i Hi. rewrite HeqVchange in Hi.
          apply elem_of_intersection in Hi.
          rewrite Heqlatest_divergent in Hi.
          destruct Hi as [Hi _].
          apply elem_of_map in Hi.
          destruct Hi as [mi [Hsender Hinmi]].
          apply elem_of_filter in Hinmi.
          rewrite <- Is_true_iff_eq_true in Hinmi.
          rewrite negb_true_iff in Hinmi.
          rewrite bool_decide_eq_false in Hinmi.
          destruct Hinmi as [Hvote_mi Hlatest].
          assert (Hlatest' := Hlatest).
          apply latest_message_sender_info in Hlatest.
          destruct Hlatest as [Hnon_equiv Hlatest].
          subst i.
          split;[intuition|].
          exists mi.
          split;intuition. 
        }
        
        assert (Heq_change_disjoint : Veq ## Vchange). {
          intros i contra1 contra2.
          apply Hin_vchange in contra2.
          apply Hin_veq1 in contra1.
          intuition.
        }
        
        assert (Hmi: forall i, i ∈ Vk_1 /\ i ∉ Veq /\ i ∉ Vchange -> 
          (exists mi, (latest_message_from u i) = Some mi /\ vote mi = Some value)). {
          intros i Hi.
          destruct Hi as [Hk_1 [Hn_veq Hn_change]].
          specialize (Hin_veq3 i).
          spec Hin_veq3. intuition.
          destruct Hin_veq3 as [mi Hlatest].
          exists mi.
          split; [intuition|].
          
          destruct (@decide (vote mi = Some value) (decide_eq (vote mi) (Some value))). 
          - intuition.
          - contradict Hn_change.
            rewrite HeqVchange.
            apply elem_of_intersection.
            split;[|intuition].
            rewrite Heqlatest_divergent.
            apply elem_of_map.
            
            assert (Hsendermi: sender mi = i) by (apply latest_message_sender in Hlatest; intuition).
            
            exists mi.
            split;[intuition|].
            apply elem_of_filter. rewrite <- Is_true_iff_eq_true. 
            rewrite negb_true_iff. rewrite bool_decide_eq_false.
            split;[intuition|].
            apply latest_message_in_latest_messages.
            rewrite Hsendermi. intuition.
            apply Hin_veq2.
            rewrite Hsendermi.
            intuition.
        }
        remember (Vk_1 ∖ (Veq ∪ Vchange)) as value_voters_vk.
        
        assert (Hvoters_size1 : (size value_voters_vk + size Veq + size Vchange = size Vk_1)). {
          rewrite Heqvalue_voters_vk.
          assert (Hsizeu : Z.of_nat (size (Veq ∪ Vchange)) = size Veq + size Vchange). {
            specialize (size_union Veq Vchange Heq_change_disjoint) as Hnat.
            lia.
          }
          rewrite <- Zplus_assoc.
          rewrite <- Hsizeu.
          specialize (size_union_alt (Veq ∪ Vchange) Vk_1) as Hinv.
          
          assert (Hveq2: Vk_1 ≡ Veq ∪ Vchange ∪ Vk_1). {
             rewrite <- assoc by (apply union_assoc).
             assert (Htemp: Vchange ∪ Vk_1 ≡ Vk_1). {
                apply subseteq_union_1.
                rewrite HeqVchange.
                apply intersection_subseteq_r.
             }
             rewrite Htemp.
             specialize (subseteq_union_1 Veq Vk_1) as Htemp2.
             spec Htemp2.
             rewrite HeqVeq.
             clear. set_solver.
             set_solver.
          }
          rewrite <- Hveq2 in Hinv.
          lia.
        }
        
        remember (senders (concurrent_last_messages u (Some value))) as value_voters.
        
        assert (Hvalue_vk_incl : value_voters_vk ⊆ value_voters). {
          apply elem_of_subseteq. intros v Hv.
          rewrite Heqvalue_voters_vk in Hv.
          rewrite Heqvalue_voters.
          apply elem_of_difference in Hv.
          destruct Hv as [Hv Hvn].
          specialize (Hmi v).
          spec Hmi. {
            split_prune_and.
            - intros contra. contradict Hvn. apply elem_of_union. left. intuition.
            - intros contra. contradict Hvn. apply elem_of_union. right. intuition.
          }
          destruct Hmi as [mi Hmi].
          apply elem_of_map.
          exists mi. 
          assert (Htemp : v = sender mi) . {
            destruct Hmi as [Hmi _].
            apply latest_message_sender in Hmi.
            intuition.
          }
          split;[intuition|].
          apply elem_of_filter.
          rewrite bool_decide_spec.
          split;[intuition|].
          apply latest_message_in_latest_messages.
          subst v. intuition.
          intros contra.
          contradict Hvn.
          apply elem_of_union. left.
          rewrite HeqVeq.
          apply elem_of_filter.
          rewrite bool_decide_spec.
          subst v. intuition.
        }
        
        assert (Hvoters_disjoint : extra_voters ## value_voters_vk). {
          apply elem_of_disjoint. intros v Hv Hv2.
          rewrite Heqextra_voters in Hv.
          rewrite Heqvalue_voters_vk in Hv2.
          apply elem_of_difference in Hv.
          apply elem_of_difference in Hv2.
          intuition.
        }
        
        assert (Hsz_voters : Z.of_nat (size (extra_voters ∪ value_voters_vk)) >= (q - size Veq - size Vchange) + size extra_voters). {
          specialize (size_union extra_voters value_voters_vk Hvoters_disjoint) as Hun.
          rewrite Hun.
          assert (Z.of_nat (size value_voters_vk) = size Vk_1 - size Veq - size Vchange) by lia.
          assert (Z.of_nat (size value_voters_vk) >= q - size Veq - size Vchange) by lia.
          lia. 
        }
        
        assert (Hineq1 : 2 * (q - (size Veq) - (size Vchange) + (size extra_voters)) <= n - size Eu). {
          move Hvote at bottom.
          assert (Hvote' := Hvote).
          
          assert (Hn: ~ 2 * (q - (size Veq) - (size Vchange) + (size extra_voters)) > n - size Eu). {
            intros contra.
            destruct Hu_P as [_ Hu_P].
            contradict Hu_P.
            
            assert (Hvotes_for : size value_voters >= (q - size Veq - size Vchange) + (size extra_voters)). {
                assert (Htemp : extra_voters ∪ value_voters_vk ⊆ value_voters). {
                  apply elem_of_subseteq. intros v Hv.
                  apply elem_of_union in Hv.
                  destruct Hv as [Hv | Hv].
                  - rewrite Heqextra_voters in Hv.
                    apply elem_of_difference in Hv.
                    intuition.
                  - apply elem_of_subseteq with (X0 := value_voters_vk); intuition.
                }
                assert (Htemp2 : size value_voters >= size (extra_voters ∪ value_voters_vk)). {
                  specialize (subseteq_size (extra_voters ∪ value_voters_vk) value_voters Htemp) as Htemp3.
                  lia.
                }
                lia.
            }
            
            specialize (Hvote' u (vote u) eq_refl (Some value)).
            
            destruct (@decide (vote u = Some value)).
            apply decide_eq.
            - intuition.
            - assert (Htemp : (concurrent_last_messages u (vote u)) ∪ (concurrent_last_messages u (Some value)) ⊆ latest_messages u). {
                apply elem_of_subseteq. intros m Hm.
                apply elem_of_union in Hm.
                destruct Hm as [Hm | Hm]; apply elem_of_filter in Hm; intuition.
              }
              
              assert (Htemp4 : size ((concurrent_last_messages u (vote u)) ∪ (concurrent_last_messages u (Some value))) <= size (latest_messages u)). {
                specialize (subseteq_size (concurrent_last_messages u (vote u) ∪ concurrent_last_messages u (Some value)) (latest_messages u) Htemp).
                lia.
              }
              
              assert (Htemp5 : Z.of_nat (size (latest_messages u)) <= n - size Eu). {
                specialize (latest_messages_size u). rewrite HeqEu. lia.
              }
              
              assert (Htemp2: Z.of_nat (size (concurrent_last_messages u (vote u) ∪ (concurrent_last_messages u (Some value)))) =
                      size (concurrent_last_messages u (vote u)) + size (concurrent_last_messages u (Some value))). {
                specialize (size_union (concurrent_last_messages u (vote u)) (concurrent_last_messages u (Some value))) as Htemp3.
                spec Htemp3. {
                  apply elem_of_disjoint. intros m Hm Hm2.
                  apply elem_of_filter in Hm.
                  apply elem_of_filter in Hm2.
                  rewrite bool_decide_spec in *.
                  intuition congruence.
                }
                lia.
              }
              
              assert (Htemp6: size (concurrent_last_messages u (vote u)) + size (concurrent_last_messages u (Some value)) <= n - size Eu) by lia.
              rewrite Heqvalue_voters in Hvotes_for. 
              assert (Htemp7 : size (senders (concurrent_last_messages u (Some value))) <= size (concurrent_last_messages u (Some value))). {
                 specialize (set_map_size_upper_bound (C := Cm) (D := Ci) sender (concurrent_last_messages u (Some value))).
                 unfold senders.
                 lia.
              }
              lia.
          } lia.
        }
        
        assert (HVeq_incl_Eu : Veq ⊆ Eu). {
          rewrite HeqEu.
          rewrite HeqVeq.
          unfold equivocators_from_message.
          apply filter_subset.
          apply index_set_listing.
        }
        
        assert (Hineq2 : n - size Eu <= n - size Veq). {
          cut (size Veq <= size Eu). {
            lia.
          }
          apply inj_le.
          apply subseteq_size.
          apply HVeq_incl_Eu.
        }
        
        assert (Hineq3 : 2 * q <= n + size Veq + 2 * (size Vchange) - 2 * (size extra_voters)) by lia.
        
        assert (H_Veq_incl_Au : Veq ⊆ Au). {
          unfold Au.
          unfold A.
          rewrite HeqEu in HVeq_incl_Eu.
          clear -HVeq_incl_Eu.
          set_solver.
        }
        
        destruct (elements Vchange) eqn : eqd_Vchange.
        + apply elements_empty' in eqd_Vchange.
          rewrite eqd_Vchange in Hineq3.
          rewrite size_empty in Hineq3. simpl in Hineq3.
          assert (HszVeqAu : size Veq <= size Au). {
            apply subseteq_size in H_Veq_incl_Au.
            lia.
          }
          assert (size Veq >= 2 * q - n) by lia.
          assert (size Au >= 2 * q - n) by lia.
          assert (2 ^ k0 - 1 >= 0). {
            unfold k0. 
            unfold k.
            assert ((length (com skel') - 1)%nat >= 0) by lia.
            unfold Z.pow.
            rewrite <- Heqcom'.
            simpl.
            specialize (Zpower2_le_lin (S (length l))) as Zpow.
            spec Zpow. lia.
            lia.
          }
          nia.
        + assert (Hu': exists u', happens_before' u' u /\
                             (vote u' <> Some value) /\
                             (exists v, v ∈ (downSet u') /\ v ∈ sm2)). {
            move Hin_vchange at bottom.
            specialize (Hin_vchange i).
            assert (HiniVchange : i ∈ Vchange). {
              apply elem_of_elements.
              rewrite eqd_Vchange. clear -eqd_Vchange. set_solver.
            }
            spec Hin_vchange. intuition.
            destruct Hin_vchange as [H_i_non_equiv Hinvchange].
            destruct Hinvchange as [u'' [Hlatest_u'' Hvote_u'']].
            
            assert (Hsender_u'': sender u'' = i). {
              apply latest_message_sender in Hlatest_u''.
              intuition.
            }
            
            exists u''.
            split. 
            * apply latest_message_from_compares in Hlatest_u''.
              intuition. 
            * split;[intuition|].
              assert (Hini : i ∈ Vk_1). {
                rewrite HeqVchange in HiniVchange.
                apply elem_of_intersection in HiniVchange. 
                intuition.
              }
              assert (Hini' := Hini).
              apply Hinvk2 in Hini.
              destruct Hini as [mi [Hsender Hmi2]].
              exists mi.
              split;[|intuition].
              
              assert (Hless_mi: happens_before' mi  u''). {
                apply compare_messages1 with (u := u).
                intuition congruence.
                apply latest_message_in_latest_messages.
                intuition congruence.
                intuition congruence.
                specialize (Hc0_vote mi).
                spec Hc0_vote. 
                apply Hsm2_in_c0; intuition. 
                intuition congruence.
                intuition.
              }
              apply HdownSetCorrect.
              intuition.
          }
          
          move IHHcom at bottom.
          simpl in IHHcom.
          spec IHHcom. intuition.
          
          assert (Htemp : Some (List.last l sm2) = Some c1). {
            f_equal.
            move Hc0' at bottom.
            rewrite Heqc0'.
            clear HeqHc0'.
            rewrite <- Heqcom' in Hc0'.
            simpl in Hc0'.
            inversion Hc0'.
            destruct l.
            - intuition.
            - inversion Hc0'.
              rewrite !unroll_last.
              intuition.
          }
          
          remember (@Build_committee_skeleton value relSet0 c1 (sm2 :: l) q Htemp) as new_skel.
          simpl in new_skel.
        
          specialize (IHHcom Hs new_skel).
          rewrite Heqnew_skel in IHHcom. simpl in IHHcom.
          spec IHHcom. intuition congruence.
          spec IHHcom. intuition congruence.
          spec IHHcom. intuition congruence.
          specialize (IHHcom eq_refl eq_refl Htemp eq_refl).
          specialize (IHHcom sm2). unfold get_top in IHHcom. simpl in IHHcom.
          specialize (IHHcom eq_refl).
          
          destruct Hu' as [u'' Hu''].
          
          remember (fun u' => (happens_before' u' u \/ u' = u) /\ 
                             u' ∈ (composite_observed s) /\
                             (vote u' <> Some value) /\
                             (exists v, v ∈ (downSet u') /\ v ∈ sm2)) as Pdown'.
          specialize (minimal_element_P Pdown') as Hmin_u'.
          
            spec Hmin_u'. {
              intros. unfold Decision.
              rewrite HeqPdown'.
              apply Decision_and.
              - apply Decision_or.
                apply happens_before'_dec.
                apply decide_eq.
              - apply Decision_and.
                apply elem_of_dec_slow. 
                apply Decision_and.
                apply Decision_not. apply decide_eq.
                apply set_Exists_dec.
                intros.
                apply elem_of_dec_slow.
          }
          
          specialize (Hmin_u' u'').
          
          assert (Hu''_obs : u'' ∈ (composite_observed s)). {
            apply protocol_state_closed with (u := u).
            all : intuition.
          }
          
          spec Hmin_u'. {
            rewrite HeqPdown'.
            intuition.
          }
          
          destruct Hmin_u' as [u' Hmin_u'].

          specialize (IHHcom u' u).
          
          spec IHHcom. {
            unfold is_minimal_wrt_P in Hmin_u'.
            rewrite HeqPdown' in Hmin_u'.
            intuition.
          }
          
          spec IHHcom. {
            rewrite HeqPdown' in Hmin_u'.
            unfold is_minimal_wrt_P in *.
            destruct Hmin_u' as [Hmin_u'1 Hmin_u'2].
            split.
            - intuition.
            - intros m' Hmin_u'3.
              specialize (Hmin_u'2 m').
              apply Hmin_u'2.
              apply Hmin_u'3.
          }
          
          clear Heqvalue' Heqq' HeqrelSet' Heqc0' Hc0' HeqHc0' Htop Hcom.
          
          unfold k in IHHcom. simpl in IHHcom.
          
          remember (A u' (Some value) c1) as Au'.
          clear Hineq2 Hsz_voters.
          
          assert (Hineq2main : (size (Au' ∪ Veq) + size Vchange - size extra_voters) * 2 ^ k0 >= (2 * q0 - n) * (2 ^ k0 - 1)). {
            specialize (union_size_ge_average Au' Veq) as Havg.
            
            assert (Hineq_temp1 : 2 * (size (Au' ∪ Veq) + size Vchange - size extra_voters) >= size Au' + size Veq + 2 * size Vchange - 2 * size extra_voters) by lia.
            
            move Hineq_temp1 at bottom. (* Hineq1 *)
            unfold k0. unfold k. simpl.
            rewrite <- Heqcom'. simpl.
            unfold value in HeqAu'.
            rewrite <- HeqAu' in IHHcom.
            
            assert (Z.succ (length l) = S (length l)) by lia.
            rewrite <- H13.
            rewrite Z.pow_succ_r by lia.
            clear -Havg Hineq_temp1 Hineq1 Hineq3 IHHcom.
            assert ((length l - 0)%nat = length l) by lia.
            rewrite H in IHHcom.
            unfold q in Hineq3.
            clear Hineq1 H.
            assert (2 * q0 - n <= size Veq + 2 * size Vchange - 2 * size extra_voters) by lia.
            clear Hineq3.
            remember (2 ^ length l) as p2.
            cut ((size (Au' ∪ Veq) + size Vchange - size extra_voters) * (2 * p2) >= (2 * q0 - n) * (2 * p2) - (2 * q0 - n)). {
              lia.
            }
            rewrite Zmult_assoc.
            rewrite Zmult_minus_distr_r.
            rewrite Zmult_plus_distr_l.
            replace (size (Au' ∪ Veq) * 2) with (2 * size (Au' ∪ Veq)) by lia.
            rewrite Zmult_minus_distr_r.
            rewrite Zmult_plus_distr_l.
            assert (p2 > 0). {
              rewrite Heqp2.
              unfold Z.pow.
              destruct (Z.of_nat (length l)) eqn : eqzp.
              - lia.
              - specialize (Zpower_pos_pos 2 p). lia.
              - lia.
            }
            replace (2 * size (Au' ∪ Veq) * p2 + size Vchange * 2 * p2) with (2 * (size (Au' ∪ Veq) + size Vchange) * p2) by lia.
            assert ((size Au' + size Veq + 2 * size Vchange) * p2 >= (2 * q0 - n) * (2 * p2) - (2 * q0 - n)). {
              nia.
            }
            
            nia.
          }
          
          clear Hineq1 Hineq3 HVk1_sz Hvoters_size1 IHHcom Heqnew_skel Htemp Heqcom'.
          
          rewrite HeqPdown' in Hmin_u'.
          unfold is_minimal_wrt_P in Hmin_u'.
          destruct Hmin_u' as [Hu' Hmin_u'].
          
          destruct Hu' as [Hu_u' Hu'].
          
          assert (HVchange_sub_Au : Vchange ⊆ Au). {
            intros v Hv.
            move Hin_vchange at bottom.
            specialize (Hin_vchange v Hv).
            destruct Hin_vchange as [Hin_change' Hin_vchange].
            destruct Hin_vchange as [vdif Hdif].
            
            assert (Hvdif_info : happens_before' vdif u /\ sender vdif = v). {
              destruct Hdif as [Hdif1 Hdif2].
              apply latest_message_from_compares in Hdif1 as Hcompv.
              apply latest_message_sender in Hdif1.
              intuition.
            }
            
            assert (Hvdif_in_latest: vdif ∈ latest_messages u). {
              apply latest_message_in_latest_messages; replace (sender vdif) with v by intuition; intuition.
            }
            
            assert (Hvtemp: v ∈ Vk_1). {
              rewrite HeqVchange in Hv.
              apply elem_of_intersection in Hv; intuition.
            }
            
            move Hinvk2 at bottom.
            specialize (Hinvk2 v Hvtemp).
            destruct Hinvk2 as [vk1 Hvk1].
            
           assert (Hvk1_vote : vote vk1 = Some value). {
             apply Hc0_vote.
             apply Hsm2_in_c0.
             intuition.
           }
            
           assert (Hvdif_vk1 : happens_before' vk1 vdif). {
            apply compare_messages1 with (u := u).
            all : intuition congruence.
           }
            
            move Hinvk3 at bottom.
            specialize (Hinvk3 v Hvtemp).
            destruct Hinvk3 as [vk Hvk].
            
            assert (Hvk_vote : vote vk = Some value). {
              assert (Hvk_c1 : vk ∈ c1). {
                 destruct Hvk as [_ Hvk].
                 apply Hsm1_in_c0; assumption.
              }
              apply (Hc0_vote vk Hvk_c1).
            }
            
            assert (Hncomp : ~ comparable happens_before' vk vdif). {
              intros contra.
              unfold comparable in contra.
              destruct contra as [contra|contra].
              - intuition congruence.
              - destruct contra as [contra|contra].
                + contradict Hu_minimal.
                  unfold Pdown.
                  intros contra2.
                  unfold is_minimal_wrt_P in contra2.
                  destruct contra2 as [Hutemp contra2].
                  destruct Hutemp as [Hutemp _].
                  
                  specialize (contra2 vdif).
                  spec contra2. {
                    split_and?.
                    - left.
                      destruct Hutemp.
                      + apply t_trans with (y := u); intuition.
                      + subst fake_u. intuition.
                    - apply protocol_state_closed with (u := u); intuition.
                    - intuition.
                    - exists vk.
                      split_and?.
                      + apply HdownSetCorrect. assumption.
                      + rewrite Htop_sm1. clear -Hvk. intuition.
                  }
                  intuition.
                + contradict Hc0_convex.
                  intros contra_convex.
                  unfold convexity in contra_convex.
                  specialize (contra_convex vk1 vdif vk).
                  spec contra_convex. intuition.
                  spec contra_convex. intuition congruence.
                  spec contra_convex. intuition.
                  specialize (Hc0_vote vdif contra_convex).
                  intuition congruence.
            }
            
            assert (Hv_equiv: v ∈ equivocators_from_set (c1 ∪ downSet u)). {
              unfold equivocators_from_set.
              apply elem_of_filter.
              rewrite bool_decide_spec.
              split.
              - unfold is_equivocating_from_set.
                exists vk. exists vdif.
                split_and?.
                + apply elem_of_union. 
                  left.
                  apply Hsm1_in_c0; intuition.
                + intuition.
                + apply elem_of_union.
                  right.
                  destruct Hdif as [Hdif _].
                  apply latest_message_from_compares in Hdif.
                  apply HdownSetCorrect. 
                  intuition.
                + destruct Hdif as [Hdif _].
                  apply latest_message_sender in Hdif.
                  intuition.
                + apply Hncomp.
              - specialize (index_set_listing {[ v ]}).
                unfold subseteq. unfold set_subseteq_instance.
                intros Htemp'. specialize (Htemp' v).
                apply Htemp'.
                apply elem_of_singleton. reflexivity.
            }
            
            unfold Au. unfold A.
            apply elem_of_union.
            right.
            apply elem_of_intersection.
            split.
            - intuition.
            - unfold divergent_last_messages.
              apply elem_of_map.
              exists vdif.
              split;[intuition|].
              apply elem_of_filter.
              rewrite <- Is_true_iff_eq_true.
              rewrite negb_true_iff.
              rewrite bool_decide_eq_false.
              intuition.
          } 
          
          
         assert (Hnequiv_u_u' : forall v,  ~v ∈ equivocators_from_message u -> ~ v ∈ equivocators_from_message u'). {
          destruct Hu_u' as [Hu_u'|Hu_u'].
          - intros v Hv.
            intros contra.
            rewrite <- equivocators_from_equiv in  Hv.
            specialize (is_equivocating_from_message_hb u' u v Hu_u') as Hb.
            spec Hb. clear -contra. set_solver.
            intuition.
          - subst u'. intuition.
         }
          
         assert (HAu'_Au : forall v, v ∈ Au' -> (v ∈ Au \/ v ∈ extra_voters)). {
            intros v Hv_Au'.
            rewrite HeqAu' in Hv_Au'. unfold A in Hv_Au'.
            apply elem_of_union in Hv_Au'.
            destruct Hv_Au' as [Hv|Hv].
            - left. unfold Au. unfold A.
              apply elem_of_union. left.
              unfold equivocators_from_message in Hv.
              unfold equivocators_from_message.
              specialize (filter_subprop ((λ i1 : index, bool_decide (is_equivocating_from_message u' i1)))) as Hsubpr.
              specialize (Hsubpr ((λ i1 : index, bool_decide (is_equivocating_from_message u i1))) _ _ index_set).
              spec Hsubpr. {
                intros k.
                rewrite !bool_decide_spec.
                destruct Hu_u' as [Hu_u'|Hu_u'].
                + apply is_equivocating_from_message_hb.
                  intuition.
                + intuition congruence.
              }
              clear -Hv Hsubpr.
              set_solver.
            - apply elem_of_intersection in Hv.
              destruct (@decide (v ∈ senders (divergent_last_messages u (Some value)))).
              apply elem_of_dec_slow.
              + left. unfold Au. unfold A.
                apply elem_of_union. right.
                apply elem_of_intersection.
                split;[|intuition].
                destruct Hv as [Hv _].
                specialize (equivocators_from_set_subset (c1 ∪ downSet u') (c0 ∪ downSet u)) as Hsub.
                spec Hsub. {
                  subst c0.
                  apply elem_of_subseteq. intros m Hm.
                  apply elem_of_union in Hm.
                  apply elem_of_union.
                  destruct Hm as [Hm|Hm].
                  - left. intuition.
                  - right. 
                    rewrite <- HdownSetCorrect.
                    rewrite <- HdownSetCorrect in Hm.
                    destruct Hu_u' as [Hu_u'|Hu_u'].
                    + apply t_trans with (y := u'); intuition.
                    + subst u'. intuition.
                }
                specialize (Hsub v).
                apply Hsub; intuition.
              + destruct (@decide (v ∈ equivocators_from_message u)).
                apply elem_of_dec_slow.
                * left. unfold Au. unfold A. 
                  apply elem_of_union. left.
                  intuition.
                * assert (Hnequiv_u' : ~ v ∈ equivocators_from_message u') by (apply Hnequiv_u_u'; intuition). 
                
                  assert (Hv_latest : v ∈ senders (latest_messages u)). {
                    destruct Hv as [_ Hv].
                    apply elem_of_map in Hv.
                    destruct Hv as [m_temp Hm_temp].
                    apply latest_message_some with (m' := m_temp).
                    apply equivocators_from_equiv.
                    intuition.
                    split;[|intuition congruence].
                    destruct Hm_temp as [_ Hm_temp].
                    apply elem_of_filter in Hm_temp.
                    destruct Hm_temp as [_ Hm_temp].
                    apply latest_message_sender_info in Hm_temp.
                    destruct Hm_temp as [_ Hm_temp].
                    apply latest_message_from_compares in Hm_temp.
                    apply HdownSetCorrect.
                    destruct Hu_u' as [Hu_u'|Hu_u'].
                    + apply t_trans with (y := u'); intuition.
                    + subst u'. intuition.
                  }
                  
                  assert (Hv_con : v ∈ senders (concurrent_last_messages u (Some value))). {
                    apply elem_of_map in Hv_latest.
                    destruct Hv_latest as [v_latest_u [Hv_latest_sender Hv_latest]].
                    apply elem_of_map.
                    exists v_latest_u.
                    split;[intuition|].
                    apply elem_of_filter.
                    rewrite bool_decide_spec.
                    split;[|intuition].
                    destruct (@decide (vote v_latest_u = Some value)).
                    apply decide_eq.
                    - intuition.
                    - contradict n0.
                      apply elem_of_map.
                      exists v_latest_u.
                      split;[intuition|].
                      apply elem_of_filter.
                      split;[|intuition].
                      rewrite <- Is_true_iff_eq_true.
                      rewrite negb_true_iff.
                      rewrite bool_decide_eq_false.
                      intuition.
                  }
                  
                  assert (Hv_nVk : v ∉ Vk_1). {
                    destruct (@decide (v ∈ Vk_1)).
                    apply elem_of_dec_slow.
                    - specialize (Hinvk2 v e) as Hv_Vk.
                      destruct Hv_Vk as [v' [Hsender_v' Hv']].
                      destruct Hv as [Hv Hv_latest'].
                      specialize (is_equivocating_from_set_union c1 (downSet u') v) as Heach.
                      spec Heach. {
                        apply Hinvk4; intuition.
                      }
                      spec Heach. {
                        rewrite <- equivocators_from_equiv in Hnequiv_u'.
                        intuition.
                      }
                      spec Heach. {
                        apply elem_of_filter in Hv.
                        rewrite bool_decide_spec in Hv. 
                        intuition.
                      }
                      
                      destruct Heach as [witness_c1 [witness_u' Hcomp]].
                      assert (Htemp2 : happens_before' witness_u' u') by (apply HdownSetCorrect;intuition).
                      apply elem_of_map in Hv_latest'.
                      destruct Hv_latest' as [latest_v_u' Hlatest_v_u'].
                      destruct Hlatest_v_u' as [Hlatest_v_u'_sender Hlatest_v_u'].
                      
                      assert (Hlatest_v_u'_u' : happens_before' latest_v_u' u'). {
                        apply latest_message_from_compares with (i := v).
                        apply elem_of_filter in Hlatest_v_u'.
                        destruct Hlatest_v_u' as [_ Hlatest_v_u'].
                        apply latest_message_sender_info in Hlatest_v_u'.
                        intuition congruence.
                      }
                      
                      assert (Hlatest_v_u'_vote : vote latest_v_u' <> Some value). {
                        apply elem_of_filter in Hlatest_v_u'.
                        rewrite <- Is_true_iff_eq_true in Hlatest_v_u'.
                        rewrite negb_true_iff in Hlatest_v_u'.
                        rewrite bool_decide_eq_false in Hlatest_v_u'.
                        intuition.
                      }
                      
                      assert (Hlatest_witness : equivocating_pair latest_v_u' witness_c1 v). {
                        destruct (decide (latest_v_u' = witness_u')).
                        - subst witness_u'. clear -Hcomp. firstorder.
                        - specialize (lift_equivocating_pair witness_u' witness_c1 latest_v_u' v) as Hlift.
                          spec Hlift. {
                            clear -Hcomp. firstorder.
                          }
                      
                        spec Hlift. {
                          apply compare_messages1 with (u := u').
                          intuition congruence.
                          apply elem_of_filter in Hlatest_v_u'. all : intuition.
                        }
                      
                        spec Hlift. intuition.
                        
                        spec Hlift. {
                          intros contra.
                          apply is_equivocating_from_message_hb with (m2 := u') in contra.
                          rewrite <- equivocators_from_equiv in Hnequiv_u'.
                          intuition.
                          intuition.
                        }
                        intuition.
                     }  
                      
                      assert (Hv_equiv_u : v ∈ equivocators_from_message u). {
                        apply elem_of_filter.
                        rewrite bool_decide_spec.
                        split;[|apply index_set_one].
                        
                        assert (Hcomp_v'_wc1 : comparable happens_before' v' witness_c1). {
                          apply (Hcomp_in_c1 v' witness_c1).
                          split.
                          - apply Hsm2_in_c0; intuition.
                          - split;intuition congruence.
                        }
                        
                        destruct Hcomp_v'_wc1 as [Hcomp'|Hcomp'].
                        - exists v', latest_v_u'.
                          subst v'.
                          split.
                          + destruct Hv' as [_ Hv']. apply HdownSetCorrect;intuition.
                          + split;[intuition congruence|].
                            split.
                            * apply HdownSetCorrect.
                              destruct Hu_u' as [Hu_u'|Hu_u'].
                              -- apply t_trans with (y := u'); intuition.
                              -- subst u. intuition.
                            * split;[intuition congruence|].
                              clear -Hlatest_witness. firstorder.
                        - destruct Hcomp' as [Hcomp'|Hcomp'].
                          + assert (Hcompv' : ~ comparable happens_before' v' latest_v_u'). {
                              intros contra.
                              destruct contra as [contra|contra].
                              - subst latest_v_u'.
                                intuition.
                              - destruct contra as [contra|contra].
                                + move Hmin_u' at bottom.
                                  specialize (Hmin_u' latest_v_u').
                                  spec Hmin_u'. {
                                    split.
                                    - left. 
                                      destruct Hu_u' as [Hu_u'|Hu_u'].
                                      + apply t_trans with (y := u'); intuition.
                                      + subst u'. intuition.
                                    - split.
                                      + apply protocol_state_closed with (u := u'); intuition.
                                      + split;[intuition|].
                                        exists v'.
                                        rewrite <- !HdownSetCorrect.
                                        intuition.
                                  }
                                  intuition.
                                + assert (happens_before' latest_v_u' witness_c1) by (apply t_trans with (y := v'); intuition).
                                  unfold equivocating_pair in Hlatest_witness.
                                  destruct Hlatest_witness as [_ [_ Hlatest_witness]].
                                  contradict Hlatest_witness.
                                  right. left. intuition.
                            }
                            exists v', latest_v_u'.
                            rewrite <- !HdownSetCorrect.
                            split;[intuition|].
                            split;[intuition|].
                            split.
                            * destruct Hu_u' as [Hu_u'|Hu_u'].
                              ++ apply t_trans with (y := u'); intuition.
                              ++ subst u'. intuition.
                            * intuition.
                          + exists witness_c1, latest_v_u'.
                            rewrite <- !HdownSetCorrect.
                            split.
                            * apply t_trans with (y := v'); intuition.
                            * split;[intuition|].
                              split.
                              -- destruct Hu_u' as [Hu_u'|Hu_u'].
                                  ++ apply t_trans with (y := u'); intuition.
                                  ++ subst u'. intuition.
                              -- split;[intuition|].
                                 clear -Hlatest_witness. firstorder.
                      }
                      intuition.
                    - intuition.
                  }
                  right.
                  rewrite Heqextra_voters.
                  apply elem_of_difference.
                  rewrite Heqvalue_voters.
                  split;assumption.
         }
         
         assert (HAu'_Vchange_disjoint : Au' ## Vchange). {
            destruct (elements (Au' ∩ Vchange)) as [|v rem] eqn : eq_elem.
            - apply elements_empty' in eq_elem.
              apply disjoint_intersection; intuition.
            - exfalso.
              assert (Hv: v ∈ (Au' ∩ Vchange)). {
               apply elem_of_elements.
               rewrite eq_elem.
               apply elem_of_list_In. left. intuition.
              }
              
              apply elem_of_intersection in Hv.
              destruct Hv as [Hv_Au' Hv_Vchange].
              move Hin_vchange at bottom.
              specialize (Hin_vchange v Hv_Vchange).
              destruct Hin_vchange as [Hnequiv_vu Hvchange_v].
              rewrite HeqAu' in Hv_Au'.
              unfold A in Hv_Au'.
              apply elem_of_union in Hv_Au'.
              destruct Hv_Au' as [Hv_Au'|Hv_Au'].
              + rewrite equivocators_from_equiv in Hnequiv_vu.
                specialize (Hnequiv_u_u' v Hnequiv_vu).
                intuition.
              + apply elem_of_intersection in Hv_Au'.
                destruct Hv_Au' as [Hequiv_c1_u' Hv_divergent].
                specialize (Hinvk2 v) as Hv_wit.
                spec Hv_wit. {
                  rewrite HeqVchange in Hv_Vchange.
                  apply elem_of_intersection in Hv_Vchange.
                  intuition.
                }
                destruct Hv_wit as [v' [Hv'_sender [Hv'_sm2 Hv'_u]]].
                
                apply elem_of_map in Hv_divergent.
                destruct Hv_divergent as [latest_v_u' [Hlatest_v_u'_sender Hv_divergent]].
                
                apply elem_of_filter in Hv_divergent.
                rewrite <- Is_true_iff_eq_true in Hv_divergent.
                rewrite negb_true_iff in Hv_divergent.
                rewrite bool_decide_eq_false in Hv_divergent.
                destruct Hv_divergent as [Hlatest_v_u'_vote Hlatest_v_u'_latest].
                apply latest_message_sender_info in Hlatest_v_u'_latest.
                
                assert (Hlatest_v_u'_u' : happens_before' latest_v_u' u'). {
                  apply latest_message_from_compares with (i := v).
                  subst v. intuition.
                }
                
                assert (Hv'_comp : comparable happens_before' latest_v_u' v'). {
                  destruct (decide (comparable happens_before' latest_v_u' v')).
                  - intuition.
                  - contradict Hnequiv_vu.
                    exists latest_v_u', v'.
                    rewrite <- !HdownSetCorrect.
                    split.
                    + destruct Hu_u'.
                      * apply t_trans with (y := u'); intuition.
                      * subst u'. intuition.
                    + split;[intuition|].
                      split; intuition.
                }
                
                destruct Hv'_comp as [Hv'_comp|Hv'_comp].
                * assert (vote v' = Some value). {
                    apply Hc0_vote.
                    apply Hsm2_in_c0; intuition.
                  }
                  intuition congruence.
                * destruct Hv'_comp as [Hv'_comp|Hv'_comp].
                  -- apply elem_of_filter in Hequiv_c1_u'.
                     rewrite bool_decide_spec in Hequiv_c1_u'.
                     destruct Hequiv_c1_u' as [Hequiv _].
                     apply is_equivocating_from_set_union in Hequiv.
                     destruct Hequiv as [witness_c1 [witness_u' Hcomp]].
                     destruct Hcomp as [Hwitness_c1 [Hwitness_u' [Hc1_sender [Hu'_sender Hcomp]]]].
                     
                     assert (Hwitness_small : witness_u' = latest_v_u' \/ happens_before' witness_u' latest_v_u'). {
                        destruct (decide (witness_u' = latest_v_u')).
                        - left. intuition.
                        - right. apply compare_messages1 with (u := u').
                          intuition congruence.
                          apply latest_message_in_latest_messages.
                          intuition congruence.
                          intuition congruence.
                          intuition.
                          rewrite <- HdownSetCorrect in Hwitness_u'. intuition.
                     }
                     
                     assert (Hwitness_in_downset_c1 : witness_u' ∈ relSet). {
                        rewrite HrelSet.
                        apply elem_of_union_list.
                        exists (downSet' v').
                        split.
                        - apply elem_of_list_In.
                          apply in_map_iff.
                          exists v'.
                          split;[intuition|].
                          apply elem_of_list_In.
                          apply elem_of_elements.
                          apply Hsm2_in_c0; intuition.
                        - unfold downSet'.
                          apply elem_of_union. left.
                          rewrite <- HdownSetCorrect.
                          destruct Hwitness_small.
                          + subst witness_u'.
                            intuition.
                          + apply t_trans with (y := latest_v_u'); intuition.
                     }
                     
                     assert (Hwitness_c1_in_downsetc1 : witness_c1 ∈ relSet). {
                      rewrite HrelSet.
                      apply set_downSet'_self.
                      intuition.
                     }
                     
                     contradict Hc0_honest.
                     unfold honesty.
                     intros contra.
                     specialize (contra v).
                     spec contra. apply elem_of_map. exists v'. split;[intuition|].
                     apply Hsm2_in_c0; intuition.
                     
                     contradict contra.
                     apply elem_of_filter.
                     rewrite bool_decide_spec.
                     split;[|apply index_set_one].
                     
                     exists witness_c1, witness_u'.
                     split;[intuition|].
                     split;[intuition|].
                     split;[intuition|].
                     split;[intuition|].
                     intuition.
                     
                     apply Hinvk4.
                     rewrite HeqVchange in Hv_Vchange. apply elem_of_intersection in Hv_Vchange. intuition.
                     destruct Hlatest_v_u'_latest as [Hneed _].
                     unfold is_equivocating_from_message in Hneed.
                     intuition congruence.
                  -- move Hmin_u' at bottom.
                     specialize (Hmin_u' latest_v_u').
                     spec Hmin_u'. {
                        split.
                        - left. 
                          destruct Hu_u' as [Hu_u'|Hu_u'].
                          + apply t_trans with (y := u'); intuition.
                          + subst u'. intuition.
                          - split.
                            + apply protocol_state_closed with (u := u'); intuition.
                            + split;[intuition|].
                              exists v'.
                              rewrite <- !HdownSetCorrect.
                              intuition.
                     }
                    intuition.
         }
         
         assert (HAu_size : size Au >= size (Au' ∪ Veq) + size Vchange - size extra_voters). {
           assert (Hunion : Z.of_nat (size (Au' ∪ Veq ∪ Vchange)) = size (Au' ∪ Veq) + size Vchange). {
             specialize (size_union (Au' ∪ Veq) Vchange) as Hsize_union.
             spec Hsize_union. {
               apply disjoint_union_l.
               intuition.
             }
             lia.
           }
           
           rewrite <- Hunion.
           
           assert (Hdif : ((Au' ∪ Veq ∪ Vchange) ∖ extra_voters) ⊆ Au). {
             apply elem_of_subseteq. intros v Hv.
             apply elem_of_difference in Hv.
             destruct Hv as [Hv Hv_extra].
             apply elem_of_union in Hv.
             rewrite elem_of_union in Hv at 1.
             destruct Hv as [Hv|Hv].
             - destruct Hv as [Hv|Hv].
               + specialize (HAu'_Au v Hv).
                 destruct HAu'_Au as [HAu'_Au|HAu'_Au]; intuition.
               + apply elem_of_subseteq with (X0 := Veq); set_solver.  
             - apply elem_of_subseteq with (X0 := Vchange); intuition.
           }
           
           assert (size ((Au' ∪ Veq ∪ Vchange) ∖ extra_voters) <= size Au). { 
              specialize (subseteq_size ((Au' ∪ Veq ∪ Vchange) ∖ extra_voters) Au Hdif).
              lia.
           }
           
           assert (Hdif_size : size ((Au' ∪ Veq ∪ Vchange) ∖ extra_voters) >= size (Au' ∪ Veq ∪ Vchange) - size extra_voters). {
              specialize (StdppFinSetExtras.difference_size_ge_disjoint_case (Au' ∪ Veq ∪ Vchange) extra_voters).
              lia.
           }
          lia.
         }
         
         assert (HAu_size': size Au * 2 ^ k0  >= (size (Au' ∪ Veq) + size Vchange - size extra_voters) * 2 ^ k0). {
          assert (size Au >= 0 /\ 2 ^ k0 >= 0). {
            split.
            - destruct (elements Au) eqn : eq_Au.
              + apply elements_empty' in eq_Au. lia.
              + lia.
            - unfold Z.pow.
              destruct (Z.of_nat k0) eqn : eq_k0.
              + lia.
              + specialize (Zpower_pos_pos 2 p). lia.
              + lia.
          }
          nia.
         }
         lia.
    Qed.
      
End Inspector.
End FullNodeLike.