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

From stdpp Require Import base fin_sets.

Section FullNodeLike.

Context
  {CV : consensus_values}
  {CV_eq_dec : Classes.EqDecision C}
  {Cm Ci : Type}
  {message : Type}
  {index : Type}
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
  (n := length index_listing)
  {Hfinite : Listing index_listing}
  {idec : Classes.EqDecision index}
  {i0 : Classes.Inhabited index}
  (sender : message -> index)
  {IM : index -> VLSM message}
  (computable_sent : forall (i : index), computable_sent_messages (IM i))
  (computable_received : forall (i : index), computable_received_messages (IM i)). 
  
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
      simpl in Hm'. set_solver.
    - remember (@min_predecessors _ happens_before' happens_before'_dec (m0 :: dP) dP m0) as m_min.
      assert (Hmin_inf : In m_min (m0 :: dP)). {
        specialize (@min_predecessors_in _ happens_before' happens_before'_dec (m0 :: dP) dP m0) as Hin'.
        destruct Hin' as [Hin'|Hin'].
        + rewrite Heqm_min. rewrite Hin'. set_solver.
        + rewrite Heqm_min. set_solver.
      }
      
      assert (Hmin : m_min ∈ d /\ P m_min). {
        rewrite eq_dP in Hmin_inf.
        rewrite HeqdP in Hmin_inf.
        destruct Hmin_inf as [Hmin_f|Hmin_f].
        + rewrite Hmin_f in HeqdP.
          assert (Hmin : m_min ∈ set_filter (λ m1 : message, bool_decide (P m1)) _ d). {
            unfold set_filter.
            rewrite <- HeqdP.
            intuition set_solver.
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
            rewrite elem_of_list_In.
            simpl. right.
            unfold set_filter in Hm'.
            apply elem_of_list_to_set in Hm'.
            apply elem_of_list_In.
            set_solver.
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
  
  Local Instance is_equivocating_from_set_dec : RelDecision is_equivocating_from_set.
  Proof.
  Admitted.
  
  Definition index_set : Ci := (list_to_set index_listing).
  
  Remark index_set_listing
    (ci : Ci) :
    ci ⊆ index_set.
  Proof.
    intros i Hi.
    apply elem_of_list_to_set.
    apply elem_of_list_In.
    apply Hfinite.
  Qed.
  
  Definition equivocators_from_set 
    (sm : Cm) :=
    set_filter (fun i => bool_decide (is_equivocating_from_set sm i)) _ index_set.
  
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
  Admitted.
  
  Definition equivocators_from_message
    (m : message) : Ci := 
    set_filter (fun (i : index) => (bool_decide (is_equivocating_from_message m i))) _ index_set.
  
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
    apply something_pretentious.
    apply Forall_forall. intuition.
    destruct Hsome as [mi Hmi].
    
    destruct (elements (messages_from m i)) eqn : eq.
    - apply elements_empty' in eq.
      set_solver.
    - intuition congruence.
  Qed. 
  
  Definition latest_messages
    (m : message) : Cm :=
  list_to_set (ListExtras.cat_option (List.map (latest_message_from m) (elements (honest_validators_from_message m)))).
  
  Lemma latest_message_in_latest_messages
    (m m' : message)
    (Hlatest : latest_message_from m (sender m') = Some m') 
    (Hne : ~ is_equivocating_from_message m (sender m')) :
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
       rewrite <- Is_true_iff_eq_true in Hlatest.
       rewrite bool_decide_eq_true in Hlatest.
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
      split;[apply HdownSetCorrect;intuition|].
      split;[intuition|].
      split;[apply HdownSetCorrect;intuition|].
      split;[symmetry;intuition|intuition].
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
      intros a b Hab.
      destruct Hab as [Hina Hinb].
      rewrite <- elem_of_list_In in Hina, Hinb.
      rewrite elem_of_elements in Hina, Hinb.
      apply elem_of_filter in Hina.
      apply elem_of_filter in Hinb.
      rewrite <- Is_true_iff_eq_true in Hina, Hinb.
      rewrite bool_decide_eq_true in Hina, Hinb.
      apply non_equiv_compare with (u := u).
      intuition congruence.
      rewrite <- HdownSetCorrect in Hina, Hinb.
      intuition.
      intuition congruence.
      apply elem_of_list_In.
      apply elem_of_elements.
      apply elem_of_filter.
      rewrite <- HdownSetCorrect.
      rewrite <- Is_true_iff_eq_true.
      rewrite bool_decide_eq_true.
      intuition.
  Qed. 
 
Section Inspector.

Context
    (X := composite_vlsm IM fullnode_constraint)
    (vote : message -> option C)
    (Hvote : forall (m : message) (oc : option C),
             vote m = oc ->
             (forall (oc' : option C),
             List.count_occ decide_eq (List.map vote (elements (latest_messages m))) oc >= 
             List.count_occ decide_eq (List.map vote (elements (latest_messages m))) oc')). 
   
    Definition count_votes_for
      (m : message)
      (oc : option C) :=
    List.count_occ decide_eq (List.map vote (elements (latest_messages m))) oc.
    
    Check downSet'.
    
    Definition set_downSet'
      (cm : Cm) : Cm := ⋃ List.map downSet' (elements cm). 
    
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
    Admitted.
    
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
    
    Inductive valid_com_prop : vstate X -> C -> nat -> list Cm -> Prop :=
    | valid_com_base 
      (s : vstate X)
      (value : C)
      (q : nat)
      (sm : Cm)
      (H : unanimity value sm /\ honesty s sm /\ convexity sm) : valid_com_prop s value q [sm]
    | valid_com_ind 
        (s : vstate X)
        (value : C)
        (q : nat)
        (sm1 sm2 : Cm) 
        (l : list Cm)
        (Hincl : sm1 ⊆ sm2)
        (Hdensity : density sm1 sm2 q)
        (Hconv : convexity sm1)
        (Hgood : valid_com_prop s value q (sm2 :: l)) : valid_com_prop s value q (sm1 :: (sm2 :: l)).
    
    Definition committee : Type := {
      comskel : committee_skeleton | valid_com_prop (com_state comskel) (value comskel) (q comskel) (com comskel)
    }.
    
    Lemma committee_info
      (vcom : committee)
      (skel := proj1_sig vcom) :
      exists (base : Cm), (
        get_base skel = Some base /\
        convexity base /\
        unanimity (value skel) base /\
        forall (c : Cm), In c (com skel) -> c ⊆ base).
    Proof.
      destruct vcom as [vcom Hvcom].
      simpl in skel.
      
      remember (com_state vcom) as com_state'.
      remember (value vcom) as com_value'.
      remember (q vcom) as com_q.
      remember (com vcom) as com_com.
      
      generalize dependent vcom.
      
      induction Hvcom.
      - exists sm.
        unfold get_base.
        rewrite <- Heqcom_com.
        simpl.
        split;[intuition|].
        intuition set_solver.
      - remember (@Build_committee_skeleton s value0 (sm2 :: l) q0) as new_skel.
        specialize (IHHvcom new_skel).
        subst new_skel.
        spec IHHvcom. intuition.
        spec IHHvcom. intuition.
        spec IHHvcom. intuition.
        spec IHHvcom. intuition.
        intros.
        destruct IHHvcom as [base IHHvcom].
        exists base.
        subst skel.
        unfold get_base.
        rewrite <- Heqcom_com.
        split.
        + destruct IHHvcom as [IHH _].
          unfold get_base in IHH.
          rewrite <- IHH.
          simpl. f_equal.
          destruct l.
          * intuition.
          * rewrite !unroll_last.
            intuition.
        + split;[intuition|].
          destruct IHHvcom as [_ [_ IHHvcom]].
          simpl in IHHvcom.
          split;[rewrite <- Heqcom_value';intuition|].
          intros c Hc.
          simpl in IHHvcom.
          simpl in Hc.
          destruct IHHvcom as [_ IHHvcom].
          destruct Hc as [Hc|Hc].
          * subst c. 
            specialize (IHHvcom sm2).
            spec IHHvcom. intuition.
            set_solver.
          * destruct Hc as [Hc|Hc].
            -- specialize (IHHvcom sm2).
               spec IHHvcom. intuition.
               subst c. intuition.
            -- specialize (IHHvcom c).
               spec IHHvcom. intuition.
               intuition.
    Qed.
    
    Local Open Scope Z_scope.
    
    (* Local Coercion Z_of_nat : nat >-> Z. *)
    
    Theorem main
      (s : vstate X)
      (Hpr : protocol_state_prop X s)
      (sigma := composite_observed s)
      (Com : committee)
      (skel := proj1_sig Com)
      (q := (q skel))
      (k := (k skel))
      (value := (value skel))
      (base top : Cm)
      (Hbase : get_base skel = Some base)
      (Htop : get_top skel = Some top)
      (Hstate : com_state skel = s)
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
      (Au := A u (Some value) sigma) :
      (size Au) * (2 ^ k) >=  
      (2 * q - n) * (2 ^ k - 1).
    Proof.
      assert (Com' := Com).
      destruct Com as [skel' Hcom]. simpl in *.
      subst skel.
      simpl in *.
      remember (com_state skel') as com_state'.
      remember (Inspector.value skel') as value'.
      remember (Inspector.q skel') as q'.
      remember (com skel') as com'.
    
      generalize dependent fake_u.
      generalize dependent u.
      generalize dependent base.
      generalize dependent top.
      generalize dependent skel'.
      
      specialize (committee_info Com') as Hcom_info.
      
      destruct Hcom_info as [base Hcom_info].
        destruct Hcom_info as [_ Hcom_info].
        assert (Hbase_vote : forall m, m ∈ base -> vote m = Some value). {
          intros m Hm.
          destruct Hcom_info as [_ [Hcom_info _]].
          simpl in Hcom_info.
          unfold unanimity in Hcom_info.
          specialize (Hcom_info m).
          
        }

      induction Hcom.
      - intros.
        simpl in *.
        unfold k0. unfold Inspector.k.
        rewrite <- Heqcom'. simpl. lia.
      - intros.
        specialize (committee_info Com') as Hcom_info.
        
        unfold Pdown in Hu_P.
        destruct Hu_P as [_ Hu_P].
        apply and_assoc in Hu_P.
        
        destruct Hu_P as [Hu_P Huc].
        destruct Huc as [uk Huk].
        
        assert (Huk_u : forall m', happens_before' m' uk -> happens_before' m' u). {
          intros.
          apply t_trans with (y := uk).
          intuition.
          destruct Huk as [Huk _].
          apply HdownSetCorrect in Huk.
          intuition.
        }
        
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
          rewrite <- Is_true_iff_eq_true.
          rewrite bool_decide_eq_true.
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
          rewrite <- Is_true_iff_eq_true in Hinmi.
          rewrite bool_decide_eq_true in Hinmi.
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
            rewrite <- !Is_true_iff_eq_true.
            rewrite !bool_decide_eq_true.
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
        
        (* remember (set_filter (fun i => bool_decide (is_equivocating_from_message u i)) _ Vk_1) as Veq. *)
        remember (set_filter (fun i => bool_decide (is_equivocating_from_message u i)) _ Vk_1) as Veq.
        remember (divergent_last_messages u (Some value)) as latest_divergent.
        remember ((senders latest_divergent) ∩ Vk_1) as Vchange.
        
        assert (Hin_veq1 : forall i, i ∈ Veq -> is_equivocating_from_message u i). {
          intros i Hi. rewrite HeqVeq in Hi.
          apply elem_of_filter in Hi.
          rewrite <- Is_true_iff_eq_true in Hi.
          rewrite bool_decide_eq_true in Hi. intuition.
        }
        
        assert (Hin_veq2 : forall i, i ∈ Vk_1 /\ i ∉ Veq -> ~ is_equivocating_from_message u i). {
          intros i Hi. rewrite HeqVeq in Hi.
          intros contra.
          destruct Hi as [Hini Hi].
          contradict Hi; apply elem_of_filter; rewrite <- Is_true_iff_eq_true; rewrite bool_decide_eq_true; intuition.
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
        remember (Vk_1 ∖ (Veq ∪ Vchange)) as value_voters.
        
        assert (Hvoters_size1 : (size value_voters + size Veq + size Vchange = size Vk_1)). {
          rewrite Heqvalue_voters.
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
             intuition set_solver.
             intuition.
          }
          rewrite <- Hveq2 in Hinv.
          lia.
        }
        
        assert (Hineq1 : 2 * (q - (size Veq) - (size Vchange)) <= n - size Eu). {
          move Hvote at bottom.
          assert (Hvote' := Hvote).
          
          assert (~ 2 * (q - (size Veq) - (size Vchange)) > n - size Eu). {
            intros contra.
            destruct Hu_P as [_ Hu_P].
            contradict Hu_P.
           
            remember (count_votes_for u (Some value)) as votes_for_value.
            assert (Hvotes_for : votes_for_value >= (q - size Veq - size Vchange)). {
                assert (Hvotes_for' : votes_for_value >= size value_voters). {
                   rewrite Heqvotes_for_value.
                   admit.
                }
                lia.
            }
            
            specialize (Hvote' u (vote u) eq_refl (Some value)).
            rewrite Heqvotes_for_value in Hvotes_for.
                assert (count_votes_for u (Some value) + count_votes_for u (vote u) <= n - size Eu). {
                  admit.
                }
                unfold count_votes_for in *.
                clear- Hvotes_for H13 contra Hvote'.
                admit.
            }
            intuition.
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
        
        assert (Hineq3 : 2 * q <= n + size Veq + 2 * (size Vchange)) by lia.
        
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
                admit.
                intuition.
              }
              apply HdownSetCorrect.
              intuition.
          }
          
          move IHHcom at bottom.
          specialize (IHHcom Hstate).
    
          remember (@Build_committee_skeleton s value (sm2 :: l) q) as new_skel.
          specialize (IHHcom new_skel).
          rewrite Heqnew_skel in IHHcom. simpl in IHHcom.
          spec IHHcom. intuition congruence.
          spec IHHcom. intuition congruence.
          spec IHHcom. intuition congruence.
          specialize (IHHcom eq_refl).
          specialize (IHHcom sm2). unfold get_top in IHHcom. simpl in IHHcom.
          specialize (IHHcom eq_refl).
          specialize (IHHcom base).
          
          spec IHHcom. {
            move Hbase at bottom.
            unfold get_base in Hbase.
            rewrite <- Heqcom' in Hbase.
            unfold get_base. simpl.
            simpl in Hbase.
            destruct l.
            * intuition.
            * rewrite unroll_last.
              rewrite unroll_last in Hbase.
              intuition.
          }
          
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
            - intros.
              specialize (Hmin_u'2 m').
              intuition.
          }
          
          unfold k in IHHcom. simpl in IHHcom.
          
          remember (A u' (Some value) sigma) as Au'.
          
          assert (Hineq2main : (size (Au' ∪ Veq) + size Vchange) * 2 ^ k0 >= (2 * q0 - n) * (2 ^ k0 - 1)). {
            specialize (union_size_ge_average Au' Veq) as Havg.
            
            assert (Hineq_temp1 : 2 * (size (Au' ∪ Veq) + size Vchange) >= size Au' + size Veq + 2 * size Vchange) by lia.
            
            move Hineq1 at bottom.
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
            assert (2 * q0 - n <= size Veq + 2 * size Vchange) by lia.
            clear Hineq3.
            remember (2 ^ length l) as p2.
            cut ((size (Au' ∪ Veq) + size Vchange) * (2 * p2) >= (2 * q0 - n) * (2 * p2) - (2 * q0 - n)). {
              lia.
            }
            rewrite Zmult_assoc.
            rewrite Zmult_plus_distr_l.
            replace (size (Au' ∪ Veq) * 2) with (2 * size (Au' ∪ Veq)) by lia.
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
          
          rewrite HeqPdown' in Hmin_u'.
          unfold is_minimal_wrt_P in Hmin_u'.
          destruct Hmin_u' as [Hu' Hmin_u'].
          
          destruct Hu' as [Hu_u' Hu'].
          
          assert (HAu'_sub_Au : Au' ⊆ Au). {
            intros v Hv.
            rewrite HeqAu' in Hv.
            unfold Au.
            unfold A in Hv. unfold A.
            apply elem_of_union in Hv.
            destruct Hv as [Hv|Hv].
            - apply elem_of_union.
              left.
              unfold equivocators_from_message in Hv.
              unfold equivocators_from_message.
              specialize (filter_subprop ((λ i1 : index, bool_decide (is_equivocating_from_message u' i1)))) as Hsubpr.
              specialize (Hsubpr ((λ i1 : index, bool_decide (is_equivocating_from_message u i1))) _ _ index_set).
              spec Hsubpr. {
                intros j.
                rewrite <- !Is_true_iff_eq_true.
                rewrite !bool_decide_eq_true.
                destruct Hu_u' as [Hu_u'|Hu_u'].
                + apply is_equivocating_from_message_hb.
                  intuition.
                + intuition congruence.
              }
              clear -Hv Hsubpr.
              set_solver.
            - apply elem_of_union.
              right.
              apply elem_of_intersection in Hv.
              apply elem_of_intersection.
              admit.
          }
          
          
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
            
            assert (Hvtemp: v ∈ Vk_1). {
              rewrite HeqVchange in Hv.
              apply elem_of_intersection in Hv; intuition.
            }
            
            move Hinvk2 at bottom.
            specialize (Hinvk2 v Hvtemp).
            destruct Hinvk2 as [vk1 Hvk1].
            
           assert (Hvk1_vote : vote vk1 = Some value). {
            admit.
           }
            
           assert (Hvdif_vk1 : happens_before' vk1 vdif). {
            apply compare_messages1 with (u := u).
              intuition congruence.
              apply latest_message_in_latest_messages.
              replace (sender vdif) with v by intuition; intuition.
              replace (sender vdif) with v by intuition.
              intuition.
              intuition congruence.
              intuition.
           }
            
            move Hinvk3 at bottom.
            specialize (Hinvk3 v Hvtemp).
            destruct Hinvk3 as [vk Hvk].
            
            assert (Hvk_vote : vote vk = Some value). {
              assert (vk ∈ base) by admit.
              admit.
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
                    split.
                    - left.
                      destruct Hutemp.
                      + apply t_trans with (y := u); intuition.
                      + subst fake_u. assumption.
                    - split.
                      + apply protocol_state_closed with (u := u); intuition.
                      + split;[intuition|].
                        exists vk.
                        split.
                        * apply HdownSetCorrect. assumption.
                        * rewrite Htop_sm1. intuition.  
                  }
                  intuition.
                +
              admit.
            }
            
            assert (v ∈ equivocators_from_set (base ∪ downSet u)). {
              unfold equivocators_from_set.
              apply elem_of_filter.
              rewrite <- Is_true_iff_eq_true. rewrite bool_decide_eq_true.
              split.
              - unfold is_equivocating_from_set.
                exists vk. exists vdif.
                split.
                + apply elem_of_union. 
                  left.
                  admit.
                + split;[intuition|].
                  split.
                  * apply elem_of_union.
                    right.
                    destruct Hdif as [Hdif _].
                    apply latest_message_from_compares in Hdif.
                    apply HdownSetCorrect. 
                    intuition.
                  * destruct Hdif as [Hdif _].
                    apply latest_message_sender in Hdif.
                    split;[intuition|].
                    apply Hncomp.
                    
              - specialize (index_set_listing {[ v ]}).
                unfold subseteq. unfold set_subseteq_instance.
                intros Htemp. specialize (Htemp v).
                apply Htemp.
                apply elem_of_singleton. reflexivity.
            } 
           
            admit.
          } 
    Admitted.
      
End Inspector.
End FullNodeLike.