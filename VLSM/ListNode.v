Require Import Bool List Streams Logic.Epsilon Logic.Decidable Reals ProofIrrelevance Fin FinFun OrdersFacts Wellfounded. 
Require Import Lia.
Import ListNotations.
From CasperCBC
Require Import Lib.Preamble Lib.ListExtras Lib.ListSetExtras Lib.RealsExtras CBC.Definitions CBC.Common VLSM.Common VLSM.Composition VLSM.Decisions VLSM.Equivocation CBC.FullNode.

Section ListNode.

(** 

*** Minimal List Validator Protocol 

We introduce here the "minimal list validator protocol", by quoting the official 
documentation: 

In this section, we propose a protocol where each validator keeps a list of states of other validators. Each validator broadcasts its view of the other validators’
states. We claim that the protocol is nontrivial and safe: when equivocations are limited, it is possible to reach either outcome, and if the protocol reaches
a decision, all the validators agree on what it is.

**) 

(** Our context includes a finite [index] type with decidable equality and an instance of it, [index_self] which
    designates the chosen index of the current machine **)

Context 
  {index : Type}
  {index_self : index}
  {index_listing : list index}
  {Hfinite : Listing index_listing}
  {dec : EqDec index}
  {temp_dec : EqDec (option bool)}.

(** Each state contains a binary value and a list of all the states of the other validators. **)

Inductive state : Type := 
| Bottom
| Something
  : forall (b : bool) (is : indexed_state index_listing),
  state
with indexed_state : list index -> Type :=
| Empty
  : indexed_state []
| Append
  : forall (v : index) (l : list index)
      (s : state) (is : indexed_state l),
  indexed_state (v :: l)
.


Fixpoint depth (s : state) : nat :=
  match s with
  | Bottom => 0
  | Something cv ls => depth_indexed index_listing ls + 1
  end
  with depth_indexed (l : list index) (ls : indexed_state l) : nat :=
  match ls with
  | Empty => 0
  | Append v l' s' is' => max (depth s') (depth_indexed l' is') 
  end.

(** Some utility functions. **)

Fixpoint project_indexed
  (l : list index)
  (is : indexed_state l)
  (v : index)
  : state
  :=
  match is with
  | Empty =>
    Bottom
  | Append v' l' s is' =>
    if eq_dec v' v
    then s
    else project_indexed l' is' v
  end.
  
Definition project
  (s : state)
  (v : index)
  : state
  :=
  match s with 
  | Bottom => Bottom
  | Something b is => project_indexed index_listing is v
  end.

Fixpoint update_indexed 
  (l : list index)
  (is : indexed_state l) 
  (v : index) 
  (new_s : state)
  : indexed_state l
  :=
  match is with
  | Empty => Empty
  | Append v' l' s is' =>
    if eq_dec v' v
    then Append v' l' new_s is'
    else Append v' l' s (update_indexed l' is' v new_s)
  end.

Lemma update_indexed_eq
  (l : list index)
  (is : indexed_state l)
  (i : index)
  (news : state)
  (Heq : project_indexed l is i = news) :
  (update_indexed l is i news = is).
Proof.
  induction is.
  - simpl. 
    reflexivity.
  - simpl.
    destruct (eq_dec v i) eqn : eq.
    + assert (Hsame : s = news). {
        simpl in Heq.
        rewrite eq in Heq.
        assumption.
      }
      rewrite Hsame.
      reflexivity.
    + 
      assert (Hstep : project_indexed (v :: l) (Append v l s is) i = project_indexed l is i). {
        unfold project_indexed.
        rewrite eq.
        simpl.
        reflexivity.
      }
      
      assert (update_indexed l is i news = is). {
        apply IHis.
        rewrite Hstep in Heq.
        assumption.
      }
      
      rewrite H.
      reflexivity.
Qed.

Lemma in_fast
  (l : list index)
  (a : index)
  (b : index)
  (Hin : In a (b :: l))
  (Hneq : b <> a) :
  In a l.
Proof.
  destruct Hin.
  - subst. elim Hneq. reflexivity.
  - assumption.
Qed.

Lemma update_indexed_same
  (l : list index)
  (is : indexed_state l)
  (i : index)
  (j : index)
  (Heq : i = j)
  (Hin : In i l)
  (news : state) :
  project_indexed l (update_indexed l is i news) j = news.
Proof.
  induction is.
  - unfold In in Hin. 
    exfalso. 
    assumption.
  - simpl. 
    destruct (eq_dec v i) eqn : dec_eq; simpl; rewrite <- Heq; rewrite dec_eq; 
    simpl.
    + reflexivity.
    + assert (Hin' : In i l). {
        apply (in_fast l i v Hin n).
      }
      rewrite Heq in IHis.
      rewrite Heq.
      apply IHis.
      rewrite <- Heq.
      assumption.
Qed.

Lemma update_indexed_different
  (l : list index)
  (is : indexed_state l)
  (i : index)
  (j : index)
  (Heq : i <> j)
  (Hin : In i l /\ In j l)
  (news : state) :
  project_indexed l (update_indexed l is i news) j = project_indexed l is j.
Proof.
  induction is.
  - simpl. 
    reflexivity.
  - simpl.
    destruct (eq_dec v i).
    + simpl.
      destruct (eq_dec v j).
      * rewrite e in e0. subst. elim Heq. reflexivity.
      * reflexivity.
    + simpl.
      destruct (eq_dec v j).
      * reflexivity.
      * apply IHis.
        destruct Hin.
        split.
        apply (in_fast l i v H n).
        apply (in_fast l j v H0 n0).
Qed.

Lemma update_indexed_idempotent
  (l : list index)
  (is : indexed_state l)
  (i : index)
  (Hin : In i l)
  (news : state) :
  update_indexed l (update_indexed l is i news) i news = update_indexed l is i news.

Proof.
  induction is.
  - simpl. reflexivity.
  - simpl.
    destruct (eq_dec v i) eqn : eq.
    + simpl. rewrite eq. reflexivity.
    + simpl. rewrite eq. 
      assert (update_indexed l (update_indexed l is i news) i news = update_indexed l is i news). {
        apply IHis.
        apply (in_fast l i v Hin n).
      }
      rewrite H. reflexivity. 
Qed.

Fixpoint all_bottom_f (l : list index) : indexed_state l :=
  match l with
  | [] => Empty
  | (h :: t) => Append h t Bottom (all_bottom_f t)
  end.
  
Definition all_bottom := all_bottom_f index_listing.

Definition update_consensus (big : state) (value : bool) :=
  match big with
  | Bottom => Bottom
  | Something cv f => Something value f
  end.

Definition update_state (big : state) (news : state) (i : index) : state :=
  match big with
  | Bottom => Bottom
  | Something cv f => Something cv (update_indexed index_listing f i news)
  end.

(* update_consensus doesn't touch state *)
Lemma update_consensus_clean
  (s : state)
  (i : index)
  (value : bool) :
  project s i = project (update_consensus s value) i.

Proof.
  unfold update_consensus.
  destruct s.
  - simpl. reflexivity.
  - unfold project. reflexivity.
Qed.

Lemma project_same
  (s : state)
  (news : state)
  (i : index)
  (Hnot_bottom : s <> Bottom) :
  project (update_state s news i) i = news.
Proof.
  unfold project.
  destruct s.
  - elim Hnot_bottom. reflexivity.
  - simpl. apply update_indexed_same.
    + reflexivity.
    + apply ((proj2 Hfinite) i).
Qed.

Lemma project_different
  (s : state)
  (news : state)
  (i j : index)
  (Hdif : i <> j)
  (Hnot_bottom : s <> Bottom) :
  project (update_state s news j) i = project s i.

Proof.
  unfold project.
  destruct s.
  - intuition.
  - unfold update_state.
    rewrite update_indexed_different.
    intuition.
    intuition.
    split. 
    apply ((proj2 Hfinite) j).
    apply ((proj2 Hfinite) i).
Qed.

Lemma update_state_eq
      (big : state)
      (news : state)
      (i : index)
      (Hin : In i index_listing)
      (Heq : project big i = news)
      : update_state big news i = big.

Proof.
  intros.
  unfold update_state.
  destruct big.
  -reflexivity.
  - assert (Heqis : (update_indexed index_listing is i news) = is). {
      apply update_indexed_eq.
      unfold project in Heq.
      inversion Heq.
      reflexivity.
    }
    rewrite Heqis.
    reflexivity.
Qed.

Lemma update_state_idempotent 
      (big : state)
      (news : state)
      (i : index)
      : update_state (update_state big news i) news i = update_state big news i.
Proof.
  unfold update_state.
  destruct big.
  - reflexivity.
  - specialize update_indexed_idempotent.
    intros.
    rewrite H.
    reflexivity.
    apply (proj2 Hfinite i).
Qed.

Fixpoint get_all_states
  (l : list index)
  (is : indexed_state l)
  : list state.
  intros.
  destruct is eqn:is_eqn.
  - exact [].
  - exact (s :: get_all_states l i).
  Defined.


(** Our only initial state will be Bottom. **)

Definition state00 := Bottom.

Definition initial_state_prop (s : state) : Prop := 
  exists (cv : bool),
  (s = Something cv all_bottom).

Lemma bottom_good : initial_state_prop (Something false all_bottom).
  Proof.
    unfold initial_state_prop.
    exists false.
    reflexivity.
  Qed.

Definition state0 : {s | initial_state_prop s} := 
  exist _ (Something false all_bottom) bottom_good.

(** Messages are pairs of indices and states.
    There are no initial messages.
    The type is trivially inhabitated by
    the pair of [index_self] and Bottom]. **)

Definition message : Type := (index * state).

Definition initial_message_prop (m : message) : Prop := False.

Definition message00 := (index_self, state00).

(** The decision function extracts the consensus value
    from a state. It is possible that a state is undecided.
    We choose to encode this by making consensus values
    options of bool. In this way [None] signifies the 
    absence of decision. **)

Definition decision (s : state) : option bool :=
  match s with
  | Bottom => None
  | Something c some => Some c
  end.

(** Get a list of everyone's decisions from the view
    of a given state **)

Definition global_decisions (s : state) : list (option bool) :=
  match s with
  | Bottom => []
  | Something c some => List.map decision (get_all_states index_listing some)
  end.

(** The value of the estimator is defined as the mode of all decisions,
    where possible decisions are <0>, <1> or <{0, 1}> (no decision).
    We choose to define the estimator as a relation between state and bool.
    If the mode value is a decisive one, the estimator will only relate
    to the chosen value, otherwise it will relate to both values.
    
    Currently, ties resolve generously (everyone equal to the mode is
    taken into account).
**)

Definition estimator (s : state) (b : bool) : Prop :=
  let none_count := List.count_occ temp_dec (global_decisions s) None in
  let our_count := List.count_occ temp_dec (global_decisions s) (Some b) in
  let other_count := List.count_occ temp_dec (global_decisions s) (Some (negb b)) in
  match s with 
  | Bottom => True
  | Something c some => (none_count >= our_count /\ none_count >= other_count) \/ our_count >= other_count
  end.

(** Labels describe the type of transitions: either updates (with boolean values) or receiving of messages. **)

Inductive label_list : Type :=
| update (c : bool)
| receive.

(** Transitions:
    - Update <c> => updates the state at [index_self] with a new state which
                    contains <c> as a consensus value. A message is emitted to broadcast
                    this update: it contains the machine's index and its _previous state_.
    - Receive => Updates the view of global states with new information
                 about the node which sent the received message.
                 No message is emitted.
**)

Definition transition (l : label_list) (som : state * option message) : state * option message :=
  let (s, om) := som in
     match l with
     | update c => ((update_consensus (update_state s s index_self) c), Some (index_self, s)) 
     | receive => match om with 
                  | Some m => ((update_state s (snd m) (fst m)), None)
                  | None => (s, None)
                  end
     end.

(** Validity:
    - Update <c> => <c> must be in the estimator of the given state.
    - Receive => A message must be received, sent by a _different_ node.
                 The sender's state in his own state list
                 should match our view of it in our state list. **)

Definition valid
  (l : label_list)
  (som : state * option message)
  := 
  let (s, om) := som in
  match l with
  | update c => estimator s c /\ om = None
  | receive => match om with 
               | None => False
               | Some m => project s (fst m) = project (snd m) (fst m) /\ (snd m) <> Bottom /\ index_self <> (fst m)
               end
    end.

(** Finally, we are ready to instantiate the protocol as a VLSM **)

Instance VLSM_list_protocol : VLSM_type message :=
  { state := state
  ; label := label_list
  }.
    
Instance LSM_list : VLSM_sign VLSM_list_protocol :=
  { initial_state_prop := initial_state_prop
  ; initial_message_prop := initial_message_prop
  ; s0 := state0
  ; m0 := message00
  ; l0 := receive
  }.

Instance VLSM_list : VLSM LSM_list :=
  { transition := transition
    ; valid := valid
  }.


End ListNode.

Section Equivocation.

Context 
  {index : Type}
  {index_self : index}
  {index_listing : list index}
  {Hfinite : Listing index_listing}
  {idec : EqDec index}
  {temp_dec : EqDec (option bool)}
  (X := @VLSM_list _ index_self index_listing idec temp_dec)
  (preX := pre_loaded_vlsm X)
  (Xtype := type preX)
  {sdec : EqDec (@state index index_listing)}.
  
  Definition last_recorded (l : list index) (ls : indexed_state l) (who : index) : state :=
    @project_indexed _ index_listing _ l ls who.
    
  Fixpoint rec_history (s : state) (who : index) (d : nat) : list state :=
    match s, d with
    | Bottom, _ => []
    | _, 0 => []
    | (Something cv ls), (S d') => s :: rec_history (last_recorded index_listing ls who) who d'
    end.
    
  Definition get_history (s : state) (who : index) : list state :=
     match s with
     | Bottom => []
     | Something cv ls => let child := last_recorded index_listing ls who in
                          rec_history child who (depth child)
    end.
    
  Definition state_eqb (s1 s2 : state) : bool :=
    match sdec s1 s2 with
    | left _ => true
    | right _ => false
    end.
    
  Lemma state_eqb_eq (s1 s2 : state) :
    (state_eqb s1 s2) = true <-> s1 = s2.
  
  Proof.
    unfold state_eqb.
    split.
    - destruct (sdec s1 s2).
      + intuition.
      + intros. discriminate H.
    - intros.
      destruct (sdec s1 s2).
      + intuition.
      + intuition.
  Qed.
  
  Lemma state_eqb_neq (s1 s2 : state) :
    (state_eqb s1 s2) = false <-> s1 <> s2.
  
  Proof.
    unfold state_eqb.
    split.
    - destruct (sdec s1 s2).
      + intuition.
      + intuition.
    - destruct (sdec s1 s2).
      + intuition.
      + intuition.
  Qed.
    
  Definition send_oracle (who : index) (s : state) (m : message)  : bool :=
    let who := fst m in
    let what := snd m in
    match idec who index_self with
    | right _ => false
    | left _ => match s with
                | Bottom => false
                | Something cv ls => existsb (state_eqb what) (get_history s who)
                end
    end.
    
  Definition receive_oracle (who : index) (s : state) (m : message) : bool :=
    let who := fst m in
    let what := snd m in
    match idec who index_self with
    | left _ => false
    | right _ => existsb (state_eqb what) (get_history s who)
    end.
    
    Lemma protocol_no_bottom 
      (s : protocol_state preX) :
      (proj1_sig s) <> Bottom.
    
    Proof.
      destruct s.
      simpl.
      destruct p.
      remember (x, x0) as gigi.
      generalize dependent x0.
      generalize dependent x.
      induction H.
      - intros.
        simpl in *.
        destruct is.
        simpl in *.
        unfold initial_state_prop in i.
        destruct i.
        unfold s.
        inversion Heqgigi.
        subst.
        discriminate.
      - intros.
        simpl in *.
        unfold s.
        inversion Heqgigi.
        unfold s.
        discriminate.
      - destruct l eqn : eq.
        + intros.
          simpl in *.
          inversion Heqgigi.
          unfold update_consensus.
          unfold update_state.
          assert (dif : s <> Bottom). {
            apply IHprotocol_prop1 with (x0 := _om).
            reflexivity.
          }
          destruct s.
          * assumption.
          * simpl in *.
            discriminate.
         + intros.
           simpl in *.
           assert (dif : s <> Bottom). {
            apply IHprotocol_prop1 with (x0 := _om).
            reflexivity.
          }
          destruct om.
          inversion Heqgigi.
          * unfold update_state.
            destruct s.
            assumption.
            discriminate.
          * inversion Heqgigi.
            destruct s.
            elim dif.
            reflexivity.
            rewrite <- H2.
            discriminate.
    Qed.
    
    Lemma protocol_prop_no_bottom :
      forall (s : state)
             (Hprotocol_prop : protocol_state_prop preX s),
             s <> Bottom.
    Proof.
      intros.
      remember (exist _ s Hprotocol_prop) as protocol_s.
      assert (s = proj1_sig protocol_s). 
        - inversion Heqprotocol_s. simpl. reflexivity.
        - rewrite H. apply protocol_no_bottom.
    Qed.

    Lemma output_gets_recordedd :
      forall (l : label)
             (s1 s2 : state)
             (m1 : option message)
             (m2 : message)
             (som1 := (s1, m1))
             (som2 := (s2, Some m2))
             (Hprotocol : protocol_transition preX l som1 som2),
             project s2 index_self = snd m2.
    Proof.
      intros.
      unfold protocol_transition in Hprotocol.
      destruct Hprotocol as [pr_valid_prop transition_prop].
      unfold protocol_valid in pr_valid_prop.
      simpl in *.
      unfold transition in transition_prop.
      destruct l eqn : l_eq.
      - unfold som2 in transition_prop.
        inversion transition_prop. 
        simpl.
        assert (project (update_consensus (update_state s1 s1 index_self) c) index_self
                = project (update_state s1 s1 index_self) index_self). {
                  symmetry.
                  apply (@update_consensus_clean index index_listing _ _).
                }
       rewrite H.
       Check @project_same index index_listing Hfinite.
       apply (@project_same index index_listing Hfinite _ _).
       apply protocol_prop_no_bottom.
       destruct pr_valid_prop.
       assumption.
       - destruct m1 eqn : m1_eq.
         + inversion transition_prop.
         + inversion transition_prop.
    Qed.
    
    Lemma input_gets_recorded :
      forall (l : label)
             (s1 s2 : state)
             (m1 : message)
             (m2 : option message)
             (i : index)
             (som1 := (s1, Some m1))
             (som2 := (s2, m2))
             (Hmi : fst m1 = i)
             (Hnot_self : i <> index_self)
             (Hprotocol : protocol_transition preX l som1 som2),
             project s2 i = snd m1.
    Proof.
      intros.
      unfold protocol_transition in Hprotocol.
      destruct Hprotocol as [pr_valid_prop transition_prop].
      unfold protocol_valid in pr_valid_prop.
      simpl in *.
      unfold transition in transition_prop.
      unfold som2 in transition_prop.
      destruct l eqn : l_eq.
      - inversion transition_prop.
        rewrite <- Hmi in Hnot_self.
        elim Hnot_self.
        destruct pr_valid_prop as [_ [_ [_ Hno_input]]].
        discriminate Hno_input.
       - inversion transition_prop.
         rewrite Hmi.
         rewrite @project_same.
         reflexivity.
         exact Hfinite.
         apply protocol_prop_no_bottom.
         destruct pr_valid_prop as [Hprotocol Hothers].
         assumption. 
    Qed.
     
     (* begin hide *)
    Lemma depth_parent_child_indexed
      (indices : list index)
      (i : index)
      (Hi : In i indices)
      (ls : indexed_state indices)
      : depth_indexed indices ls >= @depth _ index_listing (project_indexed indices ls i).
    Proof.
      generalize dependent indices.
      induction ls.
      - auto.
      - simpl.
        destruct (eq_dec v i) eqn : Heqdec.
        + unfold depth_indexed. unfold depth. lia.
        + pose (in_fast l i v Hi n) as Hi'.
          specialize (IHls Hi').
          unfold depth_indexed in *. unfold depth in *. lia.
    Qed.
          

    Lemma depth_parent_child :
      forall (ls : indexed_state index_listing)
         (cv : bool)
         (i : index),
         depth (Something cv ls) >= S (depth (project_indexed index_listing ls i)).
    
      Proof.
        intros.
        specialize depth_parent_child_indexed.
        intros.
        specialize (H index_listing i ((proj2 Hfinite) i) ls).
        unfold depth at 1.
        unfold depth_indexed in H.
        lia.
   Qed.

    Lemma depth_redundancy :
      forall (s : state)
             (i : index)
             (d : nat)
             (Hbig : d >= depth s),
        rec_history s i d = rec_history s i (depth s).
    Proof.
      intros.
      remember (depth s) as dpth.
      generalize dependent s. generalize dependent d.
      induction dpth using (well_founded_induction lt_wf); intros.
      destruct s. 
      - simpl. unfold rec_history.
         destruct d; destruct dpth; reflexivity.
      - destruct dpth.
        + unfold depth in Heqdpth. lia.
        + destruct d. 
          * lia.
          * simpl. f_equal.
            {
              unfold last_recorded.
              pose (depth (project_indexed index_listing is i)) as dlst.
              pose (depth_parent_child is b i) as Hdlst.
              apply eq_trans with (rec_history (project_indexed index_listing is i) i dlst).
              - 
                apply H; lia.
              - symmetry. apply H; lia.
            }
    Qed.
    
    Lemma history_oblivious:
      forall (s : state)
             (news : state)
             (i : index)
             (j : index)
             (Hdif : j <> i),
             get_history s i = get_history (update_state s news j) i.
    
    Proof.
      intros.
      unfold get_history.
      destruct s.
      - simpl. reflexivity.
      - simpl. 
        assert ((last_recorded index_listing is i) = 
                (last_recorded index_listing (update_indexed index_listing is j news) i)). {
                  unfold last_recorded.
                  symmetry.
                  apply update_indexed_different.
                  assumption.
                  split.
                  apply ((proj2 Hfinite) j).
                  apply ((proj2 Hfinite) i).
                }
        rewrite H.
        reflexivity.
    Qed.
    
    Lemma history_disregards_cv :
        forall (s : state)
               (cv : bool)
               (i : index),
          get_history (update_consensus s cv) i = get_history s i.
    
    Proof.
      intros.
      unfold update_consensus.
      destruct s.
      - reflexivity.
      - reflexivity.
    Qed.
    
    Lemma history_append :
      forall (s : state)
             (news : state)
             (Hno_bottom_s : s <> Bottom)
             (Hno_bottom_news : news <> Bottom)
             (i : index)
             (Hvalidity : project news i = project s i),
             get_history (update_state s news i) i = (news :: get_history s i).
    Proof.
      intros.
      unfold update_state.
      destruct s eqn : s_eq.
      - elim Hno_bottom_s. reflexivity.
      - unfold get_history.
        unfold last_recorded.
        
        assert ((project_indexed index_listing (update_indexed index_listing is i news) i) =
                 news). {
          apply update_indexed_same.
          reflexivity.
          apply ((proj2 Hfinite) i).
        }
        
        rewrite H.
        destruct news eqn : news_eq.
        + elim Hno_bottom_news. reflexivity.
        + unfold rec_history at 1.
          simpl in *.
          
          assert ((depth (Something b0 is0)) >= (S (depth (project_indexed index_listing is i)))). {
            rewrite <- Hvalidity.
            apply depth_parent_child.
          }
          
          assert (exists x, depth (Something b0 is0) = S x /\ x >= depth (project_indexed index_listing is i)). {
            destruct (depth (Something b0 is0)).
            lia.
            exists n.
            split.
            reflexivity.
            lia.
          }

          specialize depth_redundancy.
          intros.
          destruct H1 as [x [Heqx Hineqx]].
          rewrite Heqx.
          unfold last_recorded.
          rewrite Hvalidity.
          assert (rec_history (project_indexed index_listing is i) i
                  x = 
                  rec_history (project_indexed index_listing is i) i
                  (depth (project_indexed index_listing is i))). {
                     apply H2.
                     assumption.
                  }
         rewrite <- H1.
         reflexivity.
    Qed.


    
    Lemma history_persists_transition:
      forall (s1 s2 s3 : state)
             (l : label)
             (om1 om2 : option message)
             (i : index)
             (Hprotocol: protocol_transition preX l (s1, om1) (s2, om2))
             (Hhas_1 : In s3 (get_history s1 i)),
             In s3 (get_history s2 i).
    
    Proof.
     intros.
     unfold protocol_transition in Hprotocol.
     destruct Hprotocol as [Hprotocol_valid Htransition].
     simpl in *.
     destruct l eqn : eq.
     - inversion Htransition.
       destruct (eq_dec index_self i).
       + specialize history_disregards_cv.
         intros.
         assert (get_history (update_consensus (update_state s1 s1 index_self) c) i
              = get_history (update_state s1 s1 index_self) i)  by apply history_disregards_cv.
        rewrite H2.
        assert ((get_history (update_state s1 s1 index_self) i)
                = (s1 :: get_history s1 i)). {
                rewrite e.
                apply history_append.
                apply protocol_prop_no_bottom.
                destruct Hprotocol_valid. assumption.
                apply protocol_prop_no_bottom.
                destruct Hprotocol_valid. assumption.
                reflexivity.
              }
        rewrite H3.
        unfold In.
        right.
        assumption.
      + assert (get_history (update_consensus (update_state s1 s1 index_self) c) i
                = get_history s1 i). {
                  assert (get_history (update_consensus (update_state s1 s1 index_self) c) i 
                          = get_history (update_state s1 s1 index_self) i). {
                            apply history_disregards_cv with (s := (update_state s1 s1 index_self)) (cv := c).
                          }
                  rewrite H.
                  symmetry.
                  apply history_oblivious.
                  assumption.
                }
        rewrite H.
        assumption.
     -  destruct om1.
        destruct (idec (fst m) i) eqn : dec_eq.
        + inversion Htransition.
          assert (get_history (update_state s1 (snd m) i) i
                   = (snd m) :: (get_history s1 i)). {
                      apply history_append.
                      apply protocol_prop_no_bottom.
                      destruct Hprotocol_valid.
                      assumption.
                      destruct Hprotocol_valid as [x [y [z [t u]]]].
                      assumption.
                      destruct Hprotocol_valid as [x [y [z t]]].
                      rewrite e in z.
                      symmetry.
                      assumption.
                   }
          rewrite e.
          rewrite H.
          unfold In.
          right.
          assumption.
        + inversion Htransition.
          assert (get_history (update_state s1 (snd m) (fst m)) i = get_history s1 i). {
            symmetry.
            apply history_oblivious.
            assumption.
          }
          rewrite H.
          assumption.
        + inversion Htransition.
          rewrite <- H0.
          assumption.
    Qed.
    
    Lemma history_persists_trace :
      forall (s1 s2 s3 : state)
             (i : index)
             (Hin : in_futures preX s1 s2),
             In s3 (get_history s1 i) -> In s3 (get_history s2 i).
             
    Proof.
      intros.
      unfold in_futures in Hin.
      destruct Hin.
      destruct H0.
      generalize dependent s1.
      induction x.
      - intros.
        simpl in *.
        rewrite <- H1.
        assumption.
      - intros.
        apply IHx with (s1 := destination a).
        + inversion H0.
          assumption.
        + assert (List.map destination (a :: x) = (destination a) :: (List.map destination x)). {
            apply map_cons.
          }
          rewrite H2 in H1.
          rewrite unroll_last in H1.
          assumption.
        + inversion H0.
          simpl. 
          apply history_persists_transition with (s1 := s1) (s2 := s) (l := l) (om1 := iom) (om2 := oom).
          assumption.
          assumption.
    Qed.
    
    (* TODO : remove duplication for infinite traces *)
    
    Lemma projection_in_history :
      forall (s : state)
             (news : state)
             (i : index)
             (Hnot_bottom : news <> Bottom)
             (Hproject : project s i = news),
             In news (get_history s i).
    
    Proof.
      intros.
      unfold get_history.
      unfold project in Hproject.
      destruct s eqn : eqs.
      - rewrite Hproject in Hnot_bottom. elim Hnot_bottom. reflexivity.
      - unfold last_recorded.
        rewrite Hproject.
        unfold rec_history.
        destruct news.
        + elim Hnot_bottom. reflexivity.
        + assert (exists x, depth (Something b0 is0) = S x). {
          exists (depth_indexed index_listing is0).
          unfold depth.
          unfold depth_indexed.
          lia.
        }
        
        destruct H.
        rewrite H.
        unfold In.
        left.
        reflexivity.
    Qed.
    
    Lemma message_gets_recorded :
      forall (s : (@state index index_listing))
             (s0 : state)
             (m : message)
             (tr : list transition_item)
             (last_item : transition_item) 
             (Hprotocol : finite_protocol_trace preX s0 (tr ++ [last_item]))
             (Hm: output last_item = Some m),
             project (destination (last_item)) index_self = snd m.
    Proof.
     intros.
    Admitted.
    
    (*
     intros.
     
     assert (smth : protocol_trace_prop preX (Finite (trace_first (proj1_sig tr)) (prefix ++ [last1]))). {
        apply trace_prefix_protocol.
        assumption.
     }
     
     destruct tr as [raw tr_prop].
     destruct raw as [s0 l0| s0 l0] eqn : eq.
     - destruct prefix as [|t l1] eqn : prefix_eq.
       + simpl in smth.
          unfold finite_protocol_trace in smth.
          destruct smth.
          
          assert (Hpr_tr : protocol_transition preX (l last1) (s0, (input last1)) ((destination last1), (output last1))). {
            apply first_transition_valid.
            assumption.
          }
          
          apply output_gets_recordedd with (l := l last1) (s1 := s0) (m1 := input last1).
          * simpl in *.
            destruct tr_prop.
            destruct H2.
            rewrite H2.
            discriminate.
          * rewrite <- Hm. 
            assumption.
       + simpl in *.
         assert (exists (tr1 : list transition_item)
                        (prev : transition_item),
                        (t :: l1 ++ [last1]) = tr1 ++ [prev;last1]). {
          destruct l1.
          * simpl. exists []. exists t. reflexivity.
          * specialize exists_last with (l := (t :: (t0 :: l1))).
            intros. 
            destruct X0 as [tr [a Heq]].
            discriminate.
            exists tr.
            exists a.
            simpl.
            assert (tr ++ [a;last1] = (tr ++ [a]) ++ [last1]). {
              rewrite <- app_assoc.
              simpl.
              reflexivity.
            }
            rewrite H.
            rewrite <-Heq.
            reflexivity.
         }
         
         destruct H as [tr1 [prev Hdecomp]].
         pose proof (@finite_ptrace_consecutive_valid_transition _ _ _ preX) as consecutive.
         
         assert (Hp_tr : protocol_transition preX (l last1) (destination prev, (input last1)) ((destination last1), (output last1))). {
            simpl in *.
            eapply consecutive with (te2 := last1) (te1 := prev); eauto.
            apply smth.
         }
         
         apply output_gets_recordedd with (l := l last1) (s1 := destination prev) (m1 := input last1).
         
         * assert(protocol_state_prop preX (destination prev)). {
            unfold protocol_transition in Hp_tr.
            destruct Hp_tr.
            destruct H.
            assumption.
         }
           remember (exist _ (destination prev) H) as protocol_prev.
           assert (destination prev = proj1_sig protocol_prev). {
              inversion protocol_prev.
              rewrite Heqprotocol_prev.
              simpl. reflexivity.
           }
           rewrite H0.
           apply protocol_no_bottom with (s := protocol_prev).
         * rewrite <- Hm.
           assumption.
      - destruct prefix as [|t l1] eqn : prefix_eq.
       + simpl in smth.
          unfold finite_protocol_trace in smth.
          destruct smth.
          
          assert (Hpr_tr : protocol_transition preX (l last1) (s0, (input last1)) ((destination last1), (output last1))). {
            apply first_transition_valid.
            assumption.
          }
          
          apply output_gets_recordedd with (l := l last1) (s1 := s0) (m1 := input last1).
          * simpl in *.
            destruct tr_prop.
            destruct H2.
            rewrite H2.
            discriminate.
          * rewrite <- Hm. 
            assumption.
       + simpl in *.
         assert (exists (tr1 : list transition_item)
                        (prev : transition_item),
                        (t :: l1 ++ [last1]) = tr1 ++ [prev;last1]). {
          destruct l1.
          * simpl. exists []. exists t. reflexivity.
          * specialize exists_last with (l := (t :: (t0 :: l1))).
            intros. 
            destruct X0 as [tr [a Heq]].
            discriminate.
            exists tr.
            exists a.
            simpl.
            assert (tr ++ [a;last1] = (tr ++ [a]) ++ [last1]). {
              rewrite <- app_assoc.
              simpl.
              reflexivity.
            }
            rewrite H.
            rewrite <-Heq.
            reflexivity.
         }
         
         destruct H as [tr1 [prev Hdecomp]].
         pose proof (@finite_ptrace_consecutive_valid_transition _ _ _ preX) as consecutive.
         
         assert (Hp_tr : protocol_transition preX (l last1) (destination prev, (input last1)) ((destination last1), (output last1))). {
            simpl in *.
            eapply consecutive with (te2 := last1) (te1 := prev); eauto.
            apply smth.
         }
         
         apply output_gets_recordedd with (l := l last1) (s1 := destination prev) (m1 := input last1).
         
         * assert(protocol_state_prop preX (destination prev)). {
            unfold protocol_transition in Hp_tr.
            destruct Hp_tr.
            destruct H.
            assumption.
         }
           remember (exist _ (destination prev) H) as protocol_prev.
           assert (destination prev = proj1_sig protocol_prev). {
              inversion protocol_prev.
              rewrite Heqprotocol_prev.
              simpl. reflexivity.
           }
           rewrite H0.
           apply protocol_no_bottom with (s := protocol_prev).
         * rewrite <- Hm.
           assumption.
    Qed.
    *)
    
    Lemma emitted_messages_only_from_self 
      (m : message)
      (Hemit : can_emit preX m) :
      (fst m) = index_self.
    Proof.
      unfold can_emit in Hemit.
      simpl in *.
      destruct Hemit as [som [l [s Htransition]]]. 
      simpl in *.
      inversion Htransition.
      simpl in *.
      unfold transition in H0.
      simpl in *.
      destruct l.
      - destruct som. inversion H0. simpl. reflexivity.
      - destruct som. destruct o; discriminate H0.
    Qed.
    
    Lemma emitted_not_bottom
      (m : message)
      (Hemit : can_emit preX m) :
      (snd m) <> Bottom.
    
    Proof.
      unfold can_emit in Hemit.
      destruct Hemit as [som [l [s Htransition]]].
      simpl in *.
      inversion Htransition.
      simpl in *.
      unfold transition in H0.
      destruct som.
      destruct H.
      destruct l eqn : eq_l.
      - simpl in *.
        inversion H0.
        simpl.
        apply protocol_prop_no_bottom.
        assumption.
      - destruct o; inversion H0.
    Qed.
    
    Lemma depth_zero_bottom
      (s : state)
      (Hzero : @depth index index_listing s = 0) :
      s = Bottom.
    
    Proof.
      unfold depth in Hzero.
      destruct s.
      - reflexivity.
      - lia.
    Qed.
    
    Lemma no_bottom_in_history
      (s s': state)
      (i : index) 
      (l : list state)
      (Heql : l = rec_history s i (depth s))
      (Hin : In s' l) :
      s' <> Bottom.
    Proof.
      generalize dependent s.
      generalize dependent s'.
      induction l.
      - intros. 
        simpl in *.
        intuition.
      - intros.
        destruct (sdec a s').
        + destruct s eqn : eq_s.
          * discriminate Heql.
          * unfold rec_history in Heql.
            simpl in *.
            assert (exists (n : nat), depth (Something b is) = n + 1). {
              exists (depth_indexed index_listing is).
              unfold depth.
              reflexivity.
            }
            
            destruct H as [n H].
            rewrite H in Heql.
            replace (n + 1) with (S n) in Heql.
            inversion Heql.            
            rewrite <- e.
            rewrite H1.
            intuition.
            discriminate H0.
            discriminate H0.
            lia.
        + simpl in Hin.
          destruct Hin.
          * elim n. 
            intuition.
          * unfold get_history in Heql.
            destruct s.
            discriminate Heql.
            unfold rec_history in Heql.
            simpl in *. 
            
            assert (exists (n : nat), depth (Something b is) = n + 1). {
              exists (depth_indexed index_listing is).
              unfold depth.
              reflexivity.
            }
            
            destruct H0 as [m H0].
            rewrite H0 in Heql.
            replace (m + 1) with (S m) in Heql.
            specialize (IHl s' H (last_recorded index_listing is i)).
            inversion Heql.
            
            assert (m >= depth (last_recorded index_listing is i)). {
               specialize (depth_parent_child is b i).
               intros.
               rewrite H0 in H1.
               unfold last_recorded.
               lia.
            }
            
            rewrite depth_redundancy in H3.
            specialize (IHl H3).
            assumption.
            assumption.
            lia.
    Qed.
    
    Lemma new_projection_implies_output_message
      (l : label)
      (som som' : (state * option message))
      (Hprotocol : protocol_transition preX l som som')
      (s' : state)
      (Hold : project (fst som) index_self <> s')
      (Hnew : project (fst som') index_self = s') :
      (snd som') = Some (index_self, s').
    Proof.
      remember Hprotocol as Horiginal.
      unfold protocol_transition in Hprotocol.
      destruct Hprotocol as [Hvalid Htransition].
      simpl in *.
      unfold protocol_valid in *.
      unfold transition in *.
      destruct l eqn: eq_l.
      - destruct som as [s1 om1].
        destruct som' as [s2 om2].
        simpl in *.
        inversion Htransition.
        rewrite <- H0 in Hnew.
        rewrite <- update_consensus_clean with (value := c) in Hnew .
        rewrite @project_same in Hnew.
        rewrite Hnew.
        reflexivity.
        exact Hfinite.
        apply protocol_prop_no_bottom.
        destruct Hvalid as [Hproto Hother].
        assumption.
      - destruct som.
        simpl in *.
        destruct o eqn : eq_o.
        + destruct som'.
          inversion Htransition.
          simpl in Hnew.
          rewrite <- H0 in Hnew.
          destruct (idec (fst m) (index_self)).
          * destruct Hvalid as [tmp1 [tmp2 [tmp3 [tmp4 Hneed]]]].
            elim Hneed.
            intuition.
          * rewrite @project_different in Hnew.
            elim Hold.
            intuition.
            exact Hfinite.
            intuition.
            apply protocol_prop_no_bottom.
            destruct Hvalid as [Hneed Hother].
            assumption.
        + destruct Hvalid as [tmp1 [tmp2 Hfalse]].
          exfalso.
          assumption.
    Qed.
    
    Lemma new_projection_implies_input_message
      (l : label)
      (som som' : (state * option message))
      (Hprotocol : protocol_transition preX l som som')
      (i : index)
      (Hnot_self : i <> index_self)
      (s' : state)
      (Hold : project (fst som) i <> s')
      (Hnew : project (fst som') i = s') :
      (snd som) = Some (i, s').
    Proof.
      remember Hprotocol as Horiginal.
      unfold protocol_transition in Hprotocol.
      destruct Hprotocol as [Hvalid Htransition].
      simpl in *.
      unfold protocol_valid in *.
      unfold transition in *.
      destruct l eqn: eq_l.
      - destruct som as [s1 om1].
        destruct som' as [s2 om2].
        simpl in *.
        inversion Htransition.
        rewrite <- H0 in Hnew.
        rewrite <- update_consensus_clean with (value := c) in Hnew .
        rewrite @project_different in Hnew.
        elim Hold.
        assumption.
        exact Hfinite.
        assumption.
        apply protocol_prop_no_bottom.
        destruct Hvalid as [Hneed Hother].
        assumption.
      - destruct som.
        simpl in *.
        destruct o eqn : eq_o.
        + destruct som'.
          inversion Htransition.
          simpl in Hnew.
          rewrite <- H0 in Hnew.
          destruct (idec (fst m) i).
          * rewrite e in Hnew.
            rewrite @project_same in Hnew.
            rewrite <- Hnew.
            rewrite <- e.
            rewrite <- surjective_pairing.
            reflexivity.
            exact Hfinite.
            apply protocol_prop_no_bottom.
            destruct Hvalid as [Hneed Hother].
            assumption.
          * rewrite @project_different in Hnew.
            elim Hold.
            intuition.
            exact Hfinite.
            intuition.
            apply protocol_prop_no_bottom.
            destruct Hvalid as [Hneed Hother].
            assumption.
        + destruct som'.
          destruct Hvalid as [temp1 [temp2 Hfalse]].
          exfalso.
          assumption.
    Qed.
    
    Lemma project_all_bottom_f
      (i : index)
      (l : list index) :
      @project_indexed _ index_listing _ l (all_bottom_f l) i = Bottom.
    
    Proof.
      induction l.
      - simpl. reflexivity.
      - simpl.
        destruct (eq_dec a i).
        + reflexivity.
        + assumption.
    Qed.
    
    Lemma project_all_bottom
      (i : index) :
      project_indexed index_listing all_bottom i = Bottom.
    
    Proof.
      apply project_all_bottom_f.
    Qed.
    
    Lemma some_project
      (s si target : state)
      (len : nat)
      (tr : list transition_item)
      (Hlen : length tr = len)
      (i : index)
      (Hprotocol_tr : finite_protocol_trace preX si tr)
      (Hlast : last (List.map destination tr) si = s)
      (Hin : In target (get_history s i)) :
      List.Exists (fun elem : (@transition_item _ (type preX)) => project (destination elem) i = target) tr.
    Proof.
    Admitted.
    (* 
      generalize dependent s.
      generalize dependent tr.
      induction len.
      - intros. 
        rewrite length_zero_iff_nil in Hlen.
        subst.
        simpl in *.
        inversion Hprotocol_tr.
        destruct H0.
        rewrite H0 in Hin.
        assert (get_history (Something x all_bottom) i = []). {
          unfold get_history.
          unfold last_recorded.
          rewrite project_all_bottom.
          simpl.
          reflexivity.
        }
        rewrite H1 in Hin.
        simpl in *.
        exfalso. 
        assumption.
      - intros.
        rewrite Exists_exists.
        assert (exists (tr' : list transition_item) (lst : transition_item), tr = tr' ++ [lst]). {
          destruct tr.
          - discriminate Hlen.
          - apply first_implies_last.
        }
        
        destruct H as [tr' [lst Hlst]].
        destruct (sdec (project s i) target) eqn : eq.
        + exists lst. 
          split.
          * rewrite Hlst. 
            apply in_or_app.
            right.
            intuition.
          * rewrite Hlst in Hlast.
            rewrite map_app in Hlast.
            rewrite last_app in Hlast.
            simpl in *.
            subst.
            reflexivity.
       + assert (Hlen' : length tr' = len). {
          rewrite Hlst in Hlen.
          rewrite app_length in Hlen.
          simpl in *.
          lia.
         }
         
         assert (Hprotocol' : finite_protocol_trace preX si tr'). {
           remember (@Finite _ (type preX) si tr) as trace.
           remember (exist _ trace Hprotocol_tr) as protocol_trace.
           destruct Hprotocol_tr.
           specialize (finite_protocol_trace_from_prefix preX si tr f (length tr - 1)).
           intros.
           
           assert (Hone_less: tr' = list_prefix tr (length tr - 1)). {
              rewrite Hlst.
              specialize (list_prefix_split tr tr' [lst] (length tr')).
              intros.
              intuition.
              rewrite <- H0 at 1.
              rewrite <- Hlst.
              assert (length tr' = length tr - 1). {
                lia.
              }
              intuition.
           }
           
           rewrite Hone_less.
           unfold finite_protocol_trace.
           intuition.
         }
         
         destruct tr' as [| h tl] eqn : eq'.
         * assert (s = destination lst). {
             rewrite Hlst in Hlast.
             simpl in Hlast.
             intuition.
           }
           
           assert (protocol_transition preX (l lst) (si, input lst) (destination lst, output lst)). {
              rewrite Hlst in Hprotocol_tr.
              simpl in *.
              destruct Hprotocol_tr.
              specialize (first_transition_valid preX si lst H0).
              intros.
              assumption.
           }
           
           remember H0 as Horiginal.
           unfold protocol_transition in H0.
           destruct H0 as [Hvalid Htransition].
           simpl in *.
           inversion Htransition.
           
           assert (Hempty : get_history si i = []). {
               unfold get_history.
               unfold last_recorded.
               destruct Hprotocol_tr.
               simpl in *.
               unfold initial_state_prop in H2.
               destruct H2 as [cv Heq_initial].
               rewrite Heq_initial.
               rewrite project_all_bottom.
               simpl.
               reflexivity.
           }
           
           destruct (l lst) eqn : eq_l. { 
              - inversion H1. 
                rewrite <- H in H2.
                rewrite <- H2 in Hin.
                rewrite history_disregards_cv in Hin.
                rewrite history_append in Hin.
                simpl in Hin.
                specialize (output_gets_recordedd (l lst) si (destination lst) (input lst) (index_self, si)).
                intros.
                assert (project (destination lst) index_self = snd (index_self, si)). {
                  replace (@Some (@message index index_listing)
                        (@pair index (@state index index_listing) index_self si)) with (output lst) in H0.
                  apply H0.
                  rewrite eq_l.
                  assumption.
                }
                simpl in *.
                assert (si <> target). {
                  rewrite <- H4.
                  rewrite <- H.
                  assumption.
                }
                
                intuition.
                rewrite Hempty in H6.
                simpl in H6.
                exfalso.
                assumption.
                apply protocol_prop_no_bottom. destruct Hvalid. assumption.
                apply protocol_prop_no_bottom. destruct Hvalid. assumption.
                reflexivity. 
           }
           { - destruct (input lst).
               + inversion Htransition.
                 rewrite H in Hin.
                 rewrite <- H2 in Hin.
                 Check history_oblivious.
                 rewrite <- (history_oblivious si (snd m) index_self (fst m)) in Hin.
                 rewrite Hempty in Hin.
                 simpl in Hin.
                 exfalso.
                 assumption.
                 destruct Hvalid as [a [b [c [d e]]]].
                 intuition.
               + destruct Hvalid as [a [b c]].
                 exfalso.
                 assumption.
         }

         * assert (exists (tr'' : list transition_item) (lst' : transition_item), tr' = tr'' ++ [lst']). {
              destruct tr'.
              - discriminate eq'.
              - apply first_implies_last.
           }
           destruct H as [tr'' [lst' Hlst']].
           rewrite <- eq' in Hlen'. 
           rewrite <- eq' in Hprotocol'.
           assert (Hlast'' : last (List.map destination tr') si = (destination lst')). {
              rewrite Hlst'.
              rewrite map_app.
              rewrite last_app.
              simpl.
              reflexivity.
           }
           
           specialize (IHlen tr' Hlen' Hprotocol' (destination lst') Hlast'').
           
           assert (Hin' : In target (get_history (destination lst') index_self)). {
              assert (protocol_transition preX (l lst) (destination lst', input lst) (destination lst, output lst)). {
                specialize (finite_ptrace_consecutive_valid_transition preX) as Hcons.
                simpl in *.
                specialize (Hcons si tr [] tr'' lst' lst).
                destruct Hprotocol_tr as [Hfrom Hinit].
                specialize (Hcons Hfrom).
                apply Hcons.
                simpl.
                rewrite <- app_cons.
                rewrite app_assoc.
                rewrite <- Hlst'.
                rewrite eq'.
                rewrite Hlst.
                reflexivity.
              }
              
              remember H as Hold.
              unfold protocol_transition in H.
              destruct H as [Hvalid Htransition].
              
              assert (s = destination lst). {
                rewrite Hlst in Hlast.
                rewrite map_app in Hlast.
                rewrite last_app in Hlast.
                simpl in Hlast.
                symmetry.
                assumption.
              }
              
              destruct (l lst) eqn : eq_l.
              - simpl in *.
                inversion Htransition.
                rewrite H in Hin.
                rewrite <- H1 in Hin.
                rewrite history_disregards_cv in Hin.
                rewrite history_append in Hin.
                specialize (output_gets_recordedd 
                            (update c)
                            (destination lst')
                            (destination lst)
                            (input lst)
                            (index_self, destination lst')).
               intros.
               replace (@Some (@message index index_listing)
                   (@pair index
                      (@Common.state (@message index index_listing)
                         (@VLSM_list_protocol index index_listing)) index_self
                      (@destination (@message index index_listing)
                         (@VLSM_list_protocol index index_listing) lst'))) with (output lst) in H0.
               specialize (H0 Hold).
               simpl in *.
               rewrite <- H in H0.
               
               inversion Hin.
               + rewrite H3 in H0. elim n. assumption.
               + assumption.
               + apply protocol_prop_no_bottom. destruct Hvalid. intuition.
               + apply protocol_prop_no_bottom. destruct Hvalid. intuition.
               + reflexivity.
             - simpl in *.
               inversion Htransition.
               destruct (input lst) eqn : input_eq. 
               + inversion H1.
                 rewrite <- H in H2.
                 rewrite <- H2 in Hin.
                 rewrite <- (history_oblivious (destination lst') (snd m) index_self (fst m)) in Hin.
                 assumption.
                 destruct Hvalid as [a [b [c [d e]]]].
                 intuition.
               + destruct Hvalid as [a [b c]].
                 exfalso.
                 assumption.
           }
           specialize (IHlen Hin').
           rewrite Exists_exists in IHlen.
           destruct IHlen as [x' [Hin_x Hproject_x]].
           exists x'.
           split.
           rewrite Hlst.
           rewrite <- eq'.
           intuition.
           assumption.
    Qed.
    *)
    
    
    (*
    Lemma some_project
      (s si target : state)
      (len : nat)
      (tr : list transition_item)
      (Hlen : length tr = len)
      (Hprotocol_tr : finite_protocol_trace preX si tr)
      (Hlast : last (List.map destination tr) si = s)
      (Hin : In target (get_history s index_self)) :
      List.Exists (fun elem : (@transition_item _ (type preX)) => project (destination elem) index_self = target) tr.
    Proof.
      generalize dependent s.
      generalize dependent tr.
      induction len.
      - intros. 
        rewrite length_zero_iff_nil in Hlen.
        subst.
        simpl in *.
        inversion Hprotocol_tr.
        destruct H0.
        rewrite H0 in Hin.
        assert (get_history (Something x all_bottom) index_self = []). {
          unfold get_history.
          unfold last_recorded.
          rewrite project_all_bottom.
          simpl.
          reflexivity.
        }
        rewrite H1 in Hin.
        simpl in *.
        exfalso. 
        assumption.
      - intros.
        rewrite Exists_exists.
        assert (exists (tr' : list transition_item) (lst : transition_item), tr = tr' ++ [lst]). {
          destruct tr.
          - discriminate Hlen.
          - apply first_implies_last.
        }
        
        destruct H as [tr' [lst Hlst]].
        destruct (sdec (project s index_self) target) eqn : eq.
        + exists lst. 
          split.
          * rewrite Hlst. 
            apply in_or_app.
            right.
            intuition.
          * rewrite Hlst in Hlast.
            rewrite map_app in Hlast.
            rewrite last_app in Hlast.
            simpl in *.
            subst.
            reflexivity.
       + assert (Hlen' : length tr' = len). {
          rewrite Hlst in Hlen.
          rewrite app_length in Hlen.
          simpl in *.
          lia.
         }
         
         assert (Hprotocol' : finite_protocol_trace preX si tr'). {
           remember (@Finite _ (type preX) si tr) as trace.
           remember (exist _ trace Hprotocol_tr) as protocol_trace.
           destruct Hprotocol_tr.
           specialize (finite_protocol_trace_from_prefix preX si tr f (length tr - 1)).
           intros.
           
           assert (Hone_less: tr' = list_prefix tr (length tr - 1)). {
              rewrite Hlst.
              specialize (list_prefix_split tr tr' [lst] (length tr')).
              intros.
              intuition.
              rewrite <- H0 at 1.
              rewrite <- Hlst.
              assert (length tr' = length tr - 1). {
                lia.
              }
              intuition.
           }
           
           rewrite Hone_less.
           unfold finite_protocol_trace.
           intuition.
         }
         
         destruct tr' as [| h tl] eqn : eq'.
         * assert (s = destination lst). {
             rewrite Hlst in Hlast.
             simpl in Hlast.
             intuition.
           }
           
           assert (protocol_transition preX (l lst) (si, input lst) (destination lst, output lst)). {
              rewrite Hlst in Hprotocol_tr.
              simpl in *.
              destruct Hprotocol_tr.
              specialize (first_transition_valid preX si lst H0).
              intros.
              assumption.
           }
           
           remember H0 as Horiginal.
           unfold protocol_transition in H0.
           destruct H0 as [Hvalid Htransition].
           simpl in *.
           inversion Htransition.
           
           assert (Hempty : get_history si index_self = []). {
               unfold get_history.
               unfold last_recorded.
               destruct Hprotocol_tr.
               simpl in *.
               unfold initial_state_prop in H2.
               destruct H2 as [cv Heq_initial].
               rewrite Heq_initial.
               rewrite project_all_bottom.
               simpl.
               reflexivity.
           }
           
           destruct (l lst) eqn : eq_l. { 
              - inversion H1. 
                rewrite <- H in H2.
                rewrite <- H2 in Hin.
                rewrite history_disregards_cv in Hin.
                rewrite history_append in Hin.
                simpl in Hin.
                specialize (output_gets_recordedd (l lst) si (destination lst) (input lst) (index_self, si)).
                intros.
                assert (project (destination lst) index_self = snd (index_self, si)). {
                  replace (@Some (@message index index_listing)
                        (@pair index (@state index index_listing) index_self si)) with (output lst) in H0.
                  apply H0.
                  rewrite eq_l.
                  assumption.
                }
                simpl in *.
                assert (si <> target). {
                  rewrite <- H4.
                  rewrite <- H.
                  assumption.
                }
                
                intuition.
                rewrite Hempty in H6.
                simpl in H6.
                exfalso.
                assumption.
                apply protocol_prop_no_bottom. destruct Hvalid. assumption.
                apply protocol_prop_no_bottom. destruct Hvalid. assumption.
                reflexivity. 
           }
           { - destruct (input lst).
               + inversion Htransition.
                 rewrite H in Hin.
                 rewrite <- H2 in Hin.
                 Check history_oblivious.
                 rewrite <- (history_oblivious si (snd m) index_self (fst m)) in Hin.
                 rewrite Hempty in Hin.
                 simpl in Hin.
                 exfalso.
                 assumption.
                 destruct Hvalid as [a [b [c [d e]]]].
                 intuition.
               + destruct Hvalid as [a [b c]].
                 exfalso.
                 assumption.
         }

         * assert (exists (tr'' : list transition_item) (lst' : transition_item), tr' = tr'' ++ [lst']). {
              destruct tr'.
              - discriminate eq'.
              - apply first_implies_last.
           }
           destruct H as [tr'' [lst' Hlst']].
           rewrite <- eq' in Hlen'. 
           rewrite <- eq' in Hprotocol'.
           assert (Hlast'' : last (List.map destination tr') si = (destination lst')). {
              rewrite Hlst'.
              rewrite map_app.
              rewrite last_app.
              simpl.
              reflexivity.
           }
           
           specialize (IHlen tr' Hlen' Hprotocol' (destination lst') Hlast'').
           
           assert (Hin' : In target (get_history (destination lst') index_self)). {
              assert (protocol_transition preX (l lst) (destination lst', input lst) (destination lst, output lst)). {
                specialize (finite_ptrace_consecutive_valid_transition preX) as Hcons.
                simpl in *.
                specialize (Hcons si tr [] tr'' lst' lst).
                destruct Hprotocol_tr as [Hfrom Hinit].
                specialize (Hcons Hfrom).
                apply Hcons.
                simpl.
                rewrite <- app_cons.
                rewrite app_assoc.
                rewrite <- Hlst'.
                rewrite eq'.
                rewrite Hlst.
                reflexivity.
              }
              
              remember H as Hold.
              unfold protocol_transition in H.
              destruct H as [Hvalid Htransition].
              
              assert (s = destination lst). {
                rewrite Hlst in Hlast.
                rewrite map_app in Hlast.
                rewrite last_app in Hlast.
                simpl in Hlast.
                symmetry.
                assumption.
              }
              
              destruct (l lst) eqn : eq_l.
              - simpl in *.
                inversion Htransition.
                rewrite H in Hin.
                rewrite <- H1 in Hin.
                rewrite history_disregards_cv in Hin.
                rewrite history_append in Hin.
                specialize (output_gets_recordedd 
                            (update c)
                            (destination lst')
                            (destination lst)
                            (input lst)
                            (index_self, destination lst')).
               intros.
               replace (@Some (@message index index_listing)
                   (@pair index
                      (@Common.state (@message index index_listing)
                         (@VLSM_list_protocol index index_listing)) index_self
                      (@destination (@message index index_listing)
                         (@VLSM_list_protocol index index_listing) lst'))) with (output lst) in H0.
               specialize (H0 Hold).
               simpl in *.
               rewrite <- H in H0.
               
               inversion Hin.
               + rewrite H3 in H0. elim n. assumption.
               + assumption.
               + apply protocol_prop_no_bottom. destruct Hvalid. intuition.
               + apply protocol_prop_no_bottom. destruct Hvalid. intuition.
               + reflexivity.
             - simpl in *.
               inversion Htransition.
               destruct (input lst) eqn : input_eq. 
               + inversion H1.
                 rewrite <- H in H2.
                 rewrite <- H2 in Hin.
                 rewrite <- (history_oblivious (destination lst') (snd m) index_self (fst m)) in Hin.
                 assumption.
                 destruct Hvalid as [a [b [c [d e]]]].
                 intuition.
               + destruct Hvalid as [a [b c]].
                 exfalso.
                 assumption.
           }
           specialize (IHlen Hin').
           rewrite Exists_exists in IHlen.
           destruct IHlen as [x' [Hin_x Hproject_x]].
           exists x'.
           split.
           rewrite Hlst.
           rewrite <- eq'.
           intuition.
           assumption.
    Qed.
    
    *)
      
    
    Lemma send_oracle_prop 
      (s : state)
      (Hprotocol : protocol_state_prop preX s)
      (m : message) :
      has_been_sent_prop X (send_oracle index_self) s m.
    
    Proof.
      unfold has_been_sent_prop.
      unfold all_traces_have_message_prop.
      split.
      - intros.
        unfold send_oracle in H.
        destruct (idec (fst m) index_self) eqn:eq.
        2: discriminate H.
        destruct s eqn:eq_s.
        + discriminate H.
        + apply existsb_exists in H.
          destruct H as [x [Hin Heq_state]].
          (* Somewhere, the message shows up as somebody's projection *)
          
          assert (List.Exists (fun elem : (@transition_item _ (type preX)) => project (destination elem) index_self = (snd m)) tr). {
              apply some_project with (s := s) (si := start) (len := length tr).
              reflexivity.
              assumption.
              rewrite eq_s.
              assumption.
              rewrite eq_s.
              rewrite state_eqb_eq in Heq_state.
              rewrite Heq_state.
              rewrite <- e.
              assumption.
          }
          
          (* Among those places, we choose the earliest one *)
          
          assert (exists (prefix : list transition_item)
                         (suffix : list transition_item)
                         (target : transition_item),
                         tr = prefix ++ [target] ++ suffix /\
                         project (destination target) index_self = (snd m) /\
                         ~List.Exists (fun elem : (@transition_item _ (type preX)) 
                                        => project (destination elem) index_self = (snd m)) prefix). {
              rewrite Exists_exists in H.
              destruct H as [t [Hin' Hproject]].
              rewrite <- state_eqb_eq in Hproject.
              assert (exists (t : transition_item), In t tr /\ state_eqb (project (destination t) index_self) (snd m) = true). {
                exists t.
                intuition.
              }
              
              rewrite <- existsb_exists in H.
              specialize (existsb_first 
                          tr 
                          (fun x : transition_item => state_eqb (project (destination x) index_self) (snd m))
                          H).
              intros.
              destruct H0 as [prefix [suffix [first [Heqb [Hsplt Hno_earlier]]]]].
              exists prefix.
              exists suffix.
              exists first.
              split.
              assumption.
              split.
              rewrite <- state_eqb_eq.
              assumption.
              rewrite <- Forall_Exists_neg.
              rewrite Forall_forall.
              intros.
              apply In_nth with (d := x0) in H0.
              destruct H0 as [n [Hless Hnth]].
              apply existsb_nth with (n := n) (d := x0) in Hno_earlier.
              rewrite <- Hnth.
              rewrite state_eqb_neq in Hno_earlier.
              assumption.
              assumption.
          }
         
          destruct H0 as [prefix [suffix [target [Hsplit [Hproject Hnot_earlier]]]]].
         
          unfold finite_protocol_trace in Htr.
          destruct Htr as [Htr Hinitial].
          
          rewrite Exists_exists.
          exists target.
          split.
          * rewrite Hsplit.
            apply in_elt.
          * destruct prefix.
            simpl in *.
            
            assert (protocol_transition 
                    preX 
                    (l target) 
                    (start, (input target)) 
                    ((destination target), (output target))). {
                specialize (first_transition_valid preX start target).
                intros.
                apply H0.
                specialize (finite_protocol_trace_from_prefix preX start tr Htr 1).
                intros.
                assert (list_prefix tr 1 = [target]). { 
                  rewrite Hsplit.
                  simpl.
                  unfold list_prefix.
                  destruct suffix; reflexivity.
                }
                rewrite <- H2.
                assumption.
            }
            
            specialize (new_projection_implies_output_message 
                        (l target) 
                        (start, (input target)) 
                        ((destination target), (output target))
                        H0
                        (snd m)).
            
            intros.
            simpl in H1.
            
            assert (project start index_self <> snd m). {
              unfold project.
              destruct start eqn : eq_start.
              - unfold initial_state_prop in Hinitial.
                destruct Hinitial.
                discriminate H2.
              - unfold initial_state_prop in Hinitial.
                destruct Hinitial.
                inversion H2.
                assert (project_indexed index_listing all_bottom index_self = Bottom). {
                  rewrite project_all_bottom.
                  reflexivity.
                }
                rewrite H3.
                specialize (no_bottom_in_history (Something b is) x).
                intros.
                specialize (H6 index_self).
                rewrite <- e in H6.
                subst.
                rewrite state_eqb_eq in Heq_state.
                rewrite Heq_state.
                intuition.
            }
            
            specialize (H1 H2 Hproject).
            rewrite <- e in H1.
            rewrite <- surjective_pairing in H1.
            assumption.
            
            assert (exists (prev_target : transition_item)
                           (rem_pref : list transition_item),
                           (t :: prefix) = (rem_pref ++ [prev_target])). {
                   specialize (first_implies_last t prefix).
                   intros.
                   destruct H0 as [l2 [lst Hrem]].
                   exists lst. 
                   exists l2.
                   assumption.
            }
            
            destruct H0 as [prev_target [rem_pref Heqprev]].
            rewrite Heqprev in Hsplit.
            specialize (finite_ptrace_consecutive_valid_transition preX start tr suffix rem_pref).
            intros.
            specialize (H0 prev_target target).
            specialize (H0 Htr).
            simpl in *.
            rewrite <- app_assoc in Hsplit.
            simpl in Hsplit.
            specialize (H0 Hsplit).
            specialize (new_projection_implies_output_message 
                       (l target) 
                       (destination prev_target, (input target)) 
                       ((destination target), (output target))
                       H0
                       (snd m)).
            intros.
            simpl in *.
            rewrite <- e in H1.
            rewrite <- surjective_pairing in H1.
            apply H1.
            rewrite Heqprev in Hnot_earlier.
            rewrite <- Forall_Exists_neg in Hnot_earlier.
            rewrite Forall_app in Hnot_earlier.
            destruct Hnot_earlier as [left right].
            rewrite Forall_forall in right.
            specialize (right prev_target).
            simpl in *.
            rewrite e.
            apply right.
            intuition.
            rewrite e. assumption.
      - unfold send_oracle.
        intros.
        remember Hprotocol as Hprotocol'.
        destruct Hprotocol as [om Hprotocol].
        specialize (protocol_is_trace preX s om Hprotocol) as Hsome_trace.
        intros.
        simpl in *.
        destruct Hsome_trace.
        + unfold initial_state_prop in H0.
          remember H0 as H0'.
          destruct H0.
          assert (Hempty : finite_protocol_trace (pre_loaded_vlsm preX) s []). { 
            unfold finite_protocol_trace.
            simpl.
            split.
            - apply finite_ptrace_empty. assumption.
            - assumption. 
          }
          
          specialize (H s [] Hempty). 
          simpl in H.
          specialize (H eq_refl).
          
          simpl in H.
          inversion H.
        + destruct H0 as [s0 [tr [Hfinite_protocol [Hdest Hmessage]]]].
          destruct Hmessage.
          specialize (H s0 tr Hfinite_protocol).
          assert (last (List.map destination tr) s0 = s). {
            specialize (@last_map (@transition_item message (type preX)) state destination).
            intros. 
            unfold option_map in Hdest.
            destruct (last_error tr) eqn : eq.
            - inversion Hdest.
              unfold last_error in eq.
              destruct tr.
              + discriminate eq.
              + inversion eq.
                apply H0.
           - discriminate Hdest.
                
          }
          
          specialize (H H0).
          assert (can_emit preX m). {
            specialize (can_emit_from_protocol_trace preX s0 m tr Hfinite_protocol H).
            intros.
            assumption.
          }
          
          assert ((fst m) = index_self). {
            apply emitted_messages_only_from_self.
            assumption.
          }
          
          destruct (idec (fst m) index_self).
          * assert (s <> Bottom). {
              apply protocol_prop_no_bottom.
              assumption.
            }
            
            destruct s. elim H3. reflexivity.
            
            (* Rewrite it as Prop involving In. *)
            
            assert (In (snd m) (get_history (Something b is) (fst m))). {
              rewrite e.
              
              remember (@Finite _ (type preX) s0 tr) as original.
              assert (protocol_trace_prop preX original). {
                unfold protocol_trace_prop.
                rewrite Heqoriginal.
                assumption.
              }
              remember (exist _ original H4) as original_protocol.
              
              assert (Htriv: proj1_sig original_protocol = original). {
                destruct original_protocol eqn : eq.
                simpl.
                inversion Heqoriginal_protocol.
                reflexivity.
              }

              assert (exists (tr' : list transition_item) 
                             (lst : transition_item),
                             (trace_prefix (proj1_sig original_protocol) lst tr') /\
                             (output lst = Some m)). {
                    rewrite Exists_exists in H.
                    destruct H as [x [Hin Hm']].
                    apply in_split in Hin.
                    destruct Hin as [l1 [l2 Hsplit]].
                    exists l1.
                    exists x.
                    split.
                    - unfold trace_prefix.
                      rewrite Htriv.
                      rewrite Heqoriginal.
                      exists l2.
                      assumption.
                    - assumption.
                }
              
              destruct H5 as [tr' [lst [Hprefix Hm]]].
              specialize (message_gets_recorded (destination lst) s0 m tr' lst) as Hrecorded.
              intros.

              assert (finite_protocol_trace preX s0 (tr' ++ [lst])). {
                specialize (trace_prefix_protocol preX original_protocol lst tr' Hprefix).
                intros.
                replace ((@proj1_sig
                (@Trace (@message index index_listing) (@VLSM_list_protocol index index_listing))
                (fun
                   tr : @Trace (@message index index_listing)
                          (@VLSM_list_protocol index index_listing) =>
                 @protocol_trace_prop (@message index index_listing)
                   (@VLSM_list_protocol index index_listing)
                   (@pre_loaded_vlsm_sig (@message index index_listing)
                      (@VLSM_list_protocol index index_listing)
                      (@LSM_list index index_self index_listing) X) preX tr) original_protocol)) with (original) in H5.
                unfold protocol_trace_prop in H5.
                unfold trace_first in H5.
                rewrite Heqoriginal in H5.
                assumption.
              }
             
              specialize (Hrecorded H5 Hm).
              
              apply projection_in_history in Hrecorded.
              apply history_persists_trace with (s1 := (destination lst)).
              
              - unfold in_futures.
                unfold trace_prefix in Hprefix.
                rewrite Htriv in Hprefix.
                rewrite Heqoriginal in Hprefix.
                destruct Hprefix as [suffix Hsuffix].
                exists suffix.
                split.
                + Check finite_protocol_trace_from_app_iff.
                  specialize (finite_protocol_trace_from_app_iff preX s0 (tr' ++ [lst]) suffix).
                  intros.
                  destruct H6 as [_ right].
                  
                  assert (last (List.map destination (tr' ++ [lst])) s0 = destination lst). {
                    rewrite map_app.
                    simpl.
                    rewrite last_app.
                    simpl.
                    reflexivity.
                  }
                  
                  rewrite <- H6.
                  apply right.
                  rewrite <- app_assoc.
                  simpl.
                  rewrite <- Hsuffix.
                  unfold finite_protocol_trace in Hfinite_protocol.
                  destruct Hfinite_protocol.
                  assumption.
                + destruct suffix eqn : eq_suffix.
                  * simpl in *. rewrite <- H0.
                    rewrite Hsuffix.
                    rewrite map_last.
                    rewrite last_is_last.
                    reflexivity.
                  * rewrite <- H0.
                    rewrite Hsuffix.
                    rewrite map_app.
                    rewrite last_app.
                    rewrite map_cons.
                    rewrite map_cons.
                    rewrite unroll_last.
                    rewrite unroll_last.
                    rewrite map_cons.
                    rewrite unroll_last.
                    reflexivity.
              - assumption.
              - apply emitted_not_bottom. assumption.
            }
            
            apply existsb_exists.
            exists (snd m).
            split.
            assumption.
            unfold state_eqb.
            destruct (sdec (snd m) (snd m)). reflexivity. elim n. reflexivity.
            * rewrite H2 in n. elim n. reflexivity.
    Qed.
    
    Lemma receive_oracle_prop 
      (s : state)
      (Hprotocol : protocol_state_prop preX s)
      (m : message) :
      has_been_received_prop X (receive_oracle index_self) s m.
    
    Proof.
      unfold has_been_received_prop.
      unfold all_traces_have_message_prop.
      split.
      - intros.
        unfold receive_oracle in H.
        destruct (idec (fst m) index_self) eqn:eq.
        + discriminate H.
        + destruct s eqn:eq_s.
          * discriminate H.
          * apply existsb_exists in H.
            destruct H as [x [Hin Heq_state]].
          (* Somewhere, the message shows up as somebody's projection *)
          
          assert (List.Exists (fun elem : (@transition_item _ (type preX)) => project (destination elem) (fst m) = (snd m)) tr). {
              apply some_project with (s := s) (si := start) (len := length tr).
              reflexivity.
              assumption.
              rewrite eq_s.
              assumption.
              rewrite eq_s.
              rewrite state_eqb_eq in Heq_state.
              rewrite Heq_state.
              assumption.
          }
          
          (* Among those places, we choose the earliest one *)
          
          assert (exists (prefix : list transition_item)
                         (suffix : list transition_item)
                         (target : transition_item),
                         tr = prefix ++ [target] ++ suffix /\
                         project (destination target) (fst m) = (snd m) /\
                         ~List.Exists (fun elem : (@transition_item _ (type preX)) 
                                        => project (destination elem) (fst m) = (snd m)) prefix). {
              rewrite Exists_exists in H.
              destruct H as [t [Hin' Hproject]].
              rewrite <- state_eqb_eq in Hproject.
              assert (exists (t : transition_item), In t tr /\ state_eqb (project (destination t) (fst m)) (snd m) = true). {
                exists t.
                intuition.
              }
              
              rewrite <- existsb_exists in H.
              specialize (existsb_first 
                          tr 
                          (fun x : transition_item => state_eqb (project (destination x) (fst m)) (snd m))
                          H).
              intros.
              destruct H0 as [prefix [suffix [first [Heqb [Hsplt Hno_earlier]]]]].
              exists prefix.
              exists suffix.
              exists first.
              split.
              assumption.
              split.
              rewrite <- state_eqb_eq.
              assumption.
              rewrite <- Forall_Exists_neg.
              rewrite Forall_forall.
              intros.
              apply In_nth with (d := x0) in H0.
              destruct H0 as [nn [Hless Hnth]].
              apply existsb_nth with (n := nn) (d := x0) in Hno_earlier.
              rewrite <- Hnth.
              rewrite state_eqb_neq in Hno_earlier.
              assumption.
              assumption.
          }
        
        rewrite Exists_exists.
        destruct H0 as [prefix [suffix [target [Hconcat [Hproject Hno_earlier]]]]].
        
        exists target.
        split.
        rewrite Hconcat.
        apply in_elt.
        
        remember (last (List.map destination prefix) start) as prev_target.
        assert (Hptransition: protocol_transition preX (l target) (prev_target, input target) (destination target, output target)). {
          admit.
        }
        
        specialize new_projection_implies_input_message as Hchange.
        specialize (Hchange (l target) (prev_target, input target) (destination target, output target)).
        specialize (Hchange Hptransition (fst m) n (snd m)).
        simpl in *.
        
        assert (Hold: project prev_target (fst m) <> snd m). {
          destruct prefix eqn : eq_prefix.
          - simpl in *.
            rewrite Heqprev_target.
            assert (Hnot_bottom : snd m <> Bottom). {
              specialize (no_bottom_in_history s x (fst m)).
              intros.
              rewrite eq_s in H0.
              specialize (H0 Hin).
              rewrite state_eqb_eq in Heq_state.
              rewrite <- Heq_state in H0.
              assumption.
            }
            
            unfold project.
            destruct Htr as [_ Hinit].
            simpl in Hinit.
            unfold initial_state_prop in Hinit.
            destruct Hinit as [cv Hinit].
            rewrite Hinit.
            rewrite project_all_bottom.
            intuition.
          - assert (Hprev: exists 
                           (lst : transition_item) 
                           (prefix' : list transition_item),
                           (prefix = prefix' ++ [lst])). {
              specialize (first_implies_last t l).
              intros.
              destruct H0 as [l2 [lst Hrev]].
              exists lst.
              exists l2.
              rewrite eq_prefix.
              assumption.
            }
            
            destruct Hprev as [lst [prefix' Hprefix]].
            assert (prev_target = destination lst). {
              rewrite Heqprev_target.
              rewrite <- eq_prefix.
              rewrite Hprefix.
              rewrite map_app.
              rewrite last_app.
              simpl.
              reflexivity.
            }
            rewrite H0.
            rewrite <- Forall_Exists_neg in Hno_earlier.
            rewrite Forall_forall in Hno_earlier.
            specialize (Hno_earlier lst).
            apply Hno_earlier.
            rewrite <- eq_prefix.
            rewrite Hprefix.
            apply in_elt.
        }
        specialize (Hchange Hold Hproject).
        rewrite <- surjective_pairing in Hchange.
        assumption.
      - intros.
        unfold receive_oracle.
        remember Hprotocol as Hprotocol'.
        destruct Hprotocol as [om Hprotocol].
        specialize (protocol_is_trace preX s om Hprotocol) as Hsome_trace.
        intros.
        simpl in *.
        destruct Hsome_trace eqn : trace_eq.
        + unfold initial_state_prop in i.
          remember i as i'.
          destruct i.
          assert (Hempty : finite_protocol_trace (pre_loaded_vlsm preX) s []). { 
            unfold finite_protocol_trace.
            simpl.
            split.
            - apply finite_ptrace_empty. assumption.
            - assumption. 
          }
          
          specialize (H s [] Hempty). 
          simpl in H.
          specialize (H eq_refl).
          
          simpl in H.
          inversion H.
        + destruct e as [start [tr [Hprotocol_tr [Hdest Hothers]]]].
          destruct trace_eq.
          specialize (H start tr Hprotocol_tr).
          assert (last (List.map destination tr) start = s). {
            specialize (@last_map (@transition_item message (type preX)) state destination).
            intros. 
            unfold option_map in Hdest.
            destruct (last_error tr) eqn : eq.
            - inversion Hdest.
              unfold last_error in eq.
              destruct tr.
              + discriminate eq.
              + inversion eq.
                apply H0.
           - discriminate Hdest.
          }
          specialize (H H0).
          rewrite Exists_exists in H.
          destruct H as [x [Hin Hm]].
          apply in_split in Hin.
          destruct Hin as [l1 [l2 Hconcat]].
          remember (last (List.map destination l1) start) as prev_x.
          
          assert (protocol_transition preX (l x) (prev_x, input x) (destination x, output x)). {
            destruct l1.
            - simpl in *.
              rewrite Heqprev_x.
              admit.
            - simpl in *.
              admit.
          }
          
          destruct (idec (fst m) index_self). 
          * unfold protocol_transition in H.
            destruct H as [Hvalid Htransition].
            unfold protocol_valid in Hvalid.
            destruct Hvalid as [Hpstate [_ Hvalid']].
            simpl in *.
            destruct (l x) eqn : eq_l. 
            {
              destruct Hvalid' as [_ Hnoinput].
              rewrite Hm in Hnoinput.
              discriminate Hnoinput.
            }
            { rewrite Hm in Hvalid'.
              destruct Hvalid' as [_ [_ Hdiff]].
              elim Hdiff.
              symmetry.
              assumption.
            }
          * specialize (input_gets_recorded (l x) prev_x (destination x) m (output x) (fst m)) as Hrecorded.
            intros.
            rewrite Hm in H.
            specialize (Hrecorded eq_refl n H).
            specialize (projection_in_history (destination x) (snd m) (fst m)) as Hproject.
            intros.
            
            assert (Hnot_bottom: snd m <> Bottom). {
              admit.
            }
            
            specialize (Hproject Hnot_bottom Hrecorded).
            specialize (history_persists_trace (destination x) s (snd m) (fst m)) as Hpersists.
            intros.
            
            assert (Hfutures: in_futures preX (destination x) s). {
              admit.
            }
            
            specialize (Hpersists Hfutures Hproject).
            rewrite existsb_exists.
            exists (snd m).
            split.
            assumption.
            rewrite state_eqb_eq.
            reflexivity.
    Admitted.
End Equivocation.
      


