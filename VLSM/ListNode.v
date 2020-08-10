Require Import Bool List Streams Logic.Epsilon Logic.Decidable Reals ProofIrrelevance Fin FinFun OrdersFacts.
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
  | update c => estimator s c
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

    Lemma last_recorded_present
      (s child : state)
      (ls : indexed_state index_listing)
      (cv : bool)
      (Heq : s = Something cv ls)
      (Hchild : last_recorded index_listing ls index_self = child)
      (tr : protocol_trace (pre_loaded_vlsm X))
      (last : transition_item)
      (prefix : list transition_item)
      (Hpr : trace_prefix (proj1_sig tr) last prefix)
      (Hlast : destination last = s) :
      List.Exists (fun (elem : transition_item) => output elem = Some (index_self, child)) prefix.
      
    Proof.
    Admitted.
    
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

    
    Lemma transition_gets_recorded :
      forall (l : label)
             (s1 s2 : state)
             (m1 : option message)
             (m2 : message)
             (som1 := (s1, m1))
             (som2 := (s2, Some m2))
             (* TODO: remove not_bottom assumption *)
             (Hnot_bottom : s1 <> Bottom)
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
       assumption.
       - destruct m1 eqn : m1_eq.
         + inversion transition_prop.
         + inversion transition_prop.
    Qed.
    
    
    Lemma rec_history_split :
      forall (s : state)
             (i : index)
             (d1 d2 : nat)
             (Hsufficient : d2 >= (depth s))
             (Hsmaller : d1 <= d2)
             (short := rec_history s i d1),
             rec_history s i d2 = short ++ rec_history (project (last short Bottom) i) i (d2 - d1).
             
    Proof.
    Admitted.
    
    Lemma last_cant_progress :
      forall (s : state)
             (i : index)
             (random : state),
             (project (last (rec_history s i (depth s)) random) i = Bottom).
    
    Proof.
      intros.
      induction (depth s).
      - simpl. admit.
      - unfold rec_history.
     Admitted.
     
     (* begin hide *)
    Lemma depth_parent_child :
      forall (ls : indexed_state index_listing)
         (cv : bool)
         (i : index),
         depth (Something cv ls) >= S (depth (project_indexed index_listing ls i)).
    
      Proof.
        intros.
        assert ((depth_indexed index_listing ls) >= depth (project_indexed index_listing ls i)). {
          induction ls.
          - auto.
          - destruct (eq_dec v i) eqn : Heqdec.
            + simpl. rewrite Heqdec.
              unfold depth_indexed. 
              admit.
        }
        
        unfold depth in H. 
        unfold depth at 1.
        
      Admitted.
(* end hide *)

    Lemma depth_redundancy :
      forall (s : state)
             (i : index)
             (d : nat)
             (Hbig : d >= depth s),
        rec_history s i d = rec_history s i (depth s).
    Proof.
      intros.
      specialize (rec_history_split s i (depth s) d Hbig Hbig).
      intros.
      rewrite H.
      assert (rec_history (project (last (rec_history s i (depth s)) Bottom) i) i (d - depth s) = []). {
        assert ((project (last (rec_history s i (depth s)) Bottom) i) = Bottom). {
          apply last_cant_progress.
        }
        rewrite H0.
        unfold rec_history.
        destruct (d - depth s); reflexivity.
      }
      rewrite H0.
      rewrite app_nil_r.
      reflexivity.
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
    
    Lemma message_gets_recorded :
      forall (m : message)
             (tr : protocol_trace preX)
             (last1 : transition_item)
             (prefix : list transition_item)
             (Hpr : trace_prefix (proj1_sig tr) last1 prefix)
             (Hm : output last1 = Some m),
             project (destination last1) index_self = snd m.
    Proof.
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
          
          apply transition_gets_recorded with (l := l last1) (s1 := s0) (m1 := input last1).
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
         
         apply transition_gets_recorded with (l := l last1) (s1 := destination prev) (m1 := input last1).
         
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
          
          apply transition_gets_recorded with (l := l last1) (s1 := s0) (m1 := input last1).
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
         
         apply transition_gets_recorded with (l := l last1) (s1 := destination prev) (m1 := input last1).
         
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
    
    
    (* This is not true though. *)
    Lemma only_from_self
      (m : protocol_message preX) :
      fst (proj1_sig m) = index_self.
      
    Proof.
      destruct m.
      simpl.
      destruct p.
      simpl in *.
      inversion H.
      - destruct im.
        simpl in i.
    Admitted.
    
    Lemma send_oracle_prop 
      (s : state)
      (m : message) :
      has_been_sent_prop preX (send_oracle index_self) s m.
    
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
          destruct H.
          admit.
      - unfold send_oracle.
        admit.
    Admitted.
    
End Equivocation.
      


