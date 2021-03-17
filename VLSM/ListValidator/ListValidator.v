Require Import Bool List Reals FinFun Program.
Require Import Lia.
Import ListNotations.
From CasperCBC
Require Import Lib.Preamble Lib.ListExtras VLSM.Common VLSM.Composition VLSM.Equivocation .

Section ListNode.

(**

*** Minimal List Validator Protocol

We introduce here the "minimal list validator protocol", by quoting the official
documentation:

In this section, we propose a protocol where each validator keeps a list of states of other validators. Each validator broadcasts its view of the other validators'
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
  `{EqDecision index}.

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
Fixpoint state_eq_dec (s1 s2 : state)
  : {s1 = s2} + {s1 <> s2}
with
indexed_state_eq_dec (l : list index) (ls1 : indexed_state l) (ls2 : indexed_state l)
  : {ls1 = ls2} + {ls1 <> ls2}.
Proof.
- destruct s1; destruct s2.
  + left. reflexivity.
  + right. intro H. discriminate H.
  + right. intro H. discriminate H.
  + destruct (bool_eq_dec b b0).
    * { destruct (indexed_state_eq_dec index_listing is is0).
      - subst. left. reflexivity.
      - right. subst. intro H. elim n. inversion H. reflexivity.
      }
    * right. intro H. elim n. inversion H. reflexivity.
- dependent destruction ls1; dependent destruction ls2.
  + left. reflexivity.
  + destruct (state_eq_dec s s0).
    * { destruct (indexed_state_eq_dec l ls1 ls2).
      - left. subst. reflexivity.
      - right. intro H. elim n. inversion H. apply inj_pairT2 in H2. assumption.
      }
    * right. intro H. elim n. inversion H. reflexivity.
Qed.

Global Instance state_EqDecision : EqDecision state := state_eq_dec.

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
    if decide (v' = v)
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
    if decide (v' = v)
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
    destruct (decide (v = i)) eqn : eq.
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
    destruct (decide (v = i)) eqn : dec_eq; simpl; rewrite <- Heq; rewrite dec_eq;
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
    destruct (decide (v = i)).
    + simpl.
      destruct (decide (v = j)).
      * rewrite e in e0. subst. elim Heq. reflexivity.
      * reflexivity.
    + simpl.
      destruct (decide (v = j)).
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
    destruct (decide (v = i)) eqn : eq.
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

Lemma depth_consensus_clean
  (s : state)
  (value : bool) :
  depth s = depth (update_consensus s value).
Proof.
  unfold depth.
  destruct s; simpl; reflexivity.
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


     (* begin hide *)
    Lemma depth_parent_child_indexed
      (indices : list index)
      (i : index)
      (Hi : In i indices)
      (ls : indexed_state indices)
      : depth_indexed indices ls >= depth (project_indexed indices ls i).
    Proof.
      generalize dependent indices.
      induction ls.
      - auto.
      - simpl.
        destruct (decide (v = i)) eqn : Heqdec.
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

Global Instance message_EqDecision : EqDecision message := _.

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

Definition in_mode (modes : list (option bool)) (b : bool) : Prop :=
  match (inb decide_eq (Some b) modes) with
  | true => True
  | false => (inb decide_eq None modes) = true
  end.

Global Instance in_mode_dec : RelDecision in_mode.
Proof.
  unfold RelDecision; intros modes b.
  unfold in_mode.
  destruct (inb decide_eq (Some b) modes) eqn : eq_b.
  - left. intuition.
  - destruct (inb decide_eq None modes); intuition.
Qed. 

Definition estimator (s : state) (b : bool) : Prop :=
  let ob_dec := (option_eq_dec) in
  let decision_modes := mode (global_decisions s) in
  match s with
  | Bottom => True
  | Something c some => in_mode decision_modes b 
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

Definition list_transition (l : label_list) (som : state * option message) : state * option message :=
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

Definition list_valid
  (est : state -> bool -> Prop)
  (l : label_list)
  (som : state * option message)
  :=
  let (s, om) := som in
  match l with
  | update c => est s c /\ om = None
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

Instance VLSM_list_machine
  (est : state -> bool -> Prop)
  : VLSM_class LSM_list :=
  { transition := list_transition
    ; valid := list_valid est
  }.

Definition VLSM_list
  (est : state -> bool -> Prop)
  : VLSM message := mk_vlsm (VLSM_list_machine est).

Definition mk_label (l : label_list) : @label _ VLSM_list_protocol := l.

Definition last_recorded (l : list index) (ls : indexed_state l) (who : index) : state :=
  project_indexed l ls who.

Definition last_sent (s : state) : state := project s index_self.

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
    match decide_eq s1 s2 with
    | left _ => true
    | right _ => false
    end.

  Lemma state_eqb_eq (s1 s2 : state) :
    (state_eqb s1 s2) = true <-> s1 = s2.
  Proof.
    unfold state_eqb.
    split.
    - destruct (decide (s1 = s2)).
      + intuition.
      + intros. discriminate H.
    - intros.
      destruct (decide (s1 = s2));
      intuition.
  Qed.

  Lemma state_eqb_neq (s1 s2 : state) :
    (state_eqb s1 s2) = false <-> s1 <> s2.
  Proof.
    unfold state_eqb.
    split;
    destruct (decide (s1 = s2));
    intuition.
  Qed.

  Definition send_oracle (s : state) (m : message)  : bool :=
    let who := fst m in
    let what := snd m in
    match decide (who = index_self) with
    | right _ => false
    | left _ => existsb (state_eqb what) (get_history s who)
    end.

  Definition receive_oracle (s : state) (m : message) : bool :=
    let who := fst m in
    let what := snd m in
    match decide (who = index_self) with
    | left _ => false
    | right _ => existsb (state_eqb what) (get_history s who)
    end.

    Definition not_send_oracle (s : state) (m : message)  : bool :=
      negb (send_oracle s m).

    Definition not_receive_oracle (s : state) (m : message) : bool :=
      negb (receive_oracle s m). 
   
End ListNode. 
