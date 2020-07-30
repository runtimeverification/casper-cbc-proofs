Require Import Bool List Streams Logic.Epsilon Logic.Decidable Reals ProofIrrelevance Fin FinFun.
Import ListNotations.
From CasperCBC
Require Import Lib.Preamble Lib.ListExtras Lib.ListSetExtras Lib.RealsExtras CBC.Definitions CBC.Common VLSM.Common VLSM.Composition VLSM.Decisions CBC.FullNode.

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
  (Hin : In i l)
  (Heq : project_indexed l is i Hin = news) :
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
    + assert (Hin' : In i l). {
        destruct Hin.
        * subst. 
          elim n. 
          reflexivity.
        * assumption.
      }
      assert (Hstep : project_indexed (v :: l) (Append v l s is) i Hin = project_indexed l is i Hin'). {
        unfold project_indexed.
        rewrite eq.
        simpl.
        
        admit.
      }
      
      assert (update_indexed l is i news = is). {
        apply IHis with (Hin := Hin').
        rewrite Hstep in Heq.
        assumption.
      }
      
      rewrite H.
      reflexivity.
Admitted.
  

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
  
Lemma update_state_eq
      (big : state)
      (news : state)
      (i : index)
      (Hin : In i index_listing)
      (Heq : project big i = Some news)
      : update_state big news i = big.

Proof.
  intros.
  unfold update_state.
  destruct big.
  -reflexivity.
  - assert (Heqis : (update_indexed index_listing is i news) = is). {
    apply update_indexed_eq with (Hin := proj2 Hfinite i).
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
Admitted.

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

Definition initial_state_prop (s : state) : Prop := (s = Bottom).

Lemma bottom_good : initial_state_prop Bottom.
  Proof.
    unfold initial_state_prop.
    auto.
  Qed.

Definition state0 : {s | initial_state_prop s} := 
  exist _ Bottom bottom_good.

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
               | Some m => project s (fst m) = project (snd m) (fst m) /\ index_self <> (fst m)
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

Instance VLSM_list_machine : VLSM_class LSM_list :=
  { transition := transition
    ; valid := valid
  }.

Definition VLSM_list : VLSM message := mk_vlsm VLSM_list_machine.

End ListNode.

