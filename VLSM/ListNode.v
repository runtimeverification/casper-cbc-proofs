Require Import Bool List Streams Logic.Epsilon Logic.Decidable Reals ProofIrrelevance Fin FinFun.
Import ListNotations.
From CasperCBC
Require Import Lib.Preamble Lib.ListExtras Lib.ListSetExtras Lib.RealsExtras CBC.Definitions CBC.Common VLSM.Common VLSM.Composition VLSM.Decisions CBC.FullNode.

Section ListNode.

Context 
  {index : Type}
  {index_self : index}
  {index_listing : list index}
  {Hfinite : Listing index_listing}
  {dec : EqDec index}
  {temp_dec : EqDec (option bool)}.

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

Fixpoint project_indexed
  (l : list index)
  (is : indexed_state l)
  : forall
    (v : index)
    (Hin : In v l)
,
    state.
  intros.
  inversion is; subst;try inversion Hin.
  destruct (eq_dec v v0).
  + exact s.
  + assert (Hin0 : In v l0).
    { destruct Hin as [Heq | Hin] ; try assumption.
      subst. elim n. reflexivity.
    }
    exact (project_indexed l0 is0 v Hin0).
Defined. 

Definition project
  (s : state)
  (v : index)
  : option state
  :=
  match s with 
  | Bottom => None
  | Something b is => Some (project_indexed index_listing is v (proj2 Hfinite v))
  end.

Fixpoint get_all_states
  (l : list index)
  (is : indexed_state l)
  : list state.
  intros.
  destruct is eqn:is_eqn.
  - exact [].
  - exact (s :: get_all_states l i).
  Defined.

Definition state00 := Bottom.

Definition message : Type := (index * state).

Definition message00 := (index_self, state00).

Definition initial_state_prop_list (s : state) : Prop := (s = Bottom).

Definition initial_message_prop_list (m : message) : Prop := False.

Lemma bottom_good : initial_state_prop_list Bottom.
  Proof.
    unfold initial_state_prop_list.
    auto.
  Qed.

Definition state0 : {s | initial_state_prop_list s} := 
  exist _ Bottom bottom_good.

Definition decision (s : state) : option bool :=
  match s with
  | Bottom => None
  | Something c some => Some c
  end.
  
Definition global_decisions (s : state) : list (option bool) :=
  match s with
  | Bottom => []
  | Something c some => List.map decision (get_all_states index_listing some)
  end.

(* Introduce some tie-breaking here? *)

Definition estimator_list (s : state) (b : bool) : Prop :=
  let our_count := List.count_occ temp_dec (global_decisions s) (Some b) in
  match s with 
  | Bottom => True
  | Something c some => our_count >= List.count_occ temp_dec (global_decisions s) (Some (negb b))
  end.

Inductive label_list : Type :=
| update (c : bool)
| receive.

Fixpoint update_indexed 
  (l : list index)
  (is : indexed_state l) 
  (i : index) 
  (new_s : state) : 
  indexed_state l.
  intros.
  inversion is.
  - exact Empty.
  - destruct (eq_dec v i).
    + exact (Append v l0 new_s is0).
    + exact (Append v l0 s (update_indexed l0 is0 i new_s)).
Defined.

(* Definition all_bottom : indexed_state index_listing := *)

Fixpoint all_bottom_f (l : list index) : indexed_state l :=
  match l with
  | [] => Empty
  | (h :: t) => Append h t Bottom (all_bottom_f t)
  end.
  
Definition all_bottom := all_bottom_f index_listing.

Definition update_list (big : state) (news : state) (i : index) (value : bool): state :=
  match big with
  | Bottom => Something value (update_indexed index_listing all_bottom i news)
  | Something cv f => Something value (update_indexed index_listing f i news)
  end.

Definition transition_list (l : label_list) (som : state * option message) : state * option message :=
    let (s, om) := som in
       match l with
       | update c => (update_list s s index_self c, Some (index_self, s)) 
       | receive => match om with 
                    | Some m => ((update_list s (snd m) (fst m) false), None)
                    | None => (s, None)
                    end
       end.

Definition valid_list
    (l : label_list)
    (som : state * option message)
    := 
    let (s, om) := som in
    match l with
    | update c => estimator_list s c
    | receive => match om with 
                 | None => False
                 | Some m => project s (fst m) = project (snd m) (fst m) /\ index_self <> (fst m)
                 end
    end.
      

Instance VLSM_list_protocol : VLSM_type message :=
    { state := state
    ; label := label_list
    }.
    
Instance LSM_list : VLSM_sign VLSM_list_protocol :=
    { initial_state_prop := initial_state_prop_list
    ; initial_message_prop := initial_message_prop_list
    ; s0 := state0
    ; m0 := message00
    ; l0 := receive
    }.

Instance VLSM_list : VLSM LSM_list :=
    { transition := transition_list
      ; valid := valid_list
    }.



