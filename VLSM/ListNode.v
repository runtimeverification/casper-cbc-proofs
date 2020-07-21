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

Inductive state_list := 
| Bottom : state_list
| Something : (bool -> (index -> state_list) -> state_list).

Definition state_list00 := Bottom.

Definition message : Type := (index * state_list).

Definition message00 := (index_self, state_list00).

Definition initial_state_prop_list (s : state_list) : Prop := True.

Definition initial_message_prop_list (m : message) : Prop := False.

Lemma bottom_good : initial_state_prop_list Bottom.
Proof.
unfold initial_state_prop_list.
auto.
Qed.

Definition state_list0 : {s | initial_state_prop_list s} := 
  exist _ Bottom bottom_good.
  
Definition all_bottom (i : index) := Bottom.

Definition decision_list (s : state_list) : option bool :=
  match s with
  | Bottom => None
  | Something c some => Some c
  end.
  
Definition global_decisions (s : state_list) : list (option bool) :=
  match s with 
  | Bottom => []
  | Something c some => List.map decision_list (List.map some index_listing)
  end.

(* Introduce some tie-breaking here? *)

Definition estimator_list (s : state_list) (b : bool) : Prop :=
  let our_count := List.count_occ temp_dec (global_decisions s) (Some b) in
  match s with 
  | Bottom => True
  | Something c some => our_count >= List.count_occ temp_dec (global_decisions s) (Some (negb b))
  end.

Inductive label_list : Type :=
| update (c : bool)
| receive.

Definition update_f (f : index -> state_list) (i : index) (s : state_list) : (index -> state_list) :=
  (fun (j : index) => 
    match eq_dec i j with
    | left e => s
    | _ => f j
    end
  ).

Definition update_list (big : state_list) (news : state_list) (i : index) (value : bool) : state_list :=
  match big with
  | Bottom => Something value (update_f all_bottom i news)
  | Something cv f => Something value (update_f f i news)
  end.

Definition transition_list (l : label_list) (som : state_list * option message) : state_list * option message :=
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
    (som : state_list * option message)
    := 
    let (s, om) := som in
    match l with
    | update c => estimator_list s c
    (* Not actually true, must compare states *)
    | receive => True
    end. 
      


Instance VLSM_list_protocol : VLSM_type message :=
    { state := state_list
    ; label := label_list
    }.
    
Instance LSM_list : VLSM_sign VLSM_list_protocol :=
    { initial_state_prop := initial_state_prop_list
    ; initial_message_prop := initial_message_prop_list
    ; s0 := state_list0
    ; m0 := message00
    ; l0 := receive
    }.

Instance VLSM_list : VLSM LSM_list :=
    { transition := transition_list
      ; valid := valid_list
    }.



