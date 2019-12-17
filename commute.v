Require Import Bool List Streams Logic.Epsilon.
Import List Notations.
From Casper 
Require Import preamble ListExtras ListSetExtras RealsExtras protocol common definitions vlsm indexed_vlsm.

(* 3.1 Decisions on consensus values *) 

(* Need to add consensus values (and decision functions) to VLSM definitions? *) 
Class VLSM_plus `{VLSM} :=
  { C : Type;
    about_C : exists (c1 c2 : C), c1 <> c2;
  }.

Definition decision `{VLSM_plus} : Type := protocol_state -> option C -> Prop. 

(* 3.2.1 Decision finality *)
Program Definition prot_state0 `{VLSM} : protocol_state := 
  exist protocol_state_prop (proj1_sig s0) _.
Next Obligation.
  red.
  exists None. 
  constructor.
Defined.

Definition Trace_nth `{VLSM} (tr : Trace)
  : nat -> option state :=
  fun (n : nat) =>
    match tr with
    | Finite ls => option_map mid (nth_error ls n)
    | Infinite st => Some (mid (Str_nth n st))
   end. 

Definition final `{VLSM_plus} : decision -> Prop :=
  fun (D : decision) => forall (tr : Trace), 
      forall (n1 n2 : nat) (c1 c2 : option C),
        (D (Trace_nth tr n1) c1 -> c1 <> None) ->
        (D (Trace_nth tr n1) c2 -> c2 <> None) ->
        c1 = c2.

(* 3.2.2 Decision consistency *)
Definition in_trace `{VLSM} : protocol_state -> Trace -> Prop :=
  fun (s : protocol_state) (tr : Trace) => exists (n : nat), Trace_nth tr n = s.

Definition consistent
  {index : Set}
  {message : Type}
  `{VLSM_plus}
  (IS : index -> LSM_sig message)
  (IM : forall i : index, @VLSM message (IS i))
  (ID : index -> decision)
  : Prop
  :=
    (* Assuming we want traces of the overall protocol *)
    forall (tr : protocol_trace) (s : protocol_state),
      in_trace s tr ->
      forall (n1 n2 j k : index),
      exists (c1 c2 : C),
        (ID n1) s (Some c1) -> (ID n2) s (Some c2) ->
        forall (c : C),
          (ID n1) s (Some c) <-> (ID n2) s (Some c).       
  
(* 3.3.1 Initial protocol state bivalence *)
Definition bivalent `{VLSM_plus} : decision -> Prop :=
  fun (D : decision) =>
    (* All initial states decide on None *) 
    (forall (s0 : protocol_state),
      initial_state_prop (proj1_sig s0) ->
      D s0 None) /\
    (* Every protocol trace (already beginning from an initial state) contains a state deciding on each consensus value *) 
    (forall (c : C) (tr : protocol_trace),
        exists (s : protocol_state) (n : nat), 
          (Trace_nth tr n) = s /\ D s (Some c)).

(* 3.3.2 No stuck states *) 
Definition stuck_free `{VLSM_plus} : decision -> Prop :=
  fun (D : decision) =>
    (exists (s : protocol_state),
        forall (tr : protocol_trace_from (fun s => s = s)) (n : nat),
            D (Trace_nth tr n) None) -> False. 

(* 3.3.3 Protocol definition symmetry *) 
(* How do we formalize this property set-theoretically? *)
Definition behavior `{VLSM_plus} : decision -> Prop := fun _ => True. 
Definition symmetric `{VLSM_plus} :=
  forall (D : decision),
  exists (f : decision -> decision),
    behavior D = behavior (f D). 

(* 3.4 Liveness *) 
Definition live `{VLSM_plus} : (nat -> VLSM_plus) -> (nat -> decision) -> Prop :=
  fun (IS : nat -> VLSM_plus) (ID : nat -> decision) =>
    (* Here we want traces starting at the initial states *)
    forall (tr : protocol_trace),
      complete_trace_prop tr -> 
      exists (i n : nat) (c : C),
        (ID i) (Trace_nth tr n) (Some c). 

(* Section 4 *) 



  
