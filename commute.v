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

Definition decision `{VLSM_plus} : Type := state -> option C -> Prop. 

(* 3.2.1 Decision finality *)
(* Program Definition prot_state0 `{VLSM} : protocol_state := 
  exist protocol_state_prop (proj1_sig s0) _.
Next Obligation.
  red.
  exists None. 
  constructor.
Defined. *)

Definition final `{VLSM_plus} : decision -> Prop :=
  fun (D : decision) => forall (tr : protocol_trace), 
      forall (n1 n2 : nat) (s1 s2 : state) (c1 c2 : C),
        (trace_nth (proj1_sig tr) n1 = Some s1) ->
        (trace_nth (proj1_sig tr) n2 = Some s2) ->
        (D s1 (Some c1)) ->
        (D s2 (Some c2)) ->
        c1 = c2.

(* 3.2.2 Decision consistency *)
Definition in_trace `{VLSM} : state -> Trace -> Prop :=
  fun (s : state) (tr : Trace) => exists (n : nat), trace_nth tr n = Some s.

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
    forall (tr : protocol_trace) (s : state),
      in_trace s (proj1_sig tr) ->
      forall (n1 n2 j k : index),
      exists (c1 c2 : C),
        (ID n1) s (Some c1) -> (ID n2) s (Some c2) ->
        forall (c : C),
          (ID n1) s (Some c) <-> (ID n2) s (Some c).       
  
(* 3.3.1 Initial protocol state bivalence *)
Definition bivalent `{VLSM_plus} : decision -> Prop :=
  fun (D : decision) =>
    (* All initial states decide on None *) 
    (forall (s0 : state),
      initial_state_prop s0 ->
      D s0 None) /\
    (* Every protocol trace (already beginning from an initial state) contains a state deciding on each consensus value *) 
    (forall (c : C) (tr : protocol_trace),
        exists (s : state) (n : nat), 
          (trace_nth (proj1_sig tr) n) = Some s /\ D s (Some c)).

(* 3.3.2 No stuck states *) 
(* Definition stuck_free `{VLSM_plus} : decision -> Prop :=
  fun (D : decision) =>
    (exists (s : state),
        forall (tr : trace) (n : nat),
            D (Trace_nth tr n) None) -> False. 
 *)
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
    forall (tr : protocol_trace) (s : state) (n : nat),
      trace_nth (proj1_sig tr) n = Some s ->
      exists (i n : nat) (c : C),
        (ID i) s (Some c). 

(* Section 4 *) 



  
