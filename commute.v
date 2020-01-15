Require Import Bool List Streams Logic.Epsilon.
Import List Notations.
From Casper 
Require Import preamble ListExtras ListSetExtras RealsExtras protocol common definitions vlsm indexed_vlsm indexed_vlsm_projections.

(* 3.1 Decisions on consensus values *) 

(* Need to add consensus values (and decision functions) to VLSM definitions? *) 
Class consensus_values :=
  { C : Type;
    about_C : exists (c1 c2 : C), c1 <> c2;
  }.


(** TODO: Define projection friendliness **)
(** TODO: Make function **)

Definition decision {message} (S : LSM_sig message) {CV : consensus_values} : Type
  := @state _ S -> option C -> Prop. 

(* 3.2.1 Decision finality *)
(* Program Definition prot_state0 `{VLSM} : protocol_state := 
  exist protocol_state_prop (proj1_sig s0) _.
Next Obligation.
  red.
  exists None. 
  constructor.
Defined. *)

Definition final {message} {S : LSM_sig message} (V : @VLSM message S) {CV : consensus_values}
  : decision S -> Prop :=
  fun (D : decision S) => forall (tr : protocol_trace), 
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
  {CV : consensus_values}
  {index : Set} `{Heqd : EqDec index}
  {message : Type} 
  {IS : index -> LSM_sig message}
  {IM : forall i : index, @VLSM message (IS i)}
  {Hi : index}
  (constraint : indexed_label IS -> indexed_state IS * option (indexed_proto_message IS) -> Prop)
  (X := indexed_vlsm_constrained IM Hi constraint)
  (ID : forall i : index, decision (IS i))
  : Prop
  :=
    (* Assuming we want traces of the overall protocol *)
    forall (tr : @protocol_trace _ _ X) (s : @state _ (sign X)), True.

(**
      in_trace s (proj1_sig tr) ->
      forall (n1 n2 j k : index),
      exists (c1 c2 : C),
        (ID n1) s (Some c1) -> (ID n2) s (Some c2) ->
        forall (c : C),
          (ID n1) s (Some c) <-> (ID n2) s (Some c).    
**)

Definition consistent_mihai
  {CV : consensus_values}
  {index : Set} `{Heqd : EqDec index}
  {message : Type} 
  {IS : index -> LSM_sig message}
  (IM : forall i : index, @VLSM message (IS i))
  (Hi : index)
  (constraint : indexed_label IS -> indexed_state IS * option (indexed_proto_message IS) -> Prop)
  (X := indexed_vlsm_constrained IM Hi constraint)
  (ID : forall i : index, decision (IS i)) : Prop
  :=
    forall (tr : @protocol_trace _ _ X), 
    forall (n1 n2 : nat),
    forall (j k : index),
    forall (s1 s2 : @state _ (sign X)),
    forall (c1 c2 : C),
    j <> k ->
    trace_nth (proj1_sig tr) n1 = (Some s1) ->
    trace_nth (proj1_sig tr) n2 = (Some s2) ->
    (ID j) (@s1 j) (Some c1) -> 
    (ID k) (@s2 k) (Some c2) -> 
    c1 = c2.

(**Like consistent_mihai, but no longer requiring j <> k, which should imply finality in projections**)

Definition final_and_consistent_mihai
  {CV : consensus_values}
  {index : Set} `{Heqd : EqDec index}
  {message : Type} 
  {IS : index -> LSM_sig message}
  (IM : forall i : index, @VLSM message (IS i))
  (Hi : index)
  (constraint : indexed_label IS -> indexed_state IS * option (indexed_proto_message IS) -> Prop)
  (X := indexed_vlsm_constrained IM Hi constraint)
  (ID : forall i : index, decision (IS i)) : Prop
  :=
    forall (tr : @protocol_trace _ _ X), 
    forall (n1 n2 : nat),
    forall (j k : index),
    forall (s1 s2 : @state _ (sign X)),
    forall (c1 c2 : C),
    trace_nth (proj1_sig tr) n1 = (Some s1) ->
    trace_nth (proj1_sig tr) n2 = (Some s2) ->
    (ID j) (@s1 j) (Some c1) -> 
    (ID k) (@s2 k) (Some c2) -> 
    c1 = c2.

Check final_and_consistent_mihai.

Lemma final_and_consistent_implies_consistent 
  {CV : consensus_values}
  {index : Set} `{Heqd : EqDec index}
  {message : Type} 
  {IS : index -> LSM_sig message}
  (IM : forall i : index, @VLSM message (IS i))
  (Hi : index)
  (constraint : indexed_label IS -> indexed_state IS * option (indexed_proto_message IS) -> Prop)
  (X := indexed_vlsm_constrained IM Hi constraint)
  (ID : forall i : index, decision (IS i))
  : 
    final_and_consistent_mihai IM Hi constraint ID ->
    consistent_mihai IM Hi constraint ID.

Proof.
   intros.
   unfold final_and_consistent_mihai in H.
   unfold consistent_mihai.
   intros.
   apply H with (tr := tr )(j := j) (n1 := n1) (n2 := n2) (k := k) (s1 := s1) (s2 := s2).
   - apply H1.
   - apply H2.
   - apply H3.
   - apply H4.
Qed.

Check final.

Lemma final_and_consistent_implies_final
  {CV : consensus_values}
  {index : Set} `{Heqd : EqDec index}
  {message : Type} 
  {IS : index -> LSM_sig message}
  (IM : forall i : index, @VLSM message (IS i))
  (Hi : index)
  (constraint : indexed_label IS -> indexed_state IS * option (indexed_proto_message IS) -> Prop)
  (X := indexed_vlsm_constrained IM Hi constraint)
  (ID : forall i : index, decision (IS i))
  : 
    final_and_consistent_mihai IM Hi constraint ID ->
    forall i : index, final (indexed_vlsm_constrained_projection IM Hi constraint i) (ID i).

Proof.
  unfold final_and_consistent_mihai.
  intros.
  unfold final.
  intros.
  Admitted.
Qed.



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



  
