Require Import Bool List Streams Logic.Epsilon.
Import List Notations.
From Casper 
Require Import preamble ListExtras ListSetExtras RealsExtras protocol common definitions vlsm indexed_vlsm.

(* 3.1 Decisions on consensus values *) 

(* Need to add consensus values (and decision functions) to VLSM definitions? *) 
Class consensus_values :=
  { C : Type;
    about_C : exists (c1 c2 : C), c1 <> c2;
  }.

Definition decision {message} (S : LSM_sig message) {CV : consensus_values}
  := @state _ S -> option C.

Section CommuteSingleton.
  
  Context 
    {message : Type}
    {S : LSM_sig message}
    {CV : consensus_values}
    (V : VLSM S).

  (* 3.2.1 Decision finality *)
  (* Program Definition prot_state0 `{VLSM} : protocol_state := 
    exist protocol_state_prop (proj1_sig s0) _.
  Next Obligation.
    red.
    exists None. 
    constructor.
  Defined. *)

  Definition final : decision S -> Prop :=
    fun (D : decision S) => forall (tr : protocol_trace V), 
        forall (n1 n2 : nat) (s1 s2 : state) (c1 c2 : C),
          (trace_nth (proj1_sig tr) n1 = Some s1) ->
          (trace_nth (proj1_sig tr) n2 = Some s2) ->
          (D s1 = (Some c1)) ->
          (D s2 = (Some c2)) ->
          c1 = c2.

  (* 3.3.1 Initial protocol state bivalence *)
  Definition bivalent : decision S -> Prop :=
    fun (D : decision S) =>
      (* All initial states decide on None *) 
      (forall (s0 : state),
        initial_state_prop s0 ->
        D s0 = None) /\
      (* Every protocol trace (already beginning from an initial state) contains a state deciding on each consensus value *) 
      (forall (c : C) ,
          exists (tr : protocol_trace V) (s : state) (n : nat), 
            (trace_nth (proj1_sig tr) n) = Some s /\ D s = (Some c)).

  (* 3.3.2 No stuck states *) 

  Definition stuck_free : decision S -> Prop :=
    fun (D : decision S) =>
      (forall (s : state),
          exists (tr : protocol_trace V) 
                 (decided_state : state)
                 (n_s n_decided : nat)
                 (c : C),
         trace_nth (proj1_sig tr) n_s = Some s /\
         trace_nth (proj1_sig tr) n_decided = Some decided_state /\
         n_decided >= n_s /\
         D decided_state = Some c).

  (* 3.3.3 Protocol definition symmetry *) 
  (* How do we formalize this property set-theoretically? *)

  Definition behavior : decision S -> Prop := 
    fun _ => True.

  Definition symmetric : decision S -> Prop :=
    fun (D : decision S) =>
    exists (f : decision S -> decision S),
      behavior D = behavior (f D).

End CommuteSingleton.

Section CommuteIndexed.

  Context
    {CV : consensus_values}
    {index : Set} `{Heqd : EqDec index}
    {message : Type} 
    {IS : index -> LSM_sig message}
    (IM : forall i : index, VLSM (IS i))
    (Hi : index)
    (constraint : indexed_label IS -> indexed_state IS * option (indexed_proto_message IS) -> Prop)
    (X := indexed_vlsm_constrained Hi IS IM constraint)
    (ID : forall i : index, decision (IS i)).
    
  (* 3.2.2 Decision consistency *)

  Definition consistent :=
      forall (tr : protocol_trace X), 
      forall (n1 n2 : nat),
      forall (j k : index),
      forall (s1 s2 : @state _ (sign X)),
      forall (c1 c2 : C),
      j <> k ->
      trace_nth (proj1_sig tr) n1 = (Some s1) ->
      trace_nth (proj1_sig tr) n2 = (Some s2) ->
      (ID j) (s1 j) = (Some c1) -> 
      (ID k) (s2 k) = (Some c2) -> 
      c1 = c2.

  (** The following is an attempt to include finality in the definition of consistency by dropping the requirement 
      that (j <> k). **)

  Definition final_and_consistent : Prop :=
      forall (tr : protocol_trace X), 
      forall (n1 n2 : nat),
      forall (j k : index),
      forall (s1 s2 : @state _ (sign X)),
      forall (c1 c2 : C),
      trace_nth (proj1_sig tr) n1 = (Some s1) ->
      trace_nth (proj1_sig tr) n2 = (Some s2) ->
      (ID j) (s1 j) = (Some c1) -> 
      (ID k) (s2 k) = (Some c2) -> 
      c1 = c2.

  Lemma final_and_consistent_implies_final : 
      final_and_consistent ->
      forall i : index, final (indexed_vlsm_constrained_projection Hi IS IM constraint i) (ID i).

  Proof.
    unfold final_and_consistent.
    intros.
    unfold final.
    intros.
    Admitted.

  Definition live :=
    forall (tr : protocol_trace X),
      complete_trace_prop X tr -> 
      exists (s : @state _ (sign X)) (n : nat) (i : index) (c : C), 
        trace_nth (proj1_sig tr) n = Some s /\
        (ID i) (s i) = Some c.

End CommuteIndexed.

(* Section 4 *)

Section Estimators.
  Context
    {CV : consensus_values}
    {index : Set} `{Heqd : EqDec index}
    {message : Type} 
    {IS : index -> LSM_sig message}
    (IM : forall i : index, VLSM (IS i))
    (Hi : index)
    (constraint : indexed_label IS -> indexed_state IS * option (indexed_proto_message IS) -> Prop)
    (X := indexed_vlsm_constrained Hi IS IM constraint)
    (ID : forall i : index, decision (IS i))
    (IE : forall i : index, Estimator (@state _ (IS i)) C).

  Definition decision_estimator_property
    (i : index)
    (Xi := indexed_vlsm_constrained_projection Hi IS IM constraint i)
    (Ei := @estimator _ _ (IE i))
    := forall
      (psigma : protocol_state Xi)
      (sigma := proj1_sig psigma)
      (c : C)
      (HD : ID i sigma = Some c)
      (psigma' : protocol_state Xi)
      (sigma' := proj1_sig psigma')
      (Hreach : in_futures Xi psigma psigma')
      (c' : C),
      Ei sigma' c'
      -> c' = c.

  Lemma decision_estimator_finality
    (i : index)
    (Xi := indexed_vlsm_constrained_projection Hi IS IM constraint i)
    : decision_estimator_property i -> final Xi (ID i).
  Proof.
    intros He tr n1 n2 s1 s2 c1 c2 Hs1 Hs2 Hc1 Hc2.
  Admitted.
End Estimators.
