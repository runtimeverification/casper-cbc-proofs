From Coq Require Import ssreflect ssrfun ssrbool.

Require Import
  List Coq.Vectors.Fin
  Arith.Compare_dec Lia
  Program Reals Lra ListSet Nat
  Coq.Logic.FinFun
  .
Import ListNotations.
From CasperCBC
  Require Import
    Preamble
    Lib.Measurable
    VLSM.Common
    VLSM.Composition
    .

Require Import List.
    
Inductive Label := Receive | Send.

Inductive Prestate : Type :=
| Cprestate: list Observation -> Prestate
with
Observation : Type :=
| Cobservation: Label -> Premessage -> nat -> Observation
with
Premessage : Type :=
| Cpremessage: Prestate -> nat -> Premessage
.

Instance Label_eqdec : EqDecision Label.
Proof.
  intros l1 l2.
  unfold Decision.
  decide equality.
Qed.

 

Lemma Prestate_eqdec : forall (s1 s2 : Prestate), {s1 = s2} + {s1 <> s2}
with  Observation_eqdec : forall (o1 o2 : Observation), {o1 = o2} + {o1 <> o2}
with  Premessage_eqdec : forall (m1 m2 : Premessage), {m1 = m2} + {m1 <> m2}.
Proof.
  decide equality. decide equality. decide equality. decide equality.
  decide equality. decide equality. decide equality.
Qed.

Instance Prestate_eqdec' : EqDecision Prestate.
Proof.
  intros x y.
  apply Prestate_eqdec.
Qed.

Instance Observation_eqdec' : EqDecision Observation.
Proof.
  intros x y.
  apply Observation_eqdec.
Qed.

Instance Premessage_eqdec' : EqDecision Premessage.
Proof.
  intros x y.
  apply Premessage_eqdec.
Qed.

Definition dummy_prestate := Cprestate [].
Definition dummy_premessage := Cpremessage dummy_prestate 0.
Definition dummy_observation := Cobservation Receive dummy_premessage 0.


Definition observationsOf (prs : Prestate) : list Observation :=
  match prs with
  | Cprestate l => l
  end.

Definition labelOf (ob : Observation) : Label :=
  match ob with
  | Cobservation lbl _ _ => lbl
  end.

Definition messageOf (ob : Observation) : Premessage :=
  match ob with
  | Cobservation _ msg _ => msg
  end.

Definition witnessOf (ob : Observation) : nat :=
  match ob with
  | Cobservation _ _ w => w
  end.

Definition stateOf (m : Premessage) : Prestate :=
  match m with
  | Cpremessage s _ => s
  end.

Definition authorOf (m : Premessage) : nat :=
  match m with
  | Cpremessage _ a => a
  end.


Instance elmo_type : VLSM_type Premessage :=
  {| state := Prestate;
     Common.label := Label;
  |}.

Definition elmo_state : Type := @state Premessage elmo_type.

Definition elmo_initial_state_prop (ps : elmo_state) : Prop :=
  observationsOf ps = [].

Definition elmo_initial_state
  := sig elmo_initial_state_prop.

Definition elmo_s0 : elmo_initial_state.
Proof.
  unfold elmo_initial_state.
  exists (Cprestate []).
  unfold elmo_initial_state_prop.
  reflexivity.
Defined.

Definition elmo_m0 : Premessage := Cpremessage (Cprestate []) 0.

Definition elmo_sig : VLSM_sign elmo_type :=
  {| initial_state_prop := elmo_initial_state_prop
     ; s0 := elmo_s0
     ; initial_message_prop := (fun x => False)
     ; m0 := elmo_m0
     ; l0 := Receive
     ;
  |}.


(* Check that every message received or sent in m has been received in the prefix by the component *)
Definition fullNode (m : Premessage) (prefix: list Observation) (component: nat) : bool :=
  fold_right andb true
             (map (fun (ob2 : Observation) =>
                     match (labelOf ob2) with
                     | Receive =>
                       if
                         (In_dec Observation_eqdec (Cobservation Receive (messageOf ob2) component) prefix)
                       then true else false
                     | Send => false
                     end
                  )
                  (observationsOf (stateOf m))
             ).


Definition nth_update {A : Type} (l : list A) (idx : nat) (v : A) : list A :=
  firstn idx l ++ cons v (skipn (S idx) l).

Program Definition update
           (m : Premessage)
           (component : nat)
           (weights : list pos_R)
           (treshold : R)
           (curState : list Prestate)
           (curEq : set nat)
  : bool * (list Prestate) * (set nat) :=
  let p := stateOf m in
  let a := authorOf m in
  let lp := length (observationsOf p) in
  let ca := nth a curState dummy_prestate in
  let la := length (observationsOf (ca)) in
  if andb (la <=? lp)
          (bool_decide ((firstn la (observationsOf p))=(observationsOf ca))) then
    (true,
     nth_update curState a (Cprestate (observationsOf p ++ [Cobservation Send m a])),
     curEq)
  else
    if andb (S lp <=? la)
            (andb
               (bool_decide ((firstn lp (observationsOf ca))=(observationsOf p)))
               (bool_decide ((nth lp (observationsOf ca) dummy_observation)=(Cobservation Send m a)))) then
      (true, curState, curEq)
    else
      let newEq := curEq in
      if (Rlt_dec (@sum_weights _ (Build_Measurable _ (fun idx => nth idx weights (exist _ 1%R _))) newEq) treshold) then
        (false, curState, curEq)
      else
        (true, curState, newEq).
Next Obligation.
  lra.
Defined.


Definition isProtocol_step (component : nat) (weights : list pos_R) (treshold : R)
           (args : bool * nat * list Observation * list Prestate * set nat) (ob : Observation)
  : bool * nat * list Observation * list Prestate * set nat
  :=
    let: (result, i, observations, curState, curEq) := args in
    match result with
    | false => args
    | true =>
      let l := labelOf ob in
      let m := messageOf ob in
      let p := stateOf m in
      let a := authorOf m in
      let w := witnessOf ob in
      let prefix := firstn i observations in
      let i := S i in
      (* w <> component *)
      if negb (bool_decide (w=component)) then
        (false, i, observations, curState, curEq)
      else (* w = component *)
        if bool_decide (a=component) then
          match l with
          | Send =>
            let result := bool_decide (observationsOf p = prefix) in
            (result, i, observations, curState, curEq)
          | Receive =>
            let result := bool_decide (In (Cobservation Send m component) prefix) in
            (result, i, observations, curState, curEq)
          end
        else
          (* a <> component *)
          match l with
          | Send =>
            let result := false in
            (result, i, observations, curState, curEq)
          | Receive =>
            if negb (fullNode m prefix component) then
              let result := false in
              (result, i, observations, curState, curEq)
            else
              let: (result, curState, curEq) := update m component weights treshold curState curEq in
              (result, i, observations, curState, curEq)
          end 
    end.

Definition isProtocol
           (prestate : Prestate)
           (component : nat)
           (weights : list pos_R)
           (treshold: R) : bool
  :=
    let initialState := map (fun x => Cprestate nil) weights in
    let initialEq := @nil nat in
    let result := (fold_left (isProtocol_step component weights treshold) (observationsOf prestate) (true, 0, observationsOf prestate, initialState, initialEq )) in
    fst (fst (fst (fst result))).

Definition elmo_valid
           (weights : list pos_R)
           (treshold : R)
           (label : Label)
           (bsom : Prestate * option Premessage)
  : bool :=
  let: (state, message) := bsom in
  match label,message with
  | Send, None => true
  | Send, Some _ => false
  | Receive, None => false
  | Receive, Some m => isProtocol (stateOf m) (authorOf m) weights treshold
  end.

Definition elmo_transition
           (component : nat)
           (weights : list pos_R)
           (treshold : R)
           (label : Common.label)
           (bsom : Prestate * option Premessage)
  : Prestate * option Premessage
  :=
    let: (state, message) := bsom in
    match label, message with
    | Send, Some _ => (state, None)
    | Send, None
      => let m := Cpremessage state component in
         let ob := Cobservation Send m component in
         let s := Cprestate (observationsOf state ++ [ob]) in
         (s, Some m)
    | Receive, None
      => (state, None)
    | Receive, Some msg
      => let ob := Cobservation Receive msg component in
         let s := Cprestate (observationsOf state ++ [ob]) in
         (s, None)
    end.

(* TODO move to Lib/ListExtras.v *)
Fixpoint zip_with {A B C : Type} (f : A -> B -> C) (l1 : list A) (l2 : list B) : list C :=
  match l1 with
  | [] => []
  | x::xs =>
    match l2 with
    |  [] => []
    |  y::ys => (f x y) :: zip_with f xs ys
    end
  end.

Definition elmo_vlsm_machine (component : nat) (weights : list pos_R) (treshold : R)
  : @VLSM_class Premessage elmo_type elmo_sig
  :=
    {| valid := elmo_valid weights treshold
       ; transition := elmo_transition component weights treshold
    |}.


(* m1 is a prefix of m2 *)
Definition is_prefix_of (m1 m2 : Premessage) : Prop :=
  let s1 := stateOf m1 in
  let s2 := stateOf m2 in
  observationsOf s1 = firstn (length (observationsOf s1)) (observationsOf s2).

Lemma is_prefix_of_dec : RelDecision is_prefix_of.
Proof.
  intros m1 m2.
  unfold is_prefix_of.
  apply list_eq_dec.
  apply Observation_eqdec.
Qed.

Definition equivocation_evidence (m1 m2 : Premessage) : Prop :=
  authorOf m1 = authorOf m2 /\
  ~ is_prefix_of m1 m2 /\
  ~ is_prefix_of m2 m1.

Instance equivocation_evidence_dec : RelDecision equivocation_evidence.
Proof.
  intros m1 m2.
  unfold equivocation_evidence.
  apply Decision_and.
  { unfold Decision. decide equality. }
  apply Decision_and; apply Decision_not; apply is_prefix_of_dec.
Qed.

(* `component` is equivocating and we have an evidence in the state `s` (of another component) *)
Definition is_equivocator (s : Prestate) (component : nat) : bool :=
  let obs := observationsOf s in
  existsb
    (fun ob1 =>
       existsb
         (fun ob2 =>
            bool_decide (labelOf ob1 = Receive) &&
            bool_decide (labelOf ob2 = Receive) &&
            bool_decide (authorOf (messageOf ob1) = component) &&
            bool_decide (authorOf (messageOf ob2) = component) &&
            bool_decide (equivocation_evidence (messageOf ob1) (messageOf ob2))
         )
         obs
    )
    obs.

Section composition.

  Context
    (weights : list pos_R)
    (treshold : R)
    (index : Type)
    {i0 : Inhabited index}
    {IndEqDec : EqDecision index}
    (indices : list index)
    (finite_index : Listing indices)
    (indices_weights_eqlenght : length indices = length weights)
  .

  Fixpoint index_to_component' (idx : index) (component : nat) (indices : list index) :=
    match indices with
    | [] => component
    | x::xs
      => if decide (x = idx)
         then component
         else index_to_component' idx (S component) xs
    end.

  Lemma index_to_component'_valid (idx : index) (component : nat) (indices': list index) :
    In idx indices' -> index_to_component' idx component indices' < length indices' + component.
  Proof.
    intros Hin.
    move: component.
    induction indices'.
    - simpl in Hin. inversion Hin.
    - intros component.
      simpl.
      destruct (decide (a = idx)); simpl.
      + lia.
      + simpl in Hin.
        destruct Hin as [Haeqidx|Hin].
        * contradiction.
        * specialize (IHindices' Hin).
          specialize (IHindices' (S component)).
          lia.
  Qed.

  Definition index_to_component (idx : index) :=
    index_to_component' idx 0 indices.

  Lemma index_to_component_valid (idx : index) : index_to_component idx < length indices.
  Proof.
    pose proof (P := index_to_component'_valid).
    specialize (P idx 0 indices).
    rewrite Nat.add_0_r in P.
    apply P.
    apply finite_index.
  Qed.
  

  Definition IM' (i : index) := elmo_vlsm_machine (index_to_component i) weights treshold.
  Definition IM (i : index) := mk_vlsm (IM' i).

  (* TODO *)
  Definition composition_constraint
             (cl : composite_label IM)
             (sm : composite_state IM * option Premessage) : Prop
    := let cs := fst sm in
       let om := snd sm in
       match om with
       | None => True
       | Some m =>
         let states := map cs indices in
         let transitions := map (fun i => @transition _ _ _ (IM' i)) indices in
         let new_states := zip_with (fun s t => t Receive (s, Some m))
                                    states
                                    transitions in
         True
       end.
  
  
  Definition composite_elmo := @composite_vlsm Premessage index IndEqDec IM i0 composition_constraint.

End composition.
