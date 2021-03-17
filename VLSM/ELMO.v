Require Import
  List Coq.Vectors.Fin
  Arith.Compare_dec Lia
  Program Reals Lra ListSet Nat
  .
Import ListNotations.
From CasperCBC
  Require Import
    Preamble
    Lib.SumWeights
    VLSM.Common
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

Lemma Prestate_eqdec : forall (s1 s2 : Prestate), {s1 = s2} + {s1 <> s2}
with  Observation_eqdec : forall (o1 o2 : Observation), {o1 = o2} + {o1 <> o2}
with  Premessage_eqdec : forall (m1 m2 : Premessage), {m1 = m2} + {m1 <> m2}.
Proof.
  decide equality. decide equality. decide equality. decide equality.
  decide equality. decide equality. decide equality.
Qed.

Definition observations (prs : Prestate) : list Observation :=
  match prs with
  | Cprestate l => l
  end.

Definition label (ob : Observation) : Label :=
  match ob with
  | Cobservation lbl _ _ => lbl
  end.

Definition message (ob : Observation) : Premessage :=
  match ob with
  | Cobservation _ msg _ => msg
  end.

Definition witness (ob : Observation) : nat :=
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


Definition elmo_type : VLSM_type Premessage :=
  {| state := Prestate;
     Common.label := Label;
  |}.

Definition elmo_state : Type := @state Premessage elmo_type.

Definition elmo_initial_state_prop (ps : elmo_state) : Prop :=
  observations ps = [].

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
                     match (label ob2) with
                     | Receive =>
                       if
                         (In_dec Observation_eqdec (Cobservation Receive (message ob2) component) prefix)
                       then true else false
                     | Send => false
                     end
                  )
                  (observations (stateOf m))
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
  let lp := length (observations p) in
  let ca := nth a curState (Cprestate []) in
  let la := length (observations (ca)) in
  if andb (la <=? lp)
          (if (list_eq_dec Observation_eqdec (firstn la (observations p)) (observations ca)) then true else false) then
    (true,
     nth_update curState a (Cprestate (observations p ++ [Cobservation Send m a])),
     curEq)
  else
    if andb (S lp <=? la)
            (andb
               (if (list_eq_dec Observation_eqdec (firstn lp (observations ca)) (observations p)) then true else false)
               (if (Observation_eqdec (nth lp (observations ca) (Cobservation Receive m a) ) (Cobservation Send m a)) then true else false)) then
      (true, curState, curEq)
    else
      let newEq := curEq in
      (*      if (Rlt_dec (sum_weights (map (fun idx => nth idx weights (0%R)) newEq)) treshold) then *)
      if (Rlt_dec (@sum_weights _ (Build_Measurable _ (fun idx => nth idx weights (exist _ 1%R _))) newEq) treshold) then
        (false, curState, curEq)
      else
        (true, curState, newEq).
Next Obligation.
  lra.
Defined.


