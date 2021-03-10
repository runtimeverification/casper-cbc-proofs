Require Import
  List Coq.Vectors.Fin
  Arith.Compare_dec Lia
  Program
  .
Import ListNotations.
From CasperCBC
  Require Import
    Preamble
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

Definition elmo_sig : VLSM_sign elmo_type :=
  {| initial_state_prop := elmo_initial_state_prop
     ; s0 := elmo_s0
     ;
  |}.
