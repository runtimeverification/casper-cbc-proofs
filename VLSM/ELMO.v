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
