Require Import Reals Bool Relations RelationClasses List ListSet Setoid Permutation EqdepFacts ChoiceFacts.
Import ListNotations.
From CasperCBC
Require Import Lib.Preamble Lib.ListExtras Lib.ListSetExtras Lib.RealsExtras CBC.Protocol CBC.Definitions.

Definition reach_one `{CBC_protocol_eq} (sigma1 sigma2 : pstate) : Prop :=
  sigma1 <> sigma2 /\
  pstate_rel sigma1 sigma2 /\
  forall sigma,
    pstate_rel sigma1 sigma
    -> pstate_rel sigma sigma2
    -> sigma = sigma1 \/ sigma = sigma2.

Context `{CBC_protocol_eq}.

Definition pred : Type := pstate -> Prop.

Definition AX (P : pred) (s : pstate) : Prop :=
  forall s', reach_one s s' -> P s'.
Definition EX (P : pred) (s : pstate) : Prop :=
  exists s', reach_one s s' /\ P s'.
Inductive AG (P : pred) (s : pstate) : Prop :=
| AG_rule : P s -> AX (AG P) s -> AG P s.
Inductive EG (P : pred) (s : pstate) : Prop :=
| EG_rule : P s -> EX (EG P) s -> EG P s.
Inductive AF (P : pred) (s : pstate) : Prop :=
| AF_now : P s -> AF P s
| AF_later : AX (AF P) s -> AF P s.
Inductive EF (P : pred) (s : pstate) : Prop :=
| EF_now : P s -> EF P s
| EF_later : EX (EF P) s -> EF P s.

(* Binary consensus values are exclusive *)
Parameter is_zero : pred.
Definition is_one : pred := fun s => is_zero s -> False.

Definition decided (P : pred) : pstate -> Prop :=
  fun s => AG P s.
Definition not_decided (P : pred) : pstate -> Prop :=
  fun s => decided P s -> False.
(* "locked on 0 : all execution traces from s eventually decide 0" *)
Definition locked_on (P : pred) : pstate -> Prop :=
  fun s => AF (decided P) s.
Definition not_locked_on (P : pred) : pstate -> Prop :=
  fun s => locked_on P s -> False.
(* "bivalent: state has future decided 0 and future decided 1" *)
Definition bivalent : pstate -> Prop :=
  fun s => EF (decided is_zero) s /\ EF (decided is_one) s.
(* "stuck: s not decided 0 or decided 1 and there is no future of s that is decided 0 or decided 1" *)
Definition stuck : pstate -> Prop :=
  fun s => (not_decided is_zero s \/ not_decided is_one s) /\
        (EF (decided is_zero) s \/ EF (decided is_one) s -> False).
(* "locked off 0: no future is decided 0" *)
Definition locked_off (P : pred) : pstate -> Prop :=
  fun s => EF (decided P) s -> False.
Definition not_locked_off (P : pred) : pstate -> Prop :=
  fun s => locked_off P s -> False.

Theorem no_stuck_states :
  forall (s : pstate), stuck s -> False.
Admitted.

Theorem exists_bivalent_state :
  exists (s : pstate), bivalent s.
Admitted.

Goal forall (s : pstate), locked_on is_zero s -> decided is_zero s.
Admitted.

Goal forall (s : pstate), not_locked_on is_zero s -> not_locked_on is_one s -> bivalent s.
Admitted.

Goal forall (s : pstate), not_decided is_zero s -> not_decided is_one s -> bivalent s.
Admitted.

