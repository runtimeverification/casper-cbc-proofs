Require Import List ListSet.

Import ListNotations.

From CasperCBC
  Require Import
    Lib.Preamble
    VLSM.Common
    CBC.Common
    CBC.Equivocation
    Validator.State
    Validator.Equivocation
    .

Section CompositeClient.

(** * Full-node client as a VLSM

This section defines a full-node client as a VLSM.
The full node client does not produce messages, but incorporates received
messages, implementing a limited equivocation tolerance policy.
*)

  Context
    {C V : Type}
    {about_C : StrictlyComparable C}
    {about_V : StrictlyComparable V}
    {Hmeasurable : Measurable V}
    {Hrt : ReachableThreshold V}
    (message := State.message C V)
    .

  (* 2.5.1 Minimal full client protocol: Client2 *)
  Definition label2 : Type := unit.

  Definition vtransition2
    (l : unit)
    (sm : state C V * option message)
    : state C V * option message
    :=
    let (s, om) := sm in
    let (msgs, final) := s in
    match om with
    | None => pair s None
    | Some msg => pair (pair (set_add compare_eq_dec msg msgs) final)  None
    end.

  Definition not_heavy
    :=
    @CBC.Equivocation.set_not_heavy _ (full_node_equivocation C V ).

  Definition valid_client2
    (_ : unit)
    (som : state C V * option message)
    :=
    let (s, om) := som in
    match om with
    | None => True
    | Some msg =>
      incl (get_message_set (unmake_justification (get_justification msg))) (get_message_set s)
      /\ not_heavy (set_add compare_eq_dec msg (get_message_set s))
    end.

  Instance VLSM_type_full_client2 : VLSM_type message :=
    { state := state C V
    ; label := label2
    }.

  Definition initial_state_prop
    (s : state C V)
    : Prop
    :=
    s = pair [] None.

  Definition state0 : {s | initial_state_prop s} :=
    exist _ (pair [] None) eq_refl.

  Definition initial_message_prop (m : message) : Prop := False.

  Instance LSM_full_client2 : VLSM_sign VLSM_type_full_client2 :=
    { initial_state_prop := initial_state_prop
    ; initial_message_prop := initial_message_prop
    ; s0 := state0
    ; m0 := State.message0
    ; l0 := tt
    }.

  Definition VLSM_full_client2_machine  : VLSM_class LSM_full_client2 :=
    {| transition := vtransition2
      ; valid := valid_client2
    |}.

  Definition VLSM_full_client2 : VLSM message := mk_vlsm VLSM_full_client2_machine.

End CompositeClient.
