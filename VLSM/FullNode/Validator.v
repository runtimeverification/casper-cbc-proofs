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

Section CompositeValidator.

  Context
    {C V : Type}
    {about_C : StrictlyComparable C}
    {about_V : StrictlyComparable V}
    {Hmeasurable : Measurable V}
    {Hrt : ReachableThreshold V}
    {Hestimator : Estimator (state C V) C}
    (message := State.message C V)
    .

  (** * Full-node validator VLSM instance

  Here we define a VLSM for a full-node validator identifying itself as
  <<v>> when sending messages.

  The validator and incorporates messages (sent by other validators), and
  creates and sends new messages proposing consensus values estimated based
  on its current state, signing them with its name and current state.

  Unlike the client, no equivocation check is done within the validator upon
  receiving a new message.
  *)
  Definition labelv : Type := option C.

  Definition vtransitionv
    (v : V)
    (l : labelv)
    (som : state C V * option message)
    : state C V * option message
    :=
    let (s, om) := som in
    let (msgs, final) := s in
    match l with
    | None => match om with
             | None => som
             | Some msg => pair (pair (set_add compare_eq_dec msg msgs) final) None
           end
    | Some c =>
      let msg := (c, v, make_justification s) in
      pair (pair (set_add compare_eq_dec msg msgs) (Some msg)) (Some msg)
    end.

  Definition valid_validator
    (l : labelv)
    (som : state C V * option message)
    : Prop
    :=
    let (s, om) := som in
    match l, om with
    | None, None => True
    | None, Some msg =>
      incl (get_message_set (unmake_justification (get_justification msg))) (get_message_set s)
    | Some c, _ =>
      @estimator (state C V) C Hestimator s c
    end.

  Instance VLSM_type_full_validator : VLSM_type message :=
    { state := state C V
    ; label := labelv
    }.

  Definition initial_state_prop
    (s : state C V)
    : Prop
    :=
    s = pair [] None.

  Definition state0 : {s | initial_state_prop s} :=
    exist _ (pair [] None) eq_refl.

  Definition initial_message_prop (m : message) : Prop := False.

  Instance LSM_full_validator : VLSM_sign VLSM_type_full_validator :=
    { initial_state_prop := initial_state_prop
    ; initial_message_prop := initial_message_prop
    ; s0 := state0
    ; m0 := State.message0
    ; l0 := None
    }.

  Definition VLSM_full_validator_machine (v : V) : VLSM_class LSM_full_validator :=
    {| transition := vtransitionv v
     ; valid := valid_validator
    |}.

  Definition VLSM_full_validator (v : V) : VLSM message :=
    mk_vlsm (VLSM_full_validator_machine v).

End CompositeValidator.
