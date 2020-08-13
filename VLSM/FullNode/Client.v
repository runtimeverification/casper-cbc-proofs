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
    (sm : set message * option message)
    : set message * option message
    :=
    let (msgs, om) := sm in
    match om with
    | None => pair msgs None
    | Some msg => pair (set_add compare_eq_dec msg msgs)  None
    end.

  Definition not_heavy
    :=
    @CBC.Equivocation.set_not_heavy _ (full_node_equivocation C V ).

  Definition valid_client2
    (_ : unit)
    (som : set message * option message)
    :=
    let (msgs, om) := som in
    match om with
    | None => True
    | Some msg =>
      ~In msg msgs
      /\ incl (get_message_set (unmake_justification (get_justification msg))) msgs
      /\ not_heavy (set_add compare_eq_dec msg msgs)
    end.

  Instance VLSM_type_full_client2 : VLSM_type message :=
    { state := set message
    ; label := label2
    }.

  Definition initial_state_prop
    (s : set message)
    : Prop
    :=
    s = [].

  Definition state0 : {s | initial_state_prop s} :=
    exist _ [] eq_refl.

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

  Lemma client_protocol_state_nodup
    (s : set message)
    (Hs : protocol_state_prop (pre_loaded_vlsm VLSM_full_client2) s)
    : NoDup s.
  Proof.
    generalize dependent s.
    apply
      (protocol_state_prop_ind (pre_loaded_vlsm VLSM_full_client2)
        (fun (s : vstate (pre_loaded_vlsm VLSM_full_client2)) =>
          NoDup s
        )
      ); intros.
    - inversion Hs. constructor.
    - destruct Ht as [_ Ht].
      simpl in Ht. unfold vtransition in Ht. simpl in Ht.
      destruct om as [msg|]; inversion Ht.
      * apply set_add_nodup. assumption.
      * subst. assumption.
  Qed.

End CompositeClient.
