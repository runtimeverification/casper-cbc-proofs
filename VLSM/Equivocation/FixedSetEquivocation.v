From Coq Require Import List ListSet FinFun.
Import ListNotations.

From CasperCBC Require Import
    Lib.Preamble Lib.ListExtras
    VLSM.Common
    VLSM.Equivocation
    VLSM.Composition
    VLSM.Equivocation.KnownEquivocators
    VLSM.SubProjectionTraces
    .

Section fixed_equivocation_without_fullnode.

(**
In this section we define fixed equivocation for the regular composition.
*)

Context
  {message : Type}
  {index : Type}
  {IndEqDec : EqDecision index}
  (IM : index -> VLSM message)
  (Hbs : forall i : index, has_been_sent_capability (IM i))
  (Hbr : forall i : index, has_been_received_capability (IM i))
  (equivocating : set index)
  (Hi0_equiv : equivocating <> [])
  (i0 : Inhabited index := @SubProjectionTraces.i0 index equivocating Hi0_equiv)
  (X := free_composite_vlsm IM)
  {index_listing : list index}
  (finite_index : Listing index_listing)
  (X_has_been_sent_capability : has_been_sent_capability X := free_composite_has_been_sent_capability IM finite_index Hbs)
  (X_has_been_received_capability : has_been_received_capability X := free_composite_has_been_received_capability IM finite_index Hbr)
  (X_has_been_observed_capability : has_been_observed_capability X := has_been_observed_capability_from_sent_received X)
  (index_equivocating_prop : index -> Prop := sub_index_prop equivocating)
  (equivocating_index : Type := sub_index equivocating)
  (equivocating_i0 : Inhabited equivocating_index := sub_index_i0 equivocating Hi0_equiv)
  (equivocating_IM := sub_IM IM equivocating)
  (equivocating_index_eq_dec : EqDecision equivocating_index := sub_index_eq_dec equivocating)
  (free_equivocating_vlsm_composition : VLSM message := free_composite_vlsm equivocating_IM)
  .

Existing Instance X_has_been_observed_capability.

(**
[free_equivocating_vlsm_composition] is the free composition of the subset of
nodes which are allowed to equivocate.

[pre_loaded_free_equivocating_vlsm_composition] adds to that composition as initial
messages all initial messages of the full composition, along with those given by
the predicate argument @messageSet@.
*)
Definition pre_loaded_free_equivocating_vlsm_composition
  (messageSet : message -> Prop)
  := pre_loaded_vlsm free_equivocating_vlsm_composition
      (fun m => messageSet m \/ vinitial_message_prop X m).

Context
  {validator : Type}
  .

(**
The fixed equivocation constraint for the regular composition of nodes
stipulates that a message can be received either if receiving it satisfies
the [no_additional_equivocations_constraint] (message [has_been_observed],
or it has the [initial_message_prop]erty), or it can be emited by the
free composition of equivocators pre=loaded with with messages producing
[no_additional_equivocations] for the current state.
*)
Definition fixed_equivocation_constraint
  (l : composite_label IM)
  (som : composite_state IM * option message)
  : Prop
  :=
  no_additional_equivocations_constraint X l som \/
  let (s, om) := som in
  exists m : message, om = Some m /\
  can_emit (pre_loaded_free_equivocating_vlsm_composition (no_additional_equivocations X s)) m.

Existing Instance i0.

(** Composition of regular VLSMs under the [fixed_equivocation_constraint].
*)
Definition fixed_equivocation_vlsm_composition : VLSM message
  := composite_vlsm IM fixed_equivocation_constraint.

End fixed_equivocation_without_fullnode.

(*
Section known_equivocators_fixed_set.

Context
  {message : Type}
  {index : Type}
  {IndEqDec : EqDecision index}
  {index_listing : list index}
  (finite_index : Listing index_listing)
  (IM : index -> VLSM message)
  (Hbs : forall i, has_been_sent_capability (IM i))
  (Hbr : forall i, has_been_received_capability (IM i))
  (Hbo := fun i => has_been_observed_capability_from_sent_received (IM i))
  (i0 : Inhabited index)
  (Free := free_composite_vlsm IM)
  (Free_has_been_sent_capability : has_been_sent_capability Free := free_composite_has_been_sent_capability IM finite_index Hbs)
  (Free_has_been_received_capability : has_been_received_capability Free := free_composite_has_been_received_capability IM finite_index Hbr)
  (Free_has_been_observed_capability : has_been_observed_capability Free := has_been_observed_capability_from_sent_received Free)
  (sender : message -> option index)
  (globally_known_equivocators : composite_state IM -> set index)
  {Hknown_equivocators : known_equivocators_capability IM i0 Hbs Hbr index  (fun i => i) sender globally_known_equivocators}
  (constraint : composite_label IM -> composite_state IM * option message -> Prop)
  (X := composite_vlsm IM constraint)
  .

Existing Instance Free_has_been_sent_capability.

Definition known_equivocators_fixed_equivocation_constraint
  (s : composite_state IM)
  (ke := globally_known_equivocators s)
  : composite_label IM -> composite_state IM * option message -> Prop
  :=
  match null_dec ke with
  | left _ => no_equivocations Free
  | right n => fixed_equivocation_constraint IM Hbs Hbr ke n finite_index
  end.

Definition known_equivocators_fixed_equivocation_additional_constraint
  (base_state : composite_state IM)
  (l : composite_label IM)
  (som : composite_state IM * option message)
  : Prop
  := constraint l som /\ known_equivocators_fixed_equivocation_constraint base_state l som.

Lemma mine
  s0 s tr
  (Htr : finite_protocol_trace_init_to X s0 s tr)
  (Y := composite_vlsm IM (known_equivocators_fixed_equivocation_additional_constraint s))
  : finite_protocol_trace_init_to Y s0 s tr.
Proof.
  destruct Htr as [Htr Hinit].
  split; [| assumption]. clear Hinit.
  induction Htr.


End known_equivocators_fixed_set.
*)