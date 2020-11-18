Require Import
  List Coq.Vectors.Fin FinFun
  Arith.Compare_dec Lia
  Program
  .
Import ListNotations.
From CasperCBC
  Require Import
    Preamble ListExtras FinExtras FinFunExtras
    VLSM.Common VLSM.Composition VLSM.Equivocation
    VLSM.Equivocators.Common VLSM.Equivocators.Projections
    VLSM.Equivocators.MessageProperties
    .

(** ** equivocator composition

Given a composition <<X>> of VLSMs, we can model equivocator behavior by
creating a _equivocator composition_ which replaces each component of <<X>>
with its equivocator version and strengthens the composition constraint to
allow no (additional) equivocations, that is, all messages being received
must have been previously sent by one of the (equivocator) VLSMs in the
composition.
*)

(** ** Extracting equivocator traces from equivocator composition traces
To recover the equivocator trace for the regular composition <<X>> from
the traces of the equivocator composition, we'll assume that only the
first state copy of each machine is observable in the composition
and we ignore the activity corresponding to any other state copy,
including the forks.

This amounts to removing from the trace all transitions in which the
state copy index is not 1, forgetting the additional components of
the label, and keeping only the copy of index 1 for each machine.

*)

Section fully_equivocating_composition.

Context {message : Type}
  {index equiv_index nequiv_index : Type}
  (partition : index -> equiv_index + nequiv_index)
  (rpartition : equiv_index + nequiv_index -> index)
  (Hlpartition : forall i : index, i = rpartition (partition i))
  (Hrpartition : forall i : equiv_index + nequiv_index, partition (rpartition i) = i)
  {IndEqDec : EqDecision index}
  (IM : index -> VLSM message)
  (Hbs : forall i : index, has_been_sent_capability (IM i))
  (i0 : index)
  (X := free_composite_vlsm IM i0)
  .

(* TODO: this follows from sumbool instance *)
Instance partition_eq_dec : EqDecision (equiv_index + nequiv_index).
Proof.
  intros x y.
  destruct (decide (rpartition x = rpartition y)).
  - left. apply (f_equal partition) in e.
    repeat rewrite Hrpartition in e. assumption.
  - right. intro contra; elim n. subst. reflexivity.
Defined.

Definition equivocator_IM
  (i : index)
  : VLSM message
  :=
  match (partition i) with
  | inl _ => equivocator_vlsm (IM i)
  | inr _ => (IM i)
  end.

Lemma equivocator_Hbs
  (i : index)
  :  has_been_sent_capability (equivocator_IM i).
Proof.
  unfold equivocator_IM.
  destruct (partition i) as [eqv | neqv] eqn:Hi.
  - apply equivocator_has_been_sent_capability. apply Hbs.
  - apply Hbs.
Qed.


Context
  (index_listing : list index)
  (finite_index : Listing index_listing)
  .

Definition equivocators_no_equivocations_constraint
  (l : composite_label equivocator_IM)
  (som : composite_state equivocator_IM * option message)
  : Prop
  :=
  no_equivocations equivocator_IM i0 (free_constraint equivocator_IM) finite_index equivocator_Hbs l som.

Definition equivocators_no_equivocations_vlsm
  : VLSM message
  :=
  composite_vlsm equivocator_IM i0 equivocators_no_equivocations_constraint.

Definition equivocators_state_project
  (s : vstate equivocators_no_equivocations_vlsm)
  (i : index)
  : vstate (IM i)
  :=
  match (partition i) as s1
    return (vstate match s1 with
         | inl _ => equivocator_vlsm (IM i)
         | inr _ => IM i
         end -> vstate (IM i))
  with
  | inl _ =>
      fun si0 : vstate (equivocator_vlsm (IM i)) =>
      projT2 si0 (of_nat_lt (Hzero (IM i) si0))
  | inr _ => fun si0 : vstate (IM i) => si0
  end (s i).

Definition equivocators_label_project
  (l : vlabel equivocators_no_equivocations_vlsm)
  : option (vlabel X)
  :=
  let (i, li) := l in
  match (partition i) as s1
    return (vlabel match s1 with
         | inl _ => equivocator_vlsm (IM i)
         | inr _ => IM i
         end -> option (vlabel X))
  with
  | inl _ =>
      fun li0 : vlabel (equivocator_vlsm (IM i)) =>
      let (lj, dj) := li0 in
      match dj with
      | Existing _ 0 false =>
        Some (existT _ i lj)
      | _ => None
      end
  | inr _ => fun li0 : vlabel (IM i) =>
    Some (existT _ i li0)
  end li.

Definition equivocators_transition_item_project
  (item : vtransition_item equivocators_no_equivocations_vlsm)
  : option (vtransition_item X)
  :=
  match item with {| l := el; input := iom; output := oom; destination := s |} =>
    match  equivocators_label_project el with
    | None => None
    | Some lx =>
      let sx := equivocators_state_project s in
      Some {| l := lx; input := iom; output := oom; destination := sx |}
    end
  end.

Definition equivocators_trace_project
  (tr : list (vtransition_item equivocators_no_equivocations_vlsm))
  : list (vtransition_item X)
  := map_option equivocators_transition_item_project tr.

Lemma equivocators_initial_state_project
  (es : vstate equivocators_no_equivocations_vlsm)
  (Hes : vinitial_state_prop equivocators_no_equivocations_vlsm es)
  : vinitial_state_prop X (equivocators_state_project es).
Proof.
Admitted.

Lemma equivocators_protocol_state_project
  (es : vstate equivocators_no_equivocations_vlsm)
  (om : option message)
  (Hes : protocol_prop equivocators_no_equivocations_vlsm (es, om))
  : protocol_state_prop X (equivocators_state_project es)
  /\ option_protocol_message_prop X om.
Proof.
Admitted.

Lemma equivocators_protocol_trace_project
  (is : vstate equivocators_no_equivocations_vlsm)
  (tr : list (vtransition_item equivocators_no_equivocations_vlsm))
  (Htr : finite_protocol_trace_from equivocators_no_equivocations_vlsm is tr)
  : finite_protocol_trace_from X
    (equivocators_state_project is) (equivocators_trace_project tr).
Proof.
Admitted.
  

End fully_equivocating_composition.
