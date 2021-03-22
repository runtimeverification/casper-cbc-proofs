Require Import List Streams Nat Bool.
Import ListNotations.
Require Import Logic.FunctionalExtensionality.

Require Import Coq.Logic.FinFun Coq.Logic.Eqdep Coq.Program.Basics List ListSet.

From CasperCBC
  Require Import
    StreamExtras ListExtras Preamble
    VLSM.Common
    VLSM.Plans
    .
(**

This module provides Coq definitions for composite VLSMs and their projections
to components.
*)

Section VLSM_composition.

(**
* VLSM composition

Let us fix a type for <<message>>s, and an <<index>> type for the VLSM components
such that equality on <<index>> is decidable.

*)

  Context {message : Type}
          {index : Type}
          {IndEqDec : EqDecision index}
          (IM : index -> VLSM message)
          .

  Section composite_type.

(**

** The type of a composite VLSM

Let IM be a family of VLSMs indexed by <<index>>. Note that all
[VLSM]s share the same type of <<message>>s.

*)

(**
A [composite_state] is an indexed family of [state]s, yielding for each
index <<n>> a [state] of [type] <<IT n>>, the [VLSM_type] corresponding to
machine <<n>>.

Note that the [composite_state] type is the dependent product type of the
family of [state] types corresponding to each index.
*)
    Definition _composite_state : Type :=
      forall n : index, vstate (IM n).

(**
A [composite_label] is a pair between an index <<N>> and a [label] of <<IT n>>.

Note that the [composite_label] type is the dependent sum of the family of
types <<[@label _ (IT n) | n <- index]>>.
*)
    Definition _composite_label
      : Type
      := sigT (fun n => vlabel (IM n)).

    Definition composite_type : VLSM_type message :=
      {| state := _composite_state
       ; label := _composite_label
      |}.

    Definition composite_state := @state message composite_type.
    Definition composite_label := @label message composite_type.
    Definition composite_transition_item : Type := @transition_item message composite_type.

(**
A very useful operation on [composite_state]s is updating the state corresponding
to a component:
*)
    Definition state_update
               (s : composite_state)
               (i : index)
               (si : vstate (IM i))
               (j : index)
      : vstate (IM j)
      :=
      match decide (j = i) with
      | left e => eq_rect_r (fun i => vstate (IM i)) si e
      | _ => s j
      end.

(**
The next few results describe several properties of the [state_update] operation.
*)
    Lemma state_update_neq
               (s : composite_state)
               (i : index)
               (si : vstate (IM i))
               (j : index)
               (Hneq : j <> i)
      : state_update s i si j = s j.
    Proof.
      unfold state_update. destruct (decide (j = i)); try contradiction. reflexivity.
    Qed.

    Lemma state_update_eq
               (s : composite_state)
               (i : index)
               (si : vstate (IM i))
      : state_update s i si i = si.
    Proof.
      unfold state_update.
      unfold decide, decide_rel.
      rewrite eq_dec_refl. reflexivity.
    Qed.

    Lemma state_update_id
               (s : composite_state)
               (i : index)
               (si : vstate (IM i))
               (Heq : s i = si)
      : state_update s i si = s.
    Proof.
      apply functional_extensionality_dep_good.
      intro j.
      destruct (decide (j = i)).
      - subst. apply state_update_eq.
      - apply state_update_neq. assumption.
    Qed.

    Lemma state_update_twice
               (s : composite_state)
               (i : index)
               (si si': vstate (IM i))
      : state_update (state_update s i si) i si' = state_update s i si'.
    Proof.
      apply functional_extensionality_dep_good.
      intro j.
      destruct (decide (j = i)).
      - subst. rewrite state_update_eq. symmetry. apply state_update_eq.
      - repeat rewrite state_update_neq; try assumption.
        reflexivity.
    Qed.

    Lemma state_update_twice_neq
               (s : composite_state)
               (i j : index)
               (si : vstate (IM i))
               (sj : vstate (IM j))
               (Hij : j <> i)
      : state_update (state_update s i si) j sj
      = state_update (state_update s j sj) i si.
    Proof.
      apply functional_extensionality_dep_good.
      intro k.
      destruct (decide (k = j)); destruct (decide (k = i)); subst
      ; repeat (rewrite state_update_eq ; try (rewrite state_update_neq; try assumption))
      ; try reflexivity.
      repeat (rewrite state_update_neq; try assumption).
      reflexivity.
    Qed.
  End composite_type.

  Section composite_sig.
(**

** The signature of a composite VLSM

Assume an non-empty <<index>> type and let <<IT>> be
an <<index>>ed family of [VLSM_type]s, and for each index <<i>>, let <<IS i>> be
a [VLSM_sign]ature of type <<IT i>>.
*)

    Context `{i0: Inhabited index}.

(**
A [composite_state] has the [initial_state_prop]erty if all of its component
states have the [initial_state_prop]erty in the corresponding component signature.
*)
    Definition composite_initial_state_prop
               (s : composite_state)
      : Prop
      :=
        forall n : index, vinitial_state_prop (IM n) (s n).

    Definition composite_initial_state
      := sig composite_initial_state_prop.

    Definition composite_s0 : composite_initial_state.
    Proof.
      exists (fun (n : index) => proj1_sig (vs0 (IM n))).
      intro i. unfold vs0. destruct s0 as [s Hs]. assumption.
    Defined.

(**
A message has the [initial_message_prop]erty in the [composite_sig]nature
iff it has the [initial_message_prop]erty in any of the component signatures.
*)
    Definition composite_initial_message_prop (m : message) : Prop
      :=
        exists (n : index) (mi : vinitial_message (IM n)), proj1_sig mi = m.

    (* An explicit argument for the initial state witness is no longer required: *)
    Definition composite_m0 : message := vm0 (IM inhabitant).

    Definition composite_l0 : composite_label
      := existT _ inhabitant (vl0 (IM inhabitant)) .

    Definition composite_sig
      : VLSM_sign composite_type
      :=
        {|   initial_state_prop := composite_initial_state_prop
           ; s0 := composite_s0
           ; initial_message_prop := composite_initial_message_prop
           ; m0 := composite_m0
           ; l0 := composite_l0
        |}.

(**
We can always "lift" state <<sj>> from component <<j>> to a composite state by
updating an initial composite state, say [s0], to <<sj>> on component <<j>>.
*)
    Definition lift_to_composite_state
      (j : index)
      (sj : vstate (IM j))
      (s0X := proj1_sig composite_s0)
      : composite_state
      := state_update s0X j sj.

    Definition lift_to_composite_transition_item
      (j : index)
      (item : vtransition_item (IM j))
      (s0X := proj1_sig composite_s0)
      : @transition_item _ composite_type.
    Proof.
      destruct item.
      split.
      - exact (existT _ j l).
      - exact input.
      - exact (lift_to_composite_state j destination).
      - exact output.
    Defined.

    Definition lift_to_composite_state'
      (s : composite_state)
      (j : index)
      (sj : vstate (IM j))
      : composite_state
      := state_update s j sj.

    Definition lift_to_composite_transition_item'
      (s : composite_state)
      (j : index)
      (item : vtransition_item (IM j))
      : @transition_item _ composite_type.
    Proof.
      destruct item.
      split.
      - exact (existT _ j l).
      - exact input.
      - exact (lift_to_composite_state' s j destination).
      - exact output.
    Defined.

    (**
    Composite versions for [plan_item] and [plan].
    *)
    Definition composite_plan_item := @plan_item _ composite_type.
    Definition composite_plan := list composite_plan_item.

    Definition lift_to_composite_plan_item
      (i : index)
      (a : vplan_item (IM i)) :
      composite_plan_item.
    Proof.
      destruct a.
      split.
      - exact (existT _ i label_a).
      - exact input_a.
    Defined.

    Definition lift_to_composite_finite_trace
      (j : index)
      (trj : list (vtransition_item (IM j)))
      : list (@transition_item _ composite_type)
      :=
      List.map (lift_to_composite_transition_item j) trj.

    Definition lift_to_composite_trace
      (j : index)
      (trj : vTrace (IM j))
      : @Trace _ composite_type
      :=
      match trj with
      | Finite s l => Finite (lift_to_composite_state j s) (lift_to_composite_finite_trace j l)
      | Infinite s l => Infinite (lift_to_composite_state j s) (Streams.map (lift_to_composite_transition_item j) l)
      end.

  End composite_sig.

  Section composite_vlsm.
(**

** Constrained VLSM composition

Assume an non-empty <<index>> type, let
<<IT>> be an <<index>>ed family of [VLSM_type]s, and for each index <<i>>, let
<<IS i>> be a [VLSM_sign]ature of type <<IT i>> and <<IM i>> be a VLSM of
signature <<IS i>>.
*)

    Context `{i0 : Inhabited index}.

(**
The [transition] function for the [composite_vlsm] is defined as follows
takes a transition in the VLSM corresponding to the given [composite_label]
and returnes the produced message together with the state updated on that
component:
*)
    Definition composite_transition
      (l : composite_label)
      (som : composite_state * option message)
      : composite_state * option message
      :=
      let (s, om) := som in
      let (i, li) := l in
      let (si', om') := vtransition (IM i) li (s i, om) in
      (state_update s i si',  om').

(**
Given a [composite_label] <<(i, li)>> and a [composite_state]-message
pair <<(s, om)>>, [composite_valid]ity is defined as [valid]ity in
the <<i>>th component <<IM i>>.
*)
    Definition composite_valid
      (l : composite_label)
      (som : composite_state * option message)
      : Prop
      :=
      let (s, om) := som in
      let (i, li) := l in
      vvalid (IM i) li (s i, om).

(**
A <<constraint>> for a composite VLSM is a [valid]ity condition defined
directly on [composite_label]s and [composite_state]s, thus being able to
impose a global condition.

[constrained_composite_valid]ity interposes such a <<constraint>> on top of
the [composite_valid]ity.
*)

    Definition constrained_composite_valid
      (constraint : composite_label -> composite_state * option message -> Prop)
      (l : composite_label)
      (som : composite_state * option message)
      :=
      composite_valid l som /\ constraint l som.

    Definition composite_vlsm_machine
      (constraint : composite_label -> composite_state * option message -> Prop)
      : VLSM_class composite_sig
      :=
      {|  transition := composite_transition
       ;  valid := constrained_composite_valid constraint
      |}.

    Definition composite_vlsm
      (constraint : composite_label -> composite_state * option message -> Prop)
      : VLSM message
      := mk_vlsm (composite_vlsm_machine constraint).

    Lemma composite_transition_state_neq
      {constraint : composite_label -> composite_state * option message -> Prop}
      (l : composite_label)
      (s s' : composite_state)
      (om om' : option message)
      (Ht : protocol_transition (composite_vlsm constraint) l (s, om) (s', om'))
      (i : index)
      (Hi : i <> projT1 l)
      : s' i = s i.
    Proof.
      destruct Ht as [_ Ht]. simpl in Ht. destruct l as (il, l). simpl in Hi.
      destruct (vtransition (IM il) l (s il, om)) as (si', omi') eqn:Ht'.
      inversion Ht. subst omi'. apply state_update_neq. assumption.
    Qed.

    Lemma composite_transition_state_eq
      {constraint : composite_label -> composite_state * option message -> Prop}
      (l : composite_label)
      (s s' : composite_state)
      (om om' : option message)
      (Ht : protocol_transition (composite_vlsm constraint) l (s, om) (s', om'))
      (il := projT1 l)
      : s' il = fst (vtransition (IM il) (projT2 l) (s il, om)).
    Proof.
      destruct Ht as [_ Ht]. simpl in Ht.
      unfold il in *. clear il. destruct l as (il, l). simpl.
      destruct (vtransition (IM il) l (s il, om)) as (si', omi') eqn:Ht'.
      inversion Ht. apply state_update_eq.
    Qed.

    (** Composite versions for the generic [_apply_plan]-related definitions and
    results.
    *)
    Definition composite_apply_plan := (@_apply_plan _ composite_type composite_transition).
    Definition composite_apply_plan_app
      (start : composite_state)
      (a a' : list plan_item)
      : composite_apply_plan start (a ++ a') =
        let (aitems, afinal) := composite_apply_plan start a in
        let (a'items, a'final) := composite_apply_plan afinal a' in
         (aitems ++ a'items, a'final)
      := (@_apply_plan_app _ composite_type composite_transition start a a').
    Definition composite_apply_plan_last
      (start : composite_state)
      (a : list plan_item)
      (after_a := composite_apply_plan start a)
      : last (map destination (fst after_a)) start = snd after_a
      := (@_apply_plan_last _ composite_type composite_transition start a).
    Definition composite_trace_to_plan := (@_trace_to_plan _ composite_type).

    Section constraint_subsumption_part_one.
(**

** Constraint subssumption

A <<constraint1>> is subssumed by <<constraint2>> if <<constraint1> is stronger
than <<constraint2>> for any input.
*)

    Definition constraint_subsumption
        (constraint1 constraint2 : composite_label -> composite_state * option message -> Prop)
        :=
        forall (l : composite_label) (som : composite_state * option message),
          constraint1 l som -> constraint2 l som.

    Context
      (constraint1 constraint2 : composite_label -> composite_state * option message -> Prop)
      (Hsubsumption : constraint_subsumption constraint1 constraint2)
      (X1 := composite_vlsm constraint1)
      (X2 := composite_vlsm constraint2)
      .

(**
Let <<X1>>, <<X2>> be two compositions of the same family of VLSMs but with
constraints <<constraint1>> and <<constraint2>, respectively. Further assume
that <<constraint1>> is subssumed by <<constraint2>>.

We will show that <<X1>> is trace-included into <<X2>> by applying
Lemma [basic_VLSM_inclusion]
*)

(* begin hide *)
    Lemma constraint_subsumption_protocol_valid
      (l : label)
      (s : state)
      (om : option message)
      (Hv : protocol_valid X1 l (s, om))
      : vvalid X2 l (s, om).
    Proof.
      destruct Hv as [Hps [Hopm [Hv Hctr]]].
      split; try assumption.
      apply Hsubsumption.
      assumption.
    Qed.

    Lemma constraint_subsumption_protocol_prop
      (s : state)
      (om : option message)
      (Hps : protocol_prop X1 (s, om))
      : protocol_prop X2 (s, om).
    Proof.
      induction Hps.
      - apply (protocol_initial X2);assumption.
      - apply (protocol_generated X2) with _om _s; try assumption.
        apply constraint_subsumption_protocol_valid.
        apply protocol_generated_valid with _om _s; assumption.
    Qed.

    End constraint_subsumption_part_one.

(**

** Free VLSM composition

The [free_constraint] is defined to be [True] for all inputs.
Thus, the [free_composite_vlsm] is the [composite_vlsm] using the
[free_constraint].
*)

    Definition free_constraint
      (l : composite_label)
      (som : composite_state * option message)
      : Prop
      := True.

    Definition free_composite_vlsm : VLSM message
      := composite_vlsm free_constraint.

    Lemma constraint_free_protocol_prop
      (constraint : composite_label -> composite_state * option message -> Prop)
      (som : state * option message)
      (Hsom : protocol_prop (composite_vlsm constraint) som)
      : protocol_prop free_composite_vlsm som.
    Proof.
      destruct som as (s, om).
      apply constraint_subsumption_protocol_prop
      ; try assumption.
      intro l; intros. exact I.
    Qed.

    Section preloaded_constraint_subsumption.

    Definition preloaded_constraint_subsumption
        (constraint1 constraint2 : composite_label -> composite_state * option message -> Prop)
        :=
        forall (s : composite_state),
          protocol_state_prop (pre_loaded_with_all_messages_vlsm free_composite_vlsm) s ->
          forall (l : composite_label) (om : option message),
            constraint1 l (s, om) -> constraint2 l (s, om).

    Lemma preloaded_constraint_subsumption_weaker
        (constraint1 constraint2 : composite_label -> composite_state * option message -> Prop)
        : constraint_subsumption constraint1 constraint2 -> preloaded_constraint_subsumption constraint1 constraint2.
    Proof.
      intros Hcs s Hs l om Hc1.
      apply Hcs. assumption.
    Qed.

    Context
      (constraint1 constraint2 : composite_label -> composite_state * option message -> Prop)
      (Hsubsumption : preloaded_constraint_subsumption constraint1 constraint2)
      (X1 := composite_vlsm constraint1)
      (X2 := composite_vlsm constraint2)
      .

    Lemma preloaded_constraint_subsumption_protocol_valid
      (l : label)
      (s : state)
      (om : option message)
      (Hv : protocol_valid X1 l (s, om))
      : vvalid X2 l (s, om).
    Proof.
      destruct Hv as [Hps [Hopm [Hv Hctr]]].
      split; try assumption.
      apply Hsubsumption; [|assumption].
      destruct Hps as [_om Hps].
      exists _om. apply preloaded_weaken_protocol_prop.
      apply constraint_free_protocol_prop with constraint1.
      assumption.
    Qed.

    Lemma preloaded_constraint_subsumption_protocol_prop
      (s : state)
      (om : option message)
      (Hps : protocol_prop X1 (s, om))
      : protocol_prop X2 (s, om).
    Proof.
      induction Hps.
      - apply (protocol_initial X2);assumption.
      - apply (protocol_generated X2) with _om _s; try assumption.
        apply preloaded_constraint_subsumption_protocol_valid.
        apply protocol_generated_valid with _om _s; assumption.
    Qed.

    Lemma preloaded_constraint_subsumption_can_emit
      (m : message)
      (Hm : can_emit X1 m)
      : can_emit X2 m.
    Proof.
      destruct Hm as [(s0,om0) [l [s [Hv1 Ht]]]].
      assert (Hv2 := preloaded_constraint_subsumption_protocol_valid _ _ _ Hv1).
      destruct Hv1 as [[_om0 Hs0] [[_s0 Hom0] Hv1]].
      apply preloaded_constraint_subsumption_protocol_prop in Hs0.
      apply preloaded_constraint_subsumption_protocol_prop in Hom0.
      exists (s0, om0). exists l. exists s.
      destruct Hv2 as [Hv2 Hc2].
      repeat split; try assumption.
      - exists _om0. assumption.
      - exists _s0. assumption.
    Qed.

    Lemma preloaded_constraint_subsumption_preloaded_protocol_valid
      (l : label)
      (s : state)
      (om : option message)
      (Hv : protocol_valid (pre_loaded_with_all_messages_vlsm X1) l (s, om))
      : vvalid (pre_loaded_with_all_messages_vlsm X2) l (s, om).
    Proof.
      destruct Hv as [Hps [Hopm [Hv Hctr]]].
      split; [assumption|].
      apply Hsubsumption; [|assumption].
      clear -Hps.
      apply preloaded_protocol_state_prop_iff in Hps.
      apply preloaded_protocol_state_prop_iff.
      induction Hps; [constructor; assumption|].
      apply (preloaded_protocol_generated free_composite_vlsm); [assumption|].
      split; [apply Hv|exact I].
    Qed.

    Lemma preloaded_constraint_subsumption_preloaded_protocol_prop
      (s : state)
      (om : option message)
      (Hps : protocol_prop (pre_loaded_with_all_messages_vlsm X1) (s, om))
      : protocol_prop (pre_loaded_with_all_messages_vlsm X2) (s, om).
    Proof.
      induction Hps.
      - apply (protocol_initial (pre_loaded_with_all_messages_vlsm X2));assumption.
      - apply (protocol_generated (pre_loaded_with_all_messages_vlsm X2)) with _om _s;[assumption..|].
        apply preloaded_constraint_subsumption_preloaded_protocol_valid.
        destruct Hv as [Hv Hc1].
        repeat split; try assumption.
        + exists _om. assumption.
        + exists _s. assumption.
    Qed.

    Lemma preloaded_constraint_subsumption_byzantine_message_prop
      (m : message)
      (Hm : byzantine_message_prop X1 m)
      : byzantine_message_prop X2 m.
    Proof.
      destruct Hm as [(s0,om0) [l [s [Hv1 Ht]]]].
      assert (Hv2 := preloaded_constraint_subsumption_preloaded_protocol_valid _ _ _ Hv1).
      destruct Hv1 as [[_om0 Hs0] [[_s0 Hom0] Hv1]].
      apply preloaded_constraint_subsumption_preloaded_protocol_prop in Hs0.
      apply preloaded_constraint_subsumption_preloaded_protocol_prop in Hom0.
      exists (s0, om0). exists l. exists s.
      destruct Hv2 as [Hv2 Hc2].
      repeat split; try assumption.
      - exists _om0. assumption.
      - exists _s0. assumption.
    Qed.

(* end hide *)

(**
Then <<X1>> is trace-included into <<X2>>.
*)

    Lemma preloaded_constraint_subsumption_incl
      : VLSM_incl X1 X2.
    Proof.
      apply (basic_VLSM_incl (machine X1) (machine X2))
      ; intros; try (assumption || reflexivity).
      - apply initial_message_is_protocol;assumption.
      - apply preloaded_constraint_subsumption_protocol_valid.
        assumption.
    Qed.

    Lemma preloaded_constraint_subsumption_pre_loaded_with_all_messages_incl
      : VLSM_incl (pre_loaded_with_all_messages_vlsm X1) (pre_loaded_with_all_messages_vlsm X2).
    Proof.
      apply (basic_VLSM_incl (machine (pre_loaded_with_all_messages_vlsm X1)) (machine (pre_loaded_with_all_messages_vlsm X2)))
      ; intros; try (assumption || reflexivity).
      - apply initial_message_is_protocol; assumption.
      - apply preloaded_constraint_subsumption_preloaded_protocol_valid.
        assumption.
    Qed.

    End preloaded_constraint_subsumption.

    Section constraint_subsumption_part_two.

    Context
      (constraint1 constraint2 : composite_label -> composite_state * option message -> Prop)
      (Hsubsumption : constraint_subsumption constraint1 constraint2)
      (X1 := composite_vlsm constraint1)
      (X2 := composite_vlsm constraint2)
      .

    Lemma constraint_subsumption_can_emit
      (m : message)
      (Hm : can_emit X1 m)
      : can_emit X2 m.
    Proof.
      apply preloaded_constraint_subsumption_can_emit with constraint1 ; [|assumption].
      apply preloaded_constraint_subsumption_weaker. assumption.
    Qed.

    Lemma constraint_subsumption_preloaded_protocol_valid
      (l : label)
      (s : state)
      (om : option message)
      (Hv : protocol_valid (pre_loaded_with_all_messages_vlsm X1) l (s, om))
      : vvalid (pre_loaded_with_all_messages_vlsm X2) l (s, om).
    Proof.
      apply preloaded_constraint_subsumption_preloaded_protocol_valid; [|assumption].
      apply preloaded_constraint_subsumption_weaker. assumption.
    Qed.

    Lemma constraint_subsumption_preloaded_protocol_prop
      (s : state)
      (om : option message)
      (Hps : protocol_prop (pre_loaded_with_all_messages_vlsm X1) (s, om))
      : protocol_prop (pre_loaded_with_all_messages_vlsm X2) (s, om).
    Proof.
      apply preloaded_constraint_subsumption_preloaded_protocol_prop; [|assumption].
      apply preloaded_constraint_subsumption_weaker. assumption.
    Qed.

    Lemma constraint_subsumption_byzantine_message_prop
      (m : message)
      (Hm : byzantine_message_prop X1 m)
      : byzantine_message_prop X2 m.
    Proof.
      apply preloaded_constraint_subsumption_byzantine_message_prop with constraint1; [|assumption].
      apply preloaded_constraint_subsumption_weaker. assumption.
    Qed.

(* end hide *)

(**
Then <<X1>> is trace-included into <<X2>>.
*)

    Lemma constraint_subsumption_incl
      : VLSM_incl X1 X2.
    Proof.
      apply preloaded_constraint_subsumption_incl.
      apply preloaded_constraint_subsumption_weaker. assumption.
    Qed.

    Lemma constraint_subsumption_pre_loaded_with_all_messages_incl
      : VLSM_incl (pre_loaded_with_all_messages_vlsm X1) (pre_loaded_with_all_messages_vlsm X2).
    Proof.
      apply preloaded_constraint_subsumption_pre_loaded_with_all_messages_incl.
      apply preloaded_constraint_subsumption_weaker. assumption.
    Qed.

    End constraint_subsumption_part_two.

    Lemma constraint_free_incl
      (constraint : composite_label -> composite_state  * option message -> Prop)
      : VLSM_incl (composite_vlsm constraint) free_composite_vlsm.
    Proof.
      apply constraint_subsumption_incl.
      intro l; intros. exact I.
    Qed.

    Lemma protocol_prop_composite_free_lift_generalized_initial
      (P Q : message -> Prop)
      (PimpliesQ : forall m, P m -> Q m)
      (j : index)
      (sj : vstate (IM j))
      (om : option message)
      (Hp : protocol_prop (pre_loaded_vlsm (IM j) P) (sj, om))
      (s := lift_to_composite_state j sj)
      : protocol_prop (pre_loaded_vlsm free_composite_vlsm Q) (s, om).
    Proof.
      remember (sj, om) as sjom.
      generalize dependent om. generalize dependent sj.
      induction Hp; intros; inversion Heqsjom; subst; clear Heqsjom
      ; unfold s0; clear s0.
      - apply protocol_initial.
        { intro i. unfold lift_to_composite_state.
          destruct (decide (i = j)).
          - subst; rewrite state_update_eq. assumption.
          - rewrite state_update_neq by assumption.
            unfold composite_s0. simpl. unfold vs0.
            apply proj2_sig.
        }
        destruct om0 as [m|];[|exact I].
        { simpl in Hom |- *.
          destruct Hom;[left|right;apply PimpliesQ;assumption].
          exists j. exists (exist _ _ H). reflexivity.
        }
      - specialize (IHHp1 s _om eq_refl).
        specialize (IHHp2 _s om eq_refl).
        replace
          (@pair composite_state (option message) (lift_to_composite_state j sj) om0)
          with
          (vtransition (pre_loaded_vlsm free_composite_vlsm Q) (existT _ j l) (lift_to_composite_state j s, om)).
        + apply (protocol_generated (pre_loaded_vlsm free_composite_vlsm Q)) with _om (lift_to_composite_state j _s)
          ; [assumption | assumption|].
          split; [|exact I].
          simpl. unfold lift_to_composite_state. rewrite state_update_eq. assumption.
        + unfold vtransition. simpl. unfold lift_to_composite_state.
          rewrite state_update_eq. unfold vtransition.
          match goal with
          |- (let (_, _) := ?t in _) = _ => replace t with (sj, om0)
          end.
          f_equal.
          apply state_update_twice.
    Qed.

(**
If @(sj, om)@ has the [protocol_prop]erty for component and @s@ is the [lift_to_composite_state] of @sj@, then
@(s, om)@ has the [protocol_prop]erty for the [free_composite_vlsm].
*)
    Lemma protocol_prop_composite_free_lift
      (j : index)
      (sj : vstate (IM j))
      (om : option message)
      (Hp : protocol_prop (IM j) (sj, om))
      (s := lift_to_composite_state j sj)
      : protocol_prop free_composite_vlsm (s, om).
    Proof.
      apply vlsm_is_pre_loaded_with_False_protocol_prop.
      apply vlsm_is_pre_loaded_with_False_protocol_prop in Hp.
      remember (fun _ : message => False) as P.
      apply (protocol_prop_composite_free_lift_generalized_initial P P); [|assumption].
      intro m. exact id.
    Qed.

    Lemma protocol_message_prop_composite_free_lift
      (j : index)
      (m : message)
      (Hp : protocol_message_prop (IM j) m)
      : protocol_message_prop free_composite_vlsm m.
    Proof.
      unfold protocol_message_prop in *.
      destruct Hp as [s Hprop].
      apply protocol_prop_composite_free_lift in Hprop.
      exists (lift_to_composite_state j s).
      assumption.
    Qed.

    Lemma can_emit_composite_free_lift
      (P Q : message -> Prop)
      (PimpliesQ : forall m, P m -> Q m)
      (j : index)
      (m : message)
      (Htrj : can_emit (pre_loaded_vlsm (IM j) P) m)
      : can_emit (pre_loaded_vlsm free_composite_vlsm Q) m.
    Proof.
      destruct Htrj as [(s,om) [l [s' [[[_om Hs] [[_s Hom] Hv]] Ht]]]].
      exists ((lift_to_composite_state j s), om).
      exists (existT _ j l).
      exists (lift_to_composite_state j s').
      apply (protocol_prop_composite_free_lift_generalized_initial _ _ PimpliesQ) in Hs.
      apply (protocol_prop_composite_free_lift_generalized_initial _ _ PimpliesQ) in Hom.
      repeat split; [exists _om;assumption| exists (lift_to_composite_state j _s); assumption| ..].
      - simpl. unfold lift_to_composite_state. rewrite state_update_eq. assumption.
      - unfold lift_to_composite_state. simpl. rewrite state_update_eq.
        match goal with
        |- (let (_, _) := ?t in _) = _ => replace t with (s', Some m)
        end.
        f_equal.
        apply state_update_twice.
    Qed.

    (** Updating a composite initial state with a component initial state
    yields a composite initial state *)
    Lemma composite_free_update_initial_state_with_initial
      (s : vstate free_composite_vlsm)
      (Hs : vinitial_state_prop free_composite_vlsm s)
      (i : index)
      (si : vstate (IM i))
      (Hsi : vinitial_state_prop (IM i) si)
      : vinitial_state_prop free_composite_vlsm (state_update s i si).
    Proof.
      intro j. destruct (decide (j = i)).
      - subst. rewrite state_update_eq. assumption.
      - rewrite state_update_neq; try assumption. apply Hs.
    Qed.

    (** Updating a composite protocol state for the free composition with
    a component initial state yields a composite protocol state *)
    Lemma composite_free_update_state_with_initial
      (s : vstate free_composite_vlsm)
      (Hs : protocol_state_prop free_composite_vlsm s)
      (i : index)
      (si : vstate (IM i))
      (Hsi : vinitial_state_prop (IM i) si)
      : protocol_state_prop free_composite_vlsm (state_update s i si).
    Proof.
      generalize dependent s. apply protocol_state_prop_ind; intros.
      - remember (state_update s i si) as s'.
        assert (Hs' : vinitial_state_prop free_composite_vlsm s')
          by (subst; apply composite_free_update_initial_state_with_initial; assumption).
        apply initial_is_protocol.
        assumption.
      - destruct Ht as [[Hps [Hom Hv]] Ht].
        unfold transition in Ht. simpl in Ht.
        destruct Hv as [Hv _]. simpl in Hv.
        destruct l as (j, lj).
        destruct (vtransition (IM j) lj (s j, om)) as (sj', omj') eqn:Htj.
        inversion Ht. subst s' om'. clear Ht.
        destruct (decide (i = j)).
        + subst. rewrite state_update_twice. assumption.
        + rewrite state_update_twice_neq; try assumption.
          destruct Hs as [_om Hs].
          destruct Hom as [_s Hom].
          specialize
            (protocol_generated free_composite_vlsm (existT _ j lj) _ _ Hs _ _ Hom)
            as Hgen.
          assert (n' : j <> i) by (intro contra; subst; elim n; reflexivity).
          spec Hgen.
          { split; try exact I. simpl. rewrite state_update_neq; assumption. }
          simpl in Hgen.
          rewrite state_update_neq in Hgen; try assumption. simpl in *.
          rewrite Htj in Hgen.
          eexists _. apply Hgen.
    Qed.
  End composite_vlsm.

End VLSM_composition.


(**
   These basic projection lemmas relate
   the [protocol_state_prop] and [protocol_transition] of
   a composite VLSM back to those conditions holding
   over projections to individual components of the state.

   Because the composition may have validly produced
   messages that are not protocol in an individual
   component (by interaction between components),
   We cannot just use properties [protocol_prop (IM i)]
   or [protocol_transition (IM i)].
   For simplicity these lemmas use
   [pre_loaded_with_all_messages_vlsm (IM i)].

   This does not precisely reflect the set of
   messages and transitions that can actually be
   seen in projections of transitions of the composite VLSM,
   but seems to be the best we can do with a result
   type that doesn't mention the other components or
   the composition constraint of the composite.

   Later in this file a
   [composite_constrained_projection_vlsm] is defined
   that shares the states of [IM i] which is more
   precise.
 *)

Lemma protocol_state_project_preloaded_to_preloaded
      message `{EqDecision index} `{Inhabited index} (IM : index -> VLSM message) constraint
      (X:=composite_vlsm IM constraint)
      (s: vstate (pre_loaded_with_all_messages_vlsm X)) i:
  protocol_state_prop (pre_loaded_with_all_messages_vlsm X) s ->
  protocol_state_prop (pre_loaded_with_all_messages_vlsm (IM i)) (s i).
Proof.
  intros [om Hproto].
  apply preloaded_protocol_state_prop_iff.
  change (vstate _) with (state (VLSM_type:=(@type _ (pre_loaded_with_all_messages_vlsm X)))) in s.
  set (som:=(s,om)) in Hproto.
  change s with (fst som).
  clearbody som;clear s om.
  induction Hproto.
  - apply preloaded_protocol_initial_state.
    apply (Hs i).
  - destruct l as [j lj].
    cbn.
    rewrite (surjective_pairing (vtransition (IM j) lj (s j, om))).
    simpl.
    destruct (decide (i = j)).
    + subst j.
      rewrite state_update_eq.
      apply preloaded_protocol_generated;[assumption|].
      apply Hv.
    + rewrite state_update_neq by assumption.
      exact IHHproto1.
Qed.

Lemma protocol_state_project_preloaded
      message `{EqDecision index} `{Inhabited index} (IM : index -> VLSM message) constraint
      (X:=composite_vlsm IM constraint)
      (s: vstate X) i:
  protocol_state_prop X s ->
  protocol_state_prop (pre_loaded_with_all_messages_vlsm (IM i)) (s i).
Proof.
  change (vstate X) with (vstate (pre_loaded_with_all_messages_vlsm X)) in s.
  intros [om Hproto].
  apply protocol_state_project_preloaded_to_preloaded.
  exists om.
  apply preloaded_weaken_protocol_prop.
  assumption.
Qed.

Lemma protocol_transition_preloaded_project_active
      {message} `{EqDecision V} `{Inhabited V} {IM: V -> VLSM message} {constraint}
      (X := composite_vlsm IM constraint)
      l s im s' om:
  protocol_transition (pre_loaded_with_all_messages_vlsm X) l (s,im) (s',om) ->
  protocol_transition (pre_loaded_with_all_messages_vlsm (IM (projT1 l))) (projT2 l)
                      (s (projT1 l), im) (s' (projT1 l), om).
Proof.
  intro Hptrans.
  destruct l as [j lj].
  destruct Hptrans as [Hpvalid Htrans].
  split.
  - destruct Hpvalid as [Hproto_s [_ Hcvalid]].
    split;[|split].
    + revert Hproto_s.
      apply protocol_state_project_preloaded_to_preloaded.
    + apply any_message_is_protocol_in_preloaded.
    + destruct Hcvalid as [Hvalid Hconstraint].
      exact Hvalid.
  - simpl.
    cbn in Htrans.
    destruct (vtransition (IM j) lj (s j, im)).
    inversion_clear Htrans.
    f_equal.
    rewrite state_update_eq.
    reflexivity.
Qed.

Lemma protocol_transition_project_active
      {message} `{EqDecision V} `{Inhabited V} {IM: V -> VLSM message} {constraint}
      (X := composite_vlsm IM constraint)
      l s im s' om:
  protocol_transition X l (s,im) (s',om) ->
  protocol_transition (pre_loaded_with_all_messages_vlsm (IM (projT1 l))) (projT2 l)
                      (s (projT1 l), im) (s' (projT1 l), om).
Proof.
  intro Hptrans.
  apply preloaded_weaken_protocol_transition in Hptrans.
  revert Hptrans.
  apply protocol_transition_preloaded_project_active.
Qed.

Lemma protocol_transition_preloaded_project_any {V} (i:V)
      {message} `{EqDecision V} `{Inhabited V} {IM: V -> VLSM message} {constraint}
      (X := composite_vlsm IM constraint)
      (l:vlabel X) s im s' om:
  protocol_transition (pre_loaded_with_all_messages_vlsm X) l (s,im) (s',om) ->
  (s i = s' i \/
   exists li, (l = existT _ i li) /\
   protocol_transition (pre_loaded_with_all_messages_vlsm (IM i))
                       li
                       (s i,im) (s' i,om)).
Proof.
  intro Hptrans.
  destruct l as [j lj].
  destruct (decide (i = j)).
  - subst j.
    right.
    exists lj.
    split;[reflexivity|].
    revert Hptrans.
    apply protocol_transition_preloaded_project_active.
  - left.
    destruct Hptrans as [Hpvalid Htrans].
    cbn in Htrans.
    destruct (vtransition (IM j) lj (s j, im)).
    inversion_clear Htrans.
    rewrite state_update_neq by assumption.
    reflexivity.
Qed.

Lemma protocol_transition_project_any {V} (i:V)
      {message} `{EqDecision V} `{Inhabited V} {IM: V -> VLSM message} {constraint}
      (X := composite_vlsm IM constraint)
      (l:vlabel X) s im s' om:
  protocol_transition X l (s,im) (s',om) ->
  (s i = s' i \/
   exists li, (l = existT _ i li) /\
   protocol_transition (pre_loaded_with_all_messages_vlsm (IM i))
                       li
                       (s i,im) (s' i,om)).
Proof.
  intro Hproto.
  apply preloaded_weaken_protocol_transition in Hproto.
  revert Hproto.
  apply protocol_transition_preloaded_project_any.
Qed.

Section projections.
(**
* Composite VLSM projections

Let us fix an indexed set of VLSMs <<IM>> and their composition <<X>> using <<constraint>>.

*)

  Context {message : Type}
          {index : Type}
          {IndEqDec : EqDecision index}
          (IM : index -> VLSM message)
          `{i0 : Inhabited index}
          (T := composite_type IM)
          (constraint : composite_label IM -> composite_state IM * option message -> Prop)
          (X := composite_vlsm IM constraint)
          .

(**
The [VLSM_type] of a projection of <<X>> to component <<i>> is the
type of the <<i>>th component of <<X>>.
We defined the signature of the projection to be the same as that of the component,
with the exception that the [initial_message]s for the projection are defined
to be all [protocol_message]s of <<X>>:

*)
  Definition composite_vlsm_constrained_projection_sig
    (i : index)
    : VLSM_sign (type (IM i))
    :=
    {|   initial_state_prop := vinitial_state_prop (IM i)
     ;   initial_message_prop := fun pmi => exists xm : protocol_message X, proj1_sig xm = pmi
     ;   s0 := vs0 (IM i)
     ;   m0 := vm0 (IM i)
     ;   l0 := vl0 (IM i)
    |}.

(**
[projection_valid]ity is defined as the projection of [protocol_valid]ity of <<X>>:
*)

  Definition projection_valid
    (i : index)
    (li : vlabel (IM i))
    (siomi : vstate (IM i) * option message)
    :=
    let (si, omi) := siomi in
    exists (s : vstate X),
      s i = si /\ protocol_valid X (existT _ i li) (s, omi).

(**
Since [projection_valid]ity is derived from [protocol_valid]ity, which in turn
depends on [valid]ity in the component, it is easy to see that
[projection_valid]ity implies [valid]ity in the component.
*)
  Lemma projection_valid_implies_valid
    (i : index)
    (li : vlabel (IM i))
    (siomi : vstate (IM i) * option message)
    (Hcomposite : projection_valid i li siomi)
    : vvalid (IM i) li siomi.
  Proof.
    destruct siomi as [si omi].
    destruct Hcomposite as [s [Hsi [_ [_ Hvalid]]]].
    subst; simpl in *.
    destruct Hvalid as [Hvalid Hconstraint].
    assumption.
  Qed.

(**
We define the projection of <<X>> to index <<i>> as the [VLSM] whose signature
is the [composite_vlsm_constrained_projection_sig]nature corresponding to <<i>>,
having the same transition function as <<IM i>>, the <<i>>th component of
*)
  Definition composite_vlsm_constrained_projection_machine
    (i : index)
    : VLSM_class (composite_vlsm_constrained_projection_sig i) :=
    {|  transition :=  vtransition (IM i)
     ;  valid := projection_valid i
    |}.

  Definition composite_vlsm_constrained_projection
    (i : index)
    : VLSM message
    := mk_vlsm (composite_vlsm_constrained_projection_machine i).

  Section fixed_projection.

(**

** Projection traces are Byzantine

Let us fix an index <<j>> and let <<Xj>> be the projection of <<X>> on
component <<j>>.

In this section we establish some basic properties for projections, building up
to Lemma [proj_pre_loaded_with_all_messages_incl], which guarantees that all
[protocol_trace]s of <<Xj>> are also [protocol_trace]s for the
[pre_loaded_with_all_messages_vlsm] associated to the component <<IM j>>.
In particular this ensures that the byzantine traces of <<IM j>> include all
[protocol_trace]s of <<Xj>> (see Lemma [pre_loaded_with_all_messages_alt_eq]).

*)

    Context
      (j : index)
      (Xj := composite_vlsm_constrained_projection j)
      .

(**
As a basic property of the definition of initial states it follows that
the <<j>>th component of an [initial_state] of <<X>> is initial for <<Xj>>
*)

    Lemma initial_state_projection
      (s : vstate X)
      (Hinit : vinitial_state_prop X s)
      : vinitial_state_prop Xj (s j).
    Proof.
      specialize (Hinit j).
      assumption.
    Qed.

(**
Since all [protocol_message]s of <<X>> become [initial_message]s in <<Xj>>, the
following result is not surprising.
*)
    Lemma protocol_message_projection
      (iom : option message)
      (HpmX : option_protocol_message_prop X iom)
      : option_protocol_message_prop Xj iom.
    Proof.
      apply option_initial_message_is_protocol.
      destruct iom as [m|];[|exact I].
      exists (exist _ m HpmX).
      reflexivity.
    Qed.

(**
Interestingly enough, <<Xj>> cannot produce any additional messages than
the initial ones available from <<X>>.
*)
    Lemma protocol_message_projection_rev
      (iom : option message)
      (Hpmj: option_protocol_message_prop Xj iom)
      : option_protocol_message_prop X iom.
    Proof.
      destruct iom as [m|];[|apply option_protocol_message_None].
      destruct Hpmj as [sj Hpmj].
      inversion Hpmj; subst.
      - destruct Hom as [pm <-]. apply proj2_sig.
      - destruct Hv as [sX [Heqs Hv]].
        subst s.
        set (lX := existT (fun n => vlabel (IM n)) j l) in Hv.
        apply protocol_prop_valid_out in Hv.
        simpl in Hv.
        unfold vstate in Hv.
        rewrite H0 in Hv.
        eexists; exact Hv.
    Qed.

(**
As a stepping stone towards proving trace inclusion between <<Xj>> and
the [pre_loaded_with_all_messages_vlsm] associated to <<IM j>>, we prove that the
[protocol_prop]erty is transferred.
*)
    Lemma proj_pre_loaded_with_all_messages_protocol_prop
      (PreLoaded := pre_loaded_with_all_messages_vlsm (IM j))
      (s : state)
      (om : option message)
      (Hps : protocol_prop Xj (s, om))
      : protocol_prop PreLoaded (s, om).
    Proof.
      induction Hps.
      - apply (protocol_initial PreLoaded).
        assumption. destruct om0;exact I.
      - apply (protocol_generated PreLoaded) with _om _s; try assumption.
        apply projection_valid_implies_valid. assumption.
    Qed.

(**
We can now finally prove the main result for this section:
*)
    Lemma proj_pre_loaded_with_all_messages_incl
      (PreLoaded := pre_loaded_with_all_messages_vlsm (IM j))
      : VLSM_incl Xj PreLoaded.
    Proof.
      apply (basic_VLSM_incl (machine Xj) (machine PreLoaded))
      ; intros; try (assumption || reflexivity).
      - apply initial_message_is_protocol; exact I.
      - apply projection_valid_implies_valid.
        destruct H as [_ [_ Hv]].
        assumption.
    Qed.

  End fixed_projection.

  Section projection_friendliness_sufficient_condition.

  (** ** A sufficient condition for being [projection_friendly]. *)

  Context
  (j : index)
  (Xj := composite_vlsm_constrained_projection j)
  .

  (**
  This condition states that [protocol_valid]ity in a projection <<Xj>>
  can be lifted to any [protocol_state] in <<X>> which projects to the
  corresponding <<Xj>> state.
  *)

  Definition projection_friendliness_sufficient_condition
    := forall
      (lj : vlabel (IM j))
      (sj : vstate (IM j))
      (om : option message)
      (Hpv : protocol_valid Xj lj (sj, om))
      (s : vstate X)
      (Hs : protocol_state_prop X s)
      (Hsi : s j = sj)
      , vvalid X (existT _ j lj) (s, om).

  Lemma projection_friendliness_sufficient_condition_protocol_message
    (l : label)
    (s : state)
    (om : option message)
    (Hv : protocol_valid Xj l (s, om))
    : option_protocol_message_prop X om.
  Proof.
    destruct Hv as [Hpsj [Hpmj [sx [Hs [HpsX [HpmX Hv]]]]]].
    assumption.
  Qed.

  Lemma lift_to_composite_state_initial
    (sj : vstate (IM j))
    (Hinitj : vinitial_state_prop (IM j) sj)
    : vinitial_state_prop X (lift_to_composite_state IM j sj).
  Proof.
    intro i.
    unfold lift_to_composite_state.
    destruct (decide (i = j)).
    - subst. rewrite state_update_eq. assumption.
    - rewrite state_update_neq; try assumption.
      simpl.
      unfold vs0. destruct s0 as [s Hs].
      assumption.
  Qed.

  Lemma projection_friendliness_sufficient_condition_protocol_state
    (Hfr : projection_friendliness_sufficient_condition)
    (s : state)
    (om : option message)
    (Hp : protocol_prop Xj (s, om))
    : protocol_state_prop X (lift_to_composite_state IM j s).
  Proof.
    remember (s, om) as som.
    generalize dependent om. generalize dependent s.
    induction Hp; intros; inversion Heqsom; subst; clear Heqsom.
    - exists None.
      apply (protocol_initial X);[|exact I].
      apply lift_to_composite_state_initial.
      assumption.
    - specialize (IHHp1 s _om eq_refl).
      exists om0.
      replace
        (lift_to_composite_state IM j s0, om0)
        with (vtransition X (existT (fun n : index => vlabel (IM n)) j l) (lift_to_composite_state IM j s, om)).
      +
        specialize (protocol_generated_valid Xj Hp1 Hp2 Hv); intros Hpvj.
        specialize (Hfr l s om Hpvj _ IHHp1).
        unfold lift_to_composite_state at 1 in Hfr.
        rewrite state_update_eq in Hfr.
        specialize (Hfr eq_refl).
        specialize (projection_friendliness_sufficient_condition_protocol_message _ _ _ Hpvj)
        ; intros  [_sX HpmX].
        destruct IHHp1 as [_omX HpsX].
        apply
          (protocol_generated X
            (existT (fun n : index => vlabel (IM n)) j l)
            (lift_to_composite_state IM j s)
            _omX
            HpsX
            _sX
            om
            HpmX
            Hfr
          ).
      + unfold vtransition. simpl. unfold lift_to_composite_state at 1. rewrite state_update_eq.
        replace
          (@vtransition message (IM j) l (@pair (@vstate message (IM j)) (option message) s om))
          with (s0, om0).
        f_equal.
        unfold lift_to_composite_state.
        apply state_update_twice.
  Qed.

  Lemma projection_friendliness_sufficient_condition_valid
    (Hfr : projection_friendliness_sufficient_condition)
    (l : label)
    (s : state)
    (om : option message)
    (Hv : protocol_valid Xj l (s, om))
    : vvalid X (existT (fun n : index => vlabel (IM n)) j l) (lift_to_composite_state IM j s, om).
  Proof.
    specialize (projection_friendliness_sufficient_condition_protocol_state Hfr s)
    ; intros HpsX.
    specialize (Hfr l s om Hv (lift_to_composite_state IM j s)).
    destruct Hv as [[_om Hpsj] [Hpmj [_sx [Hs [_HpsX [HpmX Hv]]]]]].
    specialize (HpsX _om Hpsj).
    unfold lift_to_composite_state at 2 in Hfr.
    rewrite state_update_eq in Hfr.
    specialize (Hfr HpsX eq_refl).
    assumption.
  Qed.

  Lemma projection_friendliness_sufficient_condition_protocol_transition
    (Hfr : projection_friendliness_sufficient_condition)
    (l : label)
    (is os : state)
    (iom oom : option message)
    (Ht : protocol_transition Xj l (is, iom) (os, oom))
    : protocol_transition X
      (existT (fun n : index => vlabel (IM n)) j l)
      (lift_to_composite_state IM j is, iom)
      (lift_to_composite_state IM j os, oom).
  Proof.
    destruct Ht as [[[_om Hps] [[_s Hpm] Hv]] Ht].
    specialize (protocol_generated_valid Xj Hps Hpm Hv); intros Hpv.
    repeat split.
    - apply projection_friendliness_sufficient_condition_protocol_state with _om; assumption.
    - apply projection_friendliness_sufficient_condition_protocol_message in Hpv. assumption.
    - specialize (projection_friendliness_sufficient_condition_valid Hfr l is iom Hpv); intros [HvX _].
      assumption.
    - specialize (projection_friendliness_sufficient_condition_valid Hfr l is iom Hpv); intros [_ Hctr].
      assumption.
    - simpl. unfold lift_to_composite_state at 1. rewrite state_update_eq.
      replace
        (@vtransition message (IM j) l (@pair (@vstate message (IM j)) (option message) is iom))
        with (os, oom).
      f_equal.
      unfold lift_to_composite_state.
      apply state_update_twice.
  Qed.

  Lemma projection_friendliness_sufficient_condition_finite_ptrace
    (Hfr : projection_friendliness_sufficient_condition)
    (s : state)
    (ls : list transition_item)
    (Hpxt : finite_protocol_trace_from Xj s ls)
    : finite_protocol_trace_from X
      (lift_to_composite_state IM j s)
      (List.map (lift_to_composite_transition_item IM j) ls).
  Proof.
    induction Hpxt.
    - constructor.
      destruct H as [m H].
      apply projection_friendliness_sufficient_condition_protocol_state in H; assumption.
    - constructor; try assumption.
      apply projection_friendliness_sufficient_condition_protocol_transition; assumption.
  Qed.

  Lemma projection_friendliness_sufficient_condition_infinite_ptrace
    (Hfr : projection_friendliness_sufficient_condition)
    (s : state)
    (ls : Stream transition_item)
    (Hpxt : infinite_protocol_trace_from Xj s ls)
    : infinite_protocol_trace_from X
      (lift_to_composite_state IM j s)
      (Streams.map (lift_to_composite_transition_item IM j) ls).
  Proof.
    generalize dependent s. generalize dependent ls.
    cofix H.
    intros [[l input destination output] ls] s Hx.
    inversion Hx; subst.
    rewrite map_Cons.
    constructor.
    - apply H. assumption.
    - apply projection_friendliness_sufficient_condition_protocol_transition
    ; assumption.
  Qed.

  (**
  The result below shows that the [projection_friendliness_sufficient_condition]
  might be too strong, in the sense that it allows any trace from the
  projection to be lifted direclty to <<X>>
  (all other machines stay in their initial state).
  *)
  Lemma projection_friendliness_sufficient_condition_protocol_trace
    (Hfr : projection_friendliness_sufficient_condition)
    (t : Trace)
    (Hpt : protocol_trace_prop Xj t)
    : protocol_trace_prop X (lift_to_composite_trace IM j t).
  Proof.
    destruct t as [s ls| s ss]; simpl in *; destruct Hpt as [Hxt Hinit].
    - apply projection_friendliness_sufficient_condition_finite_ptrace in Hxt
      ; try assumption.
      split; try assumption.
      apply lift_to_composite_state_initial. assumption.
    - apply projection_friendliness_sufficient_condition_infinite_ptrace in Hxt
      ; try assumption.
      split; try assumption.
      apply lift_to_composite_state_initial. assumption.
  Qed.

  End projection_friendliness_sufficient_condition.

End projections.

Section free_projections.
(**

** Projections of free compositions

These projections are simple instances of the projections defined above in which
the composition constraint is taken to be [True].

All results from regular projections carry to these "free" projections.
*)

  Context {message : Type}
          {index : Type}
          {IndEqDec : EqDecision index}
          (IM :index -> VLSM message)
          {i0 : Inhabited index}
          (X := free_composite_vlsm IM)
          .

  Definition composite_vlsm_free_projection
    (i : index)
    : VLSM message
    :=
    composite_vlsm_constrained_projection IM (free_constraint IM) i.

  Lemma preloaded_composed_protocol_state
    (s : vstate X)
    (Hs : protocol_state_prop (pre_loaded_with_all_messages_vlsm X) s)
    (i : index)
    : protocol_state_prop (pre_loaded_with_all_messages_vlsm (IM i)) (s i).
  Proof.
    revert i. generalize dependent s.
    induction 1 using protocol_state_prop_ind; intros.
    - apply protocol_state_prop_iff. left. specialize (Hs i). unfold vinitial_state_prop in Hs.
      exists (exist _ (s i) Hs). reflexivity.
    - destruct Ht as [[Hps [Hpm [Hv _]]] Ht].
      simpl in Hv.
      simpl in Ht. unfold vtransition in Ht. simpl in Ht.
      destruct l as (i', li').
      destruct (vtransition (IM i') li' (s i', om)) as (si', omi') eqn:Ht'.
      inversion Ht. subst s' omi'; clear Ht.
      destruct (decide (i = i')).
      + subst i'. rewrite state_update_eq.
        specialize (IHHs i).
        apply protocol_state_prop_iff. right.
        exists li'. exists (s i, om). exists om'.
        repeat split; try assumption.
        exists (proj1_sig (vs0 (pre_loaded_with_all_messages_vlsm (IM i)))).
        apply protocol_initial.
        apply proj2_sig.
        destruct om;exact I.
      + rewrite state_update_neq; try assumption. apply IHHs.
  Qed.

  (* The following results concern facts about applying a [plan X] <<P>>
     to a [vstate X] <<s'>>, knowing its effects on a different [vstate X] <<s>>
     which shares some relevant features with <<s'>>. *)

  (* A transition on component <<i>> is protocol from <<s'>> if it is
     protocol from <<s>> and their <<i>>'th components are equal *)

  Lemma relevant_component_transition
    (s s' : vstate X)
    (l : vlabel X)
    (input : option message)
    (i := projT1 l)
    (Heq : (s i) = (s' i))
    (Hprs : protocol_state_prop X s')
    (Hpr : protocol_valid X l (s, input)) :
    protocol_valid X l (s', input).
  Proof.
    unfold protocol_valid in *.
    split; [intuition|intuition|..].
    unfold valid in *; simpl in *.
    unfold constrained_composite_valid in *.
    unfold composite_valid in *.
    unfold free_constraint in *; simpl.
    unfold vvalid in *.
    destruct l.
    simpl in i.
    unfold i in Heq.
    rewrite <- Heq.
    assumption.
  Qed.

  (* The effect of the transition is also the same *)

  Lemma relevant_component_transition2
    (s s' : vstate X)
    (l : vlabel X)
    (input : option message)
    (i := projT1 l)
    (Heq : (s i) = (s' i))
    (Hprs : protocol_state_prop X s') :
    let (dest, output) := vtransition X l (s, input) in
    let (dest', output') := vtransition X l (s', input) in
    output = output' /\ (dest i) = (dest' i).
  Proof.
    unfold vtransition.
    unfold transition.
    destruct l; simpl.
    simpl in i.
    unfold i in Heq.
    rewrite Heq.
    destruct (vtransition (IM x) v (s' x, input)); [intuition|..].
    unfold i.
    rewrite state_update_eq.
    rewrite state_update_eq.
    reflexivity.
  Qed.

  Lemma relevant_components_one
    (s s' : vstate X)
    (Hprs' : protocol_state_prop X s')
    (ai : vplan_item X)
    (i := projT1 (label_a ai))
    (Heq : (s i) = (s' i))
    (Hpr : finite_protocol_plan_from X s [ai]) :
    let res' := snd (apply_plan X s' [ai]) in
    let res := snd (apply_plan X s [ai]) in
    finite_protocol_plan_from X s' [ai] /\
    (res' i) = res i.
  Proof.
    simpl.
    unfold finite_protocol_plan_from in *.
    unfold apply_plan, _apply_plan in *.
    destruct ai; simpl in *.
    match goal with
    |- context [let (_, _) := let (_, _) := ?t in _ in _] =>
      destruct t eqn : eq_trans'
    end.
    match goal with
    |- context [let (_, _) := let (_, _) := ?t in _ in _] =>
      destruct t eqn : eq_trans
    end.
    inversion Hpr.
    split.
    - assert (protocol_transition X label_a (s', input_a) (s0, o)). {
        unfold protocol_transition in *.
        destruct H6 as [Hpr_valid Htrans].
        apply relevant_component_transition with (s' := s') in Hpr_valid.
        all : intuition.
      }

      apply finite_ptrace_extend.
      apply finite_ptrace_empty.
      apply protocol_transition_destination in H7; assumption.
      assumption.
    - simpl.
      specialize (relevant_component_transition2 s s' l input_a) as Hrel.
      simpl in Hrel. unfold i in Heq. rewrite <- H in Heq. specialize (Hrel Heq Hprs').
      rewrite H in Hrel.
      match type of Hrel with
      | let (_, _) := ?t in _ => replace t with (s1, o0) in Hrel
      end.
      match type of Hrel with
      | let (_, _) := ?t in _ => replace t with (s0, o) in Hrel
      end.
      unfold i.
      intuition.
  Qed.

  (* Transitioning on some index different from <<i>> does not affect
     component i. *)

  Lemma irrelevant_components_one
    (s : state)
    (ai : composite_plan_item IM)
    (i : index)
    (Hdif : i <> projT1 (label_a ai)) :
    let res := snd (composite_apply_plan IM s [ai]) in
    (res i) = (s i).
  Proof.
    unfold composite_apply_plan, apply_plan, _apply_plan.
    simpl.
    destruct ai.
    match goal with
    |- context [let (_, _) := let (_, _) := ?t in _ in _] =>
      destruct t eqn : eq_trans
    end.
    simpl in *.
    unfold vtransition in eq_trans.
    simpl in eq_trans.
    destruct label_a; simpl in *.
    match type of eq_trans with
    | (let (si', om') := ?t in _) = _ => destruct t end.
    inversion eq_trans.
    rewrite state_update_neq.
    reflexivity.
    assumption.
  Qed.

  (* Same as the previous result, but for multiple transitions. *)

  Lemma irrelevant_components
    (s : state)
    (a : composite_plan IM)
    (a_indices := List.map (@projT1 _ _) (List.map (@label_a _ _) a))
    (i : index)
    (Hdif : ~In i a_indices) :
    let res := snd (composite_apply_plan IM s a) in
    (res i) = (s i).
  Proof.
    induction a using rev_ind.
    - simpl; intuition.
    - simpl in *.
      rewrite (composite_apply_plan_app IM).
      destruct (composite_apply_plan IM s a) as (tra, sa) eqn : eq_a; simpl in *.
      destruct (composite_apply_plan IM sa [x]) as (trx, sx) eqn : eq_x; simpl in *.

      unfold a_indices in Hdif.
      rewrite map_app in Hdif.
      rewrite map_app in Hdif.

      spec IHa. {
        intuition.
      }

      rewrite <- IHa.
      replace sx with (snd (composite_apply_plan IM sa [x])) by (rewrite eq_x; reflexivity).
      apply irrelevant_components_one.
      intros contra.
      rewrite contra in Hdif.

      rewrite in_app_iff in Hdif; simpl in Hdif.
      intuition.
  Qed.

  (* Same as relevant_components_one but for multiple transitions *)

  Lemma relevant_components
    (s s' : vstate X)
    (Hprs' : protocol_state_prop X s')
    (a : plan X)
    (a_indices := List.map (@projT1 _ _) (List.map (@label_a _ _) a))
    (li : list index)
    (Heq : forall (i : index), In i li -> (s' i) = (s i))
    (Hincl : incl a_indices li)
    (Hpr : finite_protocol_plan_from X s a) :
    let res' := snd (apply_plan X s' a) in
    let res := snd (apply_plan X s a) in
    finite_protocol_plan_from X s' a /\
    (forall (i : index), In i li -> (res' i) = res i).
  Proof.
    induction a using rev_ind.
    - split.
      apply finite_protocol_plan_empty.
      assumption.
      simpl. assumption.
    - simpl in *.
      apply finite_protocol_plan_from_app_iff in Hpr.
      destruct Hpr as [Hrem Hsingle].

      spec IHa. {
        remember (map (projT1 (P:=fun n : index => vlabel (IM n))) (map label_a a)) as small.
        apply incl_tran with (m := a_indices).
        unfold a_indices.
        unfold incl; intros; simpl.
        rewrite map_app.
        rewrite map_app.
        all : intuition.
      }

      spec IHa. {
        assumption.
      }

      destruct IHa as [IHapr IHaind].

      specialize (relevant_components_one (snd (apply_plan X s a)) (snd (apply_plan X s' a))) as Hrel.

      spec Hrel. {
        apply apply_plan_last_protocol.
        all : intuition.
      }

      specialize (Hrel x); simpl in *.

      spec Hrel. {
        specialize (IHaind (projT1 (label_a x))).
        symmetry.
        apply IHaind.
        unfold incl in Hincl.
        specialize (Hincl (projT1 (label_a x))).
        apply Hincl.
        unfold a_indices.
        rewrite map_app.
        rewrite map_app.
        apply in_app_iff.
        right; simpl; intuition.
      }

      specialize (Hrel Hsingle).
      destruct Hrel as [Hrelpr Hrelind].
      split.
      + apply finite_protocol_plan_from_app_iff.
        split; intuition.
      + intros i Hi.
        specialize (IHaind i Hi).
        specialize (Heq i Hi).
        rewrite !apply_plan_app.
        simpl in *.
        destruct (apply_plan X s' a)
          as (tra', sa') eqn : eq_as'.
        destruct (apply_plan X s a)
          as (tra, sa) eqn : eq_as.
        simpl in *.
        destruct (apply_plan X sa [x])
          as (trx, sx) eqn : eq_xsa.
        destruct (apply_plan X sa' [x])
          as (trx', sx') eqn : eq_xsa'.
        simpl in *.
        destruct (decide (i = (projT1 (label_a x)))).
        * rewrite e; intuition.
        * specialize (irrelevant_components_one sa) as Hdiff.
          specialize (Hdiff x i n).

          specialize (irrelevant_components_one sa') as Hdiff0.
          specialize (Hdiff0 x i n).
          simpl in *.
          apply (f_equal snd) in eq_xsa.
          apply (f_equal snd) in eq_xsa'.

          replace sx' with (snd (composite_apply_plan IM sa' [x])).
          replace sx with (snd (composite_apply_plan IM sa [x])).
          setoid_rewrite Hdiff.
          setoid_rewrite Hdiff0.
          assumption.
  Qed.

  Lemma pre_loaded_with_all_messages_projection_protocol_transition_eq
    (s1 s2 : vstate X)
    (om1 om2 : option message)
    (l : label)
    (Ht : protocol_transition (pre_loaded_with_all_messages_vlsm X) l (s1, om1) (s2, om2))
    (i := projT1 l)
    : protocol_transition (pre_loaded_with_all_messages_vlsm (IM i)) (projT2 l) (s1 i, om1) (s2 i, om2).
  Proof.
    destruct Ht as [[Hs1 [Hom1 [Hv _]]] Ht].
    simpl in Hv. simpl in Ht. unfold vtransition in Ht. simpl in Ht.
    destruct l as [il l]. simpl in *. unfold i in *. clear i.
    destruct (vtransition (IM il) l (s1 il, om1)) as (si', om') eqn:Htj.
    inversion Ht. subst; clear Ht.
    rewrite state_update_eq.
    repeat split; try assumption.
    - apply preloaded_composed_protocol_state. assumption.
    - apply any_message_is_protocol_in_preloaded.
  Qed.

  Lemma pre_loaded_with_all_messages_projection_protocol_transition_neq
    (s1 s2 : vstate X)
    (om1 om2 : option message)
    (l : label)
    (Ht : protocol_transition (pre_loaded_with_all_messages_vlsm X) l (s1, om1) (s2, om2))
    (i : index)
    (Hi : i <> projT1 l)
    : s1 i = s2 i.
  Proof.
    destruct Ht as [[Hs1 [Hom1 [Hv _]]] Ht].
    simpl in Hv. simpl in Ht. unfold vtransition in Ht. simpl in Ht.
    destruct l as [il l]. simpl in *.
    destruct (vtransition (IM il) l (s1 il, om1)) as (si', om') eqn:Htj.
    inversion Ht. subst; clear Ht.
    rewrite state_update_neq; try assumption.
    reflexivity.
  Qed.

  Lemma pre_loaded_with_all_messages_projection_in_futures
    (s1 s2 : vstate X)
    (Hfutures : in_futures (pre_loaded_with_all_messages_vlsm X) s1 s2)
    (i : index)
    : in_futures (pre_loaded_with_all_messages_vlsm (IM i))  (s1 i) (s2 i).
  Proof.
    destruct Hfutures as [tr [Htr Hlast]].
    generalize dependent s1.
    induction tr; intros.
    - exists []. simpl in Hlast. subst.
      split; try constructor; simpl; try reflexivity.
      inversion Htr.
      apply preloaded_composed_protocol_state. assumption.
    - rewrite map_cons in Hlast. rewrite unroll_last in Hlast.
      inversion Htr. subst. simpl in *.
      specialize (IHtr s H2 eq_refl).
      destruct (decide (i = projT1 l)).
      + subst. apply pre_loaded_with_all_messages_projection_protocol_transition_eq in H3.
        destruct IHtr as [tri [Htri Hlasti]].
        exists
          ({| l := projT2 l; input := iom; destination := s (projT1 l); output := oom |}
          ::tri
          ).
        split; try apply (finite_ptrace_extend (pre_loaded_with_all_messages_vlsm (IM (projT1 l))))
        ; try assumption.
        rewrite map_cons. rewrite unroll_last. simpl.
        assumption.
      + specialize
          (pre_loaded_with_all_messages_projection_protocol_transition_neq _ _ _ _ _ H3 _ n) as Hs1i.
        rewrite Hs1i. assumption.
  Qed.

End free_projections.

Section binary_free_composition.

(**

* Free composition of two VLSMs

This serves an example of how composition can be built, but is also being
used in definiting the [byzantine_trace_prop]erties.

This instantiates the regular composition using the [bool] type as an <<index>>.

*)
  Context
    {message : Type}
    (M1 M2 : VLSM message)
    .

  Definition binary_index : Set := bool.

  Definition first : binary_index := true.
  Definition second : binary_index := false.

  Global Instance binary_index_dec :  EqDecision binary_index := _.
  Global Instance binary_index_inhabited : Inhabited binary_index
    :=
    populate first.

  Definition binary_IM
    (i : binary_index)
    : VLSM message
    :=
    match i with
    | true => M1
    | false => M2
    end.

  Definition binary_free_composition
    : VLSM message
    := free_composite_vlsm binary_IM.

  Definition binary_free_composition_fst
    := composite_vlsm_free_projection binary_IM first.

  Definition binary_free_composition_snd
    := composite_vlsm_free_projection binary_IM second.

End binary_free_composition.

Section composite_decidable_initial_message.

(** ** Composite decidable initial message

Here we show that if the [initial_message_prop]erty is decidable for every
component, then it is decidable for a finite composition as well.

*)

Context
  {message : Type}
  {index : Type}
  {IndEqDec : EqDecision index}
  (IM : index -> VLSM message)
  {i0 : Inhabited index}
  {index_listing : list index}
  (finite_index : Listing index_listing).

Lemma composite_decidable_initial_message
  (Hdec_init : forall i, vdecidable_initial_messages_prop (IM i))
  : decidable_initial_messages_prop (composite_sig IM).
Proof.
  intro m. simpl. unfold composite_initial_message_prop.
  apply
    (Decision_iff
      (P := List.Exists (fun i => vinitial_message_prop (IM i) m) index_listing)
    ).
  - rewrite <- exists_finite by (apply finite_index).
    split; intros [i Hm]; exists i.
    + exists (exist _ _ Hm). reflexivity.
    + destruct Hm as [[im Hinit] Him]. subst. assumption.
  - apply @Exists_dec. intro i. apply Hdec_init.
Qed.

End composite_decidable_initial_message.
