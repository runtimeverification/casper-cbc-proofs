Require Import List Streams Nat Bool.
Import ListNotations.
Require Import Logic.FunctionalExtensionality.

Require Import Coq.Logic.FinFun Coq.Logic.Eqdep.

From CasperCBC
  Require Import
    StreamExtras ListExtras Preamble
    VLSM.Common
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

Assume an non-empty <<index>> type (let <<i0>> be an index) and let <<IT>> be
an <<index>>ed family of [VLSM_type]s, and for each index <<i>>, let <<IS i>> be
a [VLSM_sign]ature of type <<IT i>>.
*)

    Context (i0 : index).

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
    Definition composite_m0 : message := vm0 (IM i0).

    Definition composite_l0 : composite_label
      := existT _ i0 (vl0 (IM i0)) .

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

    Definition lift_to_composite_trace
      (j : index)
      (trj : vTrace (IM j))
      : @Trace _ composite_type
      :=
      match trj with
      | Finite s l => Finite (lift_to_composite_state j s) (List.map (lift_to_composite_transition_item j) l)
      | Infinite s l => Infinite (lift_to_composite_state j s) (Streams.map (lift_to_composite_transition_item j) l)
      end.

  End composite_sig.

  Section composite_vlsm.
(**

** Constrained VLSM composition

Assume an non-empty <<index>> type (let <<i0>> be an index), let
<<IT>> be an <<index>>ed family of [VLSM_type]s, and for each index <<i>>, let
<<IS i>> be a [VLSM_sign]ature of type <<IT i>> and <<IM i>> be a VLSM of
signature <<IS i>>.
*)

    Context (i0 : index).

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
pair <<(s, om)>>, [free_composite_valid]ity is defined as [valid]ity in
the <<i>>th component <<IM i>>.
*)
    Definition free_composite_valid
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
the [free_composite_valid]ity.
*)

    Definition constrained_composite_valid
      (constraint : composite_label -> composite_state * option message -> Prop)
      (l : composite_label)
      (som : composite_state * option message)
      :=
      free_composite_valid l som /\ constraint l som.

    Definition composite_vlsm_machine
      (constraint : composite_label -> composite_state * option message -> Prop)
      : VLSM_class (composite_sig i0)
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

    Section constraint_subsumption.
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
      - apply (protocol_initial_state X2 is).
      - apply (protocol_initial_message X2).
      - apply (protocol_generated X2) with _om _s; try assumption.
        apply constraint_subsumption_protocol_valid.
        apply protocol_generated_valid with _om _s; assumption.
    Qed.

    Lemma constraint_subsumption_can_emit
      (m : message)
      (Hm : can_emit X1 m)
      : can_emit X2 m.
    Proof.
      destruct Hm as [(s0,om0) [l [s [Hv1 Ht]]]].
      assert (Hv2 := constraint_subsumption_protocol_valid _ _ _ Hv1).
      destruct Hv1 as [[_om0 Hs0] [[_s0 Hom0] Hv1]].
      apply constraint_subsumption_protocol_prop in Hs0.
      apply constraint_subsumption_protocol_prop in Hom0.
      exists (s0, om0). exists l. exists s.
      destruct Hv2 as [Hv2 Hc2].
      repeat split; try assumption.
      - exists _om0. assumption.
      - exists _s0. assumption.
    Qed.

    Lemma constraint_subsumption_preloaded_protocol_valid
      (l : label)
      (s : state)
      (om : option message)
      (Hv : protocol_valid (pre_loaded_with_all_messages_vlsm X1) l (s, om))
      : vvalid (pre_loaded_with_all_messages_vlsm X2) l (s, om).
    Proof.
      destruct Hv as [Hps [Hopm [Hv Hctr]]].
      split; try assumption.
      apply Hsubsumption.
      assumption.
    Qed.

    Lemma constraint_subsumption_preloaded_protocol_prop
      (s : state)
      (om : option message)
      (Hps : protocol_prop (pre_loaded_with_all_messages_vlsm X1) (s, om))
      : protocol_prop (pre_loaded_with_all_messages_vlsm X2) (s, om).
    Proof.
      induction Hps.
      - apply (protocol_initial_state (pre_loaded_with_all_messages_vlsm X2) is).
      - apply (protocol_initial_message (pre_loaded_with_all_messages_vlsm X2)).
      - apply (protocol_generated (pre_loaded_with_all_messages_vlsm X2)) with _om _s; try assumption.
        apply constraint_subsumption_preloaded_protocol_valid.
        destruct Hv as [Hv Hc1].
        repeat split; try assumption.
        + exists _om. assumption.
        + exists _s. assumption.
    Qed.

    Lemma constraint_subsumption_byzantine_message_prop
      (m : message)
      (Hm : byzantine_message_prop X1 m)
      : byzantine_message_prop X2 m.
    Proof.
      destruct Hm as [(s0,om0) [l [s [Hv1 Ht]]]].
      assert (Hv2 := constraint_subsumption_preloaded_protocol_valid _ _ _ Hv1).
      destruct Hv1 as [[_om0 Hs0] [[_s0 Hom0] Hv1]].
      apply constraint_subsumption_preloaded_protocol_prop in Hs0.
      apply constraint_subsumption_preloaded_protocol_prop in Hom0.
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

    Lemma constraint_subsumption_incl
      : VLSM_incl X1 X2.
    Proof.
      apply (basic_VLSM_incl (machine X1) (machine X2))
      ; intros; try (assumption || reflexivity).
      - destruct H as [_ [[_s Hom] _]]. exists _s.
        apply constraint_subsumption_protocol_prop.
        assumption.
      - apply constraint_subsumption_protocol_valid.
        assumption.
    Qed.

    Lemma constraint_subsumption_pre_loaded_with_all_messages_incl
      : VLSM_incl (pre_loaded_with_all_messages_vlsm X1) (pre_loaded_with_all_messages_vlsm X2).
    Proof.
      apply (basic_VLSM_incl (machine (pre_loaded_with_all_messages_vlsm X1)) (machine (pre_loaded_with_all_messages_vlsm X2)))
      ; intros; try (assumption || reflexivity).
      - destruct H as [_ [[_s Hom] _]]. exists _s.
        apply constraint_subsumption_preloaded_protocol_prop. assumption.
      - apply constraint_subsumption_preloaded_protocol_valid.
        assumption.
    Qed.

    End constraint_subsumption.

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

    (** Next two lemmas are corrolaries of the above, instantiates on the
      free composition whose constraint ([True]) subsumes any constraint.
    *)

    Lemma constraint_free_incl
      (constraint : composite_label -> composite_state  * option message -> Prop)
      : VLSM_incl (composite_vlsm constraint) free_composite_vlsm.
    Proof.
      apply constraint_subsumption_incl.
      intro l; intros. exact I.
    Qed.

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

(**
A component [protocol_state]'s [lift_to_composite_state] is a [protocol_state]
for the [free_composite_vlsm].
*)
    Lemma protocol_prop_composite_free_lift
      (j : index)
      (sj : vstate (IM j))
      (om : option message)
      (Hp : protocol_prop (IM j) (sj, om))
      (s := lift_to_composite_state j sj)
      : protocol_prop free_composite_vlsm (s, om).
    Proof.
      remember (sj, om) as sjom.
      generalize dependent om. generalize dependent sj.
      induction Hp; intros; inversion Heqsjom; subst; clear Heqsjom
      ; unfold s0; clear s0.
      - assert (Hinit : vinitial_state_prop free_composite_vlsm (lift_to_composite_state j s)).
        { intro i. unfold lift_to_composite_state.
          destruct (decide (i = j)).
          - subst; rewrite state_update_eq. unfold s. destruct is. assumption.
          - rewrite state_update_neq; try assumption.
            unfold composite_s0. simpl. unfold vs0.
            destruct s0 as [s0 Hinit].
            simpl.
            apply Hinit.
        }
        remember (exist (vinitial_state_prop free_composite_vlsm) (lift_to_composite_state j s) Hinit) as six.
        replace (lift_to_composite_state j s) with (proj1_sig six); try (subst; reflexivity).
        apply (protocol_initial_state free_composite_vlsm).
      - assert (Hinit : vinitial_message_prop free_composite_vlsm (proj1_sig im)).
        { exists j. exists im. reflexivity. }
        replace (lift_to_composite_state j s) with (proj1_sig (vs0 free_composite_vlsm))
        ; try (symmetry; apply state_update_id; reflexivity).
        unfold om in *; unfold s in *; clear s om.
        destruct im as [m _H]; simpl in *; clear _H.
        remember (exist (vinitial_message_prop free_composite_vlsm) m Hinit) as im.
        replace m with (proj1_sig im); try (subst; reflexivity).
        apply (protocol_initial_message free_composite_vlsm).
      - specialize (IHHp1 s _om eq_refl).
        specialize (IHHp2 _s om eq_refl).
        replace
          (@pair composite_state (option message) (lift_to_composite_state j sj) om0)
          with
          (vtransition free_composite_vlsm (existT _ j l) (lift_to_composite_state j s, om)).
        + apply (protocol_generated free_composite_vlsm) with _om (lift_to_composite_state j _s)
          ; try assumption.
          split; try exact I.
          simpl. unfold lift_to_composite_state. rewrite state_update_eq. assumption.
        + unfold vtransition. simpl. unfold lift_to_composite_state.
          rewrite state_update_eq. unfold vtransition.
          replace (@transition message
          (@projT1 (VLSM_type message)
             (fun T : VLSM_type message =>
              @sigT (@VLSM_sign message T)
                (fun S : @VLSM_sign message T => @VLSM_class message T S))
             (IM j))
          (@projT1
             (@VLSM_sign message
                (@projT1 (VLSM_type message)
                   (fun T : VLSM_type message =>
                    @sigT (@VLSM_sign message T)
                      (fun S : @VLSM_sign message T => @VLSM_class message T S))
                   (IM j)))
             (fun
                S : @VLSM_sign message
                      (@projT1 (VLSM_type message)
                         (fun T : VLSM_type message =>
                          @sigT (@VLSM_sign message T)
                            (fun S : @VLSM_sign message T =>
                             @VLSM_class message T S))
                         (IM j)) =>
              @VLSM_class message
                (@projT1 (VLSM_type message)
                   (fun T : VLSM_type message =>
                    @sigT (@VLSM_sign message T)
                      (fun S0 : @VLSM_sign message T => @VLSM_class message T S0))
                   (IM j)) S)
             (@projT2 (VLSM_type message)
                (fun T : VLSM_type message =>
                 @sigT (@VLSM_sign message T)
                   (fun S : @VLSM_sign message T => @VLSM_class message T S))
                (IM j))) (@machine message (IM j)) l
          (@pair (@vstate message (IM j)) (option message) s om))
          with (sj, om0).
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
        exists None. replace s' with (proj1_sig (exist _ _ Hs')) by reflexivity.
        apply protocol_initial_state.
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

Section projections.
(**
* Composite VLSM projections

Let us fix an indexed set of VLSMs <<IM>> and their composition <<X>> using <<constraint>>.

*)

  Context {message : Type}
          {index : Type}
          {IndEqDec : EqDecision index}
          (IM : index -> VLSM message)
          (i0 : index)
          (T := composite_type IM)
          (constraint : composite_label IM -> composite_state IM * option message -> Prop)
          (X := composite_vlsm IM i0 constraint)
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
      exists (proj1_sig (vs0 Xj)).
      destruct iom as [im|].
      - specialize (protocol_initial_message Xj ); intro Hinit.
        assert (Hpim : protocol_message_prop X im)
          by assumption.
        assert (Hini : vinitial_message_prop Xj im)
          by (exists (exist _ im Hpim); reflexivity).
        specialize (Hinit (exist _ im Hini)); simpl in Hinit.
        assumption.
      - apply (protocol_initial_state Xj).
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
      destruct Hpmj as [sj Hpmj].
      inversion Hpmj; subst.
      - exists (proj1_sig (vs0 X)).
        apply (protocol_initial_state X).
      - destruct im as [im Him].
        unfold om in *; simpl in *; clear om.
        destruct Him as [[m Hpm] Heq].
        subst; assumption.
      - destruct Hv as [sX [Heqs Hv]].
        subst s.
        destruct
          (vtransition X
            (@existT index (fun n : index => vlabel (IM n)) j l)
            (@pair (@state message (@composite_type message index IM))
               (option message) sX om))
          as [s' om'] eqn:Heqsom'.
        assert (Ht := Heqsom').
        unfold vtransition in Heqsom'. simpl in Heqsom'.
        replace
          (@vtransition message (IM j) l
            (@pair (@vstate message (IM j)) (option message) (sX j) om)
          )
          with
          (sj, iom)
          in Heqsom'.
        inversion Heqsom'; subst.
        exists (state_update IM sX j sj).
        replace
          (@pair (@state message (@type message X)) (option message)
            (@state_update message index _ IM sX j sj) om')
          with
          (vtransition X (existT (fun n : index => vlabel (IM n)) j l) (sX, om)).
        apply (protocol_prop_valid_out X).
        assumption.
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
      - apply (protocol_initial_state PreLoaded is).
      - destruct im as [m Him]. simpl in om0. clear Him.
        assert (Him : vinitial_message_prop (pre_loaded_with_all_messages_vlsm X) m)
          by exact I.
        apply (protocol_initial_message PreLoaded (exist _ m Him)).
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
      - destruct H as [_ [[_s Hpm] _]]. exists _s.
        apply proj_pre_loaded_with_all_messages_protocol_prop.
        assumption.
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
      destruct is as [is' Hinit].
      unfold s in *; simpl in *.
      specialize (lift_to_composite_state_initial is' Hinit)
      ; intro HinitX.
      remember (lift_to_composite_state IM j is') as initX.
      replace initX with (proj1_sig (exist _ initX HinitX)); try reflexivity.
      apply (protocol_initial_state X).
    - replace (lift_to_composite_state IM j s) with (proj1_sig (vs0 X)).
      + exists None. apply (protocol_initial_state X).
      + unfold lift_to_composite_state.
        rewrite state_update_id; reflexivity.
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
          (i0 : index)
          (X := free_composite_vlsm IM i0)
          .

  Definition composite_vlsm_free_projection
    (i : index)
    : VLSM message
    :=
    composite_vlsm_constrained_projection IM i0 (free_constraint IM) i.

  Lemma preloaded_composed_protocol_state
    (s : vstate X)
    (Hs : protocol_state_prop (pre_loaded_with_all_messages_vlsm X) s)
    (i : index)
    : protocol_state_prop (pre_loaded_with_all_messages_vlsm (IM i)) (s i).
  Proof.
    revert i. generalize dependent s.
    apply
      (protocol_state_prop_ind (pre_loaded_with_all_messages_vlsm X)
        (fun (s : vstate (pre_loaded_with_all_messages_vlsm X)) =>
          forall i : index, protocol_state_prop (pre_loaded_with_all_messages_vlsm (IM i)) (s i)
        )
      ); intros.
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
        specialize (Hs i).
        apply protocol_state_prop_iff. right.
        exists li'. exists (s i, om). exists om'.
        repeat split; try assumption.
        exists (proj1_sig (vs0 (pre_loaded_with_all_messages_vlsm (IM i)))).
        destruct om as [m|].
        * assert (Him : vinitial_message_prop  (pre_loaded_with_all_messages_vlsm (IM i)) m)
            by exact I.
          pose (exist _ m Him) as im.
          apply (protocol_initial_message (pre_loaded_with_all_messages_vlsm (IM i)) im).
        * apply (protocol_initial_state (pre_loaded_with_all_messages_vlsm (IM i))).
      + rewrite state_update_neq; try assumption. apply Hs.
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
    - destruct om1 as [m1|]; exists (proj1_sig (vs0 (IM il))).
      + assert (Hm1 : vinitial_message_prop (pre_loaded_with_all_messages_vlsm (IM il)) m1) by exact I.
        replace m1 with (proj1_sig (exist _ m1 Hm1)) by reflexivity.
        apply (protocol_initial_message (pre_loaded_with_all_messages_vlsm (IM il))).
      + apply (protocol_initial_state (pre_loaded_with_all_messages_vlsm (IM il))).
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
    := free_composite_vlsm binary_IM first.

  Definition binary_free_composition_fst
    := composite_vlsm_free_projection binary_IM first first.

  Definition binary_free_composition_snd
    := composite_vlsm_free_projection binary_IM first second.

End binary_free_composition.
