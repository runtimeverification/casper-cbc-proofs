Require Import List Streams Nat Bool.
Import ListNotations.
Require Import Logic.FunctionalExtensionality.

Require Import Coq.Logic.FinFun Coq.Logic.Eqdep.

From CasperCBC
     Require Import Lib.StreamExtras Lib.ListExtras Lib.Preamble VLSM.Common.

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
          {IndEqDec : EqDec index}
          .
          
  Section composite_type.

(**

** The type of a composite VLSM

Let IM be a family of VLSMs indexed by <<index>> and for each index <<i>>,
let <<IT i>> be the [VLSM_type] of VLSM <<IM i>>.  Note that all 
[VLSM_type]s share the same type of <<message>>s.

*)

    Context (IT : index -> VLSM_type message).

(**
A [composite_state] is an indexed family of [state]s, yielding for each
index <<n>> a [state] of <<IT n>>, the [VLSM_type] corresponding to <<n>>.

Note that the [composite_state] type is the dependent product type of the 
family of types <<[@state _ (IT n) | n <- index]>>.
*)
    Definition _composite_state : Type :=
      forall n : index, (@state _ (IT n)).

(**
A [composite_label] is a pair between an index <<N>> and a [label] of <<IT n>>.

Note that the [composite_label] type is the dependent sum of the family of
types <<[@label _ (IT n) | n <- index]>>.
*)
    Definition _composite_label
      : Type
      := sigT (fun n => @label _ (IT n)).

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
               (si : @state message (IT i))
               (j : index)
      : @state message (IT j)
      :=
      match eq_dec j i with
      | left e => eq_rect_r (fun i => @state message (IT i)) si e
      | _ => s j
      end.

(**
The next few results describe several properties of the [state_update] operation.
*)
    Lemma state_update_neq
               (s : composite_state)
               (i : index)
               (si : @state message (IT i))
               (j : index)
               (Hneq : j <> i)
      : state_update s i si j = s j.
    Proof.
      unfold state_update. destruct (eq_dec j i); try contradiction. reflexivity.
    Qed.

    Lemma state_update_eq
               (s : composite_state)
               (i : index)
               (si : @state message (IT i))
      : state_update s i si i = si.
    Proof.
      unfold state_update.
      rewrite eq_dec_refl. reflexivity.
    Qed.

    Lemma state_update_id
               (s : composite_state)
               (i : index)
               (si : @state message (IT i))
               (Heq : s i = si)
      : state_update s i si = s.
    Proof.
      apply functional_extensionality_dep_good.
      intro j.
      destruct (eq_dec j i).
      - subst. apply state_update_eq.
      - apply state_update_neq. assumption.
    Qed.

    Lemma state_update_twice
               (s : composite_state)
               (i : index)
               (si si': @state message (IT i))
      : state_update (state_update s i si) i si' = state_update s i si'.
    Proof.
      apply functional_extensionality_dep_good.
      intro j.
      destruct (eq_dec j i).
      - subst. rewrite state_update_eq. symmetry. apply state_update_eq.
      - repeat rewrite state_update_neq; try assumption.
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

    Context {IT : index -> VLSM_type message}
            (i0 : index)
            (IS : forall i : index, VLSM_sign (IT i)).

(**
A [composite_state] has the [initial_state_prop]erty if all of its component
states have the [initial_state_prop]erty in the corresponding component signature.
*)
    Definition composite_initial_state_prop
               (s : composite_state IT)
      : Prop
      :=
        forall n : index, @initial_state_prop _ _ (IS n) (s n).

    Definition composite_initial_state
      := { s : composite_state IT | composite_initial_state_prop s }.

    Definition composite_s0 : composite_initial_state.
      exists (fun (n : index) => proj1_sig (@s0 _ _ (IS n))).
      intro i. destruct s0 as [s Hs]. assumption.
    Defined.

(**
A message has the [initial_message_prop]erty in the [composite_sig]nature
iff it has the [initial_message_prop]erty in any of the component signatures.
*)
    Definition composite_initial_message_prop (m : message) : Prop
      :=
        exists (n : index) (mi : @initial_message _ _ (IS n)), proj1_sig mi = m.

    (* An explicit argument for the initial state witness is no longer required: *)
    Definition composite_m0 : message := @m0 _ _ (IS i0).

    Definition composite_l0 : composite_label IT
      := existT _ i0 (@l0 _ _ (IS i0)) .

    Definition composite_sig
      : VLSM_sign (composite_type IT)
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
      (sj : @state _ (IT j))
      (s0X := proj1_sig (@s0 _ _ composite_sig))
      : composite_state IT
      := state_update IT s0X j sj
      .
    
    Lemma lift_to_composite_state_initial
      (j : index)
      (sj : @state _ (IT j))
      (Hinitj : initial_state_prop sj)
      : @initial_state_prop _ _ composite_sig (lift_to_composite_state j sj)
      .
    Proof.
      intro i.
      unfold lift_to_composite_state.
      destruct (eq_dec i j).
      - subst. rewrite state_update_eq. assumption.
      - rewrite state_update_neq; try assumption.
        simpl. 
        destruct s0 as [s Hs].
        assumption.
    Qed.

    Definition lift_to_composite_transition_item
      (j : index)
      (item : @transition_item _ (IT j))
      (s0X := proj1_sig (@s0 _ _ composite_sig))
      : @transition_item _ (composite_type IT)
      .
      destruct item.
      split.
      - exact (existT _ j l).
      - exact input.
      - exact (lift_to_composite_state j destination).
      - exact output.
    Defined.

    Definition lift_to_composite_trace
      (j : index)
      (trj : @Trace _ (IT j))
      : @Trace _ (composite_type IT)
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

    Context {IT : index -> VLSM_type message}
            (i0 : index)
            {IS : forall i : index, VLSM_sign (IT i)}
            (IM : forall n : index, VLSM (IS n)).

(**
The [transition] function for the [composite_vlsm] is defined as follows
takes a transition in the VLSM corresponding to the given [composite_label]
and returnes the produced message together with the state updated on that
component:
*)
    Definition composite_transition
               (l : composite_label IT)
               (som : composite_state IT * option message)
      : composite_state IT * option message
      :=
      let (s, om) := som in
      let (i, li) := l in
      let (si', om') := transition li (s i, om) in
      (state_update IT s i si',  om').

(**
Given a [composite_label] <<(i, li)>> and a [composite_state]-message
pair <<(s, om)>>, [free_composite_valid]ity is defined as [valid]ity in 
the <<i>>th component <<IM i>>.
*)
    Definition free_composite_valid
               (l : composite_label IT)
               (som : composite_state IT * option message)
      : Prop
      :=
      let (s, om) := som in
      let (i, li) := l in
      valid li (s i, om).

(**
A <<constraint>> for a composite VLSM is a [valid]ity condition defined
directly on [composite_label]s and [composite_state]s, thus being able to
impose a global condition.

[constrained_composite_valid]ity interposes such a <<constraint>> on top of
the [free_composite_valid]ity.
*)

    Definition constrained_composite_valid
               (constraint : composite_label IT -> composite_state IT  * option message -> Prop)
               (l : composite_label IT)
               (som : composite_state IT * option message)
      :=
        free_composite_valid l som /\ constraint l som.

    Definition composite_vlsm
               (constraint : composite_label IT -> composite_state IT * option (message) -> Prop)
      : VLSM (composite_sig i0 IS)
      :=
        {|  transition := composite_transition
            ;   valid := constrained_composite_valid constraint
        |}.

    Definition composite_valid
      (constraint : composite_label IT -> composite_state IT * option (message) -> Prop)
      := @valid _ _ _ (composite_vlsm constraint).

    Section constraint_subsumption.
(**

** Constraint subssumption

A <<constraint1>> is subssumed by <<constraint2>> if <<constraint1> is stronger
than <<constraint2>> for any input.
*)

    Definition constraint_subsumption
        (constraint1 constraint2 : composite_label IT -> composite_state IT * option message -> Prop)
        :=
        forall (l : composite_label IT) (som : composite_state IT * option message),
          constraint1 l som -> constraint2 l som.

    Context
      (constraint1 constraint2 : composite_label IT -> composite_state IT * option message -> Prop)
      (Hsubsumption : constraint_subsumption constraint1 constraint2)
      (X1 := composite_vlsm constraint1)
      (X2 := composite_vlsm constraint2)
      (S := composite_sig i0 IS)
      (T := composite_type IT)
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
      : @valid _ _ _ X2 l (s, om)
      .
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

(* end hide *)

(**
Then <<X1>> is trace-included into <<X2>>.
*)

    Lemma constraint_subsumption_incl
      : VLSM_incl X1 X2
      .
    Proof.
      apply (basic_VLSM_incl X1 X2)
      ; intros; try (assumption || reflexivity).
      - destruct H as [_ [[_s Hom] _]]. exists _s.
        apply constraint_subsumption_protocol_prop.
        assumption.
      - apply constraint_subsumption_protocol_valid.
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
               (l : composite_label IT)
               (som : composite_state IT * option message)
      : Prop
      :=
        True.

    Definition free_composite_vlsm : VLSM (composite_sig i0 IS)
      :=
        composite_vlsm free_constraint
    .


(**
A component [protocol_state]'s [lift_to_composite_state] is a [protocol_state]
for the [free_composite_vlsm].
*)
    Lemma protocol_prop_composite_free_lift
      (S := (composite_sig i0 IS))
      (j : index)
      (sj : @state _ (IT j))
      (om : option message)
      (Hp : protocol_prop (IM j) (sj, om))
      (s := lift_to_composite_state i0 IS j sj)
      : protocol_prop free_composite_vlsm (s, om)
      .
    Proof.
      remember (sj, om) as sjom.
      generalize dependent om. generalize dependent sj.
      induction Hp; intros; inversion Heqsjom; subst; clear Heqsjom
      ; unfold s0; clear s0.
      - assert (Hinit : @initial_state_prop _ _ S (lift_to_composite_state i0 IS j s)).
        { intro i. unfold lift_to_composite_state.
          destruct (eq_dec i j).
          - subst; rewrite state_update_eq. unfold s. destruct is. assumption.
          - rewrite state_update_neq; try assumption.
            destruct @Common.s0 as [s00 Hinit].
            simpl.
            apply Hinit.
        }
        remember (exist (@initial_state_prop _ _ S) (lift_to_composite_state i0 IS j s) Hinit) as six.
        replace (lift_to_composite_state i0 IS j s) with (proj1_sig six); try (subst; reflexivity).
        apply (protocol_initial_state free_composite_vlsm).
      - assert (Hinit : @initial_message_prop _ _ S (proj1_sig im)).
        { exists j. exists im. reflexivity. }
        replace (lift_to_composite_state i0 IS j s) with (proj1_sig (@Common.s0 _ _ S))
        ; try (symmetry; apply state_update_id; reflexivity).
        unfold om in *; unfold s in *; clear s om.
        destruct im as [m _H]; simpl in *; clear _H.
        remember (exist (@initial_message_prop _ _ S) m Hinit) as im.
        replace m with (proj1_sig im); try (subst; reflexivity).
        apply (protocol_initial_message free_composite_vlsm).
      - specialize (IHHp1 s _om eq_refl).
        specialize (IHHp2 _s om eq_refl).
        replace
          (@pair (composite_state IT) (option message) (@lift_to_composite_state IT i0 IS j sj) om0)
          with (@transition _ _ _ free_composite_vlsm (existT _ j l) (lift_to_composite_state i0 IS j s, om)).
        + apply (protocol_generated free_composite_vlsm) with _om (lift_to_composite_state i0 IS j _s)
          ; try assumption.
          split; try exact I.
          simpl. unfold lift_to_composite_state. rewrite state_update_eq. assumption.
        + simpl. unfold lift_to_composite_state. rewrite state_update_eq. rewrite H0.
          f_equal.
          apply state_update_twice.
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
          {IndEqDec : EqDec index}
          (i0 : index)
          {IT : index -> VLSM_type message}
          {IS : forall i : index, VLSM_sign (IT i)}
          (IM : forall n : index, VLSM (IS n))
          (T := composite_type IT)
          (S := composite_sig i0 IS)
          (constraint : @label _ T -> @state _ T * option message -> Prop)
          (X := composite_vlsm i0 IM constraint)
          .

(**
The [VLSM_type] of a projection of <<X>> to component <<i>> is <<IT i>>, the
type of the <<i>>th component of <<X>>.
We defined the signature of the projection to be the same as that of the component,
with the exception that the [initial_message]s for the projection are defined
to be all [protocol_message]s of <<X>>:

*)
  Definition composite_vlsm_constrained_projection_sig (i : index) : VLSM_sign (IT i)
    :=
      {|      initial_state_prop := @initial_state_prop _ _ (IS i)
          ;   initial_message_prop := fun pmi => exists xm : (@protocol_message _ _ _ X), proj1_sig xm = pmi
          ;   s0 := @s0 _ _ (IS i)
          ;   m0 := @m0 _ _ (IS i)
          ;   l0 := @l0 _ _ (IS i)
      |}.

(**
[projection_valid]ity is defined as the projection of [protocol_valid]ity of <<X>>:
*)

  Definition projection_valid
    (i : index)
    (li : @label _ (IT i))
    (siomi : @state _ (IT i) * option message)
    :=
    let (si, omi) := siomi in
    exists (s : @state _ T),
      s i = si /\ protocol_valid X (existT _ i li) (s, omi)
    .

(**
Since [projection_valid]ity is derived from [protocol_valid]ity, which in turn
depends on [valid]ity in the component, it is easy to see that
[projection_valid]ity implies [valid]ity in the component.
*)
  Lemma projection_valid_implies_valid
    (i : index)
    (li : @label _ (IT i))
    (siomi : @state _ (IT i) * option message)
    (Hcomposite : projection_valid i li siomi)
    : @valid _ _ _ (IM i) li siomi
    .
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
  Definition composite_vlsm_constrained_projection
             (i : index)
    : VLSM (composite_vlsm_constrained_projection_sig i) :=
    {|  transition :=  @transition _ _ _ (IM i)
     ;  valid := projection_valid i
    |}.

  Section fixed_projection.

(**

** Projection traces are Byzantine

Let us fix an index <<j>> and let <<Xj>> be the projection of <<X>> on
component <<j>>.

In this section we establish some basic properties for projections, building up
to Lemma [proj_pre_loaded_incl], which guarantees that all
[protocol_trace]s of <<Xj>> are also [protocol_trace]s for the
[pre_loaded_vlsm] associated to the component <<IM j>>.
In particular this ensures that the byzantine traces of <<IM j>> include all
[protocol_trace]s of <<Xj>> (see Lemma [pre_loaded_alt_eq]).

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
      (s : @state _ T)
      (Hinit : @initial_state_prop _ _ S s)
      : @initial_state_prop _ _ (sign Xj) (s j)
      .
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
      : option_protocol_message_prop Xj iom
      .
    Proof.
      exists (proj1_sig s0).
      destruct iom as [im|].
      - specialize (protocol_initial_message Xj ); intro Hinit.
        assert (Hpim : protocol_message_prop X im)
          by assumption.
        assert (Hini : @initial_message_prop _ _ (sign Xj) im)
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
      : option_protocol_message_prop X iom
      .
    Proof.
      destruct Hpmj as [sj Hpmj].
      inversion Hpmj; subst.
      - exists (proj1_sig (@s0 _ _ S)).
        apply (protocol_initial_state X).
      - destruct im as [im Him].
        unfold om in *; simpl in *; clear om.
        destruct Him as [[m Hpm] Heq].
        subst; assumption.
      - destruct Hv as [sX [Heqs Hv]].
        specialize (protocol_prop_valid_out X (existT (fun n : index => label) j l) sX om Hv)
        ; intro HpsX'.
        simpl in Heqs. rewrite <- Heqs in *. clear Heqs.
        remember
          (@transition _ _ _ X
            (@existT index (fun n : index => @label message (IT n)) j l)
            (@pair (@state message (@composite_type message index IT))
               (option message) sX om))
          as som'.
        destruct som' as [s' om'].
        simpl in Heqsom'.
        rewrite H0 in Heqsom'.
        inversion Heqsom'; subst.
        exists (state_update IT sX j sj).
        assumption.
    Qed.

(**
As a stepping stone towards proving trace inclusion between <<Xj>> and
the [pre_loaded_vlsm] associated to <<IM j>>, we prove that the
[protocol_prop]erty is transferred.
*)
    Lemma proj_pre_loaded_protocol_prop
      (PreLoaded := pre_loaded_vlsm (IM j))
      (s : state)
      (om : option message)
      (Hps : protocol_prop Xj (s, om))
      : protocol_prop PreLoaded (s, om).
    Proof.
      induction Hps.
      - apply (protocol_initial_state PreLoaded is).
      - destruct im as [m Him]. simpl in om0. clear Him.
        assert (Him : @initial_message_prop _ _ (pre_loaded_vlsm_sig X) m)
          by exact I.
        apply (protocol_initial_message PreLoaded (exist _ m Him)).
      - apply (protocol_generated PreLoaded) with _om _s; try assumption.
        apply projection_valid_implies_valid. assumption.
    Qed.

(**
We can now finally prove the main result for this section:
*)
    Lemma proj_pre_loaded_incl
      (PreLoaded := pre_loaded_vlsm (IM j))
      : VLSM_incl Xj PreLoaded
      .
    Proof.
      apply (basic_VLSM_incl Xj PreLoaded)
      ; intros; try (assumption || reflexivity).
      - destruct H as [_ [[_s Hpm] _]]. exists _s.
        apply proj_pre_loaded_protocol_prop.
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
      (lj : @label _ (IT j))
      (sj : @state _ (IT j))
      (om : option message)
      (Hpv : protocol_valid Xj lj (sj, om))
      (s : @state _ (type X))
      (Hs : protocol_state_prop X s)
      (Hsi : s j = sj)
      , @valid _ _ _ X (existT _ j lj) (s, om)
    .

  Lemma projection_friendliness_sufficient_condition_protocol_message
    (l : label)
    (s : state)
    (om : option message)
    (Hv : protocol_valid Xj l (s, om))
    : option_protocol_message_prop X om
    .
  Proof.
    destruct Hv as [Hpsj [Hpmj [sx [Hs [HpsX [HpmX Hv]]]]]].
    assumption.
  Qed.

  Lemma projection_friendliness_sufficient_condition_protocol_state
    (Hfr : projection_friendliness_sufficient_condition)
    (s : state)
    (om : option message)
    (Hp : protocol_prop Xj (s, om))
    : protocol_state_prop X (lift_to_composite_state i0 IS j s)
    .
  Proof.
    remember (s, om) as som.
    generalize dependent om. generalize dependent s.
    induction Hp; intros; inversion Heqsom; subst; clear Heqsom.
    - exists None.
      destruct is as [is' Hinit].
      unfold s in *; simpl in *.
      specialize (lift_to_composite_state_initial i0 IS j is' Hinit)
      ; intro HinitX.
      remember (lift_to_composite_state i0 IS j is') as initX.
      replace initX with (proj1_sig (exist _ initX HinitX)); try reflexivity.
      apply (protocol_initial_state X).
    - replace (lift_to_composite_state i0 IS j s) with (proj1_sig (@s0 _ _ (sign X))).
      + exists None. apply (protocol_initial_state X).
      + unfold lift_to_composite_state.
        rewrite state_update_id; reflexivity.
    - specialize (IHHp1 s _om eq_refl).
      exists om0.
      replace
        (lift_to_composite_state i0 IS j s0, om0)
        with (@transition _ _ _ X (existT _ j l) (lift_to_composite_state i0 IS j s, om)).
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
            (existT (fun n : index => label) j l)
            (lift_to_composite_state i0 IS j s)
            _omX
            HpsX
            _sX
            om
            HpmX
            Hfr
          ).
      + simpl. unfold lift_to_composite_state at 1. rewrite state_update_eq.
        rewrite H0.
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
    : @valid _ _ _ X (existT _ j l) (lift_to_composite_state i0 IS j s, om)
    .
  Proof.
    specialize (projection_friendliness_sufficient_condition_protocol_state Hfr s)
    ; intros HpsX.
    specialize (Hfr l s om Hv (lift_to_composite_state i0 IS j s)).
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
    : protocol_transition X (existT _ j l) (lift_to_composite_state i0 IS j is, iom) (lift_to_composite_state i0 IS j os, oom)
    .
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
      replace (transition l (is, iom)) with (os, oom).
      f_equal.
      unfold lift_to_composite_state.
      apply state_update_twice.
  Qed.

  Lemma projection_friendliness_sufficient_condition_finite_ptrace
    (Hfr : projection_friendliness_sufficient_condition)
    (s : state)
    (ls : list transition_item)
    (Hpxt : finite_protocol_trace_from Xj s ls)
    : finite_protocol_trace_from X (lift_to_composite_state i0 IS j s) (List.map (lift_to_composite_transition_item i0 IS j) ls)
    .
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
    : infinite_protocol_trace_from X (lift_to_composite_state i0 IS j s) (Streams.map (lift_to_composite_transition_item i0 IS j) ls)
    .
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
    : protocol_trace_prop X (lift_to_composite_trace i0 IS j t)
    .
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
          {IndEqDec : EqDec index}
          (i0 : index)
          {IT : index -> VLSM_type message}
          {IS : forall i : index, VLSM_sign (IT i)}
          (IM : forall n : index, VLSM (IS n))
          (X := free_composite_vlsm i0 IM)
          .

  Definition composite_vlsm_free_projection_sig
             (i : index)
    : VLSM_sign (IT i)
    :=
      composite_vlsm_constrained_projection_sig i0 IM free_constraint i.

  Definition composite_vlsm_free_projection
             (i : index)
    : VLSM (composite_vlsm_free_projection_sig i)
    :=
      composite_vlsm_constrained_projection i0 IM free_constraint i.

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
    {T1 T2 : VLSM_type message}
    {S1 : VLSM_sign T1}
    {S2 : VLSM_sign T2}
    (M1 : VLSM S1)
    (M2 : VLSM S2)
    .

  Definition binary_index : Set := bool.

  Definition first : binary_index := true.
  Definition second : binary_index := false.

  Global Instance binary_index_dec :  EqDec binary_index := bool_dec.

  Definition binary_IT
    (i : binary_index)
    :=
    match i with
    | true => (type M1)
    | false => (type M2)
    end.

  Definition binary_IS
    (i : binary_index)
    : VLSM_sign (binary_IT i)
    :=
    match i with
    | true => S1
    | false => S2
    end.

  Definition binary_IM
    (i : binary_index)
    : VLSM (binary_IS i)
    :=
    match i with
    | true => M1
    | false => M2
    end.

  Definition binary_free_composition
    : VLSM (composite_sig first binary_IS)
    := free_composite_vlsm first binary_IM.

  Definition binary_free_composition_fst
    := composite_vlsm_free_projection first binary_IM  first.

  Definition binary_free_composition_snd
    := composite_vlsm_free_projection first binary_IM  second.

End binary_free_composition.
