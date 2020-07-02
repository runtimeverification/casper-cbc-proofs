Require Import FinFun Streams.
From CasperCBC   
Require Import Lib.Preamble VLSM.Common VLSM.Composition VLSM.Validating.

(**
** Byzantine traces.

*** Definition and basic properties

In this section we introduce two definitions for byzantine traces,
then show them equivalent, and equivalent with traces on the
corresponding pre-loaded VLSM.

We will work with a fixed VLSM <<M>> with signature <<S>> and of type <<T>>.
*)

Section ByzantineTraces.
Context
    {message : Type}
    {T : VLSM_type message}
    {S : LSM_sig T}
    (M : VLSM S)
    .

(**

The first definition says that a trace has the [byzantine_trace_prop]erty
if it is the projection of
a trace which can be obtained by freely composing <<M>> with an arbitrary
VLSM <<M'>> (of a signatulre <<S'>> and type <<T'>> over the same set of <<message>>s).

Below, [binary_free_composition_fst] represents the projection of
the free composition between <<M>> and <<M'>> to the component corresponding
to <<M>>.
*)

Definition byzantine_trace_prop
    (tr : @Trace _ T) :=
    exists (T' : VLSM_type message) (S' : LSM_sig T') (M' : VLSM S')
        (Proj := binary_free_composition_fst M M'),
        protocol_trace_prop Proj tr.

(**

The first result says that all traces with the [byzantine_trace_prop]erty
for a VLSM <<M>> are traces of the [pre_loaded_vlsm] associated to <<M>>:
*)

Lemma byzantine_pre_loaded
    (PreLoaded := pre_loaded_vlsm M)
    (tr : @Trace _ T)
    (Hbyz : byzantine_trace_prop tr)
    : protocol_trace_prop PreLoaded tr.
Proof.
    destruct Hbyz as [T' [S' [M' Htr]]].
    simpl in Htr.
    specialize
        (proj_pre_loaded_incl
            first
            (binary_IM M M')
            free_constraint
            first
            tr
            Htr
        ); intros Htr'.
    assumption.
Qed.

(**

*** An alternative definition for byzantine traces

The [alternate_byzantine_trace_prop]erty relies on the composition
of the VLSM with a special VLSM which can produce all messages.

We will define its type ([all_messages_type]),
signature ([all_messages_sig]) and the VLSM itself ([all_messages_vlsm]) below.

The type of the [all_messages_vlsm] sets the [label] set to consist of all
<<message>>s and the [state] to consist of a single state (here [tt]).
*)

Definition all_messages_type : VLSM_type message :=
    {| label := message
     ; state := unit
    |}.

(**

The [all_messages_vlsm] signature further says that the (single) state is
initial and no messages are initial.
It takes as parameter a <<message>> to ensure that the sets of labels and
messages are both non-empty.
*)

Definition all_messages_sig
    (inhm : message)
    : LSM_sig all_messages_type
    :=
    {| initial_state_prop := fun s => True
     ; initial_message_prop := fun m => False
     ; s0 := exist (fun s: @state _ all_messages_type => True) tt I
     ; m0 := inhm
     ; l0 := inhm
    |}.

(**

The [transition] function of the [all_messages_vlsm] generates the
message given as a label: 
*)

Definition all_messages_transition
    (l : @label _ all_messages_type)
    (som : @state _ all_messages_type * option message)
    : @state _ all_messages_type * option message
    := (tt, Some l)
    .


(**

The [valid]ity predicate specifies that all transitions are valid

*)
Definition all_messages_valid
    (l : @label _ all_messages_type)
    (som : @state _ all_messages_type * option message)
    : Prop
    := True.

Definition all_messages_vlsm
    (inhm : message)
    : VLSM (all_messages_sig inhm)
    :=
    {| transition := all_messages_transition
     ; valid := all_messages_valid
    |}
    .

(**

Using the VLSM defined above, we can define the [alternate_byzantine_trace_prop]erty
of a trace <<tr>> for the VLSM <<M>> as being a trace in the projection
of the free composition between <<M>> and the [all_messages_vlsm],
to the component corresponding to <<M>>:

*)

Definition alternate_byzantine_trace_prop
    (tr : @Trace _ T)
    (Proj := binary_free_composition_fst M (all_messages_vlsm m0))
    :=
    protocol_trace_prop Proj tr.

(**

Since the [byzantine_trace_prop]erty was referring to the free composition
to any other VLSM, we can instantiate that definition to the
[all_messages_vlsm] to derive that a trace with the
[alternate_byzantine_trace_prop]erty also has the [byzantine_trace_prop]erty.

*)

Lemma byzantine_alt_byzantine
    (tr : @Trace _ T)
    (Halt : alternate_byzantine_trace_prop tr)
    : byzantine_trace_prop tr.
Proof.
    exists all_messages_type.
    exists (all_messages_sig m0).
    exists (all_messages_vlsm m0).
    assumption.
Qed.

(**
*** Equivalence between the two byzantine trace definitions

In this section we prove that the [alternate_byzantine_trace_prop]erty is
equivalent to the [byzantine_trace_prop]erty.

Since we have already proven that the [alternate_byzantine_trace_prop]erty
implies the [byzantine_trace_prop]erty (Lemma [byzantine_trace_prop]erty]), 
and since we know that the traces with the [byzantine_trace_prop]erty
are [protocol_trace]s for the [pre_loaded_vlsm], to prove the
equivalence it is enough to close the circle by proving the
[VLSM_incl]usion between the [pre_loaded_vlsm] and the projection VLSM used
in the definition of the [alternate_byzantine_trace_prop]erty.

*)

Section pre_loaded_byzantine_alt.

Context
    (PreLoaded := pre_loaded_vlsm M)
    (Proj := binary_free_composition_fst M (all_messages_vlsm m0))
    (Alt := binary_free_composition M (all_messages_vlsm m0))
    .

(**
Let <<PreLoaded>> denote the [pre_loaded_vlsm] of <<M>>, <<Alt>> denote
the free composition of <<M>> with the [all_messages_vlsm],
and <<Proj>> denote the projection of <<Alt>> to the component of <<M>>.

First, note that using the results above it is easy to prove the inclusion
of <<Proj>> into <<Preloaded>>
*)

(* begin show *)
    Lemma alt_pre_loaded_incl
        : VLSM_incl Proj PreLoaded
        .
    Proof.
        intros t Hpt.
        apply byzantine_pre_loaded.
        apply byzantine_alt_byzantine.
        assumption.
    Qed.
(* end show *)

(**
To prove the reverse inclusion (between <<PreLoaded>> and <<Proj>>) we will use the
[basic_VLSM_incl] meta-result about proving inclusions bewteen
VLSMs which states that
- if all [valid] messages in the first are [protocol_message]s in the second, and
- if all [protocol_state]s in the first are also [protocol_state]s in the second,
- and if all [protocol_transition]s in the first are also [protocol_transition]s
in the second,
- then the first VLSM is included in the second.

We will tackle each of these properties in the sequel.

First note that _all_ messages are [protocol_message]s for <<Alt>>, as 
[all_messages_vlsm] can generate any message without changing state.
*)

    Lemma alt_option_protocol_message
        (om : option message)
        : option_protocol_message_prop Alt om.
    Proof.
        exists (proj1_sig (@s0 _ _ (sign Alt))).
        destruct om as [m|]; try apply protocol_initial_state.
        remember (proj1_sig (@s0 _ _ (sign Alt))) as s.
        assert (Ht : @transition _ _ _ Alt (existT _ second m) (s, None) = (s, Some m)).
        { simpl.
          f_equal.
          apply state_update_id.
          subst. reflexivity.
        }
        rewrite <- Ht.
        assert (Hps : protocol_prop Alt (s, None))
            by (subst; apply protocol_initial_state). 
        apply protocol_generated with None s; try assumption.
        split; exact I.
    Qed.

(**
Using the above, it is straight-forward to show that:
*)

    Lemma alt_proj_option_protocol_message
        (m : option message)
        : option_protocol_message_prop Proj m.
(* begin show *)
    Proof.
        apply protocol_message_projection.
        apply alt_option_protocol_message.
    Qed.
(* end show *)

(**
Next we define the "lifing" of a [state] <<s>> from <<M>> to <<Alt>>,
by simply setting to <<s>> the  corresponding component of the initial
(composed) state [s0] of <<Alt>>.
*)
    Definition lifted_alt_state
        (s : @state _ T)
        (init := proj1_sig (@s0 _ _ (sign Alt)))
        : @state _ (type Alt)
        := @state_update _ _ binary_index_dec binary_IT init first s.

(**
Lifting a [protocol_state] of <<PreLoaded>> we obtain a [protocol_state] of <<Alt>>.
*)
    Lemma preloaded_alt_protocol_state
        (sj : state)
        (om : option message)
        (Hp : protocol_prop PreLoaded (sj, om))
        : protocol_state_prop Alt (lifted_alt_state sj).
    Proof.
      remember (sj, om) as sjom.
      generalize dependent om. generalize dependent sj.
      induction Hp; intros; inversion Heqsjom; subst; clear Heqsjom.
      - assert (Hinit : @initial_state_prop _ _ (sign Alt) (lifted_alt_state s)).
        { intros [|]; try exact I.
          unfold lifted_alt_state.
          rewrite state_update_eq. unfold s. destruct is. assumption.
        }
        remember (exist (@initial_state_prop _ _ (sign Alt)) (lifted_alt_state s) Hinit) as six.
        replace (lifted_alt_state s) with (proj1_sig six); try (subst; reflexivity).
        exists None.
        apply (protocol_initial_state Alt).
      - assert (Hinit : @initial_state_prop _ _ (sign Alt) (lifted_alt_state s)).
        { intros [|]; try exact I.
          unfold lifted_alt_state.
          rewrite state_update_eq. unfold s. destruct s0. assumption.
        }
        remember (exist (@initial_state_prop _ _ (sign Alt)) (lifted_alt_state s) Hinit) as six.
        replace (lifted_alt_state s) with (proj1_sig six); try (subst; reflexivity).
        exists None.
        apply (protocol_initial_state Alt).
      - specialize (IHHp1 s _om eq_refl). clear IHHp2.
        remember (@transition _ _ _ Alt (existT _ first l) (lifted_alt_state s, om)) as xsom'.
        destruct xsom' as [xs' om'].
        destruct IHHp1 as [_omX Hlift].
        exists om'.
        replace (lifted_alt_state sj) with xs'.
        + rewrite Heqxsom'.
          destruct (alt_option_protocol_message om) as [_sX Hopm].
          apply (protocol_generated Alt) with _omX _sX; try assumption.
          split; try exact I.
          assumption.
        + simpl in Heqxsom'. 
          unfold lifted_alt_state at 1 in Heqxsom'.
          rewrite state_update_eq in Heqxsom'.
          rewrite H0 in Heqxsom'.
          inversion Heqxsom'; subst.
          unfold lifted_alt_state.
          apply state_update_twice.
    Qed.

(**
Finally, we can use [basic_VLSM_incl] together with the 
results above to show that <<Preloaded>> is included in <<Proj>>.
*)

    Lemma pre_loaded_alt_incl
        : VLSM_incl PreLoaded Proj
        .
    Proof.
        apply (basic_VLSM_incl PreLoaded Proj)
        ; intros; try (assumption || reflexivity).
        - apply alt_proj_option_protocol_message.
        - exists (lifted_alt_state s).
          split; try reflexivity.
          destruct H as [[_om Hps] [Hpm Hv]].
          repeat split; try assumption.
          + apply preloaded_alt_protocol_state with _om. assumption.
          + apply alt_option_protocol_message.
    Qed.

(**
Hence, <<Preloaded>> and <<Proj>> are actually trace-equal:
*)
(* begin show *)
    Lemma pre_loaded_alt_eq
        : VLSM_eq PreLoaded Proj
        .
    Proof.
        split.
        - apply pre_loaded_alt_incl.
        - apply alt_pre_loaded_incl.
    Qed.

(* end show *)


End pre_loaded_byzantine_alt.

(**
Finally, we can conclude that the two definitions for byzantine traces are
equivalent:
*)

Lemma byzantine_alt_byzantine_iff
    (tr : @Trace _ T)
    : alternate_byzantine_trace_prop tr <-> byzantine_trace_prop tr.
Proof.
    split; intros.
    - apply byzantine_alt_byzantine; assumption.
    - apply pre_loaded_alt_incl.
      apply byzantine_pre_loaded.
      assumption.
Qed.

End ByzantineTraces.

(**
** Composite validating byzantine traces are free

In this section we show that if all components of a composite VLSM <<X>> have
the [validating_projection_prop]erty, then its byzantine traces
are included into the free composition of the components of <<X>>.

*)
Section composite_validating_byzantine_traces.

    Context {message : Type}
            {index : Type}
            {IndEqDec : EqDec index}
            {IT : index -> VLSM_type message}
            (i0 : index)
            {IS : forall i : index, LSM_sig (IT i)}
            (IM : forall n : index, VLSM (IS n))
            (constraint : indexed_label IT -> indexed_state IT  * option message -> Prop)
            (X := indexed_vlsm_constrained i0 IM constraint)
            (PreLoadedX := pre_loaded_vlsm X)
            (FreeX := indexed_vlsm_free i0 IM)
            (Hvalidating: forall i : index, validating_projection_prop i0 IM constraint i)
            .

(**
Let us fix an indexed set of VLSMs <<IM>> and their composition <<X>> using <<constraint>>.
Let <<FreeX>> be the free composition of <<IM>>, and let <<PreloadedX>> be the
[pre_loaded_vlsm] associated to <<X>>.

Since we know that <<PreloadedX>> contains precisely
the byzantine traces of <<X>>, to prove our main result we just need to show
that <<PreLoadedX>> is included in <<FreeX>>.

First let us show that each [valid] <<PreloadedX>> message is a
[protocol_message] for <<FreeX>>.
*)
    
    Lemma pre_loaded_composite_free_protocol_message
        (l : label)
        (s : state)
        (om : option message)
        (Hv : @valid _ _ _ PreLoadedX l (s, om))
        : option_protocol_message_prop FreeX om.
    Proof.
        destruct l as (i, li).
        destruct Hv as [Hv Hconstraint].
        specialize (Hvalidating i li (s i, om) Hv).
        specialize (constraint_subsumption_protocol_prop i0 IM constraint free_constraint)
        ; intro Hprotocol.
        assert (Hsubsum : constraint_subsumption constraint free_constraint)
          by (intro; intros; exact I).
        specialize (Hprotocol Hsubsum).
        destruct Hvalidating as [sX [Hsi [Hps [[_s HpmX] H0]]]].
        apply Hprotocol in HpmX.
        exists _s. assumption.
    Qed.

(**
We can now apply the meta-lemma [basic_VLSM_incl], using
Lemma [pre_loaded_composite_free_protocol_message] above to prove that:
*)
    Lemma pre_loaded_composite_free_incl
        : VLSM_incl PreLoadedX FreeX
        .
    Proof.
        apply basic_VLSM_incl
        ; intros; try (assumption || reflexivity).
        - apply pre_loaded_composite_free_protocol_message with l s.
          destruct H as [_ [_ Hv]]. assumption.
        - intros. destruct H as [_ [_ [Hv Hc]]].
          split; try assumption.
          exact I.
    Qed.

(**
Finally,  we can conclude that [composite_validating_byzantine_traces_are_free]:
*)
(* begin show *)
    Lemma composite_validating_byzantine_traces_are_free
        (tr : @Trace _ (type X))
        (Hbyz : byzantine_trace_prop X tr)
        : protocol_trace_prop FreeX tr.
    Proof.
        apply pre_loaded_composite_free_incl.
        apply alt_pre_loaded_incl.
        apply byzantine_alt_byzantine_iff.
        assumption.
    Qed.
(* end show *)
End composite_validating_byzantine_traces.