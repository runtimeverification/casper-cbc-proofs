Require Import Nat Lia.
Require Import List Streams ProofIrrelevance.
Import ListNotations.

From CasperCBC
Require Import Lib.Preamble Lib.ListExtras Lib.StreamExtras.

(**
This module provides basic VLSM infrastructure
*)

(**

* VLSM definition

** The type of a VLSM

The type of a VLSM is a triple consisting of the undelying types of
messages, states, and labels.

In Coq it is defined as a Class taking <<message>> as parameter and having
[state] and [label] as fields.  <<message>> is a parameter to allow it to be
easily shared by multiple VLSMs during composition.

*)
  Class VLSM_type (message : Type) :=
    { state : Type
    ; label : Type
    }.

(**

** The signature of a VLSM

Although the VLSM definition does not single out the notion of a VLSM
signature, we find it convenient to extract it as the [VLSM_sign] class.

The [VLSM_sign] class is parameterized by a [VLSM_type] and defines properties
for initial states ([initial_state_prop]) and initial messages
([initial_message_prop]), from which we can immediately define the dependent
types [initial_state] (as [state]s having the [initial_state_prop]erty) and
[intial_message] (as <<message>>s having the [initial_message_prop]erty).

Additionally, [VLSM_sign] requires the identification of an [initial_state] [s0],
a <<message>> [m0], and a [label] [l0] to ensure the non-emptiness of the
corresponding sets.

*)

  Class VLSM_sign {message : Type} (vtype : VLSM_type message) :=
    { initial_state_prop : state -> Prop
    ; initial_state := { s : state | initial_state_prop s }
    ; initial_message_prop : message -> Prop
    ; initial_message := { m : message | initial_message_prop m }
    ; s0 : initial_state
    ; m0 : message
    ; l0 : label
    }.

(**

** VLSM class definition

Given a V[VLSM_sign]nature, a [VLSM] is defined by providing a [transition]
function and a [valid]ity condition.

*)

  Class VLSM {message : Type} {vtype : VLSM_type message} (lsm : VLSM_sign vtype) :=
    { transition : label -> state * option message -> state * option message
    ; valid : label -> state * option message -> Prop
    }.

(**

Given a [VLSM], it is convenient to be able to retrieve its V[VLSM_sign]nature
or [VLSM_type]. Functions [sign] and [type] below achieve this precise purpose.

*)

  Definition sign
    {message : Type}
    {vtype : VLSM_type message}
    {Sig : VLSM_sign vtype}
    (vlsm : VLSM Sig)
    := Sig.

  Definition type
    {message : Type}
    {vtype : VLSM_type message}
    {Sig : VLSM_sign vtype}
    (vlsm : VLSM Sig)
    := vtype.

  Section VLSM.

(**

In this section we assume a fixed [VLSM].
*)

    Context
      {message : Type}
      {vtype : VLSM_type message}
      {Sig : VLSM_sign vtype}
      (vlsm : VLSM Sig).



(**

** Protocol states and messages

We further characterize certain objects as being _protocol_, which means they can
be witnessed or experienced during executions of the protocol. For example,
a message is a [protocol_message] if there exists an execution of the protocol
in which it is produced.

We choose here to define protocol states and messages together as the
[protocol_prop] property, inductively defined over the
[state * option message] product type,
as this definition avoids the need of using a mutually recursive definition.

The inductive definition has three cases:
- if <<s>> is a [state] with the [initial_state_prop]erty, then <<(s, None)>> has the [protocol_prop]erty;
- if <<m>> is a <<message>> with the [initial_message_prop]erty, then <<(>>[s0, Some]<< m)>> has the [protocol_prop]erty;
- for all [state]s <<s>>, [option]al <<message>> <<om>>,
  and [label] <<l>>:

  if there is an (optional) <<message>> <<_om>> such that <<(s, _om)>> has the [protocol_prop]erty;

  and if there is a [state] <<_s>> such that <<(_s, om)>> has the [protocol_prop]erty;

  and if <<l>> [valid] <<(s, om)>>,

  then [transition] <<l (s, om)>> has the [protocol_prop]erty.
*)

    Inductive protocol_prop : state * option message -> Prop :=
    | protocol_initial_state
        (is : initial_state)
        (s : state := proj1_sig is)
      : protocol_prop (s, None)
    | protocol_initial_message
        (im : initial_message)
        (s : state := proj1_sig s0)
        (om : option message := Some (proj1_sig im))
      : protocol_prop (s, om)
    | protocol_generated
        (l : label)
        (s : state)
        (_om : option message)
        (Hps : protocol_prop (s, _om))
        (_s : state)
        (om : option message)
        (Hpm : protocol_prop (_s, om))
        (Hv : valid l (s, om))
      : protocol_prop (transition l (s, om)).

(**

The [protocol_state_prop]erty and the [protocol_message_prop]erty are now
definable as simple projections of the above definition.

Moreover, we use these derived properties to define the corresponding
dependent types [protocol_state] and [protocol_message].

*)

    Definition protocol_state_prop (s : state) :=
      exists om : option message, protocol_prop (s, om).

    Definition protocol_message_prop (m : message) :=
      exists s : state, protocol_prop (s, (Some m)).

    Definition protocol_state : Type :=
      { s : state | protocol_state_prop s }.

    Definition protocol_message : Type :=
      { m : message | protocol_message_prop m }.
      
   
    (* begin hide *)
    
    Lemma initial_is_protocol 
      (s : state)
      (Hinitial : initial_state_prop s) :
      protocol_state_prop s.
    Proof.
      unfold protocol_state_prop.
      unfold initial_state_prop.
      exists None.
      remember (exist _ s Hinitial) as is.
      assert (s = proj1_sig is). {
        rewrite Heqis.
        simpl.
        reflexivity.
      }
      rewrite H.
      apply protocol_initial_state.
    Qed.
      
    (* end hide *)

(**
As often times we work with optional protocol messages, it is convenient
to define a protocol message property for optional messages:
*)

    Definition option_protocol_message_prop (om : option message) :=
      exists s : state, protocol_prop (s, om).

    Lemma option_protocol_message_None
      : option_protocol_message_prop None.
    Proof.
      exists (proj1_sig s0). apply protocol_initial_state.
    Qed.

    Lemma option_protocol_message_Some
      (m : message)
      (Hpm : protocol_message_prop m)
      : option_protocol_message_prop (Some m).
    Proof.
      destruct Hpm as [s Hpm]. exists s. assumption.
    Qed.

(**

** Protocol validity and protocol transitions

To achieve this, it is useful to further define _protocol_ validity and
_protocol_ transitions:
*)

    Definition protocol_valid
               (l : label)
               (som : state * option message)
      : Prop
      :=
      let (s, om) := som in
         protocol_state_prop s
      /\ option_protocol_message_prop om
      /\ valid l (s,om).


    Definition protocol_transition
      (l : label)
      (som : state * option message)
      (som' : state * option message)
      :=
      protocol_valid l som
      /\  transition l som = som'.

(**
  Next three lemmas show the two definitions above are strongly related.
*)

    Lemma protocol_transition_valid
      (l : label)
      (som : state * option message)
      (som' : state * option message)
      (Ht : protocol_transition l som som')
      : protocol_valid l som.
    Proof.
      destruct Ht as [Hpv Ht].
      assumption.
    Qed.

    Lemma protocol_valid_transition
      (l : label)
      (som : state * option message)
      (Hv : protocol_valid l som)
      : exists (som' : state * option message),
        protocol_transition l som som'.
    Proof.
      exists (transition l som).
      repeat split; assumption.
    Qed.

    Lemma protocol_valid_transition_iff
      (l : label)
      (som : state * option message)
      : protocol_valid l som
      <-> exists (som' : state * option message),
            protocol_transition l som som'.
    Proof.
      split.
      - apply protocol_valid_transition.
      - intros [som' Hpt].
        apply protocol_transition_valid with som'.
        assumption.
    Qed.

(**

The next couple of lemmas relate the two definitions above with
pre-existing concepts.

*)
    Lemma protocol_generated_valid
      {l : label}
      {s : state}
      {_om : option message}
      {_s : state}
      {om : option message}
      (Hps : protocol_prop (s, _om))
      (Hpm : protocol_prop (_s, om))
      (Hv : valid l (s, om))
      : protocol_valid l (s, om).
    Proof.
      repeat split; try assumption.
      - exists _om. assumption.
      - exists _s. assumption.
    Qed.

    Lemma protocol_transition_origin
          {l : label}
          {s s' : state}
          {om om' : option message}
          (Ht : protocol_transition l (s, om) (s',om'))
      : protocol_state_prop s.
    Proof.
      destruct Ht as [[[_om Hp] _] _]. exists _om. assumption.
    Qed.

    Lemma protocol_transition_destination
          {l : label}
          {s s' : state}
          {om om' : option message}
          (Ht : protocol_transition l (s, om) (s', om'))
      : protocol_state_prop s'.
    Proof.
      exists om'.
      destruct Ht as [[[_om Hs] [[_s Hom] Hv]] Ht].
      rewrite <- Ht. apply protocol_generated with _om _s; assumption.
    Qed.

    Lemma protocol_transition_in
          {l : label}
          {s s' : state}
          {m : message}
          {om' : option message}
          (Ht : protocol_transition l (s, (Some m)) (s', om'))
      : protocol_message_prop m.
    Proof.
      destruct Ht as [[_ [[_s Hom] _]] _].
      exists _s. assumption.
    Qed.

    Lemma protocol_prop_transition_in
          {l : label}
          {s s' : state}
          {om om' : option message}
          (Ht : protocol_transition l (s, om) (s', om'))
      : exists _s, protocol_prop (_s, om).
    Proof.
      destruct om as [m|].
      - apply protocol_transition_in in Ht.
        inversion Ht. exists x. assumption.
      - exists (proj1_sig s0). constructor.
    Qed.

    Lemma protocol_prop_transition_out
          {l : label}
          {s s' : state}
          {om om' : option message}
          (Ht : protocol_transition l (s, om) (s', om'))
        : protocol_prop (s', om').
    Proof.
      destruct Ht as [[[_om Hps] [[_s Hpm] Hv]] Ht].
      rewrite <- Ht.
      apply protocol_generated with _om _s; assumption.
    Qed.

    Lemma protocol_transition_is_valid
          {l : label}
          {s s' : state}
          {om om' : option message}
          (Ht : protocol_transition l (s, om) (s', om'))
      : valid l (s, om).
    Proof.
      destruct Ht as [[_ [_ Hv]] _].
      assumption.
    Qed.

    Lemma protocol_transition_transition
          {l : label}
          {s s' : state}
          {om om' : option message}
          (Ht : protocol_transition l (s, om) (s', om'))
        :  transition l (s, om) = (s', om').
     Proof.
      destruct Ht as [_ Ht]. assumption.
     Qed.

    Lemma protocol_prop_valid_out
      (l : label)
      (s : state)
      (om : option message)
      (Hv : protocol_valid l (s, om))
      : protocol_prop (transition l (s, om)).
    Proof.
      apply protocol_valid_transition in Hv.
      destruct Hv as [[s' om'] Ht].
      specialize (protocol_transition_transition  Ht); intro Hteq.
      rewrite Hteq.
      apply (protocol_prop_transition_out Ht).
    Qed.

    (** For VLSMs initialized with many initial messages such as
    the [composite_vlsm_constrained_projection] or the [pre_loaded_vlsm],
    the question of whether a [VLSM] [can_emit] a message <<m>> becomes more
    useful than that whether <<m>> is a [protocol_message].
    *)

    Definition can_emit
      (m : message)
      :=
      exists
      (som : state * option message)
      (l : label)
      (s : state),
      protocol_transition l som (s, Some m).

    (** Of course, if a VLSM [can_emit] a message <<m>>, then <<m>> is
    a protocol message.
    *)

    Lemma can_emit_protocol
      (m : message)
      (Hm : can_emit m)
      : protocol_message_prop m .
    Proof.
      destruct Hm as [(s0, om0) [l [s [[[_om0 Hs0] [[_s0 Hom0] Hv]] Ht]]]].
      exists s.
      rewrite <- Ht.
      apply protocol_generated with _om0 _s0; assumption.
    Qed.

    (** A characterization of protocol messages in terms of [can_emit]
    *)

    Lemma can_emit_protocol_iff
      (m : message)
      : protocol_message_prop m <-> initial_message_prop m \/ can_emit m.
    Proof.
      split.
      - intros [s Hm]; inversion Hm; subst.
        + destruct im as [m Him]. simpl. left. assumption.
        + right.
          exists (s1, om). exists l. exists s.
          repeat split; try assumption.
          * exists _om. assumption.
          * exists _s. assumption.
      - intros [Him | Hem].
        + replace m with (proj1_sig (exist _ m Him))
            by reflexivity.
          exists (proj1_sig s0).
          apply protocol_initial_message.
        + apply can_emit_protocol. assumption.
    Qed.

(**

** Protocol state and protocol message characterization

The definition and results below show that the mutually-recursive definitions
for [protocol_state]s and [protocol_message]s can be derived from the
prior definitions.

The results below offers equivalent characterizations for [protocol_state]s
and [protocol_message]s, similar to their recursive definition.
*)

    Lemma protocol_state_prop_iff :
      forall s' : state,
        protocol_state_prop s'
        <-> (exists is : initial_state, s' = proj1_sig is)
          \/ exists (l : label) (som : state * option message) (om' : option message),
            protocol_transition l som (s', om').
    Proof.
      intros; split.
      - intro Hps'. destruct Hps' as [om' Hs].
        inversion Hs; subst
        ; try (left; exists is; reflexivity)
        ; try (left; exists s0; reflexivity).
        right. exists l. exists (s, om). exists om'.
        repeat split; try assumption.
        + exists _om. assumption.
        + exists _s. assumption.
      - intros [[[s His] Heq] | [l [[s om] [om' [[[_om Hps] [[_s Hpm] Hv]] Ht]]]]]; subst.
        + exists None. apply protocol_initial_state.
        + exists om'. rewrite <- Ht. apply protocol_generated with _om _s; assumption.
    Qed.

    (* Protocol message characterization - similar to the definition in the report. *)

    Lemma protocol_message_prop_iff :
      forall m' : message,
        protocol_message_prop m'
        <-> (exists im : initial_message, m' = proj1_sig im)
          \/ exists (l : label) (som : state * option message) (s' : state),
            protocol_transition l som (s', Some m').
    Proof.
      intros; split.
      - intros [s' Hpm'].
        inversion Hpm'; subst
        ; try (left; exists im; reflexivity).
        right. exists l. exists (s, om). exists s'.
        repeat split; try assumption.
        + exists _om. assumption.
        + exists _s. assumption.
      - intros [[[s His] Heq] | [l [[s om] [s' [[[_om Hps] [[_s Hpm] Hv]] Ht]]]]]; subst.
        + exists (proj1_sig s0). apply protocol_initial_message.
        + exists s'. rewrite <- Ht.
          apply protocol_generated with _om _s; assumption.
    Qed.

(**
* Traces

We introduce the concept of a trace to formalize an execution of the protocol.
It is abstracted as a pair <<(start, steps)>> where <<start>> is a state
and <<steps>> is a tuple of objects which fully describe the transitions
underwent during execution. Notably, <<steps>> might be infinite.

In Coq, we can define these objects (which we name [transition_item]s) as consisting of:
- the [label] [l]
- the (optional) [input] <<message>>
- the [destination] [state] of the transition
- the (optional) [output] <<message>> generated by the transition

*)
    Record transition_item :=
      {   l : label
          ;   input : option message
          ;   destination : state
          ;   output : option message
      }.

(**
Note that it is unnecessary to specify the source state of the transition,
as it is implied by the preceding [transition_item] (or by the <<start>> state,
if such an item doesn't exist).
*)

(**
We will now split our groundwork for defining traces into the finite case and
the infinite case.
*)

(**

** Finite [protocol_trace]s

A [finite_protocol_trace_from] a [state] <<start>> is a pair <<(start, steps)>> where <<steps>>
is a list of [transition_item]s, and is inductively defined by:
- <<(s, [])>> is a [finite_protocol_trace_from] <<s>>
- if there is a [protocol_transition] <<l (s', iom) (s, oom)>>

  and if <<(s,steps)>> is a [protocol_trace_from] <<s>>

  then <<(s', ({| l := l; input := iom; destination := s; output := oom |} :: steps)>>
  is a [protocol_transition_from] <<s'>>.

Note that the definition is given such that it extends an existing trace by
adding a transition to its front.
The reason for this choice is to have this definition be similar to the one
for infinite traces, which can only be extended at the front.
*)

    Inductive finite_protocol_trace_from : state -> list transition_item -> Prop :=
    | finite_ptrace_empty : forall (s : state), protocol_state_prop s -> finite_protocol_trace_from s []
    | finite_ptrace_extend : forall  (s : state) (tl : list transition_item),
        finite_protocol_trace_from s tl ->
        forall (s' : state) (iom oom : option message) (l : label),
          protocol_transition l (s', iom) (s, oom) ->
          finite_protocol_trace_from  s' ({| l := l; input := iom; destination := s; output := oom |} :: tl).

(**
To complete our definition of a finite protocol trace, we must also guarantee that <<start>> is an
initial state according to the protocol.
*)

    Definition finite_protocol_trace (s : state) (ls : list transition_item) : Prop :=
      finite_protocol_trace_from s ls /\ initial_state_prop s.

(**
In the remainder of the section we provide various results allowing us to
decompose the above properties in proofs.
*)

    Lemma finite_ptrace_first_valid_transition
          (s : state)
          (tr : list transition_item)
          (te : transition_item)
          (Htr : finite_protocol_trace_from s (te :: tr))
      : protocol_transition (l te) (s, input te) (destination te, output te).
    Proof.
      inversion Htr. assumption.
    Qed.

    Lemma finite_ptrace_first_pstate
      (s : state)
      (tr : list transition_item)
      (Htr : finite_protocol_trace_from s tr)
      : protocol_state_prop s.
    Proof.
      inversion Htr; subst; try assumption.
      destruct H0 as [[Hs _] _]. assumption.
    Qed.

    Lemma finite_ptrace_tail
          (s : state)
          (tr : list transition_item)
          (te : transition_item)
          (Htr : finite_protocol_trace_from s (te :: tr))
      : finite_protocol_trace_from (destination te) tr.
    Proof.
      inversion Htr. assumption.
    Qed.

    Lemma finite_ptrace_consecutive_valid_transition
          (s : state)
          (tr tr2 : list transition_item)
          (tr1 : list transition_item)
          (te1 te2 : transition_item)
          (Htr : finite_protocol_trace_from s tr)
          (Heq : tr = tr1 ++ [te1; te2] ++ tr2)
      : protocol_transition (l te2) (destination te1, input te2) (destination te2, output te2).
    Proof.
      generalize dependent s. generalize dependent tr.
      induction tr1.
      - intros tr Heq s Htr. simpl in Heq; subst. inversion Htr; subst. inversion H2; subst. assumption.
      - specialize (IHtr1 (tr1 ++ [te1; te2] ++ tr2) eq_refl).
        intros tr Heq is Htr; subst. inversion Htr; subst.
        simpl in IHtr1. specialize (IHtr1 s H2). assumption.
    Qed.
    
    Lemma first_transition_valid
      (s : state)
      (te : transition_item)
      (Htr : finite_protocol_trace_from s [te])
      : protocol_transition (l te) (s, input te) (destination te, output te).
      
    Proof.
      inversion Htr.
      simpl.
      assumption.
    Qed.
    
    Lemma protocol_transition_to
      (si : state)
      (middle : transition_item)
      (tr prefix suffix : list transition_item)
      (Hsplit : tr = prefix ++ [middle] ++ suffix)
      (Htr : finite_protocol_trace_from si tr)
      (prev_state := last (List.map destination prefix) si)
      :
      protocol_transition (l middle) (prev_state, input middle) (destination middle, output middle).
    Proof.
    Admitted.

    Lemma extend_right_finite_trace_from
      : forall s1 ts s3 iom3 oom3 l3 (s2 := List.last (List.map destination ts) s1),
        finite_protocol_trace_from s1 ts ->
        protocol_transition l3 (s2, iom3) (s3, oom3) ->
        finite_protocol_trace_from s1 (ts ++ [{| l := l3; destination := s3; input := iom3; output := oom3 |}]).
    Proof.
      intros s1 ts s3 iom3 oom3 l3 s2 Ht12 Hv23.
      induction Ht12.
      - simpl. apply finite_ptrace_extend; try assumption.
        constructor. apply (protocol_transition_destination Hv23).
      - rewrite <- app_comm_cons.
        apply finite_ptrace_extend; try assumption.
        simpl in IHHt12. apply IHHt12.
        unfold s2 in *; clear s2.
        replace
          (last (List.map destination tl) s)
          with
            (last (List.map destination ({| l := l1; input := iom; destination := s; output := oom |} :: tl)) s')
        ; try assumption.
        rewrite map_cons.
        destruct tl; try reflexivity.
        rewrite map_cons.
        eapply remove_hd_last.
    Qed.


(**
We can now prove several general properties of [finite_protocol_trace]s. For example,
the following lemma states that given two such traces, such that the latter's starting state
is equal to the former's last state, it is possible to _concatenate_ them into a single
[finite_protocol_trace].
*)

    Lemma finite_protocol_trace_from_app_iff (s : state) (ls ls' : list transition_item) (s' := (last (List.map destination ls) s))
      : finite_protocol_trace_from s ls /\ finite_protocol_trace_from s' ls'
        <->
        finite_protocol_trace_from s (ls ++ ls').
    Proof.
      intros. generalize dependent ls'. generalize dependent s.
      induction ls; intros; split.
      - intros [_ H]. assumption.
      - simpl; intros; split; try assumption. constructor. inversion H; try assumption.
        apply (protocol_transition_origin H1).
      - simpl. intros [Htr Htr'].
        destruct a. apply finite_ptrace_extend.
        + apply IHls. inversion Htr. split. apply H2.
          unfold s' in Htr'.
          assert (last_identity: last (List.map destination ls) destination0 = last
          (List.map destination
             ({| l := l1; input := input0; destination := destination0; output := output0 |} :: ls)) s). {
          rewrite map_cons. rewrite unroll_last. simpl. reflexivity. }
          rewrite last_identity. assumption.
        + inversion Htr. apply H6.
       - intros. inversion H. subst. specialize (IHls s1). simpl in IHls. specialize (IHls ls'). apply IHls in H3.
         destruct H3. split.
         + constructor. apply H0. apply H4.
         + assert (last_identity : s' = last (List.map destination ls) s1). {
           unfold s'. rewrite map_cons. rewrite unroll_last. reflexivity.
         }
         rewrite last_identity. assumption.
    Qed.

(** Several other lemmas in this vein are necessary for proving results regarding
traces.
*)

    Lemma finite_protocol_trace_from_prefix
      (s : state)
      (ls : list transition_item)
      (Htr : finite_protocol_trace_from s ls)
      (n : nat)
      : finite_protocol_trace_from s (list_prefix ls n).
    Proof.
      specialize (list_prefix_suffix ls n); intro Hdecompose.
      rewrite <- Hdecompose in Htr.
      apply finite_protocol_trace_from_app_iff in Htr.
      destruct Htr as [Hpr _].
      assumption.
    Qed.

    Lemma finite_protocol_trace_from_suffix
      (s : state)
      (ls : list transition_item)
      (Htr : finite_protocol_trace_from s ls)
      (n : nat)
      (nth : state)
      (Hnth : nth_error (s :: List.map destination ls) n = Some nth)
      : finite_protocol_trace_from nth (list_suffix ls n).
    Proof.
      specialize (list_prefix_suffix ls n); intro Hdecompose.
      rewrite <- Hdecompose in Htr.
      apply finite_protocol_trace_from_app_iff in Htr.
      destruct Htr as [_ Htr].
      assert (Heq : last (List.map destination (list_prefix ls n)) s = nth).
      { rewrite list_prefix_map.
        destruct n.
        - simpl in Hnth. inversion Hnth; subst; clear Hnth.
          remember (List.map destination ls) as l.
          destruct l; reflexivity.
        - symmetry. apply list_prefix_nth_last.
          simpl in Hnth. assumption.
      }
      rewrite Heq in Htr.
      assumption.
    Qed.

    Lemma finite_protocol_trace_from_segment
      (s : state)
      (ls : list transition_item)
      (Htr : finite_protocol_trace_from s ls)
      (n1 n2 : nat)
      (Hle : n1 <= n2)
      (n1th : state)
      (Hnth : nth_error (s :: List.map destination ls) n1 = Some n1th)
      : finite_protocol_trace_from n1th (list_segment ls n1 n2).
    Proof.
      apply finite_protocol_trace_from_suffix with s.
      - apply finite_protocol_trace_from_prefix. assumption.
      - destruct n1; try assumption.
        simpl. simpl in Hnth.
        rewrite list_prefix_map.
        rewrite list_prefix_nth; assumption.
    Qed.
    
        
    (* begin hide *)
    Lemma can_emit_from_protocol_trace
      (si : state)
      (m : message)
      (tr : list transition_item)
      (Hprotocol: finite_protocol_trace si tr)
      (Hm : List.Exists (fun elem : transition_item => output elem = Some m) tr) :
      can_emit m.
    
    Proof.
    Admitted.
    (* end hide *)

(**
** Infinite [protcol_trace]s
*)

(** We now define [infinite_protocol_trace]s. The definitions
resemble their finite counterparts, adapted to the technical
necessities of defining infinite objects. Notably, <<steps>> is
stored as a stream, as opposed to a list.
*)

    CoInductive infinite_protocol_trace_from :
      state -> Stream transition_item -> Prop :=
    | infinite_ptrace_extend : forall  (s : state) (tl : Stream transition_item),
        infinite_protocol_trace_from s tl ->
        forall (s' : state) (iom oom : option message) (l : label),
          protocol_transition l (s', iom) (s, oom) ->
          infinite_protocol_trace_from  s' (Cons {| l := l; input := iom; destination := s; output := oom |}  tl).

    Definition infinite_ptrace (s : state) (st : Stream transition_item)
      := infinite_protocol_trace_from s st /\ initial_state_prop s.

(**
As for the finite case, the following lemmas help decompose teh above
definitions, mostly reducing them to properties about their finite segments.
*)
    Lemma infinite_ptrace_consecutive_valid_transition
          (is : state)
          (tr tr2 : Stream transition_item)
          (tr1 : list transition_item)
          (te1 te2 : transition_item)
          (Htr : infinite_protocol_trace_from is tr)
          (Heq : tr = stream_app (tr1 ++ [te1; te2]) tr2)
      : protocol_transition (l te2) (destination te1, input te2) (destination te2, output te2).
    Proof.
      generalize dependent is. generalize dependent tr.
      induction tr1.
      - intros tr Heq is Htr. simpl in Heq; subst. inversion Htr; subst. inversion H2; subst. assumption.
      - specialize (IHtr1 (stream_app (tr1 ++ [te1; te2]) tr2) eq_refl).
        intros tr Heq is Htr; subst. inversion Htr; subst.
        specialize (IHtr1 s H2). assumption.
    Qed.

    Lemma infinite_protocol_trace_from_app_iff
      (s : state)
      (ls : list transition_item)
      (ls' : Stream transition_item)
      (s' := (last (List.map destination ls) s))
      : finite_protocol_trace_from s ls /\ infinite_protocol_trace_from s' ls'
        <->
        infinite_protocol_trace_from s (stream_app ls ls').
    Proof.
      intros. generalize dependent ls'. generalize dependent s.
      induction ls; intros; split.
      - intros [_ H]. assumption.
      - simpl; intros; split; try assumption. constructor. inversion H; try assumption.
        apply (protocol_transition_origin H1).
      - simpl. intros [Htr Htr'].
        destruct a. apply infinite_ptrace_extend.
        + apply IHls. inversion Htr. split. apply H2.
          unfold s' in Htr'.
          assert (last_identity: last (List.map destination ls) destination0 = last
          (List.map destination
             ({| l := l1; input := input0; destination := destination0; output := output0 |} :: ls)) s). {
          rewrite map_cons. rewrite unroll_last. simpl. reflexivity. }
          rewrite last_identity. assumption.
        + inversion Htr. apply H6.
       - intros. inversion H. subst. specialize (IHls s1). simpl in IHls. specialize (IHls ls'). apply IHls in H3.
         destruct H3. split.
         + constructor. apply H0. apply H4.
         + assert (last_identity : s' = last (List.map destination ls) s1). {
           unfold s'. rewrite map_cons. rewrite unroll_last. reflexivity.
         }
         rewrite last_identity. assumption.
    Qed.

    Lemma infinite_protocol_trace_from_prefix
      (s : state)
      (ls : Stream transition_item)
      (Htr : infinite_protocol_trace_from s ls)
      (n : nat)
      : finite_protocol_trace_from s (stream_prefix ls n).
    Proof.
      specialize (stream_prefix_suffix ls n); intro Hdecompose.
      rewrite <- Hdecompose in Htr.
      apply infinite_protocol_trace_from_app_iff in Htr.
      destruct Htr as [Hpr _].
      assumption.
    Qed.

    Lemma infinite_protocol_trace_from_prefix_rev
      (s : state)
      (ls : Stream transition_item)
      (Hpref: forall n : nat, finite_protocol_trace_from s (stream_prefix ls n))
      : infinite_protocol_trace_from s ls.
    Proof.
      generalize dependent Hpref. generalize dependent s. generalize dependent ls.
      cofix H.
      intros (a, ls) s Hpref.
      assert (Hpref0 := Hpref 1).
      inversion Hpref0; subst.
      constructor; try assumption.
      apply H.
      intro n.
      specialize (Hpref (S n)).
      simpl in Hpref.
      inversion Hpref; subst.
      assumption.
    Qed.

    Lemma infinite_protocol_trace_from_segment
      (s : state)
      (ls : Stream transition_item)
      (Htr : infinite_protocol_trace_from s ls)
      (n1 n2 : nat)
      (Hle : n1 <= n2)
      (n1th := Str_nth n1 (Cons s (Streams.map destination ls)))
      : finite_protocol_trace_from n1th (stream_segment ls n1 n2).
    Proof.
      apply finite_protocol_trace_from_suffix with s.
      - apply infinite_protocol_trace_from_prefix. assumption.
      - destruct n1; try reflexivity.
        unfold n1th. clear n1th.
        simpl.
        rewrite stream_prefix_map.
        rewrite stream_prefix_nth; try assumption.
        reflexivity.
    Qed.

(**

** Protocol traces

Finally, we define [Trace] as a sum-type of its finite/infinite variants.
It inherits some previously introduced definitions, culminating with the
[protocol_trace].
*)

    Inductive Trace : Type :=
    | Finite : state -> list transition_item -> Trace
    | Infinite : state -> Stream transition_item -> Trace.

    Definition trace_first (tr : Trace) : state :=
      match tr with
      | Finite s _ => s
      | Infinite s _ => s
      end.

    Definition trace_last (tr : Trace) : option state
      :=
        match tr with
        | Finite s ls => Some (last (List.map destination ls) s)
        | Infinite _ _ => None
        end.

    Definition ptrace_from_prop (tr : Trace) : Prop :=
      match tr with
      | Finite s ls => finite_protocol_trace_from s ls
      | Infinite s sm => infinite_protocol_trace_from s sm
      end.

    Definition protocol_trace_prop (tr : Trace) : Prop :=
      match tr with
      | Finite s ls => finite_protocol_trace s ls
      | Infinite s sm => infinite_ptrace s sm
      end.

    Definition protocol_trace : Type :=
      { tr : Trace | protocol_trace_prop tr}.

    Lemma protocol_trace_from
      (tr : Trace)
      (Htr : protocol_trace_prop tr)
      : ptrace_from_prop tr.
    Proof.
      destruct tr; simpl; destruct Htr as [Htr Hinit]; assumption.
    Qed.

    Lemma protocol_trace_initial
      (tr : Trace)
      (Htr : protocol_trace_prop tr)
      : initial_state_prop (trace_first tr).
    Proof.
      destruct tr; simpl; destruct Htr as [Htr Hinit]; assumption.
    Qed.

    Lemma protocol_trace_from_iff
      (tr : Trace)
      : protocol_trace_prop tr
      <-> ptrace_from_prop tr /\ initial_state_prop (trace_first tr).
    Proof.
      split.
      - intro Htr; split.
        + apply protocol_trace_from; assumption.
        + apply protocol_trace_initial; assumption.
      - destruct tr; simpl; intros [Htr Hinit]; split; assumption.
    Qed.

    (* begin hide *)
    (* Protocol runs *)
    Record proto_run : Type := mk_proto_run
                                 { start : initial_state
                                   ; transitions : list transition_item
                                   ; final : state * option message
                                 }.

    Inductive vlsm_run_prop : proto_run -> Prop :=
    | empty_run_initial_state
        (is : initial_state)
        (s : state := proj1_sig is)
      : vlsm_run_prop {| start := is; transitions := []; final := (s, None) |}
    | empty_run_initial_message
        (im : initial_message)
        (s : state := proj1_sig s0)
        (om : option message := Some (proj1_sig im))
      : vlsm_run_prop {| start := s0; transitions := []; final := (s, om) |}
    | extend_run
        (state_run : proto_run)
        (Hs : vlsm_run_prop state_run)
        (s := fst (final state_run))
        (is := start state_run)
        (ts := transitions state_run)
        (msg_run : proto_run)
        (Hm : vlsm_run_prop msg_run)
        (om := snd (final msg_run))
        (l : label)
        (Hv : valid l (s, om))
        (som' := transition l (s, om))
      : vlsm_run_prop {| start := is; transitions := ts ++ [
          {|   l := l
          ;   input := om
          ;   destination := fst som'
          ;   output := snd som'
          |}]; final := som' |}.

    Definition vlsm_run : Type :=
      { r : proto_run | vlsm_run_prop r }.


    Lemma vlsm_run_last_state
      (vr : vlsm_run)
      (r := proj1_sig vr)
      : last (List.map destination (transitions r)) (proj1_sig (start r)) = fst (final r).
    Proof.
      unfold r; clear r; destruct vr as [r Hr]; simpl.
      induction Hr; simpl; try reflexivity.
      rewrite map_app; simpl.
      apply last_is_last.
    Qed.

    Lemma vlsm_run_last_final
      (vr : vlsm_run)
      (r := proj1_sig vr)
      (tr := transitions r)
      (Hne_tr : tr <> [])
      (lst := last_error tr)
      : option_map destination lst = Some (fst (final r))
      /\ option_map output lst = Some (snd (final r)).
    Proof.
      unfold r in *; clear r; destruct vr as [r Hr]; inversion Hr; subst; simpl in *; clear Hr
      ; try contradiction.
      unfold tr in *. unfold lst in *. rewrite last_error_is_last . simpl.
      split; reflexivity.
    Qed.

    Lemma run_is_protocol
          (vr : vlsm_run)
      : protocol_prop (final (proj1_sig vr)).
    Proof.
      destruct vr as [r Hr]; simpl.
      induction Hr; simpl in *; try constructor.
      unfold om in *; clear om. unfold s in *; clear s.
      destruct (final state_run) as [s _om].
      destruct (final msg_run) as [_s om].
      specialize (protocol_generated l1 s _om IHHr1 _s om IHHr2 Hv). intro. assumption.
    Qed.

    Lemma protocol_is_run
          (som' : state * option message)
          (Hp : protocol_prop som')
      : exists vr : vlsm_run, (som' = final (proj1_sig vr)).
    Proof.
      induction Hp.
      - exists (exist _ _ (empty_run_initial_state is)); reflexivity.
      - exists (exist _ _ (empty_run_initial_message im)); reflexivity.
      - destruct IHHp1 as [[state_run Hsr] Heqs]. destruct IHHp2 as [[msg_run Hmr] Heqm].
        specialize (extend_run state_run Hsr). simpl. intros Hvr.
        specialize (Hvr msg_run Hmr l1). simpl in Heqs. simpl in Heqm.
        rewrite <- Heqs in Hvr. rewrite <- Heqm in Hvr. specialize (Hvr Hv).
        exists (exist _ _ Hvr). reflexivity.
    Qed.

    Lemma run_is_trace
          (vr : vlsm_run)
          (r := proj1_sig vr)
      : protocol_trace_prop (Finite (proj1_sig (start r)) (transitions r)).
    Proof.
      unfold r; clear r; destruct vr as [r Hr]; simpl.
      induction Hr; simpl.
      - specialize (protocol_initial_state is); intro Hpis; simpl in Hpis.
        destruct is as [is His]; simpl. constructor; try assumption. constructor.
        exists None. assumption.
      - specialize (protocol_initial_state s0); intro Hps0; simpl in Hps0.
        destruct s0 as [s0 Hs0]; simpl. constructor; try assumption. constructor.
        exists None. assumption.
      - destruct IHHr1 as [Htr Hinit].
        split; try assumption.
        apply extend_right_finite_trace_from; try assumption.
        specialize vlsm_run_last_state; intros Hls. specialize (Hls (exist _ state_run Hr1)).
        simpl in Hls. unfold ts. unfold is. rewrite Hls.
        repeat split; try assumption.
        + exists (snd (final state_run)). rewrite <- surjective_pairing.
          specialize (run_is_protocol (exist _ state_run Hr1)); intro Hp; assumption.
        + exists (fst (final msg_run)). rewrite <- surjective_pairing.
          specialize (run_is_protocol (exist _ msg_run Hr2)); simpl; intro Hp; assumption.
        + rewrite <- surjective_pairing. reflexivity.
    Qed.

    Lemma trace_is_run
      (is : initial_state)
      (tr : list transition_item)
      (Htr : finite_protocol_trace_from (proj1_sig is) tr)
      : exists r : proto_run,
        vlsm_run_prop r /\
        start r = is /\ transitions r = tr.
    Proof.
      generalize dependent tr.
      apply (rev_ind (fun tr => (finite_protocol_trace_from (proj1_sig is) tr ->
                exists r : proto_run, vlsm_run_prop r /\ start r = is /\ transitions r = tr))).
      - intros H.
        exists {| start := is; transitions := []; final := (proj1_sig is, None) |}; simpl; repeat split; try reflexivity.
        apply empty_run_initial_state.
      - intros lst prefix IHprefix H.
        apply finite_protocol_trace_from_app_iff in H.
        destruct H as [Hprefix Hlst].
        specialize (IHprefix Hprefix).
        destruct IHprefix as [r0 [Hr0 [Hstart Htr_r0]]].
        exists {| start := is; transitions := prefix ++ [lst]; final := (destination lst, output lst) |}.
        simpl. repeat split; try reflexivity.
        specialize (extend_run r0 Hr0); simpl; intro Hextend.
        apply finite_ptrace_first_valid_transition in Hlst.
        destruct lst as [lst_l lst_in lst_dest lst_out].
        simpl in *.
        specialize (vlsm_run_last_state (exist _ r0 Hr0)); intro Hlast_state.
        simpl in Hlast_state. rewrite Htr_r0 in Hlast_state.
        rewrite Hstart in Hlast_state. rewrite Hlast_state in Hlst.
        specialize (protocol_prop_transition_in Hlst); intro Hmsg.
        destruct Hmsg as [_s Hmsg].
        apply protocol_is_run in Hmsg.
        destruct Hmsg as [[r_msg Hr_msg] Hmsg].
        specialize (Hextend r_msg Hr_msg lst_l).
        specialize (protocol_transition_is_valid Hlst); intro Hvalid.
        simpl in Hmsg. rewrite <- Hmsg in Hextend. simpl  in Hextend.
        specialize (Hextend Hvalid). rewrite Hstart in Hextend.
        specialize (protocol_transition_transition Hlst); intro Htransition.
        rewrite Htransition in Hextend. simpl in Hextend.
        rewrite Htr_r0 in Hextend.
        apply Hextend.
        Qed.

    Lemma trace_is_protocol
      (is : initial_state)
      (tr : list transition_item)
      (Htr : finite_protocol_trace_from (proj1_sig is) tr)
      : protocol_state_prop (last (List.map destination tr) (proj1_sig is)).
    Proof.
      specialize (trace_is_run is tr Htr); simpl; intro Hrun.
      destruct Hrun as [run [Hrun [Hstart Htrans]]].
      specialize (run_is_protocol (exist _ run Hrun)); simpl; intro Hps.
      specialize (vlsm_run_last_state (exist _ run Hrun)); simpl; intros Hlast'.
      rewrite Htrans in Hlast'. rewrite Hstart in Hlast'.
      destruct (final run) as (s', om). simpl in Hlast'.
      exists om.
      subst.
      assumption.
    Qed.
    
    Lemma trace_states_are_protocol
      (s : state)
      (is : initial_state)
      (tr : list transition_item)
      (Hin : In s (List.map destination tr))
      : protocol_state_prop s.
      
      Proof.
        pose proof in_split as in_split.
        apply in_split in Hin.
        destruct Hin as [l1 [l2 Hconcat]].
        admit.
      Admitted.

        (* end hide *)

(** Having defined [protocol_trace]s, we now connect them to protocol states
and messages, in the following sense: for each state-message pair (<<s>>, <<m>>)
that has the [protocol_prop]erty, there exists a [protocol_trace] which ends
in <<s>> by outputting <<m>> *)

    Lemma protocol_is_trace
          (s : state)
          (om : option message)
          (Hp : protocol_prop (s, om))

      : initial_state_prop s
      \/ exists (is : state) (tr : list transition_item),
            finite_protocol_trace is tr
            /\ option_map destination (last_error tr) = Some s
            /\ option_map output (last_error tr) = Some om.
    Proof.
      specialize (protocol_is_run (s,om) Hp); intros [vr Heq].
      specialize (run_is_trace vr); simpl; intros Htr.
      destruct vr as [r Hvr]; simpl in *.
      destruct (transitions r) eqn:Htrace.
      - inversion Hvr; subst; simpl in Htrace; simpl in Heq; inversion Heq; subst.
        + destruct is as [s0 His]. left. assumption.
        + destruct s0 as [s0 His]. left. assumption.
        + destruct ts; inversion Htrace.
      - right. exists (proj1_sig (start r)). exists (transitions r). rewrite Htrace.
        split; try assumption.
        specialize (vlsm_run_last_final (exist _ r Hvr)); simpl; rewrite Htrace; simpl.
        rewrite <- Heq.
        intros Hlf; apply Hlf. intros HC; inversion HC.
    Qed.

(**
Next function extract the nth state of a trace, where the sequence of
states of a trace is obtained by appending the all destination
states in the transition list/stream to the initial state of the trace.
*)
    Definition trace_nth (tr : Trace)
      : nat -> option state :=
      fun (n : nat) =>
        match tr with
        | Finite s ls => nth_error (s::List.map destination ls) n
        | Infinite s st => Some (Str_nth n (Cons s (Streams.map destination st)))
        end.

(** Another benefit of defining traces is that we can succintly
describe indirect transitions between arbitrary pairs of states.

We say that state <<second>> is in state <<first>>'s futures if
there exists a finite (possibly empty) protocol trace that begins
with <<first>> and ends in <<second>>.

This relation is often used in stating safety and liveness properties.*)

    Definition in_futures
      (first second : state)
      : Prop :=
      exists (tr : list transition_item),
        finite_protocol_trace_from first tr /\
        last (List.map destination tr) first = second.

    Lemma in_futures_protocol_fst
      (first second : state)
      (Hfuture: in_futures first second)
      : protocol_state_prop first.
    Proof.
      destruct Hfuture as [tr [Htr Hlast]].
      apply finite_ptrace_first_pstate in Htr.
      assumption.
    Qed.

    (* begin hide *)

    Lemma in_futures_refl
      (first: state)
      (Hps : protocol_state_prop first)
      : in_futures first first.

    Proof.
    exists [].
    split.
    - apply finite_ptrace_empty.
      assumption.
    - reflexivity.
    Qed.

    Lemma in_futures_trans
      (first second third : state)
      (H12: in_futures first second)
      (H23 : in_futures second third)
      : in_futures first third.
    Proof.
      destruct H12 as [tr12 [Htr12 Hsnd]].
      destruct H23 as [tr23 [Htr23 Hthird]].
      subst second.
      specialize (finite_protocol_trace_from_app_iff first tr12 tr23); simpl; intros [Happ _].
      specialize (Happ (conj Htr12 Htr23)).
      exists (tr12 ++ tr23).
      split; try assumption.
      rewrite map_app.
      rewrite last_app.
      assumption.
    Qed.

    Lemma in_futures_witness
      (first second : state)
      (Hfutures : in_futures first second)
      : exists (tr : protocol_trace) (n1 n2 : nat),
        n1 <= n2
        /\ trace_nth (proj1_sig tr) n1 = Some first
        /\ trace_nth (proj1_sig tr) n2 = Some second.
    Proof.
      specialize (in_futures_protocol_fst first second Hfutures); intro Hps.
      destruct Hps as [_mfirst Hfirst].
      simpl.
      unfold in_futures in Hfutures. simpl in Hfutures.
      destruct Hfutures as [suffix_tr [Hsuffix_tr Hsnd]].
      apply protocol_is_run in Hfirst.
      destruct Hfirst as [prefix_run Hprefix_run].
      specialize (vlsm_run_last_state prefix_run); intro Hprefix_last.
      specialize (run_is_trace prefix_run); intro Hprefix_tr.
      destruct prefix_run as [prefix_run Hpref_run].
      destruct prefix_run as [prefix_start prefix_tr prefix_final].
      subst; simpl in *.
      specialize (finite_protocol_trace_from_app_iff (proj1_sig prefix_start) prefix_tr suffix_tr); intro Happ.
      simpl in Happ.
      rewrite Hprefix_last in Happ. rewrite <- Hprefix_run in Happ.
      simpl in Happ.
      destruct Happ as [Happ _].
      destruct Hprefix_tr as [Hprefix_tr Hinit].
      specialize (Happ (conj Hprefix_tr Hsuffix_tr)).
      assert (Hfinite_tr: finite_protocol_trace (proj1_sig prefix_start) (prefix_tr ++ suffix_tr))
        by (constructor; assumption).
      assert (Htr : protocol_trace_prop (Finite (proj1_sig prefix_start) (prefix_tr ++ suffix_tr)))
        by assumption.
      exists (exist _ (Finite (proj1_sig prefix_start) (prefix_tr ++ suffix_tr)) Htr).
      simpl.
      exists (length prefix_tr).
      exists (length prefix_tr + length suffix_tr).
      remember (length prefix_tr) as m.
      split.
      - lia.
      - destruct m; simpl.
        + symmetry in Heqm. apply length_zero_iff_nil in Heqm.
          subst; simpl in *.
          split; try (f_equal; assumption).
          remember (length suffix_tr) as delta.
          destruct delta; simpl.
          * symmetry in Heqdelta. apply length_zero_iff_nil in Heqdelta.
            subst; simpl in *. f_equal.
          * apply nth_error_last.
            rewrite map_length. assumption.
        + rewrite map_app.
          assert (Hnth_pref : forall suf, nth_error (List.map destination prefix_tr ++ suf) m = Some first).
          { intro. rewrite nth_error_app1.
            - specialize (nth_error_last (List.map destination prefix_tr) m); intro Hnth.
              assert (Hlen : S m = length (List.map destination prefix_tr))
                by (rewrite map_length; assumption).
              specialize (Hnth Hlen (proj1_sig prefix_start)).
              rewrite Hnth. f_equal. subst.
              rewrite Hprefix_last. reflexivity.
            - rewrite map_length. rewrite <- Heqm. constructor.
          }
          split; try apply Hnth_pref.
          remember (length suffix_tr) as delta.
          destruct delta; simpl.
          * symmetry in Heqdelta. apply length_zero_iff_nil in Heqdelta.
            subst; simpl in *. rewrite Plus.plus_0_r.
            apply Hnth_pref.
          * { rewrite nth_error_app2.
              - rewrite map_length.
                rewrite <- Heqm.
                replace (m + S delta - S m) with  delta by lia.
                specialize (nth_error_last (List.map destination suffix_tr) delta); intro Hnth.
                rewrite map_length in Hnth.
                specialize (Hnth Heqdelta first).
                assumption.
              - rewrite map_length. rewrite <- Heqm.
                lia.
            }
    Qed.

    Definition trace_segment
      (tr : Trace)
      (n1 n2 : nat)
      : list transition_item
      := match tr with
      | Finite s l => list_segment l n1 n2
      | Infinite s l => stream_segment l n1 n2
      end.

    Lemma ptrace_segment
      (tr : Trace)
      (Htr : protocol_trace_prop tr)
      (n1 n2 : nat)
      (Hle : n1 <= n2)
      (first : state)
      (Hfirst : trace_nth tr n1 = Some first)
      : finite_protocol_trace_from first (trace_segment tr n1 n2).
    Proof.
      destruct tr as [s tr | s tr]; simpl in *; destruct Htr as [Htr Hinit].
      - apply finite_protocol_trace_from_segment with s; try assumption.
      - inversion Hfirst; subst; clear Hfirst.
        apply (infinite_protocol_trace_from_segment s tr Htr n1 n2 Hle).
    Qed.

    Inductive Trace_messages : Type :=
    | Finite_messages : list (option message) -> Trace_messages
    | Infinite_messages : Stream (option message) -> Trace_messages.

    Definition protocol_output_messages_trace (tr : protocol_trace) : Trace_messages :=
      match proj1_sig tr with
      | Finite _ ls => Finite_messages (List.map output ls)
      | Infinite _ st => Infinite_messages (map output st) end.

    Definition protocol_input_messages_trace (tr : protocol_trace) : Trace_messages :=
      match proj1_sig tr with
      | Finite _ ls => Finite_messages (List.map input ls)
      | Infinite _ st => Infinite_messages (map input st) end.

    Definition trace_prefix
               (tr : Trace)
               (last : transition_item)
               (prefix : list transition_item)
      :=
        match tr with
        | Finite s ls => exists suffix, ls = prefix ++ (last :: suffix)
        | Infinite s st => exists suffix, st = stream_app prefix (Cons last suffix)
        end.

    Definition trace_prefix_fn
      (tr : Trace)
      (n : nat)
      : Trace
      :=
      match tr with
      | Finite s ls => Finite s (list_prefix ls n)
      | Infinite s st => Finite s (stream_prefix st n)
      end.

    Lemma trace_prefix_protocol
          (tr : protocol_trace)
          (last : transition_item)
          (prefix : list transition_item)
          (Hprefix : trace_prefix (proj1_sig tr) last prefix)
      : protocol_trace_prop (Finite (trace_first (proj1_sig tr)) (prefix ++ [last])).
    Proof.
      destruct tr as [tr Htr]. simpl in *.
      generalize dependent tr. generalize dependent last.
      apply (rev_ind (fun prefix => forall (last : transition_item) (tr : Trace), protocol_trace_prop tr -> trace_prefix tr last prefix -> finite_protocol_trace (trace_first tr) (prefix ++ [last]))).
      - intros last tr Htr Hprefix; destruct tr as [ | ]; unfold trace_prefix in Hprefix;   simpl in Hprefix
        ; destruct Hprefix as [suffix Heq]; subst; destruct Htr as [Htr Hinit]
        ; unfold trace_first; simpl; constructor; try assumption
        ; inversion Htr; subst; clear Htr
        ; specialize
            (finite_ptrace_extend
               s1 [] (finite_ptrace_empty _ (protocol_transition_destination H3))
               s iom oom l1); intro Hext
        ; apply Hext; assumption.
      - intros last_p p Hind last tr Htr Hprefix.
        specialize (Hind last_p tr Htr).
        destruct tr as [ | ]; unfold trace_prefix in Hprefix;   simpl in Hprefix
        ; destruct Hprefix as [suffix Heq]; subst; destruct Htr as [Htr Hinit]; simpl; simpl in Hind
        ; split; try assumption
        .
        + assert
            (Hex : exists suffix0 : list transition_item,
                (p ++ [last_p]) ++ last :: suffix = p ++ last_p :: suffix0
            ) by (exists (last :: suffix); rewrite <- app_assoc; reflexivity)
          ; specialize (Hind Hex); clear Hex
          ; destruct Hind as [Hptr _]
          ; destruct last
          ; apply extend_right_finite_trace_from
          ; try assumption
          .
          rewrite <- (app_cons {| l := l1; input := input0; destination := destination0; output := output0 |} suffix) in Htr.
          rewrite app_assoc in Htr.
          rewrite <- (app_assoc p _ _) in Htr. simpl in Htr.
          rewrite <- app_assoc in Htr.
          specialize
            (finite_ptrace_consecutive_valid_transition
               s
               (p ++ [last_p; {| l := l1; input := input0; destination := destination0; output := output0 |}] ++ suffix)
               suffix
               p
               last_p
               {| l := l1; input := input0; destination := destination0; output := output0 |}
               Htr
               eq_refl
            ).
          simpl.
          rewrite map_app. simpl. rewrite last_is_last. tauto.
        + assert
            (Hex : exists suffix0 : Stream transition_item,
                stream_app (p ++ [last_p])  (Cons last suffix) = stream_app p (Cons last_p suffix0)
            ) by (exists (Cons last suffix); rewrite <- stream_app_assoc; reflexivity)
          ; specialize (Hind Hex); clear Hex
          ; destruct Hind as [Hptr _]
          ; destruct last
          ; apply extend_right_finite_trace_from
          ; try assumption
          .
          rewrite <- stream_app_cons in Htr.
          rewrite stream_app_assoc in Htr.
          rewrite <- (app_assoc p _ _) in Htr. simpl in Htr.
          specialize
            (infinite_ptrace_consecutive_valid_transition
               s
               (stream_app (p ++ [last_p; {| l := l1; input := input0; destination := destination0; output := output0 |}]) suffix)
               suffix
               p
               last_p
               {| l := l1; input := input0; destination := destination0; output := output0 |}
               Htr
               eq_refl
            ).
          simpl.
          rewrite map_app. simpl. rewrite last_is_last. tauto.
    Qed.


    Definition build_trace_prefix_protocol
          {tr : protocol_trace}
          {last : transition_item}
          {prefix : list transition_item}
          (Hprefix : trace_prefix (proj1_sig tr) last prefix)
          : protocol_trace
      := exist _ (Finite (trace_first (proj1_sig tr)) (prefix ++ [last]))
               (trace_prefix_protocol tr last prefix Hprefix).

    Lemma trace_prefix_fn_protocol
          (tr : Trace)
          (Htr : protocol_trace_prop tr)
          (n : nat)
      : protocol_trace_prop (trace_prefix_fn tr n).
    Proof.
      specialize (trace_prefix_protocol (exist _ tr Htr)); simpl; intro Hpref.
      remember (trace_prefix_fn tr n) as pref_tr.
      destruct pref_tr as [s l | s l].
      - destruct l as [| item l].
        + destruct tr as [s' l' | s' l']
          ; destruct Htr as [Htr Hinit]
          ; inversion Heqpref_tr
          ; subst
          ; split; try assumption
          ; constructor
          ; replace s' with (proj1_sig (exist _ s' Hinit))
          ; try reflexivity
          ; exists None
          ; apply protocol_initial_state
          .
        + assert (Hnnil : item ::l <> [])
            by (intro Hnil; inversion Hnil).
          specialize (exists_last Hnnil); intros [prefix [last Heq]].
          rewrite Heq in *; clear Hnnil Heq l item.
          replace s with (trace_first (proj1_sig (exist _ tr Htr)))
          ; try (destruct tr; inversion Heqpref_tr; subst; reflexivity).
          apply trace_prefix_protocol.
          destruct tr as [s' l' | s' l']
          ; inversion Heqpref_tr
          ; subst
          ; clear Heqpref_tr
          ; simpl.
          * specialize (list_prefix_suffix l' n); intro Hl'.
            rewrite <- Hl'. rewrite <- H1.
            exists (list_suffix l' n).
            rewrite <- app_assoc.
            reflexivity.
          * specialize (stream_prefix_suffix l' n); intro Hl'.
            rewrite <- Hl'. rewrite <- H1.
            exists (stream_suffix l' n).
            rewrite <- stream_app_assoc.
            reflexivity.
      - destruct tr as [s' l' | s' l']; inversion Heqpref_tr.
    Qed.

    Lemma protocol_trace_nth
      (tr : Trace)
      (Htr : protocol_trace_prop tr)
      (n : nat)
      (s : state)
      (Hnth : trace_nth tr n = Some s)
      : protocol_state_prop s.
    Proof.
      destruct tr as [s0 l | s0 l]; destruct Htr as [Htr Hinit].
      - specialize (finite_protocol_trace_from_suffix s0 l Htr n s Hnth).
        intro Hsuf.
        apply finite_ptrace_first_pstate in Hsuf.
        assumption.
      - assert (Hle : n <= n) by lia.
        specialize (infinite_protocol_trace_from_segment s0 l Htr n n Hle)
        ; simpl; intros Hseg.
        inversion Hnth.
        apply finite_ptrace_first_pstate in Hseg.
        assumption.
    Qed.
(* alternate proof without assuming protocol_transition implies protocol_state
      destruct n.
      - exists None.
        destruct tr as [s0 l | s0 l]
        ; inversion Hnth; try (unfold Str_nth in H0; simpl in H0); subst; clear Hnth
        ; destruct Htr as [_ Hinit]
        ; replace s with (proj1_sig (exist _ s Hinit)); try reflexivity
        ;  apply protocol_initial_state.
      - specialize (trace_prefix_fn_protocol tr Htr (S n)); intro Hpref_tr.
        remember (trace_prefix_fn tr (S n)) as pref_tr.
        destruct pref_tr as [s0 l | s0 l]
        ; try (destruct tr as [s' l' | s' l']; inversion Heqpref_tr)
        ; subst; clear Heqpref_tr
        ; destruct Hpref_tr as [Hpref_tr Hinit]
        ; specialize (trace_is_protocol (exist _ s' Hinit)); intro Hps
        ; specialize (Hps (list_prefix l' (S n))) || specialize (Hps (stream_prefix l' (S n)))
        ; specialize (Hps Hpref_tr)
        ; rewrite list_prefix_map in Hps || rewrite stream_prefix_map in Hps
        ; destruct Hps as [om Hps]
        ; exists om
        .
        + replace s with (last (list_prefix (List.map destination l') (S n)) s')
          ; try assumption.
          symmetry.
          apply list_prefix_nth_last.
          assumption.
        + replace s with (last (stream_prefix (Streams.map destination l') (S n)) s')
          ; try assumption.
          rewrite stream_prefix_nth_last.
          inversion Hnth.
          reflexivity.
*)

    Lemma in_futures_protocol_snd
      (first second : state)
      (Hfutures: in_futures first second)
      : protocol_state_prop second.
    Proof.
      specialize (in_futures_witness first second Hfutures)
      ; intros [tr [n1 [n2 [Hle [Hn1 Hn2]]]]].
      destruct tr as [tr Htr]; simpl in Hn2.
      apply protocol_trace_nth with tr n2; assumption.
    Qed.

    Lemma in_futures_witness_reverse
      (first second : state)
      (tr : protocol_trace)
      (n1 n2 : nat)
      (Hle : n1 <= n2)
      (Hs1 : trace_nth (proj1_sig tr) n1 = Some first)
      (Hs2 : trace_nth (proj1_sig tr) n2 = Some second)
      : in_futures first second.
    Proof.
      destruct tr as [tr Htr].
      simpl in *.
      inversion Hle; subst; clear Hle.
      - rewrite Hs1 in Hs2. inversion Hs2; subst; clear Hs2.
        exists []. split.
        + constructor. apply protocol_trace_nth with tr n2; assumption.
        + reflexivity.
      -  exists (trace_segment tr n1 (S m)).
        split.
        + apply ptrace_segment; try assumption. lia.
        + { destruct tr as [s tr | s tr]; simpl.
          - unfold list_segment.
            rewrite list_suffix_map. rewrite list_prefix_map.
            simpl in Hs2.
            rewrite list_suffix_last.
            + symmetry. apply list_prefix_nth_last. assumption.
            + apply nth_error_length in Hs2.
              specialize (list_prefix_length (List.map destination tr) (S m) Hs2); intro Hpref_len.
              rewrite Hpref_len.
              lia.
          - unfold stream_segment.
            rewrite list_suffix_map. rewrite stream_prefix_map.
            simpl in Hs2.
            rewrite list_suffix_last.
            + symmetry. rewrite stream_prefix_nth_last.
              unfold Str_nth in Hs2. simpl in Hs2.
              inversion Hs2; subst.
              reflexivity.
            + specialize (stream_prefix_length (Streams.map destination tr) (S m)); intro Hpref_len.
              rewrite Hpref_len.
              lia.
          }
    Qed.
    (* end hide *)

(**
Stating livness properties will require quantifying over complete
executions of the protocol. To make this possible, we will now define
_complete_ [protocol_trace]s.

A [protocol_trace] is _terminating_ if there's no other [protocol_trace]
that contains it as a prefix.
*)

    Definition terminating_trace_prop (tr : Trace) : Prop
       :=
         match tr with
         | Finite s ls =>
             (exists (tr : protocol_trace)
             (last : transition_item),
             trace_prefix (proj1_sig tr) last ls) -> False
         | Infinite s ls => False
         end.

(** A [protocol_trace] is _complete_, if it is either _terminating_ or infinite.
*)

    Definition complete_trace_prop (tr : Trace) : Prop
       := protocol_trace_prop tr
          /\
          match tr with
          | Finite _ _ => terminating_trace_prop tr
          | Infinite _ _ => True
          end.

    (* begin hide *)

    (* Implicitly, the state itself must be in the trace, and minimally the last element of the trace *)
    (* Also implicitly, the trace leading up to the state is finite *)
    (* Defining equivocation on these trace definitions *)

    (* Section 7 :
       A message m received by a protocol state s with a transition label l in a
       protocol execution trace is called "an equivocation" if it wasn't produced
       in that trace
    *)

    (* 6.2.2 Equivocation-free as a composition constraint *)
    Definition composition_constraint : Type :=
      label -> state * option message -> Prop.

    (* Decidable VLSMs *)

    Class VLSM_vdecidable :=
      { valid_decidable : forall l som, {valid l som} + {~valid l som}
      }.
(* end hide *)
  End VLSM.

(**
** VLSM Inclusion and Equality.

We can also define VLSM _inclusion_  and _equality_ in terms of traces.
- VLSM X is _included_ in VLSM Y if every [protocol_trace] available to X
is also available to Y.
- VLSM X and VLSM Y are _equal_ if their [protocol_trace]s are exactly the same.
*)

  Section VLSM_equality.
    Context
      {message : Type}
      {vtype : VLSM_type message}.


    Definition VLSM_eq
      {SigX SigY: VLSM_sign vtype}
      (X : VLSM SigX) (Y : VLSM SigY)
      :=
      forall t : Trace,
        protocol_trace_prop X t <-> protocol_trace_prop Y t.

    Definition VLSM_incl
      {SigX SigY: VLSM_sign vtype}
      (X : VLSM SigX) (Y : VLSM SigY)
      :=
      forall t : Trace,
        protocol_trace_prop X t -> protocol_trace_prop Y t.

    (* begin hide *)

    Lemma VLSM_eq_incl_l
      {SigX SigY: VLSM_sign vtype}
      (X : VLSM SigX) (Y : VLSM SigY)
      : VLSM_eq X Y -> VLSM_incl X Y.
    Proof.
      intro Heq.
      intros t Hxt.
      apply Heq.
      assumption.
    Qed.

    Lemma VLSM_eq_incl_r
      {SigX SigY: VLSM_sign vtype}
      (X : VLSM SigX) (Y : VLSM SigY)
      : VLSM_eq X Y -> VLSM_incl Y X.
    Proof.
      intro Heq.
      intros t Hyt.
      apply Heq.
      assumption.
    Qed.

    Lemma VLSM_eq_incl_iff
      {SigX SigY: VLSM_sign vtype}
      (X : VLSM SigX) (Y : VLSM SigY)
      : VLSM_eq X Y <-> VLSM_incl X Y /\ VLSM_incl Y X.
    Proof.
      split.
      - intro Heq.
        split.
        + apply VLSM_eq_incl_l; assumption.
        + apply VLSM_eq_incl_r; assumption.
      - intros [Hxy Hyx].
        intro t.
        split.
        + apply Hxy.
        + apply Hyx.
    Qed.
  (* end hide *)
  End VLSM_equality.

(** It is natural to look for sufficient conditions for VLSM inclusion (or equality),
which are easy to verify in a practical setting. One such result is the following.

For VLSM <<X>> to be included in VLSM <<Y>>, the following set of conditions is sufficient:
- <<X>>'s [initial_state]s are included in <<Y>>'s [initial state]s
- Every message <<m>> (including the empty one) which can be input to a
[protocol_valid] transition in <<X>>, is a [protocol_message] in <<Y>>
- <<X>>'s [protocol_valid] is included in <<Y>>'s [valid].
- For all [protocol_valid] inputs (in <<X>>), <<Y>>'s [transition] acts
like <<X>>'s [transition].
*)

Section basic_VLSM_incl.

Context
  {message : Type}
  {T : VLSM_type message}
  {SX SY : VLSM_sign T}
  (X : VLSM SX)
  (Y : VLSM SY)
  (Hinitial_state :
    forall s : state,
      @initial_state_prop _ _ SX s -> @initial_state_prop _ _ SY s
  )
  (Hprotocol_message :
    forall (l : label) (s : state) (om : option message),
      protocol_valid X l (s, om)
      -> option_protocol_message_prop Y om
  )
  (Hvalid :
    forall (l : label) (s : state) (om : option message),
      protocol_valid X l (s, om)
      -> @valid _ _ _ Y l (s, om)
  )
  (Htransition :
    forall (l : label) (s : state) (om : option message),
      protocol_valid X l (s, om)
      -> @transition _ _ _ X l (s, om) = @transition _ _ _ Y l (s, om)
  )
  .

(* begin hide *)
Lemma VLSM_incl_protocol_state
  (s : state)
  (om : option message)
  (Hps : protocol_prop X (s,om))
  : protocol_state_prop Y s.
Proof.
  remember (s, om) as som.
  generalize dependent om. generalize dependent s.
  induction Hps; intros; inversion Heqsom; subst; clear Heqsom.
  - exists None.
    unfold s in *. clear s.
    destruct is as [is His]; simpl.
    apply Hinitial_state in His.
    replace is with (proj1_sig (exist _ is His)); try reflexivity.
    apply (protocol_initial_state Y).
  - exists None.
    unfold s in *. clear s.
    destruct s0 as [is His]; simpl.
    apply Hinitial_state in His.
    replace is with (proj1_sig (exist _ is His)); try reflexivity.
    apply (protocol_initial_state Y).
  - exists om0.
    specialize (protocol_generated_valid X Hps1 Hps2 Hv); intros Hpv.
    rewrite Htransition in H0; try assumption.
    specialize (IHHps1 s _om eq_refl). destruct IHHps1 as [_omf Hfps].
    replace (s1, om0) with (  @transition _ _ _ Y l1 (s, om))
    ; try assumption.
    specialize (Hprotocol_message l1 s om Hpv).
    destruct Hprotocol_message as [_sX HpmX].
    apply (protocol_generated Y) with _omf _sX; try assumption.
    specialize (Hvalid l1 s om Hpv).
    assumption.
Qed.

Lemma VLSM_incl_protocol_transition
  (l : label)
  (is os : state)
  (iom oom : option message)
  (Ht : protocol_transition X l (is, iom) (os, oom))
  : protocol_transition Y l (is, iom) (os, oom).
Proof.
  destruct Ht as [[[_om Hps] [[_s Hpm] Hv]] Ht].
  specialize (protocol_generated_valid X Hps Hpm Hv); intros Hpv.
  repeat split.
  - apply VLSM_incl_protocol_state with _om. assumption.
  - apply Hprotocol_message in Hpv. assumption.
  - specialize (Hvalid l is iom Hpv).
    assumption.
  - rewrite <- Htransition; assumption.
Qed.

  Lemma VLSM_incl_finite_ptrace
    (s : state)
    (ls : list transition_item)
    (Hpxt : finite_protocol_trace_from X s ls)
    : finite_protocol_trace_from Y s ls.
  Proof.
    induction Hpxt.
    - constructor.
      destruct H as [m H].
      apply VLSM_incl_protocol_state in H. assumption.
    - constructor; try assumption.
      apply VLSM_incl_protocol_transition. assumption.
  Qed.

  Lemma VLSM_incl_infinite_ptrace
    (s : state)
    (ls : Stream transition_item)
    (Hpxt : infinite_protocol_trace_from X s ls)
    : infinite_protocol_trace_from Y s ls.
  Proof.
    generalize dependent ls. generalize dependent s.
    cofix H.
    intros s [[l input destination output] ls] Hx.
    inversion Hx; subst.
    specialize (H destination ls H3).
    constructor; try assumption.
    apply VLSM_incl_protocol_transition.
    assumption.
  Qed.

  (* end hide *)

  Lemma basic_VLSM_incl
    : VLSM_incl X Y.
  Proof.
    intros [s ls| s ss]; simpl; intros [Hxt Hinit].
    - apply VLSM_incl_finite_ptrace in Hxt.
      split; try assumption.
      apply Hinitial_state. assumption.
    - apply VLSM_incl_infinite_ptrace in Hxt.
      split; try assumption.
      apply Hinitial_state. assumption.
  Qed.

End basic_VLSM_incl.

(**
** Pre-loaded VLSMs

Given a VLSM <<X>>, we introduce the _pre-loaded_ version of it,
which is identical to <<X>>, except that it is endowed with the
whole message universe as its initial messages. The high degree
of freedom allowed to the _pre-loaded_ version lets it experience
everything experienced by <<X>> but also other types of behaviour,
including _Byzantine_ behaviour, which makes it a useful concept in
Byzantine fault tolerance analysis. *)


  Section pre_loaded_vlsm.
    Context
      {message : Type}
      {vtype : VLSM_type message}
      {Sig : VLSM_sign vtype}
      .

  Definition pre_loaded_vlsm_sig
    (X : VLSM Sig)
    : VLSM_sign vtype
    :=
    {| initial_state_prop := @initial_state_prop _ _ Sig
     ; initial_message_prop := fun message => True
     ; s0 := @s0 _ _ Sig
     ; m0 := @m0 _ _ Sig
     ; l0 := @l0 _ _ Sig
    |}.

  Context (X : VLSM Sig).

  Definition pre_loaded_vlsm
    : VLSM (pre_loaded_vlsm_sig X)
    :=
    {| transition := @transition _ _ _ X
     ; valid := @valid _ _ _ X
    |}.

  (**
    A message which can be emitted during a protocol run of
    the [pre_loaded_vlsm] is called a [byzantine_message], because
    as shown by Lemmas [byzantine_pre_loaded] and [pre_loaded_alt_eq],
    byzantine traces for a [VLSM] are precisely the protocol traces
    of the [pre_loaded_vlsm], hence a byzantine message is any message
    which a byzantine trace [can_emit].
  *)

  Definition byzantine_message_prop
    (m : message)
    : Prop
    := can_emit pre_loaded_vlsm m.

  Definition byzantine_message : Type
    := sig byzantine_message_prop.

  (* begin hide *)
  Lemma pre_loaded_protocol_prop
    (s : state)
    (om : option message)
    (Hps : protocol_prop X (s, om))
    : protocol_prop pre_loaded_vlsm (s, om).
  Proof.
    induction Hps.
    - apply (protocol_initial_state pre_loaded_vlsm is).
    - destruct im as [m Him]. simpl in om0. clear Him.
      assert (Him : @initial_message_prop _ _ (pre_loaded_vlsm_sig X) m)
        by exact I.
      apply (protocol_initial_message pre_loaded_vlsm (exist _ m Him)).
    - apply (protocol_generated pre_loaded_vlsm) with _om _s; assumption.
  Qed.

  Lemma pre_loaded_can_emit
    (m : message)
    (Hm : can_emit X m)
    : can_emit pre_loaded_vlsm m.
  Proof.
    destruct Hm as [(s0, om0) [l [s [[[_om0 Hs0] [[_s0 Hom0] Hv]] Ht]]]].
    apply pre_loaded_protocol_prop in Hs0.
    apply pre_loaded_protocol_prop in Hom0.
    exists (s0, om0). exists l. exists s.
    repeat split; try assumption.
    - exists _om0. assumption.
    - exists _s0. assumption.
  Qed.

  (* end hide *)

  Lemma vlsm_incl_pre_loaded_vlsm
    : VLSM_incl X pre_loaded_vlsm.
  Proof.
    apply (basic_VLSM_incl X pre_loaded_vlsm)
    ; intros; try (assumption || reflexivity)
    ; destruct H as [_ [[_s Hpm] Hv]].
    - exists _s. apply pre_loaded_protocol_prop. assumption.
    - assumption.
  Qed.

End pre_loaded_vlsm.

