From Coq Require Import List Streams.
From Coq Require Import Program.Equality.
From CasperCBC Require Import Lib.SsrExport Lib.Traces Lib.TraceProperties Lib.TraceClassicalProperties.
From CasperCBC Require Import Lib.StreamExtras Lib.Preamble VLSM.Common.
Import ListNotations.

(** * Protocols described by possibly-infinite traces *)

Section VLSM.

Context `{M : VLSM_class} (vlsm := mk_vlsm M).

(** ** Core protocol definitions *)

Record tr_data := mkTrData {
 tr_label : label;
 tr_input : option message;
 tr_output : option message
}.

Local Notation trace := (@trace state tr_data).

CoInductive protocol_trace : trace -> Prop :=
| protocol_trace_nil : forall (s : state),
   protocol_state_prop vlsm s ->
   protocol_trace (Tnil s)
| protocol_trace_delay : forall (s : state) (d : tr_data) (tr : trace),
   protocol_trace tr ->
   protocol_transition vlsm (tr_label d) (s, tr_input d) (hd tr, tr_output d) ->
   protocol_trace (Tcons s d tr).

Definition protocol_ptrace tr :=
  protocol_trace tr /\ initial_state_prop (hd tr).

(** ** Mappings between finite traces and lists of transition items *)

Fixpoint protocol_trace_finite_transition_items (tr : trace) (h: finiteT tr) {struct h} : list transition_item :=
match tr as tr' return (finiteT tr' -> _) with
| Tnil s => fun _ => []
| Tcons s d tr => fun h =>
   {| l := tr_label d; input := tr_input d; destination := hd tr; output := tr_output d |} ::
    protocol_trace_finite_transition_items tr (invert_finiteT_delay h)
end h.

Fixpoint transition_items_list_protocol_trace (s : state) (ls : list transition_item) : trace :=
match ls with
| [] => Tnil s
| ti :: ls' =>
  Tcons s {| tr_label := l ti; tr_input := input ti; tr_output := output ti |}
   (transition_items_list_protocol_trace (destination ti) ls')
end.

Lemma protocol_trace_finite_finite_protocol_trace_from : forall tr (h:finiteT tr),
 protocol_trace tr ->
 finite_protocol_trace_from vlsm (hd tr) (protocol_trace_finite_transition_items tr h).
Proof.
refine (fix IH tr h {struct h} := _).
case: tr h => [s|s d tr] h Htr /=.
- dependent inversion h; subst => /=.
  inversion Htr; subst.
  by apply finite_ptrace_empty.
- dependent inversion h; subst => /=.
  inversion Htr; subst.
  apply finite_ptrace_extend => //.
  by apply IH.
Qed.

Lemma transition_items_list_protocol_trace_hd_nil : forall l s0 s1,
 Tnil s0 = transition_items_list_protocol_trace s1 l ->
 s0 = s1.
Proof.
case => //=.
move => s0 s1 Hs.
by inversion Hs.
Qed.

Lemma transition_items_list_protocol_trace_hd_cons : forall l s0 s1 d tr,
 Tcons s0 d tr = transition_items_list_protocol_trace s1 l ->
 s0 = s1.
Proof.
case => //=.
move => a l s0 s1 d tr Hs.
by inversion Hs.
Qed.

Lemma finite_protocol_trace_from_protocol_trace : forall ls s,
 finite_protocol_trace_from vlsm s ls ->
 protocol_trace (transition_items_list_protocol_trace s ls).
Proof.
elim => //=.
- move => s Hf.
  inversion Hf; subst.
  by apply protocol_trace_nil.
- move => a l IH s Hf.
  inversion Hf; subst => /=.
  apply protocol_trace_delay => /=; first by apply IH.
  have IH' := IH _ H2.
  inversion IH'; subst.
  * by rewrite /= (transition_items_list_protocol_trace_hd_nil _ _ _ H).
  * by rewrite /= (transition_items_list_protocol_trace_hd_cons _ _ _ _ _ H).
Qed.

(** ** Mappings between infinite traces and streams of transition items *)

Program CoFixpoint protocol_trace_infinite_transition_items (tr : trace) (h: infiniteT tr) : Stream transition_item :=
match tr with
| Tnil _ => False_rect _ _
| Tcons s d tr =>
  Cons {| l := tr_label d; input := tr_input d; destination := hd tr; output := tr_output d |}
       (protocol_trace_infinite_transition_items tr _)
end.
Next Obligation.
by inversion h.
Defined.
Next Obligation.
by inversion h; subst.
Defined.

CoFixpoint transition_items_stream_protocol_trace (s : state) (st : Stream transition_item) : trace :=
match st with
| Cons ti st' =>
  Tcons s {| tr_label := l ti; tr_input := input ti; tr_output := output ti |}
   (transition_items_stream_protocol_trace (destination ti) st')
end.

Lemma protocol_trace_infinite_infinite_protocol_trace_from : forall tr (h:infiniteT tr),
 protocol_trace tr ->
 infinite_protocol_trace_from vlsm (hd tr) (protocol_trace_infinite_transition_items tr h).
Proof.
cofix CIH.
destruct tr; first by move => h; inversion h.
move => h Htr /=.
inversion Htr; subst.
dependent inversion h; subst.
rewrite -(recons (protocol_trace_infinite_transition_items _ _)).
simpl.
apply infinite_ptrace_extend => //.
by apply CIH.
Qed.

Lemma infinite_protocol_trace_from_protocol_trace : forall st s,
 infinite_protocol_trace_from vlsm s st ->
 protocol_trace (transition_items_stream_protocol_trace s st).
Proof.
cofix CIH.
case => ti st' s Hif.
inversion Hif; subst.
rewrite [transition_items_stream_protocol_trace _ _]trace_destr /=.
apply protocol_trace_delay.
- by apply CIH.
- by inversion H2; subst.
Qed.

(** ** Mappings between Trace containers and possibly-infinite traces *)

Definition Trace_from_trace (tr : trace) : Trace :=
match finiteT_infiniteT_dec tr with
| left Hfin => Finite (hd tr) (protocol_trace_finite_transition_items tr Hfin)
| right Hinf => Infinite (hd tr) (protocol_trace_infinite_transition_items tr Hinf)
end.

Definition trace_from_Trace (Tr : Trace) : trace :=
match Tr with
| Finite s ls => transition_items_list_protocol_trace s ls
| Infinite s sm => transition_items_stream_protocol_trace s sm
end.

Lemma Trace_from_trace_ptrace_from_prop : forall tr,
 protocol_trace tr ->
 ptrace_from_prop vlsm (Trace_from_trace tr).
Proof.
move => tr Hptr.
rewrite /Trace_from_trace.
case (finiteT_infiniteT_dec _) => [Hfin|Hinf] /=.
- exact: protocol_trace_finite_finite_protocol_trace_from.
- exact: protocol_trace_infinite_infinite_protocol_trace_from.
Qed.

Lemma trace_from_Trace_ptrace_from_prop : forall Tr,
 ptrace_from_prop vlsm Tr ->
 protocol_trace (trace_from_Trace Tr).
Proof.
case => [s ls|s sm] /=.
- exact: finite_protocol_trace_from_protocol_trace.
- exact: infinite_protocol_trace_from_protocol_trace.
Qed.

End VLSM.
