From Coq Require Import List Streams.
From Coq Require Import Program.Equality.
From CasperCBC Require Import Lib.SsrExport Lib.Traces Lib.TraceProperties Lib.StreamExtras Lib.Preamble VLSM.Common.
Import ListNotations.

Section VLSM.

Context `{vlsm : VLSM}.

Record tr_data := mkTrData { tr_label : label; tr_input : option message; tr_output : option message }.

Local Notation trace := (@trace state tr_data).

CoInductive protocol_trace : trace -> Prop :=
| protocol_trace_nil : forall (s : state), protocol_state_prop vlsm s -> protocol_trace (Tnil s)
| protocol_trace_further : forall (s : state) (d : tr_data) (tr : trace),
    protocol_trace tr ->
    protocol_transition vlsm (tr_label d) (s, tr_input d) (hd tr, tr_output d) ->
    protocol_trace (Tcons s d tr).

Definition protocol_ptrace tr :=
  protocol_trace tr /\ initial_state_prop (hd tr).

Fixpoint protocol_trace_finite_transition_items (tr : trace) (h: finite tr) {struct h} : list transition_item :=
  match tr as tr' return (finite tr' -> _) with
  | Tnil s => fun _ => []
  | Tcons s d tr => fun h =>
     {| l := tr_label d; input := tr_input d; destination := hd tr; output := tr_output d |} ::
      protocol_trace_finite_transition_items tr (invert_finite_delay h)
  end h.

Program CoFixpoint protocol_trace_infinite_transition_items (tr : trace) (h: infinite tr) : Stream transition_item :=
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

Lemma protocol_trace_finite_finite_protocol_trace_from : forall tr (h:finite tr), protocol_trace tr ->
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

Lemma protocol_trace_infinite_infinite_protocol_trace_from : forall tr (h:infinite tr), protocol_trace tr ->
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

End VLSM.
