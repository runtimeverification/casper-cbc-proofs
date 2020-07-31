From Coq Require Import Classical ClassicalEpsilon.
From CasperCBC Require Import Lib.SsrExport Lib.Traces Lib.TraceProperties.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section TraceClassicalProperties.

Context {A B : Type}.

Local Notation trace := (@trace A B).
Local Notation propT := (@propT A B).

Lemma not_infiniteT_finiteT : forall tr : trace,
 ~ infiniteT tr -> finiteT tr.
Proof.
move => tr Hnot.
case (classic (finiteT tr)) => Hinf //.
case: Hnot.
exact: not_finiteT_infiniteT.
Qed.

Lemma finiteT_infiniteT : forall tr : trace,
 finiteT tr \/ infiniteT tr.
Proof.
move => tr.
case (classic (finiteT tr)) => Hinf; first by left.
right.
exact: not_finiteT_infiniteT.
Qed.

Definition finiteT_infiniteT_dec (tr : trace) : { finiteT tr }+{ infiniteT tr } :=
match excluded_middle_informative (finiteT tr) with
| left Hfin => left Hfin
| right Hfin => right (not_finiteT_infiniteT Hfin)
end.

CoFixpoint midp (p0 p1: trace -> Prop) tr0 tr1 (h: followsT (appendT p0 p1) tr0 tr1) : trace.
Proof.
case (followsT_dec h).
- case => tr; case => st; case => h1; case => h2 h3.
  apply constructive_indefinite_description in h3.
  case: h3 => x [h4 h5].
  apply x.
- case => tr; case => tr'. case => a; case => b; case => h1; case => h2 h3.
  apply (Tcons a b (@midp _ _ _ _ h3)).
Defined.

Lemma midpointT_midp : forall (p0 p1: trace -> Prop)  tr0 tr1 (h : followsT (appendT p0 p1) tr0 tr1),
 midpointT h (midp h).
Proof.
cofix CIH.
dependent inversion h.
- subst.
  intros.
  rewrite [midp _]trace_destr. simpl.
  case (constructive_indefinite_description _ _); simpl.
  move => x [a1 hm].
  by apply midpointT_nil => //; destruct x.
- subst.
  rewrite [midp _]trace_destr. simpl.
  by apply (@midpointT_delay _ _ p0 p1 (Tcons a b tr) (Tcons a b tr') (followsT_delay a b f) tr tr' f a b (midp f)).
Qed.

Lemma appendT_assoc_R: forall p1 p2 p3,
 forall tr : trace, (appendT p1 (appendT p2 p3)) tr -> (appendT (appendT p1 p2)  p3) tr.
Proof.
move => p1 p2 p3 tr0 h1.  move: h1 => [tr1 [h1 h2]].
exists (midp h2). split.
- exists tr1; split => //.
  exact: (midpointT_before (midpointT_midp h2)).
- exact: (midpointT_after (midpointT_midp h2)).
Qed.

Lemma AppendT_assoc_R: forall (p1 p2 p3 : propT), (p1 *** p2 *** p3) =>> (p1 *** p2) *** p3.
Proof.
move => p1 p2 p3 tr0 h1. destruct p1 as [f1 hf1]. destruct p2 as [f2 hf2].
destruct p3 as [f3 hf3]. simpl. simpl in h1. apply appendT_assoc_R. by apply h1.
Qed.

End TraceClassicalProperties.
