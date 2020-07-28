From CasperCBC Require Import Lib.SsrExport.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Ltac invs h := inversion h; subst => {h}.

Section Traces.

Context {A B : Type}.

CoInductive trace : Type  :=
| Tnil : A -> trace
| Tcons : A -> B -> trace -> trace.

Definition trace_decompose (tr: trace): trace :=
match tr with
| Tnil a => Tnil a
| Tcons a b tr' => Tcons a b tr'
end.

Lemma trace_destr: forall tr, tr = trace_decompose tr.
Proof. case => //=. Qed.

CoInductive bisim: trace -> trace -> Prop :=
| bisim_nil: forall a,
  bisim (Tnil a) (Tnil a)
| bisim_cons: forall a b tr tr',
  bisim tr tr' ->
  bisim (Tcons a b tr) (Tcons a b tr').

Lemma bisim_refl : forall tr, bisim tr tr. 
Proof.
cofix CIH.
case => [a|a b tr]; first exact: bisim_nil.
apply bisim_cons.
exact: CIH.
Qed.

Lemma bisim_sym : forall tr1 tr2, bisim tr1 tr2 -> bisim tr2 tr1. 
Proof.
cofix CIH.
case => [a|a b tr1] tr2 Hbs; invs Hbs; first exact: bisim_nil.
by apply: bisim_cons; apply (CIH _ _ H3).
Qed.

Lemma bisim_trans : forall tr1 tr2 tr3,
 bisim tr1 tr2 -> bisim tr2 tr3 -> bisim tr1 tr3.
Proof.
cofix CIH. 
case => [a|a b tr1] tr2 tr0 Hbs Hbs'; invs Hbs; invs Hbs'; first exact: bisim_nil.
apply: bisim_cons.
exact: CIH _ _ _ H3 H4.
Qed.

CoFixpoint trace_append (tr tr': trace): trace :=
match tr with
| Tnil a => tr'
| Tcons a b tr0 => Tcons a b (trace_append tr0 tr')
end.

Local Infix "+++" := trace_append (at level 60, right associativity).

Lemma trace_append_nil: forall a tr, (Tnil a) +++ tr = tr.
Proof. 
move => a tr.
rewrite [Tnil a +++ tr]trace_destr.
by case tr.
Qed.

Lemma trace_append_cons: forall a b tr tr',
 (Tcons a b tr) +++ tr' = Tcons a b (tr +++ tr').
Proof.
move => a b tr tr'.
rewrite [Tcons a b tr +++ tr']trace_destr.
by case tr.
Qed.

Lemma trace_eq_append: forall tr1 tr2 tr3 tr4, 
 bisim tr1 tr2 -> bisim tr3 tr4 -> bisim (tr1 +++ tr3) (tr2 +++ tr4).
Proof. 
cofix CIH. 
case => [a|a b tr1] tr2 tr3 tr4 Hbs1 Hbs2; invs Hbs1.
- do 2 rewrite trace_append_nil.
  exact: Hbs2.
- do 2 rewrite trace_append_cons.
  apply: bisim_cons.
  exact: CIH.
Qed.

Definition hd tr := match tr with Tnil a => a | Tcons a b tr0 => a end.

Lemma bisim_hd: forall tr0 tr1, bisim tr0 tr1 -> hd tr0 = hd tr1. 
Proof. by move => tr0 tr1 h0; invs h0. Qed.

End Traces.

Infix "+++" := trace_append (at level 60, right associativity).
