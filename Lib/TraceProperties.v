From Coq Require Import Program.Equality.
From CasperCBC Require Import Lib.SsrExport Lib.Traces.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section TraceProperties.

Context {A B : Type}.

Local Notation trace := (@trace A B).

Definition setoidT (p : trace -> Prop) :=
forall tr0, p tr0 -> forall tr1, bisim tr0 tr1 -> p tr1.

Definition propT := { p : trace -> Prop | setoidT p }.
Definition propA := A -> Prop.

Inductive finiteT : trace -> Prop :=
| finiteT_nil: forall a, finiteT (Tnil a)
| finiteT_delay: forall (a : A) (b : B) tr,
  finiteT tr -> finiteT (Tcons a b tr).

Lemma finiteT_setoidT : setoidT finiteT.
Proof.
induction 1.
- move => tr0 h0. invs h0. apply finiteT_nil.
- move => tr0 h0. invs h0.
  exact (finiteT_delay a b (IHfiniteT _ H4)).
Qed.

Definition FiniteT : propT.
 exists (fun tr => finiteT tr).
 move => tr0 h0 tr1 h1.
 exact: (finiteT_setoidT h0 h1).
Defined.

Lemma invert_finiteT_delay (a : A) (b : B) (tr : trace)
 (h : finiteT (Tcons a b tr)) : finiteT tr.
Proof.
 by inversion h.
Defined.

(* pattern for Fixpoint using finiteT *)
Fixpoint id_finiteT (tr : trace) (h : finiteT tr) {struct h} : trace :=
  match tr as tr' return (finiteT tr' -> trace) with
  | Tnil a => fun _ => Tnil a
  | Tcons a b tr => fun h => id_finiteT (invert_finiteT_delay h)
  end h.

(* pattern for inductive proofs using finiteT *)
Lemma id_finiteT_eq : forall tr (h h':finiteT tr),
 id_finiteT h = id_finiteT h'.
Proof.
refine (fix IH tr h {struct h} := _).
case: tr h => [a|a b tr] h.
- by dependent inversion h; move => h'; depelim h'; simpl; reflexivity.
- by dependent inversion h; move => h'; depelim h'; simpl; apply IH.
Qed.

CoInductive infiniteT : trace -> Prop :=
| infiniteT_delay: forall a b tr,
  infiniteT tr -> infiniteT (Tcons a b tr).

Lemma infiniteT_setoidT : setoidT infiniteT.
Proof.
cofix CIH. 
move => tr0 h0 tr1 h1. 
invs h0. invs h1.
exact: (infiniteT_delay a b (CIH _ H _ H4)).
Qed.

Definition InfiniteT : propT.
exists (fun tr => infiniteT tr). 
exact: infiniteT_setoidT.
Defined.

Lemma infiniteT_cons : forall a b tr,
 infiniteT (Tcons a b tr) -> infiniteT tr.
Proof.
move => a b tr Hinf.
by inversion Hinf.
Qed.

Lemma infiniteT_trace_append :
 forall tr, infiniteT tr -> forall tr', infiniteT (tr' +++ tr).
Proof.
cofix CIH.
move => tr Htr.
case => [a|a b tr']; first by rewrite trace_append_nil.
rewrite trace_append_cons.
apply infiniteT_delay.
by apply CIH.
Qed.

Lemma trace_append_infiniteT :
 forall tr, infiniteT tr -> forall tr', infiniteT (tr +++ tr').
Proof.
cofix CIH.
case => [a|a b tr0] Hinf; first by inversion Hinf.
inversion Hinf; subst => tr'.
rewrite trace_append_cons.
apply infiniteT_delay.
exact: CIH.
Qed.

Lemma finiteT_infiniteT_False : forall tr,
 finiteT tr -> infiniteT tr -> False.
Proof.
move => tr; elim => [a Hinf|a b tr' Hfin]; first by inversion Hinf.
by move => IH Hinf; inversion Hinf.
Qed.

Lemma not_finiteT_infiniteT : forall tr,
 ~ finiteT tr -> infiniteT tr.
Proof.
cofix CIH.
case => [a|a b tr] Hfin; first by case: Hfin; apply finiteT_nil.
apply infiniteT_delay.
apply CIH => Hinf.
case: Hfin.
exact: finiteT_delay.
Qed.

Definition satisfyT (p:propT) : trace -> Prop := 
fun tr => let: exist f0 h0 := p in f0 tr.

Definition AndT (p1 p2 : propT) : propT.
destruct p1 as [f0 h0]. 
destruct p2 as [f1 h1].
exists (fun tr => f0 tr /\ f1 tr). 
move => tr0 [h2 h3] tr1 h4. split.
- exact: (h0 _ h2 _ h4).
- exact: (h1 _ h3 _ h4).
Defined.

Local Infix "andT" := AndT (at level 60, right associativity).

Definition OrT (p1 p2: propT): propT.
destruct p1 as [f0 h0]. 
destruct p2 as [f1 h1].
exists (fun tr => f0 tr \/ f1 tr). 
move => tr0 [h2 | h2] tr1 h3.
- left. exact: h0 _ h2 _ h3.
- right. exact: h1 _ h2 _ h3.
Defined.

Local Infix "orT" := OrT (at level 60, right associativity).

Definition propT_imp (p1 p2: propT) : Prop :=
forall tr, satisfyT p1 tr -> satisfyT p2 tr.

Local Infix "=>>" := propT_imp (at level 60, right associativity).

Lemma propT_imp_conseq_L: forall p0 p1 q, p0 =>> p1 -> p1 =>> q -> p0 =>> q.
Proof.
move => p0 p1 q. case: p0 => [p0 hp0].
case: p1 => [p1 hp1]. case: q => [q hq]. 
move => h0 h1 tr0. simpl. move => h2. apply h1. simpl. 
by apply h0.
Qed.

Lemma propT_imp_conseq_R: forall p q0 q1,
 q0 =>> q1 -> p =>> q0 -> p =>> q1.
Proof.
move => p q0 q1. destruct p as [p hp]. 
destruct q0 as [q0 hq0]. destruct q1 as [q1 hq1]. 
move => h0 h1 tr0. simpl. move => h2. apply h0. simpl.
by apply h1.
Qed.

Lemma propT_imp_andT: forall p q0 q1,
 p =>> q0 -> p =>> q1 -> p =>> (q0 andT q1).
Proof.
move => [p hp] [q0 hq0] [q1 hq1] h0 h1 tr0 h2.
simpl in h2. simpl. split. 
- by apply h0.
- by apply h1.
Qed.

Definition ttT : trace -> Prop := fun tr => True.

Definition TtT : propT.
exists ttT. by move => tr0 h0 tr1 h1.
Defined.

Lemma propT_imp_refl: forall p, p =>> p.
Proof. by move => p tr0 h0. Qed.

Lemma satisfyT_cont: forall p0 p1, 
 p0 =>> p1 -> forall tr, satisfyT p0 tr -> satisfyT p1 tr.
Proof.
move => [f0 h0] [f1 h1] h2 tr h3. 
simpl. simpl in h3. exact: h2 _ h3.
Qed.

Lemma propT_imp_trans: forall p q r, p =>> q -> q =>> r -> p =>> r.
Proof. 
move => p q r h0 h1 tr0 h2.
apply (satisfyT_cont h1).
by apply (satisfyT_cont h0 h2).
Qed.

Lemma OrT_left: forall p1 p2, p1 =>> (p1 orT p2).
Proof.
move => p1 p2 tr h1. simpl. destruct p1 as [f1 hf1].
destruct p2 as [f2 hf2]. simpl. simpl in h1. by left.
Qed.

Lemma OrT_right: forall p1 p2, p2 =>> (p1 orT p2).
Proof.
move => p1 p2 tr h1. simpl. destruct p1 as [f1 hf1].
destruct p2 as [f2 hf2]. simpl. simpl in h1. by right. 
Qed.

Definition propA_imp (u1 u2: propA) : Prop := forall a, u1 a -> u2 a.

Local Infix "->>" := propA_imp (at level 60, right associativity).

Definition andA (u1 u2: propA) : propA := fun a => u1 a /\ u2 a.

Local Infix "andA" := andA (at level 60, right associativity).

Definition ttA : propA := fun a => True.
Definition ffA : propA := fun a => False.

Definition singletonT (u : propA) : trace -> Prop :=
fun tr => exists a, u a /\ bisim tr (Tnil a).

Lemma singletonT_setoidT : forall u, setoidT (singletonT u).
Proof. 
move => u. move => tr0 h0 tr1 h1. move: h0 => [a [h0 h2]]. 
invs h2. invs h1. exists a. split => //.
by apply bisim_refl.
Qed.

Lemma singletonT_cont : forall u v, u ->> v ->
 forall tr, singletonT u tr -> singletonT v tr.
Proof. 
move => u v huv tr0 h0. move: h0 => [a [h0 h1]]. invs h1. 
exists a. split; [ have := huv _ h0; apply | apply bisim_refl].
Qed.

Lemma singletonT_nil: forall u a, singletonT u (Tnil a) -> u a.
Proof. move => u st [st0 [h0 h1]]. by invs h1. Qed.

Lemma nil_singletonT : forall (u : propA) a, u a -> singletonT u (Tnil a).
Proof. move => u st h0. exists st. split; [ done | apply bisim_refl]. Qed.

Definition SingletonT (u: propA) : propT.
exists (singletonT u). 
exact: singletonT_setoidT.
Defined.

Notation "[| p |]" := (SingletonT p) (at level 80).

Lemma SingletonT_cont: forall u v, u ->> v -> [|u|] =>> [|v|].
Proof.
move => u v h0 tr0 h1. move: h1 => [st0 [h1 h2]]. 
invs h2. exists st0. split; [ apply (h0 _ h1) | apply bisim_refl].
Qed.

CoInductive followsT (p : trace -> Prop) : trace -> trace -> Prop :=
| followsT_nil: forall a tr, hd tr = a -> p tr -> followsT p (Tnil a) tr
| followsT_delay: forall a b tr tr',
  followsT p tr tr' -> followsT p (Tcons a b tr) (Tcons a b tr').

Lemma followsT_hd: forall p tr0 tr1, followsT p tr0 tr1 -> hd tr0 = hd tr1.
Proof. move => p tr0 tr1 h0. by invs h0. Qed.

Lemma followsT_setoidT : forall (p : trace -> Prop) (hp: forall tr0, p tr0 -> forall tr1, bisim tr0 tr1 -> p tr1), 
 forall tr0 tr1, followsT p tr0 tr1 ->
 forall tr2, bisim tr0 tr2 -> forall tr3, bisim tr1 tr3 -> 
 followsT p tr2 tr3.
Proof.
move => p hp.
cofix CIH.
move => tr0 tr1 h0 tr2 h1 tr3 h2. invs h0.
- invs h1. have h0 := bisim_hd h2. symmetry in h0. 
  by apply (followsT_nil h0 (hp _ H0 _ h2)).
- invs h2. invs h1.
  exact: (followsT_delay a b (CIH _ _ H _ H5 _ H4)).
Qed.

Lemma followsT_setoidT_L : forall p,
 forall tr0 tr1, followsT p tr0 tr1 ->
 forall tr2, bisim tr0 tr2 ->  followsT p tr2 tr1.
Proof.
move => p. cofix CIH. move =>  tr tr0 h0 tr1 h1. invs h0. 
- invs h1. apply followsT_nil. reflexivity. apply H0.
- invs h1. exact: (followsT_delay a b (CIH _ _ H _ H4)).
Qed.

Lemma followsT_setoidT_R : forall (p: trace -> Prop)
 (hp: forall tr0, p tr0 -> forall tr1, bisim tr0 tr1 -> p tr1), 
 forall tr tr0, followsT p tr tr0 ->
 forall tr1, bisim tr0 tr1 ->  followsT p tr tr1.
Proof. 
move => p hp. cofix CIH. 
move => tr tr0 h0 tr1 h1. invs h0.  
- apply followsT_nil; first by symmetry; apply (bisim_hd h1).
  exact: (hp _ H0 _ h1).
- invs h1. exact: (followsT_delay a b (CIH _ _  H _ H4)).
Qed.

Lemma followsT_cont : forall (p q : trace -> Prop),
(forall tr, p tr -> q tr) -> 
forall tr0 tr1, followsT p tr0 tr1 -> followsT q tr0 tr1.
Proof. 
move => p q hpq. cofix CIH. move => tr0 tr1 h0. invs h0. 
- apply followsT_nil => //. have := hpq _ H0; by apply.
- have := followsT_delay _ _ (CIH _ _ H). by apply. 
Qed.

Lemma followsT_singletonT: forall u tr0 tr1, 
 followsT (singletonT u) tr0 tr1 -> bisim tr0 tr1.
Proof.
move => u. cofix CIH. move => tr0 tr1 h0. invs h0. 
- move: H0 => [st0 [h0 h1]]. invs h1. by simpl; apply bisim_refl.
- exact: (bisim_cons a b (CIH _ _ H)).
Qed.

Lemma followsT_singleton_andA_L: forall u0 u1 tr0,
 followsT (singletonT (u0 andA u1)) tr0 tr0 ->
 followsT (singletonT u0) tr0 tr0.
Proof.
move => u0 u1. cofix CIH. case. 
- move => st0 h0. inversion h0. clear H1 H. simpl in H0.
  invs h0.
  move: H3 => [st1 [h1 h2]]. invs h2. move: h1 => [h1 h2].
  apply followsT_nil => //. exists st1. split; [done | apply bisim_refl].
- move => a b tr0 h0. invs h0. 
  exact: (followsT_delay a b (CIH _ H0)).
Qed.

Lemma followsT_singleton_andA_R: forall u0 u1 tr0,
 followsT (singletonT (u0 andA u1)) tr0 tr0 ->
 followsT (singletonT u1) tr0 tr0.
Proof. 
move => u0 u1. cofix CIH. case. 
- move => a h0. inversion h0. clear H1 H. simpl in H0.
  invs h0.
  move: H3 => [a' [h1 h2]]. invs h2. move: h1 => [h1 h2].
  apply followsT_nil => //. exists a'. split; [done | apply bisim_refl].
- move => a b tr0 h0. invs h0.
  exact: (followsT_delay a b (CIH _ H0)).
Qed.

Lemma singletonT_andA_followsT: forall u v tr,
 followsT (singletonT u) tr tr -> followsT (singletonT v) tr tr ->
 followsT (singletonT (u andA v)) tr tr.
Proof. 
move => u v. cofix CIH. move => tr h0 h1. inversion h0; subst.
- apply followsT_nil => //. exists a. split; last by apply bisim_refl. 
  clear H. inversion h1; subst. clear H1.
  have := singletonT_nil H0.
  have := singletonT_nil H2.
  by split.
- subst. invs h0. invs h1.
  exact: (followsT_delay a b (CIH _ H1 H2)).
Qed.

Definition appendT (p1 p2: trace -> Prop) : trace -> Prop :=
fun tr => exists tr', p1 tr' /\ followsT p2 tr' tr.

Local Infix "*+*" := appendT (at level 60, right associativity).

Lemma appendT_cont : forall (p0 p1 q0 q1 : trace -> Prop),
 (forall tr, p0 tr -> p1 tr) ->
 (forall tr, q0 tr -> q1 tr) ->
 forall tr, appendT p0 q0 tr -> appendT p1 q1 tr.
Proof.
move => p0 p1 q0 q1 hp hq tr [tr0 [h0 h1]].
exists tr0. split. have := hp _ h0; apply. clear h0. 
move: tr0 tr h1. cofix CIH.
move => tr0 tr1 h0. invs h0.
- apply followsT_nil => //. exact: (hq _ H0).
- exact: (followsT_delay a b (CIH _ _ H)).
Qed.

Lemma appendT_cont_L : forall (p0 p1 q: trace -> Prop),
 (forall tr, p0 tr -> p1 tr) ->
 forall tr, (appendT p0 q tr) -> (appendT p1 q tr).
Proof. 
move => p0 p1 q hp. move => tr [tr0 [h0 h1]]. 
exists tr0. split. have := hp _ h0; apply. apply h1. 
Qed.

Lemma appendT_cont_R: forall (p q0 q1: trace -> Prop),
(forall tr, q0 tr -> q1 tr) ->
forall tr, (appendT p q0 tr) -> (appendT p q1 tr).
Proof. 
move => p q0 q1 hq. have := (@appendT_cont p p _ _ _ hq). apply => //.
Qed.

Lemma appendT_setoidT: forall (p0 p1: trace -> Prop),
 setoidT p1 -> setoidT (appendT p0 p1).
Proof. 
move => p0 p1 hp1. move => tr0 h0 tr1 h1.
move: h0 => [tr2 [h0 h2]]. exists tr2. split; first by apply h0.
have := followsT_setoidT_R hp1 h2 h1. apply. 
Qed.

Lemma followsT_followsT: forall p q tr0 tr1 tr2, followsT p tr0 tr1 ->
 followsT q tr1 tr2 -> followsT (p *+* q) tr0 tr2. 
Proof.
move => p q. cofix CIH. case.
- move => a tr1 tr2 h0 h1. invs h0. have := followsT_hd h1 => h2. 
  apply followsT_nil => //. exists tr1. split => //. 
- move => a b tr0 tr1 tr2 h0 h1. invs h0. invs h1. apply followsT_delay. 
  exact: (CIH _ _ _ H3 H4).
Qed.

Lemma appendT_assoc_L : forall p1 p2 p3 tr,
 (appendT (appendT p1 p2) p3) tr -> appendT p1 (appendT p2 p3) tr.
Proof. 
move => p1 p2 p3 tr0 h1. move: h1 => [tr1 [h1 h2]]. move: h1 => [tr2 h1].
move: h1 => [h1 h3]. exists tr2. split; first done. clear h1.  
move: tr2 tr0 tr1 h2 h3. cofix CIH. move => tr0 tr1 tr2 h1 h2. invs h2. 
- have h2 := followsT_hd h1. symmetry in h2. have := followsT_nil h2.  apply. 
  exists tr2. by split. 
- invs h1. apply followsT_delay. exact: (CIH _ _ _ H4 H).
Qed.

Definition AppendT (p1 p2: propT) : propT.
destruct p1 as [f0 h0]. 
destruct p2 as [f1 h1]. exists (appendT f0 f1).
move => tr0 [tr1 [h2 h3]] tr2 h4. exists tr1.
split. apply h2. exact: (followsT_setoidT_R h1 h3 h4).
Defined.

Local Infix "***" := AppendT (at level 60, right associativity).

Lemma AppendT_assoc_L: forall p1 p2 p3, ((p1 *** p2) *** p3) =>> (p1 *** p2 *** p3).
Proof. 
move => p1 p2 p3 tr0 h1. destruct p1 as [f1 hf1]. destruct p2 as [f2 hf2]. 
destruct p3 as [f3 hf3]. simpl. simpl in h1. have := appendT_assoc_L h1. apply. 
Qed.

Lemma AppendT_cont : forall p1 p2 q1 q2, p1 =>> p2 -> q1 =>> q2 -> (p1 *** q1) =>> (p2 *** q2).
Proof.
move => p1 p2 q1 q2 h0 h1. destruct p1 as [p1 hp1]. destruct p2 as [p2 hp2].
destruct q1 as [q1 hq1]. destruct q2 as [q2 hq2].  move => tr0. simpl. 
move => h2. have := appendT_cont _ _ h2. apply. apply h0. apply h1. 
Qed.

Lemma AppendT_cont_L: forall p1 p2 q, p1 =>> p2 -> (p1 *** q) =>> (p2 *** q).
Proof.
move => p1 p2 q h0. destruct p1 as [p1 hp1]. destruct p2 as [p2 hp2].
destruct q as [q hq]. move => tr0. simpl.  
have := appendT_cont_L h0.  apply.
Qed.

Lemma AppendT_cont_R : forall q p1 p2, p1 =>> p2 -> (q *** p1) =>> (q *** p2).
Proof.
move => q p1 p2 h0. destruct p1 as [p1 hp1]. destruct p2 as [p2 hp2].
destruct q as [q hq]. move => tr0. simpl. move => h1.
have := (@appendT_cont q q p1 p2). apply. done. apply h0.
exact h1.
Qed.

Lemma AppendT_ttA: forall p, p =>> (p *** [| ttA |]).
Proof.
move => [f hp] tr0 h0. simpl in h0. simpl. exists tr0. 
split; first done. clear h0 hp. move: tr0. cofix hcoind. 
case. move => st0. apply followsT_nil => //.
by apply nil_singletonT. move => a b tr0.
exact: (followsT_delay _ _ (hcoind _)).
Qed.

Lemma AppendT_andA : forall u v, ([|u|] *** [|v|]) =>> [|u andA v|].
Proof.
move => u v tr0 [tr1 [h0 h1]]. destruct h0 as [st0 [hu h0]]. invs h0.
invs h1. destruct H1 as [a [hv h0]]. invs h0. simpl in hu. exists a.
by split; last apply bisim_refl.
Qed.

Lemma andA_AppendT: forall u v, [|u andA v|] =>> [|u|] *** [|v|]. 
Proof.
move => u v tr0 [a [[hu hv] h0]]. invs h0. exists (Tnil a).
split. exists a. by split; last apply bisim_refl. apply followsT_nil => //. 
exists a. by split; last apply bisim_refl.
Qed.

Lemma SingletonT_AppendT: forall v p, ([|v|] *** p) =>> p.
Proof.
move => v [p hp] tr0. simpl. move => [tr1 [h0 h1]]. 
destruct h0 as [a [h0 h2]]. invs h2. by invs h1.
Qed.

Lemma ttA_chop: forall p, ([|ttA|] *** p) =>> p.
Proof.
move => p.
exact: SingletonT_AppendT.
Qed.

Lemma ttA_chop_2: forall p, p =>> [|ttA|] *** p.
Proof.
move => [p hp] tr0; simpl => htr0. exists (Tnil (hd tr0)). split.
exists (hd tr0). by split; last apply bisim_refl.
apply followsT_nil => //.
Qed.

Lemma appendT_singletonT: forall p (hp: setoidT p) u tr, 
 appendT p (singletonT u) tr -> p tr.
Proof. 
move => p hp u tr0 h1. move: h1 => [tr1 [h1 h2]].
have h3 := followsT_singletonT h2.
exact: hp _ h1 _ h3.
Qed.

Lemma AppendT_Singleton: forall p v, (p *** [|v|]) =>> p.
Proof.
move => [p hp] v tr0. simpl. by apply appendT_singletonT.
Qed.

Lemma chop_ttA : forall p, (p *** [|ttA|]) =>> p.
Proof. move => p. by apply AppendT_Singleton. Qed.

Lemma chop_ttA_2: forall p, p =>> p *** [|ttA|].
Proof. move => [p hp] tr0; simpl => htr0. exists tr0; split; first done. 
clear hp htr0. move: tr0. cofix hcoind. case. 
- move => a. apply followsT_nil => //. exists a. by split; last apply bisim_refl. 
- move => a b tr0. exact: (followsT_delay _ _ (hcoind _)).
Qed.

Lemma TtT_idem_comp: (TtT *** TtT) =>> TtT.
Proof.
by move => tr _.
Qed.

Lemma FiniteT_idem_1: (FiniteT *** FiniteT) =>> FiniteT.
Proof.
move => tr0 [tr1 [h0 h1]]. move: tr1 h0 tr0 h1. induction 1. 
- move => tr0 h0. invs h0. done. 
- move => tr0 h1. invs h1. have h1 := IHh0 _ H3.
  have := finiteT_delay _ _ h1. by apply.
Qed.

Lemma FiniteT_idem_2: FiniteT =>> FiniteT *** FiniteT.
Proof.
move => tr0 h0. simpl. exists (Tnil (hd tr0)). split. 
apply finiteT_nil. apply followsT_nil => //.
Qed.

Lemma FiniteT_singleton: forall u, (FiniteT *** [|u|]) =>> FiniteT.
Proof. 
move => u tr h0. simpl in h0. simpl. 
move: h0 => [tr1 [h0 h1]]. 
have h2 := followsT_singletonT h1 => {h1}.
exact: (finiteT_setoidT h0 h2).
Qed.

Lemma InfiniteT_implies_chop : InfiniteT =>> (TtT *** [|ffA|]).
Proof.
move => tr0 [a b tr1] hinfiniteT. simpl. exists (Tcons a b tr1). split => //. clear tr0.  
move: a b tr1 hinfiniteT. cofix hcofix.
move => a b tr0 h. apply followsT_delay. inversion h. subst. apply hcofix. apply H.
Qed.

Lemma chop_implies_InfiniteT: (TtT *** [|ffA|]) =>> InfiniteT. 
Proof. 
move => tr0 [tr1 [_ h1]]. simpl. move: tr0 tr1 h1. cofix h0. move => tr0 tr1 h1. 
inversion h1; subst; clear h1. 
- destruct H0 as [st0 [h1 h2]]. inversion h1. 
- apply infiniteT_delay. apply (h0 _ _ H). 
Qed.

CoInductive midpointT (p0 p1: trace -> Prop) (tr0 tr1: trace) (h: followsT (appendT p0 p1) tr0 tr1) : trace -> Prop :=
| midpointT_nil :
   forall tr, tr0 = Tnil (hd tr1) -> p0 tr -> followsT p1 tr tr1 -> midpointT h tr
| midpointT_delay :
  forall (tr2 tr3 :trace) (h1: followsT (appendT p0 p1) tr2 tr3) (a : A) (b: B) tr',
  tr0 = Tcons a b tr2 -> tr1 = Tcons a b tr3 -> @midpointT p0 p1 tr2 tr3 h1 tr' ->
  midpointT h (Tcons a b tr').

Lemma midpointT_before: forall p0 p1 tr0 tr1 (h: followsT (appendT p0 p1) tr0 tr1) tr',
 midpointT h tr' -> followsT p0 tr0 tr'.
Proof.
cofix COINDHYP. dependent inversion h. move => {tr H0}.
- move: tr1 a tr0 h e a0 H. case.
  * move => a a0 tr0 h1 h2 h3 h4. simpl in h2.
    move => tr' hm.
    invs hm; last by inversion H.
    destruct h3. destruct H2. inversion h1.
    subst. apply followsT_nil; last by [].
    by inversion H1.
  * move => a b tr0 a0 tr1 h1 h2 h3 h4. simpl in h2.
    move => tr' hm.
    invs hm; last by inversion H.
    destruct h3. destruct H2. inversion h1.
    subst. apply followsT_nil; last by []. by inversion H1.
- subst.
  move => tr0 hm.
  destruct tr0; first by inversion hm.
  invs hm; subst; first by inversion H.
  invs H2; subst.
  invs H3; subst.
  apply followsT_delay.
  exact: (COINDHYP _ _ _ _ h1).
Qed.

Lemma midpointT_after: forall p0 p1 tr0 tr1 (h: followsT (appendT p0 p1) tr0 tr1) tr',
 midpointT h tr' -> followsT p1 tr' tr1.
Proof.
cofix COINDHYP. dependent inversion h. move => {tr H0}.
- move: tr1 a tr0 h e a0 H. case.
  * move => a a0 tr0 h1 h2 h3 h4. simpl in h2. move => tr' hm.
    invs hm; last by inversion H. destruct tr'; last by inversion H. destruct h3. destruct H2. inversion H3. subst.
    apply followsT_nil; last by []. by inversion H1.
  * move => a b tr0 a0 tr1 h1 h2 h3 h4. simpl in h2.
    move => tr' hm. by invs hm; last by inversion H.
- subst.
  move => tr0 hm.
 destruct tr0; first by inversion hm.
 invs hm; subst; first by inversion H.
 invs H2; subst.
 invs H3; subst.
 apply followsT_delay.
 exact: (COINDHYP _ _ _ _ h1).
Qed.

Definition followsT_dec : forall p tr0 tr1 (h: followsT p tr0 tr1),
 { tr & { a | tr0 = Tnil a /\ hd tr = a /\ p tr } } +
 { tr & { tr' & { a & { b | tr0 = Tcons a b tr /\ tr1 = Tcons a b tr' /\ followsT p tr tr'} } } }.
Proof.
intros.
destruct tr0.
- left; exists tr1; exists a. by inversion h; subst.
- destruct tr1.
  * left; exists (Tnil a); exists a. by inversion h; subst.
  * right; exists tr0; exists tr1; exists a; exists b; by inversion h; subst.
Defined.

End TraceProperties.

Infix "andT" := AndT (at level 60, right associativity).
Infix "orT" := OrT (at level 60, right associativity).
Infix "=>>" := propT_imp (at level 60, right associativity).
Infix "->>" := propA_imp (at level 60, right associativity).
Infix "andA" := andA (at level 60, right associativity).
Infix "*+*" := appendT (at level 60, right associativity).
Infix "***" := AppendT (at level 60, right associativity).
