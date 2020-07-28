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

Inductive finite: trace -> Prop :=
| finite_nil: forall a, finite (Tnil a)
| finite_delay: forall (a : A) (b : B) tr,
  finite tr -> finite (Tcons a b tr).

Lemma finite_setoidT : setoidT finite.
Proof.
induction 1.
- move => tr0 h0. invs h0. apply finite_nil. 
- move => tr0 h0. invs h0.
  exact (finite_delay a b (IHfinite _ H4)).
Qed.

Definition Finite : propT.
 exists (fun tr => finite tr). 
 move => tr0 h0 tr1 h1.
 exact: (finite_setoidT h0 h1).
Defined.

Lemma invert_finite_delay (a : A) (b : B) (tr : trace)
 (h : finite (Tcons a b tr)) : finite tr.
Proof.
 by inversion h.
Defined.

(* pattern for Fixpoint using finite *)
Fixpoint id_finite (tr : trace) (h : finite tr) {struct h} : trace :=
  match tr as tr' return (finite tr' -> trace) with
  | Tnil a => fun _ => Tnil a
  | Tcons a b tr => fun h => id_finite (invert_finite_delay h)
  end h.

(* pattern for inductive proofs using finite *)
Lemma id_finite_eq : forall tr (h h':finite tr),
 id_finite h = id_finite h'.
Proof.
refine (fix IH tr h {struct h} := _).
case: tr h => [a|a b tr] h.
- by dependent inversion h; move => h'; depelim h'; simpl; reflexivity.
- by dependent inversion h; move => h'; depelim h'; simpl; apply IH.
Qed.

CoInductive infinite : trace -> Prop :=
| infinite_delay: forall a b tr,
  infinite tr -> infinite (Tcons a b tr).

Lemma infinite_setoidT : setoidT infinite.
Proof.
cofix CIH. 
move => tr0 h0 tr1 h1. 
invs h0. invs h1.
exact: (infinite_delay a b (CIH _ H _ H4)).
Qed.

Definition Infinite : propT.
exists (fun tr => infinite tr). 
exact: infinite_setoidT.
Defined.

Definition satisfy (p:propT) : trace -> Prop := 
fun tr => let: exist f0 h0 := p in f0 tr.

Definition propT_and (p1 p2 : propT) : propT.
destruct p1 as [f0 h0]. 
destruct p2 as [f1 h1].
exists (fun tr => f0 tr /\ f1 tr). 
move => tr0 [h2 h3] tr1 h4. split.
- exact: (h0 _ h2 _ h4).
- exact: (h1 _ h3 _ h4).
Defined.

Local Infix "andT" := propT_and (at level 60, right associativity).

Definition propT_or (p1 p2: propT): propT.
destruct p1 as [f0 h0]. 
destruct p2 as [f1 h1].
exists (fun tr => f0 tr \/ f1 tr). 
move => tr0 [h2 | h2] tr1 h3.
- left. exact: h0 _ h2 _ h3.
- right. exact: h1 _ h2 _ h3.
Defined.

Local Infix "orT" := propT_or (at level 60, right associativity).

Definition propT_imp (p1 p2: propT) : Prop :=
forall tr, satisfy p1 tr -> satisfy p2 tr.

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

Definition ttt : trace -> Prop := fun tr => True.

Definition ttT : propT.
exists ttt. by move => tr0 h0 tr1 h1.
Defined. 

Lemma propT_imp_refl: forall p, p =>> p.
Proof. by move => p tr0 h0. Qed.

Lemma satisfy_cont: forall p0 p1, 
 p0 =>> p1 -> forall tr, satisfy p0 tr -> satisfy p1 tr.
Proof.
move => [f0 h0] [f1 h1] h2 tr h3. 
simpl. simpl in h3. exact: h2 _ h3.
Qed.

Lemma propT_imp_trans: forall p q r, p =>> q -> q =>> r -> p =>> r.
Proof. 
move => p q r h0 h1 tr0 h2.
apply (satisfy_cont h1).
by apply (satisfy_cont h0 h2).
Qed.

Lemma orT_left: forall p1 p2, p1 =>> (p1 orT p2).
Proof.
move => p1 p2 tr h1. simpl. destruct p1 as [f1 hf1].
destruct p2 as [f2 hf2]. simpl. simpl in h1. by left.
Qed.

Lemma orT_right: forall p1 p2, p2 =>> (p1 orT p2).
Proof.
move => p1 p2 tr h1. simpl. destruct p1 as [f1 hf1].
destruct p2 as [f2 hf2]. simpl. simpl in h1. by right. 
Qed.

Definition propA_imp (u1 u2: propA) := forall a, u1 a -> u2 a.

Local Infix "->>" := propA_imp (at level 60, right associativity).

Definition propA_and (u1 u2: propA) := fun a => u1 a /\ u2 a.

Local Infix "andA" := propA_and (at level 60, right associativity).

Definition ttA : propA := fun a => True.
Definition ffA : propA := fun a => False.

Definition singleton (u : propA) : trace -> Prop :=
fun tr => exists a, u a /\ bisim tr (Tnil a).

Lemma singleton_setoidT : forall u, setoidT (singleton u).
Proof. 
move => u. move => tr0 h0 tr1 h1. move: h0 => [a [h0 h2]]. 
invs h2. invs h1. exists a. split => //.
by apply bisim_refl.
Qed.

Lemma singleton_cont : forall u v, u ->> v ->
 forall tr, singleton u tr ->  singleton v tr.
Proof. 
move => u v huv tr0 h0. move: h0 => [a [h0 h1]]. invs h1. 
exists a. split; [ have := huv _ h0; apply | apply bisim_refl].
Qed.

Lemma singleton_nil: forall u a, singleton u (Tnil a) -> u a.
Proof. move => u st [st0 [h0 h1]]. by invs h1. Qed.

Lemma nil_singleton : forall (u : propA) a, u a -> singleton u (Tnil a).
Proof. move => u st h0. exists st. split; [ done | apply bisim_refl]. Qed.

Definition Singleton (u: propA) : propT.
exists (singleton u). 
move => tr0 [st0 [h0 h1]] tr1 h2. invs h1. invs h2.
exists st0. by split; [done | apply bisim_nil]. 
Defined.

Notation "[| p |]" := (Singleton p) (at level 80).

Lemma Singleton_cont: forall u v, u ->> v -> [|u|] =>> [|v|].
Proof.
move => u v h0 tr0 h1. move: h1 => [st0 [h1 h2]]. 
invs h2. exists st0. split; [ apply (h0 _ h1) | apply bisim_refl].
Qed.

CoInductive follows (p : trace -> Prop) : trace -> trace -> Prop :=
| follows_nil: forall a tr, hd tr = a -> p tr -> follows p (Tnil a) tr
| follows_delay: forall a b tr tr',
  follows p tr tr' -> follows p (Tcons a b tr) (Tcons a b tr').

Lemma follows_hd: forall p tr0 tr1, follows p tr0 tr1 -> hd tr0 = hd tr1.
Proof. move => p tr0 tr1 h0. by invs h0. Qed.

Lemma follows_setoidT : forall (p : trace -> Prop) (hp: forall tr0, p tr0 -> forall tr1, bisim tr0 tr1 -> p tr1), 
 forall tr0 tr1, follows p tr0 tr1 ->
 forall tr2, bisim tr0 tr2 -> forall tr3, bisim tr1 tr3 -> 
 follows p tr2 tr3.
Proof.
move => p hp.
cofix CIH.
move => tr0 tr1 h0 tr2 h1 tr3 h2. invs h0.
- invs h1. have h0 := bisim_hd h2. symmetry in h0. 
  by apply (follows_nil h0 (hp _ H0 _ h2)).
- invs h2. invs h1.
  exact: (follows_delay a b (CIH _ _ H _ H5 _ H4)).
Qed.

Lemma follows_setoidT_L : forall p,
 forall tr0 tr1, follows p tr0 tr1 ->
 forall tr2, bisim tr0 tr2 ->  follows p tr2 tr1.
Proof.
move => p. cofix CIH. move =>  tr tr0 h0 tr1 h1. invs h0. 
- invs h1. apply follows_nil. reflexivity. apply H0.
- invs h1. exact: (follows_delay a b (CIH _ _ H _ H4)).
Qed.

Lemma follows_setoidT_R : forall (p: trace -> Prop)
 (hp: forall tr0, p tr0 -> forall tr1, bisim tr0 tr1 -> p tr1), 
 forall tr tr0, follows p tr tr0 ->
 forall tr1, bisim tr0 tr1 ->  follows p tr tr1.
Proof. 
move => p hp. cofix CIH. 
move => tr tr0 h0 tr1 h1. invs h0.  
- apply follows_nil; first by symmetry; apply (bisim_hd h1).
  exact: (hp _ H0 _ h1).
- invs h1. exact: (follows_delay a b (CIH _ _  H _ H4)).
Qed.

Lemma follows_cont : forall (p q : trace -> Prop),
(forall tr, p tr -> q tr) -> 
forall tr0 tr1, follows p tr0 tr1 -> follows q tr0 tr1.
Proof. 
move => p q hpq. cofix CIH. move => tr0 tr1 h0. invs h0. 
- apply follows_nil => //. have := hpq _ H0; by apply.
- have := follows_delay _ _ (CIH _ _ H). by apply. 
Qed.

Lemma follows_singleton: forall u tr0 tr1, 
 follows (singleton u) tr0 tr1 -> bisim tr0 tr1.
Proof.
move => u. cofix CIH. move => tr0 tr1 h0. invs h0. 
- move: H0 => [st0 [h0 h1]]. invs h1. by simpl; apply bisim_refl.
- exact: (bisim_cons a b (CIH _ _ H)).
Qed.

Lemma follows_singleton_andA_L: forall u0 u1 tr0,
 follows (singleton (u0 andA u1)) tr0 tr0 ->
 follows (singleton u0) tr0 tr0.
Proof.
move => u0 u1. cofix CIH. case. 
- move => st0 h0. inversion h0. clear H1 H. simpl in H0.
  invs h0.
  move: H3 => [st1 [h1 h2]]. invs h2. move: h1 => [h1 h2].
  apply follows_nil => //. exists st1. split; [done | apply bisim_refl].
- move => a b tr0 h0. invs h0. 
  exact: (follows_delay a b (CIH _ H0)).
Qed.

Lemma follows_singleton_andA_R: forall u0 u1 tr0,
 follows (singleton (u0 andA u1)) tr0 tr0 ->
 follows (singleton u1) tr0 tr0.
Proof. 
move => u0 u1. cofix CIH. case. 
- move => a h0. inversion h0. clear H1 H. simpl in H0.
  invs h0.
  move: H3 => [a' [h1 h2]]. invs h2. move: h1 => [h1 h2].
  apply follows_nil => //. exists a'. split; [done | apply bisim_refl].
- move => a b tr0 h0. invs h0.
  exact: (follows_delay a b (CIH _ H0)).
Qed.

Lemma singleton_andA_follows: forall u v tr,
 follows (singleton u) tr tr -> follows (singleton v) tr tr ->
 follows (singleton (u andA v)) tr tr.
Proof. 
move => u v. cofix CIH. move => tr h0 h1. inversion h0; subst.
- apply follows_nil => //. exists a. split; last by apply bisim_refl. 
  clear H. inversion h1; subst. clear H1.
  have := singleton_nil H0.
  have := singleton_nil H2.
  by split.
- subst. invs h0. invs h1.
  exact: (follows_delay a b (CIH _ H1 H2)).
Qed.

Definition append (p1 p2: trace -> Prop) : trace -> Prop :=
fun tr => exists tr', p1 tr' /\ follows p2 tr' tr.

Local Infix "*+*" := append (at level 60, right associativity).

Lemma append_cont : forall (p0 p1 q0 q1 : trace -> Prop),
 (forall tr, p0 tr -> p1 tr) ->
 (forall tr, q0 tr -> q1 tr) ->
 forall tr, append p0 q0 tr -> append p1 q1 tr.
Proof.
move => p0 p1 q0 q1 hp hq tr [tr0 [h0 h1]].
exists tr0. split. have := hp _ h0; apply. clear h0. 
move: tr0 tr h1. cofix CIH.
move => tr0 tr1 h0. invs h0.
- apply follows_nil => //. exact: (hq _ H0).
- exact: (follows_delay a b (CIH _ _ H)).
Qed.

Lemma append_cont_L : forall (p0 p1 q: trace -> Prop),
 (forall tr, p0 tr -> p1 tr) ->
 forall tr, (append p0 q tr) -> (append p1 q tr).
Proof. 
move => p0 p1 q hp. move => tr [tr0 [h0 h1]]. 
exists tr0. split. have := hp _ h0; apply. apply h1. 
Qed.

Lemma append_cont_R: forall (p q0 q1: trace -> Prop),
(forall tr, q0 tr -> q1 tr) ->
forall tr, (append p q0 tr) -> (append p q1 tr).
Proof. 
move => p q0 q1 hq. have := (@append_cont p p _ _ _ hq). apply => //.
Qed.

Lemma append_setoidT: forall (p0 p1: trace -> Prop),
 setoidT p1 -> setoidT (append p0 p1).
Proof. 
move => p0 p1 hp1. move => tr0 h0 tr1 h1.
move: h0 => [tr2 [h0 h2]]. exists tr2. split; first by apply h0.
have := follows_setoidT_R hp1 h2 h1. apply. 
Qed.

Lemma follows_follows: forall p q tr0 tr1 tr2, follows p tr0 tr1 ->
 follows q tr1 tr2 -> follows (p *+* q) tr0 tr2. 
Proof.
move => p q. cofix CIH. case.
- move => a tr1 tr2 h0 h1. invs h0. have := follows_hd h1 => h2. 
  apply follows_nil => //. exists tr1. split => //. 
- move => a b tr0 tr1 tr2 h0 h1. invs h0. invs h1. apply follows_delay. 
  exact: (CIH _ _ _ H3 H4).
Qed.

Lemma append_assoc_L : forall p1 p2 p3 tr,
 (append (append p1 p2) p3) tr -> append p1 (append p2  p3) tr.
Proof. 
move => p1 p2 p3 tr0 h1. move: h1 => [tr1 [h1 h2]]. move: h1 => [tr2 h1].
move: h1 => [h1 h3]. exists tr2. split; first done. clear h1.  
move: tr2 tr0 tr1 h2 h3. cofix CIH. move => tr0 tr1 tr2 h1 h2. invs h2. 
- have h2 := follows_hd h1. symmetry in h2. have := follows_nil h2.  apply. 
  exists tr2. by split. 
- invs h1. apply follows_delay. exact: (CIH _ _ _ H4 H).
Qed.

Definition Append (p1 p2: propT) : propT.
destruct p1 as [f0 h0]. 
destruct p2 as [f1 h1]. exists (append f0 f1).  
move => tr0 [tr1 [h2 h3]] tr2 h4. exists tr1.
split. apply h2. exact: (follows_setoidT_R h1 h3 h4).
Defined.

Local Infix "***" := Append (at level 60, right associativity).

Lemma Append_assoc_L: forall p1 p2 p3, ((p1 *** p2) *** p3) =>> (p1 *** p2 *** p3).
Proof. 
move => p1 p2 p3 tr0 h1. destruct p1 as [f1 hf1]. destruct p2 as [f2 hf2]. 
destruct p3 as [f3 hf3]. simpl. simpl in h1. have := append_assoc_L h1. apply. 
Qed.

Lemma Append_cont : forall p1 p2 q1 q2, p1 =>> p2 -> q1 =>> q2 -> (p1 *** q1) =>> (p2 *** q2).
Proof.
move => p1 p2 q1 q2 h0 h1. destruct p1 as [p1 hp1]. destruct p2 as [p2 hp2].
destruct q1 as [q1 hq1]. destruct q2 as [q2 hq2].  move => tr0. simpl. 
move => h2. have := append_cont _ _ h2. apply. apply h0. apply h1. 
Qed.

Lemma Append_cont_L: forall p1 p2 q, p1 =>> p2 -> (p1 *** q) =>> (p2 *** q).
Proof.
move => p1 p2 q h0. destruct p1 as [p1 hp1]. destruct p2 as [p2 hp2].
destruct q as [q hq]. move => tr0. simpl.  
have := append_cont_L h0.  apply.
Qed.

Lemma Append_cont_R : forall q p1 p2, p1 =>> p2 -> (q *** p1) =>> (q *** p2).
Proof.
move => q p1 p2 h0. destruct p1 as [p1 hp1]. destruct p2 as [p2 hp2].
destruct q as [q hq]. move => tr0. simpl. move => h1.
have := (@append_cont q q p1 p2). apply. done. apply h0.
exact h1.
Qed.

Lemma Append_ttA: forall p, p =>> (p *** [| ttA |]).
Proof.
move => [f hp] tr0 h0. simpl in h0. simpl. exists tr0. 
split; first done. clear h0 hp. move: tr0. cofix hcoind. 
case. move => st0. apply follows_nil => //.
by apply nil_singleton. move => a b tr0.
exact: (follows_delay _ _ (hcoind _)).
Qed.

Lemma Append_andA : forall u v, ([|u|] *** [|v|]) =>> [|u andA v|].
Proof.
move => u v tr0 [tr1 [h0 h1]]. destruct h0 as [st0 [hu h0]]. invs h0.
invs h1. destruct H1 as [a [hv h0]]. invs h0. simpl in hu. exists a.
by split; last apply bisim_refl.
Qed.

Lemma andA_Append: forall u v, [|u andA v|] =>> [|u|] *** [|v|]. 
Proof.
move => u v tr0 [a [[hu hv] h0]]. invs h0. exists (Tnil a).
split. exists a. by split; last apply bisim_refl. apply follows_nil => //. 
exists a. by split; last apply bisim_refl.
Qed.

Lemma Singleton_Append: forall v p, ([|v|] *** p) =>> p.
Proof.
move => v [p hp] tr0. simpl. move => [tr1 [h0 h1]]. 
destruct h0 as [a [h0 h2]]. invs h2. by invs h1.
Qed.

Lemma ttA_Chop: forall p, ([|ttA|] *** p) =>> p.
Proof.
move => p.
by apply Singleton_Append.
Qed.

Lemma ttS_Chop_2: forall p, p =>> [|ttA|] *** p.
Proof.
move => [p hp] tr0; simpl => htr0. exists (Tnil (hd tr0)). split.
exists (hd tr0). by split; last apply bisim_refl.
apply follows_nil => //.
Qed.

Lemma append_singleton: forall p (hp: setoidT p) u tr, 
 append p (singleton u) tr -> p tr.
Proof. 
move => p hp u tr0 h1. move: h1 => [tr1 [h1 h2]].
have h3 := follows_singleton h2. 
have := hp _ h1 _ h3. apply.
Qed.

Lemma Append_Singleton: forall p v, (p *** [|v|]) =>> p.
Proof.
move => [p hp] v tr0. simpl. by apply append_singleton.
Qed.

Lemma chop_ttA : forall p, (p *** [|ttA|]) =>> p.
Proof. move => p. by apply Append_Singleton. Qed.

Lemma chop_ttA_2: forall p, p =>> p *** [|ttA|].
Proof. move => [p hp] tr0; simpl => htr0. exists tr0; split; first done. 
clear hp htr0. move: tr0. cofix hcoind. case. 
- move => a. apply follows_nil => //. exists a. by split; last apply bisim_refl. 
- move => a b tr0. exact: (follows_delay _ _ (hcoind _)).
Qed.

Lemma ttT_idem_comp: (ttT *** ttT) =>> ttT.
Proof.
by move => tr _.
Qed.

Lemma Finite_idem_1: (Finite *** Finite) =>> Finite.
Proof.
move => tr0 [tr1 [h0 h1]]. move: tr1 h0 tr0 h1. induction 1. 
- move => tr0 h0. invs h0. done. 
- move => tr0 h1. invs h1. have h1 := IHh0 _ H3.
  have := finite_delay _ _ h1. by apply.
Qed.

Lemma Finite_idem_2: Finite =>> Finite *** Finite.
Proof.
move => tr0 h0. simpl. exists (Tnil (hd tr0)). split. 
apply finite_nil. apply follows_nil => //.
Qed.

Lemma Finite_singleton: forall u, (Finite *** [|u|]) =>> Finite. 
Proof. 
move => u tr h0. simpl in h0. simpl. 
move: h0 => [tr1 [h0 h1]]. 
have h2 := follows_singleton h1 => {h1}.
have := finite_setoidT h0 h2. by apply. 
Qed.

Lemma infinite_implies_chop : Infinite =>> (ttT *** [|ffA|]).
Proof.
move => tr0 [a b tr1] hinfinite. simpl. exists (Tcons a b tr1). split => //. clear tr0.  
move: a b tr1 hinfinite. cofix hcofix. 
* move => a b tr0 h. apply follows_delay. inversion h. subst. apply hcofix. apply H. 
Qed.

Lemma chop_implies_infinite: (ttT *** [|ffA|]) =>> Infinite. 
Proof. 
move => tr0 [tr1 [_ h1]]. simpl. move: tr0 tr1 h1. cofix h0. move => tr0 tr1 h1. 
inversion h1; subst; clear h1. 
- destruct H0 as [st0 [h1 h2]]. inversion h1. 
- apply infinite_delay. apply (h0 _ _ H). 
Qed.

End TraceProperties.

Infix "andT" := propT_and (at level 60, right associativity).
Infix "orT" := propT_or (at level 60, right associativity).
Infix "=>>" := propT_imp (at level 60, right associativity).
Infix "->>" := propA_imp (at level 60, right associativity).
Infix "andA" := propA_and (at level 60, right associativity).
Infix "*+*" := append (at level 60, right associativity).
Infix "***" := Append (at level 60, right associativity).
