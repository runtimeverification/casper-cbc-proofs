
Require Import List Streams Coq.Arith.Lt Coq.Arith.Plus.
Import ListNotations.

From CasperCBC
     Require Import Lib.ListExtras.

Definition stream_app
  {A : Type}
  (prefix : list A)
  (suffix : Stream A)
  : Stream A
  :=
  fold_right (@Cons A) suffix prefix.


Definition stream_app_cons {A}
  (a : A)
  (l : Stream A)
  : stream_app [a] l = Cons a l
  := eq_refl.

Lemma stream_app_assoc
  {A : Type}
  (l m : list A)
  (n : Stream A)
  : stream_app l (stream_app m n) = stream_app (l ++ m) n.
Proof.
  induction l; try reflexivity.
  simpl. apply f_equal. assumption.
Qed.

Lemma stream_app_f_equal
  {A : Type}
  (l1 l2 : list A)
  (s1 s2 : Stream A)
  (Hl : l1 = l2)
  (Hs : EqSt s1 s2)
  : EqSt (stream_app l1 s1) (stream_app l2 s2)
  .
Proof.
  subst. induction l2; try assumption.
  simpl. constructor; try reflexivity. assumption.
Qed.

Lemma stream_app_inj_l
  {A : Type}
  (l1 l2 : list A)
  (s : Stream A)
  (Heq : stream_app l1 s = stream_app l2 s)
  (Heq_len : length l1 = length l2)
  : l1 = l2.
Proof.
  generalize dependent l2.
  induction l1; intros; destruct l2; try reflexivity; try inversion Heq_len.
  inversion Heq.
  f_equal.
  specialize (IHl1 l2 H2 H0).
  assumption.
Qed.

Fixpoint stream_prefix
  {A : Type}
  (l : Stream A)
  (n : nat)
  : list A
  := match n,l with
  | 0,_ => []
  | S n, Cons a l => a :: stream_prefix l n
  end.

Lemma stream_prefix_map
  {A B : Type}
  (f : A -> B)
  (l : Stream A)
  (n : nat)
  : List.map f (stream_prefix l n) = stream_prefix (Streams.map f l) n
  .
Proof.
  generalize dependent l. induction n; intros [a l]; try reflexivity.
  simpl.
  f_equal.
  apply IHn.
Qed.

Lemma stream_prefix_length
  {A : Type}
  (l : Stream A)
  (n : nat)
  : length (stream_prefix l n) = n
  .
Proof.
  generalize dependent l. induction n; intros [a l]; try reflexivity.
  simpl in *. f_equal.
  apply IHn.
Qed.

Definition stream_suffix
  {A : Type}
  (l : Stream A)
  (n : nat)
  : Stream A
  := Str_nth_tl n l.

Lemma stream_suffix_S
  {A : Type}
  (l : Stream A)
  (n : nat)
  : stream_suffix l n = Cons (Str_nth n l) (stream_suffix l (S n))
  .
Proof.
  generalize dependent l. induction n; intros.
  - destruct l; reflexivity.
  - specialize (IHn (tl l)); simpl in IHn.
    simpl. assumption.
Qed.
 
Lemma stream_prefix_suffix
  {A : Type}
  (l : Stream A)
  (n : nat)
  : stream_app (stream_prefix l n) (stream_suffix l n) = l
  .
Proof.
  generalize dependent l. unfold stream_suffix.
  induction n; try reflexivity; intros [a l]; simpl.
  f_equal. apply IHn.
Qed.

Lemma stream_prefix_prefix
  {A : Type}
  (l : Stream A)
  (n1 n2 : nat)
  (Hn: n1 <= n2)
  : list_prefix (stream_prefix l n2) n1 = stream_prefix l n1
  .
Proof.
  generalize dependent n2.
  generalize dependent l.
  induction n1; intros [a l]; intros [|n2] Hn; try reflexivity.
  - inversion Hn.
  - simpl. f_equal. apply IHn1. apply le_S_n.  assumption.
Qed.

Definition stream_segment
  {A : Type}
  (l : Stream A)
  (n1 n2 : nat)
  : list A
  := list_suffix (stream_prefix l n2) n1
  .

Lemma stream_prefix_segment_suffix
  {A : Type}
  (l : Stream A)
  (n1 n2 : nat)
  (Hn : n1 <= n2)
  : EqSt
   (stream_app
   ((stream_prefix l n1)
     ++
    (stream_segment l n1 n2)
   )
    (stream_suffix l n2)
    )
    l
  .
Proof.
  rewrite <- (stream_prefix_suffix l n2) at 4.
  apply stream_app_f_equal; try apply EqSt_reflex.
  unfold stream_segment.
  rewrite <- (list_prefix_suffix (stream_prefix l n2) n1) at 2.
  f_equal.
  symmetry.
  apply stream_prefix_prefix.
  assumption.
Qed.

Definition monotone_nat_stream :=
  {s : Stream nat | forall n1 n2 : nat, n1 < n2 -> Str_nth n1 s < Str_nth n2 s}.

Definition filtering_subsequence
  {A : Type}
  (P : A -> Prop)
  (s : Stream A)
  (ss : monotone_nat_stream)
  (ns := proj1_sig ss)
  := forall n : nat, P (Str_nth n s) <-> exists k : nat, Str_nth k ns = n.

Lemma filtering_subsequence_witness
  {A : Type}
  (P : A -> Prop)
  (s : Stream A)
  (ss : monotone_nat_stream)
  (Hfs : filtering_subsequence P s ss)
  (ns := proj1_sig ss)
  (k : nat)
  : P (Str_nth (Str_nth k ns) s).
Proof.
  specialize (Hfs (Str_nth k ns)).
  apply Hfs. exists k. reflexivity.
Qed.

Definition stream_subsequence
  {A : Type}
  (s : Stream A)
  (ss : monotone_nat_stream)
  (ns := proj1_sig ss)
  : Stream A
  := Streams.map (fun k => Str_nth k s) ns.

Lemma all_ForAll_hd
  {A : Type}
  (P : A -> Prop)
  (s : Stream A)
  (Hall : forall n : nat, P (Str_nth n s))
  : ForAll (fun str => P (hd str)) s.
Proof.
  apply ForAll_coind with (fun s : Stream A => forall n : nat, P (Str_nth n s))
  ; intros.
  - specialize (H 0). assumption.
  - specialize (H (S n)). 
    assumption.
  - apply Hall.
Qed.

Lemma stream_filter_Forall
  {A : Type}
  (P : A -> Prop)
  (s : Stream A)
  (ss : monotone_nat_stream)
  (s' := stream_subsequence s ss)
  (Hfs : filtering_subsequence P s ss)
  : ForAll (fun str => P (hd str)) s'.
Proof.
  apply all_ForAll_hd.
  intro n.
  unfold s'.
  unfold stream_subsequence.
  rewrite Str_nth_map.
  apply filtering_subsequence_witness. assumption.
Qed.

CoFixpoint stream_annotate
  {A : Type}
  (P : A -> Prop)
  (s : Stream A)
  (Hs : ForAll (fun str => P (hd str)) s)
  : Stream (sig P) :=
  match Hs with 
  | HereAndFurther _ H Hs'
    => Cons (exist _ (hd s) H) (stream_annotate P (tl s) Hs')
  end.

Lemma stream_prefix_Forall
  {A : Type}
  (P : A -> Prop)
  (s : Stream A)
  (Hs : ForAll (fun str => P (hd str)) s)
  : forall n : nat, Forall P (stream_prefix s n)
  .
Proof.
  intros n. generalize dependent s.
  induction n; intros.
  - constructor.
  - destruct s as (a,s).
    simpl.
    inversion Hs.
    constructor; try assumption.
    apply IHn.
    assumption.
Qed.

Lemma stream_prefix_Forall_rev
  {A : Type}
  (P : A -> Prop)
  (s : Stream A)
  (Hpref: forall n : nat, Forall P (stream_prefix s n))
  : ForAll (fun str => P (hd str)) s
  .
Proof.
  generalize dependent s.
  cofix H.
  intros (a, s) Hpref.
  constructor.
  - specialize (Hpref 1).
    inversion Hpref.
    assumption.
  - apply H.
    intro n.
    specialize (Hpref (S n)).
    inversion Hpref.
    assumption.
Qed.

Lemma stream_prefix_annotate
  {A : Type}
  (P : A -> Prop)
  (s : Stream A)
  (Hs : ForAll (fun str => P (hd str)) s)
  (n : nat)
  : exists Hs', stream_prefix (stream_annotate P s Hs) n
  = list_annotate P (stream_prefix s n) Hs'
  .
Proof.
  generalize dependent s.
  induction n.
  - intros. simpl. exists (Forall_nil P). reflexivity.
  - intros (a, s) (H, H0).
    specialize (IHn s H0).
    destruct IHn as [Hs' Heq]. 
    simpl.
    rewrite Heq.
    exists (@Forall_cons A P _ _ H Hs').
    simpl.
    f_equal.
Qed.
 
Lemma stream_annotate_proj
  {A : Type}
  (P : A -> Prop)
  : forall
    (s : Stream A)
    (Hs : ForAll (fun str => P (hd str)) s)
    , EqSt s (map (@proj1_sig _ _) (stream_annotate P s Hs)).
Proof.
  cofix cf.
  intros (x, s) Hs.
  constructor.
  - simpl.
    destruct Hs.
    trivial.
  - destruct Hs.
    simpl.
    apply cf.
Qed.

Lemma stream_prefix_nth
  {A : Type}
  (s : Stream A)
  (n : nat)
  (i : nat)
  (Hi : i < n)  
  : nth_error (stream_prefix s n) i = Some (Str_nth i s)
  .
Proof.
  generalize dependent n. generalize dependent s.
  induction i; intros [a s] [|n] Hi; try reflexivity.
  - inversion Hi.
  - inversion Hi.
  - simpl.
    apply lt_S_n in Hi.
    specialize (IHi s n Hi).
    rewrite IHi.
    reflexivity.
Qed.

Lemma stream_prefix_succ
  {A : Type}
  (s : Stream A)
  (n : nat)
  : stream_prefix s (S n) = stream_prefix s n ++ [Str_nth n s].
Proof.
  specialize (stream_prefix_suffix s n).
  rewrite stream_suffix_S. 
  rewrite <- stream_app_cons.
  rewrite stream_app_assoc.
  intros Hn.
  specialize (stream_prefix_suffix s (S n)); intros Hsn.
  rewrite <- Hsn in Hn at 4; clear Hsn.
  specialize
    (stream_app_inj_l
      (stream_prefix s n ++ [Str_nth n s])
      (stream_prefix s (S n))
      (stream_suffix s (S n))
      Hn
    ); intros Hinj.
    symmetry.
    apply Hinj.
    rewrite app_length.
    repeat (rewrite stream_prefix_length).
    rewrite plus_comm.
    reflexivity.
Qed.

Lemma stream_prefix_nth_last
  {A : Type}
  (l : Stream A)
  (n : nat)
  (_last : A)
  : last (stream_prefix l (S n)) _last = Str_nth n l
  .
Proof.
  specialize (nth_error_last (stream_prefix l (S n)) n); intro Hlast.
  specialize (stream_prefix_length l (S n)); intro Hpref_len.
  symmetry in Hpref_len.
  specialize (Hlast Hpref_len _last).
  specialize (stream_prefix_nth l (S n) n); intro Hnth.
  assert (Hlt : n < S n) by constructor.
  specialize (Hnth Hlt).
  rewrite Hnth in Hlast.
  simpl.
  inversion Hlast.
  reflexivity.
Qed.

Lemma stream_segment_nth
  {A : Type}
  (l : Stream A)
  (n1 n2 : nat)
  (Hn : n1 <= n2)
  (i : nat)
  (Hi1 : n1 <= i)
  (Hi2 : i < n2)
  : nth_error (stream_segment l n1 n2) (i - n1) = Some (Str_nth i l).
Proof.
  unfold stream_segment.
  rewrite list_suffix_nth; try assumption.
  apply stream_prefix_nth.
  assumption.
Qed.

Lemma str_map_tl
  {A B : Type}
  (f : A -> B)
  (s : Stream A)
  : EqSt (tl (map f s)) (map f (tl s))
  .
Proof.
  generalize dependent s.
  cofix IH.
  intros (a, s).
  constructor; try reflexivity.
  simpl.
  apply IH.
Qed.

Lemma str_map_cons
  {A B : Type}
  (f : A -> B)
  (s : Stream A)
  : EqSt (map f s) (Cons (f (hd s)) (map f (tl s)))
  .
Proof.
  destruct s as  (a,s).
  constructor; try reflexivity.
  simpl.
  apply EqSt_reflex.
Qed.

Lemma stream_prefix_EqSt
  {A : Type}
  (s1 s2 : Stream A)
  (Heq : EqSt s1 s2)
  : forall n : nat, stream_prefix s1 n = stream_prefix s2 n .
Proof.
  intro n.
  generalize dependent s2. generalize dependent s1.
  induction n; try reflexivity; intros (a1, s1) (a2,s2) Heq.
  inversion Heq. simpl in H; subst.
  simpl.
  f_equal.
  apply IHn.
  assumption.
Qed.

Lemma EqSt_stream_prefix
  {A : Type}
  (s1 s2 : Stream A)
  (Hpref : forall n : nat, stream_prefix s1 n = stream_prefix s2 n)
  : EqSt s1 s2
  .
Proof.
  apply ntheq_eqst.
  intro n.
  assert (Hlt : n < S n) by constructor.
  assert (HSome : Some (Str_nth n s1) = Some (Str_nth n s2)).
  { 
    rewrite <- (stream_prefix_nth  s1 (S n) n Hlt).
    rewrite <- (stream_prefix_nth  s2 (S n) n Hlt).
    specialize (Hpref (S n)).
    rewrite Hpref.
    reflexivity.
  }
  inversion HSome. reflexivity.
Qed.
