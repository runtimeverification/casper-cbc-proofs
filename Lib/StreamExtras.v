From Coq Require Import List Streams Compare_dec Lia.
Import ListNotations.

From CasperCBC Require Import Lib.ListExtras Preamble.

(** * Stream utility definitions and lemmas *)

Lemma recons
  {A : Type}
  (s : Stream A)
  : Cons (hd s) (tl s) = s.
Proof.
  case s.  reflexivity.
Qed.

Lemma map_Cons
  {A B : Type}
  (f : A -> B)
  (x : A)
  (s : Stream A)
  : map f (Cons x s) = Cons (f x) (map f s).
Proof.
  intros.
  rewrite <- (recons (map f (Cons x s))). reflexivity.
Qed.

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
  : EqSt (stream_app l1 s1) (stream_app l2 s2).
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

Lemma stream_prefix_nth
  {A : Type}
  (s : Stream A)
  (n : nat)
  (i : nat)
  (Hi : i < n)
  : nth_error (stream_prefix s n) i = Some (Str_nth i s).
Proof.
  generalize dependent n. generalize dependent s.
  induction i; intros [a s] [|n] Hi; try reflexivity.
  - inversion Hi.
  - inversion Hi.
  - simpl.
    assert (Hi': i < n) by lia.
    specialize (IHi s n Hi').
    rewrite IHi.
    reflexivity.
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
  : EqSt s1 s2.
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

Lemma stream_prefix_in
  {A : Type}
  (l : Stream A)
  (n : nat)
  (a : A)
  (Hin : In a (stream_prefix l n))
  : exists k : nat, k < n /\ Str_nth k l = a.
Proof.
  generalize dependent a. generalize dependent l.
  induction n.
  - simpl. intros. contradiction.
  - intros (b, l) a; simpl; intro Hin.
    destruct Hin as [Heq | Hin]; subst.
    + exists 0. split; try reflexivity.
      lia.
    + specialize (IHn l a Hin).
      destruct IHn as [k [Hlt Heq]].
      exists (S k).
      split; try assumption.
      lia.
Qed.

Lemma stream_prefix_app_l
  {A : Type}
  (l : list A)
  (s : Stream A)
  (n : nat)
  (Hle : n <= length l)
  : stream_prefix (stream_app l s) n = list_prefix l n.
Proof.
  generalize dependent n.
  induction l; intros [|n] Hle; try reflexivity.
  - inversion Hle.
  - simpl in Hle.
    simpl. f_equal.
    apply IHl.
    lia.
Qed.

Lemma stream_prefix_app_r
  {A : Type}
  (l : list A)
  (s : Stream A)
  (n : nat)
  (Hge : n >= length l)
  : stream_prefix (stream_app l s) n = l ++ stream_prefix s (n - length l).
Proof.
  generalize dependent l.
  generalize dependent s.
  induction n.
  - intros. simpl.
    destruct l as [|a l]; try reflexivity.
    simpl in Hge. inversion Hge.
  - intros s [| a l] Hge; try reflexivity.
    simpl. f_equal.
    apply IHn.
    simpl in Hge.
    lia.
Qed.

Lemma stream_prefix_map
  {A B : Type}
  (f : A -> B)
  (l : Stream A)
  (n : nat)
  : List.map f (stream_prefix l n) = stream_prefix (Streams.map f l) n.
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
  : length (stream_prefix l n) = n.
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
  : stream_suffix l n = Cons (Str_nth n l) (stream_suffix l (S n)).
Proof.
  generalize dependent l. induction n; intros.
  - destruct l; reflexivity.
  - specialize (IHn (tl l)); simpl in IHn.
    simpl. assumption.
Qed.

Lemma stream_suffix_nth
  {A : Type}
  (s : Stream A)
  (n : nat)
  (i : nat)
  : Str_nth i (stream_suffix s n) = Str_nth (i + n) s.
Proof.
  apply Str_nth_plus.
Qed.

Lemma stream_prefix_suffix
  {A : Type}
  (l : Stream A)
  (n : nat)
  : stream_app (stream_prefix l n) (stream_suffix l n) = l.
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
  : list_prefix (stream_prefix l n2) n1 = stream_prefix l n1.
Proof.
  generalize dependent n2.
  generalize dependent l.
  induction n1; intros [a l]; intros [|n2] Hn; try reflexivity.
  - inversion Hn.
  - simpl. f_equal. apply IHn1. lia.
Qed.

Definition stream_segment
  {A : Type}
  (l : Stream A)
  (n1 n2 : nat)
  : list A
  := list_suffix (stream_prefix l n2) n1.

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

Definition stream_segment_alt
  {A : Type}
  (l : Stream A)
  (n1 n2 : nat)
  : list A
  := stream_prefix (stream_suffix l n1) (n2 - n1).

Lemma stream_segment_alt_iff
  {A : Type}
  (l : Stream A)
  (n1 n2 : nat)
  : stream_segment l n1 n2 = stream_segment_alt l n1 n2.
Proof.
  apply nth_error_eq.
  intro k.
  unfold stream_segment_alt. unfold stream_segment.
  destruct (le_lt_dec (n2 - n1) k).
  - specialize (nth_error_None (list_suffix (stream_prefix l n2) n1) k); intros [_ H].
    specialize (nth_error_None (stream_prefix (stream_suffix l n1) (n2 - n1)) k); intros [_ H_alt].
    rewrite H, H_alt; try reflexivity.
    + rewrite stream_prefix_length; assumption.
    + rewrite list_suffix_length. rewrite stream_prefix_length. assumption.
  - rewrite stream_prefix_nth; try assumption.
    rewrite stream_suffix_nth.
    assert (Hle : n1 <= n1 + k) by lia.
    specialize (list_suffix_nth (stream_prefix l n2) n1 (n1 + k) Hle)
    ; intro Heq.
    clear Hle.
    assert (Hs: n1 + k - n1 = k) by lia.
    rewrite Hs in Heq.
    rewrite Heq.
    rewrite stream_prefix_nth.
    + rewrite Plus.plus_comm; reflexivity.
    + lia.
Qed.

Lemma stream_prefix_segment
  {A : Type}
  (l : Stream A)
  (n1 n2 : nat)
  (Hn : n1 <= n2)
  : stream_prefix l n1 ++ stream_segment l n1 n2 = stream_prefix l n2.
Proof.
  unfold stream_segment.
  rewrite <- (list_prefix_suffix (stream_prefix l n2) n1) at 2.
  f_equal.
  symmetry.
  apply stream_prefix_prefix.
  assumption.
Qed.

Lemma stream_prefix_segment_suffix
  {A : Type}
  (l : Stream A)
  (n1 n2 : nat)
  (Hn : n1 <= n2)
  : stream_app
      ((stream_prefix l n1)
        ++
       (stream_segment l n1 n2)
      )
      (stream_suffix l n2)
  = l.
Proof.
  rewrite <- (stream_prefix_suffix l n2) at 4.
  f_equal.
  apply stream_prefix_segment.
  assumption.
Qed.

Lemma stream_segment_app
  {A : Type}
  (l : Stream A)
  (n1 n2 n3 : nat)
  (H12 : n1 <= n2)
  (H23 : n2 <= n3)
  : stream_segment l n1 n2 ++ stream_segment l n2 n3 = stream_segment l n1 n3.
Proof.
  assert (Hle : n1 <= n3) by lia.
  specialize (stream_prefix_segment_suffix l n1 n3 Hle); intro Hl1.
  specialize (stream_prefix_segment_suffix l n2 n3 H23); intro Hl2.
  rewrite <- Hl2 in Hl1 at 4. clear Hl2.
  apply stream_app_inj_l in Hl1.
  - specialize (list_prefix_suffix (stream_prefix l n2) n1); intro Hl2.
    specialize (stream_prefix_prefix l n1 n2 H12); intro Hl3.
    rewrite Hl3 in Hl2.
    rewrite <- Hl2 in Hl1.
    rewrite <- app_assoc in Hl1.
    apply app_inv_head in Hl1.
    symmetry.
    assumption.
  - repeat rewrite app_length.
    unfold stream_segment.
    repeat rewrite list_suffix_length.
    repeat rewrite stream_prefix_length.
    lia.
Qed.

Definition monotone_nat_stream_prop
  (s : Stream nat)
  := forall n1 n2 : nat, n1 < n2 -> Str_nth n1 s < Str_nth n2 s.

Definition monotone_nat_stream :=
  {s : Stream nat | monotone_nat_stream_prop s}.

Lemma monotone_nat_stream_tl
  (s : Stream nat)
  (Hs : monotone_nat_stream_prop s)
  : monotone_nat_stream_prop (tl s).
Proof.
  intros n1 n2 Hlt.
  specialize (Hs (S n1) (S n2)).
  apply Hs.
  lia.
Qed.

Definition nat_sequence_suffix
  (s : Stream nat)
  :=
  Streams.map (fun i => i - (S (hd s))) (tl s).

Lemma monotone_nat_prop_suffix
  (ss : monotone_nat_stream)
  : monotone_nat_stream_prop (nat_sequence_suffix (proj1_sig ss)).
Proof.
  destruct ss as [s Hs].
  intros n1 n2 Hlt.
  unfold nat_sequence_suffix.
  destruct s as (a, s).
  simpl.
  repeat rewrite Str_nth_map.
  assert (Hlt1 : 0 < S n1) by lia.
  pose proof (Hs 0 (S n1) Hlt1) as Ha1.
  unfold Str_nth in Ha1.
  simpl in Ha1.
  assert (Hlt2 : 0 < S n2) by lia.
  pose proof (Hs 0 (S n2) Hlt2) as Ha2.
  unfold Str_nth in Ha2.
  simpl in Ha2.
  assert (HltS : S n1 < S n2) by lia.
  specialize (Hs (S n1) (S n2) HltS).
  unfold Str_nth in Hs.
  simpl in Hs.
  unfold Str_nth.
  lia.
Qed.

Definition monotone_nat_stream_suffix
  (ss : monotone_nat_stream)
  : monotone_nat_stream
  :=
  exist
    monotone_nat_stream_prop
    (nat_sequence_suffix (proj1_sig ss))
    (monotone_nat_prop_suffix ss).

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

Lemma filtering_subsequence_suffix
  {A : Type}
  (P : A -> Prop)
  (ss : Stream A)
  (kss : monotone_nat_stream)
  (ks := proj1_sig kss)
  (Hfs : filtering_subsequence P ss kss)
  (kss' := monotone_nat_stream_suffix kss)
  : filtering_subsequence
    P (stream_suffix ss (S (hd ks))) kss' .
Proof.
  intro n. simpl.
  rewrite stream_suffix_nth.
  specialize (Hfs (S (n + hd ks))).
  split; intro H.
  - apply proj1 in Hfs. specialize (Hfs H).
    destruct Hfs as [k0 Heq].
    unfold ks in *; clear ks.
    destruct kss as [(k, ks) Hseq]; simpl in *.
    destruct k0.
    + elim (Plus.succ_plus_discr k n).
      assumption.
    + exists k0. unfold nat_sequence_suffix.
      rewrite Str_nth_map .
      simpl.
      unfold Str_nth in Heq; simpl in Heq.
      assert (Hlt0 : 0 < (S k0)) by lia.
      clear kss'.
      specialize (Hseq 0 (S k0) Hlt0).
      unfold Str_nth in Hseq; simpl in Hseq.
      unfold Str_nth.
      lia.
  - apply proj2 in Hfs. apply Hfs. clear Hfs.
    destruct H as [k Heq].
    exists (S k).
    unfold nat_sequence_suffix in Heq.
    rewrite Str_nth_map in Heq.
    unfold ks in *; clear ks.
    destruct kss as [(k0, ks) Hseq]; simpl in *.
    assert (Hlt : 0 < (S k)) by lia.
    clear kss'.
    specialize (Hseq 0 (S k) Hlt).
    unfold Str_nth in *; simpl in *.
    lia.
Qed.

Definition stream_subsequence
  {A : Type}
  (s : Stream A)
  (ss : monotone_nat_stream)
  (ns := proj1_sig ss)
  : Stream A
  := Streams.map (fun k => Str_nth k s) ns.

Lemma stream_subsequence_suffix
  {A : Type}
  (ss : Stream A)
  (kss : monotone_nat_stream)
  (k := (hd (proj1_sig kss)))
  (n := Str_nth k ss)
  (ss' := stream_suffix ss (S k))
  (kss' := monotone_nat_stream_suffix kss)
  : EqSt
    (stream_subsequence ss kss)
    (Cons n (stream_subsequence ss' kss')).
Proof.
  apply ntheq_eqst.
  intros [|n']; try reflexivity.
  unfold stream_subsequence at 1.
  rewrite Str_nth_map.
  unfold Str_nth at 3.
  simpl.
  assert
    (Heq :
      hd (Str_nth_tl n' (stream_subsequence ss' kss'))
      =
      Str_nth n' (stream_subsequence ss' kss')
    ) by reflexivity.
  rewrite Heq.
  unfold stream_subsequence.
  rewrite Str_nth_map.
  unfold ss'.
  rewrite stream_suffix_nth.
  destruct kss as [ks Hks]; simpl.
  unfold nat_sequence_suffix.
  rewrite Str_nth_map.
  unfold k in *. clear k. simpl.
  unfold n in *; clear n.
  simpl in ss'.
  clear Heq kss'.
  assert (Hlt : 0 < S n') by lia.
  specialize (Hks 0 (S n') Hlt).
  replace (Str_nth n' (tl ks) - S (hd ks) + S (hd ks)) with (Str_nth (S n') ks)
  ; try reflexivity.
  unfold Str_nth in Hks; simpl in Hks.
  unfold Str_nth; simpl.
  lia.
Qed.

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
  : forall n : nat, Forall P (stream_prefix s n).
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
  : ForAll (fun str => P (hd str)) s.
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
  = list_annotate P (stream_prefix s n) Hs'.
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
    rewrite Plus.plus_comm.
    reflexivity.
Qed.

Lemma stream_filter_prefix_0
  `{forall (a : A), Decision (P a)}
  (ss : Stream A)
  (ks : monotone_nat_stream)
  (Hfs : filtering_subsequence P ss ks)
  (kn := Str_nth 0 (proj1_sig ks))
  (ss_to_kn := stream_prefix ss (S kn))
  : stream_prefix (stream_subsequence ss ks) (S 0)
    = filter (fun a => bool_decide (P a)) ss_to_kn.
Proof.
  generalize dependent ks.
  intros [(k, ks) Hseq]; intros.
  simpl in kn. simpl. unfold Str_nth in kn; simpl in kn. unfold kn in *.
  clear kn.
  unfold filtering_subsequence in Hfs. simpl in Hfs.
  unfold ss_to_kn.
  rewrite stream_prefix_succ.
  rewrite filter_app.
  simpl.
  rewrite <- decide_bool_decide.
  assert (P (Str_nth k ss)).
  { destruct (decide (P (Str_nth k ss))).
    assumption.
    specialize (Hfs k).
    apply Hfs.
    exists 0.
    reflexivity.
  }
  destruct (decide (P (Str_nth k ss))); [|tauto].
  replace (filter _ (stream_prefix ss k)) with (@nil A)
  ; try reflexivity.
  symmetry.
  apply filter_nil.
  rewrite Forall_forall.
  intros a Hin.
  rewrite bool_decide_decide.
  destruct (decide (P a)); [|reflexivity].
  exfalso.
  apply stream_prefix_in in Hin.
  destruct Hin as [k0 [Hlt Heq]]; subst.
  specialize (Hfs k0).
  apply Hfs in p0.
  destruct p0 as [i Heqki].
  specialize (Hseq 0 i).
  specialize (Lt.lt_irrefl k0); intro Hk0; elim Hk0.
  destruct i; subst; try assumption.
  apply Lt.lt_trans with k; try assumption.
  apply Hseq.
  auto with arith.
Qed.


Lemma stream_filter_prefix
  `{forall (a : A), Decision (P a)}
  (ss : Stream A)
  (ks : monotone_nat_stream)
  (Hfs : filtering_subsequence P ss ks)
  (n : nat)
  (kn := Str_nth n (proj1_sig ks))
  (ss_to_kn := stream_prefix ss (S kn))
  : stream_prefix (stream_subsequence ss ks) (S n)
    = filter (fun a => bool_decide (P a)) ss_to_kn.
Proof.
  generalize dependent ks. generalize dependent ss.
  induction n; try apply stream_filter_prefix_0.
  intros ss kss Hfs; intros.
  specialize (stream_filter_prefix_0 ss kss Hfs); intro H0.
  remember (Str_nth 0 (proj1_sig kss)) as k0.
  specialize (filtering_subsequence_suffix P ss kss Hfs); intros Hfs'.
  remember (monotone_nat_stream_suffix kss) as kss'.
  specialize (stream_subsequence_suffix ss kss); intros Hsss; simpl in Hsss.
  specialize (stream_prefix_EqSt _ _ Hsss); intro Hpref.
  destruct kss as [(k, ks) Hseq].
  simpl in Hfs'.
  remember (stream_suffix (tl ss) k) as ss'.
  specialize (IHn ss' kss' Hfs').
  assert
    (IHn':
      stream_prefix (stream_subsequence ss' kss') (S n)
      = filter (fun a => bool_decide (P a)) (stream_prefix ss' (S (Str_nth n (proj1_sig kss'))))
    ) by assumption.
  clear IHn.
  subst; simpl in Hpref. specialize (Hpref (S (S n))).
  inversion Hpref.
  remember (stream_prefix (stream_suffix (tl ss) k)) as sp.
  simpl in IHn'.
  rewrite <- H3 in IHn'.
  rewrite <- H2 in IHn'.
  simpl.
  rewrite IHn'.
  unfold ss_to_kn.
  unfold nat_sequence_suffix.
  rewrite Str_nth_map.
  remember (S kn) as skn.
  simpl.
  subst.
  specialize (stream_segment_alt_iff ss (S k) (S (Str_nth n ks)));
  unfold stream_segment; unfold stream_segment_alt; intro Heq.
  remember (S (Str_nth n ks)) as x; simpl in Heq; subst.
  assert  (Heq' : S (Str_nth n ks) - S k = (S (Str_nth n ks - S k))).
  { assert (Hle : 0 < S n) by lia.
    clear Hfs kn ss_to_kn H0 Hfs' Hsss Hpref.
    specialize (Hseq 0 (S n) Hle).
    unfold Str_nth in Hseq. simpl in Hseq.
    unfold Str_nth. simpl.
    lia.
  }
  rewrite Heq' in Heq.
  rewrite <- Heq.
  specialize (list_prefix_suffix (stream_prefix ss (S kn)) (S k)); intro Hps.
  rewrite <- Hps.
  rewrite filter_app.
  rewrite stream_prefix_prefix.
  + assert (H0' : filter (fun a => bool_decide (P a)) (stream_prefix ss (S k)) = [Str_nth k ss])
    by (symmetry; apply H0).
    rewrite H0'.
    remember (stream_prefix ss) as spss.
    simpl.
    f_equal.
  + clear -Hseq. unfold kn. simpl. clear kn.
    assert (Hlt : 0 < S n) by lia.
    apply Hseq in Hlt.
    unfold Str_nth in *; simpl in *.
    lia.
Qed.

Lemma stream_prefix_nth_last
  {A : Type}
  (l : Stream A)
  (n : nat)
  (_last : A)
  : last (stream_prefix l (S n)) _last = Str_nth n l.
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

Lemma stream_segment_singleton
  {A : Type}
  (l : Stream A)
  (n : nat)
  : stream_segment l n (S n) = [Str_nth n l].
Proof.
  remember (Str_nth n l) as a.
  unfold stream_segment.
  assert (Hlt : n < length (stream_prefix l (S n)))
    by (rewrite stream_prefix_length; constructor).
  specialize (list_suffix_last (stream_prefix l (S n)) n Hlt a); intro Hlast1.
  specialize (stream_prefix_nth_last l n a); intro Hlast2.
  rewrite Hlast2 in Hlast1.
  specialize (list_suffix_length (stream_prefix l (S n)) n).
  rewrite stream_prefix_length; try assumption.
  intro Hlength.
  rewrite <- Minus.minus_Sn_m in Hlength by lia.
  rewrite <- Minus.minus_diag_reverse in Hlength.
  remember (list_suffix (stream_prefix l (S n)) n) as x.
  rewrite <- Heqa in Hlast1.
  clear -Hlength Hlast1.
  destruct x; inversion Hlength.
  destruct x; inversion H0.
  simpl in Hlast1; subst; reflexivity.
Qed.

Lemma str_map_tl
  {A B : Type}
  (f : A -> B)
  (s : Stream A)
  : EqSt (tl (map f s)) (map f (tl s)).
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
  : EqSt (map f s) (Cons (f (hd s)) (map f (tl s))).
Proof.
  destruct s as  (a,s).
  constructor; try reflexivity.
  simpl.
  apply EqSt_reflex.
Qed.
