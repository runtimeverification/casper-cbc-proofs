Require Import Reals Bool Relations RelationClasses List ListSet Setoid Permutation EqdepFacts ChoiceFacts Classical Sorting.
Import ListNotations.
From CasperCBC
Require Import Lib.Preamble Lib.ListExtras Lib.ListSetExtras Lib.SortedLists CBC.Protocol CBC.Common.

(* Lists of state hashes *)
Definition justification_type (hash : Type) : Type := list hash.

Definition justification_type_inhabited {hash} : justification_type hash := [].

Definition justification_compare
  {hash} `{HscH : StrictlyComparable hash}
  : (justification_type hash -> justification_type hash -> comparison)
  :=
  list_compare compare.

Instance about_justification_type
  {hash} `{HscH : StrictlyComparable hash}
  : StrictlyComparable (justification_type hash)
  :=
  { inhabited := justification_type_inhabited;
    compare := list_compare compare;
    compare_strictorder := list_compare_strict_order;
  }.

Definition justification_add
  {hash} `{HscH : StrictlyComparable hash}
  : hash -> justification_type hash -> justification_type hash
  :=
  add_in_sorted_list_fn compare.

Definition justification_add_iff
  {hash} `{HscH : StrictlyComparable hash}
  :=
  @add_in_sorted_list_iff hash compare compare_strictorder.

Definition justification_add_head
  {hash} `{HscH : StrictlyComparable hash}
  :=
  @add_in_sorted_list_head hash compare compare_strictorder.

Definition justification_add_tail
  {hash} `{HscH : StrictlyComparable hash}
  :=
  @add_in_sorted_list_tail hash compare compare_strictorder.

Definition justification_add_sorted
  {hash} `{HscH : StrictlyComparable hash}
  :=
  @add_in_sorted_list_sorted hash compare compare_strictorder.

Definition justification_add_all
  {hash} `{HscH : StrictlyComparable hash}
  : list hash -> justification_type hash
  :=
  fold_right justification_add nil.

Lemma justification_sorted
  {hash} `{HscH : StrictlyComparable hash}
  : forall j : list hash,
  LocallySorted (compare_lt compare) (justification_add_all j).
Proof.
  induction j.
  - simpl. constructor.
  - apply justification_add_sorted. assumption.
Qed.

Lemma justification_set_eq
  {hash} `{HscH : StrictlyComparable hash}
  : forall hs : list hash,
  set_eq hs (justification_add_all hs).
Proof.
  induction hs; simpl.
  - apply set_eq_refl.
  - split; intros x Hin
    ; (unfold justification_add; rewrite justification_add_iff) || apply justification_add_iff in Hin
    ; destruct Hin as [Heq | Hin]
    ; try (subst; left; reflexivity)
    ;  right; apply IHhs; assumption.
Qed.

Lemma justification_add_all_injective
  {hash} `{HscH : StrictlyComparable hash}
  : forall hs1 hs2 : list hash,
  justification_add_all hs1 = justification_add_all hs2 ->
  set_eq hs1 hs2.
Proof.
  intros.
  apply (@set_equality_predicate hash (compare_lt compare) compare_lt_strict_order) in H;
    try apply justification_sorted.
  apply set_eq_tran with (justification_add_all hs1); try apply justification_set_eq.
  apply set_eq_tran with (justification_add_all hs2); try assumption.
  apply set_eq_comm. apply justification_set_eq.
Qed.

Definition justification_in
  {hash} `{HscH : StrictlyComparable hash}
  : hash -> list hash -> bool := inb compare_eq_dec.

(* Messages *)
Definition message (C V hash : Type) : Type := C * V * justification_type hash.

Class StrictlyComparable3 C V hash
  `{HscC : StrictlyComparable C} `{HscV : StrictlyComparable V} `{HscH : StrictlyComparable hash}.


Instance message_type
  {C V hash} `{Hsc3 : StrictlyComparable3 C V hash}
  : StrictlyComparable (message C V hash)
  :=
  TripleStrictlyComparable C V (justification_type hash).

(* StrictlyComparable and CompareStrictOrder for message type comes for free *)

Definition estimate
  {C V hash}
  (msg : message C V hash) : C
  :=
  match msg with (c, _, _) => c end.

Definition sender
  {C V hash}
  (msg : message C V hash) : V
  :=
  match msg with (_, v, _) => v end.

Definition justification
  {C V hash}
  (msg : message C V hash) : justification_type hash :=
  match msg with (_, _, j) => j end.


Class MessageHash message hash :=
  { hash_message : message -> hash
  }.

Class InjectiveMessageHash message hash `{Hmh : MessageHash message hash} :=
  { hash_message_injective : Injective hash_message
  }.

(* Light node states are sets of message *)
(* Additionally, we don't care about sorting *)
Definition state C V hash := set (message C V hash).

Definition state_inhabited {C V hash} : state C V hash := [].

Definition state_compare
  {C V hash} `{Hsc3 : StrictlyComparable3 C V hash}
  : (state C V hash -> state C V hash -> comparison) := list_compare compare.

Instance about_state
  {C V hash} `{Hsc3 : StrictlyComparable3 C V hash}
  : StrictlyComparable (state C V hash) :=
  { inhabited := state_inhabited;
    compare := list_compare compare;
    compare_strictorder := list_compare_strict_order;
  }.

Definition state0 C V hash : state C V hash := [].

Definition state_add
  {C V hash} `{Hsc3 : StrictlyComparable3 C V hash}
  : message C V hash -> state C V hash -> state C V hash
  :=
  set_add compare_eq_dec.

Definition state_remove
  {C V hash} `{HscM : StrictlyComparable (message C V hash)}
  : message C V hash -> state C V hash -> state C V hash
  :=
  set_remove compare_eq_dec.

Definition state_in
  {C V hash} `{Hsc3 : StrictlyComparable3 C V hash}
  : message C V hash-> state C V hash-> bool
  :=
  set_mem compare_eq_dec.

Definition state_union
  {C V hash} `{Hsc3 : StrictlyComparable3 C V hash}
  : state C V hash-> state C V hash-> state C V hash
  :=
  set_union compare_eq_dec.

Definition state_eq
  {C V hash}
  (s1 s2 : state C V hash)
  :=
  incl s1 s2 /\ incl s2 s1.

Lemma state_union_comm
  {C V hash} `{Hsc3 : StrictlyComparable3 C V hash}
  : forall s1 s2 : state C V hash, state_eq (state_union s1 s2) (state_union s2 s1).
Proof.
  intros; unfold state_eq; split;
  intros x H_in;
  now apply set_union_comm.
Qed.

Definition hash_state
  {C V hash} `{Hsc3 : StrictlyComparable3 C V hash} `{Hmh : MessageHash (message C V hash) hash}
  (sigma : state C V hash) : justification_type hash :=
  justification_add_all (map hash_message sigma).

Lemma hash_state_sorted
  {C V hash} `{Hsc3 : StrictlyComparable3 C V hash} `{Hmh : MessageHash (message C V hash) hash}
  : forall sigma : state C V hash,
  LocallySorted (compare_lt compare) (hash_state sigma).
Proof.
  intros.
  apply justification_sorted.
Qed.

Lemma hash_state_injective
  {C V hash} `{Hsc3 : StrictlyComparable3 C V hash} `{Hmhi : InjectiveMessageHash (message C V hash) hash}
  : forall sigma1 sigma2 : state C V hash,
  hash_state sigma1 = hash_state sigma2
  <->
  set_eq sigma1 sigma2.
Proof.
  split; intros.
  - apply justification_add_all_injective in H.
    destruct H as [H12 H21].
    split; intros x Hin
    ; apply (in_map hash_message) in Hin
    ; apply H12 in Hin || apply H21 in Hin
    ; apply in_map_iff in Hin
    ; destruct Hin as [x' [Heq Hin]]
    ; apply hash_message_injective in Heq
    ; subst; assumption.
  - apply (@set_equality_predicate hash (compare_lt compare) compare_lt_strict_order); try apply hash_state_sorted.
    unfold hash_state.
    apply set_eq_tran with (map hash_message sigma2); try apply (justification_set_eq (map hash_message sigma2)).
    apply set_eq_comm.
    apply set_eq_tran with (map hash_message sigma1); try apply (justification_set_eq (map hash_message sigma1)).
    apply map_set_eq. apply set_eq_comm. assumption.
Qed.

Lemma hash_state_in
  {C V hash} `{Hsc3 : StrictlyComparable3 C V hash} `{Hmhi : InjectiveMessageHash (message C V hash) hash}
  : forall (sigma : state C V hash) msg,
  In (hash_message msg) (hash_state sigma) <->
  In msg sigma.
Proof.
  unfold hash_state.
  intros.
  assert (H_s : set_eq (map hash_message sigma) (justification_add_all (map hash_message sigma)))
      by apply justification_set_eq.
  split; intro Hin.
  - apply H_s in Hin.
    apply in_map_iff in Hin.
    destruct Hin as [msg' [Heq Hin]].
    apply hash_message_injective in Heq. subst. assumption.
  - apply H_s. apply in_map. assumption.
Qed.

Lemma hash_state_incl
  {C V hash} `{Hsc3 : StrictlyComparable3 C V hash} `{Hmh : InjectiveMessageHash (message C V hash) hash}
  : forall sigma1 sigma2 : state C V hash,
  incl sigma1 sigma2 <-> incl (hash_state sigma1) (hash_state sigma2).
Proof.
  intros.
  assert (H_s1 : set_eq (map hash_message sigma1) (justification_add_all (map hash_message sigma1)))
      by apply justification_set_eq.
  assert (H_s2 : set_eq (map hash_message sigma2) (justification_add_all (map hash_message sigma2)))
      by apply justification_set_eq.
  unfold hash_state.
  split; intro Hincl.
  - intros h Hin.
    apply H_s2. apply H_s1 in Hin.
    apply in_map_iff. apply in_map_iff in Hin.
    destruct Hin as [msg [H_mh Hin_m]].
    apply Hincl in Hin_m.
    exists msg. split; assumption.
  - intros msg Hin. apply hash_state_in in Hin.
    apply Hincl in Hin.
    apply hash_state_in in Hin. assumption.
Qed.

Definition equivocating_messages
  {C V hash} `{Hsc3 : StrictlyComparable3 C V hash} `{Hmh : MessageHash (message C V hash) hash}
  (msg1 msg2 : message C V hash) : bool
  :=
  match compare_eq_dec msg1 msg2 with
  | left _  => false
  | _ => match msg1, msg2 with (c1,v1,j1), (c2,v2,j2) =>
      match compare_eq_dec v1 v2 with
      | left _  => negb (inb compare_eq_dec (hash_message msg1) j2) && negb (inb compare_eq_dec (hash_message msg2) j1)
      | right _ => false
      end
    end
  end.

Definition equivocating_messages_prop
  {C V hash} `{Hmh : MessageHash (message C V hash) hash}
  (msg1 msg2 : message C V hash) : Prop
  :=
  msg1 <> msg2 /\ sender msg1 = sender msg2 /\ ~ In (hash_message msg1) (justification msg2) /\ ~ In (hash_message msg2) (justification msg1).

Lemma equivocating_messages_sender
  {C V hash} `{Hsc3 : StrictlyComparable3 C V hash} `{Hmh : MessageHash (message C V hash) hash}
  : forall msg1 msg2 : message C V hash,
    equivocating_messages msg1 msg2 = true -> sender msg1 = sender msg2.
Proof.
  unfold equivocating_messages.
  intros [(c1, v1) j1] [(c2, v2) j2] H.
  simpl.
  destruct (compare_eq_dec (c1, v1, j1) (c2, v2, j2)).
  rewrite eq_dec_if_true in H.
  inversion H.
  assumption.
  rewrite eq_dec_if_false in H.
  destruct (compare_eq_dec v1 v2).
  assumption. inversion H. assumption.
Qed.

Lemma equivocating_messages_correct
  {C V hash} `{Hsc3 : StrictlyComparable3 C V hash} `{Hmh : MessageHash (message C V hash) hash}
  : forall (msg1 msg2 : message C V hash),
    equivocating_messages msg1 msg2 = true <-> equivocating_messages_prop msg1 msg2.
Proof.
  intros [[c1 v1] j1] [[c2 v2] j2]; split; intro H.
  - repeat split.
    + (* Proving inequality obligation *)
      intro H_absurd.
      unfold equivocating_messages in H.
      rewrite eq_dec_if_true in H.
      inversion H. assumption.
    + (* Proving sender obligation *)
      now apply equivocating_messages_sender.
    + (* Proving msg1 is not in msg2's justification *)
      intro H_absurd.
      apply (in_function compare_eq_dec) in H_absurd.
      unfold equivocating_messages in H.
      simpl in H_absurd.
      rewrite H_absurd in H.
      destruct (compare_eq_dec (c1,v1,j1) (c2,v2,j2)).
      rewrite eq_dec_if_true in H. inversion H.
      assumption. rewrite eq_dec_if_false in H.
      destruct (compare_eq_dec v1 v2).
      subst.
      simpl in H. inversion H.
      inversion H. assumption.
    + (* Proving msg2 is not in msg1's justification *)
      intro H_absurd. apply (in_function compare_eq_dec) in H_absurd.
      unfold equivocating_messages in H.
      simpl in H_absurd. rewrite H_absurd in H.
      destruct (compare_eq_dec (c1,v1,j1) (c2,v2,j2)).
      rewrite eq_dec_if_true in H. inversion H.
      assumption. rewrite eq_dec_if_false in H.
      destruct (compare_eq_dec v1 v2).
      rewrite andb_false_r in H. inversion H.
      inversion H. assumption.
  - destruct H as [H_neq [H_sender [H_in1 H_in2]]].
    simpl in H_sender.
    unfold equivocating_messages.
    destruct (compare_eq_dec (c1,v1,j1) (c2,v2,j2)).
    contradiction; try assumption.
    rewrite eq_dec_if_false; try assumption.
    destruct (compare_eq_dec v1 v2); try contradiction.
    simpl in *.
    apply andb_true_iff.
    split
    ; apply negb_true_iff
    ; rewrite mirror_reflect_curry; try exact H_in1; try exact H_in2
    ;  intros; split; apply (in_function compare_eq_dec).
Qed.

Lemma equivocating_messages_correct'
  {C V hash} `{Hsc3 : StrictlyComparable3 C V hash} `{Hmh : MessageHash (message C V hash) hash}
  : forall (msg1 msg2 : message C V hash),
    equivocating_messages msg1 msg2 = false <-> ~ equivocating_messages_prop msg1 msg2.
Proof.
  intros.
  apply mirror_reflect_curry.
  exact equivocating_messages_correct.
Qed.

Lemma equivocating_messages_comm
  {C V hash} `{Hsc3 : StrictlyComparable3 C V hash} `{Hmh : MessageHash (message C V hash) hash}
  : forall msg1 msg2 : message C V hash,
  equivocating_messages msg1 msg2 = equivocating_messages msg2 msg1.
Proof.
  intros [(c1, v1) sigma1] [(c2, v2) sigma2].
  unfold equivocating_messages.
  destruct (compare_eq_dec (c1, v1, sigma1) (c2, v2, sigma2)).
  subst. rewrite eq_dec_if_true.
  rewrite eq_dec_if_true. reflexivity.
  symmetry; assumption.
  assumption.
  rewrite (eq_dec_if_false compare_eq_dec).
  destruct (compare_eq_dec v1 v2).
  rewrite eq_dec_if_false.
  rewrite e. rewrite eq_dec_if_true.
  rewrite andb_comm. reflexivity. reflexivity.
  intro Hnot; symmetry in Hnot; tauto.
  rewrite eq_dec_if_false.
  rewrite eq_dec_if_false. reflexivity.
  intro Hnot; symmetry in Hnot; tauto.
  intro Hnot; symmetry in Hnot; tauto.
  assumption.
Qed.

Lemma equivocating_messages_prop_swap
  {C V hash} `{Hsc3 : StrictlyComparable3 C V hash} `{Hmh : MessageHash (message C V hash) hash}
  : forall msg1 msg2 : message C V hash,
    equivocating_messages_prop msg1 msg2 <-> equivocating_messages_prop msg2 msg1.
Proof.
  intros; rewrite <- equivocating_messages_correct.
  rewrite <- equivocating_messages_correct.
  rewrite equivocating_messages_comm.
  tauto.
Qed.

Lemma non_equivocating_messages_sender
  {C V hash} `{Hsc3 : StrictlyComparable3 C V hash} `{Hmh : MessageHash (message C V hash) hash}
  : forall msg1 msg2 : message C V hash,
  sender msg1 <> sender msg2 ->
  equivocating_messages msg1 msg2 = false.
Proof.
  intros [(c1, v1) j1] [(c2, v2) j2] Hneq. simpl in Hneq.
  unfold equivocating_messages.
  rewrite eq_dec_if_false.
  - rewrite eq_dec_if_false; try reflexivity. assumption.
  - intro Heq. inversion Heq; subst; clear Heq. apply Hneq. reflexivity.
Qed.

Definition equivocating_in_state
  {C V hash} `{Hsc3 : StrictlyComparable3 C V hash} `{Hmh : MessageHash (message C V hash) hash}
  (msg : message C V hash) (sigma : state C V hash) : bool
  :=
  existsb (equivocating_messages msg) sigma.

Definition equivocating_in_state_prop
  {C V hash} `{Hmh : MessageHash (message C V hash) hash}
  (msg : message C V hash) (s : state C V hash) : Prop
  :=
  exists msg', In msg' s /\ equivocating_messages_prop msg msg'.

Lemma equivocating_in_state_correct
  {C V hash} `{Hsc3 : StrictlyComparable3 C V hash} `{Hmh : MessageHash (message C V hash) hash}
  : forall (msg : message C V hash) s,
  equivocating_in_state msg s = true <-> equivocating_in_state_prop msg s.
Proof.
  intros msg s.
  split; intro H.
  - unfold equivocating_in_state in H.
    rewrite existsb_exists in H.
    destruct H as [msg' [H_in H_equiv]].
    exists msg'. split. assumption.
    rewrite <- equivocating_messages_correct. assumption.
  - destruct H as [msg' [H_in H_equiv]].
    apply existsb_exists.
    exists msg'; split. assumption.
    rewrite equivocating_messages_correct. assumption.
Qed.

Lemma equivocating_in_state_correct'
  {C V hash} `{Hsc3 : StrictlyComparable3 C V hash} `{Hmh : MessageHash (message C V hash) hash}
  : forall (msg : message C V hash) s,
  equivocating_in_state msg s = false <-> ~ equivocating_in_state_prop msg s.
Proof.
  intros.
  apply mirror_reflect_curry.
  exact equivocating_in_state_correct.
Qed.

Lemma equivocating_in_state_incl
  {C V hash} `{Hmh : MessageHash (message C V hash) hash}
  : forall sigma sigma',
  incl sigma sigma' ->
  forall msg,
    equivocating_in_state_prop msg sigma ->
    equivocating_in_state_prop msg sigma'.
Proof.
  intros.
  destruct H0 as [x [Hin Heq]]. exists x.
  split; try assumption.
  apply H. assumption.
Qed.

Lemma equivocating_in_state_not_seen
  {C V hash}  `{Hsc3 : StrictlyComparable3 C V hash} `{Hmh : MessageHash (message C V hash) hash}
  : forall msg sigma,
  ~ In (sender msg) (set_map compare_eq_dec sender sigma) ->
  ~ equivocating_in_state_prop msg sigma.
Proof.
  intros [(c, v) j] sigma Hnin. rewrite set_map_exists in Hnin. simpl in Hnin.
  rewrite <- equivocating_in_state_correct'.
  apply existsb_forall.
  intros [(cx, vx) jx] Hin.
  apply non_equivocating_messages_sender. simpl.
  intro Heq. subst. apply Hnin.
  exists (cx, vx, jx). split; try assumption. reflexivity.
Qed.

Definition equivocating_senders
  {C V hash}  `{Hsc3 : StrictlyComparable3 C V hash} `{Hmh : MessageHash (message C V hash) hash}
  (sigma : state C V hash) : set V
  :=
  set_map compare_eq_dec sender (filter (fun msg => equivocating_in_state msg sigma) sigma).

Definition equivocating_senders_prop
  {C V hash} `{Hmh : MessageHash (message C V hash) hash}
  (s : state C V hash) (lv : set V)
  :=
  forall v, In v lv <-> exists msg, In msg s /\ sender msg = v /\ equivocating_in_state_prop msg s.

Lemma equivocating_senders_correct
  {C V hash}  `{Hsc3 : StrictlyComparable3 C V hash} `{Hmh : MessageHash (message C V hash) hash}
  : forall s : state C V hash,
  equivocating_senders_prop s (equivocating_senders s).
Proof.
  intros s v; split; intro H.
  - (* Left direction *)
    apply set_map_exists in H.
    destruct H as [msg [H_in H_sender]].
    exists msg.
    apply filter_In in H_in.
    destruct H_in. repeat split; try assumption.
    rewrite <- equivocating_in_state_correct.
    assumption.
  - destruct H as [msg [H_in [H_sender H_equiv]]].
    unfold equivocating_senders.
    rewrite <- H_sender.
    apply set_map_in.
    rewrite filter_In. split.
    assumption. rewrite equivocating_in_state_correct.
    assumption.
Qed.

Lemma equivocating_senders_incl
  {C V hash}  `{Hsc3 : StrictlyComparable3 C V hash} `{Hmh : MessageHash (message C V hash) hash}
  : forall sigma sigma' : state C V hash,
  incl sigma sigma' ->
  incl (equivocating_senders sigma) (equivocating_senders sigma').
Proof.
  intros.
  apply set_map_incl.
  apply incl_tran with (filter (fun msg : message C V hash=> equivocating_in_state msg sigma) sigma').
  - apply filter_incl; assumption.
  - apply filter_incl_fn. intro.
    do 2 rewrite equivocating_in_state_correct.
    apply equivocating_in_state_incl. assumption.
Qed.

Definition reach
  {C V hash}
  (s1 s2 : state C V hash)
  :=
  incl s1 s2.

Lemma reach_refl
  {C V hash}
  : forall s : state C V hash,
  reach s s.
Proof. apply incl_refl. Qed.

Lemma reach_trans
  {C V hash}
  : forall s1 s2 s3 : state C V hash,
  reach s1 s2 -> reach s2 s3 -> reach s1 s3.
Proof. apply incl_tran. Qed.

Lemma reach_union
  {C V hash}  `{Hsc3 : StrictlyComparable3 C V hash}
  : forall s1 s2 : state C V hash,
  reach s1 (state_union s1 s2).
Proof. intros s1 s2 x H_in; apply set_union_iff; left; assumption. Qed.

Lemma reach_morphism
  {C V hash}
  : forall s1 s2 s3 : state C V hash,
  reach s1 s2 -> state_eq s2 s3 -> reach s1 s3.
Proof. intros s1 s2 s3 H_reach H_eq x H_in. spec H_reach x H_in.
       destruct H_eq as [H_eq _]. spec H_eq x H_reach; assumption.
Qed.

Definition fault_weight_state
  {C V hash}  `{Hsc3 : StrictlyComparable3 C V hash} `{Hmh : MessageHash (message C V hash) hash} `{Hm : Measurable V}
  (sigma : state C V hash) : R
  :=
  sum_weights (equivocating_senders sigma).

Lemma fault_weight_state_incl
  {C V hash}  `{Hsc3 : StrictlyComparable3 C V hash} `{Hmh : MessageHash (message C V hash) hash} `{Hm : Measurable V}
  : forall sigma sigma' : state C V hash,
  incl sigma sigma' ->
  (fault_weight_state sigma <= fault_weight_state sigma')%R.
Proof.
  intros. apply sum_weights_incl; try apply set_map_nodup.
  apply equivocating_senders_incl. assumption.
Qed.

(* The not overweight condition *)
Definition not_heavy
  {C V hash} `{Hsc3 : StrictlyComparable3 C V hash} `{Hmh : MessageHash (message C V hash) hash} `{Hrt : ReachableThreshold V}
  (sigma : state C V hash) : Prop
  :=
  (fault_weight_state sigma <= proj1_sig threshold)%R.

Lemma not_heavy_subset
  {C V hash} `{Hsc3 : StrictlyComparable3 C V hash} `{Hmh : MessageHash (message C V hash) hash} `{Hrt : ReachableThreshold V}
  : forall sigma sigma' : state C V hash,
  incl sigma sigma' ->
  not_heavy sigma' ->
  not_heavy sigma.
Proof.
  unfold not_heavy.
  intros.
  apply Rle_trans with (fault_weight_state sigma'); try assumption.
  apply fault_weight_state_incl; assumption.
Qed.

Lemma not_heavy_set_eq
  {C V hash} `{Hsc3 : StrictlyComparable3 C V hash} `{Hmh : MessageHash (message C V hash) hash} `{Hrt : ReachableThreshold V}
  : forall sigma sigma' : state C V hash,
  set_eq sigma sigma' ->
  not_heavy sigma ->
  not_heavy sigma'.
Proof.
  intros. destruct H.
  apply (not_heavy_subset _ _ H1 H0).
Qed.

Class ProtocolState C V hash
  `{Hsc3 : StrictlyComparable3 C V hash}
  `{Hmhi : InjectiveMessageHash (message C V hash) hash}
  `{Hrt : ReachableThreshold V}
  `{He : Estimator (state C V hash) C}.


Inductive protocol_state
  {C V hash} `{PS : ProtocolState C V hash}
  : state C V hash -> Prop
  :=
  | protocol_state_nil : protocol_state (state0 C V hash)
  | protocol_state_cons : forall (j : state C V hash),
    protocol_state j ->
    forall (c : C),
      valid_estimate c j ->
      forall (v : V) (s : state C V hash),
        In (c, v, hash_state j) s ->
        protocol_state (set_remove compare_eq_dec (c, v, hash_state j) s) ->
        NoDup s ->
        not_heavy s ->
        protocol_state s.


Lemma protocol_state_nodup
  {C V hash} `{PS : ProtocolState C V hash}
  : forall sigma : state C V hash,
  protocol_state sigma ->
  NoDup sigma.
Proof.
  intros. inversion H; subst.
  - constructor.
  - assumption.
Qed.

Lemma not_extx_in_x
  {C V hash} `{HPS : ProtocolState C V hash}
  : forall c v (s s' : state C V hash),
    protocol_state s ->
    protocol_state s' ->
    incl s' s ->
    ~ In (hash_message (c, v, hash_state s)) (hash_state s').
Proof.
  intros c v s s' PS PS'. induction PS'; intros Hincl Hin; apply hash_state_in in Hin.
  - unfold state0 in Hin. inversion Hin.
  - apply (set_remove_in_iff compare_eq_dec (c, v, hash_state s) (c0, v0, hash_state j) s0 H1 H0) in Hin.
    destruct Hin as [Heq | Hin].
    + inversion Heq; subst; clear Heq. apply hash_state_injective in H6. apply IHPS'1; try apply H6.
      apply hash_state_in. apply Hincl in H0. apply H6.
      assert (hash_state s = hash_state j) by (apply hash_state_injective; assumption).
      rewrite H3. assumption.
    + apply IHPS'2; try (apply hash_state_in; assumption).
      apply incl_tran with s0; try assumption.
      intros h Hin_h. apply set_remove_1 in Hin_h. assumption.
Qed.

Lemma not_in_self
  {C V hash} `{HPS : ProtocolState C V hash}
  : forall (s : state C V hash),
    protocol_state s ->
    forall (v : V),
    ~ In (get_estimate s, v, hash_state s) s.
Proof.
  intros s about_s v H_absurd.
  assert (H_useful := not_extx_in_x (get_estimate s) v s s about_s about_s (incl_refl s)).
  apply (in_map hash_message s (get_estimate s, v, hash_state s)) in H_absurd.
  assert (H_eq := justification_set_eq (map hash_message s)).
  destruct H_eq as [H_eq _].
  spec H_eq (hash_message (get_estimate s, v, hash_state s)) H_absurd.
  contradiction.
Qed.

Lemma not_in_self_relaxed
  {C V hash} `{HPS : ProtocolState C V hash}
  : forall (s : state C V hash),
    protocol_state s ->
    forall (c : C) (v : V),
    ~ In (c, v, hash_state s) s.
Proof.
  intros s about_s c v H_absurd.
  assert (H_useful := not_extx_in_x c v s s about_s about_s (incl_refl s)).
  apply (in_map hash_message s (c, v, hash_state s)) in H_absurd.
  assert (H_eq := justification_set_eq (map hash_message s)).
  destruct H_eq as [H_eq _].
  spec H_eq (hash_message (c, v, hash_state s)) H_absurd.
  contradiction.
Qed.

Lemma set_eq_protocol_state
  {C V hash} `{HPS : ProtocolState C V hash}
  : forall sigma : state C V hash,
  protocol_state sigma ->
  forall sigma',
    set_eq sigma sigma' ->
    NoDup sigma' ->
    protocol_state sigma'.
Proof.
  intros sigma H'.
  induction H'; intros.
  - destruct H. unfold state0 in *.
    apply incl_empty in H1; subst. constructor.
  - apply (set_eq_remove compare_eq_dec (c, v, hash_state j)) in H3 as Hset_eq; try assumption.
    apply IHH'2 in Hset_eq.
    apply (protocol_state_cons j H'1 c H v sigma'); try assumption.
    + destruct H3. now apply (H3 (c, v, hash_state j)).
    + apply (not_heavy_set_eq _ _ H3 H2).
    + now apply set_remove_nodup.
Qed.

(* The intuition is we can never satisfy that neither messages are contained in each other's justifications. *)
Lemma non_equivocating_messages_extend
  {C V hash} `{Hsc3 : StrictlyComparable3 C V hash} `{Hmhi : InjectiveMessageHash (message C V hash) hash}
  : forall (msg : message C V hash) sigma1 c v,
  In msg sigma1 ->
  equivocating_messages msg (c, v, hash_state sigma1) = false.
Proof.
  intros [(c0, v0) sigma']; intros.
  unfold equivocating_messages.
  destruct (compare_eq_dec (c0, v0, sigma') (c, v, hash_state sigma1)).
  - (* In the case that these two messages are equal, they cannot be equivocating *)
    now rewrite eq_dec_if_true.
  - (* In the case that these messages are not equal, *)
    rewrite eq_dec_if_false.
    (* When their senders are equal *)
    destruct (compare_eq_dec v0 v).
    + subst.
      apply hash_state_in in H.
      apply in_correct in H.
      rewrite H.
      tauto.
    + reflexivity.
    + assumption.
Qed.

Lemma equivocating_in_state_extend
  {C V hash} `{Hsc3 : StrictlyComparable3 C V hash} `{Hmhi : InjectiveMessageHash (message C V hash) hash}
  :  forall c v (s : state C V hash),
    ~ equivocating_in_state_prop (c, v, hash_state s) s.
Proof.
  intros c v s H_absurd.
  destruct H_absurd as [msg [H_in H_equiv]].
  assert (H_useful := non_equivocating_messages_extend msg s c v H_in).
  rewrite equivocating_messages_correct' in H_useful.
  rewrite equivocating_messages_prop_swap in H_equiv.
  contradiction.
Qed.

Lemma equivocating_senders_extend
  {C V hash}  `{Hsc3 : StrictlyComparable3 C V hash} `{Hmhi : InjectiveMessageHash (message C V hash) hash}
  : forall (sigma : state C V hash) c v,
  equivocating_senders ((c, v, hash_state sigma) :: sigma) = equivocating_senders sigma.
Proof.
  unfold equivocating_senders. intros.
  (* Why doesn't the suff tactic work *)
  simpl.
  assert (H_irrefl : equivocating_messages (c, v, hash_state sigma) (c, v, hash_state sigma) = false).
  { apply equivocating_messages_correct'.
    intro H_absurd.
    destruct H_absurd as [H_eq _].
    contradiction. }
  rewrite H_irrefl.
  simpl.
  assert (H_useful := equivocating_in_state_correct' (c,v,hash_state sigma) sigma).
  assert (H_useful' := equivocating_in_state_extend c v sigma).
  apply H_useful in H_useful'.
  rewrite H_useful'.
  f_equal.
  apply filter_eq_fn.
  intros.
  split; intros.
  - apply orb_prop in H0.
    destruct H0.
    exfalso.
    assert (H_goal := non_equivocating_messages_extend a sigma c v H).
    firstorder.
    apply (H1 a). split; try assumption.

    rewrite equivocating_messages_prop_swap.
    apply equivocating_messages_correct.
    assumption. assumption.
  - apply orb_true_intro. tauto.
Qed.

Lemma protocol_state_not_heavy
  {C V hash}  `{PS : ProtocolState C V hash}
  : forall sigma : state C V hash,
  protocol_state sigma ->
  not_heavy sigma.
Proof.
  intros. inversion H.
  - unfold not_heavy. unfold fault_weight_state. simpl.
    apply Rge_le. destruct threshold; easy.
  - assumption.
Qed.

(* Recording entire histories preserves protocol state-ness *)
Lemma copy_protocol_state
  {C V hash}  `{PS : ProtocolState C V hash}
  : forall s : state C V hash,
  protocol_state s ->
  forall v,
    protocol_state ((get_estimate s, v, hash_state s) :: s).
Proof.
  intros s Hps v.
  apply protocol_state_cons with s (get_estimate s) v; try assumption; try apply get_estimate_correct; try apply incl_refl.
  apply in_eq.
  rewrite set_remove_first; easy.
  apply NoDup_cons.
  now apply not_in_self.
  now apply protocol_state_nodup.
  apply not_heavy_subset with ((get_estimate s,v,hash_state s) :: s).
  - apply incl_refl.
  - unfold not_heavy. unfold fault_weight_state.
    rewrite equivocating_senders_extend.
    apply protocol_state_not_heavy in Hps. assumption.
Qed.

Lemma about_prot_state
  {C V hash}  `{PS : ProtocolState C V hash}
  : forall (s1 s2 : state C V hash),
    protocol_state s1 ->
    protocol_state s2 ->
    (fault_weight_state (state_union s1 s2) <= proj1_sig threshold)%R ->
    protocol_state (state_union s1 s2).
Proof.
  intros sig1 sig2 Hps1 Hps2.
  induction Hps2; intros.
  - simpl. assumption.
  - clear IHHps2_1.
    assert (protocol_state (state_union sig1 (set_remove compare_eq_dec (c, v, hash_state j) s))).
    { apply IHHps2_2.
      apply not_heavy_subset with (state_union sig1 s); try assumption.
      intro msg; intro Hin.
      apply set_union_intro.
      unfold state_union in Hin; apply set_union_elim in Hin.
      destruct Hin; try (left; assumption).
      right. apply (set_remove_1 _ _ _ _ H4).
    }
    clear IHHps2_2.
    apply protocol_state_nodup in Hps1 as Hnodups1.
    assert (HnodupUs1s' := H1).
    apply (set_union_nodup compare_eq_dec Hnodups1) in HnodupUs1s'.
    destruct (in_dec compare_eq_dec (c, v, hash_state j) sig1).
    + apply set_eq_protocol_state with (state_union sig1 (set_remove compare_eq_dec (c, v, hash_state j) s))
      ; try assumption.
      apply set_eq_remove_union_in; assumption.
    + eapply (protocol_state_cons j Hps2_1 c H v); try assumption.
      * apply set_union_iff. right. assumption.
      * apply (set_remove_nodup compare_eq_dec (c, v, hash_state j)) in HnodupUs1s' as Hnoduprem.
        apply set_eq_protocol_state with (state_union sig1 (set_remove compare_eq_dec (c, v, hash_state j) s))
        ; try assumption.
        apply set_eq_remove_union_not_in; assumption.
Qed.

Lemma equivocation_weight_compat
  {C V hash}  `{Hsc3 : StrictlyComparable3 C V hash} `{Hmh : MessageHash (message C V hash) hash} `{Hm : Measurable V}
  : forall s1 s2 : state C V hash,
  (fault_weight_state s1 <= fault_weight_state (state_union s2 s1))%R.
Proof.
  intros.
  apply fault_weight_state_incl.
  intros msg H_in.
  apply set_union_iff. tauto.
Qed.

Instance LightNode_seteq
  {C V hash}  `{PS : ProtocolState C V hash}
  : CBC_protocol_eq
  :=
  { consensus_values := C;
    about_consensus_values := HscC;
    validators := V;
    about_validators := HscV;
    weight := weight;
    t := threshold;
    suff_val := reachable_threshold;
    state := state C V hash;
    state0 := state0 C V hash;
    state_eq := set_eq;
    about_state := about_state;
    state_union := state_union;
    state_union_comm := state_union_comm;
    reach := reach;
    reach_refl := reach_refl;
    reach_trans := reach_trans;
    reach_union := reach_union;
    reach_morphism := reach_morphism;
    E := estimator;
    estimator_total := estimator_total;
    prot_state := protocol_state;
    about_state0 := protocol_state_nil;
    equivocation_weight := fault_weight_state;
    equivocation_weight_compat := equivocation_weight_compat;
    about_prot_state := about_prot_state;
  }.

Definition pstate_light
  (C V hash : Type)  `{PS : ProtocolState C V hash}
  : Type
  :=
  {s : state C V hash | protocol_state s}.
Definition pstate_light_proj1
  {C V hash}  `{PS : ProtocolState C V hash}
  (p : pstate_light C V hash) : state C V hash
  :=
  proj1_sig p.
Coercion pstate_light_proj1 : pstate_light >-> state.

Definition pstate_light_rel
  {C V hash}  `{PS : ProtocolState C V hash}
  : pstate_light C V hash -> pstate_light C V hash -> Prop :=
  fun p1 p2 => incl (pstate_light_proj1 p1) (pstate_light_proj1 p2).

Definition non_trivial_pstate_light
  {C V hash}  `{PS : ProtocolState C V hash}
  (P : pstate_light C V hash -> Prop) :=
  (exists (s1 : pstate_light C V hash), forall (s : pstate_light C V hash), pstate_light_rel s1 s -> P s)
  /\
  (exists (s2 : pstate_light C V hash), forall (s : pstate_light C V hash), pstate_light_rel s2 s -> (P s -> False)).


Lemma not_heavy_singleton
  {C V hash} `{Hsc3 : StrictlyComparable3 C V hash} `{Hmh : MessageHash (message C V hash) hash} `{Hrt : ReachableThreshold V}
  : forall msg : message C V hash,
  not_heavy [msg].
Proof.
  intros [(c, v) j].
  unfold not_heavy.
  unfold fault_weight_state.
  unfold equivocating_senders.
  simpl. unfold equivocating_messages.
  rewrite eq_dec_if_true; try reflexivity. simpl.
  apply Rge_le. destruct threshold. easy.
Qed.

Lemma protocol_state_singleton
  {C V hash}  `{PS : ProtocolState C V hash}
  : forall c v (j : state C V hash),
  protocol_state j ->
  valid_estimate c j ->
  protocol_state [(c, v, hash_state j)].
Proof.
  intros.
  apply protocol_state_cons with j c v; try assumption.
  - left. reflexivity.
  - simpl. rewrite eq_dec_if_true; constructor.
  - constructor; try constructor. apply in_nil.
  - apply not_heavy_singleton.
Qed.

(* This is a critical property of the light node protocol *)
(* Any duplicate-free subset of a protocol state (as list message) is itself a protocol state *)
Lemma protocol_state_incl
  {C V hash}  `{PS : ProtocolState C V hash}
  : forall (s : state C V hash),
    protocol_state s ->
    forall (s' : state C V hash),
      NoDup s' ->
      incl s' s ->
      protocol_state s'.
Proof.
  intros s about_s.
  induction about_s; intros s' H_nodup H_incl.
  - destruct s'.
    + apply protocol_state_nil.
    + spec H_incl m (in_eq m s'). inversion H_incl.
  - destruct (classic (In (c,v,hash_state j) s')).
    + spec IHabout_s2 (set_remove compare_eq_dec (c,v,hash_state j) s').
      apply protocol_state_cons with j c v; try assumption.
      2 : now apply not_heavy_subset with s.
      apply IHabout_s2.
      now apply set_remove_nodup.
      intros msg H_in.
      destruct (classic (msg = (c,v,hash_state j))).
      * subst.
        assert (H_contra := set_remove_elim compare_eq_dec (c,v,hash_state j) s').
        spec H_contra H_nodup.
        contradiction.
      * spec H_incl msg.
        spec H_incl.
        assert (H_useful := set_remove_iff compare_eq_dec msg (c,v,hash_state j)).
        spec H_useful s' H_nodup.
        rewrite H_useful in H_in.
        tauto.
        apply set_remove_iff; try tauto.
    + spec IHabout_s2 s'.
      apply IHabout_s2.
      assumption.
      intros msg H_in.
      assert (msg <> (c,v,hash_state j)).
      { intros H_absurd. subst.
        spec H_incl (c,v,hash_state j) H_in.
        contradiction. }
      apply set_remove_iff; try assumption.
      split. 2 : assumption.
      now apply (H_incl msg H_in).
Qed.

(* We can now always construct an equivocation by splitting any protocol state into duplicate-free subsets of messages *)
Lemma binary_justification_nodup
  {C V hash} `{Hsc3 : StrictlyComparable3 C V hash} `{Hmhi : InjectiveMessageHash (message C V hash) hash}
  : forall (vs : list V) (c1 c2 : C) (j1 j2 : state C V hash),
  ~ set_eq j1 j2 ->
  NoDup vs ->
  NoDup (flat_map (fun v => [(c1, v, hash_state j1); (c2, v, hash_state j2)]) vs).
Proof.
  intros.
  induction vs.
  - simpl. constructor.
  - simpl.
    apply NoDup_cons_iff in H0.
    destruct H0 as [Hnin Hnodup]. constructor.
    + intro H0. destruct H0.
      * apply H. inversion H0; subst; clear H0.
        apply hash_state_injective in H3.
        now apply set_eq_comm.
      * apply Hnin. apply in_flat_map in H0.
        destruct H0 as [x [Hinx Hin]].
        destruct Hin as [Heq | [Heq | Heq]]; inversion Heq; subst; assumption.
    + apply IHvs in Hnodup. apply NoDup_cons_iff; split; try assumption. intro.
      apply Hnin. apply in_flat_map in H0. destruct H0 as [x [Hinx Hin]].
      destruct Hin as [Heq | [Heq | Heq]]; inversion Heq; subst; assumption.
Qed.

Lemma binary_justification_protocol_state
  {C V hash}  `{PS : ProtocolState C V hash}
  : forall vs c1 j1 c2 (j2 : state C V hash),
    protocol_state j1 ->
    protocol_state j2 ->
    ~ set_eq j1 j2 ->
    valid_estimate c1 j1 ->
    valid_estimate c2 j2 ->
    NoDup vs ->
    not_heavy (flat_map (fun v => [(c1, v, hash_state j1); (c2, v, hash_state j2)]) vs) ->
    protocol_state (flat_map (fun v => [(c1, v, hash_state j1); (c2, v, hash_state j2)]) vs).
Proof.
  intros.
  induction vs.
  - simpl. constructor.
  - apply NoDup_cons_iff in H4.
    destruct H4 as [Hanin Hnodup].
    simpl. apply protocol_state_cons with j1 c1 a; try assumption.
    + left; reflexivity.
    + simpl. rewrite eq_dec_if_true; try reflexivity.
      apply protocol_state_cons with j2 c2 a; try assumption.
      * left; reflexivity.
      * simpl. rewrite eq_dec_if_true; try reflexivity.
        apply IHvs; try assumption.
        apply not_heavy_subset with (flat_map (fun v : V => [(c1, v, hash_state j1); (c2, v, hash_state j2)]) (a :: vs))
        ; try assumption.
        intros x Hin. apply in_flat_map in Hin. apply in_flat_map.
        destruct Hin as [v [Hinv Hinx]].
        exists v. split; try assumption. right. assumption.
      * apply NoDup_cons_iff. split; try apply binary_justification_nodup; try assumption.
        intro. apply Hanin.
        apply in_flat_map in H4. destruct H4 as [x [Hinx Hin]].
        destruct Hin as [Heq | [Heq | Heq]]; inversion Heq; subst; assumption.
      * apply not_heavy_subset with (flat_map (fun v : V => [(c1, v, hash_state j1); (c2, v, hash_state j2)]) (a :: vs))
        ; try assumption.
        intros x Hin. apply in_flat_map.
        { destruct Hin as [Heq | Hin].
          - subst. exists a. split; try (left; reflexivity). right. left. reflexivity.
          - apply in_flat_map in Hin. destruct Hin as [v [Hinv Hin]].
            exists v. split; try assumption. right. assumption.
        }
    + apply NoDup_cons_iff. split.
      * intro.
        { destruct H4 as [Heq | Hin].
          - apply H1. inversion Heq; subst; clear Heq.
            apply hash_state_injective in H7.
            now apply set_eq_comm.
          - apply Hanin.
            apply in_flat_map in Hin.
            destruct Hin as [v [Hinv Hin]].
            destruct Hin as [Heq | [Heq | Heq]]; inversion Heq; subst; assumption.
        }
      * apply NoDup_cons_iff.
        { split.
          - intro. apply Hanin.
            apply in_flat_map in H4. destruct H4 as [v [Hinv Hin]].
            destruct Hin as [Heq | [Heq | Heq]]; inversion Heq; subst; assumption.
          - apply binary_justification_nodup; assumption.
        }
Qed.

Lemma fault_weight_max
  {C V hash}  `{Hsc3 : StrictlyComparable3 C V hash} `{Hmh : MessageHash (message C V hash) hash} `{Hm : Measurable V}
  : forall sigma : state C V hash,
  (fault_weight_state sigma <= sum_weights (set_map compare_eq_dec sender sigma))%R.
Proof.
  intros.
  apply sum_weights_incl; try apply set_map_nodup.
  unfold equivocating_senders.
  apply set_map_incl.
  intros x Hin.
  apply filter_In in Hin. destruct Hin; assumption.
Qed.


Lemma exist_equivocating_messages
  (C V hash : Type)  `{PS : ProtocolState C V hash}
  : forall vs,
  vs <> nil ->
  exists (j1 : state C V hash), exists j2, protocol_state j1 /\ protocol_state j2 /\ ~ set_eq j1 j2 /\
    exists c1, exists c2,
      valid_estimate c1 j1 /\ valid_estimate c2 j2 /\
      (forall v,
        In v vs  ->
          equivocating_messages (c1, v, hash_state j1) (c2, v, hash_state j2) = true).
Proof.
  destruct (estimator_total []) as [c Hc].
  intros.
  destruct vs; try (exfalso; apply H; reflexivity); clear H.
  destruct (estimator_total [(c, v, [])]) as [c' Hc'].
  destruct (estimator_total [(c', v, hash_state [(c, v, [])])]) as [c'' Hc''].
  exists []. exists [(c', v, hash_state [(c, v, [])])]. repeat split; try constructor.
  - apply (protocol_state_singleton c' v [(c, v, [])]) in Hc'; try constructor; try assumption.
    apply (protocol_state_singleton c v []) in Hc; try constructor; assumption.
  - intro. destruct H. apply incl_empty in H0. inversion H0.
  - exists c. exists c''. repeat split; try assumption.
    intros. unfold equivocating_messages. rewrite eq_dec_if_false.
    + rewrite eq_dec_if_true; try reflexivity.
      apply andb_true_iff. split.
      * unfold hash_state, inb; simpl.
        rewrite eq_dec_if_false; simpl; try reflexivity.
        intro. apply hash_message_injective in H0. inversion H0; subst.
      * simpl. reflexivity.
    + intro. inversion H0.
Qed.

Theorem non_triviality_decisions_on_properties_of_protocol_states
  (C V hash : Type)  `{PS : ProtocolState C V hash}
  : exists (p : pstate_light C V hash -> Prop), non_trivial_pstate_light p.
Proof.
  (* Get a pivotal validator and its complement set *)
  destruct exists_pivotal_validator as [v [vs [Hnodup [Hvnin [Hlte Hgt]]]]].
  (* Get a pair of messages in which that validator is equivocating *)
  destruct (exist_equivocating_messages C V hash (v :: vs)) as [j1 [j2 [Hj1ps [Hj2ps [Hneq12 [c1 [c2 [Hval1 [Hval2 Heqv]]]]]]]]].
  intro H; inversion H.
  (* The property is that of containing one equivocating partner message from this pivotal validator *)
  exists (fun (p : pstate_light C V hash) => In (c1,v,hash_state j1) (proj1_sig p)).
  split.
  - (* The first state which does satisfy this property is the state containing just that one message *)
    exists (exist protocol_state [(c1,v,hash_state j1)] (protocol_state_singleton c1 v j1 Hj1ps Hval1)).
    intros sigma H.
    apply H. left; reflexivity.
  - (* The second state which does not satisfy the property is the state containing the message's equivocation partner, as well as messages from all the other validators in the complement set *)
    assert (H_prot : protocol_state ((c2, v, hash_state j2) :: flat_map (fun v => [(c1, v, hash_state j1); (c2, v, hash_state j2)]) vs)).
    { apply protocol_state_cons with j2 c2 v; try assumption.
      * (* Proving that the message partner is in the new state *)
        left; reflexivity.
      * (* Proving that the new state without the message partner is a protocol state *)
        simpl. rewrite eq_dec_if_true; try reflexivity.
        (* This state is a protocol state if it's not too heavy *)
        apply binary_justification_protocol_state; try assumption.
        unfold not_heavy, fault_weight_state.
        apply Rle_trans with (sum_weights (set_map compare_eq_dec sender (flat_map (fun v0 : V => [(c1, v0, hash_state j1); (c2, v0, hash_state j2)]) vs))); try apply fault_weight_max.
        apply Rle_trans with (sum_weights vs); try assumption.
        apply sum_weights_incl; try assumption; try apply set_map_nodup.
        (* x is some arbitrary validator in vs *)
        intros x Hin.
        (* x has sent some message in the tl of the state *)
        apply set_map_exists in Hin.
        destruct Hin as [[(mc, mv) mj] [Hin Hveq]].
        simpl in Hveq. subst.
        apply in_flat_map in Hin.
        destruct Hin as [mv [Hinv Hinm]].
        destruct Hinm as [Hinm | [Hinm | Hinm]]
        ; inversion Hinm; subst; assumption.
      * (* Proving that the new state is duplicate-free *)
        constructor; try (apply binary_justification_nodup; assumption).
        rewrite in_flat_map. intro.
        destruct H as [v'' [Hinv Hinm]].
        apply Hvnin.
        destruct Hinm as [Hinm | [Hinm | Hinm]]
        ; inversion Hinm; subst; assumption.
      * (* Proving that the new state is not *)
        unfold not_heavy, fault_weight_state.
        apply Rle_trans with (sum_weights vs); try assumption.
        apply sum_weights_incl; try assumption; try apply set_map_nodup.
        unfold equivocating_senders.
        intros v0 Hinv0.
        apply set_map_exists in Hinv0.
        destruct Hinv0 as [[(c0, v0') j0] [Hin Heq]].
        simpl in Heq; subst.
        apply filter_In in Hin.
        destruct Hin as [Hin Hequiv].
        destruct Hin as [Heq | Hin]
        ; try (
          apply in_flat_map in Hin
          ; destruct Hin as [v0' [Hinv0 [Hin | [Hin | Hin]]]]
          ; inversion Hin; subst; clear Hin; assumption
        ).
        inversion Heq; subst; clear Heq. simpl in Hequiv.
        unfold equivocating_messages in Hequiv.
        rewrite eq_dec_if_true in Hequiv; try reflexivity.
        simpl in Hequiv.
        apply existsb_exists in Hequiv.
        destruct Hequiv as [[(mc, mv) mj] [Hin Hequiv]].
        apply in_flat_map in Hin.
        unfold equivocating_messages in Hequiv.
        destruct (compare_eq_dec (c0, v0, hash_state j2) (mc, mv, mj))
        ; try (rewrite eq_dec_if_true in Hequiv; try assumption; discriminate).
        rewrite eq_dec_if_false in Hequiv; try assumption.
        destruct (compare_eq_dec v0 mv); try discriminate; subst.
        destruct Hin as [v0' [Hinv0 [Hin | [Hin | Hin]]]]
        ; inversion Hin; subst; clear Hin; assumption. }
    exists (exist protocol_state ((c2, v, hash_state j2)  :: flat_map (fun v : V => [(c1, v, hash_state j1); (c2, v, hash_state j2)]) vs) H_prot).
    intros sigma Hincl Hin.
    destruct sigma as [sigma about_sigma].
    assert (Hpssigma := about_sigma).
    apply protocol_state_not_heavy in Hpssigma.
    apply (not_heavy_subset ((c1, v, hash_state j1) :: ((c2, v, hash_state j2) :: flat_map (fun v : V => [(c1, v, hash_state j1); (c2, v, hash_state j2)]) vs))) in Hpssigma.
    * unfold not_heavy in Hpssigma.
      unfold fault_weight_state in Hpssigma.
      assert (Heq : ((c1, v, hash_state j1)
                       :: (c2, v, hash_state j2)
                       :: flat_map (fun v : V => [(c1, v, hash_state j1); (c2, v, hash_state j2)]) vs)
                    = flat_map (fun v : V => [(c1, v, hash_state j1); (c2, v, hash_state j2)]) (v :: vs))
      by reflexivity.
      rewrite Heq in Hpssigma.
      apply (Rplus_gt_compat_r (weight v)) in Hgt.
      unfold Rminus in Hgt.
      rewrite Rplus_assoc in Hgt.
      rewrite Rplus_opp_l in Hgt.
      rewrite Rplus_0_r in Hgt.
      apply Rgt_lt in Hgt.
      apply (Rle_lt_trans _ _ _ Hpssigma) in Hgt.
      { apply (Rle_lt_trans (sum_weights (v :: vs))) in Hgt.
        - rewrite Rplus_comm in Hgt. simpl in Hgt.
          apply Rlt_irrefl with (weight v + sum_weights vs)%R.
          assumption.
        - apply sum_weights_incl.
          + constructor; assumption.
          + apply set_map_nodup.
          + intros v0 Hin0. unfold equivocating_senders.
            apply set_map_exists. exists (c1, v0, hash_state j1).
            split; try reflexivity.
            apply filter_In.
            split.
            * apply in_flat_map.
              exists v0. split; try assumption.
              left; reflexivity.
            * apply existsb_exists. exists (c2, v0, hash_state j2).
              split; try (apply Heqv; assumption).
              apply in_flat_map.
              exists v0. split; try assumption. right; left; reflexivity.
      }
    * intros msg Hinm.
      destruct Hinm as [Heq | Hinm]; subst; try assumption.
      apply Hincl. assumption.
Qed.

Theorem no_local_confluence_prot_state_light
  {C V hash}  `{PS : ProtocolState C V hash}
  : exists (a a1 a2 : pstate_light C V hash),
        pstate_light_rel a a1 /\ pstate_light_rel a a2 /\
        ~ exists (a' : pstate_light C V hash), pstate_light_rel a1 a' /\ pstate_light_rel a2 a'.
Proof.
  assert (H_useful := non_triviality_decisions_on_properties_of_protocol_states C V hash).
  destruct H_useful as [P [[ps1 about_ps1] [ps2 about_ps2]]].
  exists (exist protocol_state (state0 C V hash) protocol_state_nil).
  exists ps1, ps2. repeat split; try (red; simpl; easy).
  intro Habsurd. destruct Habsurd as [s [Hs1 Hs2]].
  spec about_ps1 s Hs1.
  spec about_ps2 s Hs2. contradiction.
Qed.

Lemma pstate_light_eq_dec
  {C V hash}  `{PS : ProtocolState C V hash}
  : forall (p1 p2 : pstate_light C V hash), {p1 = p2} + {p1 <> p2}.
Proof.
  intros p1 p2.
  now apply sigify_eq_dec.
Qed.

Lemma pstate_light_inhabited
  {C V hash}  `{PS : ProtocolState C V hash}
  : exists (p1 : pstate_light C V hash), True.
Proof. now exists (exist protocol_state (state0 C V hash) protocol_state_nil). Qed.

Lemma pstate_light_rel_refl
  {C V hash}  `{PS : ProtocolState C V hash}
  : Reflexive (@pstate_light_rel C V hash _ _ _ _ _ _ _ _ _ PS).
Proof.
  red. intro p.
  destruct p as [p about_p].
  red. simpl. easy. Qed.

Lemma pstate_light_rel_trans
  {C V hash}  `{PS : ProtocolState C V hash}
  : Transitive (@pstate_light_rel C V hash _ _ _ _ _ _ _ _ _ PS).
Proof.
  red; intros p1 p2 p3 H_12 H_23.
  destruct p1 as [p1 about_p1];
    destruct p2 as [p2 about_p2];
    destruct p3 as [p3 about_p3];
    simpl in *.
  unfold pstate_rel in *; simpl in *.
  now eapply incl_tran with p2.
Qed.

Instance level0_light
  {C V hash}  `{PS : ProtocolState C V hash}
  : PartialOrder (pstate_light C V hash) :=
  { A_eq_dec := pstate_light_eq_dec;
    A_inhabited := pstate_light_inhabited;
    A_rel := pstate_light_rel;
    A_rel_refl := pstate_light_rel_refl;
    A_rel_trans := pstate_light_rel_trans;
  }.

Instance level1_light
  {C V hash}  `{PS : ProtocolState C V hash}
  : PartialOrderNonLCish (pstate_light C V hash) :=
  { no_local_confluence_ish := no_local_confluence_prot_state_light; }.

(** Strong non-triviality **)
(* Defining reachablity in terms of message sending *)
Definition in_future
  {C V hash}
  (s1 s2 : state C V hash)
  :=
  incl s1 s2.

Definition next_future
  {C V hash}  `{Hsc3 : StrictlyComparable3 C V hash}
  (s1 s2 : state C V hash) :=
  exists (msg : message C V hash), set_eq (set_add compare_eq_dec msg s1) s2.

Definition in_past
  {C V hash}
  (s1 s2 : state C V hash)
  :=
  incl s2 s1.

Definition no_common_future
  {C V hash}  `{PS : ProtocolState C V hash}
  (s1 s2 : pstate_light C V hash) :=
  forall (s : pstate_light C V hash), in_future s1 s /\ in_future s2 s -> False.

Definition yes_common_future
  {C V hash}  `{PS : ProtocolState C V hash}
  (s1 s2 : pstate_light C V hash)
  :=
  exists (s : pstate_light C V hash), in_future s1 s /\ in_future s2 s.

Definition strong_nontriviality
  (C V hash : Type)
  `{PS : ProtocolState C V hash}
  :=
  (* For every state, there exists a state *)
  forall (s1 : pstate_light C V hash),
  exists (s2 : pstate_light C V hash),
    (* That is reachable in one step *)
    next_future s1 s2 /\
    (* And there exists a third state *)
    exists (s3 : pstate_light C V hash),
      (* Such that s1 and s3 share a common future *)
      yes_common_future s1 s3
      /\
      (* But s2 and s3 don't. *)
      no_common_future s2 s3.

(* Here's how to construct an equivocation *)
Lemma about_equivocating_messages
  {C V hash}  `{PS : ProtocolState C V hash}
  : forall j : state C V hash, protocol_state j ->
       forall v v',
         v <> v' ->
         equivocating_messages_prop (get_estimate j, v, hash_state j)
                                    (get_estimate ((get_estimate j, v', hash_state j) :: j), v, hash_state ((get_estimate j, v', hash_state j) :: j)).
Proof.
  intros j about_j v v' H_neq.
  repeat split.
  - intros H_absurd.
    inversion H_absurd.
    apply hash_state_injective in H1.
    inversion H1.
    spec H2 (get_estimate j, v', hash_state j) (in_eq (get_estimate j, v', hash_state j) j).
    now apply not_in_self in H2.
  - simpl; intros H_absurd.
    apply hash_state_in in H_absurd.
    inversion H_absurd.
    + inversion H. apply H_neq. easy.
    + now apply not_in_self in H.
  - intros H_absurd.
    apply hash_state_in in H_absurd.
    assert (H_useful := not_extx_in_x (get_estimate ((get_estimate j, v', hash_state j) :: j)) v ((get_estimate j, v', hash_state j) :: j) j).
    spec H_useful.
    { now apply copy_protocol_state.  }
    spec H_useful about_j.
    spec H_useful.
    now apply incl_tl.
    apply H_useful.
    apply hash_state_in.
    assumption.
Qed.

(* Defining the state that adds this minimal equivocation *)
Definition next_equivocation_state
  {C V hash} `{Hsc3 : StrictlyComparable3 C V hash} `{Hmh : MessageHash (message C V hash) hash}  `{He : Estimator (state C V hash) C}
  (j : state C V hash) (v v' : V) : state C V hash :=
  (* One equivocation partner *)
  (get_estimate j, v, hash_state j)
    ::
    (* Other equivocation partner *)
    (get_estimate ((get_estimate j, v', hash_state j) :: j), v, hash_state ((get_estimate j, v', hash_state j) :: j))
    ::
    (* Preparatory state *)
    (get_estimate j, v', hash_state j)
    ::
    (* Original state *)
    j.

(* Explicit instances of various incl results *)
Lemma next_equivocation_state_incl
  {C V hash} `{Hsc3 : StrictlyComparable3 C V hash} `{Hmh : MessageHash (message C V hash) hash}  `{He : Estimator (state C V hash) C}
  : forall (j : state C V hash) (v v' : V),
    incl j (next_equivocation_state j v v').
Proof.
  intros j v v' msg H_in.
  unfold next_equivocation_state.
  do 3 right.
  assumption.
Qed.

Lemma next_equivocation_state_keeps_messages
  {C V hash} `{Hsc3 : StrictlyComparable3 C V hash} `{Hmh : MessageHash (message C V hash) hash}  `{He : Estimator (state C V hash) C}
  : forall (j : state C V hash) (v v' : V) (msg : message C V hash),
    In msg j ->
    In msg (next_equivocation_state j v v').
Proof.
  apply next_equivocation_state_incl.
Qed.

Lemma next_equivocation_state_keeps_equivocators
  {C V hash} `{Hsc3 : StrictlyComparable3 C V hash} `{Hmh : MessageHash (message C V hash) hash}  `{He : Estimator (state C V hash) C}
  : forall (j : state C V hash) (v v' v0 : V),
    In v (equivocating_senders j) ->
    In v (equivocating_senders (next_equivocation_state j v v')).
Proof.
  intros.
  assert (H_incl := @equivocating_senders_incl C V hash _ _ _ _ _).
  spec H_incl j (next_equivocation_state j v v') (next_equivocation_state_incl j v v').
  now apply H_incl.
Qed.

Lemma next_equivocation_state_keeps_equivocating_messages
  {C V hash} `{Hsc3 : StrictlyComparable3 C V hash} `{Hmh : MessageHash (message C V hash) hash}  `{He : Estimator (state C V hash) C}
  : forall (j : state C V hash) (v v' : V) (msg : message C V hash),
    equivocating_in_state_prop msg j ->
    equivocating_in_state_prop msg (next_equivocation_state j v v').
Proof.
  intros.
  assert (H_incl := equivocating_in_state_incl).
  spec H_incl j (next_equivocation_state j v v') (next_equivocation_state_incl j v v').
  now apply H_incl.
Qed.


Lemma about_equivocating_messages_in_state_l
  {C V hash} `{PS : ProtocolState C V hash}
  : forall (j : state C V hash) v v',
    protocol_state j ->
    v <> v' ->
    equivocating_in_state_prop (get_estimate j, v, hash_state j)
                               (next_equivocation_state j v v').
Proof.
  intros j v v' about_j H_neq.
  exists (get_estimate ((get_estimate j, v', hash_state j) :: j), v, hash_state ((get_estimate j, v', hash_state j) :: j)).
  split.
  right.
  left. reflexivity.
  now apply about_equivocating_messages.
Qed.

Lemma about_equivocating_messages_in_state_r
  {C V hash} `{PS : ProtocolState C V hash}
  : forall (j : state C V hash) v v',
    protocol_state j ->
    v <> v' ->
    equivocating_in_state_prop (get_estimate ((get_estimate j, v', hash_state j) :: j), v, hash_state ((get_estimate j, v', hash_state j) :: j))
                               (next_equivocation_state j v v').
Proof.
  intros j v v' about_j H_neq.
  exists (get_estimate j, v, hash_state j).
  split.
  left. reflexivity.
  apply equivocating_messages_prop_swap.
  now apply about_equivocating_messages.
Qed.

Lemma about_equivocating_messages_add_equivocator
  {C V hash} `{PS : ProtocolState C V hash}
  : forall (j : state C V hash) v v',
    protocol_state j ->
      v <> v' ->
      In v (equivocating_senders (next_equivocation_state j v v')).
Proof.
  intros j v v' about_j H_neq.
  apply equivocating_senders_correct.
  exists (get_estimate j, v, hash_state j).
  split.
  unfold next_equivocation_state.
  left; tauto.
  split. reflexivity.
  now apply about_equivocating_messages_in_state_l.
Qed.

Lemma equivocating_senders_sorted_extend
  {C V hash} `{Hsc3 : StrictlyComparable3 C V hash} `{Hmhi : InjectiveMessageHash (message C V hash) hash}  `{He : Estimator (state C V hash) C}
  : forall (s : state C V hash) v,
    set_eq (equivocating_senders s)
           (equivocating_senders ((get_estimate s, v, hash_state s) :: s)).
Proof.
  intros.
  assert (H_useful := equivocating_senders_extend s (get_estimate s) v).
  rewrite <- H_useful.
  eapply set_eq_tran.
  apply set_eq_refl.
  apply set_eq_refl.
Qed.

Lemma equivocating_senders_fault_weight_eq
  {C V hash}  `{Hsc3 : StrictlyComparable3 C V hash} `{Hmh : MessageHash (message C V hash) hash} `{Hm : Measurable V}
  : forall s1 s2 : state C V hash,
    set_eq (equivocating_senders s1) (equivocating_senders s2) ->
    fault_weight_state s1 = fault_weight_state s2.
Proof.
  intros s1 s2 H_eq.
  apply set_eq_nodup_sum_weight_eq; try apply set_map_nodup.
  assumption.
Qed.

Lemma add_weight_one
  {C V hash}  `{Hsc3 : StrictlyComparable3 C V hash} `{Hmh : InjectiveMessageHash (message C V hash) hash} `{Hm : Measurable V} `{He : Estimator (state C V hash) C}
  : forall (j : state C V hash) (v' : V),
    fault_weight_state j =
    fault_weight_state ((get_estimate j, v', hash_state j) :: j).
Proof.
  intros.
  apply equivocating_senders_fault_weight_eq.
  apply equivocating_senders_sorted_extend.
Qed.

Lemma add_weight_two
  {C V hash}  `{Hsc3 : StrictlyComparable3 C V hash} `{Hmh : InjectiveMessageHash (message C V hash) hash} `{Hm : Measurable V} `{He : Estimator (state C V hash) C}
  : forall (j : state C V hash) (v v' : V),
    (fault_weight_state
      ((get_estimate ((get_estimate j, v', hash_state j) :: j), v, hash_state ((get_estimate j, v', hash_state j) :: j))
         :: (get_estimate j, v', hash_state j) :: j)) =
    fault_weight_state
      ((get_estimate j, v', hash_state j) :: j)%R.
Proof.
  intros.
  apply equivocating_senders_fault_weight_eq.
  apply set_eq_comm.
  apply equivocating_senders_sorted_extend.
Qed.

Lemma add_already_equivocating_sender
  {C V hash} `{PS : ProtocolState C V hash}
  : forall (s : state C V hash),
    protocol_state s ->
    forall (msg : message C V hash),
      In (sender msg) (equivocating_senders s) ->
        set_eq (equivocating_senders s)
               (equivocating_senders (msg :: s)).
Proof.
  intros s about_s msg H_in.
  split; intros v H_v_in.
  - unfold equivocating_senders.
    apply set_map_exists in H_v_in.
    destruct H_v_in as [msg' [H_v_in H_msg'_sender]].
    apply filter_In in H_v_in.
    rewrite <- H_msg'_sender.
    apply set_map_in.
    apply filter_in.
    right.
    tauto.
    rewrite equivocating_in_state_correct.
    destruct H_v_in.
    rewrite equivocating_in_state_correct in H0.
    destruct H0 as [msg'_partner H0].
    red. exists msg'_partner. split.
    destruct H0.
    right; assumption.
    tauto.
  - destruct (classic (v = sender msg)).
    + subst. assumption.
    + unfold equivocating_senders in H_v_in.
      apply set_map_exists in H_v_in.
      destruct H_v_in as [msg' [H_v_in H_msg'_sender]].
      apply filter_In in H_v_in.
      destruct H_v_in as [H_v_in H_equiv].
      rewrite equivocating_in_state_correct in H_equiv.
      destruct H_equiv as [msg'_partner [H_msg'_partner_in H_equiv]].
      rewrite <- H_msg'_sender.
      apply set_map_in.
      apply filter_in.
      destruct H_v_in.
      subst.
      contradiction.
      assumption.
      rewrite equivocating_in_state_correct.
      exists msg'_partner.
      split.  destruct H_msg'_partner_in.
      subst. destruct H_equiv.
      destruct H1. contradiction.
      assumption. assumption.
Qed.


Lemma equivocating_sender_add_in_sorted_iff
  {C V hash}  `{Hsc3 : StrictlyComparable3 C V hash} `{Hmh : MessageHash (message C V hash) hash}
  : forall (s : state C V hash) (msg : message C V hash) (v : V),
    In v (equivocating_senders (msg :: s)) <->
    (v = sender msg /\ equivocating_in_state_prop msg s) \/
    In v (equivocating_senders s).
Proof.
  intros s msg v. split; intros.
  -  apply equivocating_senders_correct in H.
     destruct H as [msg' [H_in [H_sender H_equiv]]].
     destruct H_in as [H_eq | H_noteq].
     + subst.
       destruct H_equiv as [msg_partner [H_msg_partner H_equiv]].
       left. split. reflexivity.
       exists msg_partner.
       destruct H_msg_partner. subst. inversion H_equiv.
       contradiction. tauto.
     + destruct H_equiv as [msg'_partner [H_msg'_partner H_equiv]].
       destruct H_msg'_partner as [H_eq' | H_noteq'].
       * subst. left. destruct H_equiv. split. tauto.
         exists msg'. split.
         assumption. split.
         auto. split. easy. tauto.
       * right.
         apply equivocating_senders_correct.
         exists msg'_partner. split. assumption.
         destruct H_equiv. split. subst; symmetry; tauto.
         red. exists msg'. split. assumption.
         apply equivocating_messages_prop_swap.
         red; tauto.
  - destruct H as [[H_sender H_equiv] | H_noteq].
    + subst.
      apply equivocating_senders_correct.
      destruct H_equiv as [msg_partner [H_msg_partner H_equiv]].
      exists msg_partner.
      split.
      right; assumption.
      split. destruct H_equiv. symmetry; tauto.
      exists msg. split. apply in_eq.
      rewrite equivocating_messages_prop_swap. assumption.
    + apply set_map_exists.
      apply set_map_exists in H_noteq.
      destruct H_noteq as [msg' [H_in H_sender]].
      exists msg'. split.
      rewrite filter_In.
      apply filter_In in H_in.
      split.
      right; tauto.
      destruct H_in.
      apply equivocating_in_state_correct in H0.
      destruct H0 as [msg'_partner about_msg'_partner].
      apply equivocating_in_state_correct.
      exists msg'_partner. split;
      try right; tauto.
      assumption.
Qed.

Lemma add_equivocating_sender
  {C V hash} `{PS : ProtocolState C V hash}
  : forall (s : state C V hash),
    protocol_state s ->
    forall (msg : message C V hash),
      (exists msg',
          In msg' s /\
          equivocating_messages_prop msg msg') ->
      set_eq (equivocating_senders (msg :: s))
             (set_add compare_eq_dec (sender msg) (equivocating_senders s)).
Proof.
  (* Because we're using set_add, we don't need to care about whether (sender msg) is already in (equivocating_senders s) *)
  intros s about_s msg [msg' [H_in H_equiv]].
  destruct (classic (In msg s)) as [H_msg_in | H_msg_out].
  - (* In the case that msg is already in s, *)
    (* Adding it does nothing to the state *)
    assert (H_ignore := set_add_ignore s msg H_msg_in).
    simpl in *. rewrite <- H_ignore.
    (* Adding the sender should do nothing to (equivocating_senders s) *)
    split.
    + intros v0 H_mem.
      (* The following is winding and painful *)
      unfold equivocating_senders in H_mem.
      rewrite set_map_exists in H_mem.
      destruct H_mem as [msg0 [H0_in H0_sender]].
      rewrite filter_In in H0_in.
      assert (H_senders := equivocating_senders_correct s).
      red in H_senders.
      destruct H0_in as [H0_in H0_equiv].
      apply set_add_iff.
      destruct (classic (msg = msg0)).
      * subst.
        left; reflexivity.
      * inversion H0_in. contradiction.
        clear H0_in.
        rewrite H_ignore in *.
        rewrite equivocating_in_state_correct in H0_equiv.
        destruct H0_equiv as [msg0_partner [H0_equivl H0_equivr]].
        inversion H0_equivl.
        subst. left.
        destruct H0_equivr. tauto.
        right.
        subst.
        spec H_senders (sender msg0).
        apply H_senders.
        exists msg0_partner.
        repeat split. assumption. red in H0_equivr; symmetry; tauto.
        exists msg0. split; try assumption.
        apply equivocating_messages_prop_swap.
        assumption.
    + intros v0 H_mem.
      (* The following will also be winding and painful *)
      destruct (classic (v0 = sender msg)).
      * subst.
        clear H_mem.
        apply set_map_in.
        apply filter_in.
        apply in_eq.
        rewrite equivocating_in_state_correct.
        exists msg'. split; try assumption.
        right; rewrite H_ignore; assumption.
      * rewrite set_add_iff in H_mem.
        destruct H_mem.
        contradiction. rewrite H_ignore in *.
        assert (H_goal := equivocating_senders_incl s (msg :: s)). spec H_goal. right; now apply incl_refl.
        now apply H_goal.
  - (* In the case that msg is not already in s, *)
    (* For all we know (sender msg) could already be in (equivocating_senders s) *)
    destruct (classic (In (sender msg) (equivocating_senders s))).
    + (* If (sender msg) is already in there, then adding it again does nothing *)
      assert (H_ignore : set_eq (set_add compare_eq_dec (sender msg) (equivocating_senders s)) (equivocating_senders s)).
      {  split; intros v H_v_in.
         apply set_add_iff in H_v_in.
         destruct H_v_in.
         subst; assumption.
         assumption.
         apply set_add_iff. right; assumption. }
      apply set_eq_comm in H_ignore.
      eapply set_eq_tran.
      2 : exact H_ignore.
      apply set_eq_comm.
      now apply add_already_equivocating_sender.
    + (* If (sender msg) is not already in there *)
      split; intros.
      * intros v0 H_in0.
        destruct (classic (v0 = sender msg)).
        ** subst.
           apply set_add_iff.
           tauto.
        ** apply set_add_iff.
           right.
           destruct msg as [[c v] j].
           apply equivocating_sender_add_in_sorted_iff in H_in0.
           destruct H_in0.
           destruct H1; contradiction.
           assumption.
      * intros v0 H_in0.
        destruct (classic (v0 = sender msg)).
        ** subst.
           apply set_add_iff in H_in0.
           destruct H_in0.
           apply set_map_in.
           apply filter_in.
           apply in_eq.
           rewrite equivocating_in_state_correct.
           red. exists msg'.
           split.
           right; assumption.
           assumption. contradiction.
        ** apply set_add_iff in H_in0.
           destruct H_in0.
           contradiction.
           apply set_map_exists in H1.
           destruct H1 as [msg0 [H_in0 H_sender0]].
           apply set_map_exists. exists msg0.
           split. 2 : assumption.
           apply filter_in.
           apply filter_In in H_in0.
           destruct H_in0.
           right; assumption.
           apply filter_In in H_in0.
           destruct H_in0.
           rewrite equivocating_in_state_correct.
           red. rewrite equivocating_in_state_correct in H2.
           red in H2.
           destruct H2 as [msg0_partner [H_in0 H_equiv0]].
           exists msg0_partner.
           split.
           right; assumption.
           assumption.
Qed.

Lemma add_weight_three
  {C V hash} `{PS : ProtocolState C V hash}
  : forall (j : state C V hash) (v v' : V),
    protocol_state j ->
    ~ In v (equivocating_senders j) ->
    v <> v' ->
    fault_weight_state (next_equivocation_state j v v') =
    (fault_weight_state
      ((get_estimate ((get_estimate j, v', hash_state j) :: j), v, hash_state ((get_estimate j, v', hash_state j) :: j)) ::
         ((get_estimate j, v', hash_state j) :: j)) +
     proj1_sig (weight v))%R.
Proof.
  intros j v v' about_j H_notin H_neq.
  assert (H_useful := @add_equivocating_sender C V hash _ _ _ _ _ _ _ _ _ _).
  spec H_useful ((get_estimate ((get_estimate j, v', hash_state j) :: j), v, hash_state ((get_estimate j, v', hash_state j) :: j)) :: ((get_estimate j, v', hash_state j) :: j)).
  spec H_useful.
  { apply protocol_state_cons with ((get_estimate j, v', hash_state j) :: j) (get_estimate ((get_estimate j, v', hash_state j) :: j)) v; try assumption; try apply get_estimate_correct.
    apply copy_protocol_state; try assumption; try apply get_estimate_correct.
    apply in_eq.
    rewrite set_remove_first.
    apply copy_protocol_state; try assumption; try apply get_estimate_correct.
    reflexivity.
    apply NoDup_cons.
    apply not_in_self.
    apply copy_protocol_state; try assumption.
    apply NoDup_cons. now apply not_in_self.
    now apply protocol_state_nodup in about_j.
    red.
    rewrite <- (add_weight_one ((get_estimate j, v', hash_state j) :: j) v).
    apply protocol_state_not_heavy; try assumption .
    apply copy_protocol_state. assumption. }
  spec H_useful (get_estimate j, v, hash_state j).
  spec H_useful.
  exists (get_estimate ((get_estimate j, v', hash_state j) :: j), v, hash_state ((get_estimate j, v', hash_state j) :: j)).
  split.
  apply in_eq. apply about_equivocating_messages; try assumption.
  (* Now. *)
  assert (H_inter := senders_fault_weight_eq (equivocating_senders
                  ((get_estimate j, v, hash_state j) ::
                     ((get_estimate
                           ((get_estimate j, v', hash_state j) :: j), v,
                        hash_state ((get_estimate j, v', hash_state j) :: j)) ::
                        ((get_estimate j, v', hash_state j) :: j)))) (set_add compare_eq_dec (sender (get_estimate j, v, hash_state j))
                  (equivocating_senders
                     ((get_estimate
                           ((get_estimate j, v', hash_state j) :: j), v,
                        hash_state ((get_estimate j, v', hash_state j) :: j)) ::
                        ((get_estimate j, v', hash_state j) :: j))))).
  spec H_inter.
  apply set_map_nodup.
  spec H_inter.
  apply set_add_nodup.
  apply set_map_nodup.
  spec H_inter H_useful.
  clear H_useful.
  unfold fault_weight_state.
  unfold next_equivocation_state.
  rewrite H_inter.
  simpl. clear H_inter.
  assert (H_rewrite := sum_weights_in v (set_add compare_eq_dec v
       (equivocating_senders
          ((get_estimate ((get_estimate j, v', hash_state j) :: j), v, hash_state ((get_estimate j, v', hash_state j) :: j)) ::
             (get_estimate j, v', hash_state j) :: j)))).
  spec H_rewrite.
  apply set_add_nodup. apply set_map_nodup.
  spec H_rewrite.
  rewrite set_add_iff. tauto.
  rewrite H_rewrite. clear H_rewrite.
  rewrite Rplus_comm.
  apply Rplus_eq_compat_r.
  rewrite add_remove_inverse.
  reflexivity.
  assert (H_useful := @equivocating_senders_sorted_extend C V hash _ _ _ _ _ _ _).
  assert (H_useful' := H_useful).
  spec H_useful j v'.
  spec H_useful' ((get_estimate j, v', hash_state j) :: j) v.
  assert (H_tran := set_eq_tran _ _ _ H_useful H_useful').
  clear H_useful H_useful'.
  intros H_absurd.
  destruct H_tran as [_ H_eq].
  spec H_eq v H_absurd.
  contradiction.
Qed.

Definition add_weight_under
  {C V hash}  `{Hsc3 : StrictlyComparable3 C V hash} `{Hmh : MessageHash (message C V hash) hash} `{Hrt : ReachableThreshold V}
  (s : state C V hash) (v : V) :=
  (fault_weight_state s + proj1_sig (weight v) <= proj1_sig threshold)%R.

Lemma equivocation_adds_fault_weight
  {C V hash} `{PS : ProtocolState C V hash}
  : forall (j : state C V hash),
    protocol_state j ->
    forall (v v' : V),
      ~ In v (equivocating_senders j) ->
      v <> v' ->
      fault_weight_state (next_equivocation_state j v v') =
      (fault_weight_state j + proj1_sig (weight v))%R.
Proof.
  intros j about_j v v' H_notin about_v.
  rewrite add_weight_three; try assumption.
  rewrite add_weight_two;
  rewrite <- add_weight_one; easy.
Qed.

(* Under not-overweight conditions, the resulting state is a protocol state *)
Theorem next_equivocation_protocol_state
  {C V hash} `{PS : ProtocolState C V hash}
  : forall j : state C V hash,
    protocol_state j ->
    forall v v',
      ~ In v (equivocating_senders j) ->
      v <> v' ->
      (* This is the most minimal condition we need about fault weight *)
      (add_weight_under j v ->
       protocol_state (next_equivocation_state j v v')).
Proof.
  intros j about_j v v' H_notin H_neq H_weight.
  assert (H_useful := about_equivocating_messages j about_j v v' H_neq).
  destruct H_useful as [H2_noteq [H2_sender [H2_left H2_right]]].
  (* Now. *)
  unfold next_equivocation_state.
  (* Peeling first message *)
  apply protocol_state_cons with j (get_estimate j) v; try apply get_estimate_correct; try apply about_j; try apply in_eq.
  rewrite set_remove_first. 2 : reflexivity.
  apply protocol_state_cons with ((get_estimate j, v', hash_state j) :: j) (get_estimate ((get_estimate j, v', hash_state j) :: j)) v; try assumption; try apply get_estimate_correct; try apply in_eq.
  apply copy_protocol_state; try assumption; try apply get_estimate_correct; try apply in_eq.
  rewrite set_remove_first. 2 : reflexivity.
  apply copy_protocol_state; try assumption; try apply get_estimate_correct.
  apply NoDup_cons; try apply not_in_self.
  apply copy_protocol_state; try assumption; try apply get_estimate_correct.
  apply NoDup_cons; try apply not_in_self; try assumption.
  now apply protocol_state_nodup in about_j.
  2 : apply NoDup_cons; try apply not_in_self; try assumption.
  2 : { intros H_or.
        apply in_inv in H_or.
        destruct H_or.
        inversion H.
        apply hash_state_injective in H2.
        destruct H2. spec H0 (get_estimate ((get_estimate j, v', hash_state j) :: j), v',
                              hash_state j).
        spec H0. apply in_eq.
        apply not_in_self_relaxed in H0. auto. assumption.
        inversion H. inversion H0. subst; auto.
        now apply not_in_self in H0. }
  red. rewrite add_weight_two.
  rewrite <- add_weight_one with j v'.
  now apply protocol_state_not_heavy in about_j.
  apply NoDup_cons; try apply not_in_self; try assumption.
  now apply copy_protocol_state.
  apply NoDup_cons; try apply not_in_self; try assumption.
  now apply protocol_state_nodup in about_j.
  red.
  replace ((get_estimate j, v, hash_state j)
      :: (get_estimate ((get_estimate j, v', hash_state j) :: j), v,
         hash_state ((get_estimate j, v', hash_state j) :: j))
         :: (get_estimate j, v', hash_state j) :: j)
    with (next_equivocation_state j v v').
    rewrite equivocation_adds_fault_weight;
      assumption.
    unfold next_equivocation_state. reflexivity.
Qed.

(* Under additional not-already-equivocating conditions, the resulting state actually adds weight *)
Lemma next_equivocation_adds_weight
  {C V hash} `{PS : ProtocolState C V hash}
  : forall (s : state C V hash),
    protocol_state s ->
    forall (v : V),
      (* If the weight is not over *)
      add_weight_under s v ->
      (* And the sender is not already equivocating *)
      ~ In v (equivocating_senders s) ->
      forall (v' : V),
        v <> v' ->
        (* Then we get a protocol state *)
        protocol_state (next_equivocation_state s v v') /\
        (* With increased weight *)
        fault_weight_state (next_equivocation_state s v v') =
        (fault_weight_state s + proj1_sig (weight v))%R.
Proof.
  intros s about_s v H_not_heavy H_notin v' H_neq.
  split.
  apply next_equivocation_protocol_state; assumption.
  rewrite equivocation_adds_fault_weight; easy.
Qed.

Fixpoint next_equivocation_rec'
  {C V hash} `{Hsc3 : StrictlyComparable3 C V hash} `{Hmh : MessageHash (message C V hash) hash}  `{He : Estimator (state C V hash) C}
  (s : state C V hash) (vs : list V) (v0 : V) : state C V hash
  :=
  match vs with
  | [] => s
  | hd :: tl => next_equivocation_state (next_equivocation_rec' s tl v0) hd v0
  end.

Lemma next_equivocations_keeps_messages
  {C V hash} `{Hsc3 : StrictlyComparable3 C V hash} `{Hmh : MessageHash (message C V hash) hash}  `{He : Estimator (state C V hash) C}
  : forall (s : state C V hash) (vs : list V) (v0 : V),
  forall (msg : message C V hash),
    In msg s ->
    In msg (next_equivocation_rec' s vs v0).
Proof.
  intros s vs v0 msg H_in.
  induction vs as [|hd tl IHvs].
  - assumption.
  - simpl.
    now apply next_equivocation_state_keeps_messages.
Qed.

Lemma next_equivocations_keeps_equivocating_senders
  {C V hash} `{Hsc3 : StrictlyComparable3 C V hash} `{Hmh : MessageHash (message C V hash) hash}  `{He : Estimator (state C V hash) C}
  : forall (s : state C V hash) (vs : list V) (v0 : V),
  forall (v : V),
    In v (equivocating_senders s) ->
    In v (equivocating_senders (next_equivocation_rec' s vs v0)).
Proof.
  intros s vs v0 v H_in.
  induction vs as [|hd tl IHvs].
  - assumption.
  - simpl.
    unfold next_equivocation_state.
    do 3 (rewrite equivocating_sender_add_in_sorted_iff; right).
    assumption.
Qed.

Lemma next_equivocation_equivocating_sender_cons
  {C V hash} `{PS : ProtocolState C V hash}
  : forall (s : state C V hash),
    protocol_state s ->
    forall (hd : V) (v0 v : V),
      v <> v0 ->
      In v (equivocating_senders (next_equivocation_state s hd v0)) <->
      v = hd \/ In v (equivocating_senders s).
Proof.
  intros s about_s hd v0 v H_neq.
  split; intro H.
  - unfold next_equivocation_state in H.
    apply equivocating_sender_add_in_sorted_iff in H.
    destruct H.
    tauto.
    apply equivocating_sender_add_in_sorted_iff in H.
    destruct H.
    tauto.
    apply equivocating_sender_add_in_sorted_iff in H.
    destruct H.
    simpl in H. destruct H. contradiction.
    tauto.
  - destruct H.
    subst.
    now apply about_equivocating_messages_add_equivocator.
    apply equivocating_senders_correct in H.
    destruct H as [msg [H_in [H_sender H_equiv]]].
    apply equivocating_senders_correct.
    exists msg. repeat split.
    unfold next_equivocation_state; right.
    right.
    right.
    assumption. assumption.
    now apply next_equivocation_state_keeps_equivocating_messages.
Qed.

Lemma next_equivocations_equivocating_senders_right
  {C V hash} `{Hsc3 : StrictlyComparable3 C V hash} `{Hmhi : InjectiveMessageHash (message C V hash) hash}  `{He : Estimator (state C V hash) C}
  : forall (s : state C V hash) (vs : list V) (v0 v : V),
    (In v vs -> v <> v0) ->
    In v (equivocating_senders (next_equivocation_rec' s vs v0)) ->
    In v vs \/ In v (equivocating_senders s).
Proof.
  intros s vs; induction vs as [|hd tl IHvs]; intros v0 v H_neq.
  - intros.
    simpl in H. tauto.
  - intros.
    spec IHvs v0 v.
    spec IHvs.
    { intros.
      spec H_neq. right; assumption.
      assumption. }
    simpl in H.
    apply equivocating_sender_add_in_sorted_iff in H.
    destruct H as [[ ? ? ] | ?].
    subst. left. simpl. tauto.
    apply equivocating_sender_add_in_sorted_iff in H.
    simpl in H.
    destruct H as [[ ? ? ] | ?].
    subst. left. apply in_eq.
    apply equivocating_sender_add_in_sorted_iff in H.
    simpl in H.
    destruct H as [[ ? ? ] | ?].
    subst.
    (* Now. H0 must be false. *)
    destruct H0 as [msg_absurd [H_in H_equiv]].
    assert (H_contra := non_equivocating_messages_extend msg_absurd (next_equivocation_rec' s tl v0) (get_estimate (next_equivocation_rec' s tl v0)) v0).
    spec H_contra H_in.
    apply equivocating_messages_correct in H_equiv.
    rewrite equivocating_messages_comm in H_equiv.
    rewrite H_equiv in H_contra.
    inversion H_contra.
    spec IHvs H. destruct IHvs.
    left; apply in_cons; assumption.
    tauto.
Qed.

Lemma next_equivocations_equivocating_senders_left_weak
  {C V hash} `{PS : ProtocolState C V hash}
  : forall (s : state C V hash) (vs : list V) (v0 v : V),
    protocol_state (next_equivocation_rec' s vs v0) ->
    (In v vs -> v <> v0) ->
    In v vs ->
    In v (equivocating_senders (next_equivocation_rec' s vs v0)).
Proof.
  intros s vs; induction vs as [|hd tl IHvs]; intros v0 v H_prot H_neq H_in.
  - inversion H_in.
  - assert (H_prot_sub : protocol_state (next_equivocation_rec' s tl v0)).
    { apply protocol_state_incl with (next_equivocation_rec' s (hd :: tl) v0).
      assumption.
      apply protocol_state_nodup in H_prot.
      simpl in H_prot.
      unfold next_equivocation_state in H_prot.
      do 3 (apply NoDup_cons_iff in H_prot; destruct H_prot as [_ H_prot]).
      assumption.
      intros msg H_in_msg.
      simpl; repeat right; assumption. }
    spec IHvs v0 v.
    spec IHvs H_prot_sub.
    spec IHvs. intros. apply H_neq. auto.
    (* Case analysis on where v is *)
    destruct H_in as [H_eq | H_in].
    * (* When we are looking at the hd element, *)
      subst.
      simpl.
      apply about_equivocating_messages_add_equivocator.
      assumption. apply H_neq. apply in_eq.
    * spec IHvs H_in.
      simpl.
      assert (H_useful := @equivocating_senders_incl C V hash _ _ _ _ _).
      spec H_useful (next_equivocation_rec' s tl v0) (next_equivocation_state (next_equivocation_rec' s tl v0) hd v0).
      spec H_useful.
      apply next_equivocation_state_incl.
      apply H_useful. assumption.
Qed.

Lemma next_equivocations_add_weights
  {C V hash} `{PS : ProtocolState C V hash}
  : forall (s : state C V hash),
    protocol_state s ->
    forall (vs : list V) (v0 : V),
      NoDup vs ->
      (* The sum weight is not over *)
      (fault_weight_state s + sum_weights vs <= proj1_sig threshold)%R ->
      (* None of the senders are already equivocating *)
      (forall (v : V),
          In v vs -> ~ In v (equivocating_senders s) /\ v <> v0) ->
      (* Then we end up with a protocol state *)
      protocol_state (next_equivocation_rec' s vs v0) /\
      (* And s recursively adds the sums of all the weights in vs *)
      fault_weight_state (next_equivocation_rec' s vs v0) =
      (fault_weight_state s + sum_weights vs)%R.
Proof.
  intros s about_s vs v0 H_nodup H_underweight H_disjoint.
  induction vs as [|hd tl IHvs].
  - (* Base case : no validators to add *)
    split. assumption.
    rewrite Rplus_0_r. reflexivity.
  - (* Induction step *)
    (* Discharging first premise *)
    spec IHvs.
    rewrite NoDup_cons_iff in H_nodup; tauto.
    (* Discharging second premise *)
    spec IHvs.
    simpl in H_underweight.
    apply (Rplus_le_reg_pos_r (fault_weight_state s + sum_weights tl) (proj1_sig (weight hd)) (proj1_sig threshold)).
    destruct (weight hd). firstorder.
    rewrite Rplus_assoc.
    rewrite (Rplus_comm (sum_weights tl) (proj1_sig (weight hd))).
    rewrite <- Rplus_assoc.
    rewrite <- Rplus_assoc in H_underweight.
    assumption.
    (* Discharging third premise *)
    spec IHvs.
    intros. spec H_disjoint v. spec H_disjoint.
    right; assumption.
    assumption.
    (* Now. *)
    destruct IHvs as [H_prot H_weight].
    spec H_disjoint hd (in_eq hd tl).
    assert (H_notin_tl : ~ In hd tl).
    { rewrite NoDup_cons_iff in H_nodup.
      tauto. }
    destruct H_disjoint as [H_disjoint H_neq].
    assert (H_rewrite := next_equivocations_equivocating_senders_right s tl v0 hd).
    spec H_rewrite.
    intros. assumption.
    split.
    + simpl.
      apply next_equivocation_protocol_state; try assumption.
      intros H_absurd.
      spec H_rewrite H_absurd.
      tauto.
      (* Need a helper lemma about weight adding here *)
      unfold add_weight_under.
      rewrite H_weight. simpl in H_underweight.
      rewrite <- Rplus_assoc in H_underweight.
      rewrite Rplus_assoc.
      rewrite (Rplus_comm (sum_weights tl) (proj1_sig (weight hd))).
      rewrite <- Rplus_assoc.
      assumption.
    + simpl.
      rewrite (Rplus_comm (proj1_sig (weight hd)) (sum_weights tl)).
      rewrite <- Rplus_assoc.
      rewrite <- H_weight.
      apply equivocation_adds_fault_weight; try assumption.
      intro H_absurd. spec H_rewrite H_absurd.
      tauto.
Qed.

Definition potentially_pivotal_state
  {C V hash} `{PS : ProtocolState C V hash}
  (v : V) (s : state C V hash) :=
  (* We say that v is a pivotal validator for some state s iff : *)
  (* v is not already equivocating in s *)
  ~ In v (equivocating_senders s) /\
  (* There is a remaining list of validators *)
  exists (vs : list V),
    (* That is duplicate-free *)
    NoDup vs /\
    (* Doesn't contain v *)
    ~ In v vs /\
    (* That are all not already equivocating in s *)
    (forall (v : V), In v vs -> ~ In v (equivocating_senders s)) /\
    (* That tip over s's fault weight but only with the help of v *)
    (sum_weights ((equivocating_senders s) ++ vs) <= proj1_sig threshold)%R /\
    (sum_weights ((equivocating_senders s) ++ vs) >
     proj1_sig threshold - proj1_sig (weight v))%R.

(* This is a critical lemma *)
Lemma all_pivotal_validator
  {C V hash : Type} `{PS : ProtocolState C V hash}
  : forall (s : state C V hash),
    protocol_state s ->
  exists (v : V),
    potentially_pivotal_state v s.
Proof.
  intros s about_s.
  destruct suff_val as [vs [Hvs Hweight]].
  remember (equivocating_senders s) as eqv_s.
  remember (set_diff compare_eq_dec vs eqv_s) as vss.
  assert (sum_weights (vss ++ eqv_s) > proj1_sig threshold)%R.
  { apply Rge_gt_trans with (sum_weights vs); try assumption.
    apply Rle_ge. apply sum_weights_incl; try assumption.
    - rewrite Heqvss. apply diff_app_nodup; try assumption.
      subst. unfold equivocating_senders. apply set_map_nodup.
    - rewrite Heqvss. intros a Hin. apply in_app_iff.
      rewrite set_diff_iff. apply or_and_distr_left.
      split; try (left; assumption).
      destruct (in_dec compare_eq_dec a eqv_s); (left; assumption) || (right; assumption).
  }
  apply pivotal_validator_extension in H.
  - destruct H as [vs' [Hnodup_vs' [Hincl_vs' [Hgt [v [Hin_v Hlt]]]]]].
    exists v. split.
    + subst. apply Hincl_vs' in Hin_v. apply set_diff_elim2 in Hin_v. assumption.
    + exists (set_remove compare_eq_dec v vs').
      assert (NoDup (set_remove compare_eq_dec v vs')) as Hnodup_remove
      ; try apply set_remove_nodup; try assumption.
      repeat split.
      * assumption.
      * try apply set_remove_elim; try assumption.
      * intros. apply set_remove_1 in H. apply Hincl_vs' in H. subst.
        apply set_diff_elim2 in H. assumption.
      * subst. rewrite sum_weights_app in *. rewrite Rplus_comm in Hlt.
        assumption.
      * apply Rlt_gt. apply Rplus_lt_reg_r with (proj1_sig (weight v)).
        unfold Rminus. rewrite Rplus_assoc. rewrite Rplus_opp_l.
        rewrite Rplus_0_r. apply Rgt_lt.
        apply Rge_gt_trans with (sum_weights (vs' ++ eqv_s)); try assumption.
        unfold Rge. right. rewrite Rplus_comm.
        rewrite sum_weights_app. rewrite (Rplus_comm (sum_weights (equivocating_senders s))) .
        rewrite <- Rplus_assoc. rewrite sum_weights_app. subst.
        apply Rplus_eq_compat_r.
        symmetry. apply sum_weights_in; try assumption.
  - subst. apply set_map_nodup.
  - subst. apply protocol_state_not_heavy. assumption.
  - subst. apply diff_app_nodup; try assumption.
    apply set_map_nodup.
Qed.

Theorem strong_nontriviality_full
  (C V hash : Type) `{PS : ProtocolState C V hash} `{Hit : InhabitedTwice V}
 : strong_nontriviality C V hash.
Proof.
  intros [s1 about_s1].
  destruct (all_pivotal_validator s1 about_s1) as [v [H_v [vs [H_nodup [H_v_notin [H_disjoint [H_under H_over]]]]]]].
  remember (exist protocol_state ((get_estimate s1,v,hash_state s1) :: s1) (copy_protocol_state s1 about_s1  v)) as s2.
  (* Book-keeping *)
  assert (H_s1_s2_senders : set_eq (equivocating_senders s1) (equivocating_senders (proj1_sig s2))) by (subst; apply equivocating_senders_sorted_extend).
  assert (H_s1_s2_weight : fault_weight_state s1 = fault_weight_state (proj1_sig s2)) by (subst; apply add_weight_one).
  exists s2.
  (* Proving next-step relation is trivial. *)
  split.
  exists (get_estimate s1,v,hash_state s1); subst; simpl in *.
  split; intros x H_in.
  rewrite set_add_iff in H_in. destruct H_in. subst. apply in_eq.
  right; tauto.
  inversion H_in; subst; rewrite set_add_iff; tauto.
  (* s3 is the state with equivocations from all the senders in vs recursively added to s1, in addition to (c,v,s1)'s equivocating partner message. *)
  (* First we add the equivocating partner message *)
  remember ((get_estimate ((get_estimate s1, get_distinct_sender v, hash_state s1) :: s1), v, hash_state ((get_estimate s1, get_distinct_sender v, hash_state s1) :: s1)) :: ((get_estimate s1, get_distinct_sender v, hash_state s1) :: s1)) as s1'.
  (* Book-keeping step *)
  assert (H_eq_senders : set_eq (equivocating_senders s1') (equivocating_senders s1)).
  { subst.
    assert (H_useful := equivocating_senders_sorted_extend ((get_estimate s1, get_distinct_sender v, hash_state s1) :: s1) v).
    eapply set_eq_tran.
    apply set_eq_comm. exact H_useful.
    apply set_eq_comm. apply equivocating_senders_sorted_extend. }
  assert (H_s_inter_weight : fault_weight_state s1' = fault_weight_state s1).
  { apply equivocating_senders_fault_weight_eq; assumption. }
  (* Now we are ready to construct s3 from s1' *)
  (* And if we have set up everything correctly, the premises at this point in the proof are sufficient. *)
  remember (next_equivocation_rec' s1' vs v) as s3.
  assert (about_s3 : protocol_state s3).
  { rewrite Heqs3. apply next_equivocations_add_weights.
    { subst.
      apply copy_protocol_state; try apply get_estimate_correct; try assumption.
      apply copy_protocol_state; try apply get_estimate_correct; try assumption. }
    assumption.
    rewrite H_s_inter_weight. rewrite sum_weights_app in H_under.
    assumption.
    intros. spec H_disjoint v0 H.
    destruct H_eq_senders as [H_left H_right].
    spec H_right v0.
    split. intro H_absurd. spec H_left v0 H_absurd.
    contradiction. intro H_absurd. subst. contradiction. }
  exists (exist protocol_state s3 about_s3).
  repeat split.
  - (* Proving that s1 and s3 share a common future *)
    red. exists (exist protocol_state s3 about_s3).
    split. simpl. red.
    red. subst.
    intros m0 H_in.
    (* Need to prove that next_equivocation_rec' doesn't drop messages *)
    apply next_equivocations_keeps_messages.
    do 2 right.
    assumption.
    apply incl_refl.
  - (* Proving that s2 and s3 don't share a common future *)
    (* Arbitrary state in both s2 and s3 leads to a contradiction *)
    red. intros [s about_s] H.
    destruct H as [H_in2 H_in3].
    assert (H_in2_copy := H_in2);
      assert (H_in3_copy := H_in3).
    (* Now we show that two equivocating messages are in s *)
    (* First message *)
    spec H_in2 (get_estimate s1,v,hash_state s1).
    spec H_in2.
    subst.
    apply in_eq.
    (* Second message *)
    spec H_in3 (get_estimate
                ((get_estimate s1, get_distinct_sender v, hash_state s1) :: s1), v,

               hash_state ((get_estimate s1, get_distinct_sender v, hash_state s1) ::  s1)).
    spec H_in3.
    { (* Proving that this message is in s3 *)
      assert (H_obv : In (get_estimate ((get_estimate s1, get_distinct_sender v, hash_state s1) ::  s1), v, hash_state ((get_estimate s1, get_distinct_sender v, hash_state s1) ::  s1)) s1').
      { subst.
        left. reflexivity. }
      apply (next_equivocations_keeps_messages s1' vs v) in H_obv.
      subst; assumption. }
    (* Now we prove that these two messages are equivocating *)
    simpl in *.
    assert (H_equiv : equivocating_messages_prop (get_estimate s1,v,hash_state s1)
                                                 (get_estimate ((get_estimate s1, get_distinct_sender v, hash_state s1) :: s1), v, hash_state ((get_estimate s1, get_distinct_sender v, hash_state s1) :: s1))).
    apply about_equivocating_messages.
    assumption. apply get_distinct_sender_correct.
    (* Now we say that v will be an equivocating sender inside s *)
    assert (H_v_in : In v (equivocating_senders s)).
    { apply equivocating_senders_correct.
      exists (get_estimate s1, v, hash_state s1).
      repeat split; try assumption.
      exists (get_estimate ((get_estimate s1, get_distinct_sender v, hash_state s1) :: s1), v, hash_state ( (get_estimate s1, get_distinct_sender v, hash_state s1) :: s1)).
      split. assumption. assumption. }
    clear H_in2 H_in3 H_equiv.
    (* Now we say that v's weight will be inside s's fault weight *)
    (* This part is a little tricky *)
    assert (H_equivocators_s : incl (v :: (equivocating_senders (proj1_sig s2) ++ vs)) (equivocating_senders s)).
    { intros v0 H_in0.
      destruct H_in0 as [H_hd | H_tl].
      + subst. assumption.
      + apply in_app_iff in H_tl.
        destruct H_tl as [H_left | H_right].
        * eapply equivocating_senders_incl.
          apply H_in2_copy.
          assumption.
        * assert (H_in_v0 : In v0 (equivocating_senders (next_equivocation_rec' s1' vs v))).
          { apply next_equivocations_equivocating_senders_left_weak.
            subst; assumption. intros.
            2 : assumption.
            intro H_absurd; subst; contradiction. }
          rewrite <- Heqs3 in H_in_v0.
          eapply equivocating_senders_incl.
          exact H_in3_copy.
          assumption.
    }
    assert (H_s_overweight : (proj1_sig (weight v) + fault_weight_state (proj1_sig s2) + sum_weights vs <= fault_weight_state s)%R).
    { replace ((proj1_sig (weight v) + fault_weight_state (proj1_sig s2) + sum_weights vs))%R with (sum_weights ([v] ++ (equivocating_senders (proj1_sig s2)) ++ vs)).
      apply sum_weights_incl.
      { (* Proving mutual NoDup *)
        apply nodup_append.
        apply NoDup_cons. intros; inversion 1.
        constructor.
        apply nodup_append.
        apply set_map_nodup. assumption.
        { intros. intro Habsurd. spec H_disjoint a Habsurd.
          destruct H_s1_s2_senders as [_ H_useful].
          spec H_useful a H. contradiction.
        }
        { intros. intro Habsurd. spec H_disjoint a H.
          destruct H_s1_s2_senders as [_ H_useful].
          spec H_useful a Habsurd. contradiction. }
        { intros. inversion H. intro Habsurd.
          apply in_app_iff in Habsurd. destruct Habsurd.
          destruct H_s1_s2_senders as [_ H_useful];
            spec H_useful a H1.
          subst; contradiction. subst; contradiction. inversion H0. }
        { intros. intro Habsurd.
          inversion Habsurd.
          apply in_app_iff in H. destruct H.
          destruct H_s1_s2_senders as [_ H_useful];
            spec H_useful a H.
          subst; contradiction. subst; contradiction. inversion H0. }
      }
      apply set_map_nodup. assumption.
      do 2 rewrite sum_weights_app.
      unfold fault_weight_state.
      simpl. ring. }
    apply protocol_state_not_heavy in about_s.
    red in about_s.
    assert (H_finale := Rle_trans _ _ _ H_s_overweight about_s). auto.
    clear -H_finale H_over H_s1_s2_weight.
    rewrite sum_weights_app in H_over.
    unfold fault_weight_state in H_s1_s2_weight at 1.
    rewrite H_s1_s2_weight in H_over.
    apply (Rplus_gt_compat_l (proj1_sig (weight v))) in H_over.
    replace (proj1_sig (weight v) + (proj1_sig threshold - proj1_sig (weight v)))%R with (proj1_sig threshold)%R in H_over by ring.
    rewrite <- Rplus_assoc in H_over.
    apply Rgt_not_le in H_over.
    contradiction.
Qed.
