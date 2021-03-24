From Coq Require Import List.
Import ListNotations.

From CasperCBC Require Import Lib.ListExtras VLSM.Common.

(** * VLSM Plans *)

Section plans.
  Context
    {message : Type}
    {T : VLSM_type message}.

  (** A plan is a (sequence of actions) which can be attempted on a
  given state to yield a trace.
  A [plan_item] is a singleton plan, and contains a label and an input
  which would allow to transition from any given state
  (note that we don't address validity for now)
  *)
  Record plan_item :=
    { label_a : label;
      input_a : option message
    }.

End plans.

Section apply_plans.

  Context
    {message : Type}
    {T : VLSM_type message}
    {transition : label -> state * option message -> state * option message}
    .

  (** If we don't concern ourselves with the validity of the traces obtained
  upon applying a plan, then a [VLSM_type] and a [transition] function
  suffice for defining plan application and related results.
  The advantage of this approach is that the same definition works for
  pre_loaded versions as well as for all constrained variants of a composition.
  *)

  (** Applying a plan (list of [plan_item]s) to a state we obtain a
  final state and a trace. We define that in the [_apply_plan] definition below
  using a folding operation on the [_apply_plan_folder] function.
  *)
  Definition _apply_plan_folder
    (a : plan_item)
    (sl : state * list transition_item)
    : state * list transition_item
    :=
    let (s, items) := sl in
    match a with {| label_a := l'; input_a := input' |} =>
      let (dest, out) := (transition l' (s, input')) in
      (dest
      , {| l := l';
           input := input';
           output := out;
           destination := dest
         |} :: items)
    end.

  Lemma _apply_plan_folder_additive
    (start : state)
    (aitems : list plan_item)
    (seed_items : list transition_item)
    : let (final, items) := fold_right _apply_plan_folder (start, []) aitems in
      fold_right _apply_plan_folder (start, seed_items) aitems = (final, items ++ seed_items).
  Proof.
    generalize dependent seed_items.
    induction aitems; simpl; intros; try reflexivity.
    destruct (fold_right _apply_plan_folder (start, []) aitems) as (afinal, aitemsX).
    rewrite IHaitems.
    destruct a. simpl. destruct (transition label_a0 (afinal, input_a0)) as (dest, out).
    reflexivity.
  Qed.

  Definition _apply_plan
    (start : state)
    (a : list plan_item)
    : list transition_item * state
    :=
    let (final, items) :=
      fold_right _apply_plan_folder (@pair state _ start []) (rev a) in
    (rev items, final).

  Lemma _apply_plan_last
    (start : state)
    (a : list plan_item)
    (after_a := _apply_plan start a)
    : last (map destination (fst after_a)) start = snd after_a.
  Proof.
    induction a using rev_ind; try reflexivity.
    unfold after_a. clear after_a. unfold _apply_plan.
    rewrite rev_unit. unfold _apply_plan in IHa.
    simpl in *.
    destruct (fold_right _apply_plan_folder (start, []) (rev a)) as (final, items)
      eqn:Happly.
    simpl in IHa.
    simpl.
    destruct x.
    destruct (transition label_a0 (final, input_a0)) as (dest,out) eqn:Ht.
    unfold fst. unfold snd.
    simpl. rewrite map_app. simpl. rewrite last_last. reflexivity.
  Qed.

  Lemma _apply_plan_app
    (start : state)
    (a a' : list plan_item)
    : _apply_plan start (a ++ a') =
      let (aitems, afinal) := _apply_plan start a in
      let (a'items, a'final) := _apply_plan afinal a' in
       (aitems ++ a'items, a'final).
  Proof.
    unfold _apply_plan.
    rewrite rev_app_distr.
    rewrite fold_right_app. simpl.
    destruct
      (fold_right _apply_plan_folder (@pair state _ start []) (rev  a))
      as (afinal, aitems) eqn:Ha.
    destruct
      (fold_right _apply_plan_folder (@pair state _ afinal []) (rev a'))
      as (final, items) eqn:Ha'.
    clear - Ha'.
    specialize (_apply_plan_folder_additive afinal (rev a') aitems) as Hadd.
    rewrite Ha' in Hadd.
    rewrite Hadd. rewrite rev_app_distr. reflexivity.
  Qed.

  Lemma _apply_plan_cons
    (start : state)
    (ai : plan_item)
    (a' : list plan_item)
    : _apply_plan start (ai :: a') =
      let (aitems, afinal) := _apply_plan start [ai] in
      let (a'items, a'final) := _apply_plan afinal a' in
       (aitems ++ a'items, a'final).
  Proof.
    replace (ai :: a') with ([ai] ++ a').
    apply _apply_plan_app.
    intuition.
  Qed.

  (** We can forget information from a trace to obtain a plan. *)
  Definition _transition_item_to_plan_item
    (item : transition_item)
    : plan_item
    := {| label_a := l item; input_a := input item |}.

  Definition _trace_to_plan
    (items : list transition_item)
    : list plan_item
    := map _transition_item_to_plan_item items.

  Definition _messages_a
    (a : list plan_item) :
    list message :=
    ListExtras.cat_option (List.map input_a a).

End apply_plans.

Section protocol_plans.

  Context
    {message : Type}
    (X : VLSM message)
    .

  (**
  We define several notations useful when we want to use the results above
  for a specific [VLSM], by instantiating the generic definitions with the
  corresponding [type] and [transition].
  *)

  Definition vplan_item := (@plan_item _ (type X)).
  Definition plan : Type := list vplan_item.
  Definition apply_plan := (@_apply_plan _ (type X) (vtransition X)).
  Definition trace_to_plan := (@_trace_to_plan _ (type X)).
  Definition apply_plan_app
    (start : vstate X)
    (a a' : plan)
    : apply_plan start (a ++ a') =
      let (aitems, afinal) := apply_plan start a in
      let (a'items, a'final) := apply_plan afinal a' in
       (aitems ++ a'items, a'final)
    := (@_apply_plan_app _ (type X) (vtransition X) start a a').
  Definition apply_plan_last
    (start : vstate X)
    (a : plan)
    (after_a := apply_plan start a)
    : last (map destination (fst after_a)) start = snd after_a
    := (@_apply_plan_last _ (type X) (vtransition X) start a).

  (** A plan is protocol w.r.t. a state if by applying it to that state we
  obtain a protocol trace sequence.
  *)
  Definition finite_protocol_plan_from
    (s : vstate X)
    (a : plan)
    : Prop :=
    finite_protocol_trace_from _ s (fst (apply_plan s a)).

  Lemma finite_protocol_plan_from_app_iff
    (s : vstate X)
    (a b : plan)
    (s_a := snd (apply_plan s a))
    : finite_protocol_plan_from s a /\ finite_protocol_plan_from s_a b <-> finite_protocol_plan_from s (a ++ b).
  Proof.
    unfold finite_protocol_plan_from.
    specialize (apply_plan_app s a b) as Happ.
    specialize (apply_plan_last s a) as Hlst.
    destruct (apply_plan s a) as (aitems, afinal) eqn:Ha.
    subst s_a.
    simpl in *.
    destruct (apply_plan afinal b) as (bitems, bfinal).
    rewrite Happ. simpl. clear Happ. subst afinal.
    apply finite_protocol_trace_from_app_iff.
  Qed.

  Lemma finite_protocol_plan_empty
    (s : vstate X)
    (Hpr : protocol_state_prop X s)  :
    finite_protocol_plan_from s [].
  Proof.
    apply finite_ptrace_empty.
    assumption.
  Qed.

  Lemma apply_plan_last_protocol
    (s : vstate X)
    (Hprs : protocol_state_prop X s)
    (a : plan)
    (Hpra : finite_protocol_plan_from s a)
    (after_a := apply_plan s a) :
    protocol_state_prop X (snd after_a).
  Proof.
    subst after_a.
    rewrite <- apply_plan_last.
    apply finite_ptrace_last_pstate.
    assumption.
  Qed.

  (** By extracting a plan from a [protocol_trace] based on a state @s@
  and reapplying the plan to the same state @s@ we obtain the original trace
  *)
  Lemma trace_to_plan_to_trace
    (s : vstate X)
    (tr : list (vtransition_item X))
    (Htr : finite_protocol_trace_from X s tr)
    : fst (apply_plan s (trace_to_plan tr)) = tr.
  Proof.
    induction tr using rev_ind; try reflexivity.
    apply finite_protocol_trace_from_app_iff in Htr.
    destruct Htr as [Htr Hx].
    specialize (IHtr Htr).
    setoid_rewrite map_app. rewrite apply_plan_app.
    specialize (apply_plan_last s (map _transition_item_to_plan_item tr)) as Hlst.
    destruct (apply_plan s (map _transition_item_to_plan_item tr)) as (aitems, afinal)
      eqn:Hapl.
    setoid_rewrite Hapl in IHtr. simpl in IHtr.
    simpl in *. subst.
    apply first_transition_valid in Hx.
    destruct Hx as [_ Ht].
    unfold _transition_item_to_plan_item. simpl. unfold apply_plan, _apply_plan.
    simpl.
    match goal with
    |- context[vtransition X ?l ?lst] => replace (vtransition X l lst) with (destination x, output x)
    end.
    destruct x.
    reflexivity.
  Qed.

  (** The plan extracted from a protocol trace is protocol w.r.t. the starting
  state of the trace.
  *)
  Lemma finite_protocol_trace_from_to_plan
    (s : vstate X)
    (tr : list (vtransition_item X))
    (Htr : finite_protocol_trace_from X s tr)
    : finite_protocol_plan_from s (trace_to_plan tr).
  Proof.
    unfold finite_protocol_plan_from.
    rewrite trace_to_plan_to_trace; assumption.
  Qed.

  (** Characterization of protocol plans. *)
  Lemma finite_protocol_plan_iff
    (s : vstate X)
    (a : plan)
    : finite_protocol_plan_from s a
    <-> protocol_state_prop X s
    /\ Forall (fun ai => option_protocol_message_prop X (input_a ai)) a
    /\ forall
        (prefa suffa : plan)
        (ai : plan_item)
        (Heqa : a = prefa ++ [ai] ++ suffa)
        (lst := snd (apply_plan s prefa)),
        vvalid X (label_a ai) (lst, input_a ai).
  Proof.
    induction a using rev_ind; repeat split; intros
    ; try
      ( apply finite_protocol_plan_from_app_iff in H
      ; destruct H as [Ha Hx]; apply IHa in Ha as Ha').
    - inversion H. assumption.
    - constructor.
    - destruct prefa; simpl in Heqa; discriminate Heqa.
    - destruct H as [Hs _]. constructor. assumption.
    - destruct Ha' as [Hs _].
      assumption.
    - destruct Ha' as [_ [Hmsgs _]].
      apply Forall_app. split; try assumption.
      repeat constructor. unfold finite_protocol_plan_from in Hx.
      remember (snd (apply_plan s a)) as lst.
      unfold apply_plan, _apply_plan in Hx. simpl in Hx.
      destruct x.
      destruct ( vtransition X label_a0 (lst, input_a0)) as (dest, out).
      simpl. simpl in Hx. inversion Hx. subst.
      destruct H6 as [[_ [Hom _]] _]. assumption.
    - assert (Hsuffa : suffa = [] \/ suffa <> []) by
        (destruct suffa; try (left; congruence); right; congruence).
      destruct Hsuffa.
      + subst. rewrite app_assoc in Heqa. rewrite app_nil_r in Heqa.
        apply app_inj_tail in Heqa. destruct Heqa; subst.
        unfold lst. clear lst.
        remember (snd (apply_plan s prefa)) as lst.
        unfold finite_protocol_plan_from in Hx.
        unfold apply_plan,_apply_plan in Hx. simpl in Hx.
        destruct ai.
        destruct ( vtransition X label_a0 (lst, input_a0)) as (dest, out).
        simpl. simpl in Hx. inversion Hx. subst.
        destruct H6 as [[_ [_ Hv]] _]. assumption.
      + apply exists_last in H. destruct H as [suffa' [x' Heq]]. subst.
        repeat rewrite app_assoc in Heqa.
        apply app_inj_tail in Heqa. rewrite <- app_assoc in Heqa. destruct Heqa; subst.
        destruct Ha' as [_ [_ Ha']].
        specialize (Ha' _ _ _ eq_refl). assumption.
    - destruct H as [Hs [Hinput Hvalid]].
      apply Forall_app in Hinput. destruct Hinput as [Hinput Hinput_ai].
      apply finite_protocol_plan_from_app_iff.
      assert (Ha : finite_protocol_plan_from s a); try (split; try assumption)
      ; try apply IHa; repeat split; try assumption.
      + intros.
        specialize (Hvalid prefa (suffa ++ [x]) ai).
        repeat rewrite app_assoc in *.
        subst a.
        specialize (Hvalid eq_refl). assumption.
      + unfold finite_protocol_plan_from.
        specialize (Hvalid a [] x).
        rewrite app_assoc in Hvalid. rewrite app_nil_r in Hvalid.
        specialize (Hvalid eq_refl).
        remember (snd (apply_plan s a)) as sa.
        unfold apply_plan, _apply_plan. simpl.
        destruct x.
        destruct (vtransition X label_a0 (sa, input_a0)) as (dest, out) eqn:Ht.
        simpl.
        apply Forall_inv in Hinput_ai. simpl in Hinput_ai.
        unfold finite_protocol_plan_from in Ha.
        apply finite_ptrace_last_pstate in Ha.
        specialize (apply_plan_last s a) as Hlst.
        simpl in Hlst, Ha.
        setoid_rewrite Hlst in Ha. setoid_rewrite <- Heqsa in Ha.
        repeat constructor; try assumption.
        exists out.
        replace (@pair (@state message (@type message X)) (option message) dest out)
          with (vtransition X label_a0 (sa, input_a0)).
        destruct Ha as [_oma Hsa].
        destruct Hinput_ai as [_s Hinput_a0].
        apply protocol_generated with _oma _s; assumption.
  Qed.

  (** Characterizing a singleton protocol plan as a protocol transition. *)
  Lemma finite_protocol_plan_from_one
    (s : vstate X)
    (a : plan_item) :
    let res := vtransition X (label_a a) (s, input_a a) in
    finite_protocol_plan_from s [a] <-> protocol_transition X (label_a a) (s, input_a a) res.
  Proof.
    split;
    intros;
    destruct a;
    unfold apply_plan,_apply_plan in *; simpl in *;
    unfold finite_protocol_plan_from in *;
    unfold apply_plan, _apply_plan in *; simpl in *.
    - match type of H with
      | context[let (_, _) := let (_, _) := ?t in _ in _] =>
        destruct t as [dest output] eqn : eq_trans
      end.
      inversion H. subst. setoid_rewrite eq_trans.
      assumption.
    - match type of H with
      | protocol_transition _ _ _ ?t =>
        destruct t as [dest output] eqn : eq_trans
      end.
      setoid_rewrite eq_trans.
      apply finite_ptrace_extend.
      apply finite_ptrace_empty.
      apply protocol_transition_destination in H; intuition.
      assumption.
  Qed.

  Definition preserves
    (a : plan)
    (P : vstate X -> Prop) :
    Prop :=
    forall (s : vstate X),
    (P s -> protocol_state_prop X s -> finite_protocol_plan_from s a -> P (snd (apply_plan s a))).

  Definition ensures
    (a : plan)
    (P : vstate X -> Prop) :
    Prop :=
    forall (s : vstate X),
    (protocol_state_prop X s -> P s -> finite_protocol_plan_from s a).

   (* If some property of a state guarantees a plan `b` applied to the state is protocol,
      and this property is preserved by the application of some other plan `a`,
      then these two plans can be composed and the application of `a ++ b` will also
      be protocol. *)

   Lemma plan_independence
    (a b : plan)
    (Pb : vstate X -> Prop)
    (s : state)
    (Hpr : protocol_state_prop X s)
    (Ha : finite_protocol_plan_from s a)
    (Hhave : Pb s)
    (Hensures : ensures b Pb)
    (Hpreserves : preserves a Pb) :
   finite_protocol_plan_from s (a ++ b).
   Proof.
    unfold ensures in *.
    unfold preserves in *.
    apply finite_protocol_plan_from_app_iff.
    split.
    - assumption.
    - remember (snd (apply_plan s a)) as s'.
      specialize (Hensures s').
      apply Hensures.
      rewrite Heqs'.
      apply apply_plan_last_protocol.
      intuition.
      intuition.
      rewrite Heqs'.
      apply Hpreserves.
      all : intuition.
   Qed.

End protocol_plans.
