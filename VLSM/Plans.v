Require Import List.
Import ListNotations.
From CasperCBC
  Require Import ListExtras VLSM.Common.

Section plans.
  Context
    {message : Type}
    {T : VLSM_type message}.

  Record plan_item :=
    { label_a : label;
      input_a : option message
    }.

End plans.

Section apply_plans.

  Context
    {message : Type}
    (X : VLSM message).

  Definition vplan_item {message : Type} (X : VLSM message) : Type
    := @plan_item message (type X).

  Definition vplan {message : Type} (X : VLSM message) : Type
    := list (vplan_item X).

  Definition apply_plan_folder
    (a : vplan_item X)
    (sl : vstate X * list (vtransition_item X))
    : vstate X * list (vtransition_item X)
    :=
    let (s, items) := sl in
    match a with {| label_a := l'; input_a := input' |} =>
      let (dest, out) := (vtransition X l' (s, input')) in
      (dest
      , {| l := l';
           input := input';
           output := out;
           destination := dest
         |} :: items)
    end.

  Lemma apply_plan_folder_additive
    (start : vstate X)
    (aitems : vplan X)
    (seed_items : list (vtransition_item X))
    : let (final, items) := fold_right apply_plan_folder (start, []) aitems in
      fold_right apply_plan_folder (start, seed_items) aitems = (final, items ++ seed_items).
  Proof.
    generalize dependent seed_items.
    induction aitems; simpl; intros; try reflexivity.
    destruct (fold_right apply_plan_folder (start, []) aitems) as (afinal, aitemsX).
    rewrite IHaitems.
    destruct a. simpl. destruct (vtransition X label_a0 (afinal, input_a0)) as (dest, out).
    reflexivity.
  Qed.

  Definition apply_plan
    (start : vstate X)
    (a : vplan X)
    : list (vtransition_item X) * vstate X
    :=
    let (final, items) :=
      fold_right apply_plan_folder (@pair (vstate X) _ start []) (rev a) in
    (rev items, final).

  Lemma apply_plan_last
    (start : vstate X)
    (a : vplan X)
    (after_a := apply_plan start a)
    : last (map destination (fst after_a)) start = snd after_a.
  Proof.
    induction a using rev_ind; try reflexivity.
    unfold after_a. clear after_a. unfold apply_plan.
    rewrite rev_unit. unfold apply_plan in IHa.
    simpl in *.
    destruct (fold_right apply_plan_folder (start, []) (rev a)) as (final, items)
      eqn:Happly.
    simpl in IHa.
    simpl.
    destruct x.
    destruct (vtransition X label_a0 (final, input_a0)) as (dest,out) eqn:Ht.
    unfold fst. unfold snd.
    simpl. rewrite map_app. simpl. rewrite last_last. reflexivity.
  Qed.

  Lemma apply_plan_app
    (start : vstate X)
    (a a' : vplan X)
    : apply_plan start (a ++ a') =
      let (aitems, afinal) := apply_plan start a in
      let (a'items, a'final) := apply_plan afinal a' in
       (aitems ++ a'items, a'final).
  Proof.
    unfold apply_plan.
    rewrite rev_app_distr.
    rewrite fold_right_app. simpl.
    destruct
      (fold_right apply_plan_folder (@pair (vstate X) _ start []) (rev  a))
      as (afinal, aitems) eqn:Ha.
    destruct
      (fold_right apply_plan_folder (@pair (vstate X) _ afinal []) (rev a'))
      as (final, items) eqn:Ha'.
    clear - Ha'.
    specialize (apply_plan_folder_additive afinal (rev a') aitems) as Hadd.
    rewrite Ha' in Hadd.
    rewrite Hadd. rewrite rev_app_distr. reflexivity.
  Qed.

  Definition finite_protocol_plan_from
    (s : vstate X)
    (a : vplan X)
    : Prop :=
    finite_protocol_trace_from _ s (fst (apply_plan s a)).

  Lemma finite_protocol_plan_from_app_iff
    (s : vstate X)
    (a b : vplan X)
    (s_a := snd (apply_plan s a))
    : finite_protocol_plan_from s a /\ finite_protocol_plan_from s_a b <-> finite_protocol_plan_from s (a ++ b).
  Proof.
    unfold finite_protocol_plan_from.
    specialize (apply_plan_app s a b) as Happ.
    specialize (apply_plan_last s a) as Hlst.
    destruct (apply_plan s a) as (aitems, afinal).
    simpl in *. unfold s_a in *. clear s_a.
    destruct (apply_plan afinal b) as (bitems, bfinal).
    rewrite Happ. simpl. clear Happ. subst afinal.
    apply finite_protocol_trace_from_app_iff.
  Qed.

  Definition transition_item_to_plan_item
    (item : vtransition_item X)
    : vplan_item X
    := {| label_a := l item; input_a := input item |}.

  Definition trace_to_plan
    (items : list (vtransition_item X))
    : vplan X
    := map transition_item_to_plan_item items.

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
    unfold trace_to_plan.
    rewrite map_app. simpl. rewrite apply_plan_app.
    unfold trace_to_plan in IHtr.
    specialize (apply_plan_last s (map transition_item_to_plan_item tr)) as Hlst.
    destruct (apply_plan s (map transition_item_to_plan_item tr)) as (aitems, afinal).
    simpl in *. subst.
    inversion Hx. subst. clear -H3.
    unfold transition_item_to_plan_item. simpl. unfold apply_plan.
    simpl.
    destruct H3 as [_ Ht].
    replace
      (@vtransition message X l
      (@pair (@vstate message X) (option message)
         (@last (@state message (@type message X))
            (@map (@transition_item message (@type message X))
               (@state message (@type message X))
               (@destination message (@type message X)) tr) s) iom))
      with (s0, oom).
    reflexivity.
  Qed.

  Lemma finite_protocol_trace_from_to_plan
    (s : vstate X)
    (tr : list (vtransition_item X))
    (Htr : finite_protocol_trace_from X s tr)
    : finite_protocol_plan_from s (trace_to_plan tr).
  Proof.
    unfold finite_protocol_plan_from.
    rewrite trace_to_plan_to_trace; assumption.
  Qed.

  Lemma finite_protocol_plan_iff
    (s : vstate X)
    (a : vplan X)
    : finite_protocol_plan_from s a
    <-> protocol_state_prop X s
    /\ Forall (fun ai => option_protocol_message_prop X (input_a ai)) a
    /\ forall
        (prefa suffa : vplan X)
        (ai : vplan_item X)
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
      unfold apply_plan in Hx. simpl in Hx.
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
        unfold apply_plan in Hx. simpl in Hx.
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
        repeat rewrite app_assoc in *. rewrite <- Heqa in Hvalid.
        specialize (Hvalid eq_refl). assumption.
      + unfold finite_protocol_plan_from.
        specialize (Hvalid a [] x).
        rewrite app_assoc in Hvalid. rewrite app_nil_r in Hvalid.
        specialize (Hvalid eq_refl).
        remember (snd (apply_plan s a)) as sa.
        unfold apply_plan. simpl.
        destruct x.
        destruct (vtransition X label_a0 (sa, input_a0)) as (dest, out) eqn:Ht.
        simpl.
        apply Forall_inv in Hinput_ai. simpl in Hinput_ai.
        unfold finite_protocol_plan_from in Ha.
        apply finite_ptrace_last_pstate in Ha.
        specialize (apply_plan_last s a) as Hlst.
        simpl in Hlst. rewrite Hlst in Ha. rewrite <- Heqsa in Ha.
        repeat constructor; try assumption.
        exists out.
        replace (@pair (@state message (@type message X)) (option message) dest out)
          with (vtransition X label_a0 (sa, input_a0)).
        destruct Ha as [_oma Hsa].
        destruct Hinput_ai as [_s Hinput_a0].
        apply protocol_generated with _oma _s; assumption.
  Qed.

End apply_plans.
