Require Import List.
Import ListNotations.
From CasperCBC
  Require Import VLSM.Common.

Section actions.
  Context
      {message : Type}
      {T : VLSM_type message}.

  Record action_item :=
    {   label_a : label;   
        input_a : option message
    }.
    
End actions.

Section apply_actions.

  Context
      {message : Type}
      (X : VLSM message)
      .

Definition vaction_item {message : Type} (X : VLSM message) : Type
    := @action_item message (type X).

Definition vaction {message : Type} (X : VLSM message) : Type
    := list (vaction_item X).

  Definition apply_action_folder
    (a : vaction_item X)
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

  Definition apply_action
    (start : vstate X) 
    (a : vaction X)
    : list (vtransition_item X) * vstate X
    :=
    let (final, items) := fold_right apply_action_folder (start, []) (rev a) in
    (rev items, final).

  Lemma apply_action_last
    (start : vstate X) 
    (a : vaction X)
    (after_a := apply_action start a)
    : last (map destination (fst after_a)) start = snd after_a.
  Proof.
    induction a using rev_ind; try reflexivity.
    unfold after_a. clear after_a. unfold apply_action.
    rewrite rev_unit. unfold apply_action in IHa.
    simpl in *.
    destruct (fold_right apply_action_folder (start, []) (rev a)) as (final, items)
      eqn:Happly.
    simpl in IHa.
    simpl.
    destruct x.
    destruct (vtransition X label_a0 (final, input_a0)) as (dest,out) eqn:Ht.
    unfold fst. unfold snd.
    simpl. rewrite map_app. simpl. rewrite last_last. reflexivity.
  Qed.

  Lemma apply_action_app
    (start : state)
    (a a' : vaction X)
    : let (aitems, afinal) := apply_action start a in
      let (a'items, a'final) := apply_action afinal a' in
      apply_action start (a ++ a') = (aitems ++ a'items, a'final).
  Proof.
    induction a' using rev_ind.
    - simpl. rewrite app_nil_r. destruct (apply_action start a) as (aitems, afinal).
      rewrite app_nil_r. reflexivity.
    - rewrite app_assoc. unfold apply_action at 2. unfold apply_action at 2.
      repeat rewrite rev_unit. simpl.
      destruct (apply_action start a) as (aitems, afinal).
      unfold apply_action in IHa'.
      destruct (fold_right apply_action_folder (afinal, []) (rev a')) as (final, items).
      simpl in *.
      destruct
        (@fold_right
        (prod (@vstate message X) (list (@vtransition_item message X)))
        (@vaction_item message X) apply_action_folder
        (@pair (@vstate message X) (list (@vtransition_item message X))
           start (@nil (@vtransition_item message X)))
        (@rev (@vaction_item message X)
           (@app (@vaction_item message X) a a')))
        as (final', items').
      destruct x. simpl.
      inversion IHa'. subst final'.
      destruct (vtransition X label_a0 (final, input_a0)) as (dest, out).
      f_equal. simpl.
      rewrite app_assoc. f_equal. assumption.
  Qed.
  
  Definition protocol_action
    (s : state)
    (a : vaction X)
    : Prop :=
    finite_protocol_trace_from _ s (fst (apply_action s a)).
  
  Lemma protocol_action_app_iff
    (s : state)
    (a b : vaction X)
    (s_a := snd (apply_action s a))
    : protocol_action s a /\ protocol_action s_a b <-> protocol_action s (a ++ b).
  Proof.
    unfold protocol_action.
    specialize (apply_action_app s a b) as Happ.
    specialize (apply_action_last s a) as Hlst.
    destruct (apply_action s a) as (aitems, afinal).
    simpl in *. unfold s_a in *. clear s_a.
    destruct (apply_action afinal b) as (bitems, bfinal).
    rewrite Happ. simpl. clear Happ. subst afinal.
    apply finite_protocol_trace_from_app_iff.
  Qed.
End apply_actions.