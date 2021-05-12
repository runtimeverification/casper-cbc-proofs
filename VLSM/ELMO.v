From Coq Require Import ssreflect ssrfun ssrbool.

Require Import
  List Coq.Vectors.Fin
  Arith.Compare_dec Lia
  Program Reals Lra ListSet Nat
  Coq.Logic.FinFun
  .
Import ListNotations.
From CasperCBC
  Require Import
    Preamble
    Lib.Measurable
    Lib.ListExtras
    VLSM.Common
    VLSM.Composition
    VLSM.Validating
    VLSM.Equivocation
    .

Require Import List.
    
Inductive Label := Receive | Send.

Inductive Prestate : Type :=
| Cprestate: list Observation -> Prestate
with
Observation : Type :=
| Cobservation: Label -> Premessage -> nat -> Observation
with
Premessage : Type :=
| Cpremessage: Prestate -> nat -> Premessage
.

Section induction_principle.
  Context
    (Pps : Prestate -> Prop)
    (Plo : list Observation -> Prop)
    (Pob : Observation -> Prop)
    (Ppm : Premessage -> Prop)
    (Hps : forall (l : list Observation), Plo l -> Pps (Cprestate l))
    (Hlonil : Plo nil)
    (Hlocons : forall (a : Observation) (l : list Observation),
        Pob a ->
        Plo l ->
        Plo (a::l)
    )
    (Hob : forall (l : Label) (p : Premessage) (n : nat),
        Ppm p ->
        Pob (Cobservation l p n))
    (Hpm : forall (p : Prestate) (n : nat),
        Pps p ->
        Ppm (Cpremessage p n))
  .

  Fixpoint
    Prestate_mut_ind (p : Prestate) : Pps p :=
    let ListObservation_mut_ind := (fix ListObservation_mut_ind (lo : list Observation) : Plo lo :=
    match lo as lo0 return (Plo lo0) with
    | [] => Hlonil
    | y::lo0 => Hlocons y lo0 (Observation_mut_ind y) (ListObservation_mut_ind lo0)
    end) in
    match p as p0 return (Pps p0) with
    | Cprestate l => Hps l (ListObservation_mut_ind l)
    end
  with
  Observation_mut_ind (o : Observation) : Pob o :=
    match o as o0 return (Pob o0) with
    | Cobservation l p n => Hob l p n (Premessage_mut_ind p)
    end
  with
  Premessage_mut_ind (p : Premessage) : Ppm p :=
    match p as p0 return (Ppm p0) with
    | Cpremessage p0 n => Hpm p0 n (Prestate_mut_ind p0)
    end
  .
  
End induction_principle.


Fixpoint
  Prestate_weight (p : Prestate) : nat :=
  let ListObservation_weight := (fix ListObservation_weight (lo : list Observation) : nat :=
                                    match lo as lo0 return nat with
                                    | [] => 0
                                    | y::lo0 => S ((Observation_weight y) + (ListObservation_weight lo0))
                                    end) in
  match p as p0 return nat with
  | Cprestate l => 1 + (ListObservation_weight l)
  end
with
Observation_weight (o : Observation) : nat :=
  match o as o0 return nat with
  | Cobservation l p n => 1 + (Premessage_weight p)
  end
with
Premessage_weight (p : Premessage) : nat :=
  match p as p0 return nat with
  | Cpremessage p0 n => 1 + (Prestate_weight p0)
  end
.

Definition ListObservation_weight := (fix ListObservation_weight (lo : list Observation) : nat :=
                                    match lo as lo0 return nat with
                                    | [] => 0
                                    | y::lo0 => S ((Observation_weight y) + (ListObservation_weight lo0))
                                    end).

Instance Label_eqdec : EqDecision Label.
Proof.
  intros l1 l2.
  unfold Decision.
  decide equality.
Qed.

 

Lemma Prestate_eqdec : forall (s1 s2 : Prestate), {s1 = s2} + {s1 <> s2}
with  Observation_eqdec : forall (o1 o2 : Observation), {o1 = o2} + {o1 <> o2}
with  Premessage_eqdec : forall (m1 m2 : Premessage), {m1 = m2} + {m1 <> m2}.
Proof.
  decide equality. decide equality. decide equality. decide equality.
  decide equality. decide equality. decide equality.
Qed.

Instance Prestate_eqdec' : EqDecision Prestate.
Proof.
  intros x y.
  apply Prestate_eqdec.
Qed.

Instance Observation_eqdec' : EqDecision Observation.
Proof.
  intros x y.
  apply Observation_eqdec.
Qed.

Instance Premessage_eqdec' : EqDecision Premessage.
Proof.
  intros x y.
  apply Premessage_eqdec.
Qed.

Definition dummy_prestate := Cprestate [].
Definition dummy_premessage := Cpremessage dummy_prestate 0.
Definition dummy_observation := Cobservation Receive dummy_premessage 0.


Definition observationsOf (prs : Prestate) : list Observation :=
  match prs with
  | Cprestate l => l
  end.

Definition labelOf (ob : Observation) : Label :=
  match ob with
  | Cobservation lbl _ _ => lbl
  end.

Definition messageOf (ob : Observation) : Premessage :=
  match ob with
  | Cobservation _ msg _ => msg
  end.

Definition witnessOf (ob : Observation) : nat :=
  match ob with
  | Cobservation _ _ w => w
  end.

Definition isWitnessedBy (component : nat) (ob : Observation) : bool :=
  bool_decide (witnessOf ob = component).

Definition isReceive (ob : Observation) : bool :=
  match ob with
  | Cobservation Receive _ _ => true
  | _ => false
  end.

Definition isSend (ob : Observation) : bool :=
  match ob with
  | Cobservation Send _ _ => true
  | _ => false
  end.

Definition stateOf (m : Premessage) : Prestate :=
  match m with
  | Cpremessage s _ => s
  end.

Definition authorOf (m : Premessage) : nat :=
  match m with
  | Cpremessage _ a => a
  end.


Instance elmo_type : VLSM_type Premessage :=
  {| state := Prestate;
     Common.label := Label;
  |}.

Definition elmo_state : Type := @state Premessage elmo_type.

Definition elmo_initial_state_prop (ps : elmo_state) : Prop :=
  observationsOf ps = [].

Definition elmo_initial_state
  := sig elmo_initial_state_prop.

Definition elmo_s0 : elmo_initial_state.
Proof.
  unfold elmo_initial_state.
  exists (Cprestate []).
  unfold elmo_initial_state_prop.
  reflexivity.
Defined.

Definition elmo_m0 : Premessage := Cpremessage (Cprestate []) 0.

Definition elmo_sig : VLSM_sign elmo_type :=
  {| initial_state_prop := elmo_initial_state_prop
     ; s0 := elmo_s0
     ; initial_message_prop := (fun x => False)
     ; m0 := elmo_m0
     ; l0 := Receive
     ;
  |}.


(* Check that every message received or sent in m has been received in the prefix by the component *)
Definition fullNode (m : Premessage) (prefix: list Observation) (component: nat) : bool :=
  fold_right andb true
             (map (fun (ob2 : Observation) =>
                     match (labelOf ob2) with
                     | Receive =>
                       if
                         (In_dec Observation_eqdec (Cobservation Receive (messageOf ob2) component) prefix)
                       then true else false
                     | Send => false
                     end
                  )
                  (observationsOf (stateOf m))
             ).


Definition nth_update {A : Type} (l : list A) (idx : nat) (v : A) : list A :=
  firstn idx l ++ cons v (skipn (S idx) l).

Program Definition update
           (m : Premessage)
           (component : nat)
           (weights : list pos_R)
           (treshold : R)
           (curState : list Prestate)
           (curEq : set nat)
  : bool * (list Prestate) * (set nat) :=
  let p := stateOf m in
  let a := authorOf m in
  let lp := length (observationsOf p) in
  let ca := nth a curState dummy_prestate in
  let la := length (observationsOf (ca)) in
  if andb (la <=? lp)
          (bool_decide ((firstn la (observationsOf p))=(observationsOf ca))) then
    (true,
     nth_update curState a (Cprestate (observationsOf p ++ [Cobservation Send m a])),
     curEq)
  else
    if andb (S lp <=? la)
            (andb
               (bool_decide ((firstn lp (observationsOf ca))=(observationsOf p)))
               (bool_decide ((nth lp (observationsOf ca) dummy_observation)=(Cobservation Send m a)))) then
      (true, curState, curEq)
    else
      let newEq := curEq in
      if (Rlt_dec (@sum_weights _ (Build_Measurable _ (fun idx => nth idx weights (exist _ 1%R _))) newEq) treshold) then
        (false, curState, curEq)
      else
        (true, curState, newEq).
Next Obligation.
  lra.
Defined.


Definition isProtocol_step
           (component : nat) (weights : list pos_R) (treshold : R) (observations : list Observation)
           (args : bool * nat * list Prestate * set nat) (ob : Observation)
  : bool * nat * list Prestate * set nat
  :=
    let: (result, i,  curState, curEq) := args in
    match result with
    | false => args
    | true =>
      let l := labelOf ob in
      let m := messageOf ob in
      let p := stateOf m in
      let a := authorOf m in
      let w := witnessOf ob in
      let prefix := firstn i observations in
      let i := S i in
      (* w <> component *)
      if negb (bool_decide (w=component)) then
        (false, i, curState, curEq)
      else (* w = component *)
        if bool_decide (a=component) then
          match l with
          | Send =>
            let result := bool_decide (observationsOf p = prefix) in
            (result, i, curState, curEq)
          | Receive =>
            let result := bool_decide (In (Cobservation Send m component) prefix) in
            (result, i, curState, curEq)
          end
        else
          (* a <> component *)
          match l with
          | Send =>
            let result := false in
            (result, i, curState, curEq)
          | Receive =>
            if negb (fullNode m prefix component) then
              let result := false in
              (result, i, curState, curEq)
            else
              let: (result, curState, curEq) := update m component weights treshold curState curEq in
              (result, i, curState, curEq)
          end 
    end.

Definition isProtocol
           (prestate : Prestate)
           (component : nat)
           (weights : list pos_R)
           (treshold: R) : bool
  :=
    let initialState := map (fun x => Cprestate nil) weights in
    let initialEq := @nil nat in
    let result := (fold_left (isProtocol_step component weights treshold (observationsOf prestate)) (observationsOf prestate) (true, 0, initialState, initialEq )) in
    fst (fst (fst result)).

Definition elmo_valid
           (weights : list pos_R)
           (treshold : R)
           (label : Label)
           (bsom : Prestate * option Premessage)
  : bool :=
  let: (state, message) := bsom in
  match label,message with
  | Send, None => true
  | Send, Some _ => false
  | Receive, None => false
  | Receive, Some m => isProtocol (stateOf m) (authorOf m) weights treshold
  end.

Definition elmo_transition
           (component : nat)
           (weights : list pos_R)
           (treshold : R)
           (label : Common.label)
           (bsom : Prestate * option Premessage)
  : Prestate * option Premessage
  :=
    let: (state, message) := bsom in
    match label, message with
    | Send, Some _ => (state, None)
    | Send, None
      => let m := Cpremessage state component in
         let ob := Cobservation Send m component in
         let s := Cprestate (observationsOf state ++ [ob]) in
         (s, Some m)
    | Receive, None
      => (state, None)
    | Receive, Some msg
      => let ob := Cobservation Receive msg component in
         let s := Cprestate (observationsOf state ++ [ob]) in
         (s, None)
    end.

Definition elmo_vlsm_machine (component : nat) (weights : list pos_R) (treshold : R)
  : @VLSM_class Premessage elmo_type elmo_sig
  :=
    {| valid := elmo_valid weights treshold
       ; transition := elmo_transition component weights treshold
    |}.


Section capabilities.
  Context
    (component : nat)
    (weights : list pos_R)
    (treshold : R)
    (vlsm := mk_vlsm (elmo_vlsm_machine component weights treshold))
  .

  Check (field_selector input).
  Check oracle_stepwise_props.

  Definition elmo_has_been_received_oracle (s : Prestate) (m : Premessage) : Prop :=
    List.In m (map messageOf (filter isReceive (filter (isWitnessedBy component) (observationsOf s)))).

  Definition elmo_has_been_sent_oracle (s : Prestate) (m : Premessage) : Prop :=
    List.In m (map messageOf (filter isSend (filter (isWitnessedBy component) (observationsOf s)))).

  Lemma elmo_has_been_received_oracle_dec : RelDecision elmo_has_been_received_oracle.
  Proof.
    intros x y.
    apply list_in_dec.
  Qed.

  Lemma elmo_has_been_sent_oracle_dec : RelDecision elmo_has_been_sent_oracle.
  Proof.
    intros x y.
    apply list_in_dec.
  Qed.

  
  Lemma elmo_has_been_received_oracle_no_inits:
    forall (s : vstate vlsm),
      initial_state_prop (VLSM_sign := sign vlsm) s ->
      forall m, ~elmo_has_been_received_oracle s m.
  Proof.
    intros s Hinitial m Hcontra.
    simpl in Hinitial. unfold elmo_initial_state_prop in Hinitial.
    unfold elmo_has_been_received_oracle in Hcontra. rewrite Hinitial in Hcontra.
    simpl in Hcontra.
    exact Hcontra.
  Qed.


  Lemma elmo_has_been_received_oracle_step_update:
    forall l s im s' om,      
      protocol_transition (pre_loaded_with_all_messages_vlsm vlsm) l (s,im) (s',om) ->
      forall msg, elmo_has_been_received_oracle s' msg <->
                  ((field_selector input) msg {|l:=l; input:=im; destination:=s'; output:=om|}
                   \/ elmo_has_been_received_oracle s msg).
  Proof.
    intros l s im s' om Hpt msg.
    simpl.

    destruct Hpt as [Hvalid Htransition].
    simpl in Htransition.
    unfold vtransition in Htransition. simpl in Htransition.
    
    unfold elmo_has_been_received_oracle.
    destruct l, im; inversion Htransition; subst; clear Htransition; simpl.
    - rewrite filter_app.
      rewrite filter_app.
      rewrite map_app.
      rewrite in_app_iff.
      simpl. unfold isWitnessedBy. simpl.
      destruct (bool_decide (component = component)) eqn:Heq.
      2: { apply bool_decide_eq_false in Heq. contradiction. }
      clear Heq.
      simpl.
      split.
      + intros [H|H].
        * right. exact H.
        * left. destruct H as [H|H].
          ** congruence.
          ** inversion H.
      + intros [H|H].
        * inversion H; subst.
          right. left. reflexivity.
        * left. exact H.
    - split; intros H.
      + right. exact H.
      + destruct H.
        * inversion H.
        * exact H.
    - split; intros H.
      + right. exact H.
      + destruct H.
        * inversion H; subst.
          inversion Hvalid.
          destruct H1.
          simpl in H2. unfold vvalid in H2. simpl in H2. inversion H2.
        * exact H.
    - rewrite filter_app.
      rewrite filter_app.
      rewrite map_app.
      rewrite in_app_iff.
      simpl. unfold isWitnessedBy. simpl.
      destruct (bool_decide (component = component)) eqn:Heq.
      2: { apply bool_decide_eq_false in Heq. contradiction. }
      clear Heq.
      simpl.
      split.
      + intros [H|H].
        * right. exact H.
        * inversion H.
      + intros [H|H].
        * inversion H.
        * left. exact H.
  Qed.

  Definition elmo_has_been_received_oracle_stepwise_props
    : @oracle_stepwise_props _ vlsm (field_selector input) elmo_has_been_received_oracle
    := {| oracle_no_inits := elmo_has_been_received_oracle_no_inits;
          oracle_step_update := elmo_has_been_received_oracle_step_update;
       |}
  .


  Lemma elmo_has_been_sent_oracle_no_inits:
    forall (s : vstate vlsm),
      initial_state_prop (VLSM_sign := sign vlsm) s ->
      forall m, ~elmo_has_been_sent_oracle s m.
  Proof.
    intros s Hinitial m Hcontra.
    simpl in Hinitial. unfold elmo_initial_state_prop in Hinitial.
    unfold elmo_has_been_sent_oracle in Hcontra. rewrite Hinitial in Hcontra.
    simpl in Hcontra.
    exact Hcontra.
  Qed.


  Lemma elmo_has_been_sent_oracle_step_update:
    forall l s im s' om,      
      protocol_transition (pre_loaded_with_all_messages_vlsm vlsm) l (s,im) (s',om) ->
      forall msg, elmo_has_been_sent_oracle s' msg <->
                  ((field_selector output) msg {|l:=l; input:=im; destination:=s'; output:=om|}
                   \/ elmo_has_been_sent_oracle s msg).
  Proof.
    intros l s im s' om Hpt msg.
    simpl.

    destruct Hpt as [Hvalid Htransition].
    simpl in Htransition.
    unfold vtransition in Htransition. simpl in Htransition.
    
    unfold elmo_has_been_sent_oracle.
    destruct l, im; inversion Htransition; subst; clear Htransition; simpl.
    - rewrite filter_app.
      rewrite filter_app.
      rewrite map_app.
      rewrite in_app_iff.
      simpl. unfold isWitnessedBy. simpl.
      destruct (bool_decide (component = component)) eqn:Heq.
      2: { apply bool_decide_eq_false in Heq. contradiction. }
      clear Heq.
      simpl.
      split.
      + intros [H|H].
        * right. exact H.
        * inversion H.
      + intros [H|H].
        * inversion H.
        * left. exact H.
    - split; intros H.
      + right. exact H.
      + destruct H.
        * inversion H.
        * exact H.
    - split; intros H.
      + right. exact H.
      + destruct H.
        * inversion H; subst.
        * exact H.
    - rewrite filter_app.
      rewrite filter_app.
      rewrite map_app.
      rewrite in_app_iff.
      simpl. unfold isWitnessedBy. simpl.
      destruct (bool_decide (component = component)) eqn:Heq.
      2: { apply bool_decide_eq_false in Heq. contradiction. }
      clear Heq.
      simpl.
      split.
      + intros [H|H].
        * right. exact H.
        * destruct H.
          ** left. congruence.
          ** inversion H.
      + intros [H|H].
        * inversion H. right. left. reflexivity.
        * left. exact H.
  Qed.

  Definition elmo_has_been_sent_oracle_stepwise_props
    : @oracle_stepwise_props _ vlsm (field_selector output) elmo_has_been_sent_oracle
    := {| oracle_no_inits := elmo_has_been_sent_oracle_no_inits;
          oracle_step_update := elmo_has_been_sent_oracle_step_update;
       |}
  .

  Lemma elmo_has_been_sent_capability : has_been_sent_capability vlsm.
  Proof.
    eapply has_been_sent_capability_from_stepwise.
    2: apply elmo_has_been_sent_oracle_stepwise_props.
    apply elmo_has_been_sent_oracle_dec.
  Qed.

  Lemma elmo_has_been_received_capability : has_been_received_capability vlsm.
  Proof.
    eapply has_been_received_capability_from_stepwise.
    2: apply elmo_has_been_received_oracle_stepwise_props.
    apply elmo_has_been_received_oracle_dec.
  Qed.
  
End capabilities.

(*
Lemma isProtocol_step_len component weights treshold b n l ss es o:
  let '(b', n', l', ss', es') := isProtocol_step component weights treshold (b, n, l, ss, es) o in
  l' = l.
Proof.
  induction l.
  - simpl.
    destruct b,o,p. simpl.
    2: { reflexivity. }
    destruct (bool_decide (n0 = component)).
    2: { reflexivity. }
    simpl.
    destruct (bool_decide (n1 = component)); simpl; destruct l; try reflexivity.
    rewrite firstn_nil.
    destruct (fullNode (Cpremessage p n1) [] component); simpl.
    2: { reflexivity. }
    remember (update (Cpremessage p n1) component weights treshold ss es) as updated.
    destruct updated as [[b' s'] es'].
    reflexivity.
  - remember (isProtocol_step component weights treshold) as step.
    remember (step (b, n, l, ss, es) o) as result1.
    destruct result1 as [[[[b1 n1] l1] ss1] es1].
    remember (step (b, n, a::l, ss, es) o) as result2.
    destruct result2 as [[[[b2 n2] l2] ss2] es2].
    simpl.
    rewrite Heqstep in Heqresult1,Heqresult2.
    unfold isProtocol_step in Heqresult1,Heqresult2.
    destruct b,o; simpl in *;
      destruct p,(bool_decide (n0 = component)); simpl in *;
        destruct l0, (bool_decide (n3 = component)); simpl in *;
          inversion Heqresult1; inversion Heqresult2; subst; simpl; try reflexivity.

    remember (fullNode (Cpremessage p n3) (firstn n l) component) as fn1.
    remember (fullNode (Cpremessage p n3) (firstn n (a::l)) component) as fn2.
    remember (update (Cpremessage p n3) component weights treshold ss es) as u.
    destruct u as [[b3 ss3] es3].
    destruct fn1, fn2; simpl in *; inversion H0; inversion H1; subst; reflexivity.
Qed.
*)

Check Observation_weight.


Lemma Observation_in_list_weight ob l:
  List.In ob l ->
  Observation_weight ob < ListObservation_weight l.
Proof.
  intros H.
  induction l.
  + inversion H.
  + simpl in H.
    simpl.
    destruct H as [H|H].
    * subst. lia.
    * specialize (IHl H). lia.
Qed.


Lemma Observation_nested_weight ob1 ob2:
  List.In ob1 (observationsOf (stateOf (messageOf ob2))) ->
  Observation_weight ob1 < Observation_weight ob2.
Proof.
  destruct ob2. destruct p. destruct p. simpl.
  fold (ListObservation_weight l0).
  intros H.
  pose proof (H' := Observation_in_list_weight ob1 l0 H).
  lia.
Qed.


Lemma Observation_nested_neq ob1 ob2:
  List.In ob1 (observationsOf (stateOf (messageOf ob2))) ->
  ob1 <> ob2.
Proof.
  intros H.
  pose proof (H' := Observation_nested_weight ob1 ob2 H).
  assert (Observation_weight ob1 <> Observation_weight ob2).
  { lia. }
  congruence.
Qed.

(* Observations of send messages contain all previous messages *)
Definition ob_sent_contains_previous_prop l : Prop :=
  forall (i : nat),
    i < length l ->
    labelOf (nth i l dummy_observation) = Send ->
    forall (j : nat),
      j < i ->
      List.In
        (nth j l dummy_observation)
        (observationsOf (stateOf (messageOf (nth i l dummy_observation))))

.


Lemma ob_sent_contains_previous_prop_tail x xs:
  ob_sent_contains_previous_prop (x :: xs) ->
  ob_sent_contains_previous_prop xs.
Proof.
  unfold ob_sent_contains_previous_prop.
  intros H.
  intros i Hi Hsend j Hj.
  simpl in H.
  assert (Hi': S i < S (length xs)).
  { lia. }
  specialize (H (S i) Hi'). clear Hi'.
  simpl in H.
  assert (Hj': S j < S i).
  { lia. }
  specialize (H Hsend (S j) Hj'). clear Hj'.
  simpl in H.
  exact H.
Qed.

  

Lemma ob_sent_contains_previous_prop_app l1 l2:
  ob_sent_contains_previous_prop (l1 ++ l2) ->
  ob_sent_contains_previous_prop l1 /\ ob_sent_contains_previous_prop l2.
Proof.
  intros H.
  induction l1.
  - simpl in H. split.
    + unfold ob_sent_contains_previous_prop. intros i Hi. simpl in Hi. inversion Hi.
    + exact H.
  - simpl in H.
    pose proof (Htail:= ob_sent_contains_previous_prop_tail _ _ H).
    specialize (IHl1 Htail).
    destruct IHl1 as [IHl11 IHl12].
    split.
    2: { exact IHl12. }
    intros i Hi Hsend j Hj.
    specialize (H i).
    simpl in *.
    rewrite app_length in H.
    assert (Hi': i < S (length l1 + length l2)).
    { lia. }
    specialize (H Hi'). clear Hi'.
    destruct i.
    + specialize (H Hsend j Hj). destruct j.
      * exact H.
      * lia.
    + rewrite app_nth1 in H.
      { lia. }
      specialize (H Hsend j Hj).
      destruct j.
      * exact H.
      * rewrite app_nth1 in H.
        { lia. }
        exact H.
Qed.

Lemma ob_sent_contains_previous_prop_middle l1 a l2:
  ob_sent_contains_previous_prop (l1 ++ a :: l2) ->
  ob_sent_contains_previous_prop (l1 ++ l2).
Proof.
  intros H.
  induction l1.
  - simpl in *.
    eapply ob_sent_contains_previous_prop_tail.
    apply H.
  - simpl in *.
    specialize (IHl1 (ob_sent_contains_previous_prop_tail _ _ H)).
    intros i Hi Hsend j Hj.
    destruct j.
    + (* j = 0 -> use H *)
      clear IHl1.
      destruct i.
      { lia. }
      clear Hj.
      simpl in *.
      rewrite app_length in Hi.
      (* I need to case split on whether i < length l1 or not *)
      destruct (dec_lt i (length l1)).
      * rewrite app_nth1.
        { apply H0. }        
        specialize (H (S i)).
        simpl in H.
        assert (Htmp: (S i) < S (length (l1 ++ a :: l2))).
        { rewrite app_length. simpl. lia. }
        specialize (H Htmp). clear Htmp.
        rewrite app_nth1 in H.
        { apply H0. }
        rewrite app_nth1 in Hsend.
        { apply H0. }
        specialize (H Hsend). clear Hsend.
        specialize (H 0).
        assert (Htmp: 0 < S i).
        { lia. }
        specialize (H Htmp). clear Htmp.
        simpl in H. exact H.
      * rewrite app_nth2.
        { lia. }
        rewrite app_nth2 in Hsend.
        { lia. }
        specialize (H (S (S i))).
        simpl in H.
        rewrite app_nth2 in H.
        { lia. }
        assert (Htmp: (S i) - (length l1) = S (i - (length l1))).
        { lia. }
        rewrite Htmp in H. clear Htmp.
        simpl in H.
        assert (Htmp: S (S i) < S (length (l1 ++ a :: l2))).
        { rewrite app_length. simpl. lia. }
        specialize (H Htmp Hsend). clear Htmp.
        specialize (H 0).
        assert (Htmp: 0 < S (S i)).
        { lia. }
        specialize (H Htmp). clear Htmp.
        simpl in H. exact H.
        
      
    + (* j > 0 -> use IHl1 *)
      clear H.
      simpl. simpl in Hsend.
      destruct i.
      { lia. }
      apply IHl1.
      3: { lia. }
      2: { exact Hsend. }
      simpl in Hi. lia.
Qed.

(* We now prove that all the states of a single component satisfy [ob_sent_contains_previous_prop].
   We start with an initial state *)

Lemma ob_sent_contains_previous_prop_initial : ob_sent_contains_previous_prop [].
Proof.
  intros i Hi Hx j Hj.
  simpl in Hi.
  inversion Hi.
Qed.

(* And prove that the transition function preserves this property. *)
Lemma ob_sent_contains_previous_prop_step
      (component : nat)
      (weights : list pos_R)
      (treshold : R)
      (label : Label)
      (bsom : Prestate * option Premessage) :
  ob_sent_contains_previous_prop (observationsOf (fst bsom)) ->
  elmo_valid weights treshold label bsom ->
  ob_sent_contains_previous_prop (observationsOf (fst (elmo_transition component weights treshold label bsom))).
Proof.
  destruct bsom as [bs om].
  intros Hinit Hvalid.
  simpl. simpl in Hinit.
  destruct label.
  - (* Receive *)
    destruct om.
    + simpl.
      unfold ob_sent_contains_previous_prop.
      simpl.
      intros i Hi Hsend j Hj.
      destruct (decide (i = length (observationsOf bs))).
      * subst i.
        rewrite nth_middle in Hsend.
        simpl in Hsend.
        inversion Hsend.
      * rewrite app_length in Hi. simpl in Hi.
        assert (Hi2: i < length (observationsOf bs)).
        { lia. }
        clear Hi. clear n.
        unfold ob_sent_contains_previous_prop in Hinit.
        rewrite app_nth1.
        { lia. }
        rewrite app_nth1.
        { assumption. }
        rewrite app_nth1 in Hsend.
        { apply Hi2. }
        apply Hinit.
        { apply Hi2. }
        { apply Hsend. }
        { apply Hj. }
    + simpl. exact Hinit.
  - destruct om; simpl.
    + apply Hinit.
    + unfold ob_sent_contains_previous_prop. simpl.
      intros i Hi Hsend j Hj.
      destruct (decide (i = length (observationsOf bs))).
      * subst i.
        clear Hsend.
        rewrite app_nth1.
        { apply Hj. }
        rewrite nth_middle.
        simpl.
        apply nth_In.
        apply Hj.
      * rewrite app_length in Hi. simpl in Hi.
        assert (Hi2: i < length (observationsOf bs)).
        { lia. }
        clear Hi. clear n.
        unfold ob_sent_contains_previous_prop in Hinit.
        rewrite app_nth1.
        { lia. }
        rewrite app_nth1.
        { assumption. }
        rewrite app_nth1 in Hsend.
        { apply Hi2. }
        apply Hinit.
        { apply Hi2. }
        { apply Hsend. }
        { apply Hj. }
Qed.

(* If we have an observation of a received message, the message is not sent later
  (assuming [ob_sent_contains_previous_prop]).
 *)

Lemma ob_sent_contains_previous_prop_impl_received_is_not_sent_later component m l2:
  ob_sent_contains_previous_prop ((Cobservation Receive m component) :: l2) ->
  ~List.In (Cobservation Send m component) l2.
Proof.
  intros H.
  induction l2.
  - simpl. intros [].
  - simpl. intros Hcontra.
    destruct Hcontra.
    + subst.
      unfold ob_sent_contains_previous_prop in H.
      specialize (H 1).
      simpl in H.
      assert (H1 : 1 < S (S (length l2))).
      { lia. }
      specialize (H H1 (eq_refl _) 0).
      assert (H0 : 0 < 1).
      { lia. }
      specialize (H H0). clear H0 H1.
      simpl in H.
      remember (Cobservation Receive m component) as ob1.
      assert (Hm: m = messageOf ob1).
      { subst. reflexivity. }
      rewrite Hm in H.
      pose proof (Observation_nested_neq _ _ H).
      contradiction.
    + apply IHl2.
      2: apply H0.
      clear H0 IHl2.
      assert (Heq1: Cobservation Receive m component :: a :: l2 = [Cobservation Receive m component] ++ a :: l2).
      { reflexivity. }
      rewrite Heq1 in H. clear Heq1.
      assert (Heq2: Cobservation Receive m component :: l2 = [Cobservation Receive m component] ++ l2).
      { reflexivity. }
      rewrite Heq2. clear Heq2.
      eapply ob_sent_contains_previous_prop_middle.
      eexact H.
Qed.


(* Now we can prove the lemma saying that [isProtocol_step] ignores the rest
   of the list after [x]. Specifically, if [isProtocol_step] is given the index [i],
   it uses only the observations with lower or equal index.
 *)
Lemma isProtocol_step_in component weights treshold l1 l2 args x:
  let: (result, i,  curState, curEq) := args in
  i = length l1 ->
  ob_sent_contains_previous_prop (l1 ++ x :: l2) ->
  let step := isProtocol_step component weights treshold in
  step (l1 ++ x :: l2) args x =
  step (l1 ++ [x]) args x.
Proof.
  destruct args as [[[b i] curState] curEq].
  intros Hi Hprev.
  simpl.
  unfold isProtocol_step.
  destruct x. destruct p.
  subst i.
  induction l1.
  - destruct l; destruct b; destruct p; simpl; try reflexivity;
    destruct (bool_decide (n0 = component)) eqn:Heqn0;
    destruct (bool_decide (n = component)) eqn:Heqn; simpl; try reflexivity.
  - simpl in Hprev.
    specialize (IHl1 (ob_sent_contains_previous_prop_tail _ _ Hprev)).
    destruct b.
    2: { reflexivity. }
    destruct (bool_decide (witnessOf (Cobservation l (Cpremessage p n0) n) = component)); simpl.
    2: { reflexivity. }
    simpl in IHl1.
    destruct (bool_decide (n0 = component)),l; simpl in *.
    4: { reflexivity. }
    + inversion IHl1. clear IHl1.
      repeat (apply pair_equal_spec; split); try reflexivity.
      apply bool_decide_iff.
      split; intros [H|H].
      * left. subst a. reflexivity.
      * right.
        rewrite firstn_app.
        rewrite Nat.sub_diag.
        simpl.
        rewrite -app_nil_end.
        rewrite firstn_app in H.
        rewrite Nat.sub_diag in H.
        simpl in H.
        rewrite -app_nil_end in H.
        exact H.
      * left. subst a. reflexivity.
      * right.
        apply bool_decide_iff_iff in H0.
        apply H0. apply H.
    + repeat rewrite firstn_app.
      repeat rewrite Nat.sub_diag.
      reflexivity.
    + repeat rewrite firstn_app.
      repeat rewrite Nat.sub_diag.
      simpl. simpl in IHl1.
      repeat rewrite -app_nil_end.
      reflexivity.
Qed.

Lemma isProtocol_step_in' component weights treshold l1 l2 args x:
  let: (result, i,  curState, curEq) := args in
  i <= length l1 ->
  ob_sent_contains_previous_prop (l1 ++ x :: l2) ->
  let step := isProtocol_step component weights treshold in
  step (l1 ++ x :: l2) args x =
  step (l1 ++ [x]) args x.
Proof.
  Check firstn_skipn.
  destruct args as [[[b n] curState] curEq].
  destruct (decide (n = length l1)).
  { subst. intros _.
    pose proof (H := isProtocol_step_in component weights treshold l1 l2 (b, length l1, curState, curEq)).
    cbv iota beta zeta in H. cbv zeta. apply H. reflexivity.
  }
  intros Hn'.
  assert (n < length l1).
  { lia. }
  clear Hn'.
  
  rewrite -(firstn_skipn n l1).
  intros Hn Hoscpp.
  Search firstn skipn.
  Check isProtocol_step_in.
  remember (skipn n l1) as l1'.
  destruct l1' as [|x' l1'].
  { pose proof (Hl := skipn_length n l1).
    rewrite -Heql1' in Hl. simpl in Hl. lia.
  }
  repeat rewrite -app_assoc.
  rewrite [(x' :: l1') ++ x :: l2]/=.
  rewrite [(x' :: l1') ++ [x]]/=.
  pose proof (Htmp := isProtocol_step_in component weights treshold (firstn n l1) (l1' ++ x :: l2)).
  specialize (Htmp (b, n, curState, curEq) x').
  cbv iota beta zeta in Htmp. (*rewrite Htmp.*)
Abort.

(* But how do we know that the assumption [ob_sent_contains_previous_prop]
   of [isProtocol_step_in] holds? Yes, it holds on all local states, because we
   proved it is an invariant; however, [isProtocol_step] is called with a list of observations
   from a state contained in a received message. About the received message we know only that
   it satisfies [isProtocol]; therefore, we need to prove that [isProtocol] implies
   [ob_sent_contains_previous_prop], which is what
   the lemma [isProtocol_implies_ob_sent_contains_previous_prop] is about.
   Before that we prove some helper results.
 *)


Lemma isProtocol_step_false component weights treshold l x n curState curEq:
  isProtocol_step component weights treshold l (false, n, curState, curEq) x
  = (false, n, curState, curEq).
Proof.
  reflexivity.
Qed.

Lemma isProtocol_step_fold_false component weights treshold l1 l2 n curState curEq:
(fold_left (isProtocol_step component weights treshold l1) l2
           (false, n, curState, curEq)).1.1.1 = false.
Proof.
  induction l2.
  - reflexivity.
  - simpl. apply IHl2.
Qed.

Lemma isProtocol_step_fold_result_true component weights treshold l1 l2 b n curState curEq:
  (fold_left (isProtocol_step component weights treshold l1) l2
             (b, n, curState, curEq)).1.1.1 = true ->
  b = true
.
Proof.
  intros H.
  destruct b.
  - reflexivity.
  - pose proof (H' := isProtocol_step_fold_false component weights treshold l1 l2 n curState curEq).
    rewrite H' in H.
    exact H.
Qed.

Lemma isProtocol_step_result_true component weights treshold l args ob:
  (isProtocol_step component weights treshold l args ob).1.1.1 = true ->
  args.1.1.1 = true.
Proof.
  intros H. simpl in H.
  destruct args as [[[b n] curState] curEq].
  destruct b.
  { reflexivity. }
  simpl in H. exact H.
Qed.

Lemma isProtocol_step_fold_result_true_idx component weights treshold l1 l2 args:
  let: (_, n, _, _) := args in
  let: (b', n', _, _) := (fold_left (isProtocol_step component weights treshold l1) l2 args) in
  b' = true -> n' = n + length l2.
Proof.
  destruct args as [[[b n] curState] curEq].
  move: b n curState curEq.
  induction l2; intros b n curState curEq.
  - simpl. auto.
  - cbn [fold_left].
    remember (isProtocol_step component weights treshold l1) as step.
    remember (step (b,n,curState,curEq) a) as args1.
    destruct args1 as [[[b1 n1] curState1] curEq1].
    remember (fold_left step l2 (b1, n1, curState1, curEq1)) as result.
    destruct result as [[[b' n'] curState'] curEq'].
    intros Hb'. subst b'.
    assert (Hfltrue: (fold_left step l2 (b1, n1, curState1, curEq1)).1.1.1 = true).
    { rewrite -Heqresult. reflexivity. }
    rewrite Heqstep in Hfltrue.
    apply isProtocol_step_fold_result_true in Hfltrue.
    subst b1.
    simpl.
    specialize (IHl2 true n1 curState1 curEq1).
    rewrite -Heqresult in IHl2.
    specialize (IHl2 (eq_refl _)).
    subst n'.

    assert (Hb: b = true).
    {
      pose proof (H := isProtocol_step_result_true component weights treshold l1 (b, n, curState, curEq) a).
      rewrite Heqstep in Heqargs1.
      rewrite -Heqargs1 in H.
      simpl in H.
      specialize (H (eq_refl _)).
      exact H.
    }
    subst b.

    assert (n1 = S n).
    { clear Heqresult curEq' curState'.
      rewrite Heqstep in Heqargs1.
      cbn [isProtocol_step] in Heqargs1.
      destruct (bool_decide (witnessOf a = component)); simpl in Heqargs1.
      2: { inversion Heqargs1. }
      destruct (bool_decide (authorOf (messageOf a) = component)), (labelOf a);
        simpl in Heqargs1.
      4: { inversion Heqargs1. }
      2: { inversion Heqargs1. subst. reflexivity. }
      1: { inversion Heqargs1. subst. reflexivity. }
      destruct (fullNode (messageOf a) (firstn n l1) component); simpl in Heqargs1.
      2: { inversion Heqargs1. }
      destruct (update (messageOf a) component weights treshold curState curEq).
      destruct p.
      inversion Heqargs1. subst. reflexivity.
    }
    lia.
Qed.

    

(*
Lemma isProtocol_step_Sidx component weights treshold ob1 ob2 l n curState curEq:
  (isProtocol_step component weights treshold
                  (ob1 :: l)
                  (true, S n, curState, curEq)
                  ob2).1.1.1
  = (isProtocol_step component weights treshold
                  l
                  (true, n, curState, curEq)
                  ob2).1.1.1.
Proof.
  unfold isProtocol_step.
  destruct (bool_decide (witnessOf ob2 = component)); simpl.
  2: { reflexivity. }
  destruct (bool_decide (authorOf (messageOf ob2) = component)), (labelOf ob2); simpl.
  4: { reflexivity. }
  2: { (* This does not hold. *)
Abort.


Lemma isProtocol_step_fold_Sidx component weights treshold m n l1 l2 b idx curState curEq:
  (fold_left
     (isProtocol_step component weights treshold (Cobservation Send m n :: l1))
     l2
     (b, S idx, curState, curEq))
  =
  let: (b', idx', curState', curEq') := (fold_left
     (isProtocol_step component weights treshold l1)
     l2
     (b, idx, curState, curEq)) in
  (b', S idx', curState', curEq')
.
Proof.
  move: b idx curState curEq.
  induction l2; intros b idx curState curEq.
  - reflexivity.
  - remember (fold_left (isProtocol_step component weights treshold l1) (a :: l2) (b, idx, curState, curEq)) as RHS.
    destruct RHS as [[[b' idx'] curState'] curEq'].
    simpl. simpl in HeqRHS.
    destruct b; simpl; simpl in HeqRHS.
    2: { rewrite IHl2. simpl. rewrite -HeqRHS. reflexivity. }
    destruct (bool_decide (witnessOf a = component)) eqn:Heqwa; simpl; simpl in HeqRHS.
    2: { rewrite IHl2. simpl. rewrite -HeqRHS. reflexivity. }
    destruct (labelOf a) eqn:Heqloa, (bool_decide (authorOf (messageOf a) = component)) eqn:Haomoc; simpl; simpl in HeqRHS.
    4: { rewrite IHl2. rewrite -HeqRHS. reflexivity. }
    3: { rewrite IHl2.
         remember (fold_left (isProtocol_step component weights treshold l1) l2
      (bool_decide (observationsOf (stateOf (messageOf a)) = Cobservation Send m n :: firstn idx l1),
       S idx, curState, curEq)) as LHS.
         destruct LHS as [[[b'0 idx'0] curState'0] curEq'0].
         destruct a. simpl in *. destruct p. simpl in *. destruct p. simpl in *.
         (* Does not seem to hold *)
Abort.

  



Lemma isProtocol_tail component weights treshold a l:
  isProtocol (Cprestate (a :: l)) component weights treshold ->
  isProtocol (Cprestate l) component weights treshold.
Proof.
  unfold isProtocol.
  repeat rewrite [observationsOf _]/=.
  simpl.

  assert (Hfalse: (fold_left (isProtocol_step component weights treshold (a :: l)) l
                             (false, 1, map (fun=> Cprestate []) weights, [])).1.1.1 = false).
  { apply isProtocol_step_fold_false. }

  assert (Hnottrue: ~(fold_left (isProtocol_step component weights treshold (a :: l)) l
                                (false, 1, map (fun=> Cprestate []) weights, [])).1.1.1).
  { intros H. inversion H. rewrite Hfalse in H1. inversion H1. }

  
  destruct (bool_decide (witnessOf a = component)); simpl.
  2: { intros H. contradiction. }
  destruct a. destruct p. simpl.
  destruct (bool_decide (n0 = component)),l0; simpl.
  4: { intros H. contradiction. }
  2: { intros H.
       destruct p. simpl in H.
       destruct (bool_decide (l0 = [])).
       2: { contradiction. }
Abort.
 *)

Lemma isProtocol_step_app component weights treshold l1 l2 ob idx curState curEq:
  idx <= length l1 ->
  isProtocol_step component weights treshold (l1 ++ l2)
                  (true, idx, curState, curEq)
                  ob
  = isProtocol_step component weights treshold l1
                    (true, idx, curState, curEq) ob.
Proof.
  intros Hidx.
  unfold isProtocol_step.
  repeat rewrite firstn_app.
  assert (Hidx': idx - length l1 = 0).
  { lia. }
  repeat rewrite Hidx'.
  rewrite app_nil_r.
  reflexivity.
Qed.

Lemma isProtocol_step_app_fold component weights treshold l1 l2 l3 args:
  let: (b, idx, curState, curEq) := args in
  length l3 + idx <= length l1 ->
  fold_left (isProtocol_step component weights treshold (l1 ++ l2)) l3 args
  = fold_left (isProtocol_step component weights treshold l1) l3 args.
Proof.
  move: args.
  induction l3; intros args.
  - destruct args as [[[b idx] curState] curEq].
    auto.
  - destruct args as [[[b idx] curState] curEq].
    intros Hlen.
    simpl in Hlen.
    cbn [ fold_left ].
    remember (isProtocol_step component weights treshold l1 (true, idx, curState, curEq) a) as stp.
    destruct stp as [[[b' idx'] curState'] curEq'] eqn:Heqstp'.
    assert (idx' = S idx).
    { unfold isProtocol_step in Heqstp.
      destruct (bool_decide (witnessOf a = component)); simpl in Heqstp.
      2: { inversion Heqstp. subst. reflexivity. }
      destruct (bool_decide (authorOf (messageOf a) = component)), (labelOf a);
        simpl in Heqstp; inversion Heqstp; subst; try reflexivity.
      clear H0.
      destruct (fullNode (messageOf a) (firstn idx l1) component);
        simpl in Heqstp; inversion Heqstp.
      2: reflexivity.
      destruct (update (messageOf a) component weights treshold curState curEq).
      destruct p.
      inversion Heqstp. subst. reflexivity.
    }
    destruct b.
    + rewrite isProtocol_step_app.
      { lia. }

      rewrite -Heqstp.
      simpl in IHl3.
      specialize (IHl3 stp).
      rewrite Heqstp' in IHl3.
      apply IHl3.
      lia.
    + repeat rewrite isProtocol_step_false.
      remember (false, idx, curState, curEq) as args.
      specialize (IHl3 args).
      subst args. apply IHl3. lia.
Qed.

  
Lemma isProtocol_last component weights treshold l x:
  isProtocol (Cprestate (l ++ [x])) component weights treshold ->
  isProtocol (Cprestate l) component weights treshold.
Proof.
  unfold isProtocol.
  simpl.
  rewrite fold_left_app.
  simpl.
  intros H.
  inversion H. clear H. rename H1 into H.
  
  remember (fold_left (isProtocol_step component weights treshold (l ++ [x])) l
            (true, 0, map (fun=> Cprestate []) weights, [])) as FL1.

  pose proof (H' := isProtocol_step_result_true _ _ _ _ _ _ H).
  remember (isProtocol_step component weights treshold (l ++ [x]) FL1 x) as ARG2.
  rewrite H.
  subst ARG2. clear H.
  pose proof (Htmp := isProtocol_step_app_fold component weights treshold l [x] l
                                               (true, 0, map (fun=> Cprestate []) weights, [])).
  simpl in Htmp.
  rewrite Htmp in HeqFL1.
  { lia. }
  rewrite -HeqFL1. rewrite H'. reflexivity.
Qed.
     

Lemma isProtocol_implies_ob_sent_contains_previous_prop component weights treshold l:
  isProtocol (Cprestate l) component weights treshold ->
  ob_sent_contains_previous_prop l.
Proof.
  intros H.
  induction l using rev_ind.
  - unfold ob_sent_contains_previous_prop.
    intros i Hi. simpl in Hi. inversion Hi.
  - pose proof (isProtocol_last _ _ _ _ _ H).
    specialize (IHl H0). clear H0.
    unfold isProtocol in H.
    rewrite fold_left_app in H.
    simpl in H.
    remember (fold_left (isProtocol_step component weights treshold (l ++ [x])) l
                        (true, 0, map (fun=> Cprestate []) weights, [])) as FL.
    pose proof (HFLtrue := isProtocol_step_result_true _ _ _ _ _ _ H).
    intros i Hi Hlbl j Hj.
    rewrite app_length in Hi.
    simpl in Hi.
    destruct (decide(i = length l)).
    2: { assert (i < length l).
         { lia. }
         rewrite app_nth1.
         { lia. }
         rewrite app_nth1.
         { lia. }
         rewrite app_nth1 in Hlbl.
         { lia. }
         apply IHl.
         { lia. }
         apply Hlbl.
         exact Hj.
    }
    subst i.
    rewrite app_nth1.
    { exact Hj. }
    rewrite nth_middle.
    unfold isProtocol_step in H.
    destruct FL as [[[tt i'] curState'] curEq'].
    simpl in HFLtrue. subst tt.
    destruct (bool_decide (witnessOf x = component)) eqn:Hwitness, (labelOf x) eqn:Hlabel; simpl in H.
    4: { inversion H. }
    3: { inversion H. }
    { rewrite nth_middle in Hlbl. rewrite Hlabel in Hlbl. inversion Hlbl. }
    destruct (bool_decide (authorOf (messageOf x) = component)) eqn:Hauthor; simpl in H.
    2: { inversion H. }
    clear Hlabel Hlbl.
    destruct x. simpl in *.
    destruct p. simpl in *.
    destruct p. simpl in *.
    apply bool_decide_eq_true in Hwitness. subst n.
    apply bool_decide_eq_true in Hauthor. subst n0.
    apply bool_decide_eq_true in H.
    clear Hi.
    rewrite H.
    (* Now l1 is a prefix of l *)
    (* First, i' = length l *)
    pose proof (Hidx := isProtocol_step_fold_result_true_idx component weights treshold).
    specialize (Hidx (l ++ [Cobservation l0 (Cpremessage (Cprestate l1) component) component])).
    specialize (Hidx l (true, 0, map (fun=> Cprestate []) weights, [])).
    simpl in Hidx.
    rewrite -HeqFL in Hidx.
    specialize (Hidx (eq_refl _)).
    subst i'.
    rewrite firstn_app. rewrite Nat.sub_diag. simpl. rewrite app_nil_r. rewrite firstn_all.
    apply nth_In. apply Hj.
Qed.



Lemma fold_isProtocol_step_app component weights treshold l1 l2 b (*n*) s es:
  ob_sent_contains_previous_prop (l1 ++ l2) ->
  let FL := fold_left (isProtocol_step component weights treshold (l1 ++ l2)) l1 (b, (*n*)0, s, es) in
  FL.1.1.1 = true ->
  FL = fold_left (isProtocol_step component weights treshold l1) l1 (b, (*n*)0, s, es).
Proof.
  simpl.
  generalize dependent l2.
  generalize dependent b.
  (*generalize dependent n.*)
  generalize dependent s.
  generalize dependent es.
  (* TODO assume n <= length l1 *)
  remember (length l1) as len.
  assert (Hlen: length l1 <= len).
  { lia. }
  clear Heqlen.
  revert Hlen.
  generalize dependent l1.
  induction len; intros l1 Hlen es s (*n*) b l2 Hoscp Htrue.
  - destruct l1.
    + reflexivity.
    + simpl in Hlen. lia.
  - destruct (null_or_exists_last l1).
    { subst. reflexivity. }
    destruct H as [l1' [x Hl1]].
    remember (isProtocol_step component weights treshold) as step.
    remember (fold_left (step l1) l1 (b, (*n*)0, s, es)) as fl.
    destruct fl as [[[b' n'] s'] es'].
    rewrite Hl1. rewrite fold_left_app. simpl.
    rewrite -app_assoc.

    assert (Hlenl1': length l1' <= len).
    { subst l1. rewrite app_length in Hlen. simpl in Hlen. lia. }

    assert (Htrue': (fold_left (step (l1' ++ [x] ++ l2)) l1' (b, 0, s, es)).1.1.1 = true).
    {
      subst.
      rewrite fold_left_app in Htrue. simpl in Htrue.
      apply isProtocol_step_result_true in Htrue.
      rewrite app_assoc. exact Htrue.
    }
    
    rewrite IHlen.
    { lia. }
    { subst. rewrite app_assoc. exact Hoscp. }
    { exact Htrue'. }
    simpl.

    remember (fold_left (step l1') l1' (b, (*n*)0, s, es)) as fl'.
    destruct fl' as [[[b'' n''] s''] es''].
    subst l1.
    (*rewrite Hl1 in Heqfl.*)

    rewrite fold_left_app in Heqfl. simpl in Heqfl.


    assert (Htrue'': (fold_left (step (l1' ++ [x])) l1' (b, 0, s, es)).1.1.1 = true).
    { subst.
      rewrite app_assoc in Htrue'.
      pose proof (Htmp := isProtocol_step_app_fold component weights treshold (l1' ++ [x]) l2 l1' (b, 0, s, es)).
      cbv beta iota in Htmp. rewrite Htmp in Htrue'.
      { rewrite app_length. simpl. lia. }
      exact Htrue'.
    }
    
    
    rewrite IHlen in Heqfl.
    { lia. }
    { exact (proj1 (ob_sent_contains_previous_prop_app _ _ Hoscp)). }
    { exact Htrue''. }
    
    rewrite -Heqfl' in Heqfl.
    rewrite Heqfl.
    rewrite Heqstep.

    (*
    assert (Htrue''': (fold_left (step (l1' ++ [x] ++ l2)) l1' (b, 0, s, es)).1.1.1 = true).
    { subst. *)

    assert (Htrue''': (fold_left (step l1') l1' (b, 0, s, es)).1.1.1 = true).
    { subst.
      pose proof (Htmp := isProtocol_step_app_fold component weights treshold l1' [x] l1' (b, 0, s, es)).
      simpl in Htmp.
      rewrite Htmp in Htrue''.
      { lia. }
      exact Htrue''.
    }

    assert (n'' = length l1').
    { subst.
      pose proof (Htmp := isProtocol_step_fold_result_true_idx component weights treshold l1' l1' (b, 0, s, es)).
      cbv beta iota in Htmp. rewrite -Heqfl' in Htmp. simpl in Htmp.
      apply Htmp. clear Htmp.
      rewrite -Heqfl' in Htrue'''.
      simpl in Htrue'''.
      exact Htrue'''.
    }
    subst n''.

    pose proof (Hs := isProtocol_step_in component weights treshold l1' l2 (b'', (length l1'), s'', es'') x).
    cbv iota zeta beta in Hs.
    specialize (Hs (eq_refl _)).
    apply Hs.
    rewrite -app_assoc in Hoscp.
    simpl in Hoscp.
    exact Hoscp.
Qed.

(*
Print Cobservation.
Lemma isProtocol_nested weights treshold author:
  isProtocol (Cprestate (l::(Cobservation))) author weights treshold ->
  isProtool author weights treshold.
*)

Lemma isProtocol_implies_protocol weights treshold m:
  isProtocol (stateOf m) (authorOf m) weights treshold  ->
  let vlsm := mk_vlsm (elmo_vlsm_machine (authorOf m) weights treshold) in
  protocol_message_prop vlsm m.
Proof.
  intros Hproto.
  pose proof (Hproto' := Hproto).
  unfold isProtocol in Hproto.
  destruct m. destruct p. simpl in Hproto. simpl.
  pose proof (Hob := isProtocol_implies_ob_sent_contains_previous_prop _ _ _ _ Hproto).
                                                                       
  induction l using rev_ind.
  - simpl in Hproto.
    unfold protocol_message_prop.
    simpl.
    
    set (mk_vlsm (elmo_vlsm_machine n weights treshold)) as vlsm.
    pose proof (Hgen := protocol_generated vlsm Send).
    eexists.
    simpl in Hgen.
    assert (Hpp0: protocol_prop vlsm (Cprestate [], None)).
    { apply protocol_initial.
      reflexivity.
      reflexivity.
    }
    specialize (Hgen _ _ Hpp0). clear Hpp0.

    specialize (Hgen (Cprestate []) None).
    simpl in Hgen.
    apply Hgen.
    2: auto.
    clear Hgen.
    apply protocol_initial. reflexivity. reflexivity.
  - (* Step *)
    destruct x.
    rewrite fold_left_app in Hproto. simpl in Hproto.
    unfold isProtocol_step in Hproto at 1.
    remember (fold_left (isProtocol_step n weights treshold (l ++ [Cobservation l0 p n0])) l
                        (true, 0, map (fun=> Cprestate []) weights, []))
      as fl.
    destruct fl as [[[b n'] pss] sn].
    simpl in Hproto.
    destruct b.
    2: { simpl in Hproto. inversion Hproto. }
    destruct (bool_decide (n0 = n)).
    2: { simpl in Hproto. inversion Hproto. }
    simpl in Hproto.
    destruct p. simpl in Hproto.
    destruct (bool_decide (n1 = n)), l0.
    + simpl in Hproto.
      admit.
    + simpl in *.
      admit.
    + destruct (fullNode (Cpremessage p n1) (firstn n' (l ++ [Cobservation Receive (Cpremessage p n1) n0])) n).
      2: { simpl in Hproto. inversion Hproto. }
      simpl in Hproto. simpl in Heqfl.
      remember (isProtocol_step n weights treshold) as step.
      (* We want to use Heqfl as the premise of IHl. But to do that, we must get rid
         of the "++ [...]" part. *)
      
      (*
      simpl in Hproto.
      destruct (update (Cpremessage p n1) n weights treshold pss sn).
      destruct p0. simpl in Hproto. Search b.
       *)
      (* Not useful. Clear it. *)
      clear Hproto.
      set (fold_left (step (l ++ [Cobservation Receive (Cpremessage p n1) n0])) l
                          (true, 0, map (fun=> Cprestate []) weights, [])) as FL.
      assert (HFLtrue: FL.1.1.1 = true).
      { unfold FL. rewrite -Heqfl. reflexivity. }
      Check fold_isProtocol_step_app.
      subst step.
      (*unfold FL in HFLtrue.*)
      pose proof (Htmp := fold_isProtocol_step_app _ _ _ _ _ _ _ _ Hob HFLtrue).
      unfold FL in HFLtrue.
      rewrite Htmp in HFLtrue.
      specialize (IHl HFLtrue).
      clear FL Heqfl Htmp HFLtrue.
      clear n' pss sn.
      apply ob_sent_contains_previous_prop_app in Hob.
      destruct Hob as [Hob _].
      simpl in IHl.
      simpl in Hproto'.
      specialize (IHl (isProtocol_last _ _ _ _ _ Hproto') Hob).
      clear Hob.
      (****)
      destruct IHl as [s Hs].
      unfold protocol_message_prop.
      (* Since [Cpremessage (Cprestate l) n] is not an initial message,
         the message must be an output of the transition function, together with the state [s].
       *)
      inversion Hs; subst.
      { simpl in Hom. inversion Hom. }
      destruct l0; destruct om; try inversion H0.
      subst. clear H0.
      simpl in Hs.
      (* Now [Cprestate l] is a protocol state (see the hypothesis Hps) *)
      (* We also need the message [Cpremessage p n1] to be protocol *)
      (*remember (mk_vlsm (elmo_vlsm_machine n weights treshold)) as X.*)
      simpl.
      Print protocol_prop.
      pose proof (Hnext := protocol_generated (mk_vlsm (elmo_vlsm_machine n weights treshold)) Receive (Cprestate l) _om Hps).
      Print protocol_message_prop.
      Search protocol_message_prop.
Abort.    

  

(* m1 is a prefix of m2 *)
Definition is_prefix_of (m1 m2 : Premessage) : Prop :=
  let s1 := stateOf m1 in
  let s2 := stateOf m2 in
  observationsOf s1 = firstn (length (observationsOf s1)) (observationsOf s2).

Lemma is_prefix_of_dec : RelDecision is_prefix_of.
Proof.
  intros m1 m2.
  unfold is_prefix_of.
  apply list_eq_dec.
  apply Observation_eqdec.
Qed.

Definition equivocation_evidence (m1 m2 : Premessage) : Prop :=
  authorOf m1 = authorOf m2 /\
  ~ is_prefix_of m1 m2 /\
  ~ is_prefix_of m2 m1.

Instance equivocation_evidence_dec : RelDecision equivocation_evidence.
Proof.
  intros m1 m2.
  unfold equivocation_evidence.
  apply Decision_and.
  { unfold Decision. decide equality. }
  apply Decision_and; apply Decision_not; apply is_prefix_of_dec.
Qed.

(* `component` is equivocating and we have an evidence in the state `s` (of another component) *)
Definition is_equivocator (component : nat) (s : Prestate) : bool :=
  let obs := observationsOf s in
  existsb
    (fun ob1 =>
       existsb
         (fun ob2 =>
            bool_decide (labelOf ob1 = Receive) &&
            bool_decide (labelOf ob2 = Receive) &&
            bool_decide (authorOf (messageOf ob1) = component) &&
            bool_decide (authorOf (messageOf ob2) = component) &&
            bool_decide (equivocation_evidence (messageOf ob1) (messageOf ob2))
         )
         obs
    )
    obs.

Section composition.

  Context
    (weights : list pos_R)
    (treshold : R)
    (index : Type)
    {i0 : Inhabited index}
    {IndEqDec : EqDecision index}
    (indices : list index)
    (finite_index : Listing indices)
    (indices_weights_eqlenght : length indices = length weights)
  .

  Fixpoint index_to_component' (idx : index) (component : nat) (indices : list index) :=
    match indices with
    | [] => component
    | x::xs
      => if decide (x = idx)
         then component
         else index_to_component' idx (S component) xs
    end.

  Lemma index_to_component'_valid (idx : index) (component : nat) (indices': list index) :
    In idx indices' -> index_to_component' idx component indices' < length indices' + component.
  Proof.
    intros Hin.
    move: component.
    induction indices'.
    - simpl in Hin. inversion Hin.
    - intros component.
      simpl.
      destruct (decide (a = idx)); simpl.
      + lia.
      + simpl in Hin.
        destruct Hin as [Haeqidx|Hin].
        * contradiction.
        * specialize (IHindices' Hin).
          specialize (IHindices' (S component)).
          lia.
  Qed.

  Definition index_to_component (idx : index) :=
    index_to_component' idx 0 indices.

  Lemma index_to_component_valid (idx : index) : index_to_component idx < length indices.
  Proof.
    pose proof (P := index_to_component'_valid).
    specialize (P idx 0 indices).
    rewrite Nat.add_0_r in P.
    apply P.
    apply finite_index.
  Qed.
  

  Definition IM' (i : index) := elmo_vlsm_machine (index_to_component i) weights treshold.
  Definition IM (i : index) := mk_vlsm (IM' i).

  (* `component` is equivocating and we have an evidence in some state
     of the list `states` *)
  Definition is_equivocator_states (states : list Prestate) (component : nat) : bool :=
    let eq := map (is_equivocator component) states in
    fold_right orb false eq.

  Definition equivocators (states : list Prestate) : list nat :=
    filter (is_equivocator_states states) (seq 0 (length indices)).
  
  Program Definition composition_constraint
             (cl : composite_label IM)
             (sm : composite_state IM * option Premessage) : Prop
    := let cs := fst sm in
       let om := snd sm in
       match om with
       | None => True
       | Some m =>
         let states := map cs indices in
         let transitions := map (fun i => @transition _ _ _ (IM' i)) indices in
         let new_states := zip_with (fun s t => fst (t Receive (s, Some m)))
                                    states
                                    transitions in
         let eqs := equivocators new_states in
         ((@sum_weights _ (Build_Measurable _ (fun idx => nth idx weights (exist _ 1%R _))) eqs) < treshold)%R
       end.
  Next Obligation.
    lra.
  Defined.
  
  
  Definition composite_elmo := @composite_vlsm Premessage index IndEqDec IM i0 composition_constraint.


  Context
        (i : index)
        (Xi := composite_vlsm_constrained_projection IM composition_constraint i)
  .
  
  
  Theorem elmo_validating:
    validating_projection_prop IM composition_constraint i.
  Proof.
    intros li siomi H.
    unfold protocol_valid in H.
    unfold vvalid. unfold valid. unfold machine. simpl.
    unfold projection_valid.
    destruct siomi as [si omi].
    destruct H as [Hpsp [Hopmp Hvalid]].
    unfold valid in Hvalid. unfold machine in Hvalid. simpl in Hvalid. unfold IM in Hvalid.
    unfold IM' in Hvalid. inversion Hvalid.
    unfold vvalid in Hvalid.
  Abort.
  


End composition.
