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
                     if (decide (authorOf (messageOf ob2) = component)) then
                       bool_decide (In (Cobservation Send (messageOf ob2) component) prefix)
                     else
                       bool_decide (In (Cobservation Receive (messageOf ob2) component) prefix)
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
           (addresses : list nat)
           (component : nat)
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
  | Receive, Some m =>
    bool_decide (List.In (authorOf m) addresses) &&
    fullNode m (observationsOf state) component &&
    (if (decide (authorOf m = component)) then
      bool_decide (List.In (Cobservation Send m component) (observationsOf state))
    else
      true
    ) &&
    isProtocol (stateOf m) (authorOf m) weights treshold
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

Definition elmo_vlsm_machine (addresses : list nat)
           (component : nat) (weights : list pos_R) (treshold : R)
  : @VLSM_class Premessage elmo_type elmo_sig
  :=
    {| valid := elmo_valid addresses component weights treshold
       ; transition := elmo_transition component weights treshold
    |}.


Section capabilities.
  Context
    (addresses : list nat)
    (component : nat)
    (weights : list pos_R)
    (treshold : R)
    (vlsm := mk_vlsm (elmo_vlsm_machine addresses component weights treshold))
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

  Instance elmo_has_been_sent_capability : has_been_sent_capability vlsm.
  Proof.
    eapply has_been_sent_capability_from_stepwise.
    2: apply elmo_has_been_sent_oracle_stepwise_props.
    apply elmo_has_been_sent_oracle_dec.
  Defined.

  Instance elmo_has_been_received_capability : has_been_received_capability vlsm.
  Proof.
    eapply has_been_received_capability_from_stepwise.
    2: apply elmo_has_been_received_oracle_stepwise_props.
    apply elmo_has_been_received_oracle_dec.
  Defined.
  
End capabilities.

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
      (addresses : list nat)
      (component : nat)
      (weights : list pos_R)
      (treshold : R)
      (label : Label)
      (bsom : Prestate * option Premessage) :
  ob_sent_contains_previous_prop (observationsOf (fst bsom)) ->
  elmo_valid addresses component weights treshold label bsom ->
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

Lemma fullNode_appone (l obs : list Observation) (ob : Observation) (n component : nat) :
  fullNode (Cpremessage (Cprestate (l ++ [ob])) n) obs component ->
  fullNode (Cpremessage (Cprestate l) n) obs component.
Proof.
  intros H.
  induction l using rev_ind.
  - unfold fullNode. simpl. exact is_true_true.
  - unfold fullNode. simpl.
    unfold fullNode in H.
    simpl in H.
    rewrite map_app in H.
    rewrite fold_right_app in H.
    simpl in H.
    destruct ob. simpl in H.
    destruct (decide (authorOf p = component)); simpl in H.
    {
      destruct (bool_decide (In (Cobservation Send p component) obs)).
      { simpl in H. exact H. }
      simpl in H.
      rewrite fold_right_andb_false in H. inversion H.
    }
    destruct (bool_decide (In (Cobservation Receive p component) obs)).
    { simpl in H. exact H. }
    { simpl in H. rewrite fold_right_andb_false in H. inversion H. }
Qed.

Lemma fullNode_dropMiddle (l1 l2 obs : list Observation) (ob : Observation) (n component : nat) :
  fullNode (Cpremessage (Cprestate (l1 ++ (ob :: l2))) n) obs component ->
  fullNode (Cpremessage (Cprestate (l1 ++ l2)) n) obs component.
Proof.
  intros H.
  move: l1 H.
  induction l2; intros l1 H.
  - simpl. rewrite app_nil_r. eapply fullNode_appone. apply H.
  - apply Forall_fold_right_bool. apply Forall_fold_right_bool in H.
    simpl in H. simpl.
    apply Forall_app in H. destruct H as [H1 H2].
    apply Forall_app. split; [exact H1|]. clear H1.
    inversion H2. subst. clear H2. exact H3.
Qed.


Lemma fullNode_last_receive_self (l obs : list Observation) (p : Prestate) (n n0 component : nat) :
  fullNode (Cpremessage (Cprestate (l ++ [Cobservation Receive (Cpremessage p component) n0])) n) obs component = true ->
  List.In (Cobservation Send (Cpremessage p component) component) obs.
Proof.
  intros Hfn.
  induction l using rev_ind.
  - unfold fullNode in Hfn.
    simpl in Hfn.
    destruct (decide (component = component)).
    2: { contradiction. }
    simpl in Hfn.
    apply andb_prop in Hfn. destruct Hfn as [Hfn _].
    apply bool_decide_eq_true_1 in Hfn.
    exact Hfn.
  - rewrite -app_assoc in Hfn. simpl in Hfn.
    apply fullNode_dropMiddle in Hfn. auto.
Qed.

Lemma fullNode_last_receive_not_self (l obs : list Observation) (p : Prestate)
      (n component1 component2 component3 : nat) :
  component1 <> component2 ->
  let ob := Cobservation Receive (Cpremessage p component2) component3 in
  fullNode (Cpremessage (Cprestate (l ++ [ob])) n) obs component1 = true ->
  List.In (Cobservation Receive (Cpremessage p component2) component1) obs.
Proof.
  intros Hneq ob Hfn.
  induction l using rev_ind.
  - unfold fullNode in Hfn. simpl in Hfn.
    destruct (decide (component2 = component1)).
    { subst. contradiction. }
    simpl in Hfn.
    apply andb_prop in Hfn. destruct Hfn as [Hfn _].
    apply bool_decide_eq_true_1 in Hfn.
    exact Hfn.
  - rewrite -app_assoc in Hfn. simpl in Hfn.
    apply fullNode_dropMiddle in Hfn. auto.
Qed.

Definition all_received_satisfy_isprotocol_prop {weights} {treshold} (obs : list Observation) : Prop :=
  Forall (fun (ob : Observation) =>
            if (isReceive ob) then
              isProtocol (stateOf (messageOf ob)) (authorOf (messageOf ob)) weights treshold
            else
              true
         ) obs.

(*
Lemma fullNode_length component obs m:
  fullNode m obs component ->
 *)

Lemma Observation_list_weight_last l ob:
  Observation_weight ob < ListObservation_weight (l ++ [ob]).
Proof.
  apply Observation_in_list_weight.
  apply in_or_app.
  right. simpl. left. reflexivity.
Qed.

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

  Definition addresses : list nat := seq 0 (length indices).

  Definition index_to_component (idx : index) : nat :=
    findInList idx indices.
  
  Definition component_to_index (component : nat) : index :=
    nth component indices (@inhabitant _ i0).

  Lemma index_to_component_to_index (idx : index) :
    component_to_index (index_to_component idx) = idx.
  Proof.
    unfold component_to_index.
    unfold index_to_component.
    apply findInList_correct.
    apply finite_index.
  Qed.

  Definition address_valid (a : nat) : Prop :=
    a < length indices.

  Instance address_valid_dec (a : nat) : Decision (address_valid a).
  Proof.
    unfold address_valid.
    apply lt_dec.
  Qed.
  
  Lemma component_to_index_to_component (a : nat) :
    address_valid a ->
    index_to_component (component_to_index a) = a.
  Proof.
    intros Hvalid.
    unfold index_to_component.
    unfold component_to_index.
    apply findInList_nth.
    { exact Hvalid. }
    { apply finite_index. }
  Qed.

  Definition IM' (i : index) := elmo_vlsm_machine addresses (index_to_component i) weights treshold.
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
  Definition free_composite_elmo := @free_composite_vlsm Premessage index IndEqDec IM i0.

  Lemma all_receive_observation_have_component_as_witness st m witness idx:
    protocol_state_prop free_composite_elmo st ->
    In (Cobservation Receive m witness) (observationsOf (st idx)) ->
    witness = index_to_component idx.
  Proof.
    intros Hpsp Hin.
    induction Hpsp using protocol_state_prop_ind.
    - simpl in Hs. unfold composite_initial_state_prop in Hs.
      assert (Hos: observationsOf (s idx) = []).
      { apply Hs. }
      rewrite Hos in Hin. simpl in Hin. inversion Hin.
    - unfold protocol_transition in Ht.
      destruct Ht as [Hvalid Ht].
      unfold transition in Ht.
      simpl in Ht.
      destruct l as [i li].      
      remember (vtransition (IM i) li (s i, om)) as VT.
      destruct VT as [si'' om''].
      unfold vtransition in HeqVT. simpl in HeqVT.

      destruct (decide (i = idx)).
      2: {
        apply IHHpsp. clear IHHpsp.
        inversion Ht. subst. clear Ht.
        rewrite state_update_neq in Hin. apply nesym. exact n.
        exact Hin.
      }
      subst i.
      
      destruct li, om; inversion HeqVT; subst; clear HeqVT;
        inversion Ht; subst; clear Ht;
        rewrite state_update_eq in Hin.
      + apply in_app_or in Hin.
        destruct Hin as [Hin|Hin]; [auto|].
        simpl in Hin.
        destruct Hin as [Hin|Hin]; inversion Hin; subst.
        reflexivity.
      + auto.
      + auto.
      + simpl in Hin.
        apply in_app_or in Hin.
        destruct Hin as [Hin|Hin]; [auto|].
        simpl in Hin.
        destruct Hin as [Hin|Hin]; inversion Hin.
  Qed.

  Instance free_composite_elmo_has_been_received_capability:
    has_been_received_capability free_composite_elmo.
  Proof.
    unfold free_composite_elmo. unfold free_composite_vlsm.
    eapply composite_has_been_received_capability.
    { apply finite_index. }
    intros i.
    apply elmo_has_been_received_capability.
  Defined.

  Lemma has_receive_observation_implies_is_protocol st idx m:
    protocol_state_prop free_composite_elmo st ->
    In (Cobservation Receive m (index_to_component idx)) (observationsOf (st idx)) ->
    protocol_message_prop free_composite_elmo m.
  Proof.
    intros Hpsp Hin.
    pose proof (Hpsp' := pre_loaded_with_all_messages_protocol_state_prop _ _ Hpsp).
    pose proof (Hhbr := @proper_received _ free_composite_elmo free_composite_elmo_has_been_received_capability _ Hpsp').
    specialize (Hhbr m).
    unfold has_been_received_prop in Hhbr.
    unfold all_traces_have_message_prop in Hhbr.
    apply proj1 in Hhbr.
    unfold has_been_received in Hhbr.
    unfold free_composite_elmo_has_been_received_capability in Hhbr.
    simpl in Hhbr.
    unfold composite_has_been_received in Hhbr.
    assert (Htmp: exists i : index, @has_been_received _ (IM i) (elmo_has_been_received_capability addresses (index_to_component i) weights treshold) (st i) m).
    {
      exists idx.
      unfold has_been_received. unfold elmo_has_been_received_capability. simpl.
      unfold elmo_has_been_received_oracle.
      
      apply (filter_in _ (isWitnessedBy (index_to_component idx))) in Hin.
      2: { unfold isWitnessedBy. simpl.
           destruct (bool_decide (index_to_component idx = index_to_component idx)) eqn:Heq.
           reflexivity.
           apply bool_decide_eq_false_1 in Heq. contradiction.
      }
      apply (filter_in _ isReceive) in Hin.
      2: { reflexivity. }
      
      apply (@in_map _ _ messageOf _ _) in Hin.
      exact Hin.
    }
    specialize (Hhbr Htmp). clear Htmp.
    pose proof (Htmp := protocol_state_has_trace _ _ Hpsp).
    destruct Htmp as [si [tr [Htrace Hlast]]].
    specialize (Hhbr si tr).
    
    pose proof (Hp := (VLSM_incl_finite_protocol_trace _ _ (vlsm_incl_pre_loaded_with_all_messages_vlsm free_composite_elmo))). simpl in Hp.
    unfold finite_protocol_trace in Hp.
    pose proof (Htrace' := finite_protocol_trace_from_to_forget_last _ _ _ _ Htrace).
    specialize (Hp _ _ (conj Htrace' Hlast)).
    destruct Hp as [Hfrom Hsi].
    unfold finite_protocol_trace_init_to in Hhbr.
    specialize (Hhbr (conj (preloaded_weaken_finite_protocol_trace_from_to _ _ _ _ Htrace) Hlast)).
    clear Hlast.
    eapply protocol_trace_input_is_protocol.
    apply Htrace'. unfold trace_has_message in Hhbr. exact Hhbr.
  Qed.
  
  Lemma has_send_observation_implies_is_protocol st idx m author:
    protocol_state_prop free_composite_elmo st ->
    In (Cobservation Send m author) (observationsOf (st idx)) ->
    protocol_message_prop free_composite_elmo m.
  Proof.
    intros Hpsp Hin.
    induction Hpsp using protocol_state_prop_ind.
    - simpl in Hs. unfold composite_initial_state_prop in Hs.
      assert (Hos: observationsOf (s idx) = []).
      { apply Hs. }
      rewrite Hos in Hin.
      simpl in Hin. inversion Hin.
    - unfold protocol_transition in Ht.
      destruct Ht as [Hvalid Ht].
      unfold transition in Ht.
      simpl in Ht.
      destruct l as [i li].      
      remember (vtransition (IM i) li (s i, om)) as VT.
      destruct VT as [si'' om''].
      unfold vtransition in HeqVT. simpl in HeqVT.

      destruct (decide (i = idx)).
      2: {
        apply IHHpsp. clear IHHpsp.
        inversion Ht. subst. clear Ht.
        rewrite state_update_neq in Hin. apply nesym. exact n.
        exact Hin.
      }
      subst i.

      destruct li, om; inversion HeqVT; subst; clear HeqVT;
        inversion Ht; subst; clear Ht;
        rewrite state_update_eq in Hin.
      + apply in_app_or in Hin.
        simpl in Hin.
        destruct Hin.
        { apply IHHpsp. exact H. }
        destruct H.
        { inversion H. }
        { inversion H. }
      + apply IHHpsp. apply Hin.
      + apply IHHpsp. apply Hin.
      + simpl in Hin.
        apply in_app_or in Hin.
        destruct Hin.
        { apply IHHpsp. exact H. }
        simpl in H.
        destruct H.
        2: { inversion H. }
        inversion H. subst. clear H.
        unfold protocol_message_prop.
        clear IHHpsp.
        pose proof (Hgen := protocol_generated free_composite_elmo (existT _ idx Send)).
        simpl in Hgen.
        unfold protocol_valid in Hvalid.
        destruct Hvalid as [Hpsp [_ Hvalid]].
        destruct Hpsp as [m0 Hs].
        specialize (Hgen s m0 Hs).
        assert (Hinit: protocol_prop free_composite_elmo (fun=> Cprestate [], None)).
        { apply protocol_initial. simpl. intros x. unfold vinitial_state_prop. simpl.
          unfold elmo_initial_state_prop. reflexivity. simpl. exact I. }
        specialize (Hgen _ _ Hinit). clear Hinit.
        assert (Hvalid': constrained_composite_valid IM (free_constraint IM) (existT (fun=> Label) idx Send) (s, None)).
        {
          unfold constrained_composite_valid.
          simpl.
          unfold free_constraint.
          split; [| exact I].
          unfold vvalid. simpl. apply is_true_true.
        }
        specialize (Hgen Hvalid'). clear Hvalid'.
        unfold vtransition in Hgen. simpl in Hgen.
        eexists. apply Hgen.
  Qed.
  
  Lemma protocol_state_satisfies_all_received_satisfy_isprotocol_prop st idx:
    protocol_state_prop free_composite_elmo st ->
    @all_received_satisfy_isprotocol_prop weights treshold (observationsOf (st idx)).
  Proof.
    intros Hpsp.
    induction Hpsp using protocol_state_prop_ind.
    - simpl in Hs. unfold composite_initial_state_prop in Hs.
      assert (Hos: observationsOf (s idx) = []).
      { apply Hs. }
      rewrite Hos.
      unfold all_received_satisfy_isprotocol_prop.
      apply Forall_nil.
    - destruct l.
      unfold protocol_transition in Ht.
      destruct Ht as [Hvt Ht].
      simpl in Ht.
      remember (vtransition (IM x) v (s x, om)) as vt.
      destruct vt as [si' o].
      destruct (decide (x = idx)).
      2: {
        assert (Hsidx: s idx = s' idx).
        {
          inversion Ht. subst.
          rewrite state_update_neq. apply nesym. exact n.
          reflexivity.
        }
        rewrite Hsidx in IHHpsp.
        exact IHHpsp.
      }
      subst x.
      inversion Ht. subst. clear Ht.
      rewrite state_update_eq.
      unfold vtransition in Heqvt.
      simpl in Heqvt.
      destruct v,om; inversion Heqvt; clear Heqvt; subst.
      4: { simpl.
           unfold all_received_satisfy_isprotocol_prop.
           apply Forall_app.
           split; [exact IHHpsp|].
           apply Forall_cons.
           2: { apply Forall_nil. }
           simpl.
           exact is_true_true.
      }
      3: { exact IHHpsp. }
      2: { exact IHHpsp. }
      { simpl.
        unfold all_received_satisfy_isprotocol_prop.
        apply Forall_app.
        split; [exact IHHpsp|].
        apply Forall_cons.
        2: { apply Forall_nil. }
        simpl.
        unfold protocol_valid in Hvt.
        destruct Hvt as [[_ _] [_ Hvalid]].
        unfold valid in Hvalid. simpl in Hvalid.
        unfold constrained_composite_valid in Hvalid.
        simpl in Hvalid. destruct Hvalid as [Hvalid _].
        unfold vvalid in Hvalid. simpl in Hvalid.
        apply andb_prop in Hvalid.
        destruct Hvalid as [Hfn HisP].
        exact HisP.
      }
  Qed.

  Lemma protocol_state_contains_receive_implies_isProtocol st idx msg n0:
    protocol_state_prop free_composite_elmo st ->
    List.In (Cobservation Receive msg n0) (observationsOf (st idx)) ->
    isProtocol (stateOf msg) (authorOf msg) weights treshold.
  Proof.
    intros Hpsp Hin.
    pose proof (H := protocol_state_satisfies_all_received_satisfy_isprotocol_prop st idx Hpsp).
    unfold all_received_satisfy_isprotocol_prop in H.
    eapply (proj1 (@Forall_forall Observation _ _)) in H.
    2: apply Hin.
    simpl in H. exact H.
  Qed.

  (* TODO s1 is reachable from s0 *)
  Lemma protocol_message_was_sent_from_protocol_state s1 st author:
    protocol_prop free_composite_elmo (s1, Some (Cpremessage st author)) ->
    (
    exists s0,
      protocol_state_prop free_composite_elmo s0
      /\ (s0 (component_to_index author)) = st
    ) /\ (List.In (Cobservation Send (Cpremessage st author) author) (observationsOf (s1 (component_to_index author))))
  .
  Proof.
    intros H.
    inversion H; subst; clear H.
    { simpl in Hom. unfold composite_initial_message_prop in Hom.
      destruct Hom as [n [mi Hmi]].
      unfold vinitial_message in mi. unfold initial_message in mi.
      simpl in mi.
      pose proof (proj2_sig mi) as H0. simpl in H0. inversion H0.
    }
    destruct l as [i li].
    remember (vtransition (IM i) li (s i, om)) as VT.
    destruct VT as [st' om']. inversion H1. subst. clear H1.
    unfold vtransition in HeqVT. simpl in HeqVT.
    destruct li,om; inversion HeqVT; subst; clear HeqVT.
    rewrite index_to_component_to_index.
    split.
    - unfold protocol_state_prop.
      eexists. split. eexists. apply Hps. reflexivity.
    - rewrite state_update_eq. simpl.
      apply in_or_app. right. simpl. left. reflexivity.
  Qed.

  Lemma isProtocol_last_fullNode l p n1 n0 component:
    n1 <> component ->
    isProtocol (Cprestate (l ++ [Cobservation Receive (Cpremessage p n1) n0]))
               component weights treshold ->
    fullNode (Cpremessage p n1) l component.
  Proof.
    intros Hneq Hproto.
    unfold isProtocol in Hproto. simpl in Hproto.
    
    rewrite fold_left_app in Hproto. simpl in Hproto.
    remember (fold_left
                (isProtocol_step component weights treshold                 
                                 (l ++ [Cobservation Receive (Cpremessage p n1) n0])) l   
                (true, 0, map (fun=> Cprestate []) weights, [])) as FL.
    unfold isProtocol_step in Hproto at 1.
    destruct FL as [[[b i] curState] curEq].
    destruct b; simpl in Hproto.
    2: { inversion Hproto. }
    destruct (bool_decide (n0 = component)); simpl in Hproto.
    2: { inversion Hproto. }
    destruct (bool_decide (n1 = component)) eqn:Heq; simpl in Hproto.
    { apply bool_decide_eq_true in Heq. contradiction. }
    
    pose proof (Htmp := isProtocol_step_fold_result_true_idx component weights treshold).
    specialize (Htmp (l ++ [Cobservation Receive (Cpremessage p n1) n0])).
    specialize (Htmp l (true, 0, map (fun=> Cprestate []) weights, [])).
    simpl in Htmp.
    rewrite -HeqFL in Htmp. specialize (Htmp (eq_refl _)). subst i.
    rewrite firstn_app in Hproto. rewrite Nat.sub_diag in Hproto. simpl in Hproto.
    rewrite app_nil_r in Hproto. rewrite firstn_all in Hproto.

    remember (fullNode (Cpremessage p n1) l component) as FN.
    destruct FN; simpl in Hproto.
    2: { inversion Hproto. }
    exact is_true_true.
  Qed.


  Lemma isProtocol_last_sendInPrefix l p n0 component:
    isProtocol (Cprestate (l ++ [Cobservation Receive (Cpremessage p component) n0]))
               component weights treshold ->
    List.In (Cobservation Send (Cpremessage p component) component) l.
  Proof.
    intros Hproto.
    unfold isProtocol in Hproto. simpl in Hproto.
    
    rewrite fold_left_app in Hproto. simpl in Hproto.
    remember (fold_left
                (isProtocol_step component weights treshold                 
                                 (l ++ [Cobservation Receive (Cpremessage p component) n0])) l   
                (true, 0, map (fun=> Cprestate []) weights, [])) as FL.
    unfold isProtocol_step in Hproto at 1.
    destruct FL as [[[b i] curState] curEq].
    destruct b; simpl in Hproto.
    2: { inversion Hproto. }
    destruct (bool_decide (n0 = component)); simpl in Hproto.
    2: { inversion Hproto. }
    destruct (bool_decide (component = component)) eqn:Heq; simpl in Hproto.
    2: { apply bool_decide_eq_false in Heq. contradiction. }
    apply bool_decide_eq_true in Hproto.

    pose proof (Htmp := isProtocol_step_fold_result_true_idx component weights treshold).
    specialize (Htmp (l ++ [Cobservation Receive (Cpremessage p component) n0])).
    specialize (Htmp l (true, 0, map (fun=> Cprestate []) weights, [])).
    simpl in Htmp.
    rewrite -HeqFL in Htmp. specialize (Htmp (eq_refl _)). subst i.
    rewrite firstn_app in Hproto. rewrite Nat.sub_diag in Hproto. simpl in Hproto.
    rewrite app_nil_r in Hproto. rewrite firstn_all in Hproto.
    exact Hproto.
  Qed.

  Lemma sent_is_protocol st m component:
    address_valid component ->
    protocol_state_prop free_composite_elmo st ->
    In (Cobservation Send m component) (observationsOf (st (component_to_index component))) ->
    protocol_message_prop free_composite_elmo m.
  Proof.
    intros Haddr Hpsp Hin.
    induction Hpsp using protocol_state_prop_ind.
    - simpl in Hs. unfold composite_initial_state_prop in Hs.
      assert (Hos: observationsOf (s (component_to_index component)) = []).
      { apply Hs. }
      rewrite Hos in Hin. simpl in Hin. inversion Hin.
    - unfold protocol_transition in Ht.
      destruct Ht as [Hvalid Ht].
      unfold transition in Ht. simpl in Ht.
      destruct l as [i li].
      remember (vtransition (IM i) li (s i, om)) as VT.
      destruct VT as [si'' om'']. inversion Ht. subst. clear Ht.
      
      destruct (decide (component_to_index component = i)).
      2: { rewrite state_update_neq in Hin.
           { exact n. }
           apply IHHpsp. apply Hin.
      }
      subst i.
      rewrite state_update_eq in Hin.
      unfold protocol_valid in Hvalid. destruct Hvalid as [Hpsp [Hopmp Hvalid]].
      unfold vtransition in HeqVT. simpl in HeqVT.
      destruct li,om; inversion HeqVT; subst; clear HeqVT.
      + simpl in Hin. apply in_app_or in Hin.
        simpl in Hin. destruct Hin as [Hin|[Hin|Hin]].
        3: { inversion Hin. }
        2: { rewrite component_to_index_to_component in Hin. exact Haddr. inversion Hin. }
        auto.
      + auto.
      + auto.
      + simpl in Hin.
        rewrite component_to_index_to_component in Hin.
        { exact Haddr. }
        apply in_app_or in Hin.
        simpl in Hin.
        destruct Hin as [Hin|[Hin|Hin]].
        3: { inversion Hin. }
        2: { inversion Hin. subst. clear Hin.
             clear IHHpsp.
             Check protocol_generated.
             pose proof (Hgen := protocol_generated free_composite_elmo (existT _ (component_to_index component) Send)).
             destruct Hpsp as [_om Hpsp].
             specialize (Hgen _ _om Hpsp).
             assert (Hpi: protocol_prop free_composite_elmo (fun=> Cprestate [], None)).
             { apply protocol_initial. simpl. intros x. reflexivity. reflexivity. }
             specialize (Hgen _ _ Hpi Hvalid).
             clear Hpi.
             unfold transition in Hgen. simpl in Hgen.
             rewrite component_to_index_to_component in Hgen.
             { exact Haddr. }
             eexists. apply Hgen.
        }
        auto.
  Qed.

  
  Lemma fullNode_appObservation m component l ob:
    fullNode m l component = true ->
    fullNode m (l ++ [ob]) component = true.
  Proof.
    intros H.

    unfold fullNode in H. apply Forall_fold_right_bool in H.
    unfold fullNode. apply Forall_fold_right_bool.
    induction H.
    - apply Forall_nil.
    - apply Forall_cons.
      2: { auto. }
      clear H0 IHForall.
      destruct (decide (authorOf (messageOf x) = component)); simpl in H; simpl.
      * apply bool_decide_eq_true_1 in H. apply bool_decide_eq_true_2.
        apply in_or_app. left. exact H.
      * apply bool_decide_eq_true_1 in H. apply bool_decide_eq_true_2.
        apply in_or_app. left. exact H.
  Qed.

  (* All observations in a state have the same witness - which is the address of the node. *)
  Lemma observationsHaveSameWitness st component ob:
    address_valid component ->
    protocol_state_prop free_composite_elmo st ->
    In ob (observationsOf (st (component_to_index component))) ->
    witnessOf ob = component.
  Proof.
    intros Haddr Hpsp Hin.
    induction Hpsp using protocol_state_prop_ind.
    - simpl in Hs. unfold composite_initial_state_prop in Hs.
      assert (Hos: observationsOf (s (component_to_index component)) = []).
      { apply Hs. }
      rewrite Hos in Hin. simpl in Hin. inversion Hin.
    - unfold protocol_transition in Ht.
      destruct Ht as [Hvalid Ht].
      unfold transition in Ht. simpl in Ht.
      destruct l as [i li].
      remember (vtransition (IM i) li (s i, om)) as VT.
      destruct VT as [si'' om'']. inversion Ht. subst om'' s'. clear Ht.
      
      destruct (decide (component_to_index component = i)).
      2: { rewrite state_update_neq in Hin.
           { exact n. }
           auto.
      }
      subst i.
      rewrite state_update_eq in Hin.

      unfold vtransition in HeqVT.
      simpl in HeqVT.
      destruct li,om; inversion HeqVT; clear HeqVT; subst; auto.
      + simpl in Hin. apply in_app_or in Hin.
        destruct Hin as [Hin|Hin];[auto|].
        simpl in Hin.
        destruct Hin as [Hin|Hin];[|inversion Hin].
        subst ob. simpl.
        rewrite component_to_index_to_component.
        { exact Haddr. }
        reflexivity.
      + simpl in Hin.
        apply in_app_or in Hin.
        destruct Hin as [Hin|Hin];[auto|].
        simpl in Hin.
        destruct Hin as [Hin|Hin];[|inversion Hin].
        subst ob. simpl.
        rewrite component_to_index_to_component.
        { exact Haddr. }
        reflexivity.
  Qed.
  
  (* All observations with sender other than the component are Receive observations.  *)
  Lemma observationsWithAddressNotComponentAreReceive st component ob:
    address_valid component ->
    protocol_state_prop free_composite_elmo st ->
    In ob (observationsOf (st (component_to_index component))) ->
    authorOf (messageOf ob) <> component ->
    labelOf ob = Receive.
  Proof.
    intros Haddr Hpsp Hin Hauthor.
    induction Hpsp using protocol_state_prop_ind.
    - simpl in Hs. unfold composite_initial_state_prop in Hs.
      assert (Hos: observationsOf (s (component_to_index component)) = []).
      { apply Hs. }
      rewrite Hos in Hin. simpl in Hin. inversion Hin.
    - unfold protocol_transition in Ht.
      destruct Ht as [Hvalid Ht].
      unfold transition in Ht. simpl in Ht.
      destruct l as [i li].
      remember (vtransition (IM i) li (s i, om)) as VT.
      destruct VT as [si'' om'']. inversion Ht. subst om'' s'. clear Ht.
      
      destruct (decide (component_to_index component = i)).
      2: { rewrite state_update_neq in Hin.
           { exact n. }
           auto.
      }
      subst i.
      rewrite state_update_eq in Hin.

      unfold vtransition in HeqVT.
      simpl in HeqVT.
      destruct li,om; inversion HeqVT; clear HeqVT; subst; auto.
      + simpl in Hin. apply in_app_or in Hin.
        destruct Hin as [Hin|Hin];[auto|]. clear IHHpsp.
        simpl in Hin.
        destruct Hin as [Hin|Hin];[|inversion Hin].
        subst ob. reflexivity.
      + simpl in Hin.
        apply in_app_or in Hin.
        destruct Hin as [Hin|Hin];[auto|]. clear IHHpsp.
        simpl in Hin.
        destruct Hin as [Hin|Hin];[|inversion Hin].
        subst ob. simpl.
        simpl in Hauthor.
        rewrite component_to_index_to_component in Hauthor.
        { exact Haddr. }
        contradiction.
  Qed.

  Lemma trace_from_to_impl_observations_prefix s1 s2 (tr : list transition_item) component:
    let i := component_to_index component in
    finite_protocol_trace_from_to (pre_loaded_with_all_messages_vlsm (IM i)) s1 s2 tr ->
    exists (n : nat),
      length (observationsOf s2) >= n /\
      list_prefix (observationsOf s2) n = observationsOf s1.
  Proof.
    intros i.
    intros Htr.
    move: s1 s2 component i Htr.
    induction tr; intros s1 s2 component i Htr.
    - inversion Htr. subst.
      exists (length (observationsOf s2)).
      split. lia.
      rewrite -> list_prefix_all by lia.
      reflexivity.
    - inversion Htr. subst. clear Htr.
      rename l into lbl.
      (*destruct l as [idx lbl].*)
      unfold protocol_transition in H4.
      simpl in H4.
      destruct H4 as [[[opmp Hopmp] [Hiom Hvalid]] Htrans].
      rename H3 into Hss2.
      remember (vtransition (IM i) lbl (s1, iom)) as VT.
      destruct VT as [s1' oom'].
      inversion Htrans. subst. clear Htrans.
      unfold vtransition in HeqVT. simpl in HeqVT.
      destruct lbl,iom; inversion HeqVT; subst; clear HeqVT
      + simpl.
        pose proof (IH := IHtr _ _ component i Hss2).
        destruct IH as [n Hn].

        (* n <> 0 *)
        destruct n.
        { rewrite list_prefix_0 in Hn. simpl in Hn.
          destruct Hn as [_ Hn].
          apply eq_sym in Hn.
          destruct (last_not_null _ _ Hn).
        }
        simpl in Hn.
        destruct Hn as [Hl Hn].
        
        apply list_prefix_S in Hn.
        2: { exact Hl. }
        exists n. split. lia. apply Hn.
      + eauto.
      + eauto.
      + pose proof (IH := IHtr _ _ component i Hss2).
        destruct IH as [n Hn].
        (* n <> 0 *)
        destruct n.
        { rewrite list_prefix_0 in Hn. simpl in Hn.
          destruct Hn as [_ Hn].
          apply eq_sym in Hn.
          destruct (last_not_null _ _ Hn).
        }
        simpl in Hn.
        destruct Hn as [Hl Hn].
        
        apply list_prefix_S in Hn.
        2: { exact Hl. }
        exists n. split. lia. apply Hn. 
  Qed.
  

  (* If there is a [Cobservation Receive m component], then there is also
                   [Cobservation Send m component]. *)
  Lemma received_from_self_implies_sent st s component:
    address_valid component ->
    protocol_state_prop free_composite_elmo st ->
    let obs := observationsOf (st (component_to_index component)) in
    In (Cobservation Receive (Cpremessage s component) component) obs ->
    In (Cobservation Send (Cpremessage s component) component) obs.
  Proof.
    simpl.
    intros Haddr Hpsp Hrecv.
    assert (Hhbr:
              @has_been_received
                _
                (IM (component_to_index component))
                (elmo_has_been_received_capability _ _ _ _)
                (st (component_to_index component))
                (Cpremessage s component)
           ).
    {
      simpl.
      unfold elmo_has_been_received_oracle.
      rewrite component_to_index_to_component.
      { exact Haddr. }
      apply (filter_in _ (isWitnessedBy component)) in Hrecv.
      2: { unfold isWitnessedBy. simpl.
           destruct (bool_decide (component = component)) eqn:Heq.
           reflexivity.
           apply bool_decide_eq_false_1 in Heq. contradiction.
      }
      
      apply (filter_in _ isReceive) in Hrecv.
      2: { reflexivity. }
      Check in_map.
      apply (in_map messageOf) in Hrecv.
      exact Hrecv.
    }
    (* Maybe if we had the check that the message was already sent... *)
    (*clear Hrecv.*)

    remember (component_to_index component) as i.
    assert (Hpspi: protocol_state_prop (pre_loaded_with_all_messages_vlsm (IM i)) (st i)).
    { apply preloaded_composed_protocol_state.
      apply pre_loaded_with_all_messages_protocol_state_prop.
      exact Hpsp.
    }


    pose proof (Htmp := has_been_received_in_state_preloaded _ _ _ _ Hpspi Hhbr).
    (*pose proof (Htmp := has_been_received_in_state _ _ _ _ Hpsp Hhbr).*)
    destruct Htmp as [s0 [item [tr [Hin Hfpt]]]].
    (* We will need Hfpt' later for monotonicity. *)
    pose proof (Hfpt' := Hfpt).
    inversion Hfpt. subst tl f s' item. clear Hfpt.
    simpl in Hin. subst iom.
    (* We will use H3 later for monotonicity. *)
    
    rename H4 into Hpt.
    unfold protocol_transition in Hpt.
    destruct Hpt as [Hvalid Hs1].
    simpl in Hvalid.
    destruct Hvalid as [Hs0 [Hmsg Hvalid]].
    unfold constrained_composite_valid in Hvalid.
    (*destruct Hvalid as [Hvalid _]*)
    simpl in Hvalid.
    (*destruct l as [i li].*)
    unfold vvalid in Hvalid. simpl in Hvalid.
    destruct l; [| inversion Hvalid].

    apply andb_prop in Hvalid. destruct Hvalid as [Hvalid _].
    apply andb_prop in Hvalid. destruct Hvalid as [_ Hvalid].
    rewrite Heqi in Hvalid.
    rewrite component_to_index_to_component in Hvalid.
    { exact Haddr. }
    destruct (decide (component = component)).
    2: { contradiction. }
    simpl in Hvalid. clear e.
    apply bool_decide_eq_true_1 in Hvalid.
    subst i.
    pose proof (Hprefix := trace_from_to_impl_observations_prefix _ _ _ _ Hfpt').
    destruct Hprefix as [n [_ Hprefix]].
    rewrite -Hprefix in Hvalid.
    eapply In_list_prefix.
    apply Hvalid.
  Qed.


  Lemma protocol_message_has_valid_sender p address:
    protocol_message_prop free_composite_elmo (Cpremessage p address) ->
    address_valid address.
  Proof.
    intros Hpmp.
    apply protocol_message_prop_iff in Hpmp.
    destruct Hpmp.
    - destruct H as [im Him].
      unfold initial_message in im.
      pose proof (proj2_sig im). simpl in H. unfold composite_initial_message_prop in H.
      destruct H as [n [mi Hmi]].
      unfold vinitial_message,initial_message in mi.
      pose proof (proj2_sig mi). simpl in H. inversion H.
    - destruct H as [l [som [s' Htrans]]].
      destruct l.
      unfold protocol_transition in Htrans.
      destruct Htrans as [_ Htrans].
      unfold transition in Htrans.
      simpl in Htrans.
      unfold composite_transition in Htrans. destruct som.
      remember (vtransition (IM x) v (s x, o)) as VT.
      destruct VT. inversion Htrans. subst. clear Htrans.
      unfold vtransition,transition in HeqVT.
      simpl in HeqVT.
      destruct v,o; inversion HeqVT. clear HeqVT. subst.
      unfold address_valid.
      unfold index_to_component.
      apply findInList_found.
      apply finite_index.
  Qed.
  
  
  Lemma sent_is_fullNode st m component component':
    address_valid component ->
    protocol_state_prop free_composite_elmo st ->
    authorOf m = component ->
    let st' := st (component_to_index component) in
    In (Cobservation Send m component') (observationsOf st') ->
    fullNode m (observationsOf st') component = true.
  Proof.
    intros Haddr Hpsp Hauthor st' Hin.
    induction Hpsp using protocol_state_prop_ind.
    - simpl in Hs. unfold composite_initial_state_prop in Hs.
      assert (Hos: observationsOf (s (component_to_index component)) = []).
      { apply Hs. }
      rewrite Hos in Hin. simpl in Hin. inversion Hin.
    - unfold protocol_transition in Ht.
      destruct Ht as [Hvalid Ht].
      unfold transition in Ht. simpl in Ht.
      destruct l as [i li].
      remember (vtransition (IM i) li (s i, om)) as VT.
      destruct VT as [si'' om'']. inversion Ht. subst om'' s'. clear Ht.
      
      destruct (decide (component_to_index component = i)).
      2: { unfold st' in Hin.
           rewrite state_update_neq in Hin.
           { exact n. }
           unfold st'.
           rewrite state_update_neq.
           { exact n. }
           simpl in IHHpsp.
           (*unfold ob. unfold st'
           rewrite state_update_neq.
           { exact n. }*)
           apply IHHpsp.
           apply Hin.
      }
      subst i.
      unfold st' in Hin.
      rewrite state_update_eq in Hin.
      unfold protocol_valid in Hvalid. destruct Hvalid as [Hpsp [Hopmp Hvalid]].
      unfold vtransition in HeqVT. simpl in HeqVT.
      destruct li,om; inversion HeqVT; subst; clear HeqVT.
      + simpl in Hin. apply in_app_or in Hin.
        simpl in Hin. destruct Hin as [Hin|[Hin|Hin]].
        3: { inversion Hin. }
        2: { rewrite component_to_index_to_component in Hin. exact Haddr. inversion Hin. }
        unfold st'.
        rewrite component_to_index_to_component.
        { exact Haddr. }
        rewrite state_update_eq.
        specialize (IHHpsp Hin). clear Hin. simpl. simpl in IHHpsp.
        unfold st' in *. clear st'.
        (*unfold ob in *. clear ob.
        rewrite component_to_index_to_component.
        { exact Haddr. }
        rewrite state_update_eq.*)
        apply fullNode_appObservation. exact IHHpsp.
      + unfold st'. rewrite state_update_eq. auto.
      + unfold st'. rewrite state_update_eq. auto.
      + unfold st'. rewrite state_update_eq.
        simpl in Hin.
        rewrite component_to_index_to_component in Hin.
        { exact Haddr. }
        rewrite component_to_index_to_component.
        { exact Haddr. }
        apply in_app_or in Hin.
        simpl in Hin.
        destruct Hin as [Hin|[Hin|Hin]]; simpl.
        3: { inversion Hin. }
        2: { simpl. inversion Hin. clear Hin.
             simpl.
             destruct m. simpl. simpl in H0.
             inversion H0. clear H0. subst p.
             simpl in IHHpsp.
             apply fullNode_appObservation.
             unfold fullNode.
             simpl.
             apply Forall_fold_right_bool.
             remember (observationsOf (s (component_to_index n))) as obs.
             apply Forall_forall.
             intros x Hx. destruct x. simpl. destruct p. simpl.

             (* Some facts:
                1. All observations in a state have the same witness - which is the address
                  of the node (lemma [observationsHaveSameWitness]).
                2. If there is a [Cobservation Receive m component], then there is also
                   [Cobservation Send m component].
                3. All observations with sender other than the component are Receive observations.
                Then the following cases might happen:
                * n1 = n -> Either l=Send, and we can use Hx. Or l=Receive, and by (2), there is some Send in obs.
                * n1 <> n -> the message was sent by some other node, and by (3) we have l=Receive, and we can use Hx.
                *)
             simpl in Haddr.
             
             assert (n0 = n).
             { rewrite Heqobs in Hx.
               pose proof (observationsHaveSameWitness s n _ Haddr Hpsp Hx).
               simpl in H. exact H.
             }
             subst n0.

             simpl in Hvalid. clear Hvalid. (* a Send transition is trivially valid *)
             destruct (decide (n1 = n)); simpl; apply bool_decide_eq_true_2.
             - subst n1.
               destruct l.
               + rewrite Heqobs.
                 apply received_from_self_implies_sent.
                 { exact Haddr. }
                 { exact Hpsp. }
                 rewrite Heqobs in Hx.
                 exact Hx.
               + exact Hx.
             - assert (l = Receive).
               {
                 pose proof (H := observationsWithAddressNotComponentAreReceive).
                 rewrite Heqobs in Hx.
                 specialize (H _ _ _ Haddr Hpsp Hx).
                 simpl in H.
                 auto.
               }
               subst l. exact Hx.
               
        }
        apply fullNode_appObservation. auto.
  Qed.


  Lemma isProtocol_last_receive_impl_send l p n n0:
    isProtocol (Cprestate (l ++ [Cobservation Receive (Cpremessage p n) n0]))
               n weights treshold ->
    In (Cobservation Send (Cpremessage p n) n) l.
  Proof.
    intros H.
    unfold isProtocol in H.
    rewrite fold_left_app in H. simpl in H.
    remember (fold_left
          (isProtocol_step n weights treshold (l ++ [Cobservation Receive (Cpremessage p n) n0])) l
          (true, 0, map (fun=> Cprestate []) weights, [])) as FL.
    inversion H.
    pose proof (isProtocol_step_result_true _ _ _ _ _ _ H1).
    destruct FL as [[[b n'] ps] sn]. simpl in H0. subst b.
    clear -H1. unfold isProtocol_step in H1. simpl in H1.
    destruct (bool_decide (n0 = n)); simpl in H1.
    2: { inversion H1. }
    destruct (bool_decide (n = n)) eqn:Heq.
    2: { apply bool_decide_eq_false in Heq. contradiction. }
    clear Heq.
    simpl in H1. apply bool_decide_eq_true in H1.
    rewrite firstn_app in H1.
    apply in_app_or in H1.
    destruct H1.
    2: { Search In firstn. apply In_firstn in H. simpl in H.
         destruct H; [|contradiction]. inversion H.
    }
    eapply In_firstn. apply H.
  Qed.
  
  Lemma isProtocol_implies_protocol component st m:
    address_valid component ->
    protocol_state_prop free_composite_elmo st ->
    fullNode m (observationsOf (st (component_to_index component))) component ->
    address_valid (authorOf m) ->
    isProtocol (stateOf m) (authorOf m) weights treshold  ->
    protocol_message_prop free_composite_elmo m.
  Proof.
    intros Hcomval Hpsp Hfull Haddr Hproto.
    destruct m. destruct p. simpl.
    pose proof (Hob := isProtocol_implies_ob_sent_contains_previous_prop _ _ _ _ Hproto).

    move: n Haddr Hproto Hfull.
    induction l using rev_ind; intros n Haddr Hproto Hfull.
    - simpl in Hproto.
      unfold protocol_message_prop.
      simpl.
      
      (*set (mk_vlsm (elmo_vlsm_machine n weights treshold)) as vlsm.*)
      pose proof (Hgen := protocol_generated free_composite_elmo).
      simpl in Hgen.
      Check (existT _ n Send).
      (* We need to turn `n` into index *)
      unfold _composite_label in Hgen.
      specialize (Hgen (existT _ (component_to_index n) Send)).
      eexists.
      simpl in Hgen.
      assert (Hpp0: protocol_prop free_composite_elmo (fun=> Cprestate [], None)).
      { apply protocol_initial.
        simpl. unfold composite_initial_state_prop.
        intros n0. reflexivity.
        reflexivity.
      }
      specialize (Hgen _ _ Hpp0). clear Hpp0.

      specialize (Hgen (fun=> Cprestate []) None).
      simpl in Hgen.
      simpl in Haddr.
      rewrite component_to_index_to_component in Hgen.
      { exact Haddr. }
      apply Hgen.
      2: { unfold constrained_composite_valid.
           split.
           2: { unfold free_constraint. exact I. }
           unfold composite_valid.
           unfold vvalid. simpl. auto.
      }
      clear Hgen.
      apply protocol_initial.
      2: { reflexivity. }
      intros x. unfold vinitial_state_prop. simpl. reflexivity.
    - (* Step *)
      pose proof (Hproto' := Hproto).
      destruct x.
      unfold isProtocol in Hproto. simpl in Hproto.
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

        subst step.
        (*unfold FL in HFLtrue.*)
        pose proof (Htmp := fold_isProtocol_step_app _ _ _ _ _ _ _ _ Hob HFLtrue).
        unfold FL in HFLtrue.
        rewrite Htmp in HFLtrue.
        apply ob_sent_contains_previous_prop_app in Hob.
        destruct Hob as [Hob _].
        specialize (IHl Hob).
        simpl in IHl.
        simpl in Haddr.
        
        pose proof (IHl' := IHl n Haddr HFLtrue).
        clear FL Heqfl Htmp HFLtrue.
        clear n' pss sn.
        simpl in IHl'.
        simpl in Hproto'.
        (*specialize (IHl (isProtocol_last _ _ _ _ _ Hproto') Hob).*)
        clear Hob.
        specialize (IHl' (fullNode_appone _ _ _ _ _ Hfull)).
        (****)
        destruct IHl' as [s Hs].
        unfold protocol_message_prop.
        (* Since [Cpremessage (Cprestate l) n] is not an initial message,
         the message must be an output of the transition function, together with the state [s].
         *)
        inversion Hs; subst.
        { simpl in Hom. destruct Hom as [i [mi Hmi]].
          unfold vinitial_message in mi.
          unfold initial_message in mi.
          pose proof (Hsv := svalP mi).
          rewrite Hmi in Hsv.
          simpl in Hsv.
          inversion Hsv.
        }
        destruct l0.
        rename x into idx.
        rename v into lbl.
        remember (observationsOf (st (component_to_index component))) as obs.

        (* I want to prove the goal using [protocol_generated].
           I.e., there needs to be a state [Sx] from which a transition goes to some state [s1]
           and  generates the message
           [Cpremessage (Cprestate (l ++ [Cobservation Receive (Cpremessage p n1) n0]))].
           That means that the composite state Sx must satisfy
           [Sx n0 = (Cprestate (l ++ [Cobservation Receive (Cpremessage p n1) n0]))].
           But in order to get into this state, there must be a protocol state [Sy]
           that is the same at all components as Sx, except at the component n0, where
           [Sy n0 = (Cprestate l)]; there must be the protocol message
           [Cpremessage p n1] floating around.

           How do we prove that [Cpremessage p n1] is a protocol message?
           Either [n1 <> component], and then by Hfull,
             [In (Cobservation Receive (Cpremessage p n1) component) obs],
           or [n1 = component], and then by Hfull,
            [In (Cobservation Send (Cpremessage p n1) n0) obs].
           And we can have an invariant saying any message that has a Send observation
           in a protocol state is a protocol message.

           How do we prove that [Sy] is a protocol state?

           Hfull implies that [Cobservation Receive (Cpremessate p n1) n0] is stored in obs.
           Not necessarily: it may also happen that [Cobservation Send (Cpremessage p n1) n0]
           is stored in obs. But in both cases, [Cpremessage p n1] should be protocol, right?
           
           We have some invariant saying that all messages for which we have
           a Receive observation in obs satisfy isProtocol.

           But do we have a Receive observation for [Cpremessage p n1] ?
           
         *)

        assert(Hin' : n1 = component ->
                     In (Cobservation Send (Cpremessage p component) component)
                        (observationsOf (st (component_to_index component)))).
        {
          intros. subst.
          pose proof (Hin := fullNode_last_receive_self _ _ _ _ _ _ Hfull).
          exact Hin.
        }
        
        assert (Hmproto: protocol_message_prop free_composite_elmo (Cpremessage p n1)).
        {
          destruct (decide (n1 = component)).
          + subst.
            specialize (Hin' (eq_refl component)).
            (* Maybe the state from which the protocol message is sent can reach st? *)
            eapply has_send_observation_implies_is_protocol.
            2: { apply Hin'. }
            exact Hpsp.
          + 
            (*Check all_receive_observation_have_component_as_witness.
            Check fullNode_last_receive_not_self.*)
            apply nesym in n2.
            pose proof (Hin := fullNode_last_receive_not_self _ _ _ _ _ _ _ n2 Hfull).
            pose proof (Harsip := protocol_state_satisfies_all_received_satisfy_isprotocol_prop _ (component_to_index component) Hpsp).
            unfold all_received_satisfy_isprotocol_prop in Harsip.
            rewrite -> Forall_forall in Harsip.
            rewrite Heqobs in Hin.
            specialize (Harsip _ Hin).
            simpl in Harsip. clear Hin.

           (* Maybe the state from which [Cpremessage p n2] is sent can reach st? *)
            eapply (has_receive_observation_implies_is_protocol _ _ _ Hpsp).
            eapply fullNode_last_receive_not_self.
            2: { rewrite Heqobs in Hfull.
                 rewrite -[component]component_to_index_to_component in Hfull.
                 exact Hcomval.
                 rewrite index_to_component_to_index in Hfull.
                 apply Hfull.
            }
 
            
            erewrite -> component_to_index_to_component.
            exact n2.
            exact Hcomval.
        }
        (* We have a protocol state Sy such that [Sy (component_to_index n) = Cprestate l]. *)
        pose proof (Htmp := protocol_message_was_sent_from_protocol_state _ _ _ Hs).
        destruct Htmp as [[Sy [Hsyproto Hsyn]] Hin''].
        (* Maybe s0 is reachable from Sy ? *)

        (* When the component [n] receives [Cpremessage p n1] in [Sy], the result is some state [Sx]
           satisfying [Sx (component_to_index n)
                       = (Cprestate (l ++ [Cobservation Receive (Cpremessage p n1) n0]))].
         *)
        destruct Hsyproto as [omSy Hsyproto].
        destruct Hmproto as [_sm Hmproto].
        (* Maybe _sm can reach st? *)
        pose proof (Hgen := protocol_generated free_composite_elmo (existT _ (component_to_index n) Receive) _ _ Hsyproto _ _ Hmproto).
        (* TODO how do we know the message is valid in the state? *)
        unfold valid in Hgen. simpl in Hgen.
        unfold constrained_composite_valid in Hgen. unfold free_constraint in Hgen. simpl in Hgen.
        unfold vvalid in Hgen. simpl in Hgen.
        rewrite Hsyn in Hgen. simpl in Hgen.
        rewrite component_to_index_to_component in Hgen.
        { exact Haddr. }
        
        assert (Hfn: fullNode (Cpremessage p n1) l n).
        {
          destruct (decide (n1 = n)).
          2: { eapply isProtocol_last_fullNode. exact n2. apply Hproto'. }
          subst n1.
          (* Now: thanks to Hproto, we have [In (Cobservation Send (Cpremessage p n) n) l].
             And an invariant should hold that for all 'send' observations, fullNode holds
             (with the prefix). And (3), the prefix is a prefix of [l].
           *)
          pose proof (Hinp := isProtocol_last_sendInPrefix _ _ _ _ Hproto').
          pose proof (Hfn := sent_is_fullNode).
          specialize (Hfn Sy (Cpremessage p n)).
          specialize (Hfn n n Haddr).
          unfold protocol_state_prop in Hfn.
          specialize (Hfn (@ex_intro _ _ omSy Hsyproto)).
          simpl in Hfn.
          specialize (Hfn (eq_refl n)).
          rewrite Hsyn in Hfn.
          simpl in Hfn.
          specialize (Hfn Hinp).
          exact Hfn.
          (*
          Print ex_intro.
          Check sent_is_protocol.
          epose proof (Hpmp := sent_is_protocol _ _ _ Haddr).
          
          epose proof (Hpmp := sent_is_protocol _ _ _ Haddr Hpsp).
          specialize (Hpmp Hinp).
          Search fullNode.
          Check fullNode_appone.
          pose proof (Hfull' := fullNode_appone _ _ _ _ _ Hfull).
          Search obs. Search _sm.
          *)
        }
        inversion Hfn. rewrite H1 in Hgen.
        Check protocol_message_has_valid_sender.
        pose proof (Haddr' := protocol_message_has_valid_sender _ _ (@ex_intro _ _ _sm Hmproto)).
        assert (Hain : bool_decide (In n1 addresses) = true).
        {
          unfold address_valid in Haddr'.
          assert (In n1 (seq 0 (length indices))).
          { apply in_seq. split; lia. }
          apply bool_decide_eq_true. exact H.
        }
        rewrite Hain in Hgen. simpl in Hgen. clear Haddr' Hain H1.
        (* How to prove the non-self-equivocation check in Hgen?
           By [Hmproto] we know that [Cpremessage p n] is protocol (in the composite);
           therefore, it must have been sent by the node [n], and therefore
           [n] should have its Send observation in the state (that is, in [l]).
         *)

        assert (n1 = n -> In (Cobservation Send (Cpremessage p n1) n) l).
        { intros. subst n1.
          Search Sy.
          Check protocol_message_was_sent_from_protocol_state.
        }
        
                                                         
        
        (*
        Check protocol_state_contains_receive_implies_isProtocol.
        Check has_send_observation_implies_is_protocol.
        Search obs.*)

        
        (* [om] is [Some _]. Or not? *)
        destruct om.
        2: {
          unfold vtransition in H0.
          simpl in H0.
          destruct v.
          { inversion H0. }
          inversion H0. subst.
          rewrite H2 in H0. simpl in H0.
        }
        
        subst. clear H0.
        simpl in Hs.
        simpl in IHl.
        (* Now [Cprestate l] is a protocol state (see the hypothesis Hps) *)
        (* We also need the message [Cpremessage p n1] to be protocol;
         the we can prove that [Cprestate (l :: Cobservation Receive (Cpremessage p n1) n0)]
         is also a protocol state.

         Hproto' means that the 'current' node [n] can receive the big message.
         I would need to have
         *)
        Print protocol_prop.


        (*
      assert (n0 = n).
      { unfold isProtocol in Hproto'.
        simpl in Hproto'.
        rewrite fold_left_app in Hproto'.
        simpl in Hproto'.
      }
         *)
        
        Print elmo_vlsm_machine.
        (*remember (mk_vlsm (elmo_vlsm_machine n weights treshold)) as X.*)
        simpl.
        Print protocol_prop.
        pose proof (Hnext := protocol_generated (mk_vlsm (elmo_vlsm_machine n weights treshold)) Receive (Cprestate l) _om Hps).
        Print protocol_message_prop.
        Search protocol_message_prop.
  Abort.

  
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
