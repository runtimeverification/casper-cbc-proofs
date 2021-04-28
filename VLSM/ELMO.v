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

Scheme Prestate_mut_ind' := Induction for Prestate Sort Prop
  with Observation_mut_ind' := Induction for Observation Sort Prop
  with Premessage_mut_ind' := Induction for Premessage Sort Prop.
(*
  with ListObservation_mut_ind := Induction for (list Observation) Sort Prop.
 *)
Print Prestate_mut_ind'.
Print Observation_mut_ind'.
Print Premessage_mut_ind'.

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

  Print list_ind.
  Check list_rec.
  Check list_ind.

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

(*  
  (* Almost there *)
  Fixpoint
    Prestate_mut_ind (p : Prestate) : Pps p :=
    match p as p0 return (Pps p0) with
    | Cprestate l => Hps l (ListObservation_mut_ind l)
    end
  with
  ListObservation_mut_ind (lo : list Observation) : Plo lo :=
    match lo as lo0 return (Plo lo0) with
    | [] => Hlonil
    | y::lo0 => Hlocons y lo0 (Observation_mut_ind y) (ListObservation_mut_ind lo0)
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
*)
  
  (* Basically the original
 
  Fixpoint
    Prestate_mut_ind (p : Prestate) : Pps p :=
    match p as p0 return (Pps p0) with
    | Cprestate l => f l
    end
  with
  Observation_mut_ind (o : Observation) : Pob o :=
    match o as o0 return (Pob o0) with
    | Cobservation l p n => f0 l p (Premessage_mut_ind p) n
    end
  with
  Premessage_mut_ind (p : Premessage) : Ppm p :=
    match p as p0 return (Ppm p0) with
    | Cpremessage p0 n => f1 p0 (Prestate_mut_ind p0) n
    end
  .
  *)

  Print list_ind.

  (*
  (* Not strictly decreasing *)
  Fixpoint
    Prestate_mut_ind (p : Prestate) : Pps p :=
    match p as p0 return (Pps p0) with
    | Cprestate l =>
      match l as l0 return (Pps l0) with
      | [] => H0
      | y::l0 => Prestate_mut_ind (Cprestate l0)
      end
      f l
    end
  with
  Observation_mut_ind (o : Observation) : Pob o :=
    match o as o0 return (Pob o0) with
    | Cobservation l p n => f0 l p (Premessage_mut_ind p) n
    end
  with
  Premessage_mut_ind (p : Premessage) : Ppm p :=
    match p as p0 return (Ppm p0) with
    | Cpremessage p0 n => f1 p0 (Prestate_mut_ind p0) n
    end
  .
*)

  
End induction_principle.

Check list_ind.

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

Lemma in_notin_impl_not_eq {A : Type} (x : A) (l1 l2 : list A):
  List.In x l1 ->
  ~List.In x l2 ->
  l1 <> l2.
Proof.
  intros.
  generalize dependent l2.
  induction l1; intros l2 H0.
  - simpl in H. inversion H.
  - destruct l2 as [| b l2].
    + simpl in H.
      discriminate.
    + simpl in H. simpl in H0.
      destruct H as [Heq|Hin].
      * subst. intros Hcontra.
        inversion Hcontra. subst.
        apply H0. left. reflexivity.
      * intros Hcontra. inversion Hcontra. subst. clear Hcontra.
        apply H0. right. apply Hin.
Qed.


Search Prestate.
Lemma Observation_nested_neq ob1 ob2:
  List.In ob1 (observationsOf (stateOf (messageOf ob2))) ->
  ob1 <> ob2.
Proof.
  destruct ob2. simpl. destruct p. simpl. destruct p. simpl.
  intros H.

  Print Observation_mut_ind.
  revert n. revert n0. revert l. generalize dependent l0. generalize dependent ob1.
  Check Observation_mut_ind.
  eapply (Observation_mut_ind
            (fun p : Prestate =>
               forall l0' l1' l2' n0' n1' n n',
                 let ob := Cobservation l2' (Cpremessage p n) n' in
                 In ob l0' ->
                 (*~ (List.In (Cobservation l2' (Cpremessage p n) n') (observationsOf p)) ->*)
                 ob <> Cobservation l1' (Cpremessage (Cprestate l0') n0') n1'
            )
            
            (fun ob1' : Observation =>
               forall l0' ,
               In ob1' l0' ->
               forall l1' n0' n1',
                 ob1' <> Cobservation l1' (Cpremessage (Cprestate l0') n0') n1'
            )

            (fun p' : Premessage =>
               forall l1' l2' l' l0' n0' n1' n',
                 In (Cobservation l' p' n') l0' ->
                 (*~ In (Cobservation l' p' n') (observationsOf ())*)
                 Cobservation l2' p' n' <> Cobservation l1' (Cpremessage (Cprestate l0') n0') n1')
         ).
  3: { intros p H.
 
       (*destruct (decide (l2' = l')).
       { subst. apply H. apply H0. }*)
       destruct l2',l1',l'; try (apply H; apply H0); try congruence.
       
       1,2,3,4: admit.
  }
  
  2: { intros. eapply H. apply H0. }

  1: { intros. simpl in H0.
       intros Hcontra. inversion Hcontra. subst. clear Hcontra.
       eapply in_notin_impl_not_eq.
       apply H. apply H0. reflexivity.
  }
  
  
Abort.

Lemma isProtocol_step_in component weights treshold l1 l2 args x:
  let step := isProtocol_step component weights treshold in
  step (l1 ++ x :: l2) args x =
  step (l1 ++ [x]) args x.
Proof.
  simpl.
  unfold isProtocol_step.
  destruct x. destruct p.
  destruct args as [[[b i] curState] curEq].
  induction l1.
  - destruct l; destruct b; destruct p; simpl; try reflexivity;
    destruct (bool_decide (n0 = component)) eqn:Heqn0;
    destruct (bool_decide (n = component)) eqn:Heqn; simpl; try reflexivity.
    + remember (Cobservation Receive (Cpremessage (Cprestate l) n0) n) as x.
      remember (Cobservation Send (Cpremessage (Cprestate l) n0) component) as x'.
      apply bool_decide_eq_true in Heqn0.
      apply bool_decide_eq_true in Heqn.
      subst n0. subst n.

      repeat (apply pair_equal_spec; split); try reflexivity.
      Print isProtocol.
      (* FIXME: For the lemma to be true, it must hold that x' is not in l2 *)
Abort.
    
  

Lemma fold_isProtocol_step_app component weights treshold l1 l2 b n s es:
  fold_left (isProtocol_step component weights treshold (l1 ++ l2)) l1 (b, n, s, es)
  = fold_left (isProtocol_step component weights treshold l1) l1 (b, n, s, es).
Proof.
  generalize dependent l2.
  generalize dependent b.
  generalize dependent n.
  generalize dependent s.
  generalize dependent es.
  
  remember (length l1) as len.
  assert (Hlen: length l1 <= len).
  { lia. }
  clear Heqlen.
  revert Hlen.
  generalize dependent l1.
  induction len; intros l1 Hlen es s n b l2.
  - destruct l1.
    + reflexivity.
    + simpl in Hlen. lia.
  - destruct (null_or_exists_last l1).
    { subst. reflexivity. }
    destruct H as [l1' [x Hl1]].
    remember (isProtocol_step component weights treshold) as step.
    remember (fold_left (step l1) l1 (b, n, s, es)) as fl.
    destruct fl as [[[b' n'] s'] es'].
    rewrite Hl1. rewrite fold_left_app. simpl.
    rewrite -app_assoc.

    assert (Hlenl1': length l1' <= len).
    { subst l1. rewrite app_length in Hlen. simpl in Hlen. lia. }
    rewrite IHlen.
    { lia. }
    simpl.

    remember (fold_left (step l1') l1' (b, n, s, es)) as fl'.
    destruct fl' as [[[b'' n''] s''] es''].
    subst l1.
    (*rewrite Hl1 in Heqfl.*)

    rewrite fold_left_app in Heqfl. simpl in Heqfl.
    rewrite IHlen in Heqfl.
    { lia. }
    rewrite -Heqfl' in Heqfl.
    rewrite Heqfl. rewrite Heqfl'.
Abort.

Lemma isProtocol_implies_protocol weights treshold m:
  isProtocol (stateOf m) (authorOf m) weights treshold  ->
  let vlsm := mk_vlsm (elmo_vlsm_machine (authorOf m) weights treshold) in
  protocol_message_prop vlsm m.
Proof.
  intros Hproto.
  unfold isProtocol in Hproto.
  destruct m. destruct p. simpl in Hproto. simpl.
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
      (* Not usefull. Clear it. *)
      clear Hproto.


      (*rewrite <- Heqfl in IHl.*)
      
    destruct (fold_left (isProtocol_step n weights treshold))
    simpl. simpl in IHl.
    destruct (bool_decide (n0 = n)).
    + simpl in Hproto.
      admit.
    + simpl in Hproto.
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
