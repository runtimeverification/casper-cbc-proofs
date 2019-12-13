Require Import List Streams ProofIrrelevance.
Import ListNotations.
 
From Casper
Require Import preamble ListExtras.

(* 2.2.1 VLSM Parameters *)

Class LSM_sig (message : Type) :=
  { state : Type
  ; label : Type
  ; proto_message_prop : message -> Prop
  ; proto_message_decidable : forall m, {proto_message_prop m} + {~ proto_message_prop m}
  ; proto_message := { m : message | proto_message_prop m }
  ; initial_state_prop : state -> Prop
  ; initial_state := { s : state | initial_state_prop s }
  ; initial_message_prop : proto_message -> Prop
  ; initial_message := { m : proto_message | initial_message_prop m }
  ; s0 : initial_state
  ; m0 : proto_message
  ; l0 : label
  }.

Class VLSM (message : Type) `{Sig : LSM_sig message } :=
  { transition : label -> state * option proto_message -> state * option proto_message
  ; valid : label -> state * option proto_message -> Prop
  }.

Class VLSM_vdecidable (message : Type) `{M : VLSM message} :=
  { valid_decidable : forall l som, {valid l som} + {~valid l som} 
  }.

(* 2.2.2 VLSM protocol states and protocol messages *)

(* We choose here to use the second definition hinted at the end of the 2.2.2 section, i.e., 
we define states and messages together as a property over a product type.
*)

Inductive protocol_prop `{VLSM} : state * option proto_message -> Prop :=
  | protocol_initial_state
      (is : initial_state)
      (s : state := proj1_sig is)
    : protocol_prop (s, None)
  | protocol_initial_message
      (im : initial_message)
      (s : state := proj1_sig s0)
      (om : option proto_message := Some (proj1_sig im))
    : protocol_prop (s, om)
  | protocol_generated
      (l : label)
      (s : state)
      (_om : option proto_message)
      (Hps : protocol_prop (s, _om))
      (_s : state)
      (om : option proto_message)
      (Hps : protocol_prop (_s, om))
      (Hv : valid l (s, om))
    : protocol_prop (transition l (s, om)).

Definition protocol_state_prop `{VLSM} (s : state)
  := exists om : option proto_message, protocol_prop (s, om).

Definition protocol_message_prop `{VLSM} (m : proto_message)
  := exists s : state, protocol_prop (s, (Some m)).

Definition protocol_state
  {message}
  `{V : VLSM message}
  : Type := { s : state | protocol_state_prop s }.

Definition protocol_message
  {message}
  `{V : VLSM message}
  : Type := { m : proto_message | protocol_message_prop m }.

(* Restating validity and transition using protocol_state and protocol_messages. *)

Definition protocol_valid
  {message}
  `{V : VLSM message}
  (l : label)
  (ps_opm : protocol_state * option protocol_message)
  : Prop
  :=
  valid l (proj1_sig (fst ps_opm), option_map (@proj1_sig _ _) (snd ps_opm)).

Definition protocol_transition
  {message}
  `{V : VLSM message}
  (l : label)
  (ps_opm : protocol_state * option protocol_message)
  : state * option proto_message
  :=
  transition l (proj1_sig (fst ps_opm), option_map (@proj1_sig _ _) (snd ps_opm)).

Definition lift_option_proto_message `{VLSM}
  (om : option proto_message)
  (_s : state)
  (Hm : protocol_prop (_s, om))
  : option protocol_message.
destruct om as [m|].
- apply Some. exists m. exists _s. assumption.
- exact None.
Defined.

(* Protocol state characterization - similar to the definition in the report. *)

Lemma protocol_state_prop_iff
  {message}
  `{V : VLSM message}
  : forall s' : state,
  protocol_state_prop s'
  <-> (exists is : initial_state, s' = proj1_sig is)
  \/ exists (s : protocol_state) (l : label) (om : option protocol_message),
    protocol_valid l (s, om)
    /\ s' = fst (protocol_transition l (s, om)).
Proof.
  intros; split.
  - intro Hps'. destruct Hps' as [m' Hs]. inversion Hs; subst
    ; try (left; exists is; reflexivity)
    ; try (left; exists s0; reflexivity)
    .
    right. exists (exist _ s (ex_intro _ _ Hps)). exists l.
    exists (lift_option_proto_message om _s Hps0).
    unfold protocol_valid. unfold protocol_transition.
    unfold lift_option_proto_message. 
    destruct om as [m|]; simpl
    ; simpl
    ; rewrite H0
    ; split
    ; auto
    .
  - intros [[[s His] Heq] | [[s Hps] [l [om [Hv Ht]]]]]; subst.
    + exists None. apply protocol_initial_state.
    + exists (snd (protocol_transition l (exist (fun s1 : state => protocol_state_prop s1) s Hps, om))).
      destruct Hps as [_om Hps].
      specialize (protocol_generated l s _om Hps); intros Hps'.
      unfold protocol_transition.
      destruct om as [[m [_s Hpm]]|].
      * specialize (Hps' _s (Some m) Hpm Hv). simpl.
        destruct (transition l (s, Some m)) as [s' om']. assumption.
      *  specialize (Hps' (proj1_sig s0) None (protocol_initial_state s0) Hv). simpl.
        destruct (transition l (s, None)) as [s' om']. assumption.
Qed.

(* Protocol message characterization - similar to the definition in the report. *)

Lemma protocol_message_prop_iff
  {message}
  `{V : VLSM message}
  : forall m' : proto_message,
  protocol_message_prop m'
  <-> (exists im : initial_message, m' = proj1_sig im)
  \/ exists (s : protocol_state) (l : label) (om : option protocol_message),
    protocol_valid l (s, om)
    /\ Some m' = snd (protocol_transition l (s, om)).
Proof.
  intros; split.
  - intros [s' Hpm'].
    inversion Hpm'; subst
    ; try (left; exists im; reflexivity).
    right. exists (exist _ s (ex_intro _ _ Hps)). exists l.
    exists (lift_option_proto_message om _s Hps0).
    unfold protocol_valid. unfold protocol_transition.
    unfold lift_option_proto_message. 
    destruct om as [m|]
    ; simpl
    ; rewrite H0
    ; split
    ; auto
    .
  - intros [[[m Him] Heq] | [[s Hps] [l [om [Hv Ht]]]]]; subst.
    + exists (proj1_sig s0). apply protocol_initial_message.
    + exists (fst (protocol_transition l (exist (fun s1 : state => protocol_state_prop s1) s Hps, om))).
      destruct Hps as [_om Hps].
      specialize (protocol_generated l s _om Hps); intros Hps'.
      unfold protocol_transition.
      destruct om as [[m [_s Hpm]]|]
      ; specialize (Hps' _s (Some m) Hpm Hv) || specialize (Hps' (proj1_sig s0) None (protocol_initial_state s0) Hv)
      ; simpl
      ; unfold protocol_transition in Ht; simpl in Ht
      ; destruct (transition l (s, Some m)) as [s' om'] || destruct (transition l (s, None)) as [s' om']
      ; simpl in Ht; subst
      ;  assumption
      .
Qed.

Corollary protocol_state_destruct
  {message}
  `{V : VLSM message}
  : forall s' : protocol_state,
    (exists is : initial_state, proj1_sig s' = proj1_sig is)
    \/ exists (s : protocol_state) (l : label) (om : option protocol_message),
      protocol_valid l (s, om)
      /\ proj1_sig s' = fst (protocol_transition l (s, om)).
Proof.
  intros [s' Hps']. simpl. apply protocol_state_prop_iff. assumption.
Qed.

(* Induction principle for protocol states *)

Lemma protocol_state_ind
  {message}
  `{V : VLSM message}
  : forall (P : state -> Prop),
  (forall is : initial_state, P (proj1_sig is)) ->
  (forall (s : protocol_state) (Hind : P (proj1_sig s)) (l : label) (om : option protocol_message)
          (Hv : protocol_valid l (s, om)),
          P (fst (protocol_transition l (s, om)))) ->
  (forall s : protocol_state, P (proj1_sig s)).
Proof.
  intros P HIi HIt.
  assert (Hind : forall som' : state * option proto_message, protocol_prop som' -> P (fst som')).
  { intros som' Hp.
    induction Hp; try apply HIi.
    specialize (HIt (exist _ s (ex_intro _ _ Hp1)) IHHp1 l (lift_option_proto_message om _s Hp2)).
    unfold protocol_valid in HIt. 
    unfold lift_option_proto_message in HIt. 
    destruct om as [m|]
    ; specialize (HIt Hv)
    ; assumption.
  }
  intros [s' [om' Hps]]. simpl.
  specialize (Hind (s', om') Hps). assumption.
Qed.

(* Valid VLSM transitions *)

Definition verbose_valid_protocol_transition {message} `{VLSM message} (l : label) (s s' : state) (om om' : option proto_message) :=
  protocol_prop (s, om) /\ 
  valid l (s, om) /\
  transition l (s, om) = (s', om') /\
  protocol_prop (s', om').  

(* Valid VLSM traces *) 
Definition in_state_out {message} `{VLSM message} : Type :=
  option proto_message * state * option proto_message.

Inductive finite_ptrace_from `{VLSM} : state -> list in_state_out -> Prop :=
| finite_ptrace_empty : forall (s : state), protocol_state_prop s -> finite_ptrace_from s []
| finite_ptrace_extend : forall  (s : state) (tl : list in_state_out),
    finite_ptrace_from s tl ->  
    forall (s' : state) (iom oom : option proto_message) (l : label),
    verbose_valid_protocol_transition l s' s iom oom ->
    finite_ptrace_from  s' ((iom, s, oom) :: tl).

Definition finite_ptrace `{VLSM} (ls : list in_state_out) : Prop :=
  finite_ptrace_from (proj1_sig s0) ls. 

Lemma extend_right_finite_trace_from
  {message}
  `{V : VLSM message}
  : forall s1 ts s3 iom3 oom3 l3 (s2 := mid (List.last ts (None,s1,None))),
  finite_ptrace_from s1 ts ->
    verbose_valid_protocol_transition l3 s2 s3 iom3 oom3 ->
  finite_ptrace_from s1 (ts ++ [(iom3,s3,oom3)]).
Proof.
  intros s1 ts s3 iom3 oom3 l3 s2 Ht12 Hv23.
  induction Ht12.
  - simpl. apply finite_ptrace_extend with l3.
    + constructor. unfold verbose_valid_protocol_transition in Hv23. exists oom3. tauto.
    + assumption.
  - rewrite <- app_comm_cons.
    apply finite_ptrace_extend with l; try assumption.
    simpl in IHHt12. apply IHHt12.
    unfold s2 in *; clear s2.
    assert (Heq : (@mid (option (@proto_message message Sig)) (@state message Sig)
            (option (@proto_message message Sig))
            (@List.last
               (option (@proto_message message Sig) * @state message Sig *
                option (@proto_message message Sig)) ((iom, s, oom) :: tl)
               (@None (@proto_message message Sig), s', @None (@proto_message message Sig)))) = (@mid (option (@proto_message message Sig)) (@state message Sig)
     (option (@proto_message message Sig))
     (@List.last
        (option (@proto_message message Sig) * @state message Sig *
         option (@proto_message message Sig)) tl
        (@None (@proto_message message Sig), s, @None (@proto_message message Sig))))).
    { destruct tl. reflexivity.
      f_equal. eapply remove_hd_last. }
    rewrite <- Heq. assumption.
Qed.

CoInductive infinite_ptrace_from `{VLSM} :
  state -> Stream in_state_out -> Prop :=
| infinite_ptrace_extend : forall  (s : state) (tl : Stream in_state_out),
    infinite_ptrace_from s tl ->  
    forall (s' : state) (iom oom : option proto_message) (l : label),
    verbose_valid_protocol_transition l s' s iom oom ->
    infinite_ptrace_from  s' (Cons (iom, s, oom)  tl).

Definition infinite_ptrace `{VLSM} (st : Stream in_state_out) :
  infinite_ptrace_from (proj1_sig s0) st. 

Inductive Trace `{VLSM} : Type :=
  | Finite : list in_state_out -> Trace
  | Infinite : Stream in_state_out -> Trace.

Definition ptrace_from_prop `{VLSM} (s : state) (tr : Trace) : Prop :=
  match tr with 
  | Finite ls => finite_ptrace_from s ls
  | Infinite sm => infinite_ptrace_from s sm
  end. 

Definition ptrace_prop `{VLSM} (tr : Trace) : Prop :=
  ptrace_from_prop (proj1_sig s0) tr.

Definition protocol_trace_from `{VLSM} (s : state) : Type :=
  { tr : Trace | ptrace_from_prop s tr}. 

Definition protocol_trace `{VLSM} : Type :=
  { tr : Trace | ptrace_prop tr}. 

(* Projections of traces *)
Inductive Trace_states `{VLSM} : Type :=
| Finite_states : list state -> Trace_states
| Infinite_states : Stream state -> Trace_states.

Definition protocol_state_trace `{VLSM} (tr : protocol_trace) : Trace_states :=
  match proj1_sig tr with
  | Finite ls => Finite_states (List.map mid ls)
  | Infinite st => Infinite_states (map mid st) end. 

Inductive Trace_messages `{VLSM} : Type :=
| Finite_messages : list (option proto_message) -> Trace_messages
| Infinite_messages : Stream (option proto_message) -> Trace_messages. 

Definition protocol_output_messages_trace `{VLSM} (tr : protocol_trace) : Trace_messages :=
  match proj1_sig tr with
  | Finite ls => Finite_messages (List.map snd ls)
  | Infinite st => Infinite_messages (map snd st) end.

Definition protocol_input_messages_trace `{VLSM} (tr : protocol_trace) : Trace_messages :=
  match proj1_sig tr with
  | Finite ls => Finite_messages (List.map fst (List.map fst ls))
  | Infinite st => Infinite_messages (map fst (map fst st)) end.

(* Defining equivocation on these trace definitions *)
(* Section 6 : "A message m received by a protocol state s with a transition label l in a protocol execution trace is called "an equivocation" if it wasn't produced in that trace" *)

(* Implicitly, the state itself must be in the trace, and minimally the last element of the trace *)
(* Also implicitly, the trace leading up to the state is finite *)
Definition d0 `{VLSM} : in_state_out := (None, proj1_sig s0, None). 

Definition equivocation_in_trace `{VLSM} (msg : proto_message) (s : state) (ls : list in_state_out) (tr : finite_ptrace ls) : Prop :=
  (* Case empty for the last function *) 
  ls = [] \/
  (* Or the list is not empty, and (msg, s, something) is its last element *) 
  (fst (fst (last ls d0)) = Some msg /\
   mid (last ls d0) = s /\
   forall (elem : in_state_out), In elem ls -> snd elem = Some msg -> False).   

Definition equivocation `{VLSM} (msg : proto_message) (s : state) : Prop :=
  forall (ls : list in_state_out) (about_ls : finite_ptrace ls), 
    equivocation_in_trace msg s ls about_ls. 

(* Now we can have decidable equivocations! *) 
(* 6.2.1 Identifying equivocations *)
Definition has_been_sent `{VLSM} (msg : proto_message) (ls : list in_state_out) : Prop :=
  exists (elem : in_state_out),
    In elem ls /\ fst (fst elem) = Some msg. 

(* Since equality of proto_messages is decidable, this function must exist : *) 
Definition proto_message_eqb `{VLSM} : option proto_message -> option proto_message -> bool :=
  fun msg1 msg2 => true.

Fixpoint has_been_sentb `{VLSM} (msg : proto_message) (ls : list in_state_out) : bool :=
  match ls with
  | [] => false
  | hd :: tl => if proto_message_eqb (fst (fst hd)) (Some msg) then true else has_been_sentb msg tl
  end.

(* Now we can show that the above and below definitions are unnecessary *) 

(* Implicitly, the trace must be a protocol trace and also end with the state *) 
Definition finite_ptrace_upto `{VLSM} (s : state) : list in_state_out -> Prop :=
  fun ls => finite_ptrace ls /\ ls <> [] /\ mid (last ls d0) = s. 

Definition has_been_sent_minimal `{VLSM} (msg : proto_message) (ls : list in_state_out) (s : state) : Prop :=
  finite_ptrace_upto s ls /\ has_been_sent msg ls. 

(* 6.2.2 Equivocation-free as a composition constraint *)
Definition composition_constraint `{VLSM} : Type :=
  label -> state * option proto_message -> Prop. 

Definition equivocation_free `{VLSM} : composition_constraint :=
  fun l som => match (snd som) with
            | None => True
            | Some msg => equivocation msg (fst som) -> False
            end.

