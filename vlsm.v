Require Import List Streams ProofIrrelevance.
Import ListNotations.

From Casper
Require Import preamble ListExtras.

(** preamble **)


Definition noneOrAll
  (op : option Prop)
  : Prop
  :=
  match op with
  | None => True
  | (Some p) => p
  end.

Lemma exist_eq
  {X}
  (P : X -> Prop)
  (a b : {x : X | P x})
  : a = b <-> proj1_sig a = proj1_sig b.
Proof.
  destruct a as [a Ha]; destruct b as [b Hb]; simpl.
  split; intros Heq.
  - inversion Heq. reflexivity.
  - subst. apply f_equal. apply proof_irrelevance.
Qed.

Class EqDec X :=
  eq_dec : forall x y : X, {x = y} + {x <> y}.

Lemma DepEqDec
  {X}
  (Heqd : EqDec X)
  (P : X -> Prop)
  : EqDec {x : X | P x}.
Proof.
  intros [x Hx] [y Hy].
  specialize (Heqd x y).
  destruct Heqd as [Heq | Hneq].
  - left. subst. apply f_equal. apply proof_irrelevance.
  - right.  intros Heq. apply Hneq. inversion Heq. reflexivity.
Qed.

Lemma nat_eq_dec : EqDec nat.
Proof.
  unfold EqDec. induction x; destruct y.
  - left. reflexivity.
  - right. intros C; inversion C.
  - right. intros C; inversion C.
  - specialize (IHx y). destruct IHx as [Heq | Hneq].
    + left. subst. reflexivity.
    + right. intros Heq. inversion Heq. contradiction.
Qed.

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

(* *** begin *** *)

Definition verbose_valid_protocol_transition {message} `{VLSM message} (l : label) (s s' : state) (om om' : option proto_message) :=
  protocol_prop (s, om) /\ 
  valid l (s, om) /\
  transition l (s, om) = (s', om') /\
  protocol_prop (s', om').  

(* Alternative way to define traces *)
(* 
Record trace_element `{VLSM} : Type :=
  { l_in : label;
    msg_in : option proto_message;
    s : state;
    msg_out : option proto_message;
  }. 
*)
Definition in_state_out {message} `{VLSM message} : Type := option proto_message * state * option proto_message.

Definition mid {X Y Z : Type} (xyz : X * Y * Z) : Y :=
  snd (fst xyz). 

Inductive finite_ptrace `{VLSM} :
  list in_state_out -> Prop :=
| finite_ptrace_empty : finite_ptrace []
| finite_ptrace_singleton : forall (s : state), protocol_state_prop s -> finite_ptrace [(None, s, None)]
| finite_ptrace_extend : forall  (hd : in_state_out) (tl : list in_state_out),
    finite_ptrace (hd :: tl) ->
    forall (hd' : in_state_out) (l : label),
    verbose_valid_protocol_transition l (mid hd) (mid hd') (snd hd) (snd hd') ->
    finite_ptrace (hd' :: hd :: tl). 

CoInductive infinite_ptrace `{VLSM} :
  Stream in_state_out -> Prop :=
| infinite_ptrace_extend :
    forall (hd : in_state_out) (sm : Stream in_state_out),
      infinite_ptrace (Cons hd sm) -> 
      forall (hd' : in_state_out) (l : label),
    verbose_valid_protocol_transition l (mid hd) (mid hd') (snd hd) (snd hd') ->
    infinite_ptrace (Cons hd' (Cons hd sm)).

Inductive Trace_verbose `{VLSM} : Type :=
  | Fin : list in_state_out -> Trace_verbose
  | Inf : Stream in_state_out -> Trace_verbose.

Definition ptrace_prop `{VLSM} (tr : Trace_verbose) : Prop :=
  match tr with 
  | Fin ls => finite_ptrace ls
  | Inf sm => infinite_ptrace sm
  end. 

Definition protocol_trace_type `{VLSM} : Type :=
  { tr : Trace_verbose | ptrace_prop tr}. 

(* Defining equivocation on these trace definitions *)
(* Section 6 : "A message m received by a protocol state s with a transition label l in a protocol execution trace is called "an equivocation" if it wasn't produced in that trace" *)

(* Implicitly, the state itself must be in the trace, and minimally the last element of the trace *)
(* Also implicitly, the trace leading up to the state is finite *)
Definition d0 `{VLSM} : in_state_out := (None, proj1_sig s0, None). 

Definition equivocation_in_trace `{VLSM} (msg : proto_message) (s : state) (ls : list in_state_out) (about_ls : finite_ptrace ls) : Prop :=
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

Lemma has_been_sent_correct `{HV : VLSM} :
  forall (msg : proto_message) (ls : list in_state_out),
    has_been_sent msg ls <-> has_been_sentb msg ls = true. 
Proof.     
Admitted.   

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

(* *** end *** *)

Definition labeled_valid_transition
  {message}
  `{V : VLSM message}
  (opm : option protocol_message)
  (l : label)
  (ps ps' : protocol_state)
  : Prop
  :=
  protocol_valid l (ps, opm) /\ fst (protocol_transition l (ps, opm)) = proj1_sig ps'.

Definition valid_transition
  {message}
  `{V : VLSM message}
  (ps ps' : protocol_state)
  : Prop
  :=
  exists opm : option protocol_message,
  exists l : label,
  labeled_valid_transition opm l ps ps'.

(* Valid  VLSM trace *)

Inductive valid_trace
  {message}
  `{V : VLSM message}
  : protocol_state -> protocol_state -> Prop :=
  | valid_trace_one
    : forall s s',
    valid_transition s s' ->
    valid_trace s s'
  | valid_trace_more
    : forall s s' s'',
    valid_transition s s' ->
    valid_trace s' s'' ->
    valid_trace s s''
  .

Lemma extend_valid_trace
  {message}
  `{V : VLSM message}
  : forall s1 s2 s3,
  valid_trace s1 s2 ->
  valid_transition s2 s3 ->
  valid_trace s1 s3.
Proof.
  intros s1 s2 s3 Htrace.
  induction Htrace as [s1 s2 Ht12| s1 s1' s2 Ht11' Htrace1'2 IHtrace1'3]; intros Ht23.
  - apply valid_trace_more with s2; try assumption.
    apply valid_trace_one. assumption.
  - specialize (IHtrace1'3 Ht23).
    apply valid_trace_more with s1'; assumption.
Qed.

Definition valid_reflexive_trace
  {message}
  `{V : VLSM message}
  (s s' : protocol_state)
  : Prop
  :=
  s = s' \/ valid_trace s s'.

Lemma extend_valid_reflexive_trace
  {message}
  `{V : VLSM message}
  : forall s1 s2 s3,
  valid_reflexive_trace s1 s2 ->
  valid_transition s2 s3 ->
  valid_trace s1 s3.
Proof.
  intros s1 s2 s3 Htrace12 Ht23.
  destruct Htrace12 as [Heq | Htrace12].
  - subst. apply valid_trace_one. assumption.
  - apply extend_valid_trace with s2; assumption.
Qed.


Definition labeled_valid_message_production
  {message}
  `{V : VLSM message}
  (opm : option protocol_message)
  (l : label)
  (ps : protocol_state)
  (pm' : protocol_message)
  : Prop
  :=
  protocol_valid l (ps, opm) /\ snd (protocol_transition l (ps, opm)) = Some (proj1_sig pm').

Definition valid_message_production
  {message}
  `{V : VLSM message}
  (s : protocol_state)
  (m' : protocol_message)
  : Prop
  :=
  exists opm : option protocol_message,
  exists l : label,
  labeled_valid_message_production opm l s m'.

Definition valid_trace_message
  {message}
  `{V : VLSM message}
  (s : protocol_state)
  (m' : protocol_message)
  : Prop
  :=
  exists s', valid_reflexive_trace s s' /\ valid_message_production s' m'.

Lemma valid_protocol_message
  {message}
  `{V : VLSM message}
  : forall (pm : protocol_message),
  (exists im : initial_message, proj1_sig pm = proj1_sig im)
  \/
  (exists (s : protocol_state),
   exists (pm' : protocol_message),
   valid_trace_message s pm' /\ proj1_sig pm = proj1_sig pm').
Proof.
  intros. destruct pm as [m Hpm].  simpl.
  apply protocol_message_prop_iff in Hpm as Hpm'.
  destruct Hpm' as [Him | [s [l [om [Hv Ht]]]]]; try (left; assumption).
  right. exists s. exists (exist _ m Hpm). simpl. split; auto.
  exists s. split; try (left; auto).
  exists om. exists l. split; auto.
Qed.

(* Trace segments *)

Inductive trace_from_to
  {message}
  `{V : VLSM message}
  : protocol_state -> protocol_state -> list protocol_state -> Prop
  :=
  | trace_from_to_one
    : forall s1 s2, valid_transition s1 s2 -> trace_from_to s1 s2 [s1; s2]
  | trace_from_to_more
    : forall s1 s3 ts s2, valid_transition s1 s2 -> trace_from_to s2 s3 ts -> trace_from_to s1 s3 (s1 :: ts)
  .

Lemma extend_trace_from_to_left
  {message}
  `{V : VLSM message}
  : forall s1 s2 s3 ls,
  trace_from_to s2 s3 ls ->
  valid_transition s1 s2 ->
  trace_from_to s1 s3 (s1 :: ls).
Proof.
  intros s1 s2 s3 ls Ht23 Hv12.
  apply trace_from_to_more with s2; assumption.
Qed.

Lemma extend_trace_from_to_right
  {message}
  `{V : VLSM message}
  : forall s1 s2 s3 ls,
  trace_from_to s1 s2 ls ->
  valid_transition s2 s3 ->
  trace_from_to s1 s3 (ls ++ [s3]).
Proof.
  intros s1 s2 s3 ls Ht12 Hv23.
  induction Ht12 as [s1 s2 Hv12 | s1 s2 ls s1' Hv11' Ht1'2 Ht1'3].
  - simpl. apply trace_from_to_more with s2; try assumption.
    apply trace_from_to_one. assumption.
  - specialize (Ht1'3 Hv23).
    rewrite <- app_comm_cons.
    apply extend_trace_from_to_left with s1'; assumption.
Qed.

(* Infinite trace from state *)

CoInductive infinite_trace_from
  {message}
  `{V : VLSM message}
  : protocol_state -> Stream protocol_state -> Prop
  :=
  | infinite_trace_first
    : forall s1 ts s2,
    valid_transition s1 s2 ->
    infinite_trace_from s2 ts ->
    infinite_trace_from s1 (Cons s1 ts)
.


(* A trace is either finite or infinite *)

Inductive Trace `{VLSM} : Type :=
  | Finite : list protocol_state -> Trace
  | Infinite : Stream protocol_state -> Trace
  .

(* finite traces originating in a set *)

Definition filtered_finite_trace
  {message}
  `{V : VLSM message}
  (subset : protocol_state -> Prop)
  (ts : list protocol_state)
  : Prop
  :=
  match ts with
  | [] => False
  | [s] => False
  | s :: t => subset s /\ trace_from_to s (last t s) ts
  end.

Definition initial_protocol_state_prop
  {message}
  `{V : VLSM message}
  (ps : protocol_state)
  : Prop
  :=
  initial_state_prop (proj1_sig ps).

Definition start_protocol_state_prop `{VLSM} (s0 : protocol_state) (ts : list protocol_state) : Prop :=
  filtered_finite_trace (fun s => s = s0) ts. 
           

(* finite traces originating in the set of initial states *)

Definition protocol_finite_trace_prop
  {message}
  `{V : VLSM message}
  (ts : list protocol_state)
  : Prop
  := filtered_finite_trace initial_protocol_state_prop ts.

(* infinite traces originating in a set *)

Definition filtered_infinite_trace
  {message}
  `{V : VLSM message}
  (subset : protocol_state -> Prop)
  (ts : Stream protocol_state)
  : Prop
  :=
  subset (hd ts) /\ infinite_trace_from (hd ts) ts.

(* infinite traces originating in the set of initial states *)

Definition protocol_infinite_trace_prop
  {message}
  `{V : VLSM message}
  (ts : Stream protocol_state)
  : Prop
  := filtered_infinite_trace initial_protocol_state_prop ts.

(* a protocol trace is a (finite or infinite) trace,
originating in the set of initial states *)

Definition protocol_trace_prop
  {message}
  `{V : VLSM message}
  (t : Trace)
  : Prop
  :=
  match t with
  | Finite ts => protocol_finite_trace_prop ts
  | Infinite ts => protocol_infinite_trace_prop ts
  end.

Definition protocol_trace
  {message}
  `{V : VLSM message}
  : Type := { t : Trace | protocol_trace_prop t}.

Definition protocol_trace_proj1
  `{VLSM}
  (tr : protocol_trace) 
  : Trace := proj1_sig tr.

Coercion protocol_trace_proj1 : protocol_trace >-> Trace.

(* a protocol trace segment is a (finite or infinite) trace, 
originating in some set of states *)
Definition protocol_trace_from_prop `{VLSM} (P : protocol_state -> Prop) (t : Trace) : Prop :=
  match t with
  | Finite ts => filtered_finite_trace P ts 
  | Infinite ts => filtered_infinite_trace P ts
  end.

Definition protocol_trace_from `{VLSM} (P : protocol_state -> Prop) : Type :=
  { t : Trace | protocol_trace_from_prop P t}. 

Definition protocol_trace_from_proj1
  `{VLSM} {P}
  (tr : protocol_trace_from P) 
  : Trace := proj1_sig tr.

Coercion protocol_trace_from_proj1 : protocol_trace_from >-> Trace.

Definition first
  {message}
  `{V : VLSM message}
  (pt : protocol_trace) : protocol_state.
  destruct pt as [[t | t] Hpt]; simpl in Hpt.
  - unfold protocol_finite_trace_prop in Hpt.
    destruct t as [| h t]; simpl in Hpt; try contradiction.
    exact h.
  - destruct t as [h t].
    exact h.
Defined.

Definition last
  {message}
  `{V : VLSM message}
  (pt : protocol_trace) : option protocol_state.
  destruct pt as [[t | t] Hpt]; simpl in Hpt.
  - unfold protocol_finite_trace_prop in Hpt.
    destruct t as [| h t]; simpl in Hpt; try contradiction.
    exact (Some (last t h)).
  - exact None.
Defined.

Lemma extend_protocol_trace
  {message}
  `{V : VLSM message}
  : forall (pt2 : protocol_trace) s2 s3,
  last pt2 = Some s2 ->
  valid_transition s2 s3 ->
  exists (pt3 : protocol_trace),  last pt3 = Some s3.
Proof.
  intros [[t2 | t2] Hpt2] s2 s3 Hlast2 Hv.
  - unfold protocol_trace_prop in Hpt2. unfold protocol_finite_trace_prop in Hpt2. unfold filtered_finite_trace in Hpt2.
    destruct t2 as [| s1 [| s1' t2]]; try contradiction.
    destruct Hpt2 as [His1 Ht12]. simpl in Hlast2. simpl in Ht12. inversion Hlast2 as [Hlast2']. rewrite Hlast2' in Ht12.
    apply (extend_trace_from_to_right s1 s2 s3) in Ht12; try assumption.
    assert (Hpt3 : protocol_trace_prop (Finite ((s1 :: s1' :: t2) ++ [s3]))).
    { unfold protocol_trace_prop. unfold protocol_finite_trace_prop. unfold filtered_finite_trace. simpl.
      rewrite last_is_last. split; try assumption. destruct t2; assumption.
    }
    exists (exist _ (Finite ((s1 :: s1' :: t2) ++ [s3])) Hpt3).
    simpl. apply f_equal. rewrite last_is_last. destruct t2; reflexivity.
  - simpl in Hlast2. inversion Hlast2.
Qed.

(* Any protocol state is reachable through a (finite) protocol_trace. *)
Lemma protocol_state_reachable
  {message}
  `{V : VLSM message}
  : forall ps : protocol_state,
  initial_state_prop (proj1_sig ps) \/
  exists t : protocol_trace,
  exists ps' : protocol_state,
  last t = Some ps' /\ proj1_sig ps = proj1_sig ps'.
Proof.
  apply (protocol_state_ind
    (fun s => 
      initial_state_prop s \/ 
      exists t : protocol_trace, exists ps' : protocol_state, last t = Some ps' /\ s = proj1_sig ps'
    )); intros.
  - left. destruct is as [s His]. assumption.
  - right.
    remember (fst (protocol_transition l (s, om))) as s'.
    assert (Hps' : protocol_state_prop s') by
        (apply protocol_state_prop_iff; right; exists s; exists l; exists om; split; assumption).
    remember (exist _ s' Hps') as ps'.
    assert (Hvt : valid_transition s ps').
    { subst. exists om. exists l. split; try assumption. reflexivity. }
    destruct Hind as [His | Hstep]
    + remember (exist _ (proj1_sig s) His) as is.
      assert (Hips : initial_protocol_state_prop s)
        by (subst; unfold initial_protocol_state_prop; assumption).
      assert (Pt : trace_from_to s ps' [s; ps']) by (apply trace_from_to_one; assumption).
      assert (Hpt : protocol_trace_prop (Finite [s; ps']))  by (split; assumption).
      exists (exist _ (Finite [s; ps']) Hpt). exists ps'. subst. simpl. split; reflexivity.
    + destruct Hstep as [pt [ps [Heq_last Heq_s]]].
      assert (s = ps) by (destruct s; destruct ps; simpl in Heq_s; subst; apply f_equal; apply proof_irrelevance).
      rewrite H in Hvt.
      apply (extend_protocol_trace pt ps ps') in Hvt; try assumption.
      destruct Hvt as [pt' Hlast].
      exists pt'. exists ps'. split; subst; auto.
Qed.

(* A final state is one which is stuck (no further valid transition is possible) *)

Definition final_state_prop
  {message}
  `{V : VLSM message}
  (s : protocol_state)
  : Prop
  :=
  ~ exists s' : protocol_state, valid_transition s s'.

Definition final_state
  {message}
  `{V : VLSM message}
  : Type := { s : protocol_state | final_state_prop s}.

(* A terminating trace is a finite protocol_trace ending in a final state *)

Definition terminating_trace_prop
  {message}
  `{V : VLSM message}
  (t : protocol_trace)
  : Prop
  :=
  match last t with
  | Some ps => final_state_prop ps
  | None => False
  end.

Definition infinite_trace_prop
  {message}
  `{V : VLSM message}
  (t : protocol_trace)
  : Prop
  :=
  last t = None.

(* A complete trace is either inifinite or terminating  *)

Definition complete_trace_prop
  {message}
  `{V : VLSM message}
  (t : protocol_trace)
  : Prop
  :=
  infinite_trace_prop t \/ terminating_trace_prop t.
