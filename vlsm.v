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

    Class VLSM {message : Type} (lsm : LSM_sig message) :=
      { transition : label -> state * option proto_message -> state * option proto_message
        ; valid : label -> state * option proto_message -> Prop
      }.

    Section VLSM.

      Context
        {message : Type}
        {Sig : LSM_sig message}
        (vlsm : VLSM Sig). 

      Definition sign (vlsm : VLSM Sig):=
        Sig.

      (* 2.2.2 VLSM protocol states and protocol messages *)

      (* We choose here to use the second definition hinted at the end of the 2.2.2 section, i.e., 
we define states and messages together as a property over a product type. *)

      Inductive protocol_prop : state * option proto_message -> Prop :=
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

      Definition protocol_state_prop (s : state) :=
        exists om : option proto_message, protocol_prop (s, om).

      Definition protocol_message_prop (m : proto_message) :=
        exists s : state, protocol_prop (s, (Some m)).

      Definition protocol_state : Type :=
        { s : state | protocol_state_prop s }.

      Definition protocol_message : Type :=
        { m : proto_message | protocol_message_prop m }.
      
      (* Restating validity and transition using protocol_state and protocol_messages. *)

      Definition protocol_valid
                 (l : label)
                 (ps_opm : protocol_state * option protocol_message)
        : Prop :=
        valid l (proj1_sig (fst ps_opm), option_map (@proj1_sig _ _) (snd ps_opm)).

      Definition protocol_transition
                 (l : label)
                 (ps_opm : protocol_state * option protocol_message)
        : state * option proto_message :=
        transition l (proj1_sig (fst ps_opm), option_map (@proj1_sig _ _) (snd ps_opm)).

      Definition lift_option_proto_message 
                 (om : option proto_message)
                 (_s : state)
                 (Hm : protocol_prop (_s, om))
        : option protocol_message.
        destruct om as [m|].
        - apply Some. exists m. exists _s. assumption.
        - exact None.
      Defined.

      (* Protocol state characterization - similar to the definition in the report. *)

      Lemma protocol_state_prop_iff :
        forall s' : state,
          protocol_state_prop s'
          <-> (exists is : initial_state, s' = proj1_sig is)
            \/ exists (s : protocol_state) (l : label) (om : option protocol_message),
              protocol_valid l (s, om)
              /\ s' = fst (protocol_transition l (s, om)).
      Proof.
        intros; split.
        - intro Hps'. destruct Hps' as [m' Hs].
          inversion Hs; subst
          ; try (left; exists is; reflexivity)
          ; try (left; exists s0; reflexivity).
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
              destruct (transition l (s, Some m)) as [s' om'].
              assumption.
            * specialize (Hps' (proj1_sig s0) None (protocol_initial_state s0) Hv). simpl.
              destruct (transition l (s, None)) as [s' om']. assumption.
      Qed.

      (* Protocol message characterization - similar to the definition in the report. *)

      Lemma protocol_message_prop_iff :
        forall m' : proto_message,
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

      Corollary protocol_state_destruct :
        forall s' : protocol_state,
          (exists is : initial_state, proj1_sig s' = proj1_sig is)
          \/ exists (s : protocol_state) (l : label) (om : option protocol_message),
            protocol_valid l (s, om)
            /\ proj1_sig s' = fst (protocol_transition l (s, om)).
      Proof.
        intros [s' Hps']. simpl. apply protocol_state_prop_iff. assumption.
      Qed.

      (* Induction principle for protocol states *)

      Lemma protocol_state_ind
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

      Definition verbose_valid_protocol_transition
                 (l : label)
                 (s s' : state)
                 (om om' : option proto_message)
        :=
          exists (_om : option proto_message),
            exists (_s : state),
              protocol_prop (s, _om)
              /\  protocol_prop (_s, om)
              /\  valid l (s, om)
              /\  transition l (s, om) = (s', om')
      .

      Lemma protocol_transition_origin
            {l : label}
            {s s' : state}
            {om om' : option proto_message}
            (Ht : verbose_valid_protocol_transition l s s' om om')
        : protocol_state_prop s
      .
      Proof.
        destruct Ht as [_om [_s [Hp _]]]. exists _om. assumption.
      Qed.

      Lemma protocol_transition_destination
            {l : label}
            {s s' : state}
            {om om' : option proto_message}
            (Ht : verbose_valid_protocol_transition l s s' om om')
        : protocol_state_prop s'
      .
      Proof.
        exists om'. 
        destruct Ht as [_om [_s [Hs [Hom [Hv Ht]]]]].
        rewrite <- Ht. apply protocol_generated with _om _s; assumption.
      Qed.

      Lemma protocol_transition_in
            {l : label}
            {s s' : state}
            {m : proto_message}
            {om' : option proto_message}
            (Ht : verbose_valid_protocol_transition l s s' (Some m) om')
        : protocol_message_prop m
      .
      Proof.
        destruct Ht as [_om [_s [Hs [Hm _]]]].
        exists _s. assumption.
      Qed.

      Lemma protocol_transition_out
            {l : label}
            {s s' : state}
            {om : option proto_message}
            {m' : proto_message}
            (Ht : verbose_valid_protocol_transition l s s' om (Some m'))
        : protocol_message_prop m'
      .
      Proof.
        exists s'. 
        destruct Ht as [_om [_s [Hs [Hom [Hv Ht]]]]].
        rewrite <- Ht. apply protocol_generated with _om _s; assumption.
      Qed.

      (* Valid VLSM traces *) 
      Record in_state_out :=
        {   l : label
            ;   input : option proto_message
            ;   destination : state
            ;   output : option proto_message
        }.

      Inductive finite_ptrace_from : state -> list in_state_out -> Prop :=
      | finite_ptrace_empty : forall (s : state), protocol_state_prop s -> finite_ptrace_from s []
      | finite_ptrace_extend : forall  (s : state) (tl : list in_state_out),
          finite_ptrace_from s tl ->  
          forall (s' : state) (iom oom : option proto_message) (l : label),
            verbose_valid_protocol_transition l s' s iom oom ->
            finite_ptrace_from  s' ({| l := l; input := iom; destination := s; output := oom |} :: tl).

      Lemma finite_ptrace_consecutive_valid_transition
            (s : state)
            (tr tr2 : list in_state_out)
            (tr1 : list in_state_out)
            (te1 te2 : in_state_out)
            (Htr : finite_ptrace_from s tr)
            (Heq : tr = tr1 ++ [te1; te2] ++ tr2)
        : verbose_valid_protocol_transition (l te2) (destination te1) (destination te2) (input te2) (output te2).
      Proof.
        generalize dependent s. generalize dependent tr.
        induction tr1.
        - intros tr Heq s Htr. simpl in Heq; subst. inversion Htr; subst. inversion H2; subst. assumption.
        - specialize (IHtr1 (tr1 ++ [te1; te2] ++ tr2) eq_refl).
          intros tr Heq is Htr; subst. inversion Htr; subst.
          simpl in IHtr1. specialize (IHtr1 s H2). assumption.
      Qed.

      Definition finite_ptrace (s : state) (ls : list in_state_out) : Prop :=
        finite_ptrace_from s ls /\ initial_state_prop s.

      Lemma extend_right_finite_trace_from
        : forall s1 ts s3 iom3 oom3 l3 (s2 := List.last (List.map destination ts) s1),
          finite_ptrace_from s1 ts ->
          verbose_valid_protocol_transition l3 s2 s3 iom3 oom3 ->
          finite_ptrace_from s1 (ts ++ [{| l := l3; destination := s3; input := iom3; output := oom3 |}]).
      Proof.
        intros s1 ts s3 iom3 oom3 l3 s2 Ht12 Hv23.
        induction Ht12.
        - simpl. apply finite_ptrace_extend; try assumption.
          constructor. apply (protocol_transition_destination Hv23).
        - rewrite <- app_comm_cons.
          apply finite_ptrace_extend; try assumption.
          simpl in IHHt12. apply IHHt12.
          unfold s2 in *; clear s2.
          replace
            (last (List.map destination tl) s)
            with
              (last (List.map destination ({| l := l1; input := iom; destination := s; output := oom |} :: tl)) s')
          ; try assumption.
          rewrite map_cons.
          destruct tl; try reflexivity.
          rewrite map_cons.
          eapply remove_hd_last.
      Qed.

      CoInductive infinite_ptrace_from :
        state -> Stream in_state_out -> Prop :=
      | infinite_ptrace_extend : forall  (s : state) (tl : Stream in_state_out),
          infinite_ptrace_from s tl ->  
          forall (s' : state) (iom oom : option proto_message) (l : label),
            verbose_valid_protocol_transition l s' s iom oom ->
            infinite_ptrace_from  s' (Cons {| l := l; input := iom; destination := s; output := oom |}  tl).

      Lemma infinite_ptrace_consecutive_valid_transition 
            (is : state)
            (tr tr2 : Stream in_state_out)
            (tr1 : list in_state_out)
            (te1 te2 : in_state_out)
            (Htr : infinite_ptrace_from is tr)
            (Heq : tr = stream_app (tr1 ++ [te1; te2]) tr2)
        : verbose_valid_protocol_transition (l te2) (destination te1) (destination te2) (input te2) (output te2).
      Proof.
        generalize dependent is. generalize dependent tr.
        induction tr1.
        - intros tr Heq is Htr. simpl in Heq; subst. inversion Htr; subst. inversion H2; subst. assumption.
        - specialize (IHtr1 (stream_app (tr1 ++ [te1; te2]) tr2) eq_refl).
          intros tr Heq is Htr; subst. inversion Htr; subst.
          specialize (IHtr1 s H2). assumption.
      Qed.

      Definition infinite_ptrace (s : state) (st : Stream in_state_out)
        := infinite_ptrace_from s st /\ initial_state_prop s.

      Inductive Trace : Type :=
      | Finite : state -> list in_state_out -> Trace
      | Infinite : state -> Stream in_state_out -> Trace.

      Definition ptrace_prop (tr : Trace) : Prop :=
        match tr with 
        | Finite s ls => finite_ptrace s ls
        | Infinite s sm => infinite_ptrace s sm
        end. 

      Definition protocol_trace : Type :=
        { tr : Trace | ptrace_prop tr}. 

      (* Projections of traces *)
      Inductive Trace_states : Type :=
      | Finite_states : list state -> Trace_states
      | Infinite_states : Stream state -> Trace_states.

      Definition trace_nth (tr : Trace)
        : nat -> option state :=
        fun (n : nat) =>
          match tr with
          | Finite s ls => nth_error (s::List.map destination ls) n
          | Infinite s st => Some (Str_nth n (Cons s (Streams.map destination st)))
          end. 

      Definition protocol_state_trace (tr : protocol_trace) : Trace_states :=
        match proj1_sig tr with
        | Finite s ls => Finite_states (s :: List.map destination ls)
        | Infinite s st => Infinite_states (Cons s (map destination st)) end. 

      Definition trace_last (tr : Trace) : option state
        :=
          match tr with
          | Finite s ls => Some (last (List.map destination ls) s)
          | Infinite _ _ => None
          end.

      Definition trace_first (tr : Trace) : state
        :=
          match tr with
          | Finite s _ => s
          | Infinite s _ => s
          end.

      Inductive Trace_messages : Type :=
      | Finite_messages : list (option proto_message) -> Trace_messages
      | Infinite_messages : Stream (option proto_message) -> Trace_messages. 

      Definition protocol_output_messages_trace (tr : protocol_trace) : Trace_messages :=
        match proj1_sig tr with
        | Finite _ ls => Finite_messages (List.map output ls)
        | Infinite _ st => Infinite_messages (map output st) end.

      Definition protocol_input_messages_trace (tr : protocol_trace) : Trace_messages :=
        match proj1_sig tr with
        | Finite _ ls => Finite_messages (List.map input ls)
        | Infinite _ st => Infinite_messages (map input st) end.

      (* Defining equivocation on these trace definitions *)
      (* Section 6 :
  A message m received by a protocol state s with a transition label l in a
  protocol execution trace is called "an equivocation" if it wasn't produced
  in that trace
       *)

      Definition trace_prefix
                 (tr : Trace)
                 (last : in_state_out)
                 (prefix : list in_state_out)
        :=
          match tr with
          | Finite s ls => exists suffix, ls = prefix ++ (last :: suffix)
          | Infinite s st => exists suffix, st = stream_app prefix (Cons last suffix)
          end.

      (** A finite trace is terminating if there's no other trace that contains it as a (proper) prefix.**)

      Definition terminating_trace_prop (tr : Trace) : Prop 
         :=
           match tr with 
           | Finite s ls => 
               (exists (tr : protocol_trace) 
               (last : in_state_out), 
               trace_prefix (proj1_sig tr) last ls) -> False 
           | Infinite s ls => False
           end.

      Definition complete_trace_prop (tr : protocol_trace) : Prop
         := 
            match (proj1_sig tr) with 
            | Finite s ls => terminating_trace_prop (proj1_sig tr)
            | Infinite s ls => True
            end.

      Lemma trace_prefix_protocol
            (tr : protocol_trace)
            (last : in_state_out)
            (prefix : list in_state_out)
            (Hprefix : trace_prefix (proj1_sig tr) last prefix)
        : ptrace_prop (Finite (trace_first (proj1_sig tr)) (prefix ++ [last])).
      Proof.
        destruct tr as [tr Htr]. simpl in *.
        generalize dependent tr. generalize dependent last.
        apply (rev_ind (fun prefix => forall (last : in_state_out) (tr : Trace), ptrace_prop tr -> trace_prefix tr last prefix -> finite_ptrace (trace_first tr) (prefix ++ [last]))).
        - intros last tr Htr Hprefix; destruct tr as [ | ]; unfold trace_prefix in Hprefix;   simpl in Hprefix
          ; destruct Hprefix as [suffix Heq]; subst; destruct Htr as [Htr Hinit]
          ; unfold trace_first; simpl; constructor; try assumption
          ; inversion Htr; subst; clear Htr
          ; specialize
              (finite_ptrace_extend
                 s1 [] (finite_ptrace_empty _ (protocol_transition_destination H3))
                 s iom oom l1); intro Hext
          ; apply Hext; assumption.
        - intros last_p p Hind last tr Htr Hprefix.
          specialize (Hind last_p tr Htr).
          destruct tr as [ | ]; unfold trace_prefix in Hprefix;   simpl in Hprefix
          ; destruct Hprefix as [suffix Heq]; subst; destruct Htr as [Htr Hinit]; simpl; simpl in Hind
          ; split; try assumption
          .
          + assert
              (Hex : exists suffix0 : list in_state_out,
                  (p ++ [last_p]) ++ last :: suffix = p ++ last_p :: suffix0
              ) by (exists (last :: suffix); rewrite <- app_assoc; reflexivity)
            ; specialize (Hind Hex); clear Hex
            ; destruct Hind as [Hptr _]
            ; destruct last
            ; apply extend_right_finite_trace_from
            ; try assumption
            .
            rewrite <- (app_cons {| l := l1; input := input0; destination := destination0; output := output0 |} suffix) in Htr.
            rewrite app_assoc in Htr. 
            rewrite <- (app_assoc p _ _) in Htr. simpl in Htr.
            rewrite <- app_assoc in Htr. 
            specialize
              (finite_ptrace_consecutive_valid_transition
                 s
                 (p ++ [last_p; {| l := l1; input := input0; destination := destination0; output := output0 |}] ++ suffix)
                 suffix
                 p
                 last_p
                 {| l := l1; input := input0; destination := destination0; output := output0 |}
                 Htr
                 eq_refl
              ).
            simpl.
            rewrite map_app. simpl. rewrite last_is_last. tauto.
          + assert
              (Hex : exists suffix0 : Stream in_state_out,
                  stream_app (p ++ [last_p])  (Cons last suffix) = stream_app p (Cons last_p suffix0)
              ) by (exists (Cons last suffix); rewrite <- stream_app_assoc; reflexivity)
            ; specialize (Hind Hex); clear Hex
            ; destruct Hind as [Hptr _]
            ; destruct last
            ; apply extend_right_finite_trace_from
            ; try assumption
            .
            rewrite <- stream_app_cons in Htr.
            rewrite stream_app_assoc in Htr. 
            rewrite <- (app_assoc p _ _) in Htr. simpl in Htr.
            specialize
              (infinite_ptrace_consecutive_valid_transition
                 s
                 (stream_app (p ++ [last_p; {| l := l1; input := input0; destination := destination0; output := output0 |}]) suffix)
                 suffix
                 p
                 last_p
                 {| l := l1; input := input0; destination := destination0; output := output0 |}
                 Htr
                 eq_refl
              ).
            simpl.
            rewrite map_app. simpl. rewrite last_is_last. tauto.
      Qed.

      (* Implicitly, the state itself must be in the trace, and minimally the last element of the trace *)
      (* Also implicitly, the trace leading up to the state is finite *)

      Definition equivocation_in_trace
                 (msg : proto_message)
                 (tr : protocol_trace)
        : Prop
        :=
          exists (last : in_state_out),
          exists (prefix : list in_state_out),
            trace_prefix (proj1_sig tr) last prefix
            /\  input last = Some msg
            /\  ~ In (Some msg) (List.map output prefix)
      .

      Definition equivocation (msg : proto_message) (s : state) : Prop :=
        exists (tr : protocol_trace), trace_last (proj1_sig tr) = Some s /\ equivocation_in_trace msg tr.

      (* Now we can have decidable equivocations! *) 
      (* 6.2.1 Identifying equivocations *)
      Definition has_been_sent (msg : proto_message) (s : state) : Prop :=
        forall (tr : protocol_trace) 
          (last : in_state_out)
          (prefix : list in_state_out)
          (Hpr : trace_prefix (proj1_sig tr) last prefix)
          (Hlast : destination last = s),
          List.Exists (fun (elem : in_state_out) => output elem = Some msg) prefix. 

      (* Since equality of proto_messages is decidable, this function must exist : *) 
      Definition proto_message_eqb {Eqd : EqDec message}
                 (om1 : option proto_message)
                 (om2 : option proto_message)
        : bool
        :=
          match om1, om2 with
          | None, None => true
          | Some m1, Some m2 => if eq_dec (proj1_sig m1) (proj1_sig m2) then true else false
          | _, _ => false
          end.

      Fixpoint has_been_sentb
               {Eqd : EqDec message}
               (msg : proto_message) (ls : list in_state_out) : bool
        :=
          existsb (fun x => proto_message_eqb (output x) (Some msg)) ls.

      (* Now we can show that the above and below definitions are unnecessary *) 

      (* Implicitly, the trace must be a protocol trace and also end with the state *) 
      Definition finite_ptrace_upto 
                 (s : state)
                 (tr : protocol_trace)
        : Prop
        :=
          trace_last (proj1_sig tr) = Some s
      .

      (* 6.2.2 Equivocation-free as a composition constraint *)
      Definition composition_constraint : Type :=
        label -> state * option proto_message -> Prop. 

      Definition equivocation_free : composition_constraint :=
        fun l som => match (snd som) with
                  | None => True
                  | Some msg => equivocation msg (fst som) -> False
                  end.

      (* Protocol runs *) 
      Record proto_run : Type := mk_proto_run
                                   { start : initial_state
                                     ; transitions : list (label * option proto_message * option proto_message)
                                     ; final : state * option proto_message
                                   }.

      Inductive vlsm_run_prop : proto_run -> Prop :=
      | empty_run_initial_state
          (is : initial_state)
          (s : state := proj1_sig is)
        : vlsm_run_prop {| start := is; transitions := []; final := (s, None) |}
      | empty_run_initial_message
          (im : initial_message)
          (s : state := proj1_sig s0)
          (om : option proto_message := Some (proj1_sig im))
        : vlsm_run_prop {| start := s0; transitions := []; final := (s, om) |}
      | extend_run
          (state_run : proto_run)
          (Hs : vlsm_run_prop state_run)
          (s := fst (final state_run))
          (is := start state_run)
          (ts := transitions state_run)
          (msg_run : proto_run)
          (Hm : vlsm_run_prop msg_run)
          (om := snd (final msg_run))
          (l : label)
          (Hv : valid l (s, om))
          (som' := transition l (s, om))
        : vlsm_run_prop {| start := is; transitions := ts ++ [(l, om, snd som')]; final := som' |}.

      Definition vlsm_run : Type :=
        { r : proto_run | vlsm_run_prop r }.

      Lemma run_is_protocol
            (vr : vlsm_run)
        : protocol_prop (final (proj1_sig vr)).
      Proof.
        destruct vr as [r Hr]; simpl.
        induction Hr; simpl in *; try constructor.
        unfold om in *; clear om. unfold s in *; clear s.
        destruct (final state_run) as [s _om].
        destruct (final msg_run) as [_s om].
        specialize (protocol_generated l1 s _om IHHr1 _s om IHHr2 Hv). intro. assumption.
      Qed.

      Lemma protocol_is_run 
            (som' : state * option proto_message)
            (Hp : protocol_prop som')
        : exists vr : vlsm_run, (som' = final (proj1_sig vr)).
      Proof.
        induction Hp.
        - exists (exist _ _ (empty_run_initial_state is)); reflexivity.
        - exists (exist _ _ (empty_run_initial_message im)); reflexivity.
        - destruct IHHp1 as [[state_run Hsr] Heqs]. destruct IHHp2 as [[msg_run Hmr] Heqm]. 
          specialize (extend_run state_run Hsr). simpl. intros Hvr.
          specialize (Hvr msg_run Hmr l1). simpl in Heqs. simpl in Heqm.
          rewrite <- Heqs in Hvr. rewrite <- Heqm in Hvr. specialize (Hvr Hv).
          exists (exist _ _ Hvr). reflexivity.
      Qed.

      (* Decidable VLSMs *) 

      Class VLSM_vdecidable :=
        { valid_decidable : forall l som, {valid l som} + {~valid l som} 
        }.

    End VLSM.

