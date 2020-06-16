Require Import List Streams ProofIrrelevance Coq.Arith.Plus Coq.Arith.Minus.
Import ListNotations.
 
From Casper
Require Import Lib.Preamble Lib.ListExtras.

(* 2.2.1 VLSM Parameters *)
  Class VLSM_type (message : Type) :=
    { state : Type
    ; label : Type
    }.

  Class LSM_sig {message : Type} (vtype : VLSM_type message) :=
    { initial_state_prop : state -> Prop
    ; initial_state := { s : state | initial_state_prop s }
    ; initial_message_prop : message -> Prop
    ; initial_message := { m : message | initial_message_prop m }
    ; s0 : initial_state
    ; m0 : message
    ; l0 : label
    }.

    Class VLSM {message : Type} {vtype : VLSM_type message} (lsm : LSM_sig vtype) :=
      { transition : label -> state * option message -> state * option message
      ; valid : label -> state * option message -> Prop
      }.

    Definition sign
      {message : Type}
      {vtype : VLSM_type message}
      {Sig : LSM_sig vtype}
      (vlsm : VLSM Sig)
      := Sig.

    Definition type
      {message : Type}
      {vtype : VLSM_type message}
      {Sig : LSM_sig vtype}
      (vlsm : VLSM Sig)
      := vtype.

    Section VLSM.

      Context
        {message : Type}
        {vtype : VLSM_type message}
        {Sig : LSM_sig vtype}
        (vlsm : VLSM Sig). 

      (* 2.2.2 VLSM protocol states and protocol messages *)

      (* We choose here to use the second definition hinted at the end of the 2.2.2 section, i.e., 
we define states and messages together as a property over a product type. *)

      Inductive protocol_prop : state * option message -> Prop :=
      | protocol_initial_state
          (is : initial_state)
          (s : state := proj1_sig is)
        : protocol_prop (s, None)
      | protocol_initial_message
          (im : initial_message)
          (s : state := proj1_sig s0)
          (om : option message := Some (proj1_sig im))
        : protocol_prop (s, om)
      | protocol_generated
          (l : label)
          (s : state)
          (_om : option message)
          (Hps : protocol_prop (s, _om))
          (_s : state)
          (om : option message)
          (Hpm : protocol_prop (_s, om))
          (Hv : valid l (s, om))
        : protocol_prop (transition l (s, om)).

      Definition protocol_state_prop (s : state) :=
        exists om : option message, protocol_prop (s, om).

      Definition protocol_message_prop (m : message) :=
        exists s : state, protocol_prop (s, (Some m)).

      Definition protocol_state : Type :=
        { s : state | protocol_state_prop s }.

      Definition protocol_message : Type :=
        { m : message | protocol_message_prop m }.
      
      (* Restating validity and transition using protocol_state and protocol_messages. *)

      Definition protocol_valid
                 (l : label)
                 (ps_opm : protocol_state * option protocol_message)
        : Prop :=
        valid l (proj1_sig (fst ps_opm), option_map (@proj1_sig _ _) (snd ps_opm)).

      Definition protocol_transition
                 (l : label)
                 (ps_opm : protocol_state * option protocol_message)
        : state * option message :=
        transition l (proj1_sig (fst ps_opm), option_map (@proj1_sig _ _) (snd ps_opm)).

      Definition lift_option_proto_message 
                 (om : option message)
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
          exists (lift_option_proto_message om _s Hpm).
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
        forall m' : message,
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
          exists (lift_option_proto_message om _s Hpm).
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
        assert (Hind : forall som' : state * option message, protocol_prop som' -> P (fst som')).
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

      (* Section 2.2.3 Valid VLSM transitions, VLSM traces, and VLSM identity *)

      (* Valid VLSM transitions *)

      Definition verbose_valid_protocol_transition
                 (l : label)
                 (s s' : state)
                 (om om' : option message)
        := (exists (_om : option message), protocol_prop (s, _om))
        /\ (exists (_s : state), protocol_prop (_s, om))
        /\  valid l (s, om)
        /\  transition l (s, om) = (s', om')
        .

      Lemma protocol_transition_origin
            {l : label}
            {s s' : state}
            {om om' : option message}
            (Ht : verbose_valid_protocol_transition l s s' om om')
        : protocol_state_prop s
      .
      Proof.
        destruct Ht as [[_om Hp] _]. exists _om. assumption.
      Qed.

      Lemma protocol_transition_destination
            {l : label}
            {s s' : state}
            {om om' : option message}
            (Ht : verbose_valid_protocol_transition l s s' om om')
        : protocol_state_prop s'
      .
      Proof.
        exists om'. 
        destruct Ht as [[_om Hs] [[_s Hom] [Hv Ht]]].
        rewrite <- Ht. apply protocol_generated with _om _s; assumption.
      Qed.

      Lemma protocol_transition_in
            {l : label}
            {s s' : state}
            {m : message}
            {om' : option message}
            (Ht : verbose_valid_protocol_transition l s s' (Some m) om')
        : protocol_message_prop m
      .
      Proof.
        destruct Ht as [_ [[_s Hom] _]].
        exists _s. assumption.
      Qed.

      Lemma protocol_prop_transition_in
            {l : label}
            {s s' : state}
            {om om' : option message}
            (Ht : verbose_valid_protocol_transition l s s' om om')
        : exists _s, protocol_prop (_s, om).
      Proof.
        destruct om as [m|].
        - apply protocol_transition_in in Ht.
          inversion Ht. exists x. assumption.
        - exists (proj1_sig s0). constructor.
      Qed.

      Lemma protocol_transition_out
            {l : label}
            {s s' : state}
            {om : option message}
            {m' : message}
            (Ht : verbose_valid_protocol_transition l s s' om (Some m'))
        : protocol_message_prop m'
      .
      Proof.
        exists s'. 
        destruct Ht as [[_om Hs] [[_s Hom] [Hv Ht]]].
        rewrite <- Ht. apply protocol_generated with _om _s; assumption.
      Qed.

      Lemma protocol_transition_valid
            {l : label}
            {s s' : state}
            {om om' : option message}
            (Ht : verbose_valid_protocol_transition l s s' om om')
        : valid l (s, om).
      Proof.
        destruct Ht as [_ [_ [Hv _]]].
        assumption.
      Qed.

      Lemma protocol_transition_transition
            {l : label}
            {s s' : state}
            {om om' : option message}
            (Ht : verbose_valid_protocol_transition l s s' om om')
          :  transition l (s, om) = (s', om')
        .
       Proof.
        destruct Ht as [_ [_ [_ Ht]]]. assumption.
       Qed.


      (* Valid VLSM traces *) 
      Record in_state_out :=
        {   l : label
            ;   input : option message
            ;   destination : state
            ;   output : option message
        }.

      (* A finite protocol trace originating in a given state *)
      
      Inductive finite_ptrace_from : state -> list in_state_out -> Prop :=
      | finite_ptrace_empty : forall (s : state), protocol_state_prop s -> finite_ptrace_from s []
      | finite_ptrace_extend : forall  (s : state) (tl : list in_state_out),
          finite_ptrace_from s tl ->  
          forall (s' : state) (iom oom : option message) (l : label),
            verbose_valid_protocol_transition l s' s iom oom ->
            finite_ptrace_from  s' ({| l := l; input := iom; destination := s; output := oom |} :: tl).

      Lemma finite_ptrace_first_valid_transition
            (s : state)
            (tr : list in_state_out)
            (te : in_state_out)
            (Htr : finite_ptrace_from s (te :: tr))
        : verbose_valid_protocol_transition (l te) s (destination te) (input te) (output te).
      Proof.
        inversion Htr. assumption.
      Qed.

      Lemma finite_ptrace_first_pstate
        (s : state)
        (tr : list in_state_out)
        (Htr : finite_ptrace_from s tr)
        : protocol_state_prop s
        .
      Proof.
        inversion Htr; subst; try assumption.
        - inversion H0. assumption.
      Qed.

      Lemma finite_ptrace_tail
            (s : state)
            (tr : list in_state_out)
            (te : in_state_out)
            (Htr : finite_ptrace_from s (te :: tr))
        : finite_ptrace_from (destination te) tr.
      Proof.
        inversion Htr. assumption.
      Qed.

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

      Lemma finite_ptrace_from_app_iff (s : state) (ls ls' : list in_state_out) (s' := (last (List.map destination ls) s))
        : finite_ptrace_from s ls /\ finite_ptrace_from s' ls'
          <->
          finite_ptrace_from s (ls ++ ls').
      Proof.
        intros. generalize dependent ls'. generalize dependent s. 
        induction ls; intros; split.
        - intros [_ H]. assumption.
        - simpl; intros; split; try assumption. constructor. inversion H; try assumption.
          apply (protocol_transition_origin H1).
        - simpl. intros [Htr Htr']. 
          destruct a. apply finite_ptrace_extend.
          + apply IHls. inversion Htr. split. apply H2.
            unfold s' in Htr'. 
            assert (last_identity: last (List.map destination ls) destination0 = last
            (List.map destination
               ({| l := l1; input := input0; destination := destination0; output := output0 |} :: ls)) s). {
            rewrite map_cons. rewrite unroll_last. simpl. reflexivity. }
            rewrite last_identity. assumption. 
          + inversion Htr. apply H6.
         - intros. inversion H. subst. specialize (IHls s1). simpl in IHls. specialize (IHls ls'). apply IHls in H3.
           destruct H3. split. 
           + constructor. apply H0. apply H4.
           + assert (last_identity : s' = last (List.map destination ls) s1). {
             unfold s'. rewrite map_cons. rewrite unroll_last. reflexivity. 
           }
           rewrite last_identity. assumption.
      Qed.

      Lemma finite_ptrace_from_prefix
        (s : state)
        (ls : list in_state_out)       
        (Htr : finite_ptrace_from s ls)
        (n : nat)
        : finite_ptrace_from s (list_prefix ls n).
      Proof.
        specialize (list_prefix_suffix ls n); intro Hdecompose.
        rewrite <- Hdecompose in Htr.
        apply finite_ptrace_from_app_iff in Htr.
        destruct Htr as [Hpr _].
        assumption.
      Qed.

      Lemma finite_ptrace_from_suffix
        (s : state)
        (ls : list in_state_out)       
        (Htr : finite_ptrace_from s ls)
        (n : nat)
        (nth : state)
        (Hnth : nth_error (s :: List.map destination ls) n = Some nth)
        : finite_ptrace_from nth (list_suffix ls n)
        .
      Proof.
        specialize (list_prefix_suffix ls n); intro Hdecompose.
        rewrite <- Hdecompose in Htr.
        apply finite_ptrace_from_app_iff in Htr.
        destruct Htr as [_ Htr].
        assert (Heq : last (List.map destination (list_prefix ls n)) s = nth).
        { rewrite list_prefix_map.
          destruct n.
          - simpl in Hnth. inversion Hnth; subst; clear Hnth.
            remember (List.map destination ls) as l.
            destruct l; reflexivity.
          - symmetry. apply list_prefix_nth_last.
            simpl in Hnth. assumption.
        }
        rewrite Heq in Htr.
        assumption.
      Qed.

      Lemma finite_ptrace_from_segment
        (s : state)
        (ls : list in_state_out)       
        (Htr : finite_ptrace_from s ls)
        (n1 n2 : nat)
        (Hle : n1 <= n2)
        (n1th : state)
        (Hnth : nth_error (s :: List.map destination ls) n1 = Some n1th)
        : finite_ptrace_from n1th (list_segment ls n1 n2).
      Proof.
        apply finite_ptrace_from_suffix with s.
        - apply finite_ptrace_from_prefix. assumption.
        - destruct n1; try assumption.
          simpl. simpl in Hnth.
          rewrite list_prefix_map.
          rewrite list_prefix_nth; assumption.
      Qed.

      (* An infinite protocol trace originating in a given state *)
      
      CoInductive infinite_ptrace_from :
        state -> Stream in_state_out -> Prop :=
      | infinite_ptrace_extend : forall  (s : state) (tl : Stream in_state_out),
          infinite_ptrace_from s tl ->  
          forall (s' : state) (iom oom : option message) (l : label),
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

      Lemma infinite_ptrace_from_app_iff
        (s : state)
        (ls : list in_state_out)
        (ls' : Stream in_state_out)
        (s' := (last (List.map destination ls) s))
        : finite_ptrace_from s ls /\ infinite_ptrace_from s' ls'
          <->
          infinite_ptrace_from s (stream_app ls ls').
      Proof.
        intros. generalize dependent ls'. generalize dependent s. 
        induction ls; intros; split.
        - intros [_ H]. assumption.
        - simpl; intros; split; try assumption. constructor. inversion H; try assumption.
          apply (protocol_transition_origin H1).
        - simpl. intros [Htr Htr']. 
          destruct a. apply infinite_ptrace_extend.
          + apply IHls. inversion Htr. split. apply H2.
            unfold s' in Htr'. 
            assert (last_identity: last (List.map destination ls) destination0 = last
            (List.map destination
               ({| l := l1; input := input0; destination := destination0; output := output0 |} :: ls)) s). {
            rewrite map_cons. rewrite unroll_last. simpl. reflexivity. }
            rewrite last_identity. assumption. 
          + inversion Htr. apply H6.
         - intros. inversion H. subst. specialize (IHls s1). simpl in IHls. specialize (IHls ls'). apply IHls in H3.
           destruct H3. split. 
           + constructor. apply H0. apply H4.
           + assert (last_identity : s' = last (List.map destination ls) s1). {
             unfold s'. rewrite map_cons. rewrite unroll_last. reflexivity. 
           }
           rewrite last_identity. assumption.
      Qed.

      Lemma infinite_ptrace_from_prefix
        (s : state)
        (ls : Stream in_state_out)       
        (Htr : infinite_ptrace_from s ls)
        (n : nat)
        : finite_ptrace_from s (stream_prefix ls n).
      Proof.
        specialize (stream_prefix_suffix ls n); intro Hdecompose.
        rewrite <- Hdecompose in Htr.
        apply infinite_ptrace_from_app_iff in Htr.
        destruct Htr as [Hpr _].
        assumption.
      Qed.

      Lemma infinite_ptrace_from_segment
        (s : state)
        (ls : Stream in_state_out)       
        (Htr : infinite_ptrace_from s ls)
        (n1 n2 : nat)
        (Hle : n1 <= n2)
        (n1th := Str_nth n1 (Cons s (Streams.map destination ls)))
        : finite_ptrace_from n1th (stream_segment ls n1 n2).
      Proof.
        apply finite_ptrace_from_suffix with s.
        - apply infinite_ptrace_from_prefix. assumption.
        - destruct n1; try reflexivity.
          unfold n1th. clear n1th.
          simpl.
          rewrite stream_prefix_map.
          rewrite stream_prefix_nth; try assumption.
          reflexivity.
      Qed.

      Definition infinite_ptrace (s : state) (st : Stream in_state_out)
        := infinite_ptrace_from s st /\ initial_state_prop s.

      Inductive Trace : Type :=
      | Finite : state -> list in_state_out -> Trace
      | Infinite : state -> Stream in_state_out -> Trace.

      Definition trace_initial_state (tr : Trace) : state :=
        match tr with 
        | Finite s _ => s
        | Infinite s _ => s
        end. 

      Definition ptrace_prop (tr : Trace) : Prop :=
        match tr with 
        | Finite s ls => finite_ptrace s ls
        | Infinite s sm => infinite_ptrace s sm
        end.

      Definition ptrace_from_prop (tr : Trace) : Prop :=
        match tr with 
        | Finite s ls => finite_ptrace_from s ls
        | Infinite s sm => infinite_ptrace_from s sm
        end.

      Definition protocol_trace : Type :=
        { tr : Trace | ptrace_prop tr}.
      
      (* Protocol runs *) 
      Record proto_run : Type := mk_proto_run
                                   { start : initial_state
                                     ; transitions : list in_state_out
                                     ; final : state * option message
                                   }.

      Inductive vlsm_run_prop : proto_run -> Prop :=
      | empty_run_initial_state
          (is : initial_state)
          (s : state := proj1_sig is)
        : vlsm_run_prop {| start := is; transitions := []; final := (s, None) |}
      | empty_run_initial_message
          (im : initial_message)
          (s : state := proj1_sig s0)
          (om : option message := Some (proj1_sig im))
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
        : vlsm_run_prop {| start := is; transitions := ts ++ [
            {|   l := l
            ;   input := om
            ;   destination := fst som'
            ;   output := snd som'
            |}]; final := som' |}.

      Definition vlsm_run : Type :=
        { r : proto_run | vlsm_run_prop r }.


      Lemma vlsm_run_last_state
        (vr : vlsm_run)
        (r := proj1_sig vr)
        : last (List.map destination (transitions r)) (proj1_sig (start r)) = fst (final r).
      Proof.
        unfold r; clear r; destruct vr as [r Hr]; simpl.
        induction Hr; simpl; try reflexivity.
        rewrite map_app; simpl.
        apply last_is_last.
      Qed.

      Lemma vlsm_run_last_final
        (vr : vlsm_run)
        (r := proj1_sig vr)
        (tr := transitions r)
        (Hne_tr : tr <> [])
        (lst := last_error tr)
        : option_map destination lst = Some (fst (final r))
        /\ option_map output lst = Some (snd (final r)).
      Proof.
        unfold r in *; clear r; destruct vr as [r Hr]; inversion Hr; subst; simpl in *; clear Hr
        ; try contradiction.
        unfold tr in *. unfold lst in *. rewrite last_error_is_last . simpl.
        split; reflexivity.
      Qed.

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
            (som' : state * option message)
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

      Lemma run_is_trace
            (vr : vlsm_run)
            (r := proj1_sig vr)
        : ptrace_prop (Finite (proj1_sig (start r)) (transitions r)).
      Proof.
        unfold r; clear r; destruct vr as [r Hr]; simpl.
        induction Hr; simpl.
        - specialize (protocol_initial_state is); intro Hpis; simpl in Hpis.
          destruct is as [is His]; simpl. constructor; try assumption. constructor.
          exists None. assumption.
        - specialize (protocol_initial_state s0); intro Hps0; simpl in Hps0.
          destruct s0 as [s0 Hs0]; simpl. constructor; try assumption. constructor.
          exists None. assumption.
        - destruct IHHr1 as [Htr Hinit].
          split; try assumption.
          apply extend_right_finite_trace_from; try assumption.
          specialize vlsm_run_last_state; intros Hls. specialize (Hls (exist _ state_run Hr1)).
          simpl in Hls. unfold ts. unfold is. rewrite Hls.
          repeat split; try assumption.
          + exists (snd (final state_run)). rewrite <- surjective_pairing.
            specialize (run_is_protocol (exist _ state_run Hr1)); intro Hp; assumption.
          + exists (fst (final msg_run)). rewrite <- surjective_pairing.
            specialize (run_is_protocol (exist _ msg_run Hr2)); simpl; intro Hp; assumption.
          + rewrite <- surjective_pairing. reflexivity.
      Qed.

      Lemma trace_is_run
        (is : initial_state)
        (tr : list in_state_out)
        (Htr : finite_ptrace_from (proj1_sig is) tr)
        : exists r : proto_run,
          vlsm_run_prop r /\
          start r = is /\ transitions r = tr
        .
      Proof.
        generalize dependent tr.
        apply (rev_ind (fun tr => (finite_ptrace_from (proj1_sig is) tr ->
                  exists r : proto_run, vlsm_run_prop r /\ start r = is /\ transitions r = tr))).
        - intros H.
          exists {| start := is; transitions := []; final := (proj1_sig is, None) |}; simpl; repeat split; try reflexivity.
          apply empty_run_initial_state.
        - intros lst prefix IHprefix H. 
          apply finite_ptrace_from_app_iff in H.
          destruct H as [Hprefix Hlst].
          specialize (IHprefix Hprefix).
          destruct IHprefix as [r0 [Hr0 [Hstart Htr_r0]]].
          exists {| start := is; transitions := prefix ++ [lst]; final := (destination lst, output lst) |}.
          simpl. repeat split; try reflexivity.
          specialize (extend_run r0 Hr0); simpl; intro Hextend.
          apply finite_ptrace_first_valid_transition in Hlst.
          destruct lst as [lst_l lst_in lst_dest lst_out].
          simpl in *.
          specialize (vlsm_run_last_state (exist _ r0 Hr0)); intro Hlast_state.
          simpl in Hlast_state. rewrite Htr_r0 in Hlast_state.
          rewrite Hstart in Hlast_state. rewrite Hlast_state in Hlst.
          specialize (protocol_prop_transition_in Hlst); intro Hmsg.
          destruct Hmsg as [_s Hmsg].
          apply protocol_is_run in Hmsg.
          destruct Hmsg as [[r_msg Hr_msg] Hmsg].
          specialize (Hextend r_msg Hr_msg lst_l).
          specialize (protocol_transition_valid Hlst); intro Hvalid.
          simpl in Hmsg. rewrite <- Hmsg in Hextend. simpl  in Hextend.
          specialize (Hextend Hvalid). rewrite Hstart in Hextend.
          specialize (protocol_transition_transition Hlst); intro Htransition.
          rewrite Htransition in Hextend. simpl in Hextend.
          rewrite Htr_r0 in Hextend.
          apply Hextend.
          Qed.

      (* protocol states/messages correspond to protocol traces *)

      Lemma protocol_is_trace
            (som' : state * option message)
            (Hp : protocol_prop som')
            (s' := fst som')
            (om' := snd som')
           
        : initial_state_prop s' \/ exists (is : state) (tr : list in_state_out),
              finite_ptrace is tr
              /\ option_map destination (last_error tr) = Some s'
              /\ option_map output (last_error tr) = Some om'.
      Proof.
        specialize (protocol_is_run som' Hp); intros [vr Heq].
        specialize (run_is_trace vr); simpl; intros Htr.
        destruct vr as [r Hvr]; simpl in *.
        destruct (transitions r) eqn:Htrace.
        - inversion Hvr; subst; simpl in Htrace. 
          + destruct is as [s0 His]. left. assumption.
          + destruct s0 as [s0 His]. left. assumption.
          + destruct ts; inversion Htrace.
        - right. exists (proj1_sig (start r)). exists (transitions r). rewrite Htrace.
          split; try assumption.
          specialize (vlsm_run_last_final (exist _ r Hvr)); simpl; rewrite Htrace; simpl.
          rewrite <- Heq.
          intros Hlf; apply Hlf. intros HC; inversion HC.
      Qed. 

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
      
      Definition protocol_state_trace_prop (tr : Trace_states)
        := exists (ptr : protocol_trace), tr = protocol_state_trace ptr.
      

      Definition in_futures
        (pfirst psecond : protocol_state)
        (first := proj1_sig pfirst)
        (second := proj1_sig psecond)
        : Prop :=
        exists (tr : list in_state_out),
          finite_ptrace_from first tr /\
          last (List.map destination tr) first = second.

      Lemma in_futures_witness
        (pfirst psecond : protocol_state)
        (first := proj1_sig pfirst)
        (second := proj1_sig psecond)
        (Hfutures : in_futures pfirst psecond)
        : exists (tr : protocol_trace) (n1 n2 : nat),
          n1 <= n2
          /\ trace_nth (proj1_sig tr) n1 = Some first
          /\ trace_nth (proj1_sig tr) n2 = Some second.
      Proof.
        unfold first in *; clear first. unfold second in *; clear second.
        destruct pfirst as [first [_mfirst Hfirst]].
        destruct psecond as [second [_msecond Hsecond]].
        simpl.
        unfold in_futures in Hfutures. simpl in Hfutures.
        destruct Hfutures as [suffix_tr [Hsuffix_tr Hsnd]].
        apply protocol_is_run in Hfirst.
        destruct Hfirst as [prefix_run Hprefix_run].
        specialize (vlsm_run_last_state prefix_run); intro Hprefix_last.
        specialize (run_is_trace prefix_run); intro Hprefix_tr.
        destruct prefix_run as [prefix_run Hpref_run].
        destruct prefix_run as [prefix_start prefix_tr prefix_final].
        subst; simpl in *.
        specialize (finite_ptrace_from_app_iff (proj1_sig prefix_start) prefix_tr suffix_tr); intro Happ.
        simpl in Happ.
        rewrite Hprefix_last in Happ. rewrite <- Hprefix_run in Happ.
        simpl in Happ.
        destruct Happ as [Happ _].
        destruct Hprefix_tr as [Hprefix_tr Hinit].
        specialize (Happ (conj Hprefix_tr Hsuffix_tr)).
        assert (Hfinite_tr: finite_ptrace (proj1_sig prefix_start) (prefix_tr ++ suffix_tr))
          by (constructor; assumption).
        assert (Htr : ptrace_prop (Finite (proj1_sig prefix_start) (prefix_tr ++ suffix_tr)))
          by assumption.
        exists (exist _ (Finite (proj1_sig prefix_start) (prefix_tr ++ suffix_tr)) Htr).
        simpl.
        exists (length prefix_tr).
        exists (length prefix_tr + length suffix_tr).
        remember (length prefix_tr) as m.
        split; try apply le_plus_l.
        destruct m; simpl.
        + symmetry in Heqm. apply length_zero_iff_nil in Heqm.
          subst; simpl in *.
          split; try (f_equal; assumption).
          remember (length suffix_tr) as delta.
          destruct delta; simpl.
          * symmetry in Heqdelta. apply length_zero_iff_nil in Heqdelta.
            subst; simpl in *. f_equal.
          * apply nth_error_last.
            rewrite map_length. assumption.
        + rewrite map_app. 
          assert (Hnth_pref : forall suf, nth_error (List.map destination prefix_tr ++ suf) m = Some first).
          { intro. rewrite nth_error_app1.
            - specialize (nth_error_last (List.map destination prefix_tr) m); intro Hnth.
              assert (Hlen : S m = length (List.map destination prefix_tr))
                by (rewrite map_length; assumption).
              specialize (Hnth Hlen (proj1_sig prefix_start)).
              rewrite Hnth. f_equal. subst.
              rewrite Hprefix_last. reflexivity.
            - rewrite map_length. rewrite <- Heqm. constructor.
          }
          split; try apply Hnth_pref.
          remember (length suffix_tr) as delta.
          destruct delta; simpl.
          * symmetry in Heqdelta. apply length_zero_iff_nil in Heqdelta.
            subst; simpl in *. rewrite plus_0_r.
            apply Hnth_pref.
          * { rewrite nth_error_app2.
              - rewrite map_length.
                rewrite <- Heqm. 
                assert (Hdelta : m + S delta - S m = delta)
                  by (rewrite <- plus_Snm_nSm; apply minus_plus).
                rewrite Hdelta.
                specialize (nth_error_last (List.map destination suffix_tr) delta); intro Hnth.
                rewrite map_length in Hnth.
                specialize (Hnth Heqdelta first).
                assumption.
              - rewrite map_length. rewrite <- Heqm.
                rewrite <- plus_Snm_nSm. simpl.
                apply le_n_S. apply le_plus_l.
            }
      Qed.

      Definition trace_segment
        (tr : Trace)
        (n1 n2 : nat)
        : list in_state_out
        := match tr with
        | Finite s l => list_segment l n1 n2
        | Infinite s l => stream_segment l n1 n2
        end.

      Lemma ptrace_segment
        (tr : Trace)
        (Htr : ptrace_prop tr)
        (n1 n2 : nat)
        (Hle : n1 <= n2)
        (first : state)
        (Hfirst : trace_nth tr n1 = Some first)
        : finite_ptrace_from first (trace_segment tr n1 n2).
      Proof.
        destruct tr as [s tr | s tr]; simpl in *; destruct Htr as [Htr Hinit].
        - apply finite_ptrace_from_segment with s; try assumption.
        - inversion Hfirst; subst; clear Hfirst.
          apply (infinite_ptrace_from_segment s tr Htr n1 n2 Hle).
      Qed.

      Lemma in_futures_witness_reverse
        (pfirst psecond : protocol_state)
        (first := proj1_sig pfirst)
        (second := proj1_sig psecond)
        (H : exists (tr : protocol_trace) (n1 n2 : nat),
          n1 <= n2
          /\ trace_nth (proj1_sig tr) n1 = Some first
          /\ trace_nth (proj1_sig tr) n2 = Some second
        )
        : in_futures pfirst psecond.
      Proof.
        destruct H as [[tr Htr] [n1 [n2 [Hle [Hs1 Hs2]]]]].
        unfold in_futures. unfold first in *. clear first.
        unfold second in *. clear second.
        destruct pfirst as [first Hfirst].
        destruct psecond as [second Hsecond].
        simpl in *.
        inversion Hle; subst; clear Hle.
        - rewrite Hs1 in Hs2. inversion Hs2; subst; clear Hs2.
          exists []. split.
          + constructor. assumption.
          + reflexivity.
        -  exists (trace_segment tr n1 (S m)).
          split.
          + apply ptrace_segment; try assumption. constructor. assumption.
          + { destruct tr as [s tr | s tr]; simpl.
            - unfold list_segment.
              rewrite list_suffix_map. rewrite list_prefix_map.
              simpl in Hs2.
              rewrite list_suffix_last.
              + symmetry. apply list_prefix_nth_last. assumption.
              + apply nth_error_length in Hs2.
                specialize (list_prefix_length (List.map destination tr) (S m) Hs2); intro Hpref_len.
                rewrite Hpref_len. 
                apply le_n_S. assumption.
            - unfold stream_segment.
              rewrite list_suffix_map. rewrite stream_prefix_map.
              simpl in Hs2.
              rewrite list_suffix_last.
              + symmetry. rewrite stream_prefix_nth_last.
                unfold Str_nth in Hs2. simpl in Hs2.
                inversion Hs2; subst.
                reflexivity.
              + specialize (stream_prefix_length (Streams.map destination tr) (S m)); intro Hpref_len.
                rewrite Hpref_len. 
                apply le_n_S. assumption.
            }
      Qed.

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
      | Finite_messages : list (option message) -> Trace_messages
      | Infinite_messages : Stream (option message) -> Trace_messages. 

      Definition protocol_output_messages_trace (tr : protocol_trace) : Trace_messages :=
        match proj1_sig tr with
        | Finite _ ls => Finite_messages (List.map output ls)
        | Infinite _ st => Infinite_messages (map output st) end.

      Definition protocol_input_messages_trace (tr : protocol_trace) : Trace_messages :=
        match proj1_sig tr with
        | Finite _ ls => Finite_messages (List.map input ls)
        | Infinite _ st => Infinite_messages (map input st) end.

      (* Defining equivocation on these trace definitions *)
      (* Section 7 :
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

      Definition complete_trace_prop (tr : Trace) : Prop
         := ptrace_prop tr
            /\
            match tr with 
            | Finite _ _ => terminating_trace_prop tr
            | Infinite _ _ => True
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
                 (msg : message)
                 (tr : protocol_trace)
        : Prop
        :=
          exists (last : in_state_out),
          exists (prefix : list in_state_out),
            trace_prefix (proj1_sig tr) last prefix
            /\  input last = Some msg
            /\  ~ In (Some msg) (List.map output prefix)
      .

      Definition equivocation (msg : message) (s : state) : Prop :=
        exists (tr : protocol_trace), trace_last (proj1_sig tr) = Some s /\ equivocation_in_trace msg tr.

      (* Now we can have decidable equivocations! *) 
      (* 6.2.1 Identifying equivocations *)
      Definition has_been_sent (msg : message) (s : state) : Prop :=
        forall (tr : protocol_trace) 
          (last : in_state_out)
          (prefix : list in_state_out)
          (Hpr : trace_prefix (proj1_sig tr) last prefix)
          (Hlast : destination last = s),
          List.Exists (fun (elem : in_state_out) => output elem = Some msg) prefix. 

      (* Since equality of proto_messages is decidable, this function must exist : *) 
      Definition proto_message_eqb {Eqd : EqDec message}
                 (om1 : option message)
                 (om2 : option message)
        : bool
        :=
          match om1, om2 with
          | None, None => true
          | Some m1, Some m2 => if eq_dec m1 m2 then true else false
          | _, _ => false
          end.

      Fixpoint has_been_sentb
               {Eqd : EqDec message}
               (msg : message) (ls : list in_state_out) : bool
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
        label -> state * option message -> Prop. 

      Definition equivocation_free : composition_constraint :=
        fun l som => match (snd som) with
                  | None => True
                  | Some msg => equivocation msg (fst som) -> False
                  end.

      (* Decidable VLSMs *) 

      Class VLSM_vdecidable :=
        { valid_decidable : forall l som, {valid l som} + {~valid l som} 
        }.

    End VLSM.

    Section VLSM_equality. (* Section 2.2.3 *)

      Context
        {message : Type}
        {vtype : VLSM_type message}.
      
      Definition VLSM_eq
        {SigX SigY: LSM_sig vtype}
        (X : VLSM SigX) (Y : VLSM SigY)
        :=
        forall t : Trace_states,
          protocol_state_trace_prop X t <-> protocol_state_trace_prop Y t
        .

    End VLSM_equality.
