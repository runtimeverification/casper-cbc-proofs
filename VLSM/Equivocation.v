Require Import List Streams ProofIrrelevance Coq.Arith.Plus Coq.Arith.Minus Coq.Logic.FinFun Coq.Reals.Reals.
Import ListNotations.

From CasperCBC
Require Import Lib.Preamble VLSM.Common VLSM.Composition.

Section Simple.

    Context
      {message : Type}
      {vtype : VLSM_type message}
      {Sig : LSM_sig vtype}
      (vlsm : VLSM Sig).

    Definition trace_has_message
      (message_selector : transition_item -> option message)
      (msg : message)
      (tr : protocol_trace vlsm)
      : Prop
      := exists (last : transition_item),
         exists (prefix : list transition_item),
          trace_prefix (proj1_sig tr) last prefix
          /\ message_selector last = Some msg.

    Definition equivocation_in_trace
               (msg : message)
               (tr : protocol_trace vlsm)
      : Prop
      :=
        exists (last : transition_item),
        exists (prefix : list transition_item),
          trace_prefix (proj1_sig tr) last prefix
          /\  input last = Some msg
          /\  ~ In (Some msg) (List.map output prefix)
    .

    (* Definition equivocation (msg : message) (s : state) : Prop :=
      exists (tr : protocol_trace vlsm), trace_last (proj1_sig tr) = Some s /\ equivocation_in_trace msg tr. *)
      
    Definition message_oracle (x : VLSM Sig)
      := (state) -> (message) -> bool.
    
    (* Generic definitions for messages being present in all traces or none of the traces. The
       type of the message (sent or received) is given by the [message_selector] function. *)
    
    Definition all_traces_have_message_prop
      (message_selector : transition_item -> option message)
      (oracle : message_oracle vlsm) 
      (s : state)
      (m : message) 
      : Prop 
      := 
      oracle s m = true <-> 
        forall 
        (tr : protocol_trace vlsm)
        (last : transition_item)
        (prefix : list transition_item)
        (Hpr : trace_prefix (proj1_sig tr) last prefix)
        (Hlast : destination last = s),
        List.Exists (fun (elem : transition_item) => message_selector elem = Some m) prefix.
        
    Definition no_traces_have_message_prop
      (message_selector : transition_item -> option message)
      (oracle : message_oracle vlsm) 
      (s : state)
      (m : message) 

      : Prop 
      := 
      oracle s m = true <-> 
        forall 
        (tr : protocol_trace vlsm)
        (last : transition_item)
        (prefix : list transition_item)
        (Hpr : trace_prefix (proj1_sig tr) last prefix)
        (Hlast : destination last = s),
        List.Exists (fun (elem : transition_item) => message_selector elem = Some m) prefix -> False.
      
    
    Definition has_been_sent_prop : message_oracle vlsm -> state -> message -> Prop
      := (all_traces_have_message_prop output).
      
    Definition has_not_been_sent_prop : message_oracle vlsm -> state -> message -> Prop
      := (no_traces_have_message_prop output).    
      
    Definition has_been_received_prop : message_oracle vlsm -> state -> message -> Prop
      := (all_traces_have_message_prop input).
      
    Definition has_not_been_received_prop : message_oracle vlsm -> state -> message -> Prop
      := (no_traces_have_message_prop input).

    Class has_been_sent_capability := { 
      has_been_sent: message_oracle vlsm;
      
      proper_sent: 
        forall (s : state) 
               (m : message), 
               (has_been_sent_prop has_been_sent s m);
      
      has_not_been_sent: message_oracle vlsm;
      proper_not_sent: 
        forall (s : state) 
               (m : message), 
               has_not_been_sent_prop has_not_been_sent s m;
      
      sent_excluded_middle : 
        forall (s : state) 
               (m : message),
               has_been_sent s m = true <-> has_not_been_sent s m = false;
    }.
    
    Class has_been_received_capability := {
      has_been_received: message_oracle vlsm;
      
      proper_received: 
        forall (s : state) 
               (m : message), 
               (has_been_received_prop has_been_received s m);
      
      has_not_been_received: message_oracle vlsm;
      proper_not_received: 
        forall (s : state) 
               (m : message), 
               has_not_been_received_prop has_not_been_received s m;
      
      received_excluded_middle : 
        forall (s : state) 
               (m : message),
               has_been_received s m = true <-> has_not_been_received s m = false;
    }.
    
    
    Class StrongVLSM := {
      x : VLSM Sig;
      send_capable : has_been_sent_capability;
      receive_capable : has_been_received_capability;
    }.
    
    (* Old stuff below, sorting them is work in progress. *)
    
    (*
    Definition has_been_sent (msg : message) (s : state) : Prop :=
      forall (tr : protocol_trace vlsm)
        (last : transition_item)
        (prefix : list transition_item)
        (Hpr : trace_prefix (proj1_sig tr) last prefix)
        (Hlast : destination last = s),
        List.Exists (fun (elem : transition_item) => output elem = Some msg) prefix.

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
             (msg : message) (ls : list transition_item) : bool
      :=
        existsb (fun x => proto_message_eqb (output x) (Some msg)) ls.
        
    Definition equivocation_free : composition_constraint :=
      fun l som => match (snd som) with
                | None => True
                | Some msg => equivocation msg (fst som) -> False
                end.
     *)
End Simple.

Section Composite.

    Context {message : Type}
            {index : Type}
            (index_listing : list index)
            {finite_index : Listing index_listing}
            {validator : Type}
            {IndEqDec : EqDec index}
            {IT : index -> VLSM_type message}
            (i0 : index)
            {IS : forall i : index, LSM_sig (IT i)}
            (IM : forall n : index, VLSM (IS n))
            (constraint : indexed_label IT -> indexed_state IT  * option message -> Prop)
            (has_been_sent_capabilities : forall i : index, (has_been_sent_capability (IM i)))
            (has_been_received_capabilities : forall i : index, (has_been_received_capability (IM i)))
            (sender : message -> option validator)
            (A : validator -> index)
            (Weight : validator -> R)
            (X := indexed_vlsm_constrained i0 IM constraint).
           
         
     Check @has_not_been_sent message (IT i0) (IS i0) (IM i0) (has_been_sent_capabilities i0).  
     
     Definition equivocation(m : message) (s : indexed_state IT) : Prop  := forall (i : index), 
      @has_not_been_sent message (IT i) (IS i) (IM i) (has_been_sent_capabilities i) 
      (s i) m = true.
      
      Definition no_equivocations
        (l : indexed_label IT)
        (som : indexed_state IT * option message)
        : Prop
        := 
        let (s, om) := som in
        match om with 
        | None => True
        | Some m => ~equivocation m s
        end.
        
      Check indexed_vlsm_constrained_projection.
      
      Definition sender_safety_prop : Prop := 
        forall 
        (i : index)
        (m : message)
        (v : validator)
        (Hid : A v = i)
        (Hsender : sender m = Some v),
        can_emit (indexed_vlsm_constrained_projection i0 IM constraint i) m /\
        forall (j : index)
               (Hdif : i <> j),
               ~can_emit (indexed_vlsm_constrained_projection i0 IM constraint j) m.
               
       Definition sender_weak_nontriviality_prop : Prop :=
        forall (v : validator),
        exists (m : message),
        can_emit (indexed_vlsm_constrained_projection i0 IM constraint (A v)) m /\
        sender m = Some v.
        
       Definition sender_strong_nontriviality_prop : Prop :=
        forall (v : validator),
        forall (m : message),
        can_emit (indexed_vlsm_constrained_projection i0 IM constraint (A v)) m ->
        sender m = Some v.
        
       Definition equivocating_wrt
        (v : validator)
        (j : index)
        (sv sj : state)
        (i := A v)
        : Prop
        := 
        exists (m : message),
        sender(m) = Some v /\
        @has_not_been_sent message (IT i) (IS i) (IM i) (has_been_sent_capabilities i) sv m = true /\
        @has_been_received message (IT j) (IS j) (IM j) (has_been_received_capabilities j) sj m = true.
        
        Definition index_mappping : (index -> nat).
        intros.
        destruct finite_index as [Hnodup Hfull].
        unfold Full in Hfull.
        specialize Hfull with (a := X0).
        assert (Htarget : exists (n : nat), exists (def : index), nth n index_listing def = X0). {
          specialize In_nth.
          intros.
          apply H with (d := X0) in Hfull.
          destruct Hfull.
          exists x0.
          destruct H0.
          exists X0.
          assumption.
        }
        destruct Htarget.
        
        Fixpoint validator_listing : list index :=
          match index_listing with
          | [] => []
          | h :: tl => 
        
        Fixpoint equivocation_fault
          (s : protocol_state X)
          : R
          := match index_listing with
             | [] => 0%R
             | h :: tl => match 
          
         
        
        
End Composite.


