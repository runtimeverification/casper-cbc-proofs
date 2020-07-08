Require Import List Streams ProofIrrelevance Coq.Arith.Plus Coq.Arith.Minus.
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

    Definition equivocation (msg : message) (s : state) : Prop :=
      exists (tr : protocol_trace vlsm), trace_last (proj1_sig tr) = Some s /\ equivocation_in_trace msg tr.
      
    Definition message_oracle (x : VLSM Sig)
      := (protocol_state x) -> (protocol_message x) -> bool.
    
    (* Generic definitions for messages being present in all traces or none of the traces. The
       type of the message (sent or received) is given by the [message_selector] function. *)
    
    Definition all_traces_have_message_prop
      (message_selector : transition_item -> option message)
      (oracle : message_oracle vlsm) 
      (s : protocol_state vlsm)
      (m : protocol_message vlsm) 
      : Prop 
      := 
      oracle s m = true <-> 
        forall 
        (tr : protocol_trace vlsm)
        (last : transition_item)
        (prefix : list transition_item)
        (Hpr : trace_prefix (proj1_sig tr) last prefix)
        (Hlast : destination last = proj1_sig s),
        List.Exists (fun (elem : transition_item) => message_selector elem = Some (proj1_sig m)) prefix.
        
    Definition no_traces_have_message_prop
      (message_selector : transition_item -> option message)
      (oracle : message_oracle vlsm) 
      (s : protocol_state vlsm)
      (m : protocol_message vlsm) 

      : Prop 
      := 
      oracle s m = true <-> 
        forall 
        (tr : protocol_trace vlsm)
        (last : transition_item)
        (prefix : list transition_item)
        (Hpr : trace_prefix (proj1_sig tr) last prefix)
        (Hlast : destination last = proj1_sig s),
        List.Exists (fun (elem : transition_item) => message_selector elem = Some (proj1_sig m)) prefix -> False.
      
    
    Definition has_been_sent_prop : message_oracle vlsm -> protocol_state vlsm -> protocol_message vlsm -> Prop
      := (all_traces_have_message_prop output).
      
    Definition has_not_been_sent_prop : message_oracle vlsm -> protocol_state vlsm -> protocol_message vlsm -> Prop
      := (no_traces_have_message_prop output).    
      
    Definition has_been_received_prop : message_oracle vlsm -> protocol_state vlsm -> protocol_message vlsm -> Prop
      := (all_traces_have_message_prop input).
      
    Definition has_not_been_received_prop : message_oracle vlsm -> protocol_state vlsm -> protocol_message vlsm -> Prop
      := (no_traces_have_message_prop input).

    Class has_been_sent_capability := { 
      has_been_sent: message_oracle vlsm;
      
      proper_sent: 
        forall (s : protocol_state vlsm) 
               (m : protocol_message vlsm), 
               (has_been_sent_prop has_been_sent s m);
      
      has_not_been_sent: message_oracle vlsm;
      proper_not_sent: 
        forall (s : protocol_state vlsm) 
               (m : protocol_message vlsm), 
               has_not_been_sent_prop has_not_been_sent s m;
      
      sent_excluded_middle : 
        forall (s : protocol_state vlsm) 
               (m : protocol_message vlsm),
               has_been_sent s m = true <-> has_not_been_sent s m = false;
    }.
    
    Class has_been_received_capability := {
      has_been_received: message_oracle vlsm;
      
      proper_received: 
        forall (s : protocol_state vlsm) 
               (m : protocol_message vlsm), 
               (has_been_received_prop has_been_received s m);
      
      has_not_been_received: message_oracle vlsm;
      proper_not_received: 
        forall (s : protocol_state vlsm) 
               (m : protocol_message vlsm), 
               has_not_been_received_prop has_not_been_received s m;
      
      received_excluded_middle : 
        forall (s : protocol_state vlsm) 
               (m : protocol_message vlsm),
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
            {IndEqDec : EqDec index}
            {IT : index -> VLSM_type message}
            (i0 : index)
            {IS : forall i : index, LSM_sig (IT i)}
            (IM : forall n : index, VLSM (IS n))
            (constraint : indexed_label IT -> indexed_state IT  * option message -> Prop)
            (X := indexed_vlsm_constrained i0 IM constraint).
            
     Definition equivocation (state : protocol_state X) (message : protocol_message X) : Prop 
      := exists (i : index),
         
     
     .
End Composite.
