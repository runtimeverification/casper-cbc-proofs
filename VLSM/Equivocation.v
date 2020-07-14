Require Import List Streams ProofIrrelevance Coq.Arith.Plus Coq.Arith.Minus Coq.Logic.FinFun Coq.Reals.Reals.
Import ListNotations.

From CasperCBC
Require Import Lib.Preamble VLSM.Common VLSM.Composition.

(** This chapter is dedicated to building the language for discussing equivocation.
    We begin by giving the basic definitions for individual VLSMs and we then
    move towards a composite context. **)

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
    
End Simple.

Section Composite.

    Context {message : Type}
            {index : Type}
            (index_listing : list index)
            {finite_index : Listing index_listing}
            {validator : Type}
            (validator_listing : list validator)
            {finite_validator : Listing validator_listing}
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
        
        Definition is_equivocating
          (s : indexed_state IT)
          (v : validator)
          : Prop
          :=
          exists (j : index),
          j <> (A v) /\
          equivocating_wrt v j (s (A v)) (s j).
          
        (* This needs some clarification to type check (roughly, has_been_sent should belong to the projection).
          
        Definition is_equivocating_alt
          (v : validator)
          (s : indexed_state IT)
          (j := A v)
          : Prop
          := 
          forall (tr : protocol_trace X)
          (last : transition_item)
          (prefix : list transition_item)
          (Hpr : trace_prefix (proj1_sig tr) last prefix)
          (Hlast : destination last = s),
          exists (m : message),
          List.Exists 
          (fun (elem : transition_item) => 
          input elem = Some m 
          /\ @has_been_sent message (IT j) (IS j) (IM j) (has_been_sent_capabilities j) (destination elem) m = false
          ) prefix.
          
          *)
          
          
        (* This is work in progress. To define equivocation fault, we must filter validators
        by the is_equivocating property. For this, in turn, we need is_equivocating to be decidable *)
          
        
         Class equivocation_dec := {
          is_equivocating_fn (s : indexed_state IT) (v : validator) : bool;
          
          is_equivocating_dec : forall (s : indexed_state IT) (v : validator),
           is_equivocating_fn s v = true <-> is_equivocating s v;
         }.
         
         Definition equivocating_validators
         (Dec : equivocation_dec)
         (s : indexed_state IT)
         : list validator
          := List.filter (is_equivocating_fn s) validator_listing.

         Definition equivocation_fault 
          (Dec : equivocation_dec)
          (s : indexed_state IT)
          : R
          :=
          List.fold_left Rplus (List.map Weight (equivocating_validators Dec s)) 0%R.
         
End Composite.


