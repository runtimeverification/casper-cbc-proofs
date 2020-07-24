Require Import List Streams ProofIrrelevance Coq.Arith.Plus Coq.Arith.Minus Coq.Logic.FinFun Coq.Reals.Reals.
Import ListNotations.

From CasperCBC
Require Import Lib.Preamble VLSM.Common VLSM.Composition.

(** 
*** Summary
This chapter is dedicated to building the language for discussing equivocation.
    Equivocation occurs on the receipt of a message which has not been previously sent.
    The designated sender (validator) of the message is then said to be equivocating.
    Our main purpose is to keep track of equivocating senders in a composite context
    and limit equivocation by means of a composition constraint.
**)

(** **)

(**
*** State-message oracles. Endowing states with history.

    Our first step is to define some useful concepts in the context of a single VLSM.
    
    Apart from basic definitions of equivocation, we introduce the concept of a
    [state_message_oracle]. Such an oracle can, given a state and a message,
    decide whether the message has been sent (or received) in the history leading
    to the current state. Formally, we say that a [message] <m> [has_been_sent] 
    if we're in  [state] <s> iff every protocol trace which produces <s> contains <m> 
    as a sent message somewhere along the way.
    
    The existence of such oracles, which practically imply endowing states with history,
    is necessary if we are to detect equivocation using a composition constaint, as these
    constraints act upon states, not traces.
 **)

Section Simple.
    Context
      {message : Type}
      {vtype : VLSM_type message}
      {Sig : VLSM_sign vtype}
      (vlsm : VLSM Sig).
  
(** We begin with a basic utility function. **)

    Definition trace_has_message
      (message_selector : transition_item -> option message)
      (msg : message)
      (tr : protocol_trace vlsm)
      : Prop
      := exists (last : transition_item),
         exists (prefix : list transition_item),
          trace_prefix (proj1_sig tr) last prefix
          /\ message_selector last = Some msg.
          
(** The following property detects equivocation in a given trace for a given message. **)

    Definition equivocation_in_trace
               (msg : message)
               (tr : protocol_trace vlsm)
      : Prop
      :=
        exists (last : transition_item),
        exists (prefix : list transition_item),
          trace_prefix (proj1_sig tr) last prefix
          /\  input last = Some msg
          /\  ~ In (Some msg) (List.map output prefix).

(** We intend to give define several message oracles: [has_been_sent], [has_not_been_sent],
    [has_been_received] and [has_not_been_received]. To avoid repetition, we give
    build some generic definitions first. **)
    
(** General signature of a message oracle **)

    Definition state_message_oracle (x : VLSM Sig)
      := (state) -> (message) -> bool.
    
(** Checks if all [protocol_trace]s leading to a certain state contain a certain message. 
    The [message_selector] argument specifices whether we're looking for received or sent
    messages.
    
    Notably, the [protocol_trace]s over which we are iterating belong to the preloaded
    version of the target VLSM. This is because we want VLSMs to have oracles which
    are valid irrespective of the composition they take part in. As we know, 
    the behaviour preloaded VLSMs includes behaviours of its projections in any
    composition. **) 
    
    Definition all_traces_have_message_prop
      (message_selector : transition_item -> option message)
      (oracle : state_message_oracle vlsm) 
      (s : state)
      (m : message) 
      : Prop 
      := 
      oracle s m = true <-> 
        forall 
        (tr : protocol_trace (pre_loaded_vlsm vlsm))
        (last : transition_item)
        (prefix : list transition_item)
        (Hpr : trace_prefix (proj1_sig tr) last prefix)
        (Hlast : destination last = s),
        List.Exists (fun (elem : transition_item) => message_selector elem = Some m) prefix.
        
    Definition no_traces_have_message_prop
      (message_selector : transition_item -> option message)
      (oracle : state_message_oracle vlsm) 
      (s : state)
      (m : message) 

      : Prop 
      := 
      oracle s m = true <-> 
        forall 
        (tr : protocol_trace (pre_loaded_vlsm vlsm))
        (last : transition_item)
        (prefix : list transition_item)
        (Hpr : trace_prefix (proj1_sig tr) last prefix)
        (Hlast : destination last = s),
        ~ List.Exists (fun (elem : transition_item) => message_selector elem = Some m) prefix.
      
    Definition has_been_sent_prop : state_message_oracle vlsm -> state -> message -> Prop
      := (all_traces_have_message_prop output).
      
    Definition has_not_been_sent_prop : state_message_oracle vlsm -> state -> message -> Prop
      := (no_traces_have_message_prop output).    
      
    Definition has_been_received_prop : state_message_oracle vlsm -> state -> message -> Prop
      := (all_traces_have_message_prop input).
      
    Definition has_not_been_received_prop : state_message_oracle vlsm -> state -> message -> Prop
      := (no_traces_have_message_prop input).

(** Per the vocabulary of the official VLSM document, we say that VLSMs endowed
    with a [state_message_oracle] for sent messages have the [has_been_sent] capability.
    Capabilities for receiving messages are treated analogously, so we omit mentioning
    them explicitly.
    
    Notably, we also define the [has_not_been_sent] oracle, which decides if a message
    has definitely not been sent, on any of the traces producing a current state. 
    
    Furthermore, we require a [sent_excluded_middle] property, which stipulates
    that any argument to the oracle should return true in exactly one of 
    [has_been_sent] and [has_not_been_sent]. **)

    Class has_been_sent_capability := { 
      has_been_sent: state_message_oracle vlsm;
      
      proper_sent: 
        forall (s : state) 
               (m : message), 
               (has_been_sent_prop has_been_sent s m);
      
      has_not_been_sent: state_message_oracle vlsm;
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
      has_been_received: state_message_oracle vlsm;
      
      proper_received: 
        forall (s : state) 
               (m : message), 
               (has_been_received_prop has_been_received s m);
      
      has_not_been_received: state_message_oracle vlsm;
      proper_not_received: 
        forall (s : state) 
               (m : message), 
               has_not_been_received_prop has_not_been_received s m;
      
      received_excluded_middle : 
        forall (s : state) 
               (m : message),
               has_been_received s m = true <-> has_not_been_received s m = false;
    }.

End Simple.

(**
*** Equivocation in compositions.

 We now move on to a composite context. Each component of our composition
    will have [has_been_sent] and [has_been_received] capabilities.
    
    We introduce [validator]s along with their respective [Weight]s, the
    [A] function which maps validators to indices of component VLSMs and
    the [sender] function which maps messages to their (unique) designated
    sender (if any).
    
    For the equivocation fault sum to be computable, we also require that
    the number of [validator]s and the number of machines in the 
    composition are both finite. See [finite_index], [finite_validator].
**)

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
            {IS : forall i : index, VLSM_sign (IT i)}
            (IM : forall n : index, VLSM (IS n))
            (constraint : _composite_label IT -> _composite_state IT  * option message -> Prop)
            (has_been_sent_capabilities : forall i : index, (has_been_sent_capability (IM i)))
            (has_been_received_capabilities : forall i : index, (has_been_received_capability (IM i)))
            (sender : message -> option validator)
            (A : validator -> index)
            (Weight : validator -> R)
            (T : R)
            (X := composite_vlsm i0 IM constraint).
            
     (** It is now straightforward to define a [no_equivocations] composition constraint.
         An equivocating transition can be detected by calling the [has_been_sent] 
         oracle on its arguments and we simply forbid them **)
         
     Definition equivocation 
      (m : message) 
      (s : _composite_state IT) 
      : Prop  
      := 
      forall (i : index), 
      has_not_been_sent (IM i) (s i) m = true.
      
      (* TODO: Reevaluate if this looks better in a positive form *)
      
      Definition no_equivocations
        (l : _composite_label IT)
        (som : _composite_state IT * option message)
        : Prop
        := 
        let (s, om) := som in
        match om with 
        | None => True
        | Some m => ~equivocation m s
        end.
      
      
      (** Definitions for safety and nontriviality of the [sender] function.
          Safety means that if we designate a validator as the sender
          of a certain messsage, then it is impossible for other components
          to produce that message 
         
          Weak/strong nontriviality say that each validator should
          be designated sender for at least one/all its protocol
          messages. 
      **)
      
      Definition sender_safety_prop : Prop := 
        forall 
        (i : index)
        (m : message)
        (v : validator)
        (Hid : A v = i)
        (Hsender : sender m = Some v),
        can_emit (composite_vlsm_constrained_projection i0 IM constraint i) m /\
        forall (j : index)
               (Hdif : i <> j),
               ~can_emit (composite_vlsm_constrained_projection i0 IM constraint j) m.
       
       (** An alternative, possibly friendlier, formulation. Note that it is
           slightly weaker, in that it does not require that the sender
           is able to send the message. **)
       
       Definition sender_safety_alt_prop : Prop :=
        forall 
        (i : index)
        (m : message)
        (v : validator)
        (Hsender : sender m = Some v),
        can_emit (composite_vlsm_constrained_projection i0 IM constraint i) m ->
        A v = i.
               
       Definition sender_weak_nontriviality_prop : Prop :=
        forall (v : validator),
        exists (m : message),
        can_emit (composite_vlsm_constrained_projection i0 IM constraint (A v)) m /\
        sender m = Some v.
        
       Definition sender_strong_nontriviality_prop : Prop :=
        forall (v : validator),
        forall (m : message),
        can_emit (composite_vlsm_constrained_projection i0 IM constraint (A v)) m ->
        sender m = Some v.
        
        
       (** We say that a validator <v> (with associated component <i>) is equivocating wrt. 
       to another component <j>, if there exists a message which [has_been_received] by 
       <j> but [has_not_been_sent] by <i> **)
          
       Definition equivocating_wrt
        (v : validator)
        (j : index)
        (sv sj : state)
        (i := A v)
        : Prop
        := 
        exists (m : message),
        sender(m) = Some v /\
        has_not_been_sent  (IM i) sv m = true /\
        has_been_received  (IM j) sj m = true.
        
        (** We can now decide whether a validator is equivocating in a certain state. **)
        
        Definition is_equivocating_statewise
          (s : _composite_state IT)
          (v : validator)
          : Prop
          :=
          exists (j : index),
          j <> (A v) /\
          equivocating_wrt v j (s (A v)) (s j).
          
        (** An alternative definition for detecting equivocation in a certain state,
            which checks if for every [protocol_trace] there exists equivocation
            involving the given validator
            
            Notably, this definition is not generally equivalent to [is_equivocating_statewise],
            which does not verify the order in which receiving and sending occurred.
        **) 
        
        Definition is_equivocating_tracewise
          (v : validator)
          (s : _composite_state IT)
          (j := A v)
          : Prop
          := 
          forall (tr : protocol_trace X)
          (last : transition_item)
          (prefix : list transition_item)
          (Hpr : trace_prefix (proj1_sig tr) last prefix)
          (Hlast : destination last = s),
          exists (m : message),
          (sender m = Some v) /\
          List.Exists 
          (fun (elem : @transition_item _ (type X)) => 
          input elem = Some m 
          /\ has_been_sent (IM j) ((destination elem) j) m = false
          ) prefix.
          
          
        
          
        (** A possibly friendlier version using a previously defined primitive. **)
        Definition is_equivocating_tracewise_alt
          (v : validator)
          (s : _composite_state IT)
          (j := A v)
          : Prop
          := 
          forall (tr : protocol_trace X)
          (last : transition_item)
          (prefix : list transition_item)
          (Hpr : trace_prefix (proj1_sig tr) last prefix)
          (Hlast : destination last = s),
          exists (m : message),
          (sender m = Some v) /\
          equivocation_in_trace X m (build_trace_prefix_protocol X Hpr).
        
        (** For the equivocation sum fault to be computable, we require that
            our is_equivocating property is decidable. The current implementation
            refers to [is_equivocating_statewise], but this might change
            in the future **)
            
         Class equivocation_dec_statewise := {
          is_equivocating_fn (s : _composite_state IT) (v : validator) : bool;
          
          is_equivocating_dec : forall (s : _composite_state IT) (v : validator),
           is_equivocating_fn s v = true <-> is_equivocating_statewise s v;
         }.
         
         (** All validators which are equivocating in a given composite state **)
         
         Definition equivocating_validators
         (Dec : equivocation_dec_statewise)
         (s : _composite_state IT)
         : list validator
          := List.filter (is_equivocating_fn s) validator_listing.
          
          (** The equivocation fault sum: the sum of the weights of equivocating
          validators **)
          
         Definition equivocation_fault 
          (Dec : equivocation_dec_statewise)
          (s : _composite_state IT)
          : R
          :=
          List.fold_left Rplus (List.map Weight (equivocating_validators Dec s)) 0%R.
        
        (** Finally, we are able to define a composition constraint which limits
        the equivocation fault to a threshold <T> **)
        
         Definition equivocation_fault_constraint
          (Dec : equivocation_dec_statewise)
          (l : _composite_label IT)
          (som : _composite_state IT * option message)
          : Prop
          := 
          let (s', om') := (@transition _ _ _ X l som) in
          Rle (equivocation_fault Dec s') T.
          
End Composite.


