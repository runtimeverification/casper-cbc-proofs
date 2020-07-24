Require Import
  List
  Bool
  Reals
  ListSet
  RelationClasses
  .

From CasperCBC
  Require Import
    Preamble
    CBC.Common
    ListExtras
  .

Class HasEquivocation (message : Type) := 
    { V : Type
    ; about_message : StrictlyComparable message
    ; about_V : StrictlyComparable V
    ; measurable_V : Measurable V
    ; reachable_threshold : ReachableThreshold V
    ; sender : message -> V
    ; message_preceeds_fn (m1 m2 : message) : bool
    ; equivocating_messages
        (msg1 msg2 : message)  : bool
        :=
        match compare_eq_dec msg1 msg2 with
        | left _  => false
        | _ =>
          match compare_eq_dec (sender msg1) (sender msg2) with
          | left _  =>
            negb (message_preceeds_fn msg1 msg2)
            && negb (message_preceeds_fn msg2 msg1)
          | right _ => false
          end
        end
    ; equivocating_in_set
        (msg : message)
        (msgs : set message)
        :=
        existsb (equivocating_messages msg) msgs
    
    ; equivocating_senders_set
        (msgs : set message)
        :=
        set_map compare_eq_dec sender
            (filter (fun msg => equivocating_in_set msg msgs) msgs)
    ; fault_weight_set
        (msgs : set message)
        := 
        sum_weights (equivocating_senders_set msgs)
    ; not_heavy_set
        (msgs : set message)
        :=  (fault_weight_set msgs <= proj1_sig threshold)%R
    }.



