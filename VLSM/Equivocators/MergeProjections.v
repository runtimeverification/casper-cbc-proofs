From CasperCBC.stdpp Require Import base decidable numbers.
From Coq Require Import ListSet Vectors.Fin Arith.Compare_dec Lia Program.
From CasperCBC Require Import Lib.Preamble Lib.ListExtras Lib.ListSetExtras Lib.FinExtras.
From CasperCBC Require Import VLSM.Common VLSM.Equivocation.
From CasperCBC Require Import VLSM.Equivocators.Common VLSM.Equivocators.Projections.

(** * VLSM Merging of Projections *)

Section trace_mixer.

Context
  {message : Type}
  (X : VLSM message)
  (equivocator_vlsm := equivocator_vlsm X)
  (MachineDescriptor := MachineDescriptor X)
  .

(** ** Reconstructing equivocator traces from projections

In this section we show that any set of protocol traces of the original
machine can be combined into a protocol trace for the [equivocator_vlsm]
having them as its projections.
*)

(** First, let us (re)define the projection of a trace segment.
In addition to [equivocator_vlsm_trace_project], this projection also
tracks the starting state of the trace segment and produces a starting
state for the corresponding projection.
*)
Definition preloaded_protocol_equivocator_vlsm_trace_oproject
  (is : vstate equivocator_vlsm)
  (btr : list (vtransition_item equivocator_vlsm))
  (nj : Fin.t (S (projT1 (finite_trace_last is btr))))
  : option (vstate X * list (vtransition_item X))
  :=
  let (j, _) := to_nat nj in
  match equivocator_vlsm_trace_project _ btr (Existing _ j false) with
  | Some (trx, NewMachine _ sn) => Some (sn, trx)
  | Some (trx, Existing _ i _) =>
    match (le_lt_dec (S (projT1 is)) i) with
    | left _ => None
    | right Hi => Some (projT2 is (of_nat_lt Hi), trx)
    end
  | _ => None
  end.

(** We define the type of all projectors such as the one above.
*)
Definition equivocator_vlsm_projector_type
  (is : vstate equivocator_vlsm)
  (btr : list (vtransition_item equivocator_vlsm))
  : Type
  :=
  forall
    (nj : Fin.t (S (projT1 (finite_trace_last is btr)))),
    option (vstate X * list (vtransition_item X)).

(** We define an update operation on such projectors.  This will
allow to swap an existing projection for a user provided trace.
*)
Definition equivocator_projection_update
  (is : vstate equivocator_vlsm)
  (btr : list (vtransition_item equivocator_vlsm))
  (projector : equivocator_vlsm_projector_type is btr)
  (ni : Fin.t (S (projT1 (finite_trace_last is btr))))
  (ni_trace : option (vstate X * list (vtransition_item X)))
  (nj : Fin.t (S (projT1 (finite_trace_last is btr))))
  : option (vstate X * list (vtransition_item X))
  :=
  if Fin.eq_dec ni nj then ni_trace else projector nj.

(** The update operation specialized to
[preloaded_protocol_equivocator_vlsm_trace_oproject]
*)
Definition preloaded_protocol_equivocator_vlsm_trace_oproject_update
  (is : vstate equivocator_vlsm)
  (btr : list (vtransition_item equivocator_vlsm))
  (ni : Fin.t (S (projT1 (finite_trace_last is btr))))
  (isi : vstate X)
  (tri : list (vtransition_item X))
  : equivocator_vlsm_projector_type is btr
  :=
  equivocator_projection_update is btr
    (preloaded_protocol_equivocator_vlsm_trace_oproject is btr)
    ni (Some (isi, tri)).

(** Given a projector, compute the list of all projections of a trace.
*)
Definition projection_traces
  (is : vstate equivocator_vlsm)
  (btr : list (vtransition_item equivocator_vlsm))
  (projector : equivocator_vlsm_projector_type is btr)
  (n := projT1 (finite_trace_last is btr))
  : list (vstate X * list (vtransition_item X))
  :=
  map_option projector (fin_t_listing (S n)).

(** [projection_traces] specialized to
[preloaded_protocol_equivocator_vlsm_trace_oproject_update]
(swapping one projection with the provided one)
*)
Definition projection_traces_replace_one
  (is : vstate equivocator_vlsm)
  (btr : list (vtransition_item equivocator_vlsm))
  (ni : Fin.t (S (projT1 (finite_trace_last is btr))))
  (isi : vstate X)
  (tri : list (vtransition_item X))
  : list (vstate X * list (vtransition_item X))
  :=
  projection_traces is btr
    (preloaded_protocol_equivocator_vlsm_trace_oproject_update is btr ni isi tri).

(**
No traces are lost in the projection process described above.
*)
Lemma projection_traces_replace_one_length
  (is : vstate equivocator_vlsm)
  (btr : list (vtransition_item equivocator_vlsm))
  (Hbtr : finite_protocol_trace (pre_loaded_with_all_messages_vlsm equivocator_vlsm) is btr)
  (n := projT1 (finite_trace_last is btr))
  (ni : Fin.t (S n))
  (isi : vstate X)
  (tri : list (vtransition_item X))
  : length (projection_traces_replace_one is btr ni isi tri) = S n.
Proof.
  unfold projection_traces_replace_one.
  unfold projection_traces.
  rewrite map_option_length; [apply fin_t_listing_length|].
  apply Forall_forall.
  intros nj Hnj.
  unfold preloaded_protocol_equivocator_vlsm_trace_oproject_update.
  unfold equivocator_projection_update.
  destruct (Fin.eq_dec ni nj).
  - rewrite eq_dec_if_true by assumption.
    congruence.
  - rewrite eq_dec_if_false by assumption.
    unfold preloaded_protocol_equivocator_vlsm_trace_oproject.
    destruct (to_nat nj) as [j Hj] eqn:Heqnj.
    pose proof (ptrace_add_last
      (base_prop:=@finite_protocol_trace_from) (proj1 Hbtr) (eq_refl _)).
    destruct
      (preloaded_equivocator_vlsm_project_protocol_trace _ _ _ _ H _ Hj false)
      as [trX [di [Hproject Hdi]]].
    rewrite Hproject.
    destruct di as [sn | i fi].
    + congruence.
    + destruct Hdi as [Hi [HtrX]].
      destruct (le_lt_dec (S (projT1 is)) i); [lia|].
      congruence.
Qed.

Context
  (goal_state : vstate equivocator_vlsm)
  (n := projT1 goal_state)
  (traces : list (vstate X * list (vtransition_item X)))
  (Hn : length traces = S n)
  (Htraces : Forall
    (fun trace =>
      finite_protocol_trace (pre_loaded_with_all_messages_vlsm X) (fst trace) (snd trace)
    )
    traces)
  (Hne_traces : Forall (fun trace => snd trace <> []) traces)
  (Hs
    : forall i : Fin.t (S n),
      let (ni, _) := to_nat i in
      match nth ni traces (proj1_sig (vs0 X), []) with (isi, tri) =>
        finite_trace_last isi tri = projT2 goal_state i
      end
  )
  .

Definition lift_first_trace_to_equivocator
  (tri : list (vtransition_item X))
  : list (vtransition_item equivocator_vlsm)
  :=
  fold_right
  (fun lab tr =>
    match lab with {| l := lx; input := iom; output := oom; destination := sx |} =>
      {| l := mk_label _ lx  (Existing _ 0 false); input := iom; output := oom; destination := mk_singleton_state _ sx |}
      :: tr
    end)
  [] tri.

Definition lift_trace_to_equivocator
  (start : vstate equivocator_vlsm)
  (i := projT1 start)
  (isi : vstate X)
  (tri : list (vtransition_item X))
  : list (vtransition_item equivocator_vlsm)
  :=
  match tri with
  | [] => []
  | {| l := lx; input := iom; output := oom; destination := sx |} :: tri' =>
    {| l := mk_label _ lx (NewMachine _ isi); input := iom; output := oom; destination := equivocator_state_extend _ start sx |}
    :: fold_right
      (fun lab tr =>
        match lab with {| l := lx; input := iom; output := oom; destination := sx |} =>
          {| l := mk_label _ lx  (Existing _ (S i) false); input := iom; output := oom; destination := equivocator_state_extend _ start sx |}
          :: tr
        end)
      [] tri
  end.

Definition lift_traces_to_equivocator
  : option (vstate equivocator_vlsm * list (vtransition_item equivocator_vlsm))
  :=
  match traces with
  | [] => None
  | (is0, tr0) :: traces =>
    let tr := lift_first_trace_to_equivocator tr0 in
    Some (mk_singleton_state _ is0, tr ++
      fst
        (fold_left
          (fun rez tracei =>
            let isxi := fst tracei in
            let trxi := snd tracei in
            match rez with (tr, s) =>
              let tri := lift_trace_to_equivocator s isxi trxi in
              (tr ++ tri, finite_trace_last s tri)
            end
          ) traces ([], proj1_sig (vs0 equivocator_vlsm))
        ))
  end.

End trace_mixer.
