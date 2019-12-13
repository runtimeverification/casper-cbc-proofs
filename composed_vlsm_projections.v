From Casper
Require Import preamble vlsm composed_vlsm.

Definition vlsm_projection_initial_state_prop
  {message : Type}
  `{CV : composed_sig_class message}
  (i : index)
  (is : istate i)
  : Prop
  :=
  exists s : initial_state, istate_proj i (proj1_sig s) = proj1_sig is.

Definition vlsm_projection_initial_state
  {message : Type}
  `{CV : composed_sig_class message}
  (i : index)
  :=
  { s : istate i | vlsm_projection_initial_state_prop i s }.

Definition vlsm_projection_s0
  {message : Type}
  `{CV : composed_sig_class message}
  (i : index)
  : (vlsm_projection_initial_state i).
remember (proj_istate (proj1_sig s0) i) as iis.
assert (Hiis : vlsm_projection_initial_state_prop i iis)
  by (exists s0; subst; reflexivity).
exact (exist _ iis Hiis).
Defined.

Definition lift_proto_message
  {message : Type}
  `{CV : composed_sig_class message}
  (i : index)
  (m : {x : message | iproto_message_prop i x})
  : proto_message
  :=
  let m0 := proj1_sig m in
  let Hcm := iproto_message_consistent i m0 (proj2_sig m) in
  (exist _ m0 Hcm).

Definition vlsm_projection_initial_message_prop
  {message : Type}
  `{CV : composed_vlsm_class message}
  (i : index)
  (m : {x : message | iproto_message_prop i x})
  : Prop
  :=
  exists m : protocol_message, iproto_message_prop i (proj1_sig (proj1_sig m)).

Definition vlsm_sig_projection
  {message : Type}
  `{CV : composed_vlsm_class message}
  (i : index)
  : LSM_sig (message : Type)
  :=
  {|  state := istate i
  ;   label := ilabel_type i
  ;   proto_message_prop := iproto_message_prop i
  ;   proto_message_decidable := iproto_message_decidable i
  ;   initial_state_prop := vlsm_projection_initial_state_prop i
  ;   initial_message_prop := vlsm_projection_initial_message_prop i
  ;   s0 := vlsm_projection_s0 i
  ;   m0 := im0 i
  ;   l0 := il0 i
  |}.

(*   ;   transition := vlsm_projection_transition i
  ;   valid := vlsm_projection_valid i
 *)

Definition transitioning_projection
  {message : Type}
  `{CV : composed_vlsm_class message}
  (i : index)
  (il : @label _ (vlsm_sig_projection i))
  (isom isom' : @state _ (vlsm_sig_projection i) * option {m : message | @proto_message_prop _ (vlsm_sig_projection i) m})
  :=
  let (si, omi) := isom in
  let (si', omi') := isom' in
  exists (s s' : state) (om om' : option proto_message),
    proj_istate s i = si /\
    proj_istate s' i = si' /\
    option_map (@proj1_sig _ _) om = option_map (@proj1_sig _ _)  omi /\
    option_map (@proj1_sig _ _)  om' = option_map (@proj1_sig _ _)  omi' /\
    transition (proj1_sig il) (s, om) = (s', om')
  .

Lemma vlsm_projection_transition_existence
  {message : Type}
  `{CV : composed_vlsm_class message}
  (i : index)
  (il : @label _ (vlsm_sig_projection i))
  (isom : @state _ (vlsm_sig_projection i) * option {m : message | @proto_message_prop _ (vlsm_sig_projection i) m})
  : exists isom' : @state _ (vlsm_sig_projection i) * option {m : message | @proto_message_prop _ (vlsm_sig_projection i) m}, 
      transitioning_projection i il isom isom'.
Proof.
  destruct isom as [is iom].
  destruct il as [l Hl].
  destruct is as [is [s His]].
  remember (option_map (lift_proto_message i) iom) as om.

  destruct (transition l (s, om)) as [s' om'] eqn:Ht.

  destruct om' as [m'|].
  - specialize (transition_projection_message_type_preservation s om l s' m' Ht); intros Hmsg.
    rewrite Hl in Hmsg.
    exists (proj_istate s' i, Some (exist _ (proj1_sig m') Hmsg)).
    exists s. exists s'. exists om. exists (Some m'). rewrite <- His.
    simpl.  repeat split; subst; try reflexivity; try assumption.
    destruct iom; try reflexivity.
  - exists (proj_istate s' i, None).
    exists s. exists s'. exists om. exists None. rewrite <- His. 
    simpl. repeat split; try reflexivity; try assumption.
    subst. destruct iom; try reflexivity.
Qed.

Require Import Coq.Logic.IndefiniteDescription.

Definition vlsm_projection_transition
  {message : Type}
  `{CV : composed_vlsm_class message}
  (i : index)
  (il : @label _ (vlsm_sig_projection i))
  (isom : @state _ (vlsm_sig_projection i) * option {m : message | @proto_message_prop _ (vlsm_sig_projection i) m})
  : @state _ (vlsm_sig_projection i) * option {m : message | @proto_message_prop _ (vlsm_sig_projection i) m}
  :=
  (proj1_sig
    (constructive_indefinite_description
      (transitioning_projection i il isom)
      (vlsm_projection_transition_existence i il isom)
    )
  ).

Lemma vlsm_projection_transition_destruct
  {message : Type}
  `{CV : composed_vlsm_class message}
  {i : index}
  {il : @label _ (vlsm_sig_projection i)}
  {isom isom' : @state _ (vlsm_sig_projection i) * option {m : message | @proto_message_prop _ (vlsm_sig_projection i) m}}
  (Ht : isom' = vlsm_projection_transition i il isom)
  : transitioning_projection i il isom isom'.
Proof.
  subst. unfold vlsm_projection_transition. 
  destruct (constructive_indefinite_description (transitioning_projection i il isom)
          (vlsm_projection_transition_existence i il isom)) as [isom'' Hisom''].
  assumption.
Qed.

Definition vlsm_projection_valid
  {message : Type}
  `{CV : composed_vlsm_class message}
  (i : index)
  (il : @label _ (vlsm_sig_projection i))
  (isom : @state _ (vlsm_sig_projection i) * option {m : message | @proto_message_prop _ (vlsm_sig_projection i) m})
  : Prop
  :=
  let (si, omi) := isom in
  exists (s : state) (om : option proto_message),
    istate_proj i s = proj1_sig si /\
    option_map (@proj1_sig _ _) om = option_map (@proj1_sig _ _) omi /\
    valid (proj1_sig il) (s, om).

Definition vlsm_projection
  {message : Type}
  `{CV : composed_vlsm_class message}
  (i : index)
  : @VLSM (message : Type) (vlsm_sig_projection i)
  :=
  {|  transition := vlsm_projection_transition i
  ;   valid := vlsm_projection_valid i
  |}.

Lemma protocol_state_projection
  {message : Type}
  {S : LSM_sig message}
  {V : @VLSM message S}
  {SV : @composed_sig_class _ S}
  `{CV : @composed_vlsm_class message _ SV V}
  (i : index)
  (som : state * option proto_message)
  (Hp : protocol_prop som)
  : exists ps : @protocol_state _ _ (vlsm_projection i), proj1_sig ps =  proj_istate (fst som) i.
Proof.
  induction Hp.
  - assert (His : vlsm_projection_initial_state_prop i (proj_istate s i))
      by (exists is; reflexivity).
    specialize (@protocol_initial_state _ _ (vlsm_projection i) (exist _ (proj_istate s i) His)); simpl.
    intro Hps. exists (exist _ (proj_istate s i) (ex_intro _ _ Hps)). reflexivity.
  - assert (His : vlsm_projection_initial_state_prop i (proj_istate s i))
      by (exists s0; reflexivity).
    specialize (@protocol_initial_state _ _ (vlsm_projection i) (exist _ (proj_istate s i) His)); simpl.
    intro Hps. exists (exist _ (proj_istate s i) (ex_intro _ _ Hps)). reflexivity.
  - destruct (index_eq_dec (ilabel l) i).
    + simpl in IHHp1. destruct IHHp1 as [[si Hpsi] Heqps]; simpl in Heqps.
      destruct om as [m|].
      * assert (Hmi : iproto_message_prop i (proj1_sig m)).
        { destruct (iproto_message_decidable i (proj1_sig m)); try assumption.
          exfalso.
          specialize (transition_projection_message_type_mismatch s m l). rewrite e; simpl; intros Hnv.
          specialize (Hnv n). contradiction.
        }
        remember (exist _ (proj1_sig m) Hmi) as mi.
        assert (Hpm : protocol_message_prop m)
          by (exists _s; assumption).
        remember (exist _ m Hpm) as pm.
        assert (Hmii : @initial_message_prop _ (vlsm_sig_projection i) mi)
          by (exists pm; subst; assumption).
        assert (Hpmi : @protocol_message_prop _ _ (vlsm_projection i) mi).
        { apply protocol_message_prop_iff. left. exists (exist _ mi Hmii). reflexivity. }
        remember (@transition _ _ (vlsm_projection i) (exist _ l e) (si, Some mi)) as t.
        destruct t as (si', omi').
        assert (Hpsi' : @protocol_state_prop _ _ (vlsm_projection i) si').
        { apply protocol_state_prop_iff. right. exists (exist _ si Hpsi). exists (exist _ l e).
          exists (Some (exist _ mi Hpmi)). simpl.
          split.
          - exists s. exists (Some m). subst; simpl. repeat split; try reflexivity. assumption.
          - assert (Hsi' : si' = fst (@transition message (@vlsm_sig_projection message S SV V CV i) (@vlsm_projection message S SV V CV i)
            (@exist (@label message S)
               (fun l : @label message S => @eq (@index message S SV) (@ilabel message S SV l) i) l e)
            (@pair (@state message (@vlsm_sig_projection message S SV V CV i))
               (option (@sig message (@iproto_message_prop message S SV i))) si
               (@Some (@sig message (@iproto_message_prop message S SV i)) mi))))
              by (rewrite <- Heqt; reflexivity).
            subst. apply f_equal. reflexivity.
        }
        exists (exist _ si' Hpsi'). simpl.
        specialize (vlsm_projection_transition_destruct Heqt); intro Ht0.
        destruct Ht0 as [s0 [s'0 [om0 [om'0 [Hs0 [Hs'0 Ht0]]]]]]. 
        simpl in Ht0. destruct Ht0 as [Hom0 [Hom'0 Ht0]].
        simpl. subst. destruct om0 as [m0|]; simpl in Hom0; inversion Hom0; clear Hom0.
        apply exist_eq in H0. subst.
        specialize (transition_projection_consistency s s0 (Some m) l).
        simpl. intros Heq. symmetry in Hs0. apply proj_istate_eq in Hs0.
        specialize (Heq Hs0). simpl in Heq.
        destruct (transition l (s, Some m)) as [s' om'] eqn:Ht.
        rewrite Ht0 in Heq. destruct Heq as [_ Heq].
        symmetry. apply proj_istate_eq. assumption.
      * remember (@transition _ _ (vlsm_projection i) (exist _ l e) (si, None)) as t.
        destruct t as (si', omi').
        assert (Hpsi' : @protocol_state_prop _ _ (vlsm_projection i) si').
        { apply protocol_state_prop_iff. right. exists (exist _ si Hpsi). exists (exist _ l e).
          exists None. simpl.
          split.
          - exists s. exists None. subst; simpl. repeat split; try reflexivity. assumption.
          - assert
              (Hsi' : si' = fst
                (@transition message (@vlsm_sig_projection message S SV V CV i) (@vlsm_projection message S SV V CV i)
                  (@exist (@label message S)
                     (fun l : @label message S => @eq (@index message S SV) (@ilabel message S SV l) i) l e)
                  (@pair (@state message (@vlsm_sig_projection message S SV V CV i))
                     (option (@proto_message message (@vlsm_sig_projection message S SV V CV i))) si
                     (@None (@proto_message message (@vlsm_sig_projection message S SV V CV i))))
                )
              ) by (rewrite <- Heqt; reflexivity).
            subst. apply f_equal. reflexivity.
        }
        exists (exist _ si' Hpsi'). simpl.
        specialize (vlsm_projection_transition_destruct Heqt); intro Ht0.
        destruct Ht0 as [s0 [s'0 [om0 [om'0 [Hs0 [Hs'0 Ht0]]]]]]. 
        simpl in Ht0. destruct Ht0 as [Hom0 [Hom'0 Ht0]].
        simpl. subst. destruct om0 as [m0|]; simpl in Hom0; inversion Hom0; clear Hom0.
        specialize (transition_projection_consistency s s0 None l).
        simpl. intros Heq. symmetry in Hs0. apply proj_istate_eq in Hs0.
        specialize (Heq Hs0). 
        destruct (transition l (s,None)) as [s' om'] eqn:Ht.
        rewrite Ht0 in Heq. destruct Heq as [_ Heq].
        symmetry. apply proj_istate_eq. assumption.
    + specialize (transition_projection_state_preservation s om l i n).
      destruct (transition l (s, om)) eqn:Ht.
      intros Heq.
      destruct IHHp1 as [ps Heqps].
      exists ps. rewrite Heqps. simpl. symmetry. apply proj_istate_eq. assumption.
Qed.
