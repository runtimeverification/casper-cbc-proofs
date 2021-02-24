Require Import Bool List ListSet Reals FinFun RelationClasses Relations Relations_1 Sorting.
Require Import Lia.
Import ListNotations.
From CasperCBC
Require Import
  Lib.Preamble
  Lib.ListExtras
  Lib.ListSetExtras
  Lib.SortedLists
  VLSM.Common
  VLSM.Composition
  VLSM.Equivocation
  VLSM.ListValidator.ListValidator
  VLSM.ObservableEquivocation
  CBC.Common
  CBC.Equivocation.

Section Equivocation.

Context
  {index : Type}
  {index_self : index}
  {index_listing : list index}
  {Hfinite : Listing index_listing}
  {idec : EqDecision index}
  (est : state -> bool -> Prop)
  (X := @VLSM_list _ index_self index_listing idec est)
  (preX := pre_loaded_with_all_messages_vlsm X)
  (Xtype := type preX)
  {mdec : EqDecision (@message index index_listing)}
  {Mindex : Measurable index}
  {Rindex : ReachableThreshold index}.

  Definition last_recorded (l : list index) (ls : indexed_state l) (who : index) : state :=
    @project_indexed _ index_listing _ l ls who.

  Definition last_sent (s : vstate X) : vstate X := project s index_self.

  Fixpoint rec_history (s : state) (who : index) (d : nat) : list state :=
    match s, d with
    | Bottom, _ => []
    | _, 0 => []
    | (Something cv ls), (S d') => s :: rec_history (last_recorded index_listing ls who) who d'
    end.

  Definition get_history (s : state) (who : index) : list state :=
     match s with
     | Bottom => []
     | Something cv ls => let child := last_recorded index_listing ls who in
                          rec_history child who (depth child)
    end.

  (* Definition list_message_equivocation_evidence : message_equivocation_evidence message index. *)

  Definition state_eqb (s1 s2 : state) : bool :=
    match @state_eq_dec _ index_listing s1 s2 with
    | left _ => true
    | right _ => false
    end.

  Lemma state_eqb_eq (s1 s2 : state) :
    (state_eqb s1 s2) = true <-> s1 = s2.
  Proof.
    unfold state_eqb.
    split.
    - destruct (state_eq_dec s1 s2).
      + intuition.
      + intros. discriminate H.
    - intros.
      destruct (state_eq_dec s1 s2);
      intuition.
  Qed.

  Lemma state_eqb_neq (s1 s2 : state) :
    (state_eqb s1 s2) = false <-> s1 <> s2.
  Proof.
    unfold state_eqb.
    split;
    destruct (state_eq_dec s1 s2);
    intuition.
  Qed.

  Definition send_oracle (s : state) (m : message)  : bool :=
    let who := fst m in
    let what := snd m in
    match decide (who = index_self) with
    | right _ => false
    | left _ => existsb (state_eqb what) (get_history s who)
    end.

  Global Instance send_oracle_dec
    : RelDecision send_oracle
    := fun s m => bool_decision.

  Definition receive_oracle (s : state) (m : message) : bool :=
    let who := fst m in
    let what := snd m in
    match decide (who = index_self) with
    | left _ => false
    | right _ => existsb (state_eqb what) (get_history s who)
    end.

  Global Instance receive_oracle_dec
    : RelDecision receive_oracle
    := fun s m => bool_decision.

    Definition not_send_oracle (s : state) (m : message)  : Prop :=
      ~ send_oracle s m.

    Definition not_receive_oracle (s : state) (m : message) : Prop :=
      ~ receive_oracle s m.

    Lemma protocol_no_bottom
      (s : protocol_state preX) :
      (proj1_sig s) <> Bottom.
    Proof.
      destruct s as [x H].
      simpl.
      destruct H as [x0 H].
      change x with (fst (x, x0)).
      remember (x, x0) as gigi.
      clear x x0 Heqgigi.
      induction H.
      - simpl. 
        destruct Hs.
        congruence.
      - destruct l eqn : eq.
        + intros.
          simpl in *.
          unfold update_consensus.
          unfold update_state.
          destruct s;congruence.
        + intros.
          simpl in *.
          destruct s;[congruence|].
          destruct om;simpl;discriminate.
    Qed.

    Lemma protocol_prop_no_bottom :
      forall (s : state)
             (Hprotocol_prop : protocol_state_prop preX s),
             s <> Bottom.
    Proof.
      intros.
      remember (exist _ s Hprotocol_prop) as protocol_s.
      assert (s = proj1_sig protocol_s).
        - inversion Heqprotocol_s. simpl. reflexivity.
        - rewrite H. apply protocol_no_bottom.
    Qed.

    Lemma depth_redundancy :
      forall (s : state)
             (i : index)
             (d : nat)
             (Hbig : d >= depth s),
        rec_history s i d = rec_history s i (depth s).
    Proof.
      intros.
      remember (depth s) as dpth.
      generalize dependent s. generalize dependent d.
      induction dpth using (well_founded_induction lt_wf); intros.
      destruct s.
      - simpl. unfold rec_history.
         destruct d; destruct dpth; reflexivity.
      - destruct dpth.
        + unfold depth in Heqdpth. lia.
        + destruct d.
          * lia.
          * simpl. f_equal.
            {
              unfold last_recorded.
              pose (depth (project_indexed index_listing is i)) as dlst.
              pose (@depth_parent_child index index_listing Hfinite _ is b i) as Hdlst.
              apply eq_trans with (rec_history (project_indexed index_listing is i) i dlst).
              -
                apply H; lia.
              - symmetry. apply H; lia.
            }
    Qed.

    Lemma history_oblivious:
      forall (s : state)
             (news : state)
             (i : index)
             (j : index)
             (Hdif : j <> i),
             get_history s i = get_history (update_state s news j) i.
    Proof.
      intros.
      unfold get_history.
      destruct s.
      - simpl. reflexivity.
      - simpl.
        assert ((last_recorded index_listing is i) =
                (last_recorded index_listing (update_indexed index_listing is j news) i)). {
                  unfold last_recorded.
                  symmetry.
                  apply update_indexed_different.
                  assumption.
                  split.
                  apply ((proj2 Hfinite) j).
                  apply ((proj2 Hfinite) i).
                }
        rewrite H.
        reflexivity.
    Qed.

    Lemma history_disregards_cv :
        forall (s : state)
               (cv : bool)
               (i : index),
          get_history (update_consensus s cv) i = get_history s i.
    Proof.
      intros.
      unfold update_consensus.
      destruct s.
      - reflexivity.
      - reflexivity.
    Qed.

    Lemma history_append
      (s : state)
      (news : state)
      (Hno_bottom_s : s <> Bottom)
      (Hno_bottom_news : news <> Bottom)
      (i : index)
      (Hvalidity : project news i = project s i) :
      get_history (update_state s news i) i = (news :: get_history s i).
    Proof.
      intros.
      unfold update_state.
      destruct s eqn : s_eq.
      - elim Hno_bottom_s. reflexivity.
      - unfold get_history.
        unfold last_recorded.

        assert ((project_indexed index_listing (update_indexed index_listing is i news) i) =
                 news). {
          apply update_indexed_same.
          reflexivity.
          apply ((proj2 Hfinite) i).
        }

        rewrite H.
        destruct news eqn : news_eq.
        + elim Hno_bottom_news.
          reflexivity.
        + unfold rec_history at 1.
          simpl in *.
          assert ((depth (Something b0 is0)) >= (S (depth (project_indexed index_listing is i)))). {
            rewrite <- Hvalidity.
            apply (@depth_parent_child index index_listing Hfinite).
          }

          assert (exists x, depth (Something b0 is0) = S x /\ x >= depth (project_indexed index_listing is i)). {
            destruct (depth (Something b0 is0)).
            lia.
            exists n.
            split.
            reflexivity.
            lia.
          }
          destruct H1 as [x [Heqx Hineqx]].
          rewrite Heqx.
          unfold last_recorded.
          rewrite Hvalidity.
          specialize (depth_redundancy (project_indexed index_listing is i) i).
          intros.
          specialize (H1 x Hineqx).
          rewrite <- H1.
          reflexivity.
    Qed.

    Lemma unfold_history
      (s1 s2 : state)
      (i : index)
      (pref suff : list state)
      (Hin : get_history s1 i = pref ++ [s2] ++ suff) :
      suff = get_history s2 i.
    Proof.
      generalize dependent s1.
      generalize dependent s2.
      generalize dependent suff.
      generalize dependent pref.
      induction pref.
      - intros. simpl in *.
        unfold get_history in Hin.
        destruct s1.
        + discriminate Hin.
        + unfold rec_history in Hin.
          destruct (last_recorded index_listing is i).
          * simpl in Hin. discriminate Hin.
          * destruct (depth (Something b0 is0)) eqn : eq_d.
            discriminate Hin.
            inversion Hin.
            unfold get_history.
            rewrite depth_redundancy.
            reflexivity.
            specialize (@depth_parent_child _ _ Hfinite _ is0 b0 i).
            intros.
            rewrite eq_d in H.
            unfold last_recorded.
            lia.
      - intros.
        unfold get_history in Hin.
        specialize (IHpref suff s2 a).
        apply IHpref.

        destruct s1.
        + discriminate Hin.
        + unfold rec_history in Hin.
          * destruct (last_recorded index_listing is i).
            simpl in *.
            discriminate Hin.
            destruct (depth (Something b0 is0)) eqn : eq_d.
            discriminate Hin.
            inversion Hin.
            unfold get_history.
            unfold rec_history.

            rewrite depth_redundancy in H1.
            unfold rec_history.
            assumption.
            specialize (@depth_parent_child _ _ Hfinite _ is0 b0 i).
            intros.
            rewrite eq_d in H.
            unfold last_recorded.
            lia.
    Qed.

    Lemma unfold_history_bottom
      (s : state)
      (i : index)
      (Hnbp : project s i = Bottom)
      : get_history s i = [].
    Proof.
      destruct s; try reflexivity; simpl in *.
      unfold last_recorded. rewrite Hnbp. reflexivity.
    Qed.

    Lemma unfold_history_cons
      (s : state)
      (i : index)
      (Hnbp : project s i <> Bottom)
      : get_history s i = project s i :: get_history (project s i) i.
    Proof.
      assert (Hproject : exists suff, get_history s i = project s i :: suff).
      { unfold get_history. unfold project. destruct s; try (elim Hnbp; reflexivity).
        unfold last_recorded.
        destruct (project_indexed index_listing is i) eqn: Hproject; try (elim Hnbp; assumption).
        destruct (depth (Something b0 is0)) eqn:Hdepth.
        - unfold depth in Hdepth. lia.
        - exists (rec_history (last_recorded index_listing is0 i) i n).
          reflexivity.
      }
      destruct Hproject as [suff Hproject].
      specialize (unfold_history s (project s i) i [] suff Hproject) as Hunfold.
      subst. assumption.
    Qed.

    Lemma unfold_history_cons_iff
      (s : state)
      (i : index)
      (s1 : state)
      (ls : list state)
      (Hcons : get_history s i = s1 :: ls)
      : s1 = project s i
      /\ ls = get_history (project s i) i.
    Proof.
      destruct (project s i) eqn : eq_project.
      - unfold get_history in Hcons.
        destruct s.
        discriminate Hcons.
        unfold last_recorded in Hcons.
        unfold rec_history in Hcons.
        unfold project in eq_project.
        rewrite eq_project in Hcons.
        simpl in Hcons.
        discriminate Hcons.
      - specialize (unfold_history_cons s i).
        intros.
        spec H.
        rewrite eq_project.
        intuition.
        discriminate H0.
        rewrite Hcons in H.
        inversion H.
        split.
        assumption.
        rewrite eq_project.
        reflexivity.
    Qed.

    Lemma history_incl_equiv_suffix
      (s1 s2 : state)
      (i : index)
      (history1 := get_history s1 i)
      (history2 := get_history s2 i) :
      incl history1 history2 <->
      exists (pref' : list state), history2 = pref' ++ history1.
   Proof.
    split.
    - intros.
      unfold incl in H.
      destruct history1 eqn : eq_1.
      + simpl in *.
        intros.
        exists history2.
        rewrite app_nil_r.
        reflexivity.
      + specialize (H s).
        simpl in *.
        assert (s = s \/ In s l). {
          left. reflexivity.
        }

        specialize (H H0).
        apply in_split in H.
        destruct H as [pref [suff Hsplit]].
        unfold history2 in Hsplit.
        specialize (unfold_history s2 s i pref suff Hsplit).
        intros.
        exists pref.
        unfold history2.
        rewrite Hsplit.
        rewrite H.

        assert (get_history s i = l). {
          unfold history1 in eq_1.
          specialize (unfold_history s1 s i [] l eq_1).
          intros.
          symmetry.
          assumption.
        }

        rewrite H1.
        reflexivity.
      - intros.
        destruct H as [pref Hconcat].
        assert (incl history1 history1). {
          apply incl_refl.
        }

        apply incl_appr with (m := pref) in H.
        rewrite <- Hconcat in H.
        assumption.
    Qed.

    Lemma history_no_self_reference
      (s : state)
      (i : index)
      : ~ In s (get_history s i).
    Proof.
      intro Hs. apply in_split in Hs.
      destruct Hs as [pref [suff Hs]].
      specialize (unfold_history s s i pref suff Hs) as Hsuff.
      subst suff.
      assert (Hl : length(get_history s i) = length(pref ++ s :: get_history s i))
        by (f_equal; assumption).
      rewrite app_length in Hl. simpl in Hl. lia.
    Qed.

    Lemma projection_in_history
      (s : state)
      (news : state)
      (i : index)
      (Hnot_bottom : news <> Bottom)
      (Hproject : project s i = news) :
      In news (get_history s i).
    Proof.
      intros.
      unfold get_history.
      unfold project in Hproject.
      destruct s eqn : eqs.
      - rewrite Hproject in Hnot_bottom. elim Hnot_bottom. reflexivity.
      - unfold last_recorded.
        rewrite Hproject.
        unfold rec_history.
        destruct news.
        + elim Hnot_bottom. reflexivity.
        + assert (exists x, depth (Something b0 is0) = S x). {
          exists (depth_indexed index_listing is0).
          unfold depth.
          unfold depth_indexed.
          lia.
        }
        destruct H.
        rewrite H.
        unfold In.
        left.
        reflexivity.
    Qed.

    Lemma emitted_messages_only_from_self
      (m : message)
      (Hemit : can_emit preX m) :
      (fst m) = index_self.
    Proof.
      unfold can_emit in Hemit.
      simpl in *.
      destruct Hemit as [som [l [s Htransition]]].
      simpl in *.
      inversion Htransition.
      simpl in *.
      unfold transition in H0.
      simpl in *.
      destruct l.
      - destruct som. inversion H0. simpl. reflexivity.
      - destruct som. destruct o; discriminate H0.
    Qed.

    Lemma emitted_not_bottom
      (m : message)
      (Hemit : can_emit preX m) :
      (snd m) <> Bottom.
    Proof.
      unfold can_emit in Hemit.
      destruct Hemit as [som [l [s Htransition]]].
      simpl in *.
      inversion Htransition.
      simpl in *.
      unfold transition in H0.
      destruct som.
      destruct H.
      destruct l eqn : eq_l.
      - simpl in *.
        inversion H0.
        simpl.
        apply protocol_prop_no_bottom.
        assumption.
      - destruct o; inversion H0.
    Qed.

    Lemma depth_zero_bottom
      (s : state)
      (Hzero : @depth index index_listing s = 0) :
      s = Bottom.
    Proof.
      unfold depth in Hzero.
      destruct s.
      - reflexivity.
      - lia.
    Qed.

    Lemma no_bottom_in_history_rec
      (s s': state)
      (i : index)
      (l : list state)
      (Heql : l = rec_history s i (depth s))
      (Hin : In s' l) :
      s' <> Bottom.
    Proof.
      generalize dependent s.
      generalize dependent s'.
      induction l.
      - intros.
        simpl in *.
        intuition.
      - intros.
        destruct (state_eq_dec a s').
        + destruct s eqn : eq_s.
          * discriminate Heql.
          * unfold rec_history in Heql.
            simpl in *.
            assert (exists (n : nat), depth (Something b is) = n + 1). {
              exists (depth_indexed index_listing is).
              unfold depth.
              reflexivity.
            }

            destruct H as [n H].
            rewrite H in Heql.
            replace (n + 1) with (S n) in Heql.
            inversion Heql.
            rewrite <- e.
            rewrite H1.
            intuition.
            discriminate H0.
            discriminate H0.
            lia.
        + simpl in Hin.
          destruct Hin.
          * elim n.
            intuition.
          * unfold get_history in Heql.
            destruct s.
            discriminate Heql.
            unfold rec_history in Heql.
            simpl in *.

            assert (exists (n : nat), depth (Something b is) = n + 1). {
              exists (depth_indexed index_listing is).
              unfold depth.
              reflexivity.
            }

            destruct H0 as [m H0].
            rewrite H0 in Heql.
            replace (m + 1) with (S m) in Heql.
            specialize (IHl s' H (last_recorded index_listing is i)).
            inversion Heql.

            assert (m >= depth (last_recorded index_listing is i)). {
               specialize (@depth_parent_child _ _ Hfinite _ is b i).
               intros.
               rewrite H0 in H1.
               unfold last_recorded.
               lia.
            }

            rewrite depth_redundancy in H3.
            specialize (IHl H3).
            assumption.
            assumption.
            lia.
    Qed.

    Lemma no_bottom_in_history
      (s s': state)
      (i : index)
      (Hin : In s' (get_history s i)) :
      s' <> Bottom.
    Proof.
      unfold get_history in Hin.
      destruct s.
      - simpl in Hin.
        intuition.
      - specialize (no_bottom_in_history_rec (last_recorded index_listing is i)).
        intros.
        specialize (H s' i (rec_history (last_recorded index_listing is i) i
           (depth (last_recorded index_listing is i)))).
        specialize (H eq_refl Hin).
        assumption.
    Qed.

    Lemma project_all_bottom_f
      (i : index)
      (l : list index) :
      @project_indexed _ index_listing _ l (all_bottom_f l) i = Bottom.
    Proof.
      induction l.
      - simpl. reflexivity.
      - simpl.
        destruct (decide (a = i)).
        + reflexivity.
        + assumption.
    Qed.

    Lemma project_all_bottom
      (i : index) :
      project_indexed index_listing all_bottom i = Bottom.
    Proof.
      apply project_all_bottom_f.
    Qed.

    Lemma get_history_all_bottom
      (cv : bool)
      (i : index)
      : get_history (Something cv all_bottom) i = [].
    Proof.
      unfold get_history.
      unfold last_recorded.
      rewrite project_all_bottom.
      simpl.
      reflexivity.
    Qed.

    Lemma byzantine_message_self_id
      (m : message)
      (Hm : byzantine_message_prop X m)
      : fst m = index_self /\ protocol_state_prop preX (snd m).
    Proof.
      unfold byzantine_message_prop in Hm.
      unfold can_emit in Hm.
      destruct m as (im, sm); simpl in *.
      destruct Hm as [(s, om) [l [s' [[Hs [Hom Hv]] Ht]]]].
      simpl in Hv. unfold vvalid in Hv. simpl in Hv.
      simpl in Ht. unfold vtransition in Ht. simpl in Ht.
      destruct l as [c|].
      - inversion Ht. subst s' im sm; clear Ht.
        split; try assumption. reflexivity.
      - destruct om as [m|]; inversion Ht.
    Qed.
    
    Global Instance lv_sent_capability:
      has_been_sent_capability X.
    Proof.
      apply (@has_been_sent_capability_from_stepwise _ X send_oracle _).
      split.
      - intros. intro contra.
        unfold send_oracle in contra.
        unfold Common.initial_state_prop in H. simpl in H.
        unfold initial_state_prop in H.
        destruct H as [c Heqs]. subst s.
        destruct (decide (fst m = index_self));[|intuition].
        rewrite get_history_all_bottom in contra.
        intuition.
      - intros.
        destruct H as [Hpr Htr].
        simpl in *.
        unfold vvalid in Hpr.
        unfold valid in Hpr. simpl in Hpr.
        destruct l eqn : eq_l.
        + inversion Htr.
          split; intros; simpl.
          * destruct (decide (msg = (index_self, s)));[left;f_equal;intuition|].
            right.
            unfold send_oracle in H.
            destruct (decide (fst msg = index_self)); [|intuition].
            rewrite history_disregards_cv in H.
            rewrite e in H.
            rewrite history_append in H.
            unfold send_oracle.
            rewrite decide_True by intuition.
            simpl in H.
            rewrite <- Is_true_iff_eq_true in H.
            apply orb_true_iff in H.
            2, 3 : apply protocol_prop_no_bottom; intuition.
            2 : intuition.
            destruct H.
            -- destruct (decide (snd msg = s)).
               ++ destruct msg. simpl in *. intuition congruence.
               ++ rewrite state_eqb_eq in H.
                  congruence.
            -- subst index_self. intuition.
          * destruct H.
            -- inversion H. 
               assert (fst msg = index_self) by (rewrite <- H3; simpl; intuition).
               unfold send_oracle.
               rewrite decide_True by intuition.
               rewrite history_disregards_cv.
               simpl.
               rewrite history_append. simpl.
               2, 3 : apply protocol_prop_no_bottom; intuition.
               2 : intuition.
               rewrite <- Is_true_iff_eq_true.
               apply orb_true_iff.
               left. apply state_eqb_eq; intuition.
            -- unfold send_oracle.
               unfold send_oracle in H.
               destruct (decide ((fst msg) = index_self)).
               ++ rewrite history_disregards_cv.
                  rewrite e.
                  rewrite history_append. simpl.
                  2, 3 : apply protocol_prop_no_bottom; intuition.
                  2 : intuition.
                  rewrite <- Is_true_iff_eq_true.
                  apply orb_true_iff. right. rewrite <- Is_true_iff_eq_true in H.
                  rewrite e in H. intuition.
               ++ intuition.
        + destruct im;[|intuition].
          split; intros.
          * right.
            unfold send_oracle in *.
            destruct (decide (fst msg = index_self));[|intuition].
            inversion Htr.
            rewrite <- H1 in H.
            rewrite <- history_oblivious in H.
            intuition.
            rewrite e. intuition.
          * destruct H;[inversion Htr; intuition congruence|].
            inversion Htr.
            unfold send_oracle in *.
            destruct (decide (fst msg = index_self)); [|intuition].
            rewrite <- history_oblivious.
            intuition.
            rewrite e. intuition.
    Qed.
    
    Global Instance lv_received_capability:
      has_been_received_capability X.
    Proof.
      apply (@has_been_received_capability_from_stepwise _ X receive_oracle _).
      split.
      - intros. intro contra.
        unfold receive_oracle in contra.
        unfold Common.initial_state_prop in H. simpl in H.
        unfold initial_state_prop in H.
        destruct H as [c Heqs]. subst s.
        destruct (decide (fst m = index_self));[intuition|].
        rewrite get_history_all_bottom in contra.
        intuition.
      - intros.
        destruct H as [Hpr Htr].
        simpl in *.
        unfold vvalid in Hpr.
        unfold valid in Hpr. simpl in Hpr.
        destruct l eqn : eq_l.
        + inversion Htr.
          split; intros; simpl.
          * right.
            unfold receive_oracle in *.
            destruct (decide (fst msg = index_self)); [intuition|].
            rewrite history_disregards_cv in H.
            rewrite <- history_oblivious in H by intuition.
            intuition.
          * destruct H;[intuition congruence|].
            unfold receive_oracle in *.
            destruct (decide (fst msg = index_self)); [intuition|].
            rewrite history_disregards_cv.
            rewrite <- history_oblivious by intuition.
            intuition.
        + split; intros; simpl.
          * destruct im;[|intuition].
            inversion Htr.
            rewrite <- H1 in H.
            unfold receive_oracle in *.
            destruct (decide (fst msg = index_self));[intuition|].
            destruct (decide (fst m = fst msg)).
            -- unfold receive_oracle in H.
               destruct (decide (snd m = snd msg)).
               ++ left. f_equal. destruct m; destruct msg. simpl in *. 
                  rewrite e. rewrite e0. intuition.
               ++ right. rewrite e in H.
                  rewrite history_append in H.
                  2 : apply protocol_prop_no_bottom; intuition.
                  2 : intuition.
                  2 : rewrite e in Hpr; intuition.
                  simpl in H.
                  rewrite <- Is_true_iff_eq_true in H.
                  apply orb_true_iff in H.
                  destruct H.
                  ** rewrite state_eqb_eq in H. intuition congruence.
                  ** intuition.
            -- right.
               rewrite <- history_oblivious in H by intuition.
               intuition.
          * destruct im;[|intuition].
            inversion Htr.
            unfold receive_oracle in *.
            destruct (decide (fst msg = index_self));[intuition congruence|].
            destruct H.
            -- inversion H.
               subst m. 
               rewrite history_append.
               2 : apply protocol_prop_no_bottom; intuition.
               2, 3 : intuition.
               simpl.
               rewrite <- Is_true_iff_eq_true.
               apply orb_true_iff.
               left. rewrite state_eqb_eq. intuition.
            -- destruct (decide (fst m = fst msg)).
               ++ rewrite e. rewrite history_append.
                  2 : apply protocol_prop_no_bottom; intuition.
                  2 : intuition.
                  2 : rewrite <- e; intuition.
                  simpl.
                  rewrite <- Is_true_iff_eq_true.
                  apply orb_true_iff.
                  right. rewrite Is_true_iff_eq_true. intuition.
               ++ rewrite <- history_oblivious by intuition.
                  intuition.
    Qed.

    Definition get_messages_from_history (s : state) (i : index) : set message :=
      List.map (pair i) (get_history s i).

    Definition get_sent_messages (s : state) : set message :=
      get_messages_from_history s index_self.

    Definition get_messages (s : state) : set message :=
      let all := List.map (get_messages_from_history s) index_listing in
      List.fold_right (@set_union message mdec) [] all.

    Definition get_received_messages (s : state) : set message :=
      set_diff mdec (get_messages s) (get_sent_messages s).

    Lemma get_iff_history
      (s : state)
      (m : message) :
      In m (get_messages_from_history s (fst m)) <-> In (snd m) (get_history s (fst m)).
    Proof.
      split.
      - intros.
        unfold get_messages_from_history in H.
        rewrite in_map_iff in H.
        destruct H as [x [Heq Hinx]].
        rewrite <- Heq.
        simpl.
        assumption.
      - intros.
        unfold get_messages_from_history.
        rewrite in_map_iff.
        exists (snd m).
        split.
        + rewrite surjective_pairing.
          reflexivity.
        + assumption.
    Qed.

    Lemma sent_set_equiv_send_oracle
      (s : state)
      (Hprotocol : protocol_state_prop preX s)
      (m : message) :
      send_oracle s m = true <-> In m (get_sent_messages s).
    Proof.
      split.
      - intros.
        unfold send_oracle in H.
        destruct (decide (fst m = index_self)).
        + unfold get_sent_messages.
          rewrite <- e.
          rewrite get_iff_history.
          rewrite existsb_exists in H.
          destruct H as [x [Hinx Heq]].
          rewrite state_eqb_eq in Heq.
          rewrite Heq.
          assumption.
        + discriminate H.
      - intros.
        unfold send_oracle.
        destruct (decide (fst m = index_self)).
        + unfold get_sent_messages in H.
          rewrite <- e in H.
          rewrite get_iff_history in H.
          rewrite existsb_exists.
          exists (snd m).
          split.
          * assumption.
          * rewrite state_eqb_eq.
            reflexivity.
        + unfold get_sent_messages in H.
          unfold get_messages_from_history in H.
          rewrite in_map_iff in H.
          destruct H as [x [Heq Hinx]].
          elim n.
          rewrite <- Heq.
          reflexivity.
    Qed.

    Lemma message_in_unique_history
      (s : state)
      (m : message)
      (i : index)
      (Hin : In m (get_messages_from_history s i)) :
      i = (fst m).
    Proof.
      unfold get_messages_from_history in Hin.
      rewrite in_map_iff in Hin.
      destruct Hin as [x [Heq Hinx]].
      rewrite <- Heq.
      simpl.
      reflexivity.
    Qed.

    Lemma in_history_equiv_in_union
      (s : state)
      (m : message) :
      In m (get_messages s) <-> In m (get_messages_from_history s (fst m)).
    Proof.
      remember (map (get_messages_from_history s) index_listing) as haystack.
      remember (get_messages_from_history s (fst m)) as needle.
      split.
      - intros.
        unfold get_messages in H.
        specialize (union_fold haystack m).
        intros.
        destruct H0 as [Hleft _].
        rewrite <- Heqhaystack in H.
        specialize (Hleft H).
        destruct Hleft as [needle' [Hin1 Hin2]].
        assert (needle = needle'). {
          assert (exists (i : index), needle' = (get_messages_from_history s i)). {
            rewrite Heqhaystack in Hin2.
            rewrite in_map_iff in Hin2.
            destruct Hin2 as [x [Hneed _]].
            exists x.
            symmetry.
            assumption.
          }
          destruct H0 as [i Heq].
          specialize (message_in_unique_history s m i).
          intros.
          rewrite Heq in Hin1.
          specialize (H0 Hin1).
          rewrite H0 in Heq.
          rewrite Heq.
          rewrite Heqneedle.
          reflexivity.
        }

        rewrite H0.
        assumption.
      - intros.
        unfold get_messages.

        specialize (union_fold haystack m).
        intros.
        destruct H0 as [_ Hright].
        rewrite Heqhaystack in Hright.
        apply Hright.
        exists (get_messages_from_history s (fst m)).
        split.
        + rewrite <- Heqneedle.
          assumption.
        + rewrite in_map_iff.
          exists (fst m).
          split.
          * reflexivity.
          * apply ((proj2 Hfinite) (fst m)).
    Qed.

    Lemma received_set_equiv_receive_oracle
      (s : state)
      (Hprotocol : protocol_state_prop preX s)
      (m : message) :
      receive_oracle s m = true <-> In m (get_received_messages s).
    Proof.
      split.
      - intros.
        unfold receive_oracle in H.
        destruct (decide (fst m = index_self)).
        + discriminate H.
        + rewrite existsb_exists in H.
          destruct H as [x [Hinx Heq]].
          unfold get_received_messages.
          specialize set_diff_intro.
          intros.
          specialize (H message mdec m (get_messages s) (get_sent_messages s)).
          apply H.
          * rewrite state_eqb_eq in Heq.
            apply in_history_equiv_in_union.
            rewrite get_iff_history.
            rewrite Heq.
            assumption.
          * intros contra.
            specialize (message_in_unique_history s m index_self).
            intros.
            rewrite state_eqb_eq in Heq.
            unfold get_sent_messages in contra.
            specialize (H0 contra).
            elim n.
            symmetry.
            assumption.
       - intros.
         unfold receive_oracle.
         destruct (decide (fst m = index_self)).
         + unfold get_received_messages in H.
           rewrite set_diff_iff in H.
           rewrite in_history_equiv_in_union in H.
           unfold get_sent_messages in H.
           rewrite e in H.
           intuition.
         + unfold get_received_messages in H.
           rewrite set_diff_iff in H.
           destruct H as [Hin Hnot_in].
           rewrite existsb_exists.
           exists (snd m).
           split.
           * rewrite in_history_equiv_in_union in Hin.
             rewrite get_iff_history in Hin.
             assumption.
           * rewrite state_eqb_eq.
             reflexivity.
      Qed.

    Fixpoint get_observations (target : index) (d : nat) (s : state) : set state :=
      match s with
      | Bottom => []
      | _ => match d with
             | 0 => set_remove decide_eq Bottom [project s target]
             | S n => let children := List.map (@project index index_listing _ s) index_listing in
             let children_res := List.map (get_observations target n) children in
             set_remove decide_eq Bottom
             (set_union decide_eq (List.fold_right (set_union decide_eq) [] children_res) [project s target])
             end
      end.

    Definition shallow_observations (s : state) (target : index) :=
      get_observations target 1 s.

    Definition full_observations (s : state) (target : index) :=
      get_observations target (depth s) s.

    Lemma get_observations_depth_redundancy
      (target : index)
      (d : nat)
      (s : state)
      (Hineq : d >= depth s) :
      get_observations target d s = get_observations target (depth s) s.
   Proof.
    remember (depth s) as dpth.
    generalize dependent s.
    generalize dependent d.
    induction dpth using (well_founded_induction lt_wf).
    intros.
    unfold get_observations at 1.
    destruct s.
    - unfold depth in Heqdpth.
      rewrite Heqdpth.
      destruct d.
      + reflexivity.
      + simpl in *.
        reflexivity.
     - unfold get_observations.
       destruct dpth eqn : eq_dpth.
       + destruct d eqn: eq_d.
         * reflexivity.
         * symmetry in Heqdpth.
           apply depth_zero_bottom in Heqdpth.
           discriminate Heqdpth.
       + destruct d.
         lia.
         simpl.
         f_equal.
         f_equal.
         f_equal.
         apply map_ext_in.
         intros.
         rewrite in_map_iff in H0.
         destruct H0 as [j [Heq Hin]].
         assert (depth a < S n). {
           rewrite Heqdpth.
           specialize (@depth_parent_child index index_listing Hfinite decide_eq is b j).
           intros.
           unfold project in Heq.
           replace (@project_indexed index index_listing _ index_listing is j)
           with a in H0.
           lia.
         }

        assert (d >= depth a). {
          lia.
        }

         assert (get_observations target (depth a) a = get_observations target n a). {
          symmetry.
          apply H.
          lia.
          lia.
          reflexivity.
         }

         specialize (H (depth a) H0 d H1 a eq_refl).
         rewrite H2 in H.
         intuition.
   Qed.

    Lemma get_observations_nodup
      (target : index)
      (s : state) :
      (NoDup (get_observations target (depth s) s)).
    Proof.
      remember(depth s) as d.
      generalize dependent s.
       induction d using (well_founded_induction lt_wf).
       unfold get_observations.
       destruct d.
       - intros.
          simpl.
         destruct (project s target).
         + rewrite decide_True; auto.
           symmetry in Heqd.
           apply depth_zero_bottom in Heqd.
           rewrite Heqd.
           apply NoDup_nil.
         + rewrite decide_False.
           symmetry in Heqd.
           apply depth_zero_bottom in Heqd.
           rewrite Heqd.
           apply NoDup_nil.
           intros contra.
           discriminate contra.
       - intros.
         simpl.
         destruct s.
         simpl in Heqd. discriminate Heqd.
         apply set_remove_nodup.
         apply set_add_nodup.
         specialize (@set_union_iterated_nodup (@state index index_listing) decide_eq).
         intros.
         specialize (H0 (map
        ((fix get_observations (target0 : index) (d0 : nat) (s : state) {struct d0} :
              set state :=
            match s with
            | Bottom => []
            | Something _ _ =>
                match d0 with
                | 0 =>
                    if decide (Bottom = (project s target0))
                    then []
                    else project s target0 :: empty_set state
                | S n =>
                    set_remove decide_eq Bottom
                      (set_add decide_eq (project s target0)
                         (fold_right (set_union decide_eq) []
                            (map (get_observations target0 n) (map (project s) index_listing))))
                end
            end) target d) (map (project (Something b is)) index_listing))).
        apply H0.
        intros.
        rewrite in_map_iff in H1.
        destruct H1 as [x [Hleft Hright]].
        assert (depth x < S d). {
          rewrite Heqd.
          apply in_map_iff in Hright.
          destruct Hright as [i [Hi _]].
          rewrite <- Hi.
          specialize (@depth_parent_child index index_listing Hfinite decide_eq is b i).
          intros.
          unfold project.
          intuition.
        }
        rewrite <- Hleft.
        specialize H.
        rewrite get_observations_depth_redundancy.
        specialize (H (depth x)).
        specialize (H H1).
        specialize (H x eq_refl).
        assumption.
        lia.
 Qed.

  Lemma no_bottom_in_observations
    (s s': state)
    (target : index)
    (Hins' : In s' (get_observations target (depth s) s)) :
    s' <> Bottom.
  Proof.
   unfold get_observations in Hins'.
   destruct s.
   - simpl in *.
     intuition.
   - simpl in *.
     destruct (depth (Something b is)) eqn : eq_d'.
     + apply depth_zero_bottom in eq_d'.
       discriminate eq_d'.
     + simpl in *.
       apply set_remove_2 in Hins'.
       assumption.
       clear Hins'.
       apply set_add_nodup.
       apply (set_union_iterated_nodup).
       intros.
       rewrite in_map_iff in H.
       destruct H as [child [Heq_child Hin_child]].
       rewrite in_map_iff in Hin_child.
       destruct Hin_child as [i [Heq_project _]].
       rewrite <- Heq_child.
       specialize (get_observations_nodup target child).
       intros.
       rewrite get_observations_depth_redundancy.
       apply H.
       specialize (@depth_parent_child index index_listing Hfinite idec is b i) as Hparent_child.
       rewrite eq_d' in Hparent_child.
       rewrite <- Heq_project.
       unfold project.
       lia.
  Qed.

    Lemma observations_in_project
      (s : state)
      (target i : index)
      : incl (full_observations (project s i) target) (full_observations s target).
  Proof.
    unfold incl.
    intros.
    unfold full_observations.
    unfold get_observations at 1.
    destruct s eqn : eq_s.
    - simpl in *.
      assumption.
    - destruct (depth (Something b is)) eqn : eq_depth.
      + apply depth_zero_bottom in eq_depth.
        discriminate eq_depth.
      + specialize (@set_union_in_iterated (@state index index_listing) state_eq_dec).
        intros.
        specialize (H0 (map (get_observations target n) (map (project (Something b is)) index_listing))).
        specialize (H0 a).
        destruct H0 as [_ Hneed].
        assert (a <> Bottom). {
          specialize (no_bottom_in_observations (project (Something b is) i) a target).
          intros.
          apply H0.
          unfold full_observations in H.
          assumption.
        }
        apply set_remove_3.
        apply set_union_intro1.
        apply Hneed.
        rewrite Exists_exists.
        exists (get_observations target n (project (Something b is) i)).
        split.
        rewrite in_map_iff.
        exists (project (Something b is) i).
        split.
        reflexivity.
        rewrite in_map_iff.
        exists i.
        split.
        reflexivity.
        apply ((proj2 Hfinite) i).
        unfold full_observations in H.
        rewrite get_observations_depth_redundancy.
        assumption.
        specialize (@depth_parent_child index index_listing Hfinite idec is b i).
        intros.
        unfold project.
        lia.
        assumption.
  Qed.

    Lemma observations_disregards_cv
      (s : vstate X)
      (cv : bool)
      (target : index)
      : full_observations (update_consensus s cv) target
      = full_observations s target.
    Proof.
      unfold full_observations.
      unfold get_observations.
      rewrite <- depth_consensus_clean with (value := cv).
      destruct (depth s) eqn : eq_d.
      - rewrite <- update_consensus_clean.
        destruct s.
        simpl. reflexivity.
        simpl. reflexivity.
      - rewrite <- update_consensus_clean.
        assert (map (project (update_consensus s cv)) index_listing = map (project s) index_listing). {
          apply map_ext_in.
          intros.
          symmetry.
          apply update_consensus_clean.
        }
        rewrite H.
        destruct s.
        simpl.
        reflexivity.
        simpl.
        reflexivity.
    Qed.

    Lemma observations_update_eq
      (s s' : vstate X)
      (Hsnot : s <> Bottom)
      (Hs'not : s' <> Bottom)
      (target : index)
      (Hvalid : project s' target = project s target)
      : set_eq
        (full_observations (update_state s s' target) target)
        (set_add decide_eq s'
          (set_union decide_eq
            (full_observations s target)
            (full_observations s' target)
          )
        ).
    Proof.
     unfold set_eq.
     split; unfold incl; intros.
     - destruct (decide (a = s')).
       + apply set_add_intro2.
         assumption.
       + apply set_add_intro1.
         unfold full_observations in H.
         unfold get_observations in H.
         destruct (update_state s s' target) eqn : eq_up.
         * simpl in *.
           intuition.
         * destruct (depth (Something b is)) eqn : eq_d.
           apply depth_zero_bottom in eq_d.
           discriminate eq_d.
           apply set_remove_1 in H.
           assert (project (Something b is) target = s'). {
             rewrite <- eq_up.
             specialize (@project_same index index_listing Hfinite decide_eq s s' target).
             intros.
             apply H0.
             assumption.
           }
           rewrite H0 in H.
           apply set_union_elim in H.
           simpl in H.
           destruct H.
           specialize (@set_union_in_iterated (@state index index_listing) decide_eq).
           intros.
           specialize (H1 (map
            ((fix get_observations (target : index) (d : nat) (s : state) {struct d} :
                  set state :=
                match s with
                | Bottom => []
                | Something _ _ =>
                    match d with
                    | 0 =>
                        if decide (Bottom = (project s target))
                        then []
                        else project s target :: empty_set state
                    | S n =>
                        set_remove decide_eq Bottom
                          (set_add decide_eq (project s target)
                             (fold_right (set_union decide_eq) []
                                (map (get_observations target n) (map (project s) index_listing))))
                    end
                end) target n0) (map (project (Something b is)) index_listing))).
            specialize (H1 a).
            unfold ListSet.set_In in H.
            destruct H1 as [Hneed _].
            specialize (Hneed H).
            rewrite Exists_exists in Hneed.
            destruct Hneed as [child_result [Hin1 Hina]].
            rewrite in_map_iff in Hin1.
            destruct Hin1 as [child [Ha Hb]].
            rewrite in_map_iff in Hb.
            destruct Hb as [j [Hproject _]].
            specialize (@depth_parent_child index index_listing Hfinite idec is b j).
            intros.
            assert (n0 >= depth (child)). {
              rewrite eq_d in H1.
              rewrite <- Hproject.
              unfold project.
              lia.
            }
            destruct (decide (j = target)).
            rewrite e in Hproject.
            rewrite H0 in Hproject.
            rewrite <- Hproject in Ha.
            unfold ListSet.set_In.
            apply set_union_intro2.
            unfold full_observations.
            rewrite <- get_observations_depth_redundancy with (d := n0).
            rewrite <- Ha in Hina.
            intuition.
            rewrite Hproject.
            assumption.
            apply set_union_intro1.

            assert (project (Something b is) j = project s j). {
              specialize (@project_different index index_listing Hfinite idec s s' j target).
              intros.
              rewrite <- eq_up.
              apply H3.
              assumption.
              assumption.
            }

            specialize (observations_in_project s target j).
            intros.
            rewrite Hproject in H3.
            rewrite H3 in Ha.
            unfold incl in H4.
            specialize (H4 a).
            apply H4.
            rewrite <- Ha in Hina.
            unfold full_observations.
            rewrite <- get_observations_depth_redundancy with (d := n0).
            assumption.
            rewrite <- H3.
            assumption.
            destruct H.
            elim n.
            symmetry.
            assumption.
            exfalso.
            assumption.
        - remember (update_state s s' target) as u.
          assert (project u target = s'). {
            specialize (@project_same index index_listing Hfinite idec s s' target).
            intros.
            rewrite <- Hequ in H0.
            apply H0.
            assumption.
          }
          apply set_add_elim in H.
          destruct (decide (a = s')).
          (* a = s' *)
          + unfold full_observations.
            unfold get_observations.
            destruct u.
            simpl in *.
            intuition.
            destruct (depth (Something b is)) eqn: eq_d.
            apply depth_zero_bottom in eq_d.
            discriminate eq_d.
            apply set_remove_3.
            apply set_union_intro.
            right.
            rewrite H0.
            rewrite e.
            simpl.
            intuition.
            rewrite e.
            assumption.
          + unfold ListSet.set_In in H.
            destruct H.
            elim n.
            assumption.
            apply set_union_elim in H.
            destruct H.
            * (* In a (get_observations s)). *)
              unfold full_observations in H.
              assert (a <> Bottom) as Hanot_bottom. {
                apply no_bottom_in_observations in H.
                assumption.
              }
              unfold get_observations in H.
              destruct s.
              elim Hsnot.
              reflexivity.
              destruct (depth (Something b is)) eqn : eq_d.
              apply depth_zero_bottom in eq_d.
              discriminate eq_d.
              apply set_remove_1 in H.
              apply set_union_elim in H.
              destruct H.
              apply set_union_in_iterated in H.
              rewrite Exists_exists in H.
              destruct H as [child_result [Heq_child_result Hin_a]].
              rewrite in_map_iff in Heq_child_result.
              destruct Heq_child_result as [child [Heq_child Hin_child]].
              rewrite in_map_iff in Hin_child.
              destruct Hin_child as [i [Hproject _]].
              destruct (decide (i = target)).
              { (* found originally in target projection *)
                rewrite e in Hproject.
                rewrite <- Hvalid in Hproject.
                specialize (observations_in_project u target target).
                intros.
                unfold incl in H.
                specialize (H a).
                apply H.
                clear H.
                rewrite H0.
                specialize (observations_in_project s' target target).
                intros.
                unfold incl in H.
                specialize (H a).
                apply H.
                rewrite Hproject.
                rewrite get_observations_depth_redundancy in Heq_child.
                rewrite <- Heq_child in Hin_a.
                unfold full_observations.
                assumption.
                specialize (@depth_parent_child index index_listing Hfinite idec is b target) as Hdpc.
                rewrite eq_d in Hdpc.
                rewrite <- Hproject.
                simpl in Hvalid.
                rewrite Hvalid.
                lia.
              }
              { (* found originally in different projection *)
               assert (n0 >= depth child) as Hn0child. {
                   specialize (@depth_parent_child index index_listing Hfinite idec is b i) as Hdpc.
                   simpl in Hproject.
                   rewrite Hproject in Hdpc.
                   lia.
                }
                unfold full_observations.
                unfold get_observations.
                destruct u.
                discriminate Hequ.
                destruct (depth (Something b0 is0)) eqn : eq_du.
                apply depth_zero_bottom in eq_du.
                discriminate eq_du.
                apply set_remove_3.
                apply set_union_intro.
                left.
                assert (project (Something b is) i = project (Something b0 is0) i) as Hsame. {
                  specialize (@project_different index index_listing Hfinite idec).
                  intros.
                  specialize (H (Something b is) s' i target).
                  rewrite Hequ.
                  symmetry.
                  apply H.
                  assumption.
                  intros contra.
                  discriminate contra.
                }

                apply set_union_in_iterated.
                rewrite Exists_exists.
                exists child_result.
                rewrite in_map_iff.
                split.
                exists child.
                split.
                rewrite get_observations_depth_redundancy.
                rewrite get_observations_depth_redundancy in Heq_child.
                assumption.
                assumption.

                specialize (@depth_parent_child index index_listing Hfinite idec is0 b0 i) as Hdpc'.
                simpl in H0.

                rewrite Hsame in Hproject.
                rewrite <- Hproject.
                unfold project.
                lia.
                rewrite in_map_iff.
                exists i.
                split.
                rewrite Hsame in Hproject.
                assumption.
                apply ((proj2 Hfinite) i).
                assumption.
                rewrite get_observations_depth_redundancy in Heq_child.
                rewrite <- Heq_child in Hin_a.
                apply no_bottom_in_observations in Hin_a.
                assumption.
                assumption.
                }
                (* a = project s target *)
                simpl in H.
                simpl in Hvalid.
                rewrite <- Hvalid in H.
                destruct H.
                unfold full_observations.
                unfold get_observations.
                destruct u.
                simpl in *.
                discriminate Hequ.
                destruct (depth (Something b0 is0)) eqn : eq_du.
                apply depth_zero_bottom in eq_du.
                discriminate eq_du.
                apply set_remove_3.
                apply set_union_intro.
                left.
                apply set_union_in_iterated.
                rewrite Exists_exists.
                exists (full_observations s' target).
                rewrite in_map_iff.
                split.
                exists s'.
                rewrite get_observations_depth_redundancy.
                split.
                unfold full_observations.
                reflexivity.
                rewrite in_map_iff.
                exists target.
                split.
                assumption.
                apply ((proj2 Hfinite) target).
                specialize (@depth_parent_child index index_listing Hfinite idec is0 b0 target).
                intros.
                simpl in H0.
                rewrite <- H0.
                lia.
                rewrite <- H.
                unfold full_observations.
                unfold get_observations.
                destruct s'.
                elim Hs'not.
                reflexivity.
                destruct (depth (Something b1 is1)) eqn : eq_d1.
                apply depth_zero_bottom in eq_d1.
                discriminate eq_d1.
                apply set_remove_3.
                apply set_union_intro.
                right.
                simpl.
                intuition.
                rewrite H.
                assumption.
                assumption.
                exfalso.
                assumption.
            * (* In a (get_observation s') *)
              specialize (observations_in_project u target target).
              intros.
              unfold incl in H1.
              specialize (H1 a).
              apply H1.
              rewrite <- H0 in H.
              assumption.
    Qed.

    Lemma unfold_full_observations
      (s s' : state)
      (Hsnot_bottom : s <> Bottom)
      (Hs'not_bottom : s' <> Bottom)
      (target : index) :
      In s' (full_observations s target) <->
      project s target = s' \/
      (exists (i : index), (In s' (full_observations (project s i) target))).
    Proof.
      split.
      - intros.
        unfold full_observations in H.
        unfold get_observations in H.
        destruct s.
        simpl in *.
        exfalso.
        assumption.
        destruct (depth (Something b is)) eqn : eq_d.
        apply depth_zero_bottom in eq_d.
        discriminate eq_d.
        apply set_remove_1 in H.
        apply set_union_elim in H.
        destruct H.
        + apply set_union_in_iterated in H.
          rewrite Exists_exists in H.
          destruct H as [child_res [Heq_child_res Hin_child_res]].
          rewrite in_map_iff in Heq_child_res.
          destruct Heq_child_res as [child [Heq_child Hin_child]].
          rewrite in_map_iff in Hin_child.
          destruct Hin_child as [i [Hproject Hini]].
          right.
          exists i.
          rewrite get_observations_depth_redundancy in Heq_child.
          rewrite <- Heq_child in Hin_child_res.
          rewrite <- Hproject in Hin_child_res.
          assumption.
          specialize (@depth_parent_child index index_listing Hfinite idec is b i).
          intros Hdpc.
          rewrite <- Hproject.
          unfold project.
          lia.
        + simpl in H.
          left.
          intuition.
      - intros.
        destruct H.
        unfold full_observations.
        unfold get_observations.
        destruct s.
        elim Hsnot_bottom.
        reflexivity.
        destruct (depth (Something b is)) eqn : eq_d.
        apply depth_zero_bottom in eq_d.
        discriminate eq_d.
        apply set_remove_3.
        apply set_union_intro.
        right.
        simpl.
        intuition.
        assumption.
        unfold full_observations.
        unfold get_observations.
        destruct s.
        elim Hsnot_bottom.
        reflexivity.
        destruct (depth (Something b is)) eqn : eq_d.
        apply depth_zero_bottom in eq_d.
        discriminate eq_d.
        apply set_remove_3.
        apply set_union_intro.
        left.
        apply set_union_in_iterated.
        rewrite Exists_exists.
        destruct H as [i Hin_i].
        exists (full_observations (project (Something b is) i) target).
        split.
        rewrite in_map_iff.
        exists (project (Something b is) i).
        split.
        rewrite get_observations_depth_redundancy.
        unfold full_observations.
        reflexivity.
        specialize (@depth_parent_child index index_listing Hfinite idec is b i) as Hdpc.
        unfold project.
        lia.
        rewrite in_map_iff.
        exists i.
        split.
        reflexivity.
        apply ((proj2 Hfinite) i).
        assumption.
        assumption.
    Qed.

    Lemma observations_update_neq
      (s s' : vstate X)
      (Hsnot : s <> Bottom)
      (Hs'not : s' <> Bottom)
      (target i : index)
      (Hvalid : project s' i = project s i)
      (Hi : i <> target)
      : set_eq
        (full_observations (update_state s s' i) target)
        (set_union decide_eq
          (full_observations s target)
          (full_observations s' target)
        ).
    Proof.
      remember (update_state s s' i) as u.

      assert (Hproj_ui : project u i = s'). {
        rewrite Hequ.
        apply (@project_same index index_listing Hfinite).
        assumption.
      }

      assert (Hproj_utarget : project u target = project s target). {
        rewrite Hequ.
        apply (@project_different index index_listing Hfinite).
        intuition.
        assumption.
      }

            assert (Hu_not_bottom : u <> Bottom). {
         destruct u.
          simpl in *.
          elim Hs'not.
          intuition.
          intros contra.
          discriminate contra.
      }

      split;
      unfold incl;
      intros.
      - assert (Ha : a <> Bottom). {
          apply no_bottom_in_observations in H.
          assumption.
        }
        apply unfold_full_observations in H.
        destruct H.
        apply set_union_intro.
        left.
        apply unfold_full_observations.
        assumption.
        assumption.
        left.
        rewrite <- Hproj_utarget.
        assumption.
        destruct H as [j Hin_j].
        apply set_union_intro.
        destruct (decide (i = j)).
        + right.
          rewrite e in Hproj_ui.
          rewrite Hproj_ui in Hin_j.
          assumption.
        + left.
          apply unfold_full_observations.
          assumption.
          assumption.
          right.
          exists j.
          assert (Hsame_uj : (project u j) = (project s j)). {
            rewrite Hequ.
            apply (@project_different index index_listing Hfinite).
            intuition.
            assumption.
          }
          rewrite <- Hsame_uj.
          assumption.
        + assumption.
        + assumption.
      - apply set_union_elim in H.
        assert (Ha : a <> Bottom). {
          destruct H;
          apply no_bottom_in_observations in H;
          assumption.
        }
        destruct H.
        apply unfold_full_observations in H.
        destruct H.
        apply unfold_full_observations.
        assumption.
        assumption.
        left.
        rewrite Hproj_utarget.
        assumption.
        destruct H as [j Hin_j].
        apply unfold_full_observations.
        assumption.
        assumption.
        right.
        destruct (decide (i = j)).
        exists i.
        rewrite Hproj_ui.
        apply unfold_full_observations.
        assumption.
        assumption.
        right.
        exists i.
        rewrite Hvalid.
        rewrite <- e in Hin_j.
        assumption.
        exists j.
        assert (Hproj_uj : project u j = project s j). {
          rewrite Hequ.
          apply (@project_different index index_listing Hfinite).
          intuition.
          assumption.
        }
        rewrite Hproj_uj.
        assumption.
        assumption.
        assumption.
        apply unfold_full_observations.
        assumption.
        assumption.
        right.
        exists i.
        rewrite Hproj_ui.
        assumption.
    Qed.
End Equivocation.
