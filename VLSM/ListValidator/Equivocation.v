Require Import Bool List ListSet Reals FinFun RelationClasses Relations Relations_1 Sorting.
Require Import Lia.
Import ListNotations.
From CasperCBC
Require Import
  Lib.Preamble
  Lib.ListExtras
  Lib.ListSetExtras
  Lib.SortedLists
  Lib.SumWeights
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
  
  Local Notation get_history' := (@get_history index index_listing idec).
  Local Notation last_sent' := (@last_sent index index_self index_listing idec).
  
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
        rec_history s i d = rec_history s i (@depth index index_listing s).
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
             get_history' s i = get_history' (update_state s news j) i.
    Proof.
      intros.
      unfold get_history'.
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
          get_history' (update_consensus s cv) i = get_history' s i.
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
      get_history' (update_state s news i) i = (news :: get_history' s i).
    Proof.
      intros.
      unfold update_state.
      destruct s eqn : s_eq.
      - elim Hno_bottom_s. reflexivity.
      - unfold get_history'.
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
      (Hin : get_history' s1 i = pref ++ [s2] ++ suff) :
      suff = get_history' s2 i.
    Proof.
      generalize dependent s1.
      generalize dependent s2.
      generalize dependent suff.
      generalize dependent pref.
      induction pref.
      - intros. simpl in *.
        unfold get_history' in Hin.
        destruct s1.
        + discriminate Hin.
        + unfold rec_history in Hin.
          destruct (last_recorded index_listing is i).
          * simpl in Hin. discriminate Hin.
          * destruct (depth (Something b0 is0)) eqn : eq_d.
            discriminate Hin.
            inversion Hin.
            unfold get_history'.
            rewrite depth_redundancy.
            reflexivity.
            specialize (@depth_parent_child _ _ Hfinite _ is0 b0 i).
            intros.
            rewrite eq_d in H.
            unfold last_recorded.
            lia.
      - intros.
        unfold get_history' in Hin.
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
            unfold get_history'.
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
      : get_history' s i = [].
    Proof.
      destruct s; try reflexivity; simpl in *.
      unfold last_recorded. rewrite Hnbp. reflexivity.
    Qed.

    Lemma unfold_history_cons
      (s : state)
      (i : index)
      (Hnbp : project s i <> Bottom)
      : get_history' s i = project s i :: get_history' (project s i) i.
    Proof.
      assert (Hproject : exists suff, get_history' s i = project s i :: suff).
      { unfold get_history'. unfold project. destruct s; try (elim Hnbp; reflexivity).
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
      (Hcons : get_history' s i = s1 :: ls)
      : s1 = project s i
      /\ ls = get_history' (project s i) i.
    Proof.
      destruct (project s i) eqn : eq_project.
      - unfold get_history' in Hcons.
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
      (history1 := get_history' s1 i)
      (history2 := get_history' s2 i) :
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

        assert (get_history' s i = l). {
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
      : ~ In s (get_history' s i).
    Proof.
      intro Hs. apply in_split in Hs.
      destruct Hs as [pref [suff Hs]].
      specialize (unfold_history s s i pref suff Hs) as Hsuff.
      subst suff.
      assert (Hl : length(get_history' s i) = length(pref ++ s :: get_history' s i))
        by (f_equal; assumption).
      rewrite app_length in Hl. simpl in Hl. lia.
    Qed.

     Definition state_lt'
     (i : index)
     (s1 s2 : (@state index index_listing))
     : Prop
     := In s1 (get_history s2 i).
     
     Definition state_ltb'
      (i : index)
      (s1 s2 : (@state index index_listing))
      : bool
      := inb decide_eq s1 (get_history s2 i).
      
    Definition state_lt_ext
      (i : index)
      (s1 s2 : (@state index index_listing)) :=
      (s1 = Bottom /\ s2 <> Bottom) \/
      state_lt' i s1 s2.
      
    Lemma state_lt'_dec 
      (i : index)
      : RelDecision (state_lt' i).
    Proof.
      unfold RelDecision; intros.
      unfold Decision.
      destruct (state_ltb' i x y) eqn : eqb; 
      (unfold state_lt'; unfold state_ltb' in eqb).
      - left. apply in_correct in eqb. assumption.
      - right. intros contra. 
        apply in_correct in contra. 
        rewrite eqb in contra.
        discriminate contra. 
    Qed.
    
    Existing Instance state_lt'_dec.
    
    Lemma state_lt'_trans
      (i : index)
      (s1 s2 s3 : state)
      (Hlt : state_lt' i s1 s2 /\ state_lt' i s2 s3) :
      state_lt' i s1 s3.
    Proof.
      destruct Hlt as [Hlt1 Hlt2].
      unfold state_lt' in Hlt1, Hlt2.
      apply in_split in Hlt2.
      destruct Hlt2 as [pref [suff Heq]].
      apply unfold_history in Heq as Heq'.
      unfold state_lt'.
      rewrite Heq.
      rewrite Heq'.
      apply in_app_iff.
      right.
      apply in_cons.
      assumption.
    Qed.
    
    Lemma state_lt'_antisymmetric
      (i : index)
      (s1 s2 : (@state index index_listing)) :
      state_lt' i s1 s2 -> ~ state_lt' i s2 s1.
     Proof.
      intro H.
      unfold state_lt' in *.
      intros contra.
      apply in_split in H.
      destruct H as [left [right Heq]].
      apply unfold_history in Heq as Heq'.
      rewrite Heq' in Heq.
      apply in_split in contra.
      destruct contra as [left' [right' Heq_contra]].
      rewrite Heq_contra in Heq.
      specialize (history_no_self_reference s2 i) as Hnsr.
      rewrite Heq in Hnsr.
      contradict Hnsr.
      apply in_app_iff. right.
      simpl. right.
      apply in_app_iff. right.
      intuition.
     Qed.
    
    Lemma state_lt_ext_dec 
      (i : index)
      : RelDecision (state_lt_ext i).
    Proof.
      unfold RelDecision; intros.
      unfold Decision.
      unfold state_lt_ext.
      destruct x eqn : eq_x; destruct y eqn : eq_y; simpl.
      - right. intros contra. destruct contra;[intuition congruence|].
        unfold state_lt' in H. simpl in H. intuition.
      - left. left. intuition congruence.
      - right. intros contra. 
        destruct contra;[intuition|].
        unfold state_lt' in H. simpl in H. intuition.
      - destruct (decide (state_lt' i x y)); subst x; subst y.
        * left. right. intuition.
        * right. intros contra. destruct contra;[intuition congruence|intuition]. 
    Qed.
    
    Lemma state_lt_ext_antisymmetric
     (i : index)
     (s1 s2 : (@state index index_listing)) :
     state_lt_ext i s1 s2 -> ~ state_lt_ext i s2 s1.
    Proof.
      intros H.
      unfold state_lt_ext in *.
      destruct H.
      - intros contra.
        destruct contra;[intuition|].
        destruct H as [Hs1 Hs2]. subst s1.
        unfold state_lt' in H0. intuition.
      - intros contra.
        destruct contra.
        + destruct H0 as [H1 H2]. subst s2.
          unfold state_lt' in H. intuition.
        + apply state_lt'_antisymmetric in H.
          intuition.
    Qed.
    
    Lemma state_lt_ext_tran
      (i : index)
      (s1 s2 s3 : state)
      (H12 : state_lt_ext i s1 s2)
      (H23 : state_lt_ext i s2 s3)
      : state_lt_ext i s1 s3.
    Proof.
      unfold state_lt_ext in H12, H23.
      destruct H12; destruct H23.
      - intuition congruence.
      - unfold state_lt_ext.
        left. split;[intuition|].
        unfold state_lt' in H0.
        destruct s3;[simpl in H0;intuition|].
        congruence.
      - unfold state_lt' in H. 
        destruct H0 as [H0 _]. rewrite H0 in H. 
        simpl in H. intuition. 
      - unfold state_lt_ext. right.
        apply state_lt'_trans with (s2 := s2).
        intuition.
    Qed.
    
    Lemma state_lt_ext_proj
      (i : index)
      (s1 s2 : state) :
      state_lt_ext i s1 (project s2 i) ->
      state_lt_ext i s1 s2.
    Proof.
      intros.
      unfold state_lt_ext in *.
      destruct H.
      - left. split;[intuition|].
        destruct s2. simpl in H. intuition congruence. congruence.
      - right. unfold state_lt' in *.
        destruct (project s2 i) eqn : eq_p.
        + simpl in H. intuition.
        + rewrite unfold_history_cons by (intuition congruence).
          simpl. right. rewrite eq_p. intuition.
    Qed.

    Lemma projection_in_history
      (s : state)
      (news : state)
      (i : index)
      (Hnot_bottom : news <> Bottom)
      (Hproject : project s i = news) :
      In news (get_history' s i).
    Proof.
      intros.
      unfold get_history'.
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
    
    Lemma non_empty_history_nb_project
      (s so : state)
      (i : index)
      (Hin : In so (get_history' s i)) :
      project s i <> Bottom.
    Proof.
      unfold get_history' in Hin.
      destruct s.
      - intuition.
      - unfold last_recorded in Hin.
        unfold rec_history in Hin.
        unfold project.
        destruct (project_indexed index_listing is i).
        + simpl in Hin. intuition.
        + congruence.
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
      (s s': (@state index index_listing))
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
          * unfold get_history' in Heql.
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
      (Hin : In s' (get_history' s i)) :
      s' <> Bottom.
    Proof.
      unfold get_history' in Hin.
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
      : get_history' (Something cv all_bottom) i = [].
    Proof.
      unfold get_history'.
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
    Defined.
    
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
    Defined.
    
    Lemma bottom_project_empty_history
      (s : state)
      (i : index)
      (Hb : project s i = Bottom) : 
      get_history' s i = [].
    Proof.
      unfold get_history'.
      destruct s.
      - reflexivity.
      - unfold project in Hb.
        unfold last_recorded.
        rewrite Hb.
        simpl.
        reflexivity.
    Qed.

    Lemma eq_history_eq_project
      (s s' : state)
      (i : index) :
      get_history' s i = get_history' s' i <->
      project s i = @project index index_listing idec s' i.
    Proof.
      destruct (project s i) eqn : eq_ps; destruct (project s' i) eqn : eq_ps'; split; intros.
      - reflexivity.
      - apply bottom_project_empty_history in eq_ps.
        apply bottom_project_empty_history in eq_ps'.
        rewrite eq_ps. rewrite eq_ps'. reflexivity.
      - apply bottom_project_empty_history in eq_ps.
        rewrite eq_ps in H.
        specialize (unfold_history_cons s' i). intros.
        spec H0. intros contra. rewrite eq_ps' in contra. discriminate contra.
        rewrite H0 in H. discriminate H.
      - discriminate H.
      - apply bottom_project_empty_history in eq_ps'.
        rewrite eq_ps' in H.
        specialize (unfold_history_cons s i). intros.
        spec H0. intros contra. rewrite eq_ps in contra. discriminate contra.
        rewrite H0 in H. discriminate H.
      - discriminate H.
      - unfold get_history' in H.
        destruct s; destruct s';
        try discriminate eq_ps';
        try discriminate eq_ps.
        + unfold rec_history in H.
          destruct (depth (last_recorded index_listing is1 i)) eqn : eq_d1;
          destruct (depth (last_recorded index_listing is2 i)) eqn : eq_d2;
          try unfold last_recorded in *;
          try unfold project in *;
          try apply depth_zero_bottom in eq_d1;
          try apply depth_zero_bottom in eq_d2;
          try rewrite eq_d1 in eq_ps;
          try rewrite eq_d2 in eq_ps';
          try discriminate eq_ps;
          try discriminate eq_ps'.
          rewrite eq_ps in H.
          rewrite eq_ps' in H.
          inversion H.
          reflexivity.
      - specialize (unfold_history_cons s i) as Hus.
        specialize (unfold_history_cons s' i) as Hus'.
        spec Hus. intros contra. rewrite contra in eq_ps. discriminate eq_ps.
        spec Hus'. intros contra. rewrite contra in eq_ps'. discriminate eq_ps'.
        rewrite H in eq_ps.
        rewrite eq_ps in Hus.
        rewrite eq_ps' in Hus'.
        rewrite Hus.
        rewrite Hus'.
        reflexivity.
   Qed.

End Equivocation.
