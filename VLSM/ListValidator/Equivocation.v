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
      destruct s.
      simpl.
      destruct p.
      remember (x, x0) as gigi.
      generalize dependent x0.
      generalize dependent x.
      induction H.
      - intros.
        simpl in *.
        destruct is.
        simpl in *.
        unfold initial_state_prop in i.
        destruct i.
        unfold s.
        inversion Heqgigi.
        subst.
        discriminate.
      - intros.
        simpl in *.
        unfold s.
        inversion Heqgigi.
        unfold s.
        discriminate.
      - destruct l eqn : eq.
        + intros.
          simpl in *.
          inversion Heqgigi.
          unfold update_consensus.
          unfold update_state.
          assert (dif : s <> Bottom). {
            apply IHprotocol_prop1 with (x0 := _om).
            reflexivity.
          }
          destruct s.
          * assumption.
          * simpl in *.
            discriminate.
         + intros.
           simpl in *.
           assert (dif : s <> Bottom). {
            apply IHprotocol_prop1 with (x0 := _om).
            reflexivity.
          }
          destruct om.
          inversion Heqgigi.
          * unfold update_state.
            destruct s.
            assumption.
            discriminate.
          * inversion Heqgigi.
            destruct s.
            elim dif.
            reflexivity.
            rewrite <- H2.
            discriminate.
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

    Lemma output_gets_recorded :
      forall (l : label)
             (s1 s2 : state)
             (m1 : option message)
             (m2 : message)
             (som1 := (s1, m1))
             (som2 := (s2, Some m2))
             (Hprotocol : protocol_transition preX l som1 som2),
             project s2 index_self = snd m2.
    Proof.
      intros.
      unfold protocol_transition in Hprotocol.
      destruct Hprotocol as [pr_valid_prop transition_prop].
      unfold protocol_valid in pr_valid_prop.
      simpl in *.
      unfold transition in transition_prop.
      destruct l eqn : l_eq.
      - unfold som2 in transition_prop.
        inversion transition_prop.
        simpl.
        assert (project (update_consensus (update_state s1 s1 index_self) c) index_self
                = project (update_state s1 s1 index_self) index_self). {
                  symmetry.
                  apply (@update_consensus_clean index index_listing _ _).
                }
       rewrite H.
       apply (@project_same index index_listing Hfinite _ _).
       apply protocol_prop_no_bottom.
       destruct pr_valid_prop.
       assumption.
       - destruct m1 eqn : m1_eq; inversion transition_prop.
    Qed.

    Lemma input_gets_recorded :
      forall (l : label)
             (s1 s2 : state)
             (m1 : message)
             (m2 : option message)
             (i : index)
             (som1 := (s1, Some m1))
             (som2 := (s2, m2))
             (Hmi : fst m1 = i)
             (Hnot_self : i <> index_self)
             (Hprotocol : protocol_transition preX l som1 som2),
             project s2 i = snd m1.
    Proof.
      intros.
      unfold protocol_transition in Hprotocol.
      destruct Hprotocol as [pr_valid_prop transition_prop].
      unfold protocol_valid in pr_valid_prop.
      simpl in *.
      unfold transition in transition_prop.
      unfold som2 in transition_prop.
      destruct l eqn : l_eq.
      - inversion transition_prop.
        rewrite <- Hmi in Hnot_self.
        elim Hnot_self.
        destruct pr_valid_prop as [_ [_ [_ Hno_input]]].
        discriminate Hno_input.
       - inversion transition_prop.
         rewrite Hmi.
         rewrite @project_same.
         reflexivity.
         exact Hfinite.
         apply protocol_prop_no_bottom.
         destruct pr_valid_prop as [Hprotocol Hothers].
         assumption.
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

    Definition state_le
      (s1 s2 : state)
      : Prop
      := forall (i : index), incl (get_history' s1 i) (get_history' s2 i).

    Definition state_leb
      (s1 s2 : state)
      : bool
      := forallb (fun i : index => inclb (get_history' s1 i) (get_history' s2 i)) index_listing.

    Lemma state_le_function : PredicateFunction2 state_le state_leb.
    Proof.
      intros s1 s2. unfold state_leb. rewrite forallb_forall.
      split; intros Hle i.
      - intros _. apply incl_function. apply Hle.
      - apply incl_function. apply Hle. apply (proj2 Hfinite).
    Qed.

    Definition state_lt
      (s1 s2 : state)
      : Prop
      := state_le s1 s2 /\
      exists (i : index) (s : state), In s (get_history' s2 i) /\ ~In s (get_history' s1 i).

    Definition state_ltb
      (s1 s2 : state)
      : bool
      := state_leb s1 s2 &&
      existsb
        (fun i : index =>
          existsb (fun s : state => negb (inb decide_eq s (get_history' s1 i))) (get_history' s2 i))
        index_listing.
          
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

    Lemma state_lt_function : PredicateFunction2 state_lt state_ltb.
    Proof.
      intros s1 s2. unfold state_ltb.
      rewrite andb_true_iff.
      repeat split; destruct H as [Hle H]; try (apply state_le_function; assumption).
      - destruct H as [i [s [Hs2 Hs1]]]. apply existsb_exists.
        exists i. split; try apply (proj2 Hfinite).
        apply existsb_exists. exists s. split; try assumption.
        apply negb_true_iff.
        destruct (inb decide_eq s (get_history' s1 i)) eqn:H; try reflexivity.
        elim Hs1. apply in_function in H. assumption.
      - apply existsb_exists in H. destruct H as [i [_ H]].
        apply existsb_exists in H. destruct H as [s [Hs2 Hs1]].
        exists i. exists s. split; try assumption.
        intro contra. apply in_correct in contra.
        rewrite contra in Hs1. discriminate Hs1.
    Qed.

    Lemma state_lt_dec: RelDecision state_lt.
    Proof.
      intros a b.
      eapply reflect_dec.
      apply iff_reflect, state_lt_function.
    Qed.

    Lemma state_le_refl
      (s1 : state)
      : state_le s1 s1.
    Proof.
      intro i. apply incl_refl.
    Qed.

    Lemma state_le_tran
      (s1 s2 s3 : state)
      (H12 : state_le s1 s2)
      (H23 : state_le s2 s3)
      : state_le s1 s3.
    Proof.
      intro i. spec H12 i. spec H23 i.
      apply incl_tran with (m := (get_history' s2 i)); assumption.
    Qed.

    Lemma state_le_preorder : PreOrder state_le.
    Proof.
      split.
      - intro s. apply state_le_refl.
      - intros s1 s2 s3. apply state_le_tran.
    Qed.

    Lemma state_lt_tran
      (s1 s2 s3 : state)
      (H12 : state_lt s1 s2)
      (H23 : state_lt s2 s3)
      : state_lt s1 s3.
    Proof.
      destruct H12 as [Hle12 _].
      destruct H23 as [Hle23 [i [s [Hs Hns]]]].
      specialize (state_le_tran _ _ _ Hle12 Hle23) as Hle13.
      split; try assumption.
      exists i. exists s.
      split; try assumption.
      intro H13. elim Hns.
      apply Hle12. assumption.
    Qed.

    Lemma state_lt_irreflexive : Irreflexive state_lt.
    Proof.
      intros s Hlt.
      destruct Hlt as [_ [i [si [Hin Hnin]]]].
      elim Hnin. assumption.
    Qed.

    Lemma state_lt_strictorder : StrictOrder state_lt.
    Proof.
      split; try apply state_lt_irreflexive.
      intros s1 s2 s3 H12 H23.
      specialize (state_lt_tran s1 s2 s3 H12 H23).
      intro; assumption.
    Qed.

    Lemma state_le_bottom
      (s : state)
      : state_le Bottom s.
    Proof.
      intro i. simpl. apply incl_nil_l.
    Qed.

    Lemma state_le_transition : protocol_transition_preserving preX state_le.
    Proof.
      intro s1; intros.
      intro i.
      unfold protocol_transition in Hprotocol.
      destruct Hprotocol as [Hprotocol_valid Htransition].
      simpl in *.

      assert (s1 <> Bottom). {
        apply protocol_prop_no_bottom.
        intuition.
      }

      destruct l eqn : eq.
      - inversion Htransition.
        destruct (decide (index_self = i)).
        + rewrite history_disregards_cv.
          specialize (history_append s1 s1).
          intros.
          specialize (H0 H H i eq_refl).
          rewrite <- e in H0 at 1.
          rewrite H0.
          unfold In.
          right.
          assumption.
       + rewrite history_disregards_cv.
         specialize (history_oblivious s1 s1 i index_self n).
         intros.
         rewrite <- H0.
         apply incl_refl.
      -  destruct om1.
         destruct (decide (fst m = i)) eqn : dec_eq.
         + inversion Htransition.
           specialize (history_append s1 (snd m) H).
           intros.
           destruct Hprotocol_valid as [Ha [Hb [Hc [Hd He]]]].
           specialize (H0 Hd i).
           rewrite e in Hc.
           symmetry in Hc.
           specialize (H0 Hc).
           rewrite e.
           rewrite H0.
           apply incl_tl. apply incl_refl.
         + inversion Htransition.
           assert (get_history' (update_state s1 (snd m) (fst m)) i = get_history' s1 i). {
             symmetry.
             apply history_oblivious.
             assumption.
           }
           rewrite H0.
           apply incl_refl.
         + inversion Htransition.
           rewrite <- H1.
           apply incl_refl.
    Qed.

    Lemma state_lt_transition : protocol_transition_preserving preX state_lt.
    Proof.
      intro; intros.
      split; try (apply state_le_transition with l om1 om2; assumption).
      destruct Hprotocol as [[Hs1 [Hom1 Hv]] Ht].
      simpl in *. unfold vvalid in Hv. unfold vtransition in Ht. simpl in *.
      specialize (protocol_no_bottom (exist _  _ Hs1)) as Hnb.
      destruct l as [c |].
      - inversion Ht; subst; clear Ht.
        exists index_self. exists s1.
        rewrite history_disregards_cv.
        rewrite history_append; try assumption; try reflexivity.
        split; try (left; reflexivity).
        apply history_no_self_reference.
      - destruct om1 as [m|]; inversion Ht; subst; clear Ht.
        + exists (fst m). exists (snd m).
          destruct Hv as [Hv [Hnbm Hi]]. symmetry in Hv.
          rewrite history_append; try assumption; try reflexivity.
          split; try (left; reflexivity).
          destruct (project s1 (fst m)) eqn:Hs1m.
          * specialize (unfold_history_bottom _ _ Hs1m) as H.
            rewrite H. intro contra; inversion contra.
          * assert (Hs1nb : project s1 (fst m) <> Bottom)
            by (intro contra; rewrite Hs1m in contra; discriminate contra).
            rewrite unfold_history_cons; try assumption.
            rewrite Hs1m in *.
            rewrite <- Hv in *.
            rewrite <- unfold_history_cons; try assumption.
            apply history_no_self_reference.
        + inversion Hv.
    Qed.

    Lemma state_le_in_futures
      (s1 s2 : state)
      (Hin : in_futures preX s1 s2)
      : state_le s1 s2.
    Proof.
      apply (in_futures_preserving preX); try assumption; try apply state_le_transition.
      apply state_le_preorder.
    Qed.

    Lemma state_lt_in_futures
      (s1 s2 : state)
      (Hin : in_futures preX s1 s2)
      (Hne : s1 <> s2)
      : state_lt s1 s2.
    Proof.
      apply (in_futures_strict_preserving preX); try assumption.
      - apply state_lt_strictorder.
      - apply state_lt_transition.
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

    Lemma message_gets_recorded
      (s : (@state index index_listing))
      (s0 : state)
      (m : message)
      (tr : list transition_item)
      (last_item : transition_item)
      (Hprotocol : finite_protocol_trace preX s0 (tr ++ [last_item]))
      (Hm: output last_item = Some m) :
      project (destination (last_item)) index_self = snd m.
    Proof.
     intros.
     specialize (protocol_transition_to preX s0 last_item (tr ++ [last_item]) tr []).
     intros.
     simpl in H.
     destruct Hprotocol.
     specialize (H eq_refl H0).
     specialize (output_gets_recorded (l last_item) (last (List.map destination tr) s0)).
     intros.
     specialize (H2 (destination last_item) (input last_item) m).
     apply H2.
     rewrite <- Hm.
     apply H.
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

    Lemma new_projection_implies_output_message
      (l : label)
      (som som' : (state * option message))
      (Hprotocol : protocol_transition preX l som som')
      (s' : state)
      (Hold : project (fst som) index_self <> s')
      (Hnew : project (fst som') index_self = s') :
      (snd som') = Some (index_self, s').
    Proof.
      remember Hprotocol as Horiginal.
      unfold protocol_transition in Hprotocol.
      destruct Hprotocol as [Hvalid Htransition].
      simpl in *.
      unfold protocol_valid in *.
      unfold transition in *.
      destruct l eqn: eq_l.
      - destruct som as [s1 om1].
        destruct som' as [s2 om2].
        simpl in *.
        inversion Htransition.
        rewrite <- H0 in Hnew.
        rewrite <- update_consensus_clean with (value := c) in Hnew .
        rewrite @project_same in Hnew.
        rewrite Hnew.
        reflexivity.
        exact Hfinite.
        apply protocol_prop_no_bottom.
        destruct Hvalid as [Hproto Hother].
        assumption.
      - destruct som.
        simpl in *.
        destruct o eqn : eq_o.
        + destruct som'.
          inversion Htransition.
          simpl in Hnew.
          rewrite <- H0 in Hnew.
          destruct (decide (fst m = index_self)).
          * destruct Hvalid as [tmp1 [tmp2 [tmp3 [tmp4 Hneed]]]].
            elim Hneed.
            intuition.
          * rewrite @project_different in Hnew.
            elim Hold.
            intuition.
            exact Hfinite.
            intuition.
            apply protocol_prop_no_bottom.
            destruct Hvalid as [Hneed Hother].
            assumption.
        + destruct Hvalid as [tmp1 [tmp2 Hfalse]].
          exfalso.
          assumption.
    Qed.

    Lemma new_projection_implies_input_message
      (l : label)
      (som som' : (state * option message))
      (Hprotocol : protocol_transition preX l som som')
      (i : index)
      (Hnot_self : i <> index_self)
      (s' : state)
      (Hold : project (fst som) i <> s')
      (Hnew : project (fst som') i = s') :
      (snd som) = Some (i, s').
    Proof.
      remember Hprotocol as Horiginal.
      unfold protocol_transition in Hprotocol.
      destruct Hprotocol as [Hvalid Htransition].
      simpl in *.
      unfold protocol_valid in *.
      unfold transition in *.
      destruct l eqn: eq_l.
      - destruct som as [s1 om1].
        destruct som' as [s2 om2].
        simpl in *.
        inversion Htransition.
        rewrite <- H0 in Hnew.
        rewrite <- update_consensus_clean with (value := c) in Hnew .
        rewrite @project_different in Hnew.
        elim Hold.
        assumption.
        exact Hfinite.
        assumption.
        apply protocol_prop_no_bottom.
        destruct Hvalid as [Hneed Hother].
        assumption.
      - destruct som.
        simpl in *.
        destruct o eqn : eq_o.
        + destruct som'.
          inversion Htransition.
          simpl in Hnew.
          rewrite <- H0 in Hnew.
          destruct (decide (fst m = i)).
          * rewrite e in Hnew.
            rewrite @project_same in Hnew.
            rewrite <- Hnew.
            rewrite <- e.
            rewrite <- surjective_pairing.
            reflexivity.
            exact Hfinite.
            apply protocol_prop_no_bottom.
            destruct Hvalid as [Hneed Hother].
            assumption.
          * rewrite @project_different in Hnew.
            elim Hold.
            intuition.
            exact Hfinite.
            intuition.
            apply protocol_prop_no_bottom.
            destruct Hvalid as [Hneed Hother].
            assumption.
        + destruct som'.
          destruct Hvalid as [temp1 [temp2 Hfalse]].
          exfalso.
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

    Lemma get_history'_all_bottom
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

    Lemma state_le_all_bottom
      (s : state)
      (cv : bool)
      : state_le (Something cv all_bottom) s.
    Proof.
      intro j. rewrite get_history'_all_bottom. apply incl_nil_l.
    Qed.

    Lemma state_lt_last_sent
      (s : state)
      (Hs : protocol_state_prop (pre_loaded_with_all_messages_vlsm X) s)
      (Hnb : (@last_sent index index_self index_listing idec) s <> Bottom)
      : state_lt (last_sent' s) s.
    Proof.
      induction Hs using protocol_state_prop_ind.
      - inversion Hs. subst s. elim Hnb.
        unfold last_sent. simpl. apply project_all_bottom.
      - unfold last_sent.
        destruct Ht as [[Hps [Hom Hv]] Ht].
        specialize (protocol_prop_no_bottom _ Hps) as Hnb'.
        simpl in Ht. unfold vtransition in Ht. simpl in Ht.
        simpl in Hv. unfold vvalid in Hv. simpl in Hv.
        destruct l as [c|].
        + inversion Ht. clear Ht.
          subst s'.
          rewrite <- update_consensus_clean.
          rewrite (@project_same _ _ Hfinite);[|assumption].
          split;[(intro j; rewrite history_disregards_cv; destruct (decide (index_self = j)))|].
          * subst j. rewrite history_append;[|assumption|assumption|reflexivity].
            apply incl_tl. apply incl_refl.
          * rewrite <- history_oblivious;[|assumption]. apply incl_refl.
          * exists index_self. exists s.
            split;[|solve[apply history_no_self_reference]].
            rewrite history_disregards_cv.
            rewrite history_append;[|assumption|assumption|reflexivity].
            left. reflexivity.
        + destruct om as [m|]; inversion Ht; clear Ht; subst s'.
          * destruct m as (im, sm); simpl in *.
            destruct Hv as [Hsim [Hsm Him]].
            rewrite (@project_different _ _ Hfinite) by assumption.
            unfold last_sent in Hnb.
            rewrite (@project_different _ _ Hfinite) in Hnb by assumption.
            { split;[intro j; destruct (decide (im = j))|].
            - subst im. rewrite history_append; auto.
              apply incl_tl. apply IHHs. assumption.
            - rewrite <- history_oblivious by assumption.
              apply IHHs. assumption.
            - exists index_self. exists (project s index_self).
              split;[|solve[apply history_no_self_reference]].
              rewrite <- history_oblivious.
              + rewrite unfold_history_cons;[|assumption]. left. reflexivity.
              + intro. subst. elim Him. reflexivity.
            }
          * apply IHHs. assumption.
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

    Lemma state_lt_previously_sent
      (m : message)
      (Hm : byzantine_message_prop X m)
      (i := fst m)
      (s := snd m)
      (Hnb : project s i <> Bottom)
      : state_lt (project s i) s.
    Proof.
      destruct (byzantine_message_self_id m Hm) as [Hi Hs].
      unfold s in *; clear s.
      unfold i in *; clear i. rewrite Hi in *.
      apply state_lt_last_sent; assumption.
    Qed.

    (* If a state is present in some history,
       we know for sure that at some point it was equal to somebody's projection

       The proof works by inducting over the length of the protocol trace and
       destructing over whether the last state in the trace is the one
       with the sought projection (otherwise, it was in its history even
       earlier and we can fall back to the inductive hypothesis for
       a shorter trace *)

    Lemma history_to_projection
      (s si target : state)
      (len : nat)
      (tr : list transition_item)
      (Hlen : length tr = len)
      (i : index)
      (Hprotocol_tr : finite_protocol_trace preX si tr)
      (Hlast : last (List.map destination tr) si = s)
      (Hin : In target (get_history' s i)) :
      List.Exists (fun elem : (@transition_item _ (type preX)) => project (destination elem) i = target) tr.
    Proof.
      generalize dependent s.
      generalize dependent tr.
      induction len.
      - intros.
        rewrite length_zero_iff_nil in Hlen.
        subst.
        simpl in *.
        inversion Hprotocol_tr.
        destruct H0.
        rewrite H0 in Hin.
        rewrite get_history'_all_bottom in Hin.
        inversion Hin.
      - intros.
        rewrite Exists_exists.

        assert (Hnot_empty: tr <> []). {
          intros contra.
          rewrite contra in Hlen.
          discriminate Hlen.
        }
        specialize (exists_last Hnot_empty).
        intros.
        destruct X0 as [tr' [lst Hlst]].

        assert (Hlst_s : destination lst = s). {
          rewrite Hlst in Hlast.
          rewrite map_app in Hlast.
          rewrite last_app in Hlast.
          simpl in Hlast.
          assumption.
        }

        destruct (state_eq_dec (project s i) target) eqn : eq.
        + exists lst.
          split.
          * rewrite Hlst.
            apply in_or_app.
            right.
            intuition.
          * rewrite Hlst in Hlast.
            rewrite map_app in Hlast.
            rewrite last_app in Hlast.
            simpl in *.
            subst.
            reflexivity.
       + assert (Hlen' : length tr' = len). {
          rewrite Hlst in Hlen.
          rewrite app_length in Hlen.
          simpl in *.
          lia.
         }

         assert (Hprotocol' : finite_protocol_trace preX si tr'). {
           remember (@Finite _ (type preX) si tr) as trace.
           remember (exist _ trace Hprotocol_tr) as protocol_trace.
           destruct Hprotocol_tr.
           specialize (finite_protocol_trace_from_prefix preX si tr f (length tr - 1)).
           intros.

           assert (Hone_less: tr' = list_prefix tr (length tr - 1)). {
              rewrite Hlst.
              specialize (list_prefix_split tr tr' [lst] (length tr')).
              intros.
              intuition.
              rewrite <- H0 at 1.
              rewrite <- Hlst.
              assert (length tr' = length tr - 1). {
                lia.
              }
              intuition.
           }

           rewrite Hone_less.
           unfold finite_protocol_trace.
           intuition.
         }

         remember (last (List.map destination tr') si) as prev_lst.

         assert (protocol_transition preX (l lst) (prev_lst, input lst) (destination lst, output lst)). {
           specialize (protocol_transition_to preX si lst tr tr' [] Hlst).
           intros.
           destruct Hprotocol_tr.
           specialize (H H0).
           rewrite Heqprev_lst.
           assumption.
         }

         remember H as Horiginal.

         unfold protocol_transition in H.
         destruct H as [Hvalid Htransition].
         simpl in *.

         destruct (l lst) eqn : eq_l.
         * destruct (decide (i = index_self)). {
           - rewrite e in Hin.
             inversion Htransition.
             rewrite Hlst_s in H0.
             rewrite <- H0 in Hin.
             rewrite history_disregards_cv in Hin.
             rewrite history_append in Hin.
             simpl in Hin.
             assert (prev_lst <> target). {
              intros contra.
              specialize (output_gets_recorded (update c) (prev_lst) (destination lst) (input lst) (index_self, prev_lst)).
              intros.
              simpl in H.
              replace (@Some (@message index index_listing)
                  (@pair index (@state index index_listing) index_self prev_lst)) with (output lst) in H.
              specialize (H Horiginal).
              rewrite Hlst_s in H.
              rewrite <- e in H.
              elim n.
              rewrite <- contra.
              assumption.
             }

             inversion Hin.
             + elim H.
               assumption.
             + symmetry in Heqprev_lst.
               specialize (IHlen tr' Hlen' Hprotocol' prev_lst Heqprev_lst).
               rewrite <- e in H2.
               specialize (IHlen H2).
               rewrite Exists_exists in IHlen.
               destruct IHlen as [x [Hinx Hprojectx]].
               exists x.
               split.
               rewrite Hlst.
               apply in_or_app.
               left.
               assumption.
               assumption.
             + apply protocol_prop_no_bottom.
               destruct Hvalid as [Hneed Hother].
               assumption.
             + apply protocol_prop_no_bottom.
               destruct Hvalid as [Hneed Hother].
               assumption.
             + reflexivity.
           } {
           - rewrite <- Hlst_s in Hin.
             inversion Htransition.
             rewrite <- H0 in Hin.
             rewrite history_disregards_cv in Hin.
             specialize (history_oblivious prev_lst prev_lst i index_self).
             intros.

             assert (get_history' prev_lst i = get_history' (update_state prev_lst prev_lst index_self) i). {
              apply H.
              intuition.
             }

             rewrite <- H2 in Hin.
             symmetry in Heqprev_lst.
               specialize (IHlen tr' Hlen' Hprotocol' prev_lst Heqprev_lst).
               specialize (IHlen Hin).
               rewrite Exists_exists in IHlen.
               destruct IHlen as [x [Hinx Hprojectx]].
               exists x.
               split.
               rewrite Hlst.
               apply in_or_app.
               left.
               assumption.
               assumption.
            }
         * simpl in *.
           destruct (input lst) eqn : eq_input.
           {- inversion Htransition.
              rewrite <- Hlst_s in Hin.
              rewrite <- H0 in Hin.
              destruct (decide (fst m = i)).
              + rewrite e in Hin.
                rewrite history_append in Hin.
                simpl in Hin.
                assert (snd m <> target). {
                  intros contra.
                  specialize (input_gets_recorded receive prev_lst (destination lst) m (output lst) i).
                  intros.
                  specialize (H e).
                  destruct Hvalid as [Ha [Hb [Hc [Hd He]]]].
                  rewrite <- e in H.
                  assert (fst m <> index_self). {
                    intuition.
                  }
                  specialize (H H2 Horiginal).
                  rewrite e in H.
                  rewrite Hlst_s in H.
                  rewrite contra in H.
                  elim n.
                  assumption.
                }
                inversion Hin.
                * elim H.
                  assumption.
                * symmetry in Heqprev_lst.
                  specialize (IHlen tr' Hlen' Hprotocol' prev_lst Heqprev_lst).
                  specialize (IHlen H2).
                  rewrite Exists_exists in IHlen.
                  destruct IHlen as [x [Hinx Hprojectx]].
                  exists x.
                  split.
                  rewrite Hlst.
                  apply in_or_app.
                  left.
                  assumption.
                  assumption.
                * apply protocol_prop_no_bottom.
                  destruct Hvalid as [Hneed Hother].
                  assumption.
                * destruct Hvalid as [Ha [Hb [Hc [Hd He]]]].
                  assumption.
                * destruct Hvalid as [Ha [Hb [Hc [Hd He]]]].
                  rewrite <- e.
                  symmetry.
                  assumption.
               + rewrite <- history_oblivious with (news := snd m) (j := fst m) in Hin.
                 symmetry in Heqprev_lst.
                 specialize (IHlen tr' Hlen' Hprotocol' prev_lst Heqprev_lst).
                  specialize (IHlen Hin).
                  rewrite Exists_exists in IHlen.
                  destruct IHlen as [x [Hinx Hprojectx]].
                  exists x.
                  split.
                  rewrite Hlst.
                  apply in_or_app.
                  left.
                  assumption.
                  assumption.
                  assumption.
             }
             destruct Hvalid as [Ha [Hb Hc]].
             exfalso.
             assumption.
    Qed.

    Lemma output_to_history
      (s : state)
      (si : state)
      (m : message)
      (tr : list transition_item)
      (Htr : finite_protocol_trace preX si tr)
      (Hlast : last (List.map destination tr) si = s)
      (Hexists: List.Exists (fun (elem : transition_item) => output elem = Some m) tr) :
      In (snd m) (get_history' s index_self).
    Proof.
      rewrite Exists_exists in Hexists.
      destruct Hexists as [x [Hin Hm]].
      apply in_split in Hin.
      destruct Hin as [l1 [l2 Hconcat]].
      remember (last (List.map destination l1) si) as prev_x.
      specialize (protocol_transition_to preX si x tr l1 l2).
      intros.
      specialize (H Hconcat).
      destruct Htr.
      specialize (H H0).
      simpl in H.
      specialize (output_gets_recorded (l x) prev_x (destination x) (input x) m).
      intros.
      simpl in H2.
      rewrite Heqprev_x in H2.
      rewrite <- Hm in H2.
      specialize (H2 H).
      specialize (projection_in_history (destination x) (snd m) index_self).
      assert ((snd m) <> Bottom). {
           apply emitted_not_bottom.
           specialize (can_emit_from_protocol_trace preX si m tr).
           intros.
           assert (finite_protocol_trace preX si tr). {
            unfold finite_protocol_trace.
            split.
            assumption.
            assumption.
           }
           specialize (H3 H4).
           assert (List.Exists (fun elem : transition_item => output elem = Some m) tr). {
              rewrite Exists_exists.
              exists x.
              split.
              rewrite Hconcat.
              apply in_elt.
              assumption.
           }
           specialize (H3 H5).
           assumption.
      }

      intros.
      specialize (H4 H3 H2).
      specialize (state_le_in_futures (destination x) s) as Hfutures.
      assert (in_futures preX (destination x) s). {
        unfold in_futures.
        specialize (finite_protocol_trace_from_app_iff preX si) as Happ.
        specialize (Happ (l1 ++ [x]) (l2)).
        exists l2.
        split.
        - destruct Happ.
          rewrite Hconcat in H0.
          rewrite <- app_assoc in H6.
          specialize (H6 H0).
          destruct H6.

          assert (last (List.map destination (l1 ++ [x])) si = destination x). {
             rewrite map_app.
             rewrite last_app.
             simpl.
             reflexivity.
          }

          rewrite <- H8.
          assumption.
        - rewrite Hconcat in Hlast.
          rewrite map_app in Hlast.
          rewrite last_app in Hlast.
          rewrite map_cons in Hlast.
          rewrite unroll_last in Hlast.
          assumption.
      }
      specialize (Hfutures H5).
      specialize (Hfutures index_self).
      apply Hfutures.
      assumption.
    Qed.

    Lemma input_to_history
      (s : state)
      (si : state)
      (m : message)
      (tr : list transition_item)
      (Htr : finite_protocol_trace preX si tr)
      (Hlast : last (List.map destination tr) si = s)
      (Hexists: List.Exists (fun (elem : transition_item) => input elem = Some m) tr) :
      In (snd m) (get_history' s (fst m)).
    Proof.
      rewrite Exists_exists in Hexists.
      destruct Hexists as [x [Hin Hm]].
      apply in_split in Hin.
      destruct Hin as [l1 [l2 Hconcat]].
      remember (last (List.map destination l1) si) as prev_x.
      specialize (protocol_transition_to preX si x tr l1 l2).
      intros.
      specialize (H Hconcat).
      destruct Htr.
      specialize (H H0).
      simpl in H.
      specialize (input_gets_recorded (l x) prev_x (destination x) m (output x)).
      intros.
      simpl in H2.
      rewrite Heqprev_x in H2.
      rewrite <- Hm in H2.
      specialize (H2 (fst m)).
      specialize (H2 eq_refl).
      specialize (projection_in_history (destination x) (snd m) (fst m)).

      assert ((snd m) <> Bottom). {
         unfold protocol_transition in H.
         destruct H as [Hvalid Htransition].
         simpl in *.
         destruct (l x).
         destruct Hvalid as [Ha [Hb [Hc Hd]]].
         rewrite Hd in Hm.
         discriminate Hm.
         rewrite Hm in Hvalid.
         destruct Hvalid as [Ha [Hb [Hc [Hd He]]]].
         assumption.
      }

      intros.
      assert ((fst m) <> index_self). {
        unfold protocol_transition in H.
        destruct H as [Hvalid Htransition].
        unfold protocol_valid in Hvalid.
        simpl in *.
        destruct (l x).
        destruct Hvalid as [Ha [Hb [Hc Hd]]].
        rewrite Hd in Hm.
        discriminate Hm.
        rewrite Hm in Hvalid.
        destruct Hvalid as [Ha [Hb [Hc [Hd He]]]].
        intuition.
      }

      specialize (H2 H5).
      specialize (H2 H).
      specialize (H4 H3).
      specialize (state_le_in_futures (destination x) s).
      intros.
      assert (in_futures preX (destination x) s). {
               unfold in_futures.
              specialize (finite_protocol_trace_from_app_iff preX si) as Happ.
              specialize (Happ (l1 ++ [x]) (l2)).
              exists l2.
              split.
              destruct Happ.
              rewrite Hconcat in H0.
              rewrite <- app_assoc in H8.
              specialize (H8 H0).
              destruct H8.

              assert (last (List.map destination (l1 ++ [x])) si = destination x). {
                 rewrite map_app.
                 rewrite last_app.
                 simpl.
                 reflexivity.
              }

              rewrite <- H10.
              assumption.
              rewrite Hconcat in Hlast.
              rewrite map_app in Hlast.
              rewrite last_app in Hlast.
              rewrite map_cons in Hlast.
              rewrite unroll_last in Hlast.
              assumption.
      }

      specialize (H6 H7).
      apply H6.
      apply H4.
      assumption.
    Qed.
  
    Lemma send_oracle_prop
      (s : state)
      (Hprotocol : protocol_state_prop preX s)
      (m : message) :
      has_been_sent_prop X send_oracle s m.
    Proof.
      unfold has_been_sent_prop.
      unfold all_traces_have_message_prop.
      unfold selected_message_exists_in_all_preloaded_traces.
      unfold specialized_selected_message_exists_in_all_traces.
      split.
      - intros.
        unfold send_oracle in H.
        destruct (decide (fst m = index_self)) eqn:eq.
        2: contradiction H.
        destruct s eqn:eq_s.
        + contradiction H.
        + apply Is_true_eq_true, existsb_exists in H.
          destruct H as [x [Hin Heq_state]].
          rewrite e in Hin.
          specialize (no_bottom_in_history (Something b is) x index_self Hin) as Hxgood.
          rewrite <- e in Hin.
          (* Somewhere, the message shows up as somebody's projection *)

          assert (List.Exists (fun elem : (@transition_item _ (type preX)) => project (destination elem) index_self = (snd m)) tr). {
              apply history_to_projection with (s := s) (si := start) (len := length tr).
              reflexivity.
              assumption.
              rewrite eq_s.
              assumption.
              rewrite eq_s.
              rewrite state_eqb_eq in Heq_state.
              rewrite Heq_state.
              rewrite <- e.
              assumption.
          }

          (* Among those places, we choose the earliest one *)

          assert (exists (prefix : list transition_item)
                         (suffix : list transition_item)
                         (target : transition_item),
                         tr = prefix ++ [target] ++ suffix /\
                         project (destination target) index_self = (snd m) /\
                         ~List.Exists (fun elem : (@transition_item _ (type preX))
                                        => project (destination elem) index_self = (snd m)) prefix). {
              rewrite Exists_exists in H.
              destruct H as [t [Hin' Hproject]].
              rewrite <- state_eqb_eq in Hproject.
              assert (exists (t : transition_item), In t tr /\ state_eqb (project (destination t) index_self) (snd m) = true). {
                exists t.
                intuition.
              }

              rewrite <- existsb_exists in H.
              specialize (existsb_first
                          tr
                          (fun x : transition_item => state_eqb (project (destination x) index_self) (snd m))
                          H).
              intros.
              destruct H0 as [prefix [suffix [first [Heqb [Hsplt Hno_earlier]]]]].
              exists prefix.
              exists suffix.
              exists first.
              split.
              assumption.
              split.
              rewrite <- state_eqb_eq.
              assumption.
              rewrite <- Forall_Exists_neg.
              rewrite Forall_forall.
              intros.
              apply In_nth with (d := x0) in H0.
              destruct H0 as [n [Hless Hnth]].
              apply existsb_nth with (n := n) (d := x0) in Hno_earlier.
              rewrite <- Hnth.
              rewrite state_eqb_neq in Hno_earlier.
              assumption.
              assumption.
          }

          destruct H0 as [prefix [suffix [target [Hsplit [Hproject Hnot_earlier]]]]].

          unfold finite_protocol_trace in Htr.
          destruct Htr as [Htr Hinitial].

          rewrite Exists_exists.
          exists target.
          split.
          * rewrite Hsplit.
            apply in_elt.
          * destruct prefix.
            simpl in *.

            assert (protocol_transition
                    preX
                    (l target)
                    (start, (input target))
                    ((destination target), (output target))). {
                specialize (first_transition_valid preX start target).
                intros.
                apply H0.
                specialize (finite_protocol_trace_from_prefix preX start tr Htr 1).
                intros.
                replace
                  (@cons (@transition_item (@message index index_listing) (@type (@message index index_listing) preX))
                    target
                    nil)
                  with (list_prefix tr 1)
                ; try assumption.
                {
                  rewrite Hsplit.
                  simpl.
                  unfold list_prefix.
                  destruct suffix; reflexivity.
                }
            }

            specialize (new_projection_implies_output_message
                        (l target)
                        (start, (input target))
                        ((destination target), (output target))
                        H0
                        (snd m)).

            intros.
            simpl in H1.

            assert (project start index_self <> snd m). {
              unfold project.
              destruct start eqn : eq_start.
              - unfold initial_state_prop in Hinitial.
                destruct Hinitial.
                discriminate H2.
              - unfold initial_state_prop in Hinitial.
                destruct Hinitial.
                inversion H2.
                assert (project_indexed index_listing all_bottom index_self = Bottom). {
                  rewrite project_all_bottom.
                  reflexivity.
                }
                rewrite H3.
                rewrite state_eqb_eq in Heq_state.
                rewrite Heq_state.
                intuition.
            }

            specialize (H1 H2 Hproject).
            rewrite <- e in H1.
            rewrite <- surjective_pairing in H1.
            assumption.

            assert (Hnot_empty : t :: prefix <> []). {
              intros contra.
              discriminate contra.
            }

            specialize (exists_last Hnot_empty).
            intros.

            destruct X0 as [rem_pref [prev_target Heqprev]].
            rewrite Heqprev in Hsplit.
            specialize (finite_ptrace_consecutive_valid_transition preX start tr suffix rem_pref).
            intros.
            specialize (H0 prev_target target).
            specialize (H0 Htr).
            simpl in *.
            rewrite <- app_assoc in Hsplit.
            simpl in Hsplit.
            specialize (H0 Hsplit).
            specialize (new_projection_implies_output_message
                       (l target)
                       (destination prev_target, (input target))
                       ((destination target), (output target))
                       H0
                       (snd m)).
            intros.
            simpl in *.
            rewrite <- e in H1.
            rewrite <- surjective_pairing in H1.
            apply H1.
            rewrite Heqprev in Hnot_earlier.
            rewrite <- Forall_Exists_neg in Hnot_earlier.
            rewrite Forall_app in Hnot_earlier.
            destruct Hnot_earlier as [left right].
            rewrite Forall_forall in right.
            specialize (right prev_target).
            simpl in *.
            rewrite e.
            apply right.
            intuition.
            rewrite e.
            assumption.
      - unfold send_oracle.
        intros.
        remember Hprotocol as Hprotocol'.
        destruct Hprotocol as [om Hprotocol].
        specialize (protocol_is_trace preX s om Hprotocol) as Hsome_trace.
        intros.
        simpl in *.
        destruct Hsome_trace.
        + unfold initial_state_prop in H0.
          remember H0 as H0'.
          destruct H0.
          assert (Hempty : finite_protocol_trace (pre_loaded_with_all_messages_vlsm preX) s []). {
            unfold finite_protocol_trace.
            simpl.
            split.
            - apply finite_ptrace_empty. assumption.
            - assumption.
          }

          specialize (H s [] Hempty).
          simpl in H.
          specialize (H eq_refl).

          simpl in H.
          inversion H.
        + destruct H0 as [s0 [tr [Hfinite_protocol [Hdest Hmessage]]]].
          destruct Hmessage.
          specialize (H s0 tr Hfinite_protocol).
          assert (Hlst := last_error_destination_last tr s Hdest s0).
          specialize (H Hlst).
          assert (can_emit preX m). {
            specialize (can_emit_from_protocol_trace preX s0 m tr Hfinite_protocol H).
            intros.
            assumption.
          }

          assert ((fst m) = index_self). {
            apply emitted_messages_only_from_self.
            assumption.
          }

          destruct (decide (fst m = index_self)).
          * assert (s <> Bottom). {
              apply protocol_prop_no_bottom.
              assumption.
            }

            destruct s. elim H2. reflexivity.

            (* Rewrite it as Prop involving In. *)

            assert (In (snd m) (get_history' (Something b is) (fst m))). {
              specialize (output_to_history (Something b is) s0 m tr).
              intros.
              specialize (H3 Hfinite_protocol Hlst H).
              rewrite e.
              assumption.
            }

            apply Is_true_iff_eq_true, existsb_exists.
            exists (snd m).
            split.
            assumption.
            unfold state_eqb.
            rewrite eq_dec_if_true.
            reflexivity.
            reflexivity.
           * rewrite H1 in n.
              elim n.
              reflexivity.
    Qed.

    Lemma receive_oracle_prop
      (s : state)
      (Hprotocol : protocol_state_prop preX s)
      (m : message) :
      has_been_received_prop X receive_oracle s m.
    Proof.
      unfold has_been_received_prop.
      unfold all_traces_have_message_prop.
      unfold selected_message_exists_in_all_preloaded_traces.
      unfold specialized_selected_message_exists_in_all_traces.
      split.
      - intros.
        unfold receive_oracle in H.
        destruct (decide (fst m = index_self)) eqn:eq.
        + contradiction H.
        + destruct s eqn:eq_s.
          * contradiction H.
          * apply Is_true_iff_eq_true, existsb_exists in H.
            destruct H as [x [Hin Heq_state]].
          (* Somewhere, the message shows up as somebody's projection *)

          assert (List.Exists (fun elem : (@transition_item _ (type preX)) => project (destination elem) (fst m) = (snd m)) tr). {
              apply history_to_projection with (s := s) (si := start) (len := length tr).
              reflexivity.
              assumption.
              rewrite eq_s.
              assumption.
              rewrite eq_s.
              rewrite state_eqb_eq in Heq_state.
              rewrite Heq_state.
              assumption.
          }

          (* Among those places, we choose the earliest one *)

          assert (exists (prefix : list transition_item)
                         (suffix : list transition_item)
                         (target : transition_item),
                         tr = prefix ++ [target] ++ suffix /\
                         project (destination target) (fst m) = (snd m) /\
                         ~List.Exists (fun elem : (@transition_item _ (type preX))
                                        => project (destination elem) (fst m) = (snd m)) prefix). {
              rewrite Exists_exists in H.
              destruct H as [t [Hin' Hproject]].
              rewrite <- state_eqb_eq in Hproject.
              assert (exists (t : transition_item), In t tr /\ state_eqb (project (destination t) (fst m)) (snd m) = true). {
                exists t.
                intuition.
              }

              rewrite <- existsb_exists in H.
              specialize (existsb_first
                          tr
                          (fun x : transition_item => state_eqb (project (destination x) (fst m)) (snd m))
                          H).
              intros.
              destruct H0 as [prefix [suffix [first [Heqb [Hsplt Hno_earlier]]]]].
              exists prefix.
              exists suffix.
              exists first.
              split.
              assumption.
              split.
              rewrite <- state_eqb_eq.
              assumption.
              rewrite <- Forall_Exists_neg.
              rewrite Forall_forall.
              intros.
              apply In_nth with (d := x0) in H0.
              destruct H0 as [nn [Hless Hnth]].
              apply existsb_nth with (n := nn) (d := x0) in Hno_earlier.
              rewrite <- Hnth.
              rewrite state_eqb_neq in Hno_earlier.
              assumption.
              assumption.
          }

        rewrite Exists_exists.
        destruct H0 as [prefix [suffix [target [Hconcat [Hproject Hno_earlier]]]]].

        exists target.
        split.
        rewrite Hconcat.
        apply in_elt.

        remember (last (List.map destination prefix) start) as prev_target.
        assert (Hptransition: protocol_transition preX (l target) (prev_target, input target) (destination target, output target)). {
            specialize (protocol_transition_to preX start target tr prefix suffix Hconcat) as Himp.
            destruct Htr.
            specialize (Himp H0).
            rewrite Heqprev_target.
            assumption.
        }

        specialize new_projection_implies_input_message as Hchange.
        specialize (Hchange (l target) (prev_target, input target) (destination target, output target)).
        specialize (Hchange Hptransition (fst m) n (snd m)).
        simpl in *.

        assert (Hold: project prev_target (fst m) <> snd m). {
          destruct prefix eqn : eq_prefix.
          - simpl in *.
            rewrite Heqprev_target.
            assert (Hnot_bottom : snd m <> Bottom). {
              specialize (no_bottom_in_history s x (fst m)).
              intros.
              rewrite eq_s in H0.
              specialize (H0 Hin).
              rewrite state_eqb_eq in Heq_state.
              rewrite <- Heq_state in H0.
              assumption.
            }

            unfold project.
            destruct Htr as [_ Hinit].
            simpl in Hinit.
            unfold initial_state_prop in Hinit.
            destruct Hinit as [cv Hinit].
            rewrite Hinit.
            rewrite project_all_bottom.
            intuition.
          -
          assert (Hnot_empty: prefix <> []). {
            rewrite eq_prefix.
            intros contra.
            discriminate contra.
          }

          specialize (exists_last Hnot_empty).
          intros.

            destruct X0 as [prefix' [lst Hprefix]].
            assert (prev_target = destination lst). {
              rewrite Heqprev_target.
              rewrite <- eq_prefix.
              rewrite Hprefix.
              rewrite map_app.
              rewrite last_app.
              simpl.
              reflexivity.
            }
            rewrite H0.
            rewrite <- Forall_Exists_neg in Hno_earlier.
            rewrite Forall_forall in Hno_earlier.
            specialize (Hno_earlier lst).
            apply Hno_earlier.
            rewrite <- eq_prefix.
            rewrite Hprefix.
            apply in_elt.
        }
        specialize (Hchange Hold Hproject).
        rewrite <- surjective_pairing in Hchange.
        assumption.
      - intros.
        unfold receive_oracle.
        remember Hprotocol as Hprotocol'.
        destruct Hprotocol as [om Hprotocol].
        specialize (protocol_is_trace preX s om Hprotocol) as Hsome_trace.
        intros.
        simpl in *.
        destruct Hsome_trace eqn : trace_eq.
        + unfold vinitial_state_prop in v. unfold Common.initial_state_prop in v. simpl in v.
          unfold initial_state_prop in v.
          remember v as v'.
          destruct v.
          assert (Hempty : finite_protocol_trace (pre_loaded_with_all_messages_vlsm preX) s []). {
            unfold finite_protocol_trace.
            simpl.
            split.
            - apply finite_ptrace_empty. assumption.
            - assumption.
          }

          specialize (H s [] Hempty).
          simpl in H.
          specialize (H eq_refl).

          simpl in H.
          inversion H.
        + destruct e as [start [tr [Hprotocol_tr [Hdest Hothers]]]].
          destruct trace_eq.
          specialize (H start tr Hprotocol_tr).
          assert (Hlst := last_error_destination_last tr s Hdest start).
          specialize (H Hlst).
          rewrite Exists_exists in H.
          destruct H as [x [Hin Hm]].
          apply in_split in Hin.
          destruct Hin as [l1 [l2 Hconcat]].
          remember (last (List.map destination l1) start) as prev_x.

          assert (protocol_transition preX (l x) (prev_x, input x) (destination x, output x)). {
            destruct Hprotocol_tr.
            specialize (protocol_transition_to preX start x tr l1 l2 Hconcat H) as Himp.
            rewrite Heqprev_x.
            assumption.
          }

          destruct (decide (fst m = index_self)).
          * unfold protocol_transition in H.
            destruct H as [Hvalid Htransition].
            unfold protocol_valid in Hvalid.
            destruct Hvalid as [Hpstate [_ Hvalid']].
            simpl in *.
            destruct (l x) eqn : eq_l.
            {
              destruct Hvalid' as [_ Hnoinput].
              rewrite Hm in Hnoinput.
              discriminate Hnoinput.
            }
            { rewrite Hm in Hvalid'.
              destruct Hvalid' as [_ [_ Hdiff]].
              elim Hdiff.
              symmetry.
              assumption.
            }
          * specialize (input_gets_recorded (l x) prev_x (destination x) m (output x) (fst m)) as Hrecorded.
            intros.
            rewrite Hm in H.
            specialize (Hrecorded eq_refl n H).
            specialize (projection_in_history (destination x) (snd m) (fst m)) as Hproject.
            intros.

            assert (Hnot_bottom: snd m <> Bottom). {
              unfold protocol_transition in H.
              unfold protocol_valid in H.
              simpl in H.
              destruct (l x).
              - destruct H as [Hleft Hright].
                inversion Hright.
                destruct Hleft as [Ha [Hb [Hc Hd]]].
                discriminate Hd.
              - destruct H as [Hleft Hright].
                destruct Hleft as [Ha [Hb [Hc [Hd He]]]].
                assumption.
            }

            specialize (Hproject Hnot_bottom Hrecorded).
            specialize (state_le_in_futures (destination x) s) as Hpersists.
            intros.

            assert (Hfutures: in_futures preX (destination x) s). {
              unfold in_futures.
              specialize (finite_protocol_trace_from_app_iff preX start) as Happ.
              specialize (Happ (l1 ++ [x]) (l2)).
              exists l2.
              split.
              destruct Happ.
              destruct Hprotocol_tr.
              rewrite Hconcat in H2.
              rewrite <- app_assoc in H1.
              specialize (H1 H2).
              destruct H1.

              assert (last (List.map destination (l1 ++ [x])) start = destination x). {
                 rewrite map_app.
                 rewrite last_app.
                 simpl.
                 reflexivity.
              }

              rewrite <- H5.
              assumption.
              rewrite Hconcat in Hlst.
              rewrite map_app in Hlst.
              rewrite last_app in Hlst.
              rewrite map_cons in Hlst.
              rewrite unroll_last in Hlst.
              assumption.
            }

            specialize (Hpersists Hfutures (fst m) _ Hproject).
            apply Is_true_iff_eq_true, existsb_exists.
            exists (snd m).
            split; try assumption.
            rewrite state_eqb_eq.
            reflexivity.
    Qed.

    Lemma not_send_oracle_prop
      (s : state)
      (Hprotocol : protocol_state_prop preX s)
      (m : message) :
      has_not_been_sent_prop X not_send_oracle s m.
    Proof.
      intros.
      unfold has_not_been_sent_prop.
      unfold no_traces_have_message_prop.
      unfold selected_message_exists_in_no_preloaded_trace,
          specialized_selected_message_exists_in_no_trace.
      split.
      - intros.
        unfold not_send_oracle in H.
        rewrite <- Forall_Exists_neg.
        rewrite Forall_forall.
        intros.
        intros contra.
        assert (In (snd m) (get_history' s index_self)). {
          specialize (output_to_history s start m tr).
          intros.
          specialize (H1 Htr Hlast).
          assert (List.Exists (fun elem : transition_item => output elem = Some m) tr). {
            rewrite Exists_exists.
            exists x.
            split.
            assumption.
            assumption.
          }
          specialize (H1 H2).
          assumption.
        }
        unfold send_oracle in H.
        destruct (decide (fst m = index_self)).
        + destruct s.
          * simpl in H1.
            assumption.
          * apply negb_prop_intro, Is_true_iff_eq_true in H.
            rewrite negb_true_iff, existsb_forall in H.
            specialize (H (snd m)).
            rewrite <- e in H1.
            specialize (H H1).
            rewrite state_eqb_neq in H.
            elim H.
            reflexivity.
        + specialize (emitted_messages_only_from_self m).
          assert (can_emit preX m). {
             specialize (can_emit_from_protocol_trace preX start m tr Htr).
             intros.
             apply H2.
             rewrite Exists_exists.
             exists x.
             split.
             assumption.
             assumption.
          }
          intros.
          specialize (H3 H2).
          elim n.
          assumption.
      - intros.
        unfold not_send_oracle.
        intro send_oracle_eq.
        + exfalso.
          specialize (send_oracle_prop s Hprotocol m).
          intros.
          unfold has_been_sent_prop in H0.
          unfold all_traces_have_message_prop in H0.
          destruct H0.
          specialize (H0 send_oracle_eq).
          simpl in *.
          specialize (protocol_is_trace preX).
          simpl.
          intros.
          destruct Hprotocol as [Hleft Hright].
          specialize (H2 s Hleft Hright).
          destruct H2.
          * specialize (H0 s []).
            simpl in *.
            assert (finite_protocol_trace (pre_loaded_with_all_messages_vlsm X) s []). {
                unfold finite_protocol_trace.
                simpl.
                split.
                - apply finite_ptrace_empty.
                  unfold protocol_state_prop.
                  exists Hleft.
                  assumption.
                - assumption.
            }

            specialize (H0 H3 eq_refl).
            rewrite Exists_exists in H0.
            simpl in H0.
            destruct H0 as [x [Hfalse Hother]].
            assumption.
          * destruct H2 as [start [tr [Htr Hothers]]].
            destruct Hothers as [Hdest Houtput].
            assert (Hlst := last_error_destination_last tr s Hdest start).
            specialize (H start tr Htr Hlst).
            specialize (H0 start tr Htr Hlst).
            rewrite Exists_exists in H0.
            destruct H0 as [x [Hin Hm]].
            rewrite <- Forall_Exists_neg in H.
            rewrite Forall_forall in H.
            specialize (H x Hin).
            elim H.
            assumption.
    Qed.

    Lemma not_receive_oracle_prop
      (s : state)
      (Hprotocol : protocol_state_prop preX s)
      (m : message) :
      has_not_been_received_prop X not_receive_oracle s m.
     Proof.
      intros.
      unfold has_not_been_received_prop.
      unfold no_traces_have_message_prop.
      unfold selected_message_exists_in_no_preloaded_trace,
          specialized_selected_message_exists_in_no_trace.
      split.
      - intros.
        unfold not_receive_oracle in H.
        rewrite <- Is_true_iff_eq_true in H.
        apply not_true_is_false in H.
        rewrite <- Forall_Exists_neg.
        rewrite Forall_forall.
        intros.
        intros contra.
        assert (In (snd m) (get_history' s (fst m))). {
          specialize (input_to_history s start m tr).
          intros.
          specialize (H1 Htr Hlast).
          assert (List.Exists (fun elem : transition_item => input elem = Some m) tr). {
            rewrite Exists_exists.
            exists x.
            split.
            assumption.
            assumption.
          }
          specialize (H1 H2).
          assumption.
        }
        unfold receive_oracle in H.
        destruct (decide (fst m = index_self)).
        * apply in_split in H0.
          destruct H0 as [l1 [l2 Hconcat]].
          remember (last (List.map destination l1) start) as prev_x.
          specialize (protocol_transition_to preX start x tr l1 l2 Hconcat).
          destruct Htr.
          intros.
          specialize (H3 H0).
          simpl in *.
          unfold protocol_transition in H3.
          destruct H3 as [Hvalid Htransition].
          unfold protocol_valid in Hvalid.
          simpl in *.
          destruct (l x).
          destruct Hvalid as [Ha [Hb [Hc Hd]]].
          rewrite Hd in contra.
          discriminate contra.
          rewrite contra in Hvalid.
          destruct Hvalid as [Ha [Hb [Hc [Hd He]]]].
          elim He.
          symmetry.
          assumption.
        * rewrite existsb_forall in H.
          specialize (H (snd m) H1).
          rewrite state_eqb_neq in H.
          elim H.
          reflexivity.
      - intros.
        unfold not_receive_oracle.
        intro receive_oracle_eq.
        + exfalso.
          specialize (receive_oracle_prop s Hprotocol m).
          intros.
          unfold has_been_received_prop in H0.
          unfold all_traces_have_message_prop in H0.
          destruct H0.
          specialize (H0 receive_oracle_eq).
          simpl in *.
          specialize (protocol_is_trace preX).
          simpl.
          intros.
          destruct Hprotocol as [Hleft Hright].
          specialize (H2 s Hleft Hright).
          destruct H2.
          * specialize (H0 s []).
            simpl in *.
            assert (finite_protocol_trace (pre_loaded_with_all_messages_vlsm X) s []). {
                unfold finite_protocol_trace.
                simpl.
                split.
                - apply finite_ptrace_empty.
                  unfold protocol_state_prop.
                  exists Hleft.
                  assumption.
                - assumption.
            }

            specialize (H0 H3 eq_refl).
            rewrite Exists_exists in H0.
            simpl in H0.
            destruct H0 as [x [Hfalse Hother]].
            assumption.
          * destruct H2 as [start [tr [Htr Hothers]]].
            destruct Hothers as [Hdest Houtput].
            assert (Hlst := last_error_destination_last tr s Hdest start).
            specialize (H start tr Htr Hlst).
            specialize (H0 start tr Htr Hlst).
            rewrite Exists_exists in H0.
            destruct H0 as [x [Hin Hm]].
            rewrite <- Forall_Exists_neg in H.
            rewrite Forall_forall in H.
            specialize (H x Hin).
            elim H.
            assumption.
    Qed.
    
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

    Global Instance has_been_sent_lv : (has_been_sent_capability X) := {
      has_been_sent := send_oracle;
      proper_sent := send_oracle_prop;
      proper_not_sent := not_send_oracle_prop;
    }.

   Global Instance has_been_received_lv : (has_been_received_capability X) := {
      has_been_received := receive_oracle;
      proper_received := receive_oracle_prop;
      proper_not_received := not_receive_oracle_prop;
    }.

    Definition get_messages_from_history (s : state) (i : index) : set message :=
      List.map (pair i) (get_history' s i).

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
      In m (get_messages_from_history s (fst m)) <-> In (snd m) (get_history' s (fst m)).
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

    Lemma in_history_is_protocol
      (s s': state)
      (Hprotocol : protocol_state_prop preX s)
      (Hin : In s'(get_history' s index_self)) :
      protocol_state_prop preX s'.
    Proof.
      assert (send_oracle s (index_self, s')). {
        unfold send_oracle.
        simpl.
        destruct (decide (index_self = index_self)).
        - apply Is_true_iff_eq_true.
          rewrite existsb_exists.
          exists s'.
          split.
          assumption.
          rewrite state_eqb_eq.
          reflexivity.
        - elim n. reflexivity.
      }

      specialize (send_oracle_prop s Hprotocol (index_self, s')).
      intros.
      unfold has_been_sent_prop in H0.
      unfold all_traces_have_message_prop in H0.
      destruct H0 as [H0 _].
      specialize (H0 H).
      unfold protocol_state_prop in Hprotocol.
      destruct Hprotocol as [om Hprotocol].
      specialize (protocol_is_trace preX s om Hprotocol).
      intros.
      destruct H1.
      - simpl in *.
        unfold vinitial_state_prop in H1.
        simpl in H1.
        unfold initial_state_prop in H1.
        destruct H1 as [cv Heqinit].
        rewrite Heqinit in Hin.
        unfold get_history' in Hin.
        unfold last_recorded in Hin.
        rewrite project_all_bottom in Hin.
        simpl in Hin.
        exfalso.
        assumption.
      - destruct H1 as [si [tr [Htr [Hdest Hm]]]].
        specialize (H0 si tr Htr).

        assert (Hlst := last_error_destination_last tr s Hdest si).

        specialize (H0 Hlst).
        rewrite Exists_exists in H0.
        destruct H0 as [x [Hin_x Houtput]].
        apply in_split in Hin_x.
        destruct Hin_x as [l1 [l2 Hconcat]].

        remember (last (List.map destination l1) si) as prev_x.
        destruct Htr.
        specialize (protocol_transition_to preX si x tr l1 l2 Hconcat H0).
        intros.
        simpl in H2.

        unfold protocol_transition in H2.
        destruct H2 as [Hvalid Htransition].
        unfold protocol_valid in Hvalid.
        destruct Hvalid as [Hneed Hother].

        assert (last (map destination l1) si = s'). {
          simpl in *.
          unfold vtransition in Htransition.
          simpl in *.
          destruct (l x) eqn : eq_l.
          - inversion Htransition.
            rewrite Houtput in H4.
            inversion H4.
            reflexivity.
          - destruct (input x).
            + inversion Htransition.
              rewrite Houtput in H4.
              discriminate H4.
            + inversion Htransition.
              rewrite Houtput in H4.
              discriminate H4.
        }
        rewrite <- H2.
        assumption.
    Qed.

    Definition state_gt
      (s1 s2 : state)
      : Prop
      := state_lt s2 s1.

    Lemma state_gt_tran
      (s1 s2 s3 : state)
      (H12 : state_gt s1 s2)
      (H23 : state_gt s2 s3)
      : state_gt s1 s3.
    Proof.
      unfold state_gt in *.
      specialize (state_lt_tran s3 s2 s1).
      intros.
      intuition.
    Qed.

    Lemma get_history'_self_Lsorted_le
      (s : state)
      (Hprotocol : protocol_state_prop preX s) :
      LocallySorted state_gt (get_history' s index_self).
    Proof.
      remember ((get_history' s index_self)) as history.
      symmetry in Heqhistory.
      generalize dependent s.
      induction history.
      - intros.
        apply LSorted_nil.
      - intros.
        destruct history; try apply LSorted_cons1.
        specialize (IHhistory a).
        specialize (in_history_is_protocol s a Hprotocol) as Hprotocola .
        spec Hprotocola.
        { rewrite Heqhistory. left. reflexivity. }
        spec IHhistory Hprotocola.
        apply LSorted_consn.
        + apply IHhistory.
          symmetry.
          apply unfold_history with (s1 := s) (pref := []). assumption.
        + apply unfold_history_cons_iff in Heqhistory.
          destruct Heqhistory as [Ha Heqhistory].
          subst a.
          symmetry in Heqhistory.
          specialize (no_bottom_in_history (project s index_self) s0 index_self) as Hnb.
          rewrite Heqhistory in Hnb.
          spec Hnb; try (left; reflexivity).
          apply unfold_history_cons_iff in Heqhistory.
          destruct Heqhistory as [Hs0 Heqhistory].
          subst s0.
          unfold state_gt.
          apply state_lt_last_sent; assumption.
    Qed.

    Lemma get_history'_comparable
      (s s1 s2 : state)
      (Hprotocol : protocol_state_prop preX s)
      (Hs1 : In s1 (get_history' s index_self))
      (Hs2 : In s2 (get_history' s index_self))
      : s1 = s2 \/ state_lt s1 s2 \/ state_lt s2 s1.
    Proof.
      remember (get_history' s index_self) as history.
      specialize (lsorted_pair_wise_unordered history state_gt).
      intros.
      spec H.
      rewrite Heqhistory.
      apply get_history'_self_Lsorted_le.
      assumption.
      specialize (H state_gt_tran s1 s2 Hs1 Hs2).
      unfold state_gt in H.
      intuition.
    Qed.
    (*
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
      
    Definition get_raw_observations (s : state) (target : index) : set state :=
      get_observations target (depth s) s.
      
    Lemma raw_observations_consensus 
      (s : state)
      (b : bool)
      (target : index) :
      get_raw_observations s target = get_raw_observations (update_consensus s b) target.
    Proof.
      unfold get_raw_observations.
      assert (depth s = depth (update_consensus s b)) by (destruct s;intuition). 
      rewrite <- H.
      unfold get_observations.
      destruct (depth s); destruct s; intuition.
    Qed.
    
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
         f_equal. f_equal. f_equal.
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

        assert (d >= depth a) by lia.

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
      (NoDup (get_raw_observations s target)).
    Proof.
      unfold get_raw_observations.
      remember (depth s) as d.
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
         + rewrite decide_False by congruence.
           symmetry in Heqd.
           apply depth_zero_bottom in Heqd.
           rewrite Heqd.
           apply NoDup_nil.
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
        specialize (H (depth x) H1 x eq_refl).
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
    
      Lemma unfold_raw_observations
      (s s': state)
      (Hnb : s <> Bottom)
      (target : index) :
      In s' (get_raw_observations s target) ->
      (project s target = s') \/
      (exists (i : index), (In s' (get_raw_observations (project s i) target))).
  Proof.
      - intros.
        unfold get_raw_observations in H.
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
   Qed.
   
     Lemma refold_raw_observations1
      (s s': state)
      (Hnb : s <> Bottom /\ s' <> Bottom)
      (target : index) :
      (project s target = s') ->
      In s' (get_raw_observations s target).
    Proof.
      - intros.
        destruct H.
        unfold get_raw_observations.
        destruct s.
        intuition.
        destruct (depth (Something b is)) eqn : eq_d.
        apply depth_zero_bottom in eq_d.
        discriminate eq_d.
        apply set_remove_3.
        apply set_union_intro.
        right.
        simpl.
        intuition.
        intuition.
     Qed.
     
     Lemma refold_raw_observations2
      (s s': state)
      (Hnb : s <> Bottom)
      (target : index) :
      (exists (i : index), (In s' (get_raw_observations (project s i) target))) ->
      In s' (get_raw_observations s target).
     Proof.
        intros.
        unfold get_raw_observations.
        destruct s.
        intuition.
        destruct (depth (Something b is)) eqn : eq_d.
        apply depth_zero_bottom in eq_d.
        discriminate eq_d.
        apply set_remove_3.
        apply set_union_intro.
        left.
        apply set_union_in_iterated.
        rewrite Exists_exists.
        destruct H as [i Hin_i].
        exists (get_raw_observations (project (Something b is) i) target).
        split.
        rewrite in_map_iff.
        exists (project (Something b is) i).
        split.
        rewrite get_observations_depth_redundancy.
        unfold get_observations.
        reflexivity.
        specialize (@depth_parent_child index index_listing Hfinite idec is b i) as Hdpc.
        unfold project.
        lia.
        rewrite in_map_iff.
        exists i.
        split.
        reflexivity.
        apply ((proj2 Hfinite) i).
        intuition.
        destruct H as [i Hini].
        apply no_bottom_in_observations in Hini.
        intuition.
    Qed.
    
    Lemma raw_observations_in_project
      (s : state)
      (Hsnb : s <> Bottom)
      (target i : index)
      : incl (get_raw_observations (project s i) target) (get_raw_observations s target).
    Proof.
      unfold incl. intros e H.
      apply refold_raw_observations2.
      intuition.
      exists i.
      intuition.
    Qed.
    
    Lemma something_in_obs_nb 
      (s s' : state)
      (i : index)
      (Hin : In s' (get_raw_observations s i)) :
      s <> Bottom.
    Proof.
      unfold get_raw_observations in Hin.
      unfold get_observations in Hin.
      destruct s.
      - simpl in Hin. intuition.
      - congruence.
    Qed.
    
    Lemma cross_observations
      (s s1 s2: state)
      (i j : index)
      (Hin1 : In s1 (get_raw_observations s i))
      (Hin2 : In s2 (get_raw_observations s1 j)) :
      In s2 (get_raw_observations s j).
    Proof.
      remember (depth s) as dpth.
      generalize dependent s.
      generalize dependent s1.
      generalize dependent s2.
      induction dpth using (well_founded_induction lt_wf).
      intros.
      assert (Hsnb : s <> Bottom). {
        apply something_in_obs_nb in Hin1.
        intuition.
      }
      apply unfold_raw_observations in Hin1.
      2 : intuition.

      destruct Hin1 as [Hin1 | Hin1].
      - rewrite <- Hin1 in Hin2.
        apply raw_observations_in_project in Hin2.
        all : intuition.
      - destruct Hin1 as [k Hink].
        specialize (H (depth (project s k))) as Hproj.
        spec Hproj. {
          unfold project.
          rewrite Heqdpth.
          destruct s; [intuition|].
          apply (@depth_parent_child index index_listing).
          intuition.
        }
        
        specialize (Hproj s2 s1 Hin2 (project s k) Hink eq_refl).
        apply raw_observations_in_project in Hproj.
        intuition.
        intuition.
    Qed.
 

    Definition shallow_observations (s : state) (target : index) :=
      get_observations target 1 s.
    
    Inductive simp_lv_event_type : Type :=
    | State'
    | Message'.
    
    Global Instance simp_event_type_eq_dec : EqDecision simp_lv_event_type.
      solve_decision.
    Defined. 
    
    Inductive simp_lv_event : Type :=
      SimpObs: simp_lv_event_type -> index -> (@state index index_listing) -> simp_lv_event.
    
    Global Instance simp_event_eq_dec : EqDecision simp_lv_event.
      solve_decision.
    Defined. 
    
    Definition get_simp_event_subject (e : simp_lv_event) : index :=
    match e with 
      SimpObs type subject state => subject
    end.
    
    Definition get_simp_event_type (e : simp_lv_event) :=
      match e with
       SimpObs type subject state => type
      end.
      
    Definition get_simp_event_state (e : simp_lv_event) :=
      match e with
        SimpObs type subject state => state
      end.
      
    Definition simp_lv_event_comp_eq 
      (e : simp_lv_event) :
      e = SimpObs (get_simp_event_type e) (get_simp_event_subject e) (get_simp_event_state e).
    Proof.
      destruct e.
      simpl.
      reflexivity.
    Qed.
    
    Definition simp_lv_event_lt (e1 e2 : simp_lv_event) : Prop :=
    match e1, e2 with
      SimpObs type1 subject1 state1, SimpObs type2 subject2 state2 =>
        match decide_eq subject1 subject2 with
        | right _ => False
        | _ => match type1, type2 with
               | State', Message' => False
               | _, _ => state_lt' subject1 state1 state2
               end  
        end
    end.
    
    Lemma simp_lv_event_lt_dec : RelDecision simp_lv_event_lt.
    Proof.
      unfold RelDecision. intros.
      unfold Decision.
      unfold simp_lv_event_lt.
      destruct x as [type1 subject1 state1]; destruct y as [type2 subject2 state2].
      destruct (decide (subject1 = subject2)).
      - destruct type1 eqn : eq1; destruct type2 eqn : eq2.
        + exact (state_lt'_dec subject1 state1 state2).
        + right; auto.
        + exact (state_lt'_dec subject1 state1 state2).
        + exact (state_lt'_dec subject1 state1 state2).
      - right. auto.
    Qed.
      
    Definition simp_lv_state_observations (s : state) (target : index) : set simp_lv_event :=
      match decide_eq target index_self with
      | left _ => [SimpObs State' index_self s]
      | right _ => []
      end.
    
    Definition simp_lv_message_observations (s : state) (target : index) : set simp_lv_event :=
      List.map (SimpObs Message' target) (get_raw_observations s target).
    
    Definition simp_lv_observations (s : state) (target : index) : set simp_lv_event :=
      set_union decide_eq (simp_lv_message_observations s target) (simp_lv_state_observations s target).
    
    Lemma cons_clean_message_obs 
      (s : state)
      (target : index)
      (b : bool) : 
      simp_lv_message_observations s target = simp_lv_message_observations (update_consensus s b) target.
    Proof.
      unfold simp_lv_message_observations.
      rewrite raw_observations_consensus with (b := b).
      intuition.
    Qed.
    
    Lemma in_simp_lv_message_observations
      (s : state)
      (target : index)
      (e : simp_lv_event)
      (Hin : In e (simp_lv_message_observations s target)) :
      get_simp_event_type e = Message' /\ get_simp_event_subject e = target.
    Proof.
      unfold simp_lv_message_observations in *.
      apply in_map_iff in Hin.
      destruct Hin as [x [Heqx Hinx]].
      rewrite <- Heqx; intuition.
    Qed.
    
    Lemma in_simp_lv_state_observations
      (s : state)
      (target : index)
      (e : simp_lv_event)
      (Hin : In e (simp_lv_state_observations s target)) :
      get_simp_event_type e = State' /\ get_simp_event_subject e = target.
    Proof.
      unfold simp_lv_state_observations in *.
      destruct (decide (target = index_self)).
      - simpl in Hin.
        destruct Hin.
        rewrite <- H.
        all : intuition.
      - intuition.
    Qed.
    
    Lemma in_simp_lv_message_observations'
      (s : state)
      (target : index)
      (e : simp_lv_event)
      (Hin : In e (simp_lv_message_observations s target)) :
      In e (simp_lv_observations s target).
    Proof.
      unfold simp_lv_observations.
      apply set_union_iff.
      left. intuition.
    Qed.
    
    Lemma in_simp_lv_state_observations'
      (s : state)
      (target : index)
      (e : simp_lv_event)
      (Hin : In e (simp_lv_state_observations s target)) :
      In e (simp_lv_observations s target).
    Proof.
      unfold simp_lv_observations.
      apply set_union_iff.
      right. intuition.
    Qed.
    
    Lemma in_simp_lv_observations
      (s : state)
      (target : index)
      (e : simp_lv_event)
      (Hin : In e (simp_lv_observations s target)) :
      get_simp_event_subject e = target.
    Proof.
      unfold simp_lv_observations in Hin.
      apply set_union_iff in Hin.
      destruct Hin.
      - apply in_simp_lv_message_observations in H. intuition.
      - apply in_simp_lv_state_observations in H. intuition.
    Qed.
       
   Lemma in_and_message
    (s : state)
    (target : index)
    (e : simp_lv_event)
    (Hin : In e (simp_lv_observations s target))
    (Hm : get_simp_event_type e = Message') :
    In e (simp_lv_message_observations s target).
  Proof.
    unfold simp_lv_observations in Hin.
    apply set_union_iff in Hin.
    destruct Hin.
    - intuition.
    - apply in_simp_lv_state_observations in H.
      destruct H as [H _].
      congruence. 
  Qed.
  
  Lemma in_and_state
    (s : state)
    (target : index)
    (e : simp_lv_event)
    (Hin : In e (simp_lv_observations s target))
    (Hm : get_simp_event_type e = State') :
    In e (simp_lv_state_observations s target).
  Proof.
    unfold simp_lv_observations in Hin.
    apply set_union_iff in Hin.
    destruct Hin.
    - apply in_simp_lv_message_observations in H.
      destruct H as [H _].
      congruence.
    - intuition. 
  Qed.
    
    Lemma simp_lv_observations_other 
      (s : state)
      (target : index)
      (Hdif : target <> index_self) :
      simp_lv_observations s target = simp_lv_message_observations s target.
    Proof.
      unfold simp_lv_observations.
      unfold simp_lv_state_observations.
      rewrite decide_False by intuition.
      simpl; reflexivity.
    Qed.
    
    Definition get_simp_event_subject_some 
      (e : simp_lv_event) :=
      Some (get_simp_event_subject e).
    
    Program Instance simp_lv_observable_events :
      observable_events (@state index index_listing) simp_lv_event := 
      state_observable_events_instance 
      (@state index index_listing)
      index
      simp_lv_event
      decide_eq
      simp_lv_observations
      (fun (s : state) => index_listing).
      
    Program Instance simp_observable_full :
      (observation_based_equivocation_evidence
       (@state index index_listing)
       index
       simp_lv_event
       simp_lv_observable_events
       decide_eq 
       simp_lv_event_lt
       simp_lv_event_lt_dec 
       get_simp_event_subject_some).
   
   Existing Instance simp_observable_full.

   Definition get_validators {State : Type} (s : State) : list index := index_listing.

   Lemma get_validators_nodup
    {State : Type}
    (s : State) :
    NoDup (get_validators s).
   Proof.
    unfold get_validators.
    apply Hfinite.
   Qed.

  Program Definition simp_lv_basic_equivocation : basic_equivocation state index :=
      @basic_observable_equivocation
      (@state index index_listing)
      index
      simp_lv_event
      decide_eq
      simp_lv_event_lt
      simp_lv_event_lt_dec
      simp_lv_observable_events
      (fun (e : simp_lv_event) => Some (get_simp_event_subject e))
      simp_observable_full
      _
      Mindex
      Rindex
      get_validators
      get_validators_nodup.
  Next Obligation.
    apply observable_events_equivocation_evidence_dec.
    apply idec.
  Defined.

  Existing Instance simp_lv_basic_equivocation.  
    
    Lemma message_cross_observations
      (s : state)
      (e1 e2 : simp_lv_event)
      (i j : index)
      (Hin1 : In e1 (simp_lv_message_observations s i))
      (Hin2 : In e2 (simp_lv_message_observations (get_simp_event_state e1) j)) :
      In e2 (simp_lv_message_observations s j).
    Proof.
      destruct e1 as [et1 ev1 es1].
      destruct e2 as [et2 ev2 es2].
      unfold simp_lv_message_observations in *.
      apply in_map_iff in Hin1.
      destruct Hin1 as [s1 [Heq1 Hraw1]].
      apply in_map_iff in Hin2.
      destruct Hin2 as [s2 [Heq2 Hraw2]].
      inversion Heq1.
      inversion Heq2.
      subst et1. subst ev1. subst es1.
      subst et2. subst ev2. subst es2.
      simpl in *.
      apply in_map_iff.
      exists s2.
      split;[intuition|]. 
      apply cross_observations with (s1 := s1) (i := i).
      intuition.
      intuition.
    Qed.
    
    Lemma raw_message
      (s s' : state)
      (target : index) :
      In (SimpObs Message' target s') (simp_lv_message_observations s target) <-> In s' (get_raw_observations s target).
    Proof.
      split; intros; unfold simp_lv_message_observations in *. 
      - apply in_map_iff in H.
        destruct H as [x [Heqx Hinx]].
        inversion Heqx.
        rewrite <- H0; intuition.
      - apply in_map_iff.
        exists s'.
        intuition.
    Qed.
   
   Lemma in_message_observations_nb
    (s : state)
    (target : index)
    (e : simp_lv_event) 
    (Hin : In e (simp_lv_message_observations s target)) :
    get_simp_event_state e <> Bottom.
    Proof.
      unfold simp_lv_message_observations in Hin.
      apply in_map_iff in Hin.
      destruct Hin as [es [Hes Hines]].
      apply no_bottom_in_observations in Hines.
      rewrite <- Hes.
      intuition.
    Qed.
   
   Lemma unfold_simp_lv_observations
      (s : state)
      (Hnb : s <> Bottom)
      (target : index)
      (e : simp_lv_event)  :
      In e (simp_lv_message_observations s target) ->
      (e = SimpObs Message' target (project s target)) \/
      (exists (i : index), (In e (simp_lv_message_observations (project s i) target))).
   Proof.
      destruct e as [et ev es].
      intros.
      apply in_simp_lv_message_observations in H as H'.
      assert (et = Message') by intuition.
      assert (ev = target) by intuition.
      subst et. subst ev.
      apply raw_message in H as Hraw. 
      apply unfold_raw_observations in Hraw.
      2 : {
        intuition.
      }
      destruct Hraw.
        - left. rewrite H0. intuition.
        - right.
          destruct H0 as [i Hini].
          exists i.
          apply raw_message in Hini.
          intuition.
   Qed.
   
    Lemma refold_simp_lv_observations1
      (s : state)
      (Hprs : s <> Bottom)
      (target : index)
      (Hnb : project s target <> Bottom)
      (e : simp_lv_event)  :
      (e = SimpObs Message' target (project s target)) ->
      In e (simp_lv_message_observations s target).
    Proof.
      intros.
      unfold simp_lv_message_observations.
      apply in_map_iff.
      exists (project s target).
      rewrite H.
      intuition.
      apply refold_raw_observations1.
      all : intuition.
    Qed.
    
    Lemma refold_simp_lv_observations2
      (s : state)
      (Hnb : s <> Bottom)
      (target : index)
      (e : simp_lv_event) :
      (exists (i : index), (In e (simp_lv_message_observations (project s i) target))) ->
      In e (simp_lv_message_observations s target).
   Proof.
     intros.
     destruct H as [i Hine].
     unfold simp_lv_message_observations in *.
     apply in_map_iff.
     apply in_map_iff in Hine.
     destruct Hine as [x Hinx].
     exists x.
     intuition.
     apply refold_raw_observations2.
     intuition.

     exists i; intuition.
   Qed.
  
  Lemma in_history_in_observations
    (s es : state)
    (target : index)
    (Hin : In es (get_history' s target)) :
    In (SimpObs Message' target es) (simp_lv_message_observations s target).
  Proof.
    remember (get_history' s target) as l.
    generalize dependent s.
    induction l.
    - intros. intuition.
    - intros.
      
      assert (Hnb : s <> Bottom /\ (project s target) <> Bottom). {
        rewrite Heql in Hin.
        split.
        - destruct s; simpl in Hin;[intuition|congruence].
        - destruct (project s target) eqn : eq.
          + unfold get_history' in Hin. destruct s. intuition. unfold last_recorded in Hin.
          unfold project in eq. rewrite eq in Hin. intuition.
          + congruence.
      }
    
      rewrite unfold_history_cons in Heql by intuition.
      inversion Heql.
      simpl in Hin.
      destruct Hin as [Hin|Hin].
      + subst a.
        subst es.
        apply in_map_iff.
        exists (project s target).
        split.
        * intuition.
        * apply refold_raw_observations1.
          all : intuition.
      + specialize (IHl Hin (project s target) H1).
         apply refold_simp_lv_observations2.
         intuition.
         exists target.
         intuition.
  Qed.
  
  Lemma old_incl_new
    (s so : state)
    (Hnb : s <> Bottom /\ so <> Bottom)
    (i j : index)
    (Hfull : project s i = project so i)
    (s' := (update_state s so i)) :
    incl (simp_lv_message_observations s j) (simp_lv_message_observations s' j).
  Proof.
    
    assert (Hs'nb : s' <> Bottom). {
      unfold s'.
      unfold update_state.
      destruct s; intuition congruence.
    }
  
    unfold incl.
    intros e H.
    unfold simp_lv_message_observations in *.
    apply in_map_iff in H.
    destruct H as [es' Hinx].
      
    destruct Hinx as [Heqe Hines'].
    
    assert (Hes'nb : es' <> Bottom). {
      apply no_bottom_in_observations in Hines'.
      intuition.
    }  
    
    apply in_map_iff.
    exists es'.
    split. intuition.
    unfold s'.
    destruct (decide(i = j)).
    - subst i.
      apply unfold_raw_observations in Hines' as Hraw'.
      2 : intuition.
      destruct Hraw'.
      + apply refold_raw_observations2.
        intuition.
        exists j.
        rewrite (@project_same index index_listing Hfinite) by intuition.
        apply refold_raw_observations1.
        intuition.
        rewrite <- Hfull.
        intuition.
      + destruct H as [k Hink].
        apply refold_raw_observations2.
        intuition.
        exists k.
        destruct (decide (k = j)).
        * subst k.
          rewrite (@project_same index index_listing Hfinite) by intuition.
          apply refold_raw_observations2.
          intuition.
          exists j.
          rewrite <- Hfull.
          intuition.
        * rewrite (@project_different index index_listing Hfinite) by intuition.
          intuition.
    - apply unfold_raw_observations in Hines'.
      2 : intuition.
      destruct Hines'.
      + apply refold_raw_observations1.
        intuition.
        rewrite (@project_different index index_listing) by intuition.
        intuition.
      + destruct H as [k Hink].
        apply refold_raw_observations2.
        intuition.
        destruct (decide (k = i)).
        * subst k.
          exists i.
          rewrite (@project_same index index_listing) by intuition.
          apply refold_raw_observations2.
          intuition.
          exists i.
          rewrite <- Hfull.
          intuition.
        * exists k.
          rewrite (@project_different index index_listing) by intuition.
          intuition.
    Qed.
    
   Lemma received_incl_new
    (s so : state)
    (Hnb : s <> Bottom /\ so <> Bottom)
    (i j : index)
    (Hfull : project s i = project so i)
    (s' := (update_state s so i)) :
    incl (simp_lv_message_observations so j) (simp_lv_message_observations s' j).
   Proof.
    assert (Hs'nb : s' <> Bottom). {
      unfold s'.
      unfold update_state.
      destruct s; intuition congruence.
    }
   
    unfold incl. intros e H.
    unfold s'.
    unfold simp_lv_message_observations in *.
    apply in_map_iff in H.
    destruct H as [es' Hines'].
    destruct Hines' as [Heqe Hines'].
    
    assert (es' <> Bottom). {
      apply no_bottom_in_observations in Hines'.
      intuition.
    }
    
    apply in_map_iff.
    exists es'. 
    split; [intuition|].
    apply refold_raw_observations2.
    intuition.
    exists i.
    rewrite (@project_same index index_listing Hfinite) by intuition.
    intuition.
   Qed.
   
   Lemma new_incl_rest_diff
    (s so : state)
    (Hnb : s <> Bottom /\ so <> Bottom)
    (i j : index)
    (Hdif : i <> j)
    (Hfull : project s i = project so i)
    (s' := (update_state s so i)) :
    let s1 := simp_lv_message_observations s j in
    let all := set_union decide_eq s1 (simp_lv_message_observations so j) in
    incl (simp_lv_message_observations s' j) all.
   Proof.
    unfold incl. intros e H.
    unfold s' in H.
    apply in_message_observations_nb in H as Hesnb.
    apply unfold_simp_lv_observations in H as Hraw.
    2 : {
      unfold update_state; destruct s; intuition congruence.
    }
    apply set_union_iff.
    destruct Hraw.
    - destruct (decide (i = j)).
      + congruence.
      + rewrite (@project_different index index_listing Hfinite) in H0 by intuition.
        left.
        apply refold_simp_lv_observations1;[intuition|..].
        rewrite H0 in Hesnb; simpl in Hesnb.
        all : intuition.
    - destruct H0 as [k Hink].
       destruct (decide (k = i)).
       + subst k.
          rewrite (@project_same index index_listing Hfinite) in Hink by intuition.
          right.
          intuition.
       +  rewrite (@project_different index index_listing Hfinite) in Hink by intuition.
          left.
          apply refold_simp_lv_observations2;[intuition|..].
          exists k. 
          intuition.
   Qed.
  
  Lemma new_incl_rest_same
    (s so : state)
    (Hnb : s <> Bottom /\ so <> Bottom)
    (i : index)
    (Hfull : project s i = project so i)
    (s' := (update_state s so i)) :
    let s1 := simp_lv_message_observations s i in
    let s2 := set_union decide_eq s1 (simp_lv_message_observations so i) in
    let all := set_union decide_eq s2 [SimpObs Message' i so] in
    incl (simp_lv_message_observations s' i) all.
   Proof.
    unfold incl. intros e H.
    unfold s' in H.
    apply in_message_observations_nb in H as Hesnb.
    apply unfold_simp_lv_observations in H as Hraw.
    2 : {
      unfold update_state; destruct s; intuition congruence.
    }
    apply set_union_iff.
    destruct Hraw.
    - rewrite (@project_same index index_listing Hfinite) in H0 by intuition.
      right. rewrite H0. intuition.
    - destruct H0 as [k Hink].
       destruct (decide (k = i)).
       + subst k.
          rewrite (@project_same index index_listing Hfinite) in Hink by intuition.
          left.
          apply set_union_iff.
          right. intuition.
       +  rewrite (@project_different index index_listing Hfinite) in Hink by intuition.
          left.
          apply set_union_iff.
          left.
          apply refold_simp_lv_observations2;[intuition|..].
          exists k. 
          intuition.
  Qed. 
   
   Lemma new_incl_rest
    (s so : state)
    (Hnb : s <> Bottom /\ so <> Bottom)
    (i j : index)
    (Hfull : project s i = project so i)
    (s' := (update_state s so i)) :
    let s1 := simp_lv_message_observations s j in
    let s2 := set_union decide_eq s1 (simp_lv_message_observations so j) in
    let all := set_union decide_eq s2 [SimpObs Message' j so] in
    incl (simp_lv_message_observations s' j) all.
   Proof.
    unfold incl. intros e H.
    unfold s' in H.
    apply in_message_observations_nb in H as Hesnb.
    apply unfold_simp_lv_observations in H as Hraw.
    2 : {
      unfold update_state; destruct s; intuition congruence.
    }
    apply set_union_iff.
    destruct Hraw.
    - destruct (decide (i = j)).
      + subst j.
        rewrite (@project_same index index_listing Hfinite) in H0 by intuition.
        right. rewrite H0. intuition.
      + rewrite (@project_different index index_listing Hfinite) in H0 by intuition.
        left.
        apply set_union_iff.
        left.
        apply refold_simp_lv_observations1;[intuition|..].
        rewrite H0 in Hesnb; simpl in Hesnb.
        all : intuition.
    - destruct H0 as [k Hink].
       destruct (decide (k = i)).
       + subst k.
          rewrite (@project_same index index_listing Hfinite) in Hink by intuition.
          left.
          apply set_union_iff. 
          right.
          intuition.
       + rewrite (@project_different index index_listing Hfinite) in Hink by intuition.
          left.
          apply set_union_iff.
          left.
          apply refold_simp_lv_observations2;[intuition|..].
          exists k. intuition.
  Qed.

  Lemma state_obs_stuff
    (s so : state)
    (Hnb : s <> Bottom /\ so <> Bottom)
    (i : index)
    (Hfull : project s i = project so i)
    (s' := update_state s so i)
    (s_obs := (SimpObs State' index_self s))
    (s'_obs := (SimpObs State' index_self s')) 
    (e : simp_lv_event)
    (Hns : get_simp_event_type e <> State') 
    (Hsubj : get_simp_event_subject e = index_self)
    (Hcomp: comparable simp_lv_event_lt e s_obs) :
    comparable simp_lv_event_lt e s'_obs.
  Proof.
    simpl in *.
    unfold s' in *.
    unfold s'_obs in *.
    unfold s_obs in *.
    destruct e as [et ev es].
    unfold comparable in *.
    destruct Hcomp.
    - simpl in *.
      inversion H.
      congruence.
    - right.
      destruct H.
      + left.
        unfold simp_lv_event_lt in *.
        rewrite decide_True in * by intuition.
        destruct et eqn : eq_et.
        * simpl in Hns. congruence. 
        * unfold state_lt' in *.
          destruct (decide (i = ev)).
          -- subst i.
             rewrite unfold_history_cons; rewrite (@project_same index index_listing Hfinite) by intuition.
             rewrite <- eq_history_eq_project in Hfull.
             rewrite <- Hfull.
             simpl. right. intuition.
             intuition.
          -- rewrite unfold_history_cons; rewrite (@project_different index index_listing Hfinite) by intuition.
             rewrite unfold_history_cons in H.
             intuition.
             apply non_empty_history_nb_project with (so := es).
             intuition.
             apply non_empty_history_nb_project with (so := es).
             intuition.
      + right.
        unfold simp_lv_event_lt in *.
        rewrite decide_True in * by intuition.
        destruct et eqn : eq_et.
        * simpl in Hns.
          congruence.
        * intuition. 
  Qed.
  
  Lemma state_obs_stuff_cons
    (s so : state)
    (Hnb : s <> Bottom /\ so <> Bottom)
    (i : index)
    (Hfull : project s i = project so i)
    (b : bool)
    (s' := update_consensus (update_state s so i) b)
    (s_obs := (SimpObs State' index_self s))
    (s'_obs := (SimpObs State' index_self s')) 
    (e : simp_lv_event)
    (Hns : get_simp_event_type e <> State') 
    (Hsubj : get_simp_event_subject e = index_self)
    (Hcomp: comparable simp_lv_event_lt e s_obs) :
    comparable simp_lv_event_lt e s'_obs.
  Proof.
    simpl in *.
    unfold s' in *.
    unfold s'_obs in *.
    unfold s_obs in *.
    destruct e as [et ev es].
    unfold comparable in *.
    destruct Hcomp.
    - simpl in *.
      inversion H.
      congruence.
    - right.
      destruct H.
      + left.
        unfold simp_lv_event_lt in *.
        rewrite decide_True in * by intuition.
        destruct et eqn : eq_et.
        * simpl in Hns. congruence. 
        * unfold state_lt' in *.
          destruct (decide (i = ev)).
          -- subst i.
             rewrite history_disregards_cv.
             rewrite unfold_history_cons; rewrite (@project_same index index_listing Hfinite) by intuition.
             rewrite <- eq_history_eq_project in Hfull.
             rewrite <- Hfull.
             simpl. right. intuition.
             intuition.
          -- rewrite history_disregards_cv.
             rewrite unfold_history_cons; rewrite (@project_different index index_listing Hfinite) by intuition.
             rewrite unfold_history_cons in H.
             intuition.
             apply non_empty_history_nb_project with (so := es).
             intuition.
             apply non_empty_history_nb_project with (so := es).
             intuition.
      + right.
        unfold simp_lv_event_lt in *.
        rewrite decide_True in * by intuition.
        destruct et eqn : eq_et.
        * simpl in Hns.
          congruence.
        * intuition. 
  Qed.
  
  (* The following concerns the complete observation model, which distinguishes between sent
     and received message observations. It was written before we decided to opt for the
     simplified type in the common futures theorem. *)
     
  Inductive lv_event_type : Type :=
    | State
    | Sent
    | Received.
    
    Instance event_type_eq_dec : EqDecision lv_event_type.
      solve_decision.
    Defined. 
    
    Inductive lv_event : Type :=
      Obs: lv_event_type -> index -> (@state index index_listing) -> lv_event.
    
    Global Instance event_eq_dec : EqDecision lv_event.
      solve_decision.
    Defined. 
    
    Definition get_event_subject (e : lv_event) : index :=
    match e with 
      Obs type subject state => subject
    end.
        
    Definition get_event_subject_some 
      (e : lv_event) :=
      Some (get_event_subject e).
    
    Definition get_event_type (e : lv_event) :=
      match e with
       Obs type subject state => type
      end.
      
    Definition get_event_state (e : lv_event) :=
      match e with
        Obs type subject state => state
      end.
      
    Definition lv_event_comp_eq 
      (e : lv_event) :
      e = Obs (get_event_type e) (get_event_subject e) (get_event_state e).
    Proof.
      destruct e.
      simpl.
      reflexivity.
    Qed.
    
    Definition lv_event_lt (e1 e2 : lv_event) : Prop :=
    match e1, e2 with
      Obs type1 subject1 state1, Obs type2 subject2 state2 =>
        match decide_eq subject1 subject2 with
        | right _ => False
        | _ => match type1, type2 with
               | State, State => False
               | State, Sent => False
               | State, Received => False
               | _, _ => state_lt' subject1 state1 state2
               end  
        end
    end.
    
    Lemma lv_event_trans
      (e1 e2 e3 : lv_event)
      (Hlt : lv_event_lt e1 e2 /\ lv_event_lt e2 e3) :
      lv_event_lt e1 e3.
    Proof.
      destruct Hlt as [Hlt1 Hlt2].
      unfold lv_event_lt in Hlt1, Hlt2.
      destruct e1 as [et1 ev1 es1].
      destruct e2 as [et2 ev2 es2].
      destruct e3 as [et3 ev3 es3].
      assert (ev1 = ev2) by (destruct(decide(ev1 = ev2)); intuition).
      assert (ev2 = ev3) by (destruct(decide(ev2 = ev3)); intuition).
      rewrite decide_True in Hlt1 by intuition.
      rewrite decide_True in Hlt2 by intuition.
      
      assert (ev1 = ev3). {
        apply eq_trans with (y := ev2); intuition.
      }
      
      assert (et1 <> State). {
        intros contra. rewrite contra in Hlt1.
        destruct et2; intuition.
      }
      
      assert (et2 <> State). {
        intros contra. rewrite contra in Hlt2.
        destruct et3; intuition.
      }
      
      destruct et1 eqn : eq_et1.
      - intuition.
      - destruct et2 eqn : eq_et2.
        + intuition.
        + unfold lv_event_lt.
          rewrite decide_True by intuition.
          apply state_lt'_trans with (s2 := es2).
          rewrite <- H in Hlt2. intuition.
        + unfold lv_event_lt.
          rewrite decide_True by intuition.
          apply state_lt'_trans with (s2 := es2).
          rewrite <- H in Hlt2. intuition.
      - destruct et2 eqn : eq_et2.
        + intuition.
        + unfold lv_event_lt.
          rewrite decide_True by intuition.
          apply state_lt'_trans with (s2 := es2).
          rewrite <- H in Hlt2. intuition.
        + unfold lv_event_lt.
          rewrite decide_True by intuition.
          apply state_lt'_trans with (s2 := es2).
          rewrite <- H in Hlt2. intuition.
    Qed.
    
    Lemma lv_event_lt_dec : RelDecision lv_event_lt.
    Proof.
      unfold RelDecision. intros.
      unfold Decision.
      unfold lv_event_lt.
      destruct x as [type1 subject1 state1]; destruct y as [type2 subject2 state2].
      destruct (decide (subject1 = subject2)).
      - destruct type1 eqn : eq1.
        + right. destruct type2; auto.
        + exact (state_lt'_dec subject1 state1 state2).
        + exact (state_lt'_dec subject1 state1 state2).
      - right. auto.
    Qed.
    
    Definition lv_sent_states (s : state) (target : index) : set (@state index index_listing) :=
      match decide_eq target index_self with
      | left _ => get_history s index_self
      | right _ => []
      end.
    
    Definition lv_sent_observations (s : state) (target : index) : set lv_event :=
      match decide_eq target index_self with
      | left _ => List.map (Obs Sent index_self) (lv_sent_states s target)
      | right _ => []
      end.
      
    Lemma in_lv_sent 
      (s : state)
      (target : index)
      (e : lv_event)
      (Hin : In e (lv_sent_observations s target)) :
      get_event_type e = Sent /\ get_event_subject e = target.
    Proof.
      unfold lv_sent_observations in Hin.
      destruct (decide (target = index_self)).
      - unfold lv_sent_states in Hin.
        rewrite decide_True in Hin.
        apply in_map_iff in Hin.
        destruct Hin as [x [Hsent _]].
        rewrite <- Hsent; simpl.
        rewrite e0.
        all : intuition.
      - intuition.
    Qed.
      
    Definition lv_received_observations (s : state) (target : index) : set lv_event :=
      let obs := (get_observations target (depth s) s) in
      let sent_obs := lv_sent_states s target in
      match decide_eq target index_self with
      | left _ => []
      | right _ => List.map (Obs Received target) (set_remove_list sent_obs obs)
      end.
      
    Lemma in_lv_received 
      (s : state)
      (target : index)
      (e : lv_event)
      (Hin : In e (lv_received_observations s target)) :
      get_event_type e = Received /\ get_event_subject e = target.
    Proof.
      unfold lv_received_observations in Hin.
      destruct (decide (target = index_self)).
      - intuition.
      - apply in_map_iff in Hin.
        destruct Hin as [x [Hobs _]].
        rewrite <- Hobs; simpl.
        intuition.
    Qed.
      
    Definition lv_state_observations (s : state) (target : index) : set lv_event :=
      match decide_eq target index_self with
      | left _ => [Obs State index_self s]
      | right _ => []
      end.
    
    Lemma in_lv_state 
      (s : state)
      (target : index)
      (e : lv_event)
      (Hin : In e (lv_state_observations s target)) :
      get_event_type e = State /\ get_event_subject e = target.
    Proof.
      unfold lv_state_observations in Hin.
      destruct (decide (target = index_self)).
      - simpl in Hin.
        destruct Hin.
        rewrite <- H; simpl.
        rewrite e0.
        all : intuition.
      - intuition.
    Qed.
        
    Lemma raw_received
      (s s' : state)
      (target : index)
      (Hdif : target <> index_self) :
      In (Obs Received target s') (lv_received_observations s target) <-> In s' (get_raw_observations s target).
    Proof.
      split; intros; unfold lv_received_observations in *.
      - rewrite decide_False in H by intuition.
        apply in_map_iff in H.
        destruct H as [s'' [Hobs Hins'']].
        apply set_remove_list_1 in Hins''.
        unfold get_raw_observations.
        inversion Hobs.
        rewrite <- H0.
        intuition.
      - rewrite decide_False by intuition.
        apply in_map_iff.
        exists s'.
        split;[reflexivity|].
        unfold lv_sent_states.
        rewrite decide_False by intuition.
        intuition.
    Qed.
      
    Definition lv_message_observations (s : state) (target : index) : set lv_event :=
      set_union decide_eq (lv_sent_observations s target) (lv_received_observations s target).
      
    Definition lv_observations (s : state) (target : index) : set lv_event :=
      set_union decide_eq (lv_state_observations s target) (lv_message_observations s target).
    
        Lemma get_event_state_nb
      (s s': state)
      (i : index)
      (e : lv_event)
      (He : e = (Obs Received i s') \/ e = (Obs Sent i s'))
      (Hin : In e (lv_observations s i)) :
      s' <> Bottom.
    Proof.
      assert (Hse : get_event_state e = s'). {
        destruct He; rewrite H; intuition.
      }
      unfold lv_observations in Hin.
      apply set_union_elim in Hin.
      destruct Hin.
      - apply in_lv_state in H.
        destruct He as [He|He]; rewrite He in H; simpl in H; destruct H; congruence.
      - unfold lv_message_observations in H.
        apply set_union_elim in H.
        destruct H.
        + unfold lv_sent_observations in H.
          destruct (decide (i = index_self)).
          * unfold lv_sent_states in H.
            rewrite decide_True in H.
            apply in_map_iff in H.
            destruct H as [x [Hobs Hinx]].
            apply no_bottom_in_history in Hinx.
            rewrite <- Hobs in Hse; simpl in Hse.
            rewrite <- Hse.
            all : intuition.
          * simpl in H; intuition.
        + unfold lv_received_observations in H.
          destruct (decide (i = index_self)).
          * simpl in H; intuition.
          * apply in_map_iff in H.
          destruct H as [x [Hobs Hinx]].
          apply set_remove_list_1 in Hinx.
          apply no_bottom_in_observations in Hinx.
          rewrite <- Hobs in Hse; simpl in Hse.
          rewrite <- Hse.
          intuition.
    Qed. *)

End Equivocation.