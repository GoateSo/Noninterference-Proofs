Require Import Basic Lang Determinism.
Require Import SecPol SecDef Trace.
Require Import BaseTheory TraceTheories.
From Coq Require Import Basics Equality List Ensembles Relations RelationClasses Setoid Classes.Morphisms.
Import ListNotations.

Module Type SecurityTheory (B : Basic) (LD : LangDefs) (BT : BaseTheories B) (TD : TraceDefs B LD) (SP : SecurityPol LD) (SD : SecurityDefs B LD TD SP) (TT : TraceTheories B LD TD).
  Import B BT LD TD SP SD TT.
  Import LangNotations.

  Section SilentProperties.
    Lemma silent_split : forall l1 l2, erase (l1 ++ l2) = erase l1 ++ erase l2.
      intros.
      induction l1 ; [reflexivity|].
      simpl; destruct (sil_dec a); try assumption.
      rewrite IHl1.
      reflexivity.
    Qed. 

    Lemma sil_sing : forall a, sil a -> erase [a] = [].
      intros; simpl.
      destruct (sil_dec a); try contradiction.
      reflexivity.
    Qed.

    Lemma nsil_sing : forall a, ~ sil a -> erase [a] = [a].
      intros; simpl.
      destruct (sil_dec a); try contradiction.
      reflexivity.
    Qed.

    Lemma silent_break : forall l1 l2 e, 
      ~ sil e 
      -> erase l1 = erase (l2 ++ [e]) 
      -> exists l1a ls, 
          l1a ++ (e :: ls) = l1 
          /\ erase l1a = erase l2 
          /\ erase ls = [].
      induction l1 using rev_ind; induction l2 using rev_ind; intros.
      - rewrite silent_split, nsil_sing in H0; try assumption.
        discriminate.
      - rewrite <-app_assoc, silent_split, silent_split in H0.
        rewrite (nsil_sing e) in H0; try assumption.
        rewrite app_assoc, <-silent_split in H0.
        pose proof app_cons_not_nil (erase (l2 ++ [x])) [] e.
        contradiction.
      - rewrite silent_split in H0.
        destruct (sil_dec x).
        + rewrite sil_sing, app_nil_r in H0; try assumption.
          specialize (IHl1 [] e H H0) as [l1a [l1b [Hcompose [Hdeq1 Hdeq2]]]].
          exists l1a, (l1b ++ [x]).
          repeat split.
          * rewrite <-app_cons_middle in *.
            rewrite <-Hcompose.
            rewrite <- ?app_assoc.
            reflexivity.
          * exact Hdeq1.
          * rewrite silent_split, sil_sing, Hdeq2; try assumption.
            reflexivity. 
        + exists l1, [].
          rewrite silent_split, (nsil_sing x), (nsil_sing e) in H0; try assumption.
          rewrite <-app_nil_l in H0.
          apply app_inj_tail in H0 as [Ha Hb]; subst.
          eauto.
      - destruct (sil_dec x).
        + rewrite silent_split, (sil_sing x), app_nil_r in H0; try assumption.
          specialize (IHl1 (l2 ++ [x0]) e H H0) as [l1a [ls [Hcompose [Hdeq1 Hdeq2]]]].
          exists l1a, (ls ++ [x]).
          rewrite ?silent_split.
          rewrite (sil_sing x s), app_nil_r.
          rewrite <-Hcompose, <-app_assoc, app_comm_cons.
          rewrite silent_split in Hdeq1.
          repeat split; try assumption.
        + destruct (sil_dec x0).
          * rewrite ?silent_split in H0. 
            rewrite (sil_sing x0), (nsil_sing x), (nsil_sing e), app_nil_r in H0; try assumption.
            apply app_inj_tail in H0 as [Ha Hb]; subst.
            exists l1, [].
            rewrite silent_split, (sil_sing x0), app_nil_r; try assumption.
            repeat split; eauto.
          * rewrite silent_split, silent_split in H0.
            rewrite (nsil_sing x), (nsil_sing e) in H0; try assumption.
            apply app_inj_tail in H0 as [Ha Hb]; subst.
            specialize (IHl1 l2 x0 n0 Ha) as [l1a [ls [Hcompose [Hdeq1 Hdeq2]]]].
            subst; clear n.
            eauto.
    Qed.

    Lemma in_erase_impl_nsil : forall e p, List.In e (erase p) -> ~ sil e.
      intros.
      induction p.
      - inversion H.
      - simpl in H.
        destruct (sil_dec a).
        + exact (IHp H).
        + inversion H.
          * subst.
            assumption.
          * exact (IHp H0).
    Qed.

    Lemma erasure_app : forall p p' e, erase p = p' ++ [e] -> ~ sil e.
      intros.
      pose proof in_erase_impl_nsil e p.
      pose proof in_elt e p' [].
      rewrite <- H in H1.
      exact (H0 H1).
    Qed.

    Lemma erase_idemp : forall p, erase (erase p) = erase p.
      induction p.
      - auto.
      - destruct (sil_dec a) eqn:Heq; simpl; rewrite Heq.
        + apply IHp.
        + simpl; rewrite Heq.
          rewrite IHp.
          reflexivity.
    Qed.

    Lemma silent_break_2 : forall l1 l2 e, erase l1 = l2 ++ [e] 
      -> exists l1a ls, 
          l1a ++ (e :: ls) = l1 
          /\ erase l1a = l2 
          /\ erase ls = [].
      intros.
      pose proof in_elt e (l2) [].
      rewrite <-H in H0.
      apply in_erase_impl_nsil in H0.
      assert (erase (l2 ++ [e]) = l2 ++ [e]). {
        assert (erase (erase l1) = erase (l2 ++ [e])). {
          exact (f_equal erase H).
        }
        rewrite erase_idemp in H1.
        rewrite <-H1, <-H.
        reflexivity.
      }
      assert (erase l2 = l2). {
        rewrite silent_split, nsil_sing in H1; try assumption.
        apply app_inj_tail in H1.
        destruct H1.
        auto.
      }
      rewrite <-H1 in H.
      rewrite <-H2.
      apply (silent_break l1 l2 e); assumption.
    Qed.

    Lemma erasure_inv : forall p a p2, Prefix ((erase p) ++ [a]) p2 -> Prefix (erase (p ++ [a])) p2.
      intros. destruct (sil_dec a).
      - rewrite silent_split, sil_sing, app_nil_r; try assumption.
        pose proof (app_prefix (erase p) [a]).
        pose proof @prefix_preorder_inst Event as [_ Htrans].
        specialize (Htrans (erase p) (erase p ++ [a]) p2).
        apply Htrans; assumption.
      - rewrite silent_split, nsil_sing; try assumption.
    Qed.

    Lemma silent_indistinct : forall c m a p, sil a -> Same_set Store (atk_knowledge c m p) (atk_knowledge c m (p ++ [a])).
      intros.
      split; split; destruct H0; try assumption; destruct H1 as [p' [Hprod Hdeq]]; exists p'; split; try assumption; unfold deq_evt_lst.
      - rewrite silent_split; simpl.
        destruct (sil_dec a); rewrite Hdeq; [auto using app_nil_r | contradiction].
      - rewrite <-Hdeq; simpl; rewrite silent_split; simpl.
        destruct (sil_dec a); [auto using app_nil_r | contradiction].
    Qed.
  End SilentProperties.

  Section DEqLists.
    Lemma deq_evt_lst_refl : forall l1, deq_evt_lst l1 l1.
      intros.
      unfold deq_evt_lst.
      trivial.
    Qed.

    Lemma deq_evt_lst_sym : forall l1 l2,  deq_evt_lst l1 l2 -> deq_evt_lst l2 l1.
      unfold deq_evt_lst.
      intros.
      rewrite H.
      reflexivity.
    Qed.

    Lemma deq_evt_lst_trans : forall l1 l2 l3, deq_evt_lst l1 l2 -> deq_evt_lst l2 l3 -> deq_evt_lst l1 l3.
      unfold deq_evt_lst.
      intros.
      rewrite H, H0.
      reflexivity.
    Qed.

    #[global] Instance deq_evt_lst_refl_equiv: Equivalence (deq_evt_lst).
    Proof.
      constructor.
      - exact deq_evt_lst_refl.
      - exact deq_evt_lst_sym.
      - exact deq_evt_lst_trans.
    Qed.

    Global Add Setoid (list Event) deq_evt_lst deq_evt_lst_refl_equiv as deq_evt_lst_setoid.
  End DEqLists.

  Section DleLists.
    Lemma dle_evt_lst_refl : forall l1, dle_evt_lst l1 l1.
      intros.
      unfold dle_evt_lst.
      induction l1; [reflexivity | ].
      unfold erase.
      destruct (sil_dec a); auto.
    Qed.

    Lemma dle_evt_lst_trans : forall l1 l2 l3, dle_evt_lst l1 l2 -> dle_evt_lst l2 l3 -> dle_evt_lst l1 l3.
      unfold dle_evt_lst.
      intros.
      pose proof (@prefix_preorder_inst Event) as [_ Htrans].
      unfold Transitive in Htrans.
      apply (Htrans (erase l1) (erase l2) (erase l3)); assumption.
    Qed.

    Lemma pref_impl_dle : forall p1 p2, Prefix p1 p2 -> Prefix (erase p1) (erase p2).
      induction p2 using rev_ind; intros.
      - inversion H.
        reflexivity.
      - pose proof prefix_of_append p1 (p2 ++ [x]) [].
        rewrite app_nil_r in H0.
        apply H0 in H; clear H0.
        destruct H.
        + apply prop_prefix_app_implies_prefix in H.
          apply IHp2 in H.
          rewrite silent_split.
          apply prefix_app.
          assumption.
        + destruct H as [lst [H1 H2]].
          inversion H2; subst.
          rewrite app_nil_r in *.
          apply prefix_preorder_inst.
    Qed.

    Lemma gen_prefix_erase_exists : 
      forall (p l2 : list Event), 
        Prefix p (erase l2) -> 
        exists l2', Prefix l2' l2 /\ p = erase l2'.
    Proof.
      intros p l2.
      generalize dependent p.
      induction l2 as [|e l2' IHl2]; intros.
      - inversion H.
        eauto using Prefix_empty.
      - simpl in H; destruct (sil_dec e) eqn:Heq.
        + specialize (IHl2 p H) as [l2_sub [H_sub_prefix H_sub_erase]].
          exists (e :: l2_sub); simpl; split.
          * constructor; assumption.
          * rewrite Heq; assumption.
        + inversion H.
          * eauto.
          * subst.
            specialize (IHl2 lst0 H2) as [l2'' [? ?]].
            exists (e :: l2''); simpl.
            split.
            -- constructor.
              assumption.
            -- rewrite Heq, H1.
              reflexivity.
    Qed.

    Lemma dle_evt_lst_alt : 
      forall (l1 l2 : list Event), 
        dle_evt_lst l1 l2 -> 
        exists l2', Prefix l2' l2 /\ deq_evt_lst l1 l2'.
    Proof.
      intros l1 l2 H.
      apply gen_prefix_erase_exists with (p := erase l1), H.
    Qed.
    
    Lemma erase_in : forall e p, List.In e (erase p) -> ~ sil e.
      intros.
      induction p.
      - inversion H.
      - destruct (sil_dec a) eqn:Heq; simpl in H; rewrite Heq in H.
        + eauto.
        + apply in_inv in H; destruct H.
          * subst; assumption.
          * eauto.
    Qed.
  End DleLists.

  Section DeqTracePfx.
    Instance deq_pfx_equiv : Equivalence deq_pfx.
      destruct deq_store_equiv as [Hdsr Hdss Hdst].
        split; unfold deq_pfx, Reflexive, Symmetric, Transitive.
        - auto using deq_evt_lst_refl.
        - intros [s1 l1] [s2 l2] [H1 H2].
          auto using deq_evt_lst_sym.
        - intros [s1 l1] [s2 l2] [s3 l3] [H1 H2] [H3 H4].
          unfold Transitive in Hdst.
          split.
          + apply (deq_evt_lst_trans l1 l2 l3) in H1; [exact H1 | exact H3]. 
          + apply (Hdst s1 s2 s3) in H2; [exact H2 | exact H4].
    Defined. 
    
    Instance dle_pfx_preorder : PreOrder dle_pfx.
      destruct deq_store_equiv as [RS SS TS].
      split; unfold dle_pfx.
      - unfold Reflexive.
        auto using dle_evt_lst_refl.
      - unfold Transitive.
        intros [s1 l1] [s2 l2] [s3 l3].
        intros [H1 H2] [H3 H4].
        split.
        + apply (dle_evt_lst_trans l1 l2 l3); auto.
        + apply (TS s1 s2 s3); auto.
    Defined.
  End DeqTracePfx.

  Section DltTracePfx.
    Lemma dlt_conseq : forall m1 m2 p1 p2, dlt_pfx (m1, p1) (m2, p2) -> 
      dle_evt_lst p1 p2 /\ ~ deq_evt_lst p1 p2.
      intros; unfold dlt_pfx, dle_pfx, deq_pfx in H.
      simpl in H; destruct H.
      split.
      - destruct H. assumption.
      - intro Hbad.
        destruct H0, H.
        split; assumption.
    Qed.
    
    Lemma dlt_impl_prop_prefix : forall m1 m2 p1 p2, deq_store m1 m2 ->  dlt_pfx (m1, p1) (m2, p2) ->
      PropPrefix (erase p1) (erase p2).
      intros.
      apply dlt_conseq in H0 as [Hdle Hdeq].
      unfold dle_evt_lst, deq_evt_lst in *.
      split; assumption.
    Qed.

    Lemma dlt_pfx_alt : forall m1 m2 p1 p2, deq_store m1 m2 -> dlt_pfx (m1, p1) (m2, p2) -> exists a, ~ sil a /\ dle_evt_lst (p1 ++ [a]) p2.
      intros.
      apply (dlt_impl_prop_prefix m1 m2 p1 p2) in H.
      apply prop_prefix_exists_next in H as [a [Hpref Hpres]].
      exists a; split.
      - apply erase_in in Hpres. assumption.
      - unfold dle_evt_lst.
        apply erasure_inv.
        assumption.
      - assumption.
    Qed.

    Lemma dlt_pfx_alt2 : forall m1 m2 p1 p2, deq_store m1 m2 
      -> dlt_pfx (m1, p1) (m2, p2) 
      -> exists p2', PropPrefix p2' p2 /\ deq_evt_lst p1 p2'.
      intros.
      destruct H0 as [[Hpref _] Hneq]; simpl in *.
      pose proof (dle_evt_lst_alt p1 p2 Hpref) as [p2' [Hpfx Hneq2]].
      exists p2'; split.
      - split; [assumption|].
        intro Hbad.
        subst.
        apply Hneq.
        split; assumption.
      - assumption.
    Qed.

    Lemma find_first_kept : forall p, ~ deq_evt_lst p [] -> exists p_sil e p_rest,
      p = p_sil ++ e :: p_rest 
      /\ deq_evt_lst p_sil []
      /\ ~ sil e.
      induction p; intros.
      - destruct H. reflexivity.
      - destruct (sil_dec a) eqn:Heq.
        + unfold deq_evt_lst, erase in H.
          rewrite Heq in H.
          unfold deq_evt_lst in IHp; simpl in IHp.
          specialize (IHp H).
          destruct IHp as [p_sil [e [p_rest [Hcompose [Hpsil Hnsil]]]]].
          exists (a :: p_sil), e, p_rest; simpl.
          unfold deq_evt_lst, erase.
          rewrite <-Hcompose, Heq.
          auto.
        + exists [], a, p. auto.
    Qed.

    Lemma PropPrefix_nil_prod : forall p1 p2, PropPrefix (erase p1) (erase p2) ->
      exists p2' e, PropPrefix p2' p2 /\ ~ sil e /\ Prefix (p2' ++ [e]) p2 /\ deq_evt_lst p1 p2'.
      intros ? ? [Hpref Hneq].
      unfold PropPrefix.
      apply dle_evt_lst_alt in Hpref as [p2' [Hpref Hdeq]].
      assert (PropPrefix p2' p2). {
        split; [assumption|].
        intro Hbad; subst.
        apply Hneq; assumption.
      }
      assert (exists p2_suffix, p2 = p2' ++ p2_suffix /\ [] <> p2_suffix) as [p2suf [Hcompose Hnnil]]. {
        apply prefix_split in H.
        exact H.
      }
      assert (erase p2suf <> []). {
        intro Hbad.
        subst p2.
        rewrite silent_split, Hbad, app_nil_r in Hneq.
        auto.
      }
      apply find_first_kept in H0 as [p_sil [e [p_rest [Hcompose2 [Hpsil Hnsil]]]]].
      exists (p2' ++ p_sil), e.
      subst.
      repeat split; try assumption.
      - pose proof (app_prefix (p2' ++ p_sil) (e :: p_rest)).
        rewrite <-app_assoc in H0.
        assumption.
      - rewrite <-(app_nil_r (p2' ++ p_sil)), app_assoc; simpl.
        intro Hbad.
        apply app_inv_head in Hbad.
        inversion Hbad.
      - rewrite <-app_assoc, <-app_cons_middle with (ys:=p_rest).
        pose proof (app_prefix (p2' ++ p_sil ++ [e]) (p_rest)).
        rewrite <-app_assoc in H0. rewrite <-app_assoc in H0.
        assumption.
      - unfold deq_evt_lst in *.
        rewrite silent_split, Hpsil, app_nil_r.
        assumption.
    Qed. 
  End DltTracePfx.

  (* theorems for : atk_know p <= prog_know p <= atk_know (p ++ [a]) *)
  Section SubKnowledge.
    Lemma prog_impl_atk_knowledge: forall c m p a, (c, m) ==>*[p ++ [a]] -> ~ sil a -> Included Store (prog_knowledge c m p) (atk_knowledge c m p).
      intros ? ? ? ? Htsub Hnsil.
      intros m' [Hmdeq [p' [a' [[Hpprod Hpdeq] Hnsil']]]].
      split; try assumption.
      unfold deq_evt_lst in Hpdeq.
      pose proof (silent_break p' p a') Hnsil' Hpdeq as  [l1a [ls [Hcompose [Hdeq1 Hdeq2]]]].
      subst.
      exists l1a.
      split.
      - assert (Prefix l1a (l1a ++ a' :: ls)). {
          clear Hpdeq Hpprod Hdeq1.
          induction l1a; [apply Prefix_empty|].
          rewrite <-app_comm_cons.
          constructor.
          assumption.
        }
        apply (prefix_prefix_prod l1a (l1a ++ a' :: ls)); assumption.
      - unfold deq_evt_lst; auto.
    Qed.

    Lemma atk_next_impl_prog_knowledge: forall c m p e, (c, m) ==>*[p ++ [e]] -> ~ sil e -> Included Store (atk_knowledge c m (p ++ [e])) (prog_knowledge c m p).
      intros ? ? ? ? Hpeprod Hnsil m' [Hmdeq [p' [Hpprod Hpedeq]]].
      split; [assumption|].
      exists p', e.
      auto.
    Qed.
  End SubKnowledge. 
End SecurityTheory.