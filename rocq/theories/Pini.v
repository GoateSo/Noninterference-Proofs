Require Import Basic Lang Determinism.
Require Import SecDef SecPol Trace.
Require Import BaseTheory TraceTheories DetTheories.
Require Import SecTheory.

From Coq Require Import Basics Equality List Ensembles Relations RelationClasses Classes.Equivalence Arith.PeanoNat.
Import ListNotations.

Module Type PINI (B : Basic) (BT : BaseTheories B) (LD : LangDefs) (TD : TraceDefs B LD) (SP : SecurityPol LD) (Det : DeterminismDef LD) (SD : SecurityDefs B LD TD SP) (TT : TraceTheories B LD TD) (ST : SecurityTheory B LD BT TD SP SD TT)  (DT : DetTheories B LD TD Det TT).
  Import B BT LD TD Det SP SD ST TT DT.
  Import LangNotations.

  Section Core.
    Context (D : Ensemble Label) `{DecD : DecideIn Label D}.
    
    Lemma Hpini_conseq : forall c, In Property HPiniD (behavior c) -> forall m m' p e, ~ sil e 
      -> deq_store m m'
      -> (c, m)==>*[p ++ [e]]
      -> (exists p' e', ~sil e' /\ (c, m')==>*[p'] /\ deq_evt_lst p' (p ++ [e']))
      -> exists pp, (c, m')==>*[pp] /\ deq_evt_lst (p ++ [e]) pp.
      intros. 
      destruct H3 as [p' [e' [Hnsil [Hprod' Hdeq']]]].
      pose proof trace_max c m (p ++ [e]) H2 as [st [Hpfx Htprod]].
      pose proof trace_max c m' p' Hprod' as [st' [Hpfx' Htprod']].
      inversion Hpfx; inversion Hpfx'; subst.
      unfold In, HPiniD in H.
      specialize (H (m,st) (m',st') Htprod Htprod' H1).
      specialize (H (m, p++[e]) (m',p') Hpfx Hpfx').
      assert (e = e'). {
        destruct H; inversion H; subst; unfold deq_evt_lst, dle_evt_lst in *; simpl in *; rewrite Hdeq' in H3; rewrite ?silent_split in H3;
        rewrite ?nsil_sing in H3; try assumption.
        - apply (prefix_first_eq_last_eq (erase p)).
          assumption.
        - symmetry.
          apply (prefix_first_eq_last_eq (erase p) e' e).
          assumption.
      }
      exists p'.
      split; try assumption.
      congruence.
    Qed.

    Theorem Hpini_impl_KPini : forall c, In Property HPiniD (behavior c) -> In Cmd KPiniD c.
      intros c HPiniD p m e Hprod Hnsil.
      split.
      - intros m' [Hdeq [p' [e' [[Hpprod Hpdeq] Hnsil']]]].
        split; [assumption|].
        pose proof Hpini_conseq c HPiniD m m' p e.
        specialize (H Hnsil Hdeq Hprod).
        destruct H as [ps [Hpsprod Hpsdeq]]; [eauto |].
        eauto.
      - apply atk_next_impl_prog_knowledge; assumption.
    Qed.

    Lemma det_dlt_same_config_impl_shorter : forall p1 p2 c m ,
      det_rel steps_to_combined
      -> PropPrefix (erase p1) (erase p2)
      -> (c, m) ==>*[p1] 
      -> (c, m) ==>*[p2]
      -> length p1 <= length p2.
      induction p1, p2; simpl; auto.
      - intros. 
        apply le_0_n.
      - intros.
        destruct H0.
        destruct (sil_dec a).
        + inversion H0; subst.
          symmetry in H5.
          contradiction.
        + inversion H0.
      - intros.
        apply le_n_S.
        simpl in H0, IHp1.
        destruct H1, H2.
        inversion H1. inversion H2.
        pose proof (H (c,m) cs1 cs4 a e H7 H13) as [Hdet_Conf_eq Hdet_evt_eq].
        rewrite Hdet_Conf_eq in *.
        destruct cs1, cs4, x, x0.
        subst. 
        specialize (IHp1 p2 c1 s0 H).
        destruct (sil_dec e) eqn:Heq.
        + specialize (IHp1 H0).
          destruct IHp1.
          * exists (c2, s1); assumption.
          * exists (c3, s2); assumption.
          * reflexivity.
          * auto using le_S.
      + assert (PropPrefix (erase p1) (erase p2)). {
          destruct H0.
          inversion H0; subst.
          split.
          - assumption.
          - intro Hbad.
            rewrite Hbad in H3.
            apply H3.
            reflexivity.    
        }
        specialize (IHp1 H3).
        destruct IHp1.
          * exists (c2, s1); assumption.
          * exists (c3, s2); assumption.
          * reflexivity.
          * auto using le_S.
    Qed.

    Lemma det_dlt_same_config_impl_propprefix : forall p1 p2 c m ,
      det_rel steps_to_combined
      -> PropPrefix (erase p1) (erase p2)
      -> (c, m) ==>*[p1] 
      -> (c, m) ==>*[p2]
      -> PropPrefix p1 p2.
      intros.
      pose proof det_dlt_same_config_impl_shorter as Hshort.
      specialize (Hshort p1 p2 c m H H0 H1 H2).
      pose proof det_prod_impl_prefix as Hspref.
      specialize (Hspref H p1 p2 c m Hshort H1 H2).
      split.
      - assumption.
      - intro Hbad.
        destruct H0.
        subst.
        apply H3.
        reflexivity.
    Qed. 
       
    Lemma monkas : forall c m p e, (c, m) ==>*[p ++ [e]] -> exists cs' cs'', (c, m) ==>*[p] cs' /\ cs' -->[e] cs''.
      intros.
      generalize dependent m.
      revert c.
      induction p; intros.
      - simpl in H; destruct H; inversion H; inversion H5; subst.
        exists (c, m), x.
        split; [apply MultiStep_refl| assumption].
      - simpl in H; destruct H; inversion H; subst.
        destruct cs1 as (c1, m1).
        destruct (IHp c1 m1).
        + exists x; assumption.
        + destruct H0 as [[c2 m2] [HprodStart HprodEnd]].
          exists x0, (c2, m2).
          split.
          * apply MultiStep_some with (cs1:=(c1,m1)); assumption.
          * assumption.
    Qed.

    Lemma kpini_conseq : forall c m1 m2 p1 p2 e1 e2, 
    In Cmd KPiniD c 
    -> (det_rel steps_to_combined)
    -> deq_store m1 m2
    -> deq_evt_lst p1 p2
    -> ~ sil e1
    -> ~ sil e2
    -> (c,m1)==>*[p1++[e1]]
    -> (c,m2)==>*[p2++[e2]]
    -> (exists p e', ~ sil e' /\ (c, m1) ==>*[p] /\  deq_evt_lst p (p2 ++ [e']))
    -> deq_evt_lst (p1++[e1]) (p2++[e2]).
      intros ? ? ? ? ? ? ? HKpini one_step_det Hmdeq Hpdeq Hnsil1 Hnsil2 Hprod1 Hprod2 [p [e' [Hnsile' [Hnpprod Hdeq]]]].
      destruct (HKpini p2 m2 e2) as [HKpinil _]; try assumption.
      specialize (HKpinil m1).
      unfold Included, In in HKpinil.
      apply monkas in Hprod1 as [cs1' [cs1'' [Hp1Start Hp1End]]].
      apply monkas in Hprod2 as [cs2' [cs2'' [Hp2Start Hp2End]]].
      destruct HKpinil as [_ [p' [Hpprod Hdeqpp]]]. {
        split.
        + apply deq_store_equiv in Hmdeq.
          assumption.
        + exists p, e'.
          split; try split; assumption.
      }
      unfold deq_evt_lst in *.
      apply symmetry in Hdeqpp.
      assert (PropPrefix (erase p1) (erase (p2 ++ [e2]))) as Hppref. {
        split.
        - rewrite Hpdeq, silent_split, nsil_sing; try assumption.
          apply app_prefix.
        - intro Hbad.
          rewrite Hpdeq, silent_split, nsil_sing in Hbad; try assumption.
          pose proof list_app_neq_list (erase p2) e2.
          contradiction. 
      }
      rewrite <-Hdeqpp in Hppref.
      pose proof det_dlt_same_config_impl_propprefix as Hdet_ppref.
      specialize (Hdet_ppref p1 p' c m1 one_step_det Hppref).
      destruct (Hdet_ppref); clear Hdet_ppref.
      - exists (cs1').
        assumption.
      - assumption.
      - assert (PropPrefix p1 p'). { split; assumption. }
        clear H H0.
        apply (PropPrefix_production p1 p' H1) in Hpprod as [evt [Hnpref Hnprod]].
        apply monkas in Hnprod as [cs3' [cs3'' [Hp3Start Hp3End]]].
        assert (cs1' = cs3'). {
          apply (det_prod_impl_same one_step_det p1 c m1); assumption.
        }
        subst.
        unfold det_rel, steps_to_combined in one_step_det.
        specialize (one_step_det cs3' cs1'' cs3'' e1 evt).
        destruct one_step_det; try assumption.
        subst.
        apply (pref_impl_dle (p1 ++ [evt]) p') in Hnpref.
        rewrite Hdeqpp in Hnpref.
        rewrite ?silent_split in Hnpref.
        rewrite ?nsil_sing in Hnpref; try assumption.
        rewrite Hpdeq in Hnpref.
        apply prefix_first_eq_last_eq in Hnpref.
        rewrite ?silent_split.
        rewrite Hpdeq.
        rewrite Hnpref.
        reflexivity.
    Qed.

    Lemma len_erase_conseq : forall c m1 m2,
      (det_rel steps_to_combined)
    -> In Cmd KPiniD c
    -> deq_store m1 m2
    -> forall px1 px2, length px1 <= length px2
    -> forall p1 p2, px1 = erase p1 
    -> px2 = erase p2
    -> (c,m1)==>*[p1]
    -> (c,m2)==>*[p2]
    -> Prefix px1 px2.
      induction px1 using rev_ind; intros; [trivial|].
      pose proof H2 as Hlen.
      rewrite last_length in Hlen.
      pose proof H3 as Heq.
      pose proof Hlen as H_len_lt.
      apply S_le_impl_lt in H_len_lt.
      apply S_n_le_n_le in Hlen.
      specialize (IHpx1 px2 Hlen); clear Hlen.
      assert (~ sil x). {
        pose proof in_erase_impl_nsil x p1.
        pose proof in_elt x px1 [].
        rewrite H3 in H8.
        exact (H7 H8).
      }
      symmetry in H3.
      apply silent_break_2 in H3 as [p1p [p1s [Hcompose [Hdeq1 Hdeqsil]]]].
      symmetry in Hdeq1.
      unfold In, KPiniD in H0.
      assert ((c, m1) ==>*[ p1p ++ [x]]). {
        assert (Prefix (p1p ++ [x]) p1). {
          rewrite <-Hcompose.
          rewrite <-(app_cons_middle p1p p1s).
          rewrite app_assoc.
          apply app_prefix.
        }
        exact (prefix_prefix_prod (p1p++[x]) p1 H3 c m1 H5).
      }
      specialize (H0 p1p m1 x H3 H7) as [Hkpini _].
      specialize (Hkpini m2).
      pose proof Hcompose as Hpref1.
      apply prefix_of_compose in Hpref1.  
      rewrite <-app_cons_middle, app_assoc in Hcompose.
      pose proof Hcompose as Hpref2.
      apply prefix_of_compose in Hpref2.
      unfold deq_evt_lst.
      pose proof prefix_prefix_prod p1p p1 Hpref1 c m1 H5.
      specialize (IHpx1 p1p p2 Hdeq1 H4 H0 H6).
      assert (PropPrefix px1 px2). {
        split; try assumption.
        intro Hbad.
        rewrite Hbad in H_len_lt.
        apply Nat.lt_irrefl in H_len_lt.
        assumption.
      }
      clear IHpx1.
      subst px1 px2.
      destruct Hkpini.
      - split; [assumption|].
        apply PropPrefix_nil_prod in H8 as [p2' [e' [Hppref [Hnil [Hpfx Hdeq]]]]].
        unfold deq_evt_lst in *.
        pose proof prefix_prefix_prod (p2' ++ [e']) p2 Hpfx c m2 H6.
        exists (p2' ++ [e']), e'.
        split; try split; try assumption.
        rewrite ?silent_split, Hdeq.
        reflexivity. 
      - destruct H9 as [p [Hpprod Hpdeq]].
        unfold deq_evt_lst in *.
        destruct (rev_destruct (erase p)).
        + rewrite H9 in *.
          rewrite silent_split, nsil_sing in Hpdeq; try assumption.
          pose proof app_not_nil (erase p1p) x. 
          apply symmetry in Hpdeq.
          contradiction.
        + destruct H9 as [init [evt Hsplit]].
          rewrite Hsplit in *.
          pose proof in_elt evt init [].
          rewrite <-Hsplit in H9.
          apply in_erase_impl_nsil in H9.
          rewrite silent_split, nsil_sing in Hpdeq; try assumption.
          apply app_inj_tail in Hpdeq as [Heqa Heqb].
          subst x init.
          destruct (Compare.le_dec (length p) (length p2)).
          * pose proof det_prod_impl_prefix H p p2 c m2 l Hpprod H6.
            apply pref_impl_dle in H10.
            congruence.
          * pose proof det_prod_impl_prefix H p2 p c m2 l H6 Hpprod.
            apply pref_impl_dle in H10.
            rewrite Hsplit in H10.
            apply pref_le_len in H10.
            pose proof Nat.le_antisymm (length (erase p2)) (length (erase p1p ++ [evt])) H10 H2.
            subst.
            clear Hpref1 Hpref2 H10 H2. 
            pose proof det_prod_impl_prefix H p2 p c m2 l H6 Hpprod.
            apply pref_impl_dle in H2.
            rewrite Hsplit in H2.
            pose proof prefix_eq_len (erase p2) (erase p1p ++ [evt]) H2 H11.
            congruence.
    Qed.

    Theorem kpini_det_impl_hpini : forall c, In Cmd KPiniD c 
      -> (det_rel steps_to_combined)
      -> In Property HPiniD (behavior c).
        intros.
        unfold In, HPiniD.
        intros (m1, st1) (m2, st2) Htprod1 Htprod2 Hdeq (?, p1) (?, p2) Htpref1 Htpref2.
        simpl in *.
        inversion Htpref1. inversion Htpref2.
        subst.
        pose proof trace_pfx_production_fwd c m1 st1 Htprod1 p1 Htpref1.
        pose proof trace_pfx_production_fwd c m2 st2 Htprod2 p2 Htpref2.
        remember (erase p1) as px1.
        remember (erase p2) as px2. 
        destruct (Compare.le_dec (length px1) (length px2)).
        + pose proof len_erase_conseq c m1 m2 H0 H Hdeq px1 px2 l p1 p2 Heqpx1 Heqpx2 H1 H3.
          left.
          constructor; unfold dle_evt_lst; simpl; subst; assumption.
        + apply deq_store_equiv in Hdeq.
          pose proof len_erase_conseq c m2 m1 H0 H Hdeq px2 px1 l p2 p1 Heqpx2 Heqpx1 H3 H1.
          right.
          constructor; unfold dle_evt_lst; simpl; subst; assumption.
    Qed.
  End Core.
End PINI.