Require Import Basic Lang Determinism.
Require Import SecDef SecPol Trace.
Require Import BaseTheory TraceTheories DetTheories.
Require Import SecTheory.

From Coq Require Import Basics Equality List Ensembles Relations RelationClasses Classes.Equivalence Arith.PeanoNat Lia. 
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
      intros ? HPini ? ? ? ? He_nsil Hmdeq Hpeprod [p' [e' [Hnsil [Hprod' Hdeq']]]].
      get_max_trace c m (p ++ [e]) [st [Hpfx Htprod]].
      get_max_trace c m' p' [st' [Hpfx' Htprod']].
      inversion Hpfx; inversion Hpfx'; subst.
      specialize (HPini _ _ Htprod Htprod' Hmdeq _ _ Hpfx Hpfx').
      assert (e = e'). {
        destruct HPini as [Htdle | Htdle]; inversion Htdle as [Hpdle _]; subst; unfold deq_evt_lst, dle_evt_lst in *; simpl in *; rewrite Hdeq' in Hpdle; rewrite ?silent_split in Hpdle; rewrite ?nsil_sing in Hpdle; try assumption.
        - apply (prefix_first_eq_last_eq (erase p)).
          assumption.
        - symmetry.
          apply (prefix_first_eq_last_eq (erase p) e' e).
          assumption.
      }
      exists p'.
      split; [assumption | congruence].
    Qed.

    Theorem Hpini_impl_KPini : forall c, In Property HPiniD (behavior c) -> In Cmd KPiniD c.
      intros c HPiniD p m e Hprod Hnsil.
      split.
      - intros m' [Hdeq [p' [e' [[Hpprod Hpdeq] Hnsil']]]].
        split; [assumption|].
        pose proof Hpini_conseq _ HPiniD m m' p e.
        destruct (H Hnsil Hdeq Hprod); eauto.
      - apply atk_next_impl_prog_knowledge; assumption.
    Qed.

    Lemma det_dlt_same_config_impl_shorter : forall p1 p2 c m ,
      det_rel steps_to_combined
      -> PropPrefix (erase p1) (erase p2)
      -> (c, m) ==>*[p1] 
      -> (c, m) ==>*[p2]
      -> length p1 <= length p2.
      induction p1, p2; simpl; auto; intros; [apply le_0_n | |].
      - destruct H0.
        destruct (sil_dec a).
        + inversion H0; subst.
          symmetry in H5.
          contradiction.
        + inversion H0.
      - apply le_n_S.
        simpl in *.
        destruct H1, H2.
        inversion H1. inversion H2.
        destruct cs1 as [c' m'].
        det_subst.
        specialize (IHp1 p2 c' m' H).
        destruct (sil_dec a) eqn:Heq.
        + destruct (IHp1 H0); can_step_auto.
        + assert (PropPrefix (erase p1) (erase p2)). {
            destruct H0.
            inversion H0; subst.
            split; [assumption | ].
            - intro Hbad.
              rewrite Hbad in H3.
              contradiction.   
          }
          destruct (IHp1 H3); can_step_auto.
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
      det_pref_from_len Hspref.
      split; [assumption|].
      intro Hbad.
      destruct H0.
      congruence.
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
      apply multistep_tail in Hprod1 as [cs1' [cs1'' [Hp1Start Hp1End]]].
      apply multistep_tail in Hprod2 as [cs2' [cs2'' [Hp2Start Hp2End]]].
      destruct HKpinil as [_ [p' [Hpprod Hdeqpp]]]. {
        split; [| can_step_auto].
        + apply deq_store_equiv in Hmdeq.
          assumption.
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
      destruct (Hdet_ppref); clear Hdet_ppref; can_step_auto.
      - assert (PropPrefix p1 p') by (split; assumption). 
        apply (PropPrefix_production p1 p' H1) in Hpprod as [evt [Hnpref Hnprod]].
        apply multistep_tail in Hnprod as [cs3' [cs3'' [Hp3Start Hp3End]]].
        assert (cs1' = cs3') by (apply (det_prod_impl_same one_step_det p1 c m1); assumption).
        subst; det_subst.
        apply pref_impl_dle in Hnpref.
        rewrite Hdeqpp, ?silent_split, ?nsil_sing, Hpdeq in Hnpref; try assumption.
        apply prefix_first_eq_last_eq in Hnpref.
        rewrite ?silent_split, Hpdeq, Hnpref.
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
      apply S_le_impl_lt in Hlen.
      assert (length px1 <= length px2) as Hlen_weak by lia.
      specialize (IHpx1 _ Hlen_weak); clear Hlen_weak.
      symmetry in H3.
      assert (~ sil x) by exact (erasure_app _ _ _ H3).
      apply silent_break_2 in H3 as [p1p [p1s [Hcompose [Hdeq1 Hdeqsil]]]].
      symmetry in Hdeq1.
      unfold In, KPiniD in H0.
      rewrite <-app_cons_middle, app_assoc in Hcompose.
      assert ((c, m1) ==>*[p1p ++ [x]]). {
        assert (Prefix (p1p ++ [x]) p1). {
          rewrite <-Hcompose.
          apply app_prefix.
        }
        exact (prefix_prefix_prod _ _ H3 _ _ H5).
      }
      specialize (H0 _ _ _ H3 H7) as [Hkpini _].
      pose proof Hcompose as Hpref1.
      rewrite <-app_assoc in Hpref1.
      apply prefix_of_compose in Hpref1.  
      apply prefix_of_compose in Hcompose.
      pose proof prefix_prefix_prod _ _ Hpref1 _ _ H5.
      specialize (IHpx1 _ _ Hdeq1 H4 H0 H6).
      assert (PropPrefix px1 px2). {
        split; try assumption.
        intro Hbad.
        rewrite Hbad in Hlen.
        apply Nat.lt_irrefl in Hlen.
        assumption.
      }
      subst.
      destruct (Hkpini m2).
      - split; [assumption|].
        apply PropPrefix_nil_prod in H8 as [p2' [e' [Hppref [Hnil [Hpfx Hdeq]]]]].
        unfold deq_evt_lst in *.
        pose proof prefix_prefix_prod _ _ Hpfx c m2 H6.
        exists (p2' ++ [e']), e'.
        repeat split; try assumption.
        rewrite ?silent_split, Hdeq.
        reflexivity. 
      - destruct H9 as [p [Hpprod Hpdeq]].
        unfold deq_evt_lst in *.
        destruct (rev_destruct (erase p)).
        + rewrite H9 in *.
          rewrite silent_split, (nsil_sing _ H7) in Hpdeq.
          apply symmetry in Hpdeq.
          pose proof app_not_nil (erase p1p) x. 
          contradiction.
        + destruct H9 as [init [evt Hsplit]].
          rewrite Hsplit in *.
          assert (~ sil evt) by exact (erasure_app _ _ _ Hsplit).
          rewrite silent_split, (nsil_sing x H7) in Hpdeq.
          apply app_inj_tail in Hpdeq as [Heqa Heqb].
          subst.
          destruct (Compare.le_dec (length p) (length p2)).
          * det_pref_from_len Hcommon.
            apply pref_impl_dle in Hcommon.
            congruence.
          * det_pref_from_len Hp2prefp.
            apply pref_impl_dle in Hp2prefp.
            rewrite Hsplit in Hp2prefp.
            pose proof Hp2prefp.
            apply pref_le_len in Hp2prefp.
            pose proof Nat.le_antisymm _ _ Hp2prefp H2.
            pose proof prefix_eq_len _ _ H10 H11.
            congruence.
    Qed.

    Theorem kpini_det_impl_hpini : forall c, In Cmd KPiniD c 
      -> (det_rel steps_to_combined)
      -> In Property HPiniD (behavior c).
        intros ? HKpini one_step_det (m1, st1) (m2, st2) Htprod1 Htprod2 Hdeq (?, p1) (?, p2) Htpref1 Htpref2.
        inversion Htpref1. inversion Htpref2. subst.
        trace_prefix_prod c m1 p1 Hp1prod.
        trace_prefix_prod c m2 p2 Hp2prod.
        remember (erase p1) as px1.
        remember (erase p2) as px2. 
        destruct (Compare.le_dec (length px1) (length px2)).
        + pose proof len_erase_conseq _ _ _ one_step_det HKpini Hdeq _ _ l _ _ Heqpx1 Heqpx2 Hp1prod Hp2prod.
          left; constructor; subst; assumption.
        + apply deq_store_equiv in Hdeq.
          pose proof len_erase_conseq _ _ _ one_step_det HKpini Hdeq _ _ l _ _ Heqpx2 Heqpx1 Hp2prod Hp1prod.
          right; constructor; subst; assumption.
    Qed.
  End Core.
End PINI.