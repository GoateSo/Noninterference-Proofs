Require Import Basic Lang Determinism.
Require Import SecDef SecPol Trace.
Require Import BaseTheory TraceTheories DetTheories.
Require Import SecTheory.

From Coq Require Import Basics Equality List Ensembles Relations RelationClasses Classes.Equivalence.
Import ListNotations.

Module Type LFP (B : Basic) (BT : BaseTheories B) (LD : LangDefs) (TD : TraceDefs B LD) (SP : SecurityPol LD) (Det : DeterminismDef LD) (SD : SecurityDefs B LD TD SP) (TT : TraceTheories B LD TD) (ST : SecurityTheory B LD BT TD SP SD TT) (DT : DetTheories B LD TD Det TT).
  Import B BT LD TD Det SP SD ST TT DT.
  Import LangNotations.

  Section Core.
    Context (D : Ensemble Label) `{DecD : DecideIn Label D}.

    Lemma HLfpD_conseq : forall c, In Property HLfpD (behavior c)
    -> forall p m a, ((c, m) ==>*[p ++ [a]] /\ ~ sil a)
    -> forall m', (deq_store m m') 
    -> (exists p', ((c, m') ==>*[p'] /\ deq_evt_lst p p')) 
    -> (exists p2 a', ((c, m') ==>*[p2] /\ deq_evt_lst p2 (p ++ [a']) /\ ~ sil a')).
      intros ? HHLfpD ? ? ? [Hpaprod Hnsil] ? Hdeq [p' [Hpprod Hpdeq]].
      pose proof trace_max c m (p ++ [a]) Hpaprod as [st1 [Htpref1 Htprod1]]. 
      pose proof trace_max c m' (p') Hpprod as [st2 [Htpref2 Htprod2]]. 
      specialize (HHLfpD (m', st2) (m, st1) Htprod2 Htprod1 (m', p') (m, p ++ [a])  Htpref2 Htpref1). 
      inversion Htpref1; inversion Htpref2; subst.
      destruct HHLfpD as [[? p2] [Hres1 Hres2]]. {
        unfold dlt_pfx; split.
        - constructor; simpl.
          + apply deq_evt_lst_sym in Hpdeq.
            unfold dle_evt_lst,deq_evt_lst in *.
            rewrite silent_split, (nsil_sing a) in *; try assumption.
            rewrite Hpdeq.
            apply (app_prefix (erase p) [a]).
          + apply deq_store_equiv.
            assumption.
        - intro H.
          inversion H; simpl in *; clear H2 H.
          pose proof deq_evt_lst_sym p p'.
          apply H in Hpdeq.
          rewrite Hpdeq in H1.
          inversion H1.
          rewrite silent_split, nsil_sing in H3; try assumption.
          apply (list_app_neq_list (erase p) a).
          assumption.
      }
      inversion Hres1; subst.
      apply dlt_pfx_alt in Hres2 as [a' [Hnsila' Hdeqpa']].
      pose proof dle_evt_lst_alt (p'++[a']) p2 Hdeqpa' as [p'' [Hppref Hppdeq]].
      pose proof trace_pfx_production_fwd c m' st2 Htprod2 p2 Hres1 as Hp2prod.
      apply prefix_prefix_prod with (p':=p'')in Hp2prod; try assumption.
      exists p'',a'.
      split; try split; try assumption.
      unfold deq_evt_lst in *.
      rewrite silent_split, Hpdeq in *.
      auto.
      apply deq_store_equiv.
    Qed.

    Theorem Hplfp_impl_KPlfp : forall c, In Property HLfpD (behavior c) -> In Cmd KLfpD c.
      intros ? Hlfp ? ? ? Hpaprod Hnsil.
      assert ((c, m) ==>*[ p ++ [a]] /\ ~ sil a) by eauto.
      pose proof HLfpD_conseq c Hlfp p m a H as Hlemma; clear H.
      split.
      - intros m' [Hdeq [p' [Hpprod Hpdeq]]].
        pose proof Hlemma m' Hdeq; split; try assumption.
        destruct H as [p2 [a' [? [? ?]]]]; eauto.
      - apply (prog_impl_atk_knowledge c m p a); assumption.
    Qed.

    Lemma KLfP_conseq : forall c m p e, In Cmd KLfpD c
      -> ~sil e 
      -> (c,m)==>*[p ++ [e]]
      -> forall m', deq_store m m' 
      -> (exists p', (c,m')==>*[p'] /\ deq_evt_lst p p') 
      -> (exists px e, deq_evt_lst px (p ++ [e]) /\ ~sil e /\ (c,m')==>*[px]).
      intros ? ? ? ? HKlfp Hnsil Hprod ? Hmdeq Hpremise.
      unfold In, KLfpD in HKlfp.
      specialize (HKlfp p m e Hprod Hnsil) as [Hatk_impl_prog _].
      unfold Included, atk_knowledge, prog_knowledge, In in Hatk_impl_prog.
      specialize (Hatk_impl_prog m').
      destruct Hatk_impl_prog; [auto|].
      destruct H0 as [p' [e' [[? ?] ?]]].
      eauto.
    Qed.

    Theorem klfp_det_impl_hlfp : forall c, In Cmd KLfpD c 
      -> (det_rel steps_to_combined)
      -> In Property HLfpD (behavior c).  
      intros ? HKlfp one_step_det.
      intros t1 t2 Ht1Prod Ht2Prod p1 p2 Hp1tpfx Hp2tpfx.
      destruct t1 as [m1 t1], t2 as [m2 t2], p1 as [mp1 p1], p2 as [mp2 p2].
      inversion Hp1tpfx. inversion Hp2tpfx; subst.
      pose proof trace_pfx_production_fwd c m1 t1 Ht1Prod p1 Hp1tpfx.
      pose proof trace_pfx_production_fwd c m2 t2 Ht2Prod p2 Hp2tpfx.
      intro Hdlt.
      pose proof Hdlt as Hdlt'.
      destruct Hdlt as [Hdlepfx Hneq].
      inversion Hdlepfx; simpl in *.
      pose proof dlt_impl_prop_prefix m1 m2 p1 p2 H3 Hdlt'.
      pose proof PropPrefix_nil_prod p1 p2 H4 as [p2' [e [Hppref [Hnsil [Hppref2 Hdeqp1]]]]].
      pose proof prefix_prefix_prod (p2' ++ [e]) p2 Hppref2 c m2 H1.
      assert (deq_store m2 m1). {
        pose proof deq_store_equiv as [_ Hdssym _].
        unfold Symmetric in Hdssym.
        specialize (Hdssym m1 m2).
        apply Hdssym; assumption.
      }
      pose proof KLfP_conseq c m2 p2' e HKlfp Hnsil H6 m1 H7.
      destruct H8; [eauto|].
      destruct H8 as [e' [Hdeq [Hnsil2 Hprod]]].
      unfold progressD.
      exists (m1, x).
      split.
      - pose proof det_trace_pfx_production one_step_det.
        exact (H8 c m1 t1 Ht1Prod x Hprod).
      - unfold PropPrefix in H4.
        unfold deq_evt_lst in Hdeqp1, Hdeq.
        rewrite Hdeqp1 in H4.
        constructor.
        + constructor; simpl; try apply deq_store_equiv.
          unfold dle_evt_lst.
          rewrite Hdeqp1, Hdeq, silent_split, nsil_sing; auto.
          apply app_prefix.
        + intro Hbad.
          inversion Hbad; simpl in H8, H9.
          unfold deq_evt_lst in H8.
          rewrite Hdeqp1, Hdeq, silent_split, nsil_sing in H8; auto.
          pose proof list_app_neq_list (erase p2') e'.
          contradiction. 
    Qed.
  End Core.
End LFP. 