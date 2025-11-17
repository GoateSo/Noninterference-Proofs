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
      get_max_trace c m (p ++ [a]) [st1 [Htpref1 Htprod1]].
      get_max_trace c m' p' [st2 [Htpref2 Htprod2]].
      specialize (HHLfpD _ _ Htprod2 Htprod1 _ _ Htpref2 Htpref1). 
      inversion Htpref1; inversion Htpref2; subst.
      destruct HHLfpD as [[? p2] [Hres1 Hres2]]. {
        unfold dlt_pfx; split.
        - constructor; simpl.
          + apply deq_evt_lst_sym in Hpdeq.
            unfold dle_evt_lst,deq_evt_lst in *.
            rewrite silent_split, (nsil_sing a Hnsil), Hpdeq in *.
            apply (app_prefix (erase p) [a]).
          + apply deq_store_equiv.
            assumption.
        - intro H.
          inversion H; simpl in *; clear H2 H.
          apply deq_evt_lst_sym in Hpdeq.
          rewrite Hpdeq in H1.
          inversion H1.
          rewrite silent_split, (nsil_sing a Hnsil) in H2.
          apply (list_app_neq_list (erase p) a).
          assumption.
      }
      inversion Hres1; subst.
      apply dlt_pfx_alt in Hres2 as [a' [Hnsila' Hdeqpa']]; [|apply deq_store_equiv].
      pose proof dle_evt_lst_alt (p'++[a']) p2 Hdeqpa' as [p'' [Hppref Hppdeq]].
      trace_prefix_prod c m' p2 Hp2prod.
      apply prefix_prefix_prod with (p':=p'')in Hp2prod; try assumption.
      exists p'',a'.
      repeat split; try assumption.
      unfold deq_evt_lst in *.
      rewrite silent_split in *.
      congruence.
    Qed.

    Theorem Hplfp_impl_KPlfp : forall c, In Property HLfpD (behavior c) -> In Cmd KLfpD c.
      intros ? Hlfp ? ? ? Hpaprod Hnsil.
      assert ((c, m) ==>*[ p ++ [a]] /\ ~ sil a) by eauto.
      pose proof HLfpD_conseq _ Hlfp _ _ _ H as Hlemma; clear H.
      split.
      - intros m' [Hdeq [p' [Hpprod Hpdeq]]].
        pose proof Hlemma _ Hdeq; split; try assumption.
        destruct H as [p2 [a' [? [? ?]]]]; eauto.
      - apply (prog_impl_atk_knowledge _ _ p a); assumption.
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
      specialize (Hatk_impl_prog m').
      unfold atk_knowledge, In in Hatk_impl_prog.
      destruct Hatk_impl_prog; [auto|].
      destruct H0 as [p' [e' [[? ?] ?]]].
      eauto.
    Qed.

    Theorem Klfp_det_impl_Hlfp : forall c, In Cmd KLfpD c 
      -> (det_rel steps_to_combined)
      -> In Property HLfpD (behavior c).  
      intros ? HKlfp one_step_det.
      intros t1 t2 Ht1Prod Ht2Prod p1 p2 Hp1tpfx Hp2tpfx Hdlt.
      destruct t1 as [m1 t1], t2 as [m2 t2], p1 as [mp1 p1], p2 as [mp2 p2].
      inversion Hp1tpfx. inversion Hp2tpfx; subst.
      trace_prefix_prod c m1 p1.
      trace_prefix_prod c m2 p2.
      pose proof Hdlt as Hdlt'.
      destruct Hdlt as [Hdlepfx Hneq].
      inversion Hdlepfx; simpl in *.
      pose proof dlt_impl_prop_prefix _ _ _ _ H3 Hdlt'.
      pose proof PropPrefix_nil_prod _ _ H4 as [p2' [e [Hppref [Hnsil [Hppref2 Hdeqp1]]]]].
      pose proof prefix_prefix_prod _ _ Hppref2 _ _ H1.
      apply deq_store_equiv in H3.
      pose proof KLfP_conseq _ _ _ _ HKlfp Hnsil H6 _ H3.
      destruct H7 as [p' [e' [Hdeq [Hnsil2 Hprod]]]]; [eauto|].
      unfold progressD.
      exists (m1, p').
      split.
      - exact (det_trace_pfx_production one_step_det _ _ _ Ht1Prod _ Hprod).
      - unfold PropPrefix, deq_evt_lst in *.
        rewrite Hdeqp1 in H4.
        constructor.
        + constructor; simpl; try apply deq_store_equiv.
          unfold dle_evt_lst.
          rewrite Hdeqp1, Hdeq, silent_split, nsil_sing; auto.
          apply app_prefix.
        + intro Hbad.
          inversion Hbad; simpl in H7, H8.
          unfold deq_evt_lst in H7.
          rewrite Hdeqp1, Hdeq, silent_split, nsil_sing in H7; auto.
          pose proof list_app_neq_list (erase p2') e'.
          contradiction. 
    Qed.
  End Core.
End LFP. 