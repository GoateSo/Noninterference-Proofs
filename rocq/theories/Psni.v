Require Import Basic Lang Determinism.
Require Import SecDef SecPol Trace.
Require Import BaseTheory TraceTheories DetTheories.
Require Import SecTheory.

From Stdlib Require Import Basics Equality List Ensembles Relations RelationClasses Classes.Equivalence.
Import ListNotations.

Module Type PSNI (B : Basic) (BT : BaseTheories B) (LD : LangDefs) (TD : TraceDefs B LD) (SP : SecurityPol LD) (Det : DeterminismDef LD) (SD : SecurityDefs B LD TD SP) (TT : TraceTheories B LD TD) (ST : SecurityTheory B LD BT TD SP SD TT)  (DT : DetTheories B LD TD Det TT).
  Import B BT LD TD Det SP SD ST TT DT.
  Import LangNotations.

  Section Core.
    Context (D : Ensemble Label) `{DecD : DecideIn Label D}.

    (* ------------------ KPSNI <=== HPSNI  ------------------ *)
    Lemma hpsni_indistinct_conseq : forall c, In Property HPsniD (behavior c)
    -> forall s1 m1 s2 m2, c ~~> (m1, s1) -> c ~~> (m2, s2)
    -> deq_store m1 m2 <-> deq_store m1 m2 
          /\ (forall p1, (m1, p1) <=| (m1, s1) -> exists p2, (c, m2)==>*[p2] /\ deq_evt_lst p1 p2).
      split; intros; [split|]; try assumption.
      - intros p1 Hp1s1.
        specialize (H _ _ H0 H1 H2 _ Hp1s1) as [[m p2] [Hpfx [Hlst Hstore]]].
        exists p2.
        split; [|assumption].
        + inversion Hpfx; subst.
          trace_prefix_prod c m2 p2.
          assumption.
      - destruct H2.
        assumption.
    Qed.

    Lemma hpsni_memset_invariance : forall c, 
    In Property HPsniD (behavior c) 
    -> forall m st, c ~~> (m, st)
    -> forall p', (m, p') <=| (m, st) -> Same_set Store (atk_knowledge c m p') (indistincts c m).
      split; intros m' Hin.
      - destruct Hin; assumption.
      - pose proof univ_production c m' as [st' Hprod].
        pose proof hpsni_indistinct_conseq c H st m st' m'.
        apply H2 in Hin as [? ?]; try split; auto.
    Qed.

    Theorem Hpsni_impl_KPsni : forall c, In Property HPsniD (behavior c) -> In Cmd KPsniD c.
      unfold HPsniD, KPsniD.
      intros c HHPsniD p m a ? ?.
      pose proof (hpsni_memset_invariance c HHPsniD m) as Hinv.
      assert (Same_set Store (atk_knowledge c m p) (indistincts c m)). {
        apply (prefix_prefix_prod _ _ (app_prefix p [a])) in H.
        get_max_trace c m p [st [Hpfx Htprod]].
        apply Hinv with st; assumption.
      }
      assert (Same_set Store (indistincts c m) (atk_knowledge c m (p ++ [a]))). {
        get_max_trace c m (p ++ [a]) [st [Hepfx Htprod]].
        apply Same_set_sym, Hinv with st; assumption.
      }
      apply Same_set_trans with (indistincts c m); assumption.
    Qed.
    
    (* ------------------ KPSNI + DET ==> HPSNI  ------------------ *)    
    Lemma kpsni_indistinct_conseq : forall c, In Cmd KPsniD c
    -> forall s1 m1 s2 m2, c ~~> (m1, s1) -> c ~~> (m2, s2)
    -> deq_store m1 m2 <-> deq_store m1 m2 
          /\ (forall p1, (m1, p1) <=| (m1, s1) -> exists p2, (c, m2)==>*[p2] /\ deq_evt_lst p1 p2).
      intros ? HKPsni ? ? ? ? Hdp1 Hdp2.
      split; intros; [| destruct H; assumption].
      split; [assumption |].
      induction p1 using rev_ind; intros.
      + exists []; split; auto.
        exists (c, m2); auto.
      + inversion H0; subst.
        unfold deq_evt_lst.
        pose proof app_prefix p1 [x] as app_prefix_p1_x.
        assert (EvtPrefix p1 s1) by eauto using app_prefix_p1_x, lst_prefix_stream_prefix.
        apply (LeTrace_intro m1) in H1.
        apply IHp1 in H1.
        destruct H1 as [p2 [Hp2Prod Hp2Deq]].
        rewrite silent_split; simpl.
        destruct (sil_dec x).
          * rewrite app_nil_r.
            can_step_auto. 
          * trace_prefix_prod c m1 (p1 ++ [x]).
            destruct (HKPsni p1 m1 x) as [H4 _]; try assumption.
            unfold Included, In, atk_knowledge in H4.
            pose proof H4 m2 as H4ak; clear H4.
            destruct H4ak as [Htprod [p' [Hpprod Hpeq]]]; can_step_auto.
            unfold deq_evt_lst in Hpeq.
            rewrite silent_split, (nsil_sing x n) in Hpeq.
            can_step_auto.
    Qed.  

    Theorem kpsni_det_impl_hpsni : forall c, In Cmd KPsniD c 
      -> (det_rel steps_to_combined)
      -> In Property HPsniD (behavior c).
      intros ? HKPsniD one_step_det [m1 st1] [m2 st2] ? ? ? [mp1 p1] Hpsub.
      destruct (kpsni_indistinct_conseq c HKPsniD st1 m1 st2 m2) as [Hl _]; eauto.
      specialize (Hl H1) as [Hindist Hprod].
      inversion Hpsub; subst.
      apply Hprod in Hpsub as [p2 [Hp2prod Hp2deq]].
      get_max_trace c m2 p2 [stp2 [Hp2pfx Ht2prod]].
      pose proof det_trace_pfx_production one_step_det _ _ _ H0 p2.
      exists (m2, p2).
      split; auto.
    Qed.
  End Core.
End PSNI.