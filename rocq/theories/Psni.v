Require Import Basic Lang Determinism.
Require Import SecDef SecPol Trace.
Require Import BaseTheory TraceTheories DetTheories.
Require Import SecTheory.

From Coq Require Import Basics Equality List Ensembles Relations RelationClasses Classes.Equivalence.
Import ListNotations.

Module Type PSNI (B : Basic) (BT : BaseTheories B) (LD : LangDefs) (TD : TraceDefs B LD) (SP : SecurityPol LD) (Det : DeterminismDef LD) (SD : SecurityDefs B LD TD SP) (ST : SecurityTheory B LD TD SP SD) (TT : TraceTheories B LD TD) (DT : DetTheories B LD TD Det TT).
  Import B BT LD TD Det SP SD ST TT DT.
  Import LangNotations.

  Section Core.
    Context (D : Ensemble Label) `{DecD : DecideIn Label D}.

    Lemma prefix_prefix_prod : forall p' p, Prefix p' p -> forall c m,  (c, m) ==>*[p] -> (c, m) ==>*[p'].
      unfold iter_trace_prod.
      intros ? ? HPref.
      dependent induction HPref; intros.
      - exists (c, m); apply MultiStep_refl.
      - destruct H.
        inversion H; subst.
        destruct cs1 as [c' m'].
        pose proof IHHPref c' m'.
        destruct H0.
        + exists x; apply H5.
        + exists x0.
          apply (MultiStep_some (c, m) (c', m') x0); assumption. 
    Qed.

    (* ------------------ KPSNI <=== HPSNI  ------------------ *)
    Lemma hpsni_indistinct_conseq : forall c, In Property HPsniD (behavior c)
    -> forall s1 m1 s2 m2, c ~~> (m1, s1) /\ c ~~> (m2, s2)
    -> deq_store m1 m2 <-> deq_store m1 m2 
          /\ (forall p1, (m1, p1) <=| (m1, s1) -> exists p2, (c, m2)==>*[p2] /\ deq_evt_lst p1 p2).
      split; intros.
      - split.
        * assumption.
        * unfold In, HPsniD in H.
          destruct H0 as [Hcs1 Hcs2].
          intros p1 Hp1s1.
          pose proof (H (m1, s1) (m2, s2) Hcs1 Hcs2 H1) as PSNI'.
          pose proof (PSNI' (m1, p1) Hp1s1) as [[m p2] [Hpfx [Hlst Hstore]]].
          exists p2.
          split.
          + inversion Hpfx; subst.
            apply (trace_pfx_production_fwd c m2 s2); assumption.
          + assumption.
      - destruct H1.
        assumption.
    Qed.

    Lemma hpsni_memset_invariance : forall c, 
    In Property HPsniD (behavior c) 
    -> forall m st, c ~~> (m, st)
    -> forall p', (m, p') <=| (m, st) -> Same_set Store (atk_knowledge c m p') (indistincts c m).
      unfold Included.
      split; intros m' Hin.
      - destruct Hin as [Hdeq _]; assumption.
      - pose proof univ_production c m' as [st' Hprod].
        pose proof hpsni_indistinct_conseq c H st m st' m'.
        destruct H2; [split; assumption |].
        unfold In, indistincts in Hin.
        apply (hpsni_indistinct_conseq c H st m st') in Hin. 
          + destruct Hin. split; auto.
          + split; assumption.
    Qed.
    
    Lemma app_prefix : forall (a : Event) p, Prefix p (p ++ [a]).
      intros; induction p; [apply Prefix_empty | apply Prefix_some, IHp].
    Qed.

    Theorem Hpsni_impl_KPsni : forall c, In Property HPsniD (behavior c) -> In Cmd KPsniD c.
      unfold HPsniD, KPsniD.
      intros c HHPsniD p m a ? ?.
      pose proof (hpsni_memset_invariance c HHPsniD m) as Hinv.
      assert (Same_set Store (atk_knowledge c m p) (indistincts c m)). {
        apply (prefix_prefix_prod p (p ++ [a]) (app_prefix a p)) in H.
        apply (trace_max c m p) in H as [st [Hepfx Htprod]]. 
        apply Hinv with st; assumption.
      }
      assert (Same_set Store (indistincts c m) (atk_knowledge c m (p ++ [a]))). {
        apply (trace_max c m (p ++ [a])) in H as [st [Hepfx Htprod]].
        apply Same_set_sym.
        apply Hinv with st; assumption.
      }
      apply Same_set_trans with (indistincts c m); assumption.
    Qed.
    
    (* ------------------ KPSNI + DET ==> HPSNI  ------------------ *)    
    Lemma kpsni_indistinct_conseq : forall c, In Cmd KPsniD c
    -> forall s1 m1 s2 m2, c ~~> (m1, s1) /\ c ~~> (m2, s2)
    -> deq_store m1 m2 <-> deq_store m1 m2 
          /\ (forall p1, (m1, p1) <=| (m1, s1) -> exists p2, (c, m2)==>*[p2] /\ deq_evt_lst p1 p2).
      intros c HKPsni s1 m1 s2 m2 [Hdp1 Hdp2].
      split; intros; [| destruct H; assumption].
      split; [assumption |].
      apply (rev_ind (fun p1 => (m1, p1) <=| (m1, s1) -> exists p2, (c,m2)==>*[p2] /\ deq_evt_lst p1 p2)); intros.
      + exists []; split; auto.
        exists (c, m2); apply MultiStep_refl. apply deq_evt_lst_refl.
      + inversion H1; subst.
        unfold deq_evt_lst.
        assert (EvtPrefix l s1) by eauto using (app_prefix x l), lst_prefix_stream_prefix.
        apply (LeTrace_intro m1) in H2.
        apply H0 in H2.
        destruct H2 as [p2 [Hp2Prod Hp2Deq]].
        rewrite silent_split; simpl.
        destruct (sil_dec x).
          * exists p2.
            split; [assumption|].
            unfold deq_evt_lst in Hp2Deq.
            rewrite app_nil_r.
            assumption.
          * apply (trace_pfx_production_fwd c m1 s1) in H1; try assumption.
            destruct (HKPsni l m1 x) as [H4 _]; try assumption.
            unfold Included, In, atk_knowledge in H4.
            pose proof H4 m2 as H4ak; clear H4.
            destruct H4ak as [Htprod [p' [Hpprod Hpeq]]]. {
              split; [| exists p2; split]; assumption. 
            }
            unfold deq_evt_lst in Hpeq.
            rewrite silent_split in Hpeq. simpl in Hpeq.
            destruct (sil_dec x); [contradiction |].
            exists p'.
            auto.
    Qed.  

    Theorem kpsni_det_impl_hpsni : forall c, In Cmd KPsniD c 
      -> (det_rel steps_to_combined)
      -> In Property HPsniD (behavior c).
      unfold det_rel, steps_to_combined, KPsniD, In, HPsniD.
      intros ? HKPsniD one_step_det [m1 st1] [m2 st2] ? ? ? p1 Hpsub.
      destruct (kpsni_indistinct_conseq c HKPsniD st1 m1 st2 m2) as [Hl _]; [eauto| ].
      apply Hl in H1  as [Hindist Hprod].
      destruct p1 as [mp1 p1].
      inversion Hpsub; subst.
      apply (Hprod p1) in Hpsub.
      destruct Hpsub as [p2 [Hp2prod Hp2deq]].
      pose proof trace_max c m2 p2 Hp2prod as [stp2 [Hp2pfx Ht2prod]].
      exists (m2, p2).
      split.
      - pose proof det_trace_pfx_production one_step_det c m2 st2 H0 p2.
        apply H1.
        assumption.
      - unfold deq_pfx.
        eauto.
    Qed.
  End Core.
End PSNI.