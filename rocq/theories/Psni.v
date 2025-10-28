Require Import Basic.
Require Import Lang.
Require Import SecPol.
Require Import Determinism.
Require Import SecDef SecPol Trace.
Require Import BaseTheory.
Require Import SecTheory.

From Coq Require Import Basics Equality List Ensembles Relations RelationClasses Classes.Equivalence.
Import ListNotations.

Module Type PSNI (B : Basic) (BT : BaseTheories B) (LD : LangDefs) (TD : TraceDefs B LD) (SP : SecurityPol LD) (Det : DeterminismDef LD) (SD : SecurityDefs B LD TD SP) (ST : SecurityTheory B LD TD SP SD).
  Import B BT LD TD Det SP SD ST.
  Import LangNotations.

  Section Core.
    Context (D : Ensemble Label) `{DecD : DecideIn Label D}.
    
    Axiom trace_pfx_production : forall c cs, trace_pfx_prod c cs.
    Axiom trace_max : forall p, trace_pfx_maximize p.
    Axiom trace_max_prod : forall c m p st, (c, m)==>*[p] -> (m, p) <=| (m, st) -> c ~~> (m, st).

    Lemma prefix_prefix_prod : forall c a p m, (c, m) ==>*[a :: p] -> (c, m) ==>*[p].
      unfold iter_trace_prod.
      intros.
      destruct H.
      inversion H.
      exists cs1.
      assumption.
    Qed.

    Definition indistincts (c : Cmd) (s : Store) : Ensemble Store :=
      fun s' => deq_store s s'/\ exists t, c ~~> (s', t).

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
          + rewrite (trace_pfx_production c (m2, s2) (m, p2)) in Hcs2.
            destruct Hcs2.
            apply H0.
            assumption.
          + assumption.
      - destruct H1.
        assumption.
    Qed.

    Lemma hpsni_memset_invariance : forall c, 
    In Property HPsniD (behavior c) 
    -> forall m st, c ~~> (m, st)
    -> forall p', (m, p') <=| (m, st) -> Same_set Store (atk_knowledge c m p') (indistincts c m).
      intros.
      split; intros m' [Hdeq Ht]; split; trivial.
      - destruct Ht as [t [Htprod [p'' Hpprod]]].
        exists t.
        assumption.
      - destruct Ht as [st' Hp].
        apply (hpsni_indistinct_conseq c H st m st') in Hdeq. 
          + destruct Hdeq as [Hdeq Hindist].
            exists st'.
            auto.
          + split; assumption.
    Qed.
    
    Theorem Hpsni_impl_KPsni : forall c, In Property HPsniD (behavior c) -> In Cmd KPsniD c.
      unfold HPsniD, KPsniD.
      intros c HHPsniD p m a.
      intros.
      pose proof trace_pfx_production as Htraceprod.
      pose proof (hpsni_memset_invariance c HHPsniD m) as Htmp.
      assert (Same_set Store (atk_knowledge c m p) (indistincts c m)). {
        apply prefix_prefix_prod in H.
        pose proof trace_max (m, p) as [st Htmaxpref].
        apply Htmp with st.
        - apply trace_max_prod with p; assumption.
        - assumption.
      }
      assert (Same_set Store (indistincts c m) (atk_knowledge c m (a :: p))). {
        pose proof trace_max (m, a :: p) as [st Htmaxpref].
        apply Same_set_sym.
        apply Htmp with st.
        - apply trace_max_prod with (a :: p); assumption.
        - assumption.  
      }
      apply Same_set_trans with (indistincts c m); assumption.
    Qed.
    
    (* ------------------ KPSNI + DET ==> HPSNI  ------------------ *)    
    Lemma foo : forall m a p s, (m, (a :: p)) <=| (m, s) -> (m, p) <=| (m, s).
      intros.
      apply LeTrace_intro.
      inversion H; subst.
      inversion H1; subst.
    Admitted.
      

    Lemma kpsni_indistinct_conseq : forall c, In Cmd KPsniD c
    -> forall s1 m1 s2 m2, c ~~> (m1, s1) /\ c ~~> (m2, s2)
    -> deq_store m1 m2 <-> deq_store m1 m2 
          /\ (forall p1, (m1, p1) <=| (m1, s1) -> exists p2, (c, m2)==>*[p2] /\ deq_evt_lst p1 p2).
      intros c HKPsni s1 m1 s2 m2 [Hdp1 Hdp2].
      unfold KPsniD, In in HKPsni.
      split; intros.
      - split; trivial.
        intros.
        induction p1.
        + exists []; split.
          * exists (c, m2). apply MultiStep_refl.
          * unfold deq_evt_lst.
            reflexivity.
        + pose proof (trace_pfx_production c (m1, s1) (m1, (a :: p1))) as [Ha _].
          unfold deq_evt_lst, erase. 
          assert ((m1, p1) <=| (m1, s1)). {
            apply foo in H0.
            assumption.
          }
          apply IHp1 in H1.
          destruct H1 as [p2 [Hp2a Hp2b]].
          destruct (sil_dec a).
          * apply (silent_indistinct c m1 a p1) in s.
            unfold Same_set, Included, In, atk_knowledge in s.
            destruct s as [Hpsubap Hapsubp].
            inversion H0.
            exists p2.
            unfold deq_evt_lst, erase.
            split; trivial.
          * simpl in Ha. 
            rewrite (Ha Hdp1) in H0.
            destruct (HKPsni p1 m1 a); auto.
            unfold  Included, In, atk_knowledge in H1. 
            pose proof H1 m2.
            destruct H3. {
              split; trivial.
              exists s2.
              split; trivial.
              exists p2.
              auto.
            }
            destruct H4 as [st' [Hprod [p' [Hpp Hdeqp]]]].
            exists p'.
            split; trivial.
            unfold deq_evt_lst in Hdeqp.
            destruct (sil_dec a).
            contradiction.
            rewrite (non_silent_erasure a p1 n0) in Hdeqp.
            assumption.
      - destruct H; assumption. 
   Qed.  
  End Core.
End PSNI.