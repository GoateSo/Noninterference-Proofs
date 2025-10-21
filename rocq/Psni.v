Require Import Basic.
Require Import Lang.
Require Import SecPol.
Require Import Determinism.
Require Import SecDef SecPol Trace.
Require Import Grounding.

From Coq Require Import Basics Equality List Ensembles Relations RelationClasses.
Import ListNotations.

Module Type PSNI (B : Basic) (G : GroundTheories B) (LD : LangDefs) (TD : TraceDefs B LD) (SP : SecurityPol LD) (Det : DeterminismDef LD) (SD : SecurityDefs B LD TD SP) .
  Import B G LD TD Det SP SD.
  Import LangNotations.

  Section Core.
    Context (D : Ensemble Label) `{DecD : DecideIn Label D}.
    
    Axiom trace_pfx_production : forall c cs, trace_pfx_prod c cs.
    Axiom trace_max : forall p, maximalization p.
    Axiom trace_max_prod : forall c m p st, (c, m)==>*[p] -> (m, p) <=| (m, st) -> c ~~> (m, st).

    Lemma prefix_prefix_prod : forall c a p m, (c, m) ==>*[a :: p] ->  (c, m) ==>*[p].
      unfold iter_trace_prod.
      intros.
      destruct H.
      inversion H.
      exists cs1.
      assumption.
    Qed.

    Definition indistincts (c : Cmd) (s : Store) : Ensemble Store :=
      fun s' => deq_store s s'/\ exists t, c ~~> (s', t).

    Lemma hpsni_indistinct_conseq : forall c, In Property HPsniD (behavior c)
    -> forall s1 m1 s2 m2, c ~~> (m1, s1) /\ c ~~> (m2, s2)
    -> deq_store m1 m2 <-> deq_store m1 m2 
          /\ (forall p1, (m1, p1) <=| (m1, s1) -> exists p2, (c, m2)==>*[p2] /\ deq_evt_lst p1 p2).
      split; intros.
      - split.
        * assumption.
        * unfold In, HPsniD in H.
          destruct H0 as [Hcs1 Hcs2].
          pose proof (H (m1, s1) (m2, s2) Hcs1 Hcs2 H1) as PSNI'.
          intros p1 Hp1s1.
          pose proof (PSNI' (m1, p1) Hp1s1) as [[m p2] [Hpfx [Hlst Hstore]]].
          exists p2.
          split.
          + rewrite (trace_pfx_production c (m2, s2) (m, p2)) in Hcs2.
            destruct Hcs2.
            auto.
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
          + auto.
    Qed.
    
    Theorem Hpsni_impl_KPsni : forall c, In Property HPsniD (behavior c) -> In Cmd KPsniD c.
      unfold HPsniD, KPsniD.
      intros c HHPsniD p m a.
      intros.
      pose proof trace_pfx_production as Htraceprod.
      assert (Same_set Store (atk_knowledge c m p) (indistincts c m)). {
        pose proof trace_max (m, p) as [st Htmaxpref].
        apply prefix_prefix_prod in H.
        pose proof trace_max_prod c m p st as Hmaxprod.
        pose proof hpsni_memset_invariance c HHPsniD m st as Hminv.
        pose proof (Htraceprod c (m, st) (m, p)) as [Hprodl _].
        pose proof Hminv (Hmaxprod H Htmaxpref) p.
        auto.
      }
      assert (Same_set Store (indistincts c m) (atk_knowledge c m (a :: p))). {
        pose proof trace_max (m, a :: p) as [st H3].
        pose proof trace_max_prod c m (a :: p) st as Hmaxprod.
        pose proof hpsni_memset_invariance c HHPsniD m st as Hminv.
        pose proof (Htraceprod c (m, st) (m, (a :: p))) as [Hprodl _].
        pose proof Hminv (Hmaxprod H H3) (a :: p).
        auto with sets.
      }
      auto using (Same_set_trans Store (atk_knowledge c m p) (indistincts c m) (atk_knowledge c m (a :: p))).
    Qed.
  End Core.
End PSNI.