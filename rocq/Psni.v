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
    Axiom trace_max_prod : forall c m p st, (c, m)==>*[p] -> le_trace (m, p) (m, st) -> In Trace (behavior c) (m, st).

    Lemma prefix_prefix_prod : forall c a p m, (c, m) ==>*[a :: p] ->  (c, m) ==>*[p].
      unfold iter_trace_prod.
      intros.
      destruct H.
      inversion H.
      exists cs1.
      assumption.
    Qed.

    Definition indistincts (c : Cmd) (s : Store) : Ensemble Store :=
      fun s' => deq_store s s'/\ exists t, In Trace (behavior c) (s', t).

    Lemma hpsni_indistinct_conseq : forall c, In Property HPsniD (behavior c)
    -> forall s1 m1 s2 m2, In Trace (behavior c) (m1, s1) /\ In Trace (behavior c) (m2, s2)
    -> deq_store m1 m2 <-> deq_store m1 m2 
          /\ (forall p1, (m1, p1) <=| (m1, s1) -> exists p2, (c, m2)==>*[p2] /\ deq_evt_lst p1 p2).
      split; intros.
      - split.
        * assumption.
        * unfold In, HPsniD in H.
          destruct H0 as [Hcs1 Hcs2].
          pose proof (H (m1, s1) (m2, s2) Hcs1 Hcs2 H1) as PSNI'.
          intros p1 Hp1s1.
          unfold deq_pfx in PSNI'.
          pose proof (PSNI' (m1, p1) Hp1s1) as Hp2.
          destruct Hp2 as [p2 Hp2].
          destruct p2 as [m p2]. simpl in Hp2.
          destruct Hp2 as [Hpfx [Hlst Hstore]].
          exists p2.
          split.
          + pose proof (trace_pfx_production c (m2, s2) (m, p2)) as [Htprodl _].
            destruct (Htprodl Hcs2).
            auto.
          + assumption.
      - destruct H1.
        assumption.
    Qed.

    Lemma hpsni_memset_invariance : forall c, 
    In Property HPsniD (behavior c) 
    -> forall m st, In Trace (behavior c) (m, st)
    -> forall p', (m, p') <=| (m, st) -> Same_set Store (atk_knowledge c m p') (indistincts c m).
      unfold Same_set, Included, indistincts, atk_knowledge, In.
      intros.
      simpl.
      pose proof (hpsni_indistinct_conseq c H st m) as Hpar_indist.
      split; intros m' [Hdeq Hp]; split.
      - assumption.
      - destruct Hp.
        destruct H2.
        destruct H3.
        destruct H3. 
        pose proof (trace_max (m', x0)); unfold maximalization in H3; destruct H3.
        exists x.
        assumption.
      - assumption.
      - destruct Hp as [st' Hp].
        assert (behavior c (m, st) /\ behavior c (m', st')) by auto.
        pose proof (Hpar_indist st' m' H2) as [H_indistl H_indistr].
        apply H_indistl in Hdeq.
        destruct Hdeq as [Hdeq Hindist].
        pose proof (Hindist p' H1) as [p'' Hp'].
        exists st'.
        auto.
    Qed.
    
    Theorem Hpsni_impl_KPsni : forall c,
    In Property HPsniD (behavior c)
    -> In Cmd KPsniD c.
      unfold HPsniD, KPsniD.
      intros c HHPsniD p.
      intros.
      pose proof (trace_pfx_production).
      assert (Same_set Store (atk_knowledge c m p) (indistincts c m)). {
        pose proof trace_max (m, p); unfold maximalization in H2.
        destruct H2 as [st H2]; simpl in H2.
        pose proof trace_max_prod c m p st as Hmaxprod.
        pose proof hpsni_memset_invariance c HHPsniD m st as Hminv.
        pose proof (H1 c (m, st) (m, p)) as [Hprodl _].
        apply prefix_prefix_prod in H.
        pose proof Hminv (Hmaxprod H H2) p.
        auto.
      }
      assert (Same_set Store (indistincts c m) (atk_knowledge c m (a :: p))). {
        pose proof trace_max (m, a :: p). unfold maximalization in H3.
        destruct H3 as [st H3]; simpl in H3.
        pose proof trace_max_prod c m (a :: p) st as Hmaxprod.
        pose proof hpsni_memset_invariance c HHPsniD m st as Hminv.
        pose proof (H1 c (m, st) (m, (a :: p))) as [Hprodl _].
        pose proof Hminv (Hmaxprod H H3) (a :: p).
        auto with sets.
      }
      pose proof (Same_set_trans Store (atk_knowledge c m p) (indistincts c m) (atk_knowledge c m (a :: p))).
      auto.
    Qed.
  End Core.
End PSNI.