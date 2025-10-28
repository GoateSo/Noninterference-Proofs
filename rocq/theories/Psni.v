Require Import Basic Lang Determinism.
Require Import SecDef SecPol Trace.
Require Import BaseTheory TraceTheories.
Require Import SecTheory.

From Coq Require Import Basics Equality List Ensembles Relations RelationClasses Classes.Equivalence.
Import ListNotations.

Module Type PSNI (B : Basic) (BT : BaseTheories B) (LD : LangDefs) (TD : TraceDefs B LD) (SP : SecurityPol LD) (Det : DeterminismDef LD) (SD : SecurityDefs B LD TD SP) (ST : SecurityTheory B LD TD SP SD) (TT : TraceTheories B LD TD Det).
  Import B BT LD TD Det SP SD ST TT.
  Import LangNotations.

  Section Core.
    Context (D : Ensemble Label) `{DecD : DecideIn Label D}.
    
    Axiom trace_pfx_production : forall c cs, trace_pfx_prod c cs.
    Axiom trace_max : forall p, trace_pfx_maximize p.
    Axiom trace_max_prod : forall c m p st, (c, m)==>*[p] -> (m, p) <=| (m, st) -> c ~~> (m, st).

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
      - destruct Ht as [t [Htprod _]].
        exists t; assumption.
      - destruct Ht as [st' Hp].
        apply (hpsni_indistinct_conseq c H st m st') in Hdeq. 
          + destruct Hdeq as [Hdeq Hindist].
            exists st'.
            auto.
          + split; assumption.
    Qed.
    
    Lemma app_prefix : forall (a : Event) p, Prefix p (p ++ [a]).
      intros; induction p; [apply Prefix_empty | apply Prefix_some, IHp].
    Qed.

    Theorem Hpsni_impl_KPsni : forall c, In Property HPsniD (behavior c) -> In Cmd KPsniD c.
      unfold HPsniD, KPsniD.
      intros c HHPsniD p m a ? ?.
      pose proof trace_pfx_production as Htraceprod.
      pose proof (hpsni_memset_invariance c HHPsniD m) as Htmp.
      assert (Same_set Store (atk_knowledge c m p) (indistincts c m)). {
        apply (prefix_prefix_prod p (p ++ [a]) (app_prefix a p)) in H.
        pose proof trace_max (m, p) as [st Htmaxpref].
        apply Htmp with st.
        - apply trace_max_prod with p; assumption.
        - assumption.
      }
      assert (Same_set Store (indistincts c m) (atk_knowledge c m (p ++ [a]))). {
        pose proof trace_max (m, p ++ [a]) as [st Htmaxpref].
        apply Same_set_sym.
        apply Htmp with st.
        - apply trace_max_prod with (p ++ [a]); assumption.
        - assumption.  
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
          * rewrite (trace_pfx_production c (m1, s1) (m1, l ++ [x])) in Hdp1.
            rewrite Hdp1 in H1.
            destruct (HKPsni l m1 x); [assumption | assumption |].
            unfold Included, In, atk_knowledge in H2.
            pose proof H2 m2 as H2ak.
            destruct H2ak. {
              split; [assumption | exists s2].
              split; [| exists p2; split]; assumption. 
            }
            intros.
            destruct H6 as [st' [Htprod [p' [Hpprod Hpeq]]]].
            unfold deq_evt_lst in Hpeq.
            rewrite silent_split in Hpeq. simpl in Hpeq.
            destruct (sil_dec x); [contradiction |].
            exists p'.
            auto.
    Qed.  
  End Core.
End PSNI.