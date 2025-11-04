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
      destruct HHLfpD. {
        unfold dlt_pfx; split.
        - constructor; simpl.
          + apply deq_evt_lst_sym in Hpdeq.
            unfold dle_evt_lst,deq_evt_lst in *.
            rewrite silent_split in *.
            rewrite (nsil_sing a) in *; try assumption.
            rewrite Hpdeq.
            apply (app_prefix a (erase p)).
          + apply deq_store_equiv.
            assumption.
        - intro H.
          inversion H; simpl in *; clear H2 H.
          admit.
      }
      destruct H.
      admit. 
    Admitted.

    Theorem Hplfp_impl_KPlfp : forall c, In Property HLfpD (behavior c) -> In Cmd KLfpD c.
      intros ? Hlfp ? ? ? Hpaprod Hnsil.
      assert ((c, m) ==>*[ p ++ [a]] /\ ~ sil a) by eauto.
      pose proof HLfpD_conseq c Hlfp p m a H as Hlemma; clear H.
      split.
      - intros m' [Hdeq [p' [Hpprod Hpdeq]]].
        pose proof Hlemma m' Hdeq; split; try assumption.
        destruct H as [p2 [a' [? [? ?]]]]. { exists p'; eauto. }
        exists p2, a'.
        split; try split; try assumption.
      - apply (prog_impl_atk_knowledge c m p a); assumption.
    Qed.

    Theorem klfp_det_impl_hlfp : forall c, In Cmd KLfpD c 
      -> (det_rel steps_to_combined)
      -> In Property HLfpD (behavior c).  
    Admitted.
  End Core.
End LFP.