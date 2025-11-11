Require Import Basic Lang Determinism.
Require Import SecDef SecPol Trace.
Require Import BaseTheory TraceTheories DetTheories.
Require Import SecTheory.

From Coq Require Import Basics Equality List Ensembles Relations RelationClasses Classes.Equivalence.
Import ListNotations.

Module Type PINI (B : Basic) (BT : BaseTheories B) (LD : LangDefs) (TD : TraceDefs B LD) (SP : SecurityPol LD) (Det : DeterminismDef LD) (SD : SecurityDefs B LD TD SP) (TT : TraceTheories B LD TD) (ST : SecurityTheory B LD BT TD SP SD TT)  (DT : DetTheories B LD TD Det TT).
  Import B BT LD TD Det SP SD ST TT DT.
  Import LangNotations.

  Section Core.
    Context (D : Ensemble Label) `{DecD : DecideIn Label D}.

    Lemma prefix_first_eq_last_eq : forall (p : list Event) a b, Prefix (p ++ [a]) (p ++ [b]) -> a = b.
      intros; induction p; inversion H; auto.
    Qed.
    
    Lemma Hpini_conseq : forall c, In Property HPiniD (behavior c) -> forall m m' p e, ~ sil e 
      -> deq_store m m'
      -> (c, m)==>*[p ++ [e]]
      -> (exists p' e', ~sil e' /\ (c, m')==>*[p'] /\ deq_evt_lst p' (p ++ [e']))
      -> exists pp, (c, m')==>*[pp] /\ deq_evt_lst (p ++ [e]) pp.
      intros. 
      destruct H3 as [p' [e' [Hnsil [Hprod' Hdeq']]]].
      pose proof trace_max c m (p ++ [e]) H2 as [st [Hpfx Htprod]].
      pose proof trace_max c m' p' Hprod' as [st' [Hpfx' Htprod']].
      inversion Hpfx; inversion Hpfx'; subst.
      unfold In, HPiniD in H.
      specialize (H (m,st) (m',st') Htprod Htprod' H1).
      specialize (H (m, p++[e]) (m',p') Hpfx Hpfx').
      assert (e = e'). {
        destruct H; inversion H; subst; unfold deq_evt_lst, dle_evt_lst in *; simpl in *; rewrite Hdeq' in H3; repeat rewrite silent_split in H3;
        rewrite nsil_sing, nsil_sing in H3; try assumption.
        - apply (prefix_first_eq_last_eq (erase p)).
          assumption.
        - symmetry.
          apply (prefix_first_eq_last_eq (erase p) e' e).
          assumption.
      }
      exists p'.
      unfold deq_evt_lst, dle_evt_lst in *.
      split; try assumption.
      rewrite Hdeq', H3.
      reflexivity. 
    Qed.

    Theorem Hpini_impl_KPini : forall c, In Property HPiniD (behavior c) -> In Cmd KPiniD c.
      intros c HPiniD p m e Hprod Hnsil.
      split.
      - intros m' [Hdeq [p' [e' [[Hpprod Hpdeq] Hnsil']]]].
        split; [assumption|].
        pose proof Hpini_conseq c HPiniD m m' p e.
        specialize (H Hnsil Hdeq Hprod).
        destruct H as [ps [Hpsprod Hpsdeq]]; [eauto |].
        unfold deq_evt_lst in *.
        eauto.
      - apply atk_next_impl_prog_knowledge; assumption.
    Qed.

    Theorem kpini_det_impl_hpini : forall c, In Cmd KPiniD c 
      -> (det_rel steps_to_combined)
      -> In Property HPiniD (behavior c).  
    Admitted.
  End Core.
End PINI.