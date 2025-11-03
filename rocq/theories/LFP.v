Require Import Basic Lang Determinism.
Require Import SecDef SecPol Trace.
Require Import BaseTheory TraceTheories DetTheories.
Require Import SecTheory.

From Coq Require Import Basics Equality List Ensembles Relations RelationClasses Classes.Equivalence.
Import ListNotations.

Module Type LFP (B : Basic) (BT : BaseTheories B) (LD : LangDefs) (TD : TraceDefs B LD) (SP : SecurityPol LD) (Det : DeterminismDef LD) (SD : SecurityDefs B LD TD SP) (TT : TraceTheories B LD TD) (ST : SecurityTheory B LD TD SP SD TT) (DT : DetTheories B LD TD Det TT).
  Import B BT LD TD Det SP SD ST TT DT.
  Import LangNotations.

  Section Core.
    Context (D : Ensemble Label) `{DecD : DecideIn Label D}.

    Lemma awooga : forall c, In Property HLfpD (behavior c)
    -> forall p m a, ((c, m) ==>*[p ++ [a]] /\ ~ sil a)
    -> forall m', (deq_store m m') 
    -> (exists p', ((c, m') ==>*[p'] /\ deq_evt_lst p p')) 
    -> (exists p2 a', ((c, m') ==>*[p2] /\ deq_evt_lst p2 (p ++ [a]) /\ ~ sil a')).
      intros.
      destruct H2.
      destruct H0, H2.
      pose proof trace_max c m (p ++ [a]) H0 as [st1 [? ?]].  
      inversion H5. inversion H7. subst.
      admit.
    Admitted.

    Lemma rev_destruct {A : Type} : forall (l : list A), l = [] \/ (exists init a, l = init ++ [a]).
      induction l as [| a l' IH].
      - left; reflexivity.
      - destruct l' as [| b l''].
        + right.
          exists [], a; reflexivity.
        + destruct IH; try discriminate.
          destruct H as [? [? ?]].
          right. 
          exists (a :: x), x0.
          rewrite <-app_comm_cons.
          rewrite H.
          reflexivity.
    Qed.
           

    Theorem Hplfp_impl_KPlfp : forall c, In Property HLfpD (behavior c) -> In Cmd KLfpD c.
      unfold HLfpD, KLfpD, Same_set, progressD, Included, In, atk_knowledge, prog_knowledge.
      intros. 
      assert ((c, m) ==>*[ p ++ [a]] /\ ~ sil a) by eauto.
      pose proof awooga c H p m a H2.
      split; intros m' [? ?]. pose proof H3 m' H4.
      - pose proof H6 H5; split; try assumption.
        destruct H7 as [p2 [a' [? [? ?]]]].
        exists p2.
        exists a'.
        split; try split; try assumption.
        unfold deq_evt_lst in *.
        destruct H5 as [p' [? ?]].
        assert (a = a') by admit.
        rewrite <-H11.
        assumption.
      - split; try assumption.
        (* destruct H5 as [p' [a' [[? ?] ?]]].
        destruct (rev_destruct p').
        + subst.
          inversion H6.
          rewrite silent_split in H9.
          simpl in H9.
          destruct (sil_dec a'); try contradiction.
          pose proof app_cons_not_nil (erase p) nil a'.
          contradiction.
        + destruct H8 as [? [? ?]].
          unfold deq_evt_lst in *.
          rewrite H8 in H6.
          repeat rewrite silent_split in *.
          admit. *)
    Admitted.

    Theorem klfp_det_impl_hlfp : forall c, In Cmd KLfpD c 
      -> (det_rel steps_to_combined)
      -> In Property HLfpD (behavior c).  
    Admitted.
  End Core.
End LFP.