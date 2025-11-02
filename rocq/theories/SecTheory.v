Require Import Basic Lang Determinism.
Require Import SecPol SecDef Trace.
Require Import BaseTheory.
From Coq Require Import Basics Equality List Ensembles Relations RelationClasses.
Import ListNotations.

Module Type SecurityTheory (B : Basic) (LD : LangDefs) (TD : TraceDefs B LD) (SP : SecurityPol LD) (SD : SecurityDefs B LD TD SP) .
  Import B LD TD SP SD.
  Import LangNotations.

  Section SilentProperties.
    Theorem silent_split : forall l1 l2, erase (l1 ++ l2) = erase l1 ++ erase l2.
      intros.
      induction l1 ; [reflexivity|].
      simpl; destruct (sil_dec a); auto.
      rewrite IHl1.
      reflexivity.
    Qed.

    Theorem silent_indistinct : forall c m a p, sil a -> Same_set Store (atk_knowledge c m p) (atk_knowledge c m (p ++ [a])).
      unfold Same_set, Included, In, atk_knowledge, deq_evt_lst.
      intros.
      split; split; destruct H0; trivial; destruct H1 as [st' [Ha [p' [Hprod Hdeq]]]].
      - exists st'; split; trivial.
        exists p'; split; trivial.
        rewrite silent_split; simpl.
        destruct (sil_dec a); rewrite Hdeq; [auto using app_nil_r | contradiction].
      - exists st'; split; trivial.
        exists p'; split; trivial.
        simpl in Hdeq.
        rewrite <-Hdeq; simpl; rewrite silent_split; simpl.
        destruct (sil_dec a); [auto using app_nil_r | contradiction].
    Qed.
  End SilentProperties.

  Section DEqLists.
    Theorem deq_evt_lst_refl : forall l1, deq_evt_lst l1 l1.
      intros.
      unfold deq_evt_lst.
      trivial.
    Qed.

    Theorem deq_evt_lst_sym : forall l1 l2,  deq_evt_lst l1 l2 -> deq_evt_lst l2 l1.
      unfold deq_evt_lst.
      intros.
      rewrite H.
      reflexivity.
    Qed.

    Theorem deq_evt_lst_trans : forall l1 l2 l3, deq_evt_lst l1 l2 -> deq_evt_lst l2 l3 -> deq_evt_lst l1 l3.
      unfold deq_evt_lst.
      intros.
      rewrite H, H0.
      reflexivity.
    Qed.
  End DEqLists.

  Section DleLists.
    Theorem dle_evt_lst_refl : forall l1, dle_evt_lst l1 l1.
      intros.
      unfold dle_evt_lst.
      induction l1.
        - auto.
        - unfold erase.
          destruct (sil_dec a); auto.
    Qed.

    Theorem dle_evt_lst_trans : forall l1 l2 l3, dle_evt_lst l1 l2 -> dle_evt_lst l2 l3 -> dle_evt_lst l1 l3.
      unfold dle_evt_lst.
      intros.
      pose proof (@prefix_preorder_inst Event) as [_ Htrans].
      unfold Transitive in Htrans.
      apply (Htrans (erase l1) (erase l2) (erase l3)); assumption.
    Qed.
  End DleLists.

  Section DeqTracePfx.
    Instance deq_pfx_equiv : Equivalence deq_pfx.
      destruct deq_store_equiv as [Hdsr Hdss Hdst].
        split; unfold deq_pfx, Reflexive, Symmetric, Transitive.
        - auto using deq_evt_lst_refl.
        - intros [s1 l1] [s2 l2] [H1 H2].
          auto using deq_evt_lst_sym.
        - intros [s1 l1] [s2 l2] [s3 l3] [H1 H2] [H3 H4].
          unfold Transitive in Hdst.
          split.
          + apply (deq_evt_lst_trans l1 l2 l3) in H1; [exact H1 | exact H3]. 
          + apply (Hdst s1 s2 s3) in H2; [exact H2 | exact H4].
    Defined. 
    
    Instance dle_pfx_preorder : PreOrder dle_pfx.
      destruct deq_store_equiv as [RS SS TS].
      split; unfold dle_pfx.
      - unfold Reflexive.
        intros.
        auto using dle_evt_lst_refl.
      - unfold Transitive.
        intros [s1 l1] [s2 l2] [s3 l3].
        simpl.
        intros [H1 H2] [H3 H4].
        split.
        + apply (dle_evt_lst_trans l1 l2 l3); auto.
        + apply (TS s1 s2 s3); auto.
    Defined.
  End DeqTracePfx.
End SecurityTheory.