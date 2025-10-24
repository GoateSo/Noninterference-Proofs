Require Import Basic.
Require Import Lang.
Require Import SecPol.
Require Import Determinism.
Require Import SecDef SecPol Trace.
Require Import Grounding.
From Coq Require Import Equality Relations RelationClasses List Compare.
Import ListNotations.

From Coq Require Import Basics Equality List Ensembles Relations RelationClasses.

Module Type SecurityTheory (B : Basic) (LD : LangDefs) (TD : TraceDefs B LD) (SP : SecurityPol LD) (SD : SecurityDefs B LD TD SP) .
  Import B LD TD SP SD.
  Import LangNotations.

  Section SilentProperties.
      Theorem silent_indistinct : forall c m a p, sil a -> Same_set Store (atk_knowledge c m p) (atk_knowledge c m (a :: p)).
        unfold Same_set, Included, In, atk_knowledge, deq_evt_lst.
        intros.
        split; split; destruct H0; trivial; destruct H1 as [st' [Ha [p' [Hprod Hdeq]]]].
        - exists st'; split; trivial.
          exists p'; split; trivial.
          simpl.
          destruct (sil_dec a); trivial.
          contradiction.
        - exists st'; split; trivial.
          exists p'; split; trivial.
          simpl in Hdeq.
          destruct (sil_dec a); trivial.
          contradiction.
      Qed.
    End SilentProperties.

  Section DEqLists.
    Theorem deq_evt_lst_refl : forall l1, 
      deq_evt_lst l1 l1 -> deq_evt_lst l1 l1.
      trivial.
    Qed.

    Theorem deq_evt_lst_sym : forall l1 l2, 
      deq_evt_lst l1 l2 -> deq_evt_lst l2 l1.
      unfold deq_evt_lst.
      intros.
      rewrite H.
      reflexivity.
    Qed.

    Theorem deq_evt_lst_trans : forall l1 l2 l3,
      deq_evt_lst l1 l2 -> deq_evt_lst l2 l3 -> deq_evt_lst l1 l3.
      unfold deq_evt_lst.
      intros.
      rewrite H, H0.
      reflexivity.
    Qed.
  End DEqLists.
End SecurityTheory.