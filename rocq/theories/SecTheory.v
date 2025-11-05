Require Import Basic Lang Determinism.
Require Import SecPol SecDef Trace.
Require Import BaseTheory TraceTheories.
From Coq Require Import Basics Equality List Ensembles Relations RelationClasses Setoid Classes.Morphisms.
Import ListNotations.

Module Type SecurityTheory (B : Basic) (LD : LangDefs) (BT : BaseTheories B) (TD : TraceDefs B LD) (SP : SecurityPol LD) (SD : SecurityDefs B LD TD SP) (TT : TraceTheories B LD TD).
  Import B BT LD TD SP SD TT.
  Import LangNotations.

  Ltac rev_ind_for_list :=
    lazymatch goal with
    | [ |- forall (xs : list Event), _ ] =>
        induction xs using rev_ind
    | _ => idtac
    end.

  Section SilentProperties.
    Theorem silent_split : forall l1 l2, erase (l1 ++ l2) = erase l1 ++ erase l2.
      intros.
      induction l1 ; [reflexivity|].
      simpl; destruct (sil_dec a); try assumption.
      rewrite IHl1.
      reflexivity.
    Qed.

    Lemma sil_sing : forall a, sil a -> erase [a] = [].
      intros; simpl.
      destruct (sil_dec a); try contradiction.
      reflexivity.
    Qed.

    Lemma nsil_sing : forall a, ~ sil a -> erase [a] = [a].
      intros; simpl.
      destruct (sil_dec a); try contradiction.
      reflexivity.
    Qed.

    Lemma sil_hd : forall a l, sil a -> erase (a :: l) = erase l.
      intros; simpl.
      destruct (sil_dec a); try contradiction.
      reflexivity.
    Qed.

    Lemma nsil_hd : forall a l, ~ sil a -> erase (a :: l) = a :: erase l.
      intros; simpl.
      destruct (sil_dec a); try contradiction.
      reflexivity.
    Qed.

    Lemma silent_decomp : forall l1 l2 e, ~ sil e -> erase l1 = erase l2 -> exists l' ls', erase (l1 ++ [e]) = erase (l2 ++ l') /\ l' = ls' ++ [e] /\ erase ls' = [].
      induction l1, l2; intros.
      - exists [e], [].
        eauto.
      - simpl in *.
        destruct (sil_dec e); try discriminate.
        + exists [e0], [].
          rewrite silent_split, <-H0.
          destruct (sil_dec e0); try contradiction.
          rewrite nsil_sing; try assumption.
          eauto.
      - simpl in *.
        destruct (sil_dec a); try discriminate.
        + exists [e], [].
          rewrite silent_split, nsil_sing; try assumption.
          rewrite H0.
          eauto.
      - exists [e0], [].
        rewrite silent_split, H0, silent_split.
        eauto.
    Qed.

    Lemma app_cons_middle :
      forall (A : Type) (xs ys : list A) (x : A),
        xs ++ [x] ++ ys = xs ++ (x :: ys).
    Proof.
      intros A xs ys x.
      induction xs as [| h t IH]; simpl.
      - reflexivity.
      - rewrite <-IH.
        reflexivity.
    Qed.

    Lemma silent_break : forall l1 l2 e, 
      ~ sil e 
      -> erase l1 = erase (l2 ++ [e]) 
      -> exists l1a ls, 
          l1a ++ (e :: ls) = l1 
          /\ erase l1a = erase l2 
          /\ erase ls = [].
      rev_ind_for_list; rev_ind_for_list; intros.
      - rewrite silent_split, nsil_sing in H0; try assumption.
        discriminate.
      - rewrite <-app_assoc, silent_split, silent_split in H0.
        rewrite (nsil_sing e) in H0; try assumption.
        rewrite app_assoc, <-silent_split in H0.
        pose proof app_cons_not_nil (erase (l2 ++ [x])) [] e.
        contradiction.
      - rewrite silent_split in H0.
        destruct (sil_dec x).
        + rewrite sil_sing, app_nil_r in H0; try assumption.
          specialize (IHl1 [] e H H0) as [l1a [l1b [Hcompose [Hdeq1 Hdeq2]]]].
          exists l1a, (l1b ++ [x]).
          split; [|split].
          * rewrite <-app_cons_middle in *.
            rewrite <-Hcompose.
            repeat rewrite <- app_assoc.
            reflexivity.
          * exact Hdeq1.
          * rewrite silent_split, sil_sing, Hdeq2; try assumption.
            reflexivity. 
        + exists l1, [].
          rewrite silent_split, (nsil_sing x), (nsil_sing e) in H0; try assumption.
          rewrite <-app_nil_l in H0.
          apply app_inj_tail in H0 as [Ha Hb]; subst.
          eauto.
      - destruct (sil_dec x).
        + rewrite silent_split, (sil_sing x), app_nil_r in H0; try assumption.
          specialize (IHl1 (l2 ++ [x0]) e H H0) as [l1a [ls [Hcompose [Hdeq1 Hdeq2]]]].
          exists l1a, (ls ++ [x]).
          repeat rewrite silent_split.
          rewrite (sil_sing x), app_nil_r; try assumption.
          rewrite <-Hcompose, <-app_assoc, app_comm_cons.
          rewrite silent_split in Hdeq1.
          split; try split; try assumption.
        + destruct (sil_dec x0).
          * repeat rewrite silent_split in H0. 
            rewrite (sil_sing x0), (nsil_sing x), (nsil_sing e), app_nil_r in H0; try assumption.
            apply app_inj_tail in H0 as [Ha Hb]; subst.
            exists l1, [].
            rewrite silent_split, (sil_sing x0), app_nil_r; try assumption.
            split; [|split]; eauto.
          * rewrite silent_split, silent_split in H0.
            rewrite (nsil_sing x), (nsil_sing e) in H0; try assumption.
            apply app_inj_tail in H0 as [Ha Hb]; subst.
            specialize (IHl1 l2 x0 n0 Ha) as [l1a [ls [Hcompose [Hdeq1 Hdeq2]]]].
            subst; clear n.
            exists (l1a ++ x0 :: ls), [].
            split; [|split]; try assumption; try reflexivity.
    Qed.

    Lemma erasure_inv : forall p a p2, Prefix ((erase p) ++ [a]) p2 -> Prefix (erase (p ++ [a])) p2.
      intros. destruct (sil_dec a).
      - rewrite silent_split, sil_sing, app_nil_r; try assumption.
        pose proof (app_prefix (erase p) [a]).
        pose proof @prefix_preorder_inst Event as [_ Htrans].
        specialize (Htrans (erase p) (erase p ++ [a]) p2).
        apply Htrans; assumption.
      - rewrite silent_split, nsil_sing; try assumption.
    Qed.

    Theorem silent_indistinct : forall c m a p, sil a -> Same_set Store (atk_knowledge c m p) (atk_knowledge c m (p ++ [a])).
      intros.
      split; split; destruct H0; try assumption; destruct H1 as [p' [Hprod Hdeq]]; exists p'; split; try assumption; unfold deq_evt_lst.
      - rewrite silent_split; simpl.
        destruct (sil_dec a); rewrite Hdeq; [auto using app_nil_r | contradiction].
      - rewrite <-Hdeq; simpl; rewrite silent_split; simpl.
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

    Instance deq_evt_lst_refl_equiv: Equivalence (deq_evt_lst).
    Proof.
      constructor.
      - exact deq_evt_lst_refl.
      - exact deq_evt_lst_sym.
      - exact deq_evt_lst_trans.
    Qed.

    Global Add Setoid (list Event) deq_evt_lst deq_evt_lst_refl_equiv as deq_evt_lst_setoid.
  End DEqLists.

  Section DleLists.
    Theorem dle_evt_lst_refl : forall l1, dle_evt_lst l1 l1.
      intros.
      unfold dle_evt_lst.
      induction l1; [reflexivity | ].
      unfold erase.
      destruct (sil_dec a); auto.
    Qed.

    Theorem dle_evt_lst_trans : forall l1 l2 l3, dle_evt_lst l1 l2 -> dle_evt_lst l2 l3 -> dle_evt_lst l1 l3.
      unfold dle_evt_lst.
      intros.
      pose proof (@prefix_preorder_inst Event) as [_ Htrans].
      unfold Transitive in Htrans.
      apply (Htrans (erase l1) (erase l2) (erase l3)); assumption.
    Qed.

    Lemma gen_prefix_erase_exists : 
      forall (p l2 : list Event), 
        Prefix p (erase l2) -> 
        exists l2', Prefix l2' l2 /\ p = erase l2'.
    Proof.
      intros p l2.
      generalize dependent p.
      induction l2 as [|e l2' IHl2]; intros.
      - inversion H.
        exists []; eauto using Prefix_empty.
      - simpl in H; destruct (sil_dec e) eqn:Heq.
        + specialize (IHl2 p H) as [l2_sub [H_sub_prefix H_sub_erase]].
          exists (e :: l2_sub); simpl; split.
          * constructor; assumption.
          * rewrite Heq; assumption.
        + inversion H.
          * exists []. now split; [constructor | reflexivity].
          * subst.
            specialize (IHl2 lst0 H2) as [l2'' [? ?]].
            exists (e :: l2''); simpl.
            split.
            -- constructor.
              assumption.
            -- rewrite Heq, H1.
              reflexivity.
    Qed.

    Theorem dle_evt_lst_alt : 
      forall (l1 l2 : list Event), 
        dle_evt_lst l1 l2 -> 
        exists l2', Prefix l2' l2 /\ deq_evt_lst l1 l2'.
    Proof.
      intros l1 l2 H.
      apply gen_prefix_erase_exists with (p := erase l1), H.
    Qed.
    
    Lemma erase_in : forall e p, List.In e (erase p) -> ~ sil e.
      intros.
      induction p.
      - inversion H.
      - destruct (sil_dec a) eqn:Heq.
        + simpl in H; rewrite Heq in H.
          eauto.
        + simpl in H; rewrite Heq in H.
          apply in_inv in H; destruct H.
          * subst; assumption.
          * eauto.
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
        auto using dle_evt_lst_refl.
      - unfold Transitive.
        intros [s1 l1] [s2 l2] [s3 l3].
        intros [H1 H2] [H3 H4].
        split.
        + apply (dle_evt_lst_trans l1 l2 l3); auto.
        + apply (TS s1 s2 s3); auto.
    Defined.
  End DeqTracePfx.

  Section DltTracePfx.
    Lemma dlt_conseq : forall m p1 p2, dlt_pfx (m, p1) (m, p2) -> 
      dle_evt_lst p1 p2 /\ ~ deq_evt_lst p1 p2.
      intros; unfold dlt_pfx, dle_pfx, deq_pfx in H.
      simpl in H; destruct H.
      split.
      - destruct H. assumption.
      - intro Hbad.
        destruct H0, H.
        split; assumption.
    Qed.
    
    Lemma dlt_impl_prop_prefix :  forall m p1 p2, dlt_pfx (m, p1) (m, p2) ->
      PropPrefix (erase p1) (erase p2).
      intros; apply dlt_conseq in H as [Hdle Hdeq].
      unfold dle_evt_lst, deq_evt_lst in *.
      split; assumption.
    Qed.

    Lemma dlt_pfx_alt : forall m p1 p2, dlt_pfx (m, p1) (m, p2) -> exists a, ~ sil a /\ dle_evt_lst (p1 ++ [a]) p2.
      intros.
      apply dlt_impl_prop_prefix in H.
      apply prop_prefix_exists_next in H as [a [Hpref Hpres]].
      exists a; split.
      - apply erase_in in Hpres. assumption.
      - unfold dle_evt_lst.
        apply erasure_inv.
        assumption.
    Qed.
  End DltTracePfx.

  (* theorems for : atk_know p <= prog_know p <= atk_know (p ++ [a]) *)
  Section SubKnowledge.
    Lemma prog_impl_atk_knowledge: forall c m p a, (c, m) ==>*[p ++ [a]] -> ~ sil a -> Included Store (prog_knowledge c m p) (atk_knowledge c m p).
      intros ? ? ? ? Htsub Hnsil.
      intros m' [Hmdeq [p' [a' [[Hpprod Hpdeq] Hnsil']]]].
      split; try assumption.
      unfold deq_evt_lst in Hpdeq.
      pose proof (silent_break p' p a') Hnsil' Hpdeq as  [l1a [ls [Hcompose [Hdeq1 Hdeq2]]]].
      subst.
      exists l1a.
      split.
      - assert (Prefix l1a (l1a ++ a' :: ls)). {
          clear Hpdeq Hpprod Hdeq1.
          induction l1a.
          - apply Prefix_empty.
          - rewrite <-app_comm_cons.
            constructor.
            assumption.
        }
        apply (prefix_prefix_prod l1a (l1a ++ a' :: ls)); assumption.
      - unfold deq_evt_lst; auto.
    Qed.
  End SubKnowledge. 
End SecurityTheory.