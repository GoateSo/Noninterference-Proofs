Require Import Basic Lang Determinism Trace.
Require Import BaseTheory.
Require Import TraceTheories.
From Coq Require Import Equality Relations RelationClasses List Compare Sets.Ensembles Streams Setoid Classes.Morphisms.
Import ListNotations.

Module Type DetTheories (B : Basic) (LD : LangDefs) (TD : TraceDefs B LD) (DD : DeterminismDef LD) (TT : TraceTheories B LD TD).
  Import B LD TD DD TT.
  Import LangNotations.

  Lemma Eq_EvtSt_refl : forall s: EvtStream, Eq_EvtSt s s.
    cofix CH.
    intros.
    destruct s; constructor; try reflexivity.
    apply CH.
  Qed.

  Lemma Eq_EvtSt_sym : forall s1 s2: EvtStream, Eq_EvtSt s1 s2 -> Eq_EvtSt s2 s1.
    cofix CH.
    intros.
    destruct H; [apply Eq_EvtSt_refl | constructor].
    - rewrite H; reflexivity.
    - apply CH.
      assumption.
  Qed.

  Lemma Eq_EvtSt_trans : forall s1 s2 s3 : EvtStream, Eq_EvtSt s1 s2 -> Eq_EvtSt s2 s3 -> Eq_EvtSt s1 s3.
    cofix CH.
    intros ? ? ? H12 H23.
    destruct H12 eqn:Heqn.
    - destruct s3.
      + inversion H23.
      + apply Eq_EvtSt_refl.
    - destruct s3; inversion H23.
      + subst; constructor; [reflexivity | ].
        apply (CH t1 t2 s3); assumption.
  Qed.  

  Instance Eq_EvtSt_equiv: Equivalence (Eq_EvtSt).
  Proof.
    constructor.
    - exact Eq_EvtSt_refl.
    - exact Eq_EvtSt_sym.
    - exact Eq_EvtSt_trans.
  Qed.

  Global Instance EvtCons_proper :
    Proper (eq ==> Eq_EvtSt ==> Eq_EvtSt ) ConsEvt.
  Proof.
    intros h1 h2 H_head t1 t2 H_tail.
    subst; constructor; [reflexivity | assumption].
  Qed.

  Global Add Setoid EvtStream Eq_EvtSt Eq_EvtSt_equiv as EvtStreamSetoid.

  Section DetTraces.
    Variable Det : (det_rel steps_to_combined).
    Lemma det_trace_prod : forall c m t1 t2, c ~~> (m, t1) -> c ~~> (m, t2) -> Eq_EvtSt t1 t2.
      unfold "~~>", behavior; simpl.
      cofix CH. 
      intros.
      unfold det_rel, steps_to_combined in Det.
      inversion H; inversion H0; subst.
      - destruct (Det (c, m) (c', s') (c'0, s'0) a a0); try assumption.
        + constructor.
          * assumption.
          * rewrite pair_equal_spec in H3; destruct H3; subst;
            apply (CH c'0 s'0 st st0); assumption.
      - apply produce_impl_canstep in H1.
        unfold no_step in H6.
        unfold has_step in H1.
        contradiction.
      - apply produce_impl_canstep in H5.
        contradiction.
      - apply Eq_EvtSt_refl.
    Qed.

    Ltac subst_eq_steps :=
      repeat lazymatch goal with
        | [H : (_, _) = (_, _) |- _] => injection H ; intros ; subst ; clear H
        | [H0 : ?cs -->[?a0] ?cs0, H1 : ?cs -->[?a1] ?cs1 |- _]
          => assert (cs1 = cs0 /\ a1 = a0) as [? ?] by eauto using (Det cs) ; subst ; clear H1
        | [H0 : ?cs -->[?a0] ?cs0, H1 : steps_to_combined ?cs ?a1 ?cs1 |- _]
          => assert (cs1 = cs0 /\ a1 = a0) as [? ?] by eauto using (Det cs) ; subst ; clear H1
      end.

    Lemma evt_prefix_prod_both : forall lst st0, EvtPrefix lst st0 -> forall c s st1, Produces c s st0 -> Produces c s st1 -> EvtPrefix lst st1.
      intros lst st0 EvtPfx. induction EvtPfx ; intros c s st1 Prod0 Prod1 ; auto using EvtPrefix_empty.
      inversion Prod0 ; inversion Prod1 ; subst; subst_eq_steps.
      - eauto using EvtPrefix_some.
      - handle_prog_contradict.
    Qed.

    Lemma pfx_prod_both : forall pfx s st0, pfx <=| (s, st0) -> forall c st1, Produces c s st0 -> Produces c s st1 -> pfx <=| (s, st1).
      intros pfx s st0 PfxOf0 c st1 Prod0 Prod1.
      inversion PfxOf0 as [? lst ? EvtPfx]. subst.
      eauto using LeTrace_intro, evt_prefix_prod_both.
    Qed.

    Lemma prod_mstep : forall c s cs lst, (c, s) ==>*[lst] cs -> forall st, Produces c s st
        -> exists st', Produces c s (prepend lst st').
      intros c s cs lst MStep. dependent induction MStep ; intros st Prod ; eauto.
      destruct cs1 as [c1 s1].
      inversion Prod ; subst.
      - subst_eq_steps.
        assert (exists st', Produces c1 s1 (prepend lst st')) as [st' ?] by eauto.
        eauto using Produces_step.
      - handle_prog_contradict.
    Qed. 

    Lemma prod_prepend_mstep : forall c s c' s' lst, (c, s) ==>*[lst] (c', s')
        -> forall st, c ~~> (s, (prepend lst st)) -> c' ~~> (s', st).
      intros c s c' s' lst MStep. dependent induction MStep ; intros st ProdPrepend ; auto.
      destruct cs1 as [c1 s1].
      simpl in ProdPrepend ; inversion ProdPrepend ; subst ; subst_eq_steps.
      eauto.
    Qed. 

    Lemma length_impl_split : forall (p1 p2 : list Event), length p1 <= length p2 -> exists p1', length (p1 ++ p1') = length p2.
      intros.
      induction p2 using rev_ind.
      - inversion H.
        exists [].
        simpl.
        rewrite app_nil_r.
        assumption.
      - rewrite (PeanoNat.Nat.lt_eq_cases (length p1) (length (p2 ++ [x]))) in H .
        destruct H.
        + rewrite last_length in H.
          apply Arith_base.lt_n_Sm_le_stt in H.
          specialize (IHp2 H) as [p1' Heq].
          exists (p1' ++ [x]).
          rewrite app_assoc, last_length, last_length.
          auto.
        + exists [].
          rewrite app_nil_r, H.
          reflexivity.
    Qed.
    
    Lemma det_prod_impl_same : forall p c m cs1 cs2,
      (c, m) ==>*[p] cs1 
      -> (c, m) ==>*[p] cs2
      -> cs1 = cs2.
      induction p; intros; inversion H; inversion H0; subst.
      - reflexivity.
      - unfold det_rel, steps_to_combined in Det.
        specialize (Det (c,m) cs3 cs6 a a H5 H11) as [Hceq _].
        subst.
        destruct cs6.
        specialize (IHp c0 s cs1 cs2 H6 H12).
        assumption.
    Qed.

    Lemma det_prod_impl_prefix : forall p1 p2 c m,
      (length p1) <= (length p2)
      -> (c, m) ==>*[p1]
      -> (c, m) ==>*[p2]
      -> Prefix p1 p2.
      induction p1, p2; auto; intros.
      - simpl in H.
        apply PeanoNat.Nat.nle_succ_0 in H.
        exfalso.
        apply H.
      - destruct H0, H1.
        inversion H0. inversion H1.
        subst.
        unfold det_rel, steps_to_combined in Det.
        pose proof (Det (c, m) cs1 cs4 a e) as one_step_det.
        specialize (one_step_det H6 H12) as [HeqConf HdeqE].
        rewrite HdeqE.
        apply Prefix_some.
        simpl in H.
        apply le_S_n in H.
        destruct cs1 as [c' m']; subst.
        specialize (IHp1 p2 c' m' H).
        destruct IHp1.
        + exists x. assumption.
        + exists x0. assumption.
        + auto.
        + apply Prefix_some.
          assumption.
    Qed.

    Lemma prod_mstep_prefix : forall lst c s st cs, Produces c s st
        -> (c, s) ==>*[lst] cs
        -> EvtPrefix lst st.
      induction lst ; intros c s st cs Prod MStep ; eauto using EvtPrefix_empty.
      inversion MStep ; subst ; inversion Prod ; subst.
      - destruct cs1 as [c1 s1] ; subst_eq_steps.
        eauto using EvtPrefix_some.
      - handle_prog_contradict.
    Qed.

    Lemma prod_conv_prefix : forall lst st, EvtPrefix lst st
        -> forall c s c' s' lst', (c, s) ==>*[lst'] (c', s') /\ no_step c' s'
        -> Produces c s st
        -> Prefix lst lst'.
        intros lst st EvtPfx. induction EvtPfx ; intros c s c' s' lst' Conv Prod ; auto.
        inversion Prod; subst; destruct Conv as [Conv Hend]; inversion Conv; subst.
        - handle_prog_contradict.
        - subst_eq_steps.
          eauto.
    Qed. 

    Lemma det_trace_pfx_production : forall c m st, 
      c ~~> (m, st) -> (forall p, (c, m) ==>*[p] -> (m, p) <=| (m, st)).
      intros ? ? ? ?.
      pose proof Det (c,m) as one_step_det.
      unfold steps_to_combined, det_rel in one_step_det.
      intros.
      destruct H0.
      pose proof prod_mstep_prefix p c m st x.
      unfold "~~>", behavior in H; simpl in H.
      constructor.
      apply H1; assumption.
    Qed.
  End DetTraces.
End DetTheories.