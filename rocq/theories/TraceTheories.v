Require Import Basic Lang Trace Determinism.
From Coq Require Import Equality Relations RelationClasses List Compare Sets.Ensembles.
Import ListNotations.

Module Type TraceTheories  (B : Basic) (LD : LangDefs) (TD : TraceDefs B LD) (DD : DeterminismDef LD).
  Import B LD TD DD.
  Import LangNotations.

  Axiom deterministic : forall cs, one_step_det cs.

  Lemma lst_prefix_stream_prefix : forall lst0 lst1, Prefix lst0 lst1 -> forall st, EvtPrefix lst1 st -> EvtPrefix lst0 st.
    intros lst0 lst1 LstPfx. induction LstPfx ; intros st EvtPfx ; [| inversion EvtPfx] ; eauto using EvtPrefix.
  Qed.

  Lemma pfx_of_prod : forall pfx0 pfx1 t, pfx0 <=, pfx1 -> pfx1 <=| t -> pfx0 <=| t.
    intros ? ? ? PfxOfPfx Prod.
    inversion PfxOfPfx ; subst ; inversion Prod ; subst.
    eauto using LeTrace_intro, lst_prefix_stream_prefix.
  Qed.

  Lemma prefix_of_same : forall lst0 st, EvtPrefix lst0 st -> forall lst1, EvtPrefix lst1 st -> (Prefix lst0 lst1 \/ Prefix lst1 lst0).
    intros lst0 st EvtPfx0. induction EvtPfx0 as [| a lst0 st] ; intros lst1 EvtPfx1 ; auto.
    inversion EvtPfx1 as [| ? lst1'] ; subst ; auto.
    assert (Prefix lst0 lst1' \/ Prefix lst1' lst0) as [|] by auto ; auto.
  Qed.

  Lemma prefix_of_prepend : forall lst0 lst1 t, Prefix lst0 lst1 -> EvtPrefix lst0 (prepend lst1 t).
    intros lst0 lst1 t Pfx. induction Pfx ; simpl ; auto using EvtPrefix.
  Qed.

  Lemma prepend_to_prefix : forall lst' lst t, EvtPrefix lst t -> EvtPrefix (lst' ++ lst) (prepend lst' t).
    induction lst' ; simpl ; intros lst t Pfx ; auto using EvtPrefix.
  Qed.

  Lemma delete_from_prefix : forall lst' lst t, EvtPrefix (lst' ++ lst) (prepend lst' t) -> EvtPrefix lst t.
    induction lst' ; simpl ; intros lst t Pfx ; [| inversion Pfx] ; auto.
  Qed.

  Lemma prefix_of_prepend_inv : forall lst1 lst0 t, EvtPrefix lst0 (prepend lst1 t)
      -> Prefix lst0 lst1 \/ exists lst0', lst0 = lst1 ++ lst0' /\ EvtPrefix lst0' t.
    induction lst1 ; intros lst0 t EvtPfx ; inversion EvtPfx ; subst ; simpl in *
    ; try (specialize (IHlst1 lst t H1) as [? | (lst0' & ? & ?)] ; subst) ; eauto using Prefix_some.
  Qed.

  Lemma pfx_from_same_trace_leq_help : forall lst0 lst1 st, EvtPrefix lst0 st
      -> EvtPrefix lst1 st
      -> Prefix lst0 lst1 \/ Prefix lst1 lst0.
    induction lst0 ; induction lst1 ; intros st EvtPfx0 EvtPfx1 ; auto.
    inversion EvtPfx0 ; subst ; inversion EvtPfx1 ; subst.
    assert (Prefix lst0 lst1 \/ Prefix lst1 lst0) as [|] by eauto ; auto.
  Qed.

  Lemma pfx_from_same_trace_leq : forall pfx0 pfx1 t, pfx0 <=| t -> pfx1 <=| t -> (pfx0 <=, pfx1 \/ pfx1 <=, pfx0).
    intros pfx0 pfx1 [s st] Pfx0LeT Pfx1LeT.
    inversion Pfx0LeT as [? lst0 ? EvtPfx0] ; subst.
    inversion Pfx1LeT as [? lst1 ? EvtPfx1] ; subst.
    assert (Prefix lst0 lst1 \/ Prefix lst1 lst0) as [|] by eauto using pfx_from_same_trace_leq_help ; auto using LePfx_intro.
  Qed.

  Lemma deterministic_step : forall cs cs1 a1,
        cs -->[a1] cs1 -> forall cs2 a2, cs -->[a2] cs2 -> cs1 = cs2 /\ a1 = a2.
      intros cs cs1 a1 Step1 ? ? ?.
      pose proof (deterministic cs cs1 cs2 a1 a2).
      apply H0; assumption.
  Qed.

  Ltac subst_eq_steps :=
    repeat lazymatch goal with
      | [H : (_, _) = (_, _) |- _] => injection H ; intros ; subst ; clear H
      | [H0 : ?cs -->[?a0] ?cs0, H1 : ?cs -->[?a1] ?cs1 |- _]
        => assert (cs1 = cs0 /\ a1 = a0) as [? ?] by eauto using deterministic_step ; subst ; clear H1
    end.

  Lemma evt_prefix_prod_both : forall lst st0, EvtPrefix lst st0 -> forall c s st1, Produces c s st0 -> Produces c s st1 -> EvtPrefix lst st1.
    intros lst st0 EvtPfx. induction EvtPfx ; intros c s st1 Prod0 Prod1 ; auto using EvtPrefix_empty.
    inversion Prod0 ; inversion Prod1 ; subst; subst_eq_steps.
    - eauto using EvtPrefix_some.
    - destruct (step_exclusive c s); split; eauto.
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
    - destruct (step_exclusive c s); split; eauto.
  Qed. 

  Lemma prod_prepend_mstep : forall c s c' s' lst, (c, s) ==>*[lst] (c', s')
      -> forall st, Produces c s (prepend lst st) -> Produces c' s' st.
    intros c s c' s' lst MStep. dependent induction MStep ; intros st ProdPrepend ; auto.
    destruct cs1 as [c1 s1].
    simpl in ProdPrepend ; inversion ProdPrepend ; subst ; subst_eq_steps.
    eauto.
  Qed. 

  Lemma prod_prefix_mstep : forall lst c s st, Produces c s st
      -> EvtPrefix lst st
      -> exists cs, (c, s) ==>*[lst] cs.
    induction lst ; intros c s st Prod Pfx ; eauto using MultiStep_refl.
    inversion Pfx ; subst.
    inversion Prod ; subst.
    assert (exists cs, (c', s') ==>*[lst] cs) as [? ?] by eauto.
    eauto using MultiStep.
  Qed.

  Lemma prod_mstep_prefix : forall lst c s st cs, Produces c s st
      -> (c, s) ==>*[lst] cs
      -> EvtPrefix lst st.
    induction lst ; intros c s st cs Prod MStep ; eauto using EvtPrefix_empty.
    inversion MStep ; subst ; inversion Prod ; subst.
    - destruct cs1 as [c1 s1] ; subst_eq_steps.
      eauto using EvtPrefix_some.
    - destruct (step_exclusive c s); split; eauto.
  Qed.

  (* Lemma prod_conv_prefix : forall lst st, EvtPrefix lst st
      -> forall c s s' lst', (c, s) ==>*[lst'] (Stop, s')
      -> Produces c s st
      -> Prefix lst lst'.
    intros lst st EvtPfx. induction EvtPfx ; intros c s s' lst' Conv Prod ; auto.
    inversion Prod ; subst ; inversion Conv ; subst ; [handle_simple_contradict | subst_eq_steps].
    eauto.
  Qed. *)
End TraceTheories.