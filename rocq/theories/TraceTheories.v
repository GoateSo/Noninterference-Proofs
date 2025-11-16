Require Import Basic Lang Trace.
From Coq Require Import Equality Relations RelationClasses List Compare Sets.Ensembles Lists.Streams.
Import ListNotations.

Module Type TraceTheories (B : Basic) (LD : LangDefs) (TD : TraceDefs B LD).
  Import B LD TD.
  Import LangNotations.

  Lemma trace_dec_thm : forall t, t = t_dcom t.
    intros; case t; simpl; auto.
  Qed.

  Lemma get_trace_prod : forall c m, Produces c m (getTrace c m).
    cofix CH.
    intros.
    rewrite (trace_dec_thm (getTrace c m)); simpl.
    destruct (can_step_dec c m) as [p_dec | p_no] eqn:Heq.
    - destruct p_dec as [[[e c'] s'] Hstep].
      simpl in *.
      apply (Produces_step c m e c' s'); [assumption | ].
      apply CH.
    - apply No_production.
      assumption. 
  Qed.

  (* all configurations produce a trace *)
  Theorem univ_production : forall c m, exists st, c ~~> (m, st).
    intros.
    exists (getTrace c m).
    unfold "~~>", behavior; simpl.
    apply get_trace_prod.
  Qed.

  Lemma produce_impl_canstep : forall c s e c' s', (c, s) -->[e] (c', s') -> can_step c s.
    intros.
    unfold has_step.
    apply exists_to_inhabited_sig.
    exists (e, c', s'); simpl.
    assumption.
  Qed.

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

  (* any finite trace prefix can be expanded to an infinite trace *)
  Theorem trace_max : forall c m p, (c, m)==>*[p] -> exists (t : EvtStream), (m, p) <=| (m, t) /\ c ~~>(m, t).
    intros.
    destruct H as [[c' s'] Hprod].
    pose proof (get_trace_prod c' s').
    exists (prepend p (getTrace c' s')).
    split.
    - constructor.
      apply prefix_of_prepend.
      apply prefix_preorder_inst.
    - generalize dependent m.
      revert c.
      unfold "~~>", behavior; simpl.
      induction p; intros.
      + inversion Hprod; subst.
        assumption.
      + inversion Hprod; destruct cs1; subst.
        apply (Produces_step _ _ _ c0 s); try assumption.
        apply IHp in H5.
        assumption.
  Qed.

  Lemma prefix_prod_mstep : forall lst c s st, Produces c s st
        -> EvtPrefix lst st
        -> (c, s) ==>*[lst].
    induction lst ; intros c s st cs Prod ; eauto using EvtPrefix_empty.
    - exists (c,s). auto.
    - inversion Prod; subst. inversion cs; subst.
      apply IHlst in H5 as [cs2 Hprod]; try assumption.
      exists cs2.
      apply (MultiStep_some (c, s) (c', s') cs2); assumption.
  Qed.

  Lemma prefix_prefix_prod : forall p' p, Prefix p' p -> forall c m,  (c, m) ==>*[p] -> (c, m) ==>*[p'].
      unfold iter_trace_prod.
      intros ? ? HPref.
      dependent induction HPref; intros.
      - eauto.
      - destruct H.
        inversion H; subst.
        destruct cs1 as [c' m'].
        pose proof IHHPref c' m'.
        destruct H0.
        + exists x; apply H5.
        + exists x0.
          apply (MultiStep_some (c, m) (c', m') x0); assumption. 
  Qed.

  Lemma PropPrefix_production : forall p' p, PropPrefix p' p -> forall c m, (c,m)==>*[p] -> exists e, Prefix (p' ++ [e]) p /\ (c,m)==>*[p' ++ [e]].
      unfold iter_trace_prod.
      intros ? ? [HPref Hneq].
      dependent induction HPref; intros.
      - destruct lst.
        + exfalso; apply Hneq; reflexivity.
        + destruct H. inversion H; subst.
          exists e.
          split; simpl; auto.
          exists cs1.
          exact (MultiStep_some (c, m) cs1 cs1 e [] H4 (MultiStep_refl cs1)).
      - destruct H.
        inversion H; subst.
        destruct cs1 as (c', m').
        assert (lst0 <> lst1). {
          intro Hbad.
          destruct Hneq.
          rewrite Hbad.
          reflexivity.
        }
        specialize (IHHPref H0 c' m').
        destruct IHHPref. { exists x; assumption. }
        destruct H1 as [Hpref [(c'', m'') Hcompose]].
        exists x0.
        split.
        + rewrite <-app_comm_cons.
          constructor.
          assumption.
        + exists (c'', m''); simpl.
          apply MultiStep_some with (cs1:=(c',m')); assumption.
  Qed.  
         
  Theorem trace_pfx_production_fwd : forall c m st, c ~~> (m, st) -> (forall p, (m, p) <=| (m, st) -> (c, m) ==>*[p]).
    intros.
    unfold "~~>", behavior in H; simpl in H.
    inversion H0; subst.
    apply prefix_prod_mstep with st; assumption.
  Qed.

  Ltac handle_prog_contradict :=
    lazymatch goal with
      | [H : (no_step ?c ?s), H1 : (steps_to ?c ?s ?e ?c' ?s') |- _] => apply produce_impl_canstep in H1; contradiction
      | [H : steps_to_combined _ _ _ |- _] => unfold steps_to_combined in H; handle_prog_contradict
    end.
End TraceTheories.