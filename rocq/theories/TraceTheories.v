Require Import Basic Lang Trace.
From Coq Require Import Equality Relations RelationClasses List Compare Sets.Ensembles.
Import ListNotations.

Module Type TraceTheories (B : Basic) (LD : LangDefs) (TD : TraceDefs B LD).
  Import B LD TD.
  Import LangNotations.

  (* defn: to produce a trace means producing all finite prefixes of it *)
  Axiom trace_pfx_production : forall c m st, c ~~> (m, st) <-> (forall p, (m, p) <=| (m, st) -> (c, m) ==>*[p]).
  (* any finite trace prefix can be expanded to an infinite trace *)
  Axiom trace_max : forall c m p, (c, m)==>*[p] -> exists (t : EvtStream), (m, p) <=| (m, t) /\ c ~~>(m, t).
  (* all configurations produce a trace *)
  Axiom univ_production : forall c m, exists st, c ~~> (m, st).

  Theorem produce_impl_canstep : forall c s e c' s', (c, s) -->[e] (c', s') -> can_step c s.
    intros.
    unfold can_step.
    eauto.
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

  Ltac handle_prog_contradict :=
    lazymatch goal with
      | [H : (~ (can_step ?c ?s)), H1 : (steps_to ?c ?s ?e ?c' ?s') |- _] => apply produce_impl_canstep in H1; contradiction
      | [H : steps_to_combined _ _ _ |- _] => unfold steps_to_combined in H; handle_prog_contradict
    end.
End TraceTheories.