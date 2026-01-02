Require Import Basic Lang.

From Coq Require Import List Basics Equality Relations Ensembles Arith.PeanoNat.

Import ListNotations.

Module Type TraceDefs (B : Basic) (LD : LangDefs).
  Import B LD.
  Import LangNotations.

  Section Definitions.
    CoInductive EvtStream :=
      | ConsEvt (e : Event) (st : EvtStream) : EvtStream
      | NoProgress : EvtStream. (* termination or stuck *)

    (* decomposer for evt streams *)
    Definition t_dcom t := match t with 
    | ConsEvt e st => ConsEvt e st
    | NoProgress => NoProgress
    end.

    CoInductive Eq_EvtSt : EvtStream -> EvtStream -> Prop := 
      | evts_eq_nil : Eq_EvtSt NoProgress NoProgress
      | evts_eq_cons : forall (h1 h2 : Event) (t1 t2 : EvtStream),
        h1 = h2 ->
        Eq_EvtSt t1 t2 ->
        Eq_EvtSt (ConsEvt h1 t1) (ConsEvt h2 t2).
    
    CoFixpoint getTrace c s: EvtStream := match (can_step_dec c s) with
      | inl (exist _ (e,c',s') _) => ConsEvt e (getTrace c' s')
      | inr _ => NoProgress
    end.

    Inductive EvtPrefix : list Event -> EvtStream -> Prop :=
      | EvtPrefix_empty : forall st, EvtPrefix [] st
      | EvtPrefix_some : forall e lst st, EvtPrefix lst st -> EvtPrefix (e :: lst) (ConsEvt e st).

    Fixpoint prepend (lst : list Event) (st : EvtStream) : EvtStream :=
      match lst with
        | [] => st
        | e :: rst => ConsEvt e (prepend rst st)
      end.

    Definition Trace : Type := Store * EvtStream.

    Definition t_input : Trace -> Store := fst.

    Definition TracePfx : Type := Store * list Event.

    Definition p_events : TracePfx -> list Event := snd.

    Inductive le_trace : TracePfx -> Trace -> Prop :=
      | LeTrace_intro : forall s lst st, EvtPrefix lst st -> le_trace (s, lst) (s, st).

    Inductive le_pfx : relation TracePfx :=
      | LePfx_intro : forall lst0 lst1, Prefix lst0 lst1 -> forall s, le_pfx (s, lst0) (s, lst1).

    Definition Property : Type := Ensemble Trace.
    Definition Hyperproperty : Type := Ensemble Property.

    CoInductive Produces : Cmd -> Store -> EvtStream -> Prop :=
      | Produces_step : forall c s e c' s' st, (c, s) -->[e] (c', s')
        -> Produces c' s' st -> Produces c s (ConsEvt e st)
      | No_production : forall c s, no_step c s -> Produces c s NoProgress.

    Definition behavior (c : Cmd) : Property :=
      (fun t => Produces c (fst t) (snd t)).
  End Definitions.

  #[global] Notation "pfx '<=|' t" := (le_trace pfx t) (at level 80).
  #[global] Notation "pfx0 '<=,' pfx1" := (le_pfx pfx0 pfx1) (at level 80).
  #[global] Notation "c '~~>' t" := (In Trace (behavior c) t) (at level 80).

  Section BasicProperties.
    Lemma le_pfx_refl : forall pfx : TracePfx, pfx <=, pfx.
      induction pfx. apply LePfx_intro ; reflexivity.
    Qed.

    Lemma le_pfx_trans : forall pfx0 pfx1 pfx2, pfx0 <=, pfx1 -> pfx1 <=, pfx2 -> pfx0 <=, pfx2.
      intros pfx0 pfx1 pfx2 Le01 Le12. dependent induction Le01. dependent induction Le12.
      apply LePfx_intro ; transitivity lst1 ; assumption.
    Qed.
  End BasicProperties.
  #[global] Hint Resolve le_pfx_refl : core.
End TraceDefs.