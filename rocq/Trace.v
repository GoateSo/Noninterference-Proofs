Require Import Basic.
Require Import Lang.

From Coq Require Import RelationClasses List Basics Equality Relations Ensembles.

Import ListNotations.

(* TODO: maybe clean up how traces group up stores and event lists/streams *)
Module Type TraceDefs (B : Basic) (LD : LangDefs).
  Import B LD.
  Import LangNotations.

  Section Definitions.
    CoInductive EvtStream :=
      | ConsEvt (a : Event) (st : EvtStream) : EvtStream
      | NoProgress : EvtStream. (* termination or stuck *)

    Inductive EvtPrefix : list Event -> EvtStream -> Prop :=
      | EvtPrefix_empty : forall st, EvtPrefix [] st
      | EvtPrefix_some : forall a lst st, EvtPrefix lst st -> EvtPrefix (a :: lst) (ConsEvt a st).

    Fixpoint prepend (lst : list Event) (st : EvtStream) : EvtStream :=
      match lst with
        | [] => st
        | a :: rst => ConsEvt a (prepend rst st)
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
      | Produces_step : forall c s a c' s' st, (c, s) -->[a] (c', s')
        -> Produces c' s' st -> Produces c s (ConsEvt a st)
        (* NOTE: this is quite different from the existing definition that has 'Stop' specifically instead of a forall c. This new definition is made to include all cases where a program gets stuck as well *)
      | No_production : forall c s, no_step c s -> Produces c s NoProgress.

    Definition behavior (c : Cmd) : Property :=
      (fun t => Produces c (fst t) (snd t)).

    (* TODO: note if possible use a more limited version of this. Current definition bakes in determinism *)
    Definition trace_pfx_prod (c : Cmd) (cs : Trace) :=
      forall p, In Trace (behavior c) cs <-> ((le_trace p cs) <-> (iter_trace_prod (c, (t_input cs)) (p_events p))).

    (* TODO: note these might belong in theories instead of definitions *)
    Definition maximalization (p : TracePfx) :=
      exists (t : EvtStream), le_trace (p) (fst p, t).
  End Definitions.

  #[global] Notation "pfx '<=|' t" := (le_trace pfx t) (at level 80).
  #[global] Notation "pfx0 '<=,' pfx1" := (le_pfx pfx0 pfx1) (at level 80).

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