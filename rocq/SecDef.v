Require Import Basic.
Require Import Lang.
Require Import Trace.
Require Import SecPol.

From Coq Require Import Basics Equality List Ensembles Relations RelationClasses.
Import ListNotations.

Class DecideIn {A : Type} (S : Ensemble A) := {
  dec_in : forall a, {In A S a} + {~ In A S a}
}.   

Module Type SecurityDefs (B : Basic) (LD : LangDefs) (TD : TraceDefs B LD) (SP : SecurityPol LD).
  Import B LD TD SP.
  Import LangNotations.
  Parameter Label : Set.
  Parameter label_order : LabelOrder Label.
  #[global] Instance label_order_inst : LabelOrder Label.
    exact label_order.
  Defined.

  (* indistinguishability equivalence and inequality relations *)
  (* TODO: add D as the paramater of deq and dle relations? *)
  Class DEquivalence := {
    D : Ensemble Label;
    deq_evt : relation Event;
    deq_evt_equiv : Equivalence deq_evt;
    
    deq_store : relation Store;
    deq_store_equiv : Equivalence deq_store;

    deq_evt_lst : relation (list Event);
    deq_evt_lst_equiv : Equivalence deq_evt_lst;

    dle_evt_lst : relation (list Event);
    dle_evt_lst_preorder : PreOrder dle_evt_lst; (* if a =[D] b,  [a] <=[D] [b] and [b] <=[D] [a] *)
  }.

  Parameter DE : DEquivalence.
  Instance deq : DEquivalence.
    exact DE.
  Defined.

  Section MoreDEquivalence.
    (* properties of prefixes (combining event list and store properties) *)
    Definition deq_pfx : relation TracePfx := 
      fun cs1 cs2 => deq_evt_lst (snd cs1) (snd cs2)  /\ deq_store (fst cs1) (fst cs2).

    Definition deq_pfx_equiv : Equivalence deq_pfx.
      destruct deq_evt_lst_equiv.
      destruct deq_evt_lst_equiv as [RL SL TL].
      destruct deq_store_equiv as [RS SS TS].
      split; unfold deq_pfx.
      - auto.
      - intros [s1 l1] [s2 l2] [H1 H2].
        auto.
      - intros [s1 l1] [s2 l2] [s3 l3] [H1 H2] [H3 H4].
        split.
        + apply (TL l1 l2 l3); auto.
        + apply (TS s1 s2 s3); auto.
    Defined.
    
    Definition dle_pfx : relation TracePfx :=
      fun cs1 cs2 => dle_evt_lst (snd cs1) (snd cs2) /\ deq_store (fst cs1) (fst cs2).
    
    Definition dle_pfx_preorder : PreOrder dle_pfx.
      destruct dle_evt_lst_preorder as [RL TL].
      destruct deq_store_equiv as [RS SS TS].
      split; unfold dle_pfx.
      - auto.
      - unfold Transitive.
        intros [s1 l1] [s2 l2] [s3 l3].
        simpl.
        intros [H1 H2] [H3 H4].
        split.
        + apply (TL l1 l2 l3); auto.
        + apply (TS s1 s2 s3); auto.
    Defined.

    Definition dlt_pfx : relation TracePfx :=
      fun cs1 cs2 => dle_pfx cs1 cs2 /\ ~(deq_pfx cs1 cs2).
    (* TODO: define with partial order? *)

    Definition silent c s :=
      forall cs' lst, (c, s) ==>*[lst] cs' -> deq_evt_lst lst [].
    
    (* Note: since specific events (like NoEvt) aren't specified, this is defined in terms of list silence, instead of being the other way around *)
    Definition sil a := deq_evt_lst [a] [].

    (* TODO: possible defn/thrm that: forall a, ~(sil a) -> deq_evt_lst [a] [a]*)
  End MoreDEquivalence.
  
  Section Knowledge.
    (* note: attacker knowledge *)
    (* note2: defined currently using Props and <-> instead of sets and = *)
    Definition atk_knowledge (c : Cmd) (m : Store) (p : list Event) : Ensemble Store :=
      fun m' => deq_store m m' 
        /\ exists st', In Trace (behavior c) (m', st')
        /\ exists p', (iter_trace_prod (c, m') p' /\ deq_evt_lst  p p' ).
    (* note: progress knowledge *)
    Definition prog_knowledge (c : Cmd) (m : Store) (p : list Event) : Ensemble Store := 
      fun m' => deq_store m m' 
        /\ exists st', In Trace (behavior c) (m', st')
        /\ exists p' a, (iter_trace_prod (c, m') p /\ deq_evt_lst p' (cons a p)) /\ ~ sil a.
  End Knowledge.

  Section Progress.
    Definition progressD pfx t := exists pfx', pfx' <=| t /\ dlt_pfx pfx pfx'.
  End Progress.

  Section NonInterference.
    Definition KPsniD : Ensemble Cmd :=
      fun c => forall p m a, iter_trace_prod (c, m) (cons a p) 
        -> ~ sil a
        -> Same_set Store (atk_knowledge c m p) (atk_knowledge c m (cons a p)).

    Definition KPiniD : Ensemble Cmd :=
      fun c => forall p m a, iter_trace_prod (c, m) (cons a p) 
        -> ~ sil a
        -> Same_set Store (prog_knowledge c m p) (atk_knowledge c m (cons a p)).

    Definition KLfpD : Ensemble Cmd :=
      fun c => forall p m a, iter_trace_prod (c, m) (cons a p) 
        -> ~ sil a
        -> Same_set Store (atk_knowledge c m p) (prog_knowledge c m p).
    
    Definition HPsniD : Hyperproperty :=
      fun t_set => forall t0 t1, (In Trace t_set t0) -> (In Trace t_set t1)
        -> deq_store (t_input t0) (t_input t1) ->
        forall pfx0, pfx0 <=| t0 -> exists pfx1, pfx1 <=| t1 /\ deq_pfx pfx0 pfx1.
    
    Definition HPiniD : Hyperproperty :=
      fun t_set => forall t0 t1, (In Trace t_set t0) -> (In Trace t_set t1)
        -> deq_store (t_input t0) (t_input t1) ->
        forall pfx0 pfx1, pfx0 <=| t0 -> pfx1 <=| t1 -> (dle_pfx pfx0 pfx1 \/ dle_pfx pfx1 pfx0).

    Definition HLfpD : Hyperproperty :=
      fun t_set => forall t0 t1, (In Trace t_set t0) -> (In Trace t_set t1)
        -> forall pfx0 pfx1, pfx0 <=| t0 -> pfx1 <=| t1 -> dlt_pfx pfx0 pfx1 -> progressD pfx0 t0.
  End NonInterference.
End SecurityDefs.