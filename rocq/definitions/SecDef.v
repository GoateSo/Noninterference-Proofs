Require Import Basic Lang Trace.
Require Import SecPol.

From Coq Require Import Basics Equality List Ensembles Relations RelationClasses.
Import ListNotations.

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
    sil : Event -> Prop;
    sil_dec : forall a, {sil a} + {~ sil a};
    
    deq_store : relation Store;
    deq_store_equiv : Equivalence deq_store;
  }.

  Parameter DE : DEquivalence.
  Instance deq : DEquivalence.
    exact DE.
  Defined.

  Section MoreDEquivalence.
    Definition indistincts (c : Cmd) (s : Store) : Ensemble Store :=
      fun s' => deq_store s s'.

    Fixpoint erase (lst : list Event): list Event :=
      match lst with
        | [] => []
        | a :: rest => if sil_dec a 
          then erase rest
          else a :: (erase rest)
      end.

    Definition deq_evt_lst : relation (list Event) :=
      fun l1 l2 => erase l1 = erase l2.

    Definition dle_evt_lst : relation (list Event) :=
      fun l1 l2 => Prefix (erase l1) (erase l2).
    (* properties of prefixes (combining event list and store properties) *)
    Definition deq_pfx : relation TracePfx := 
      fun cs1 cs2 => deq_evt_lst (snd cs1) (snd cs2) /\ deq_store (fst cs1) (fst cs2).

    Definition dle_pfx : relation TracePfx :=
      fun cs1 cs2 => dle_evt_lst (snd cs1) (snd cs2) /\ deq_store (fst cs1) (fst cs2).

    Definition dlt_pfx : relation TracePfx :=
      fun cs1 cs2 => dle_pfx cs1 cs2 /\ ~(deq_pfx cs1 cs2).
  End MoreDEquivalence.

  #[global] Hint Unfold deq_evt_lst : core.
  #[global] Hint Unfold dle_evt_lst : core.
  #[global] Hint Unfold deq_pfx : core.
  #[global] Hint Unfold dlt_pfx : core.
  #[global] Hint Unfold dle_pfx : core.
 
  Section Knowledge.
    (* note: attacker knowledge *)
    (* note2: defined currently using Props and <-> instead of sets and = *)
    Definition atk_knowledge (c : Cmd) (m : Store) (p : list Event) : Ensemble Store :=
      fun m' => deq_store m m'
        /\ exists p', ((c, m')==>*[p'] /\ deq_evt_lst  p p').
    (* note: progress knowledge *)
    Definition prog_knowledge (c : Cmd) (m : Store) (p : list Event) : Ensemble Store := 
      fun m' => deq_store m m' 
        /\ exists p' a, ((c, m')==>*[p'] /\ deq_evt_lst p' (p ++ [a])) /\ ~ sil a.
  End Knowledge.

  Section Progress.
    Definition progressD pfx t := exists pfx', pfx' <=| t /\ dlt_pfx pfx pfx'.
  End Progress.

  Section NonInterference.
    Definition KPsniD : Ensemble Cmd :=
      fun c => forall p m a,  (c, m)==>*[p ++ [a]] 
        -> ~ sil a
        -> Same_set Store (atk_knowledge c m p) (atk_knowledge c m (p ++ [a])).

    Definition KPiniD : Ensemble Cmd :=
      fun c => forall p m a, (c, m)==>*[p ++ [a]] 
        -> ~ sil a
        -> Same_set Store (prog_knowledge c m p) (atk_knowledge c m (p ++ [a])).

    Definition KLfpD : Ensemble Cmd :=
      fun c => forall p m a, (c, m)==>*[p ++ [a]] 
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