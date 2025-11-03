Require Import Basic Lang Determinism.
Require Import SecDef SecPol Trace.
Require Import BaseTheory TraceTheories DetTheories.
Require Import SecTheory.

From Coq Require Import Basics Equality List Ensembles Relations RelationClasses Classes.Equivalence.
Import ListNotations.

Module Type PINI (B : Basic) (BT : BaseTheories B) (LD : LangDefs) (TD : TraceDefs B LD) (SP : SecurityPol LD) (Det : DeterminismDef LD) (SD : SecurityDefs B LD TD SP) (ST : SecurityTheory B LD TD SP SD) (TT : TraceTheories B LD TD) (DT : DetTheories B LD TD Det TT).
  Import B BT LD TD Det SP SD ST TT DT.
  Import LangNotations.

  Section Core.
    Context (D : Ensemble Label) `{DecD : DecideIn Label D}.

    Theorem Hpini_impl_KPini : forall c, In Property HPiniD (behavior c) -> In Cmd KPiniD c.
    Admitted.

    Theorem kpini_det_impl_hpini : forall c, In Cmd KPiniD c 
      -> (det_rel steps_to_combined)
      -> In Property HPiniD (behavior c).  
    Admitted.
  End Core.
End PINI.