Require Import Basic Lang Determinism.
Require Import SecDef SecPol Trace.
Require Import BaseTheory TraceTheories DetTheories.
Require Import SecTheory.

From Coq Require Import Basics Equality List Ensembles Relations RelationClasses Classes.Equivalence.
Import ListNotations.

Module Type LFP (B : Basic) (BT : BaseTheories B) (LD : LangDefs) (TD : TraceDefs B LD) (SP : SecurityPol LD) (Det : DeterminismDef LD) (SD : SecurityDefs B LD TD SP) (ST : SecurityTheory B LD TD SP SD) (TT : TraceTheories B LD TD) (DT : DetTheories B LD TD Det TT).
  Import B BT LD TD Det SP SD ST TT DT.
  Import LangNotations.

  Section Core.
    Context (D : Ensemble Label) `{DecD : DecideIn Label D}.

    Theorem Hplfp_impl_KPlfp : forall c, In Property HLfpD (behavior c) -> In Cmd KLfpD c.
    Admitted.

    Theorem klfp_det_impl_hlfp : forall c, In Cmd KLfpD c 
      -> (det_rel steps_to_combined)
      -> In Property HLfpD (behavior c).  
    Admitted.
  End Core.
End LFP.