Require Import Basic.
Require Import Lang.

From Coq Require Import Basics Equality List Ensembles Relations RelationClasses.
Import ListNotations.

Module Type DeterminismDef (LD : LangDefs).
    Import LD.
    Import LangNotations.
    Section Determinism.
        Definition one_step_det cs :=
            forall cs1 cs2 a1 a2,
                cs -->[a1] cs1 -> cs -->[a2] cs2 -> (a1 = a2) /\ (cs1 = cs2).
    End Determinism.
End DeterminismDef.