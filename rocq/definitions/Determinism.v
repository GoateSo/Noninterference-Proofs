Require Import Basic.
Require Import Lang.

From Coq Require Import Basics Equality List Ensembles Relations RelationClasses.
Import ListNotations.

Module Type DeterminismDef (LD : LangDefs).
    Import LD.
    Import LangNotations.
    Section Determinism.
        (* take this one as axiom *)
        Definition one_step_det cs :=
            forall cs1 cs2 a1 a2,
                cs -->[a1] cs1 -> cs -->[a2] cs2 -> (a1 = a2) /\ (cs1 = cs2).
        (* TODO: in addition to one step, prove that 2 finite traces produced from cs must be equal*)
    End Determinism.
End DeterminismDef.