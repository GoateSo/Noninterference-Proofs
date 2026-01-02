Require Import Lang.

Module Type DeterminismDef (LD : LangDefs).
    Import LD LangNotations.
    Section Determinism.
        Definition det_rel {A B C: Type} (step_rel: A -> B -> C -> Prop) :=
            forall cs cs1 cs2 a1 a2,
                step_rel cs a1 cs1 -> step_rel cs a2 cs2 -> (cs1 = cs2) /\ (a1 = a2).
    End Determinism.
End DeterminismDef.