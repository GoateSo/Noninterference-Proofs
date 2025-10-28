From Coq Require Import Basics Equality List.
Import ListNotations.

Class EqDec (A : Type) := {
  eq_dec : forall (a b : A), {a = b} + {a <> b}
}.

(* The typeclass abstracting over a language's small-step semantics. *)
Class LanguageSemantics := {
  Cmd : Type;
  Store : Type;
  Event : Type; 

  (* decideability of command/store/event equality *)
  cmd_eq_dec : EqDec Cmd; 
  mem_eq_dev : EqDec Store;
  evt_eq_dec : EqDec Event;
  
  (* progess : <c,s> --a-> <c', s'> *)
  (* no step (gets stuck or terminates): <c,s> --/-> *)
  steps_to : Cmd -> Store -> Event -> Cmd -> Store -> Prop;
  no_step : Cmd -> Store -> Prop;
  step_exclusive : forall c s, ~((exists c' s' a, steps_to c s a c' s') /\ (no_step c s));
}.

Module Type LangDefs.
  Parameter lang : LanguageSemantics.
  #[global] Instance lang_inst : LanguageSemantics.
    exact lang.
  Defined. 

  (* Production properties *)
  Section Production.
    (* notation for single step progression *)
    Notation "cs1 '-->[' a ']' cs2" := (steps_to (fst cs1) (snd cs1) a (fst cs2) (snd cs2)) (at level 50, no associativity).

    (* relation for multi-step progression w/ notation as well *)
    #[local] Reserved Notation "cs0 '==>*[' lst ']' cs1" (at level 50, no associativity).
    Inductive MultiStep : Cmd * Store -> Cmd * Store -> list Event -> Prop :=
      | MultiStep_refl : forall cs, cs ==>*[[]] cs
      | MultiStep_some : forall cs0 cs1 cs2 a lst,
          cs0 -->[a] cs1 ->
          cs1 ==>*[lst] cs2 -> 
          cs0 ==>*[a :: lst] cs2
      where "cs0 '==>*[' lst ']' cs1" := (MultiStep cs0 cs1 lst) .

    (* note: iterated production *)
    Definition iter_trace_prod cs lst := exists cs', MultiStep cs cs' lst.
    Notation "cs0 '==>*[' lst ']'" := (iter_trace_prod cs0 lst) (at level 50).

    Definition diverge c s : Prop := forall cs1 lst, (c, s) ==>*[lst] cs1 -> exists cs2 a, cs1 -->[a] cs2.
  End Production.

  Module LangNotations.
    Notation "cs1 '-->[' a ']' cs2" := (steps_to (fst cs1) (snd cs1) a (fst cs2) (snd cs2)) (at level 50).
    Notation "cs0 '==>*[' lst ']' cs1" := (MultiStep cs0 cs1 lst) (at level 50, no associativity) .
    Notation "cs0 '==>*[' lst ']'" := (iter_trace_prod cs0 lst) (at level 50, no associativity).
  End LangNotations.
End LangDefs.