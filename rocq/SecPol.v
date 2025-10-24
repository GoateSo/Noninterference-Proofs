Require Import Lang.
Require Import Trace.

From Coq Require Import Basics Equality List Ensembles Relations RelationClasses.
Import ListNotations.

Class DecideIn {A : Type} (S : Ensemble A) := {
  dec_in : forall a, {In A S a} + {~ In A S a}
}.


(* Security policy class (labels)*)
Class LabelOrder (Label : Set) := {
  flows_to : Label -> Label -> Prop;
  flows_to_preorder :  PreOrder flows_to;

  e_lower_bound : forall l1 l2, exists l0, flows_to l0 l1 /\ flows_to l0 l2 ;

  reflect : Label -> Label ;
  reflect_homomorphism: forall l1 l2, (flows_to l1 l2) -> (flows_to (reflect l2) (reflect l1)) ;
}.

Module Type SecurityPol (LD : LangDefs).
  Parameter Label : Set.
  Parameter label_order : LabelOrder Label.
  #[global] Instance label_order_inst : LabelOrder Label.
    exact label_order.
  Defined.

  (* downward closed set property *)
  Class LowSet (D : Ensemble Label) `{DecideIn Label D} := {
    down_closed : forall l1 l2, In Label D l1 -> flows_to l2 l1 -> In Label D l2
  }.
End SecurityPol.