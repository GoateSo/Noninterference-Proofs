From Stdlib Require Import Equality Relations RelationClasses List.

Import ListNotations.

Module Type Basic.
  Section ListPrefix.
    Context {A : Type}.

    Inductive Prefix : relation (list A) :=
      | Prefix_empty : forall lst, Prefix [] lst
      | Prefix_some : forall a lst0 lst1, Prefix lst0 lst1 -> Prefix (a :: lst0) (a :: lst1).

    #[local] Hint Resolve Prefix_empty : core.
    #[local] Hint Resolve Prefix_some : core.

    #[global] Instance prefix_preorder_inst : PreOrder Prefix.
      split.
      * unfold Reflexive. induction x ; eauto.
      * unfold Transitive.
        induction x ; intros y z Pfxxy Pfxyz
        ; [| inversion Pfxxy ; subst ; inversion Pfxyz ; subst]
        ; constructor ; eauto.
    Defined.

    Definition PropPrefix (lst0 lst1 : list A) : Prop := Prefix lst0 lst1 /\ lst0 <> lst1.

  End ListPrefix.

  #[global] Hint Resolve Prefix_empty : core.
  #[global] Hint Resolve Prefix_some : core.
End Basic.