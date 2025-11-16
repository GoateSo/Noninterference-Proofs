Require Import Basic.
From Coq Require Import Equality Relations RelationClasses List Compare Sets.Ensembles.
Import ListNotations.

Module Type BaseTheories (B : Basic).
  Import B.

  Section SameSet.
    Variable U : Type.
    Lemma Included_refl : forall (A : Ensemble U), 
      Included U A A.
    Proof.
      unfold Included.
      intros.
      assumption.
    Qed.

    Lemma Same_set_refl : forall (A : Ensemble U), 
      Same_set U A A.
    Proof.
      intros.
      split; apply Included_refl.
    Qed.
    
    Lemma Same_set_sym : forall (A B : Ensemble U),
      Same_set U A B -> Same_set U B A.
    Proof.
      intros.
      destruct H.
      split; auto.
    Qed.

    Lemma Included_trans : forall (A B C : Ensemble U),
      Included U A B -> Included U B C -> Included U A C.
    Proof.
      unfold Included.
      auto.
    Qed.

    Lemma Same_set_trans : forall (A B C : Ensemble U),
      Same_set U A B -> Same_set U B C -> Same_set U A C.
    Proof.
      unfold Same_set.
      intros.
      destruct H, H0.
      split; apply Included_trans with B; auto.
    Qed.
  End SameSet.

  Section NatProps.
    Theorem strong_ind : forall P : nat -> Prop,
        (forall m : nat, (forall n : nat, n < m -> P n) -> P m)
        -> forall n : nat, P n.
      intros P IndCase n.
      enough (forall m, m <= n -> P m) by auto.
      induction n ; intros m mLen.
      * inversion mLen. apply IndCase. intros n nLt0. inversion nLt0.
      * apply IndCase. intros m' m'Ltp. apply IHn. unfold lt in m'Ltp.
        assert (S m' <= S n) by (transitivity m ; auto). auto using le_S_n.
    Qed.

    Lemma le_antisym : forall n m, n <= m -> m <= n -> n = m.
      induction n, m ; intros nLem mLen ; [auto | inversion mLen | inversion nLem |].
      apply f_equal. apply le_S_n in nLem, mLen. auto.
    Qed.

    Lemma le_minus : forall n m, n - m <= n.
      induction n, m ; simpl ; auto.
    Qed.

    Lemma le_or_gt : forall n m, {n <= m} + {m < n}.
      intros n m.
      destruct (le_dec n m) as [| LtMN] ; auto.
      destruct (le_decide m n LtMN) ; subst ; auto.
    Qed.

    Lemma lt_minus_lt : forall m0 m1, m0 < m1 -> forall n, m0 < n -> n - m1 < n - m0.
      unfold lt. induction m0, m1 ; intros ltm1 n ltn ; try rewrite -> minus_zero.
      * inversion ltm1.
      * inversion ltn ; subst ; apply le_n_S ; simpl ; auto using le_minus.
      * inversion ltm1.
      * induction n.
        - inversion ltn.
        - apply le_S_n in ltn, ltm1. pose proof (IHm0 m1 ltm1 n ltn).
          simpl. assumption.
    Qed.

    Lemma S_n_le_n_le : forall a b, S a <= b -> a <= b.
      intros.
      destruct b.
      - inversion H.
      - apply le_S.
        apply le_S_n in H.
        assumption.
    Qed.

    Lemma S_le_impl_lt : forall n m, S n <= m -> n < m.
      auto.
    Qed.
  End NatProps.

  Section ListPrefix.
    Context {A : Type}.
    Notation Prefix := (Prefix (A := A)).

    Lemma prop_prefix_exists_next :
      forall (p1 p2 : list A),
        PropPrefix p1 p2 ->
        exists a, Prefix (p1 ++ [a]) p2 /\ List.In a p2.
    Proof.
      intros p1 p2 H_prop.
      unfold PropPrefix in H_prop.
      destruct H_prop as [H_prefix H_neq].
      revert H_neq.
      induction H_prefix.
      - intros H_neq.
        simpl.
        destruct lst as [| y lst'].
        * exfalso. apply H_neq. reflexivity.
        * exists y. constructor; constructor.
          eauto.
          reflexivity.
      - intros H_neq.
        assert (H_neq_lists : lst0 <> lst1).
        {
          intro H_eq_lists. 
          subst lst1. 
          apply H_neq. reflexivity.
        }
        specialize (IHH_prefix H_neq_lists).
        destruct IHH_prefix as [a' H_prefix_a].
        exists a'; destruct H_prefix_a; split.
        + simpl; constructor; assumption.
        + apply in_cons; assumption.
    Qed.

    Lemma app_not_nil : forall (xs : list A) x, [] <> xs ++ [x].
      destruct xs; intros x Hbad; inversion Hbad.
    Qed.

    Lemma app_cons_middle : forall (xs ys : list A) (x : A),
        xs ++ [x] ++ ys = xs ++ (x :: ys).
    Proof.
      intros.
      induction xs; simpl.
      - reflexivity.
      - rewrite <-IHxs.
        reflexivity.
    Qed.

    Lemma app_prefix : forall (p p2 : list A), Prefix p (p ++ p2).
      intros; induction p; [apply Prefix_empty | apply Prefix_some, IHp].
    Qed.

    Lemma prefix_app : forall (ys xs zs: list A), Prefix ys xs -> Prefix ys (xs ++ zs).
      pose proof @prefix_preorder_inst A as [_ Htrans].
      unfold Transitive in Htrans.
      intros.
      specialize (Htrans ys xs (xs ++ zs)).
      apply Htrans.
      - assumption.
      - exact (app_prefix xs zs).
    Qed. 
    
    Lemma list_app_neq_list : forall (xs : list A) x, xs <> xs ++ [x].
      intros.
      induction xs; intro Hbad.
      - inversion Hbad.
      - simpl in Hbad.
        inversion Hbad.
        contradiction.
    Qed.

    Lemma rev_destruct : forall (l : list A), l = [] \/ (exists init a, l = init ++ [a]).
      induction l as [| a l' IH].
      - left; reflexivity.
      - destruct l' as [| b l''].
        + right.
          exists [], a; reflexivity.
        + destruct IH; try discriminate.
          destruct H as [? [? ?]].
          right. 
          exists (a :: x), x0.
          simpl; congruence.
    Qed.  

    Lemma cons_neq : forall (lst : list A) (a : A), lst <> a :: lst.
      induction lst ; intro.
      * apply nil_cons.
      * intro LstEq. inversion LstEq. apply IHlst with a0. assumption.
    Qed.

    Lemma cons_app : forall (lst0 lst1 : list A) (a0 a1 : A), a0 :: lst0 = lst1 ++ [a1]
        -> (a0 = a1 /\ lst0 = [] /\ lst1 = []) \/ (exists lst0' lst1', lst0 = lst0' ++ [a1] /\ lst1 = a0 :: lst1').
      induction lst0, lst1 ; intros a0' a1' LstEq ; simpl in LstEq ; injection LstEq ; intro LstEq' ; intros ; subst ; auto.
      * apply app_cons_not_nil in LstEq' ; inversion LstEq'.
      * right. apply IHlst0 in LstEq'.
        destruct LstEq' as [(? & ? & ?) | (lst0' & lst1' & ? & ?)]
        ; [do 2 exists [] | exists (a :: lst0') ; exists (a :: lst1')]
        ; subst ; simpl in * ; auto.
    Qed.

    Lemma lst_eq_app_impl_nil : forall (lst0 lst1 : list A), lst0 = lst0 ++ lst1 -> lst1 = [].
      induction lst0 ; simpl ; intros lst1 LstEq ; try injection LstEq ; auto.
    Qed.

    Lemma prefix_antisymm : forall (lst0 lst1 : list A), Prefix lst0 lst1 -> Prefix lst1 lst0 -> lst0 = lst1.
      intros lst0 lst1 Pfx01 ; induction Pfx01 ; intro Pfx10 ; dependent induction Pfx10 ; auto using f_equal.
    Qed.

    Proposition prefix_as_append : forall (lst0 lst1 : list A), Prefix lst0 lst1 <-> exists lst0', lst0 ++ lst0' = lst1.
      induction lst0 ; intro lst1 ; split ; intro Pfx ; simpl ; eauto.
      * inversion Pfx as [| ? ? ? Pfx'] ; subst. apply IHlst0 in Pfx'.
        destruct Pfx' as [lst' Pfx']. subst. eauto.
      * destruct Pfx as [lst1' Lst0Val]. simpl in Lst0Val. inversion Lst0Val.
        apply Prefix_some. apply IHlst0. eauto.
    Qed.

    Lemma prefix_length : forall (lst0 lst1 : list A), Prefix lst0 lst1 -> length lst0 <= length lst1.
      intros lst0 lst1 Pfx. induction Pfx ; simpl ; auto using le_0_n, le_n_S.
    Qed.

    Lemma prefix_eq_len : forall (lst0 lst1 : list A), Prefix lst0 lst1 -> length lst0 = length lst1 -> lst0 = lst1.
      intros lst0 lst1 Pfx LenEq. induction Pfx ; simpl in *.
      * symmetry in LenEq. apply length_zero_iff_nil in LenEq. auto.
      * inversion LenEq. apply f_equal. auto.
    Qed.

    Lemma eq_or_prefix : forall lst0 lst1 (a : A), Prefix lst0 (lst1 ++ [a]) -> lst0 = lst1 ++ [a] \/ Prefix lst0 lst1.
      intros lst0 lst1 a Pfx. dependent induction Pfx ; auto.
      pose proof (cons_app lst2 lst1 a0 a x) as [(? & ? & ?) | (lst0' & lst1' & ? & ?)] ; subst ; simpl in *.
      * inversion Pfx ; subst ; simpl ; auto.
      * injection x ; intros.
        assert (lst0 = lst1' ++ [a] \/ Prefix lst0 lst1') as [|] by auto ; subst ; auto using Prefix_some.
    Qed.

    Lemma prefix_of_append : forall (lst0 lst1 lst2 : list A), Prefix lst0 (lst1 ++ lst2)
        -> PropPrefix lst0 lst1 \/ (exists lst', lst0 = lst1 ++ lst' /\ Prefix lst' lst2).
      induction lst0, lst1 ; intros lst2 Pfx ; simpl in * ; unfold PropPrefix ; eauto using nil_cons.
      inversion Pfx as [| ? ? ? Pfx'] ; subst.
      apply IHlst0 in Pfx' ; destruct Pfx' as [[? ?] | (lst' & ? & ?)] ; subst
      ; [left ; split ; [| intro ConsNEq ; injection ConsNEq] | right ; exists lst'] ; auto.
    Qed.

    Lemma prop_prefix_length : forall (lst0 lst1 : list A), PropPrefix lst0 lst1 -> length lst0 < length lst1.
      unfold lt. intros lst0 lst1 [Pfx LstNeq]. induction Pfx ; simpl.
      * destruct lst ; [contradict LstNeq | simpl] ; auto using le_0_n, le_n_S.
      * apply le_n_S. apply IHPfx. intro. subst. contradict LstNeq. reflexivity.
    Qed.

    Lemma prefix_in : forall lst0 (a : A) lst0' lst1, Prefix (lst0 ++ a :: lst0') lst1 -> List.In a lst1.
      induction lst0 as [| a' lst0] ; intros a lst0' lst1 Pfx
      ; simpl in Pfx ; inversion Pfx ; subst ; unfold List.In
      ; [| right ; apply IHlst0 with lst0']
      ; auto.
    Qed.

    Lemma prefix_tail_eq : forall lst0 lst1 (a : A), Prefix (lst0 ++ [a]) (lst1 ++ [a]) -> ~ List.In a lst1 -> lst0 = lst1.
      induction lst0 ; destruct lst1 ; intros a' Pfx NotIn ; simpl in * ; auto
      ; inversion Pfx as [| ? ? ? Pfx'] ; subst.
      * contradict NotIn. auto.
      * inversion Pfx'.
        lazymatch goal with
        | [H : [] = _ ++ [_] |- _] => apply app_cons_not_nil in H ; inversion H
        end.
      * apply f_equal. eauto.
    Qed.

    Lemma prefix_split : forall (p p' : list A), PropPrefix p p' -> exists p'', p' = p ++ p'' /\ [] <> p''.
      intros.
      destruct H.
      induction H.
      - exists lst; split; [ reflexivity | assumption ].
      - destruct IHPrefix.
        + intro Hbad.
          destruct H0.
          congruence.
        + destruct H1. 
          exists x; split; [| assumption].
          simpl; congruence.
    Qed. 

    Lemma pref_le_len: forall (l l' : list A), Prefix l l' -> length l <= length l'.
      intros; induction H; simpl.
      - apply le_0_n.
      - apply le_n_S; assumption.
    Qed.

    Lemma prefix_of_compose : forall (zs xs ys : list A), (xs ++ ys) = zs -> Prefix xs zs.
      induction zs; intros.
      - apply app_eq_nil in H as [H1 H2]; subst.
        apply prefix_preorder_inst.
      - destruct xs.
        + auto.
        + simpl in H.
          inversion H.
          rewrite app_comm_cons.
          apply app_prefix.
    Qed.  

    Lemma prefix_first_eq_last_eq : forall (p : list A) a b, Prefix (p ++ [a]) (p ++ [b]) -> a = b.
      intros; induction p; inversion H; auto.
    Qed.

    Lemma prop_pref_lt_len: forall (l l' : list A), PropPrefix l l' -> length l < length l'.
      intros.
      destruct H; induction H.
      - destruct lst; try contradiction; simpl.
        exact (PeanoNat.Nat.lt_0_succ (length lst)).
      - assert (lst0 <> lst1). {
          intro Hbad; rewrite Hbad in H0.
          auto.
        }
        exact (Arith_base.lt_n_S_stt (length lst0) (length lst1) (IHPrefix H1)).
    Qed.

    Lemma prefix_app_last :
      forall (l1 l2 : list A) (x : A),
        Prefix l1 (l2 ++ [x]) ->
        l1 = (l2 ++ [x]) \/ Prefix l1 l2.
    Proof.
      intros ? ?.
      generalize dependent l1.
      induction l2; intros ? ? Hpref; inversion Hpref; auto.
      - inversion H1; subst. auto.
      - specialize (IHl2 lst0 x H1).
        destruct IHl2; [subst lst0|]; auto.
    Qed.

    Theorem prop_prefix_app_implies_prefix :
      forall (l1 l2 : list A) (x : A),
        PropPrefix l1 (l2 ++ [x]) ->
        Prefix l1 l2.
    Proof.
      intros ? ? ? Hppref.
      unfold PropPrefix in Hppref.
      destruct Hppref as [Hpref Hneq].
      apply prefix_app_last in Hpref.
      destruct Hpref; [contradiction | assumption].
    Qed.
  End ListPrefix.
End BaseTheories.