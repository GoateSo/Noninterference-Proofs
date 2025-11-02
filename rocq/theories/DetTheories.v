Require Import Basic Lang Determinism Trace.
Require Import BaseTheory.
Require Import TraceTheories.
From Coq Require Import Equality Relations RelationClasses List Compare Sets.Ensembles Streams Setoid Classes.Morphisms.
Import ListNotations.

Module Type DetTheories (B : Basic) (LD : LangDefs) (TD : TraceDefs B LD) (DD : DeterminismDef LD) (TT : TraceTheories B LD TD).
  Import B LD TD DD TT.
  Import LangNotations.

  Theorem Eq_EvtSt_refl : forall s: EvtStream, Eq_EvtSt s s.
    cofix CH.
    intros.
    destruct s; constructor; try reflexivity.
    apply CH.
  Qed.

  Theorem Eq_EvtSt_sym : forall s1 s2: EvtStream, Eq_EvtSt s1 s2 -> Eq_EvtSt s2 s1.
    cofix CH.
    intros.
    destruct H; [apply Eq_EvtSt_refl | constructor].
    - rewrite H; reflexivity.
    - apply CH.
      assumption.
  Qed.

  Theorem Eq_EvtSt_trans : forall s1 s2 s3 : EvtStream, Eq_EvtSt s1 s2 -> Eq_EvtSt s2 s3 -> Eq_EvtSt s1 s3.
    cofix CH.
    intros ? ? ? H12 H23.
    destruct H12 eqn:Heqn.
    - destruct s3.
      + inversion H23.
      + apply Eq_EvtSt_refl.
    - destruct s3; inversion H23.
      + subst; constructor; [reflexivity | ].
        apply (CH t1 t2 s3); assumption.
  Qed.  

  Instance Eq_EvtSt_equiv: Equivalence (Eq_EvtSt).
    Proof.
      constructor.
      - exact Eq_EvtSt_refl.
      - exact Eq_EvtSt_sym.
      - exact Eq_EvtSt_trans.
    Qed.

    Global Instance EvtCons_proper :
      Proper (eq ==> Eq_EvtSt ==> Eq_EvtSt ) ConsEvt.
    Proof.
      intros h1 h2 H_head t1 t2 H_tail.
      subst; constructor; [reflexivity | assumption].
    Qed.

    Global Add Setoid EvtStream Eq_EvtSt Eq_EvtSt_equiv as EvtStreamSetoid.

  Section DetTraces.
    Parameter Det : det_rel steps_to_combined.
    Lemma det_trace_prod : forall c m t1 t2, c ~~> (m, t1) -> c ~~> (m, t2) -> Eq_EvtSt t1 t2.
      unfold "~~>", behavior; simpl.
      cofix CH. 
      intros.
      pose proof Det (c, m) as Hdet.
      unfold det_rel, steps_to_combined in Hdet.
      inversion H; inversion H0; subst.
      - destruct (Hdet (c', s') (c'0, s'0) a a0); try assumption.
        + constructor.
          * assumption.
          * rewrite pair_equal_spec in H3; destruct H3; subst;
            apply (CH c'0 s'0 st st0); assumption.
      - apply produce_impl_canstep in H1.
        contradiction.
      - apply produce_impl_canstep in H5.
        contradiction.
      - apply Eq_EvtSt_refl.
    Qed.
  End DetTraces.
End DetTheories.