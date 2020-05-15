Require Export Dirac.
Require Import Morphisms.

Definition Operator n := Matrix (Nat.pow 2 n) (Nat.pow 2 n).
Definition State n := Matrix (Nat.pow 2 n) 1.

Definition Apply {n} (o: Operator n) (s: State n): State n :=
  @Mmult (Nat.pow 2 n) (Nat.pow 2 n) 1 o s.

Definition Compose {n} (o1 o2: Operator n): Operator n :=
  @Mmult _ (Nat.pow 2 n) _ o1 o2.

Definition OperatorEquiv {n} (o1 o2: Operator n): Prop :=
  @sta_equiv (Nat.pow 2 n) (Nat.pow 2 n) o1 o2.

Definition StateEquiv {n} (s1 s2: State n): Prop :=
  @sta_equiv (Nat.pow 2 n) 1 s1 s2.

Instance ProperApply n:
  Proper (OperatorEquiv ==> StateEquiv ==> StateEquiv) (@Apply n).
Proof.
  intros.
  apply (Mmult_sta_proper (Nat.pow 2 n) (Nat.pow 2 n) 1).
Qed.

Instance ProperCompose n:
  Proper (OperatorEquiv ==> OperatorEquiv ==> OperatorEquiv) (@Compose n).
Proof.
  intros.
  apply (Mmult_sta_proper (Nat.pow 2 n) (Nat.pow 2 n) (Nat.pow 2 n)).
Qed.

Instance OperatorEquiv_equiv n: Equivalence (@OperatorEquiv n).
Proof.
  apply (sta_equiv_equiv (Nat.pow 2 n) (Nat.pow 2 n)).
Qed.

Instance StateEquiv_equiv n: Equivalence (@StateEquiv n).
Proof.
  apply (sta_equiv_equiv (Nat.pow 2 n) 1).
Qed.

Lemma OperatorEquiv_spec: forall {n} (o1 o2: Operator n),
  OperatorEquiv o1 o2 <->
  (forall s: State n, StateEquiv (Apply o1 s) (Apply o2 s)).
Proof.
  intros.
  unfold StateEquiv, OperatorEquiv.
  split; intros.
  + rewrite H.
    reflexivity.
  + apply sta_equiv_by_Mmult.
    auto.
Qed.

Lemma Cmod_Cconj: forall c, RtoC((Cmod c)^2)%R = c^* * c.
Proof.
  intros.
  unfold RtoC.
  simpl.
  rewrite Rmult_1_r.
  destruct c; unfold Cconj, Cmult, Cmod, RtoC.
  simpl fst; simpl snd.
  f_equal; [| ring].
  rewrite sqrt_def by nra.
  ring.
Qed.

Lemma mod1_Cconj: forall c, (Cmod c = 1)%R -> c^* * c = 1.
Proof.
  intros.
  rewrite <- Cmod_Cconj.
  rewrite H.
  simpl.
  unfold RtoC.
  f_equal.
  ring.
Qed.

Lemma Cconj_eq_0: forall c, Cconj c = 0 -> c = 0.
Proof.
  intros.
  destruct c; simpl in H.
  inversion H.
  unfold RtoC.
  f_equal.
  lra.
Qed.

Lemma StateEquiv_spec: forall {n} (s1 s2: State n),
  StateEquiv s1 s2 <->
  @Mmult (Nat.pow 2 n) 1 (Nat.pow 2 n) s1 (s1 †) ≡
  @Mmult (Nat.pow 2 n) 1 (Nat.pow 2 n) s2 (s2 †) .
Proof.
  intros; split; intros.
  + unfold StateEquiv in H.
    destruct H as [c [Hc HH]].
    rewrite <- HH.
    rewrite Mscale_adj.
    rewrite Mscale_mult_dist_r.
    rewrite Mscale_mult_dist_l.
    rewrite Mscale_assoc.
    rewrite mod1_Cconj by auto.
    rewrite Mscale_1_l.
    reflexivity.
  + unfold State in s1, s2.
    unfold StateEquiv.
    revert s1 s2 H.
    set (m := (Nat.pow (S (S O)) n)).
    clearbody m; clear n.
    intros.
    unfold sta_equiv.
    assert (forall i, (i < m)%nat -> exists c, Cmod c = R1 /\ c * (s1 i O) = s2 i O).
    {
      intros i Hi.
      specialize (H ltac:(exists i; auto) ltac:(exists i; auto)).
      unfold get in H.
      simpl in H.
      unfold adjoint, Mmult in H; simpl in H.
      ring_simplify in H.
      rewrite Cmult_comm, <- Cmod_Cconj in H.
      rewrite Cmult_comm, <- Cmod_Cconj in H.
      assert (Cmod (s1 i 0%nat) = Cmod (s2 i 0%nat)).
      {
        inversion H.
        ring_simplify in H1.
        pose proof Cmod_ge_0 (s1 i O).
        pose proof Cmod_ge_0 (s2 i O).
        nra.
      }
      clear H.
      destruct (Classical_Prop.classic (s1 i O = 0)).
      {
        exists 1.
        split; [autorewrite with C_db;auto | ].
        rewrite H in H0.
        rewrite Cmod_0 in H0.
        symmetry in H0.
        apply Cmod_eq_0 in H0.
        rewrite H0, H.
        ring.
      }
      exists ((s2 i O)/(s1 i O)).
      split.
      + rewrite Cmod_div by auto.
        rewrite <- H0.
        field.
        intro.
        apply Cmod_eq_0 in H1; tauto.
      + field.
        auto.
    }
    destruct (Classical_Prop.classic (exists i, (i < m)%nat /\ s1 i O <> 0)).
    2: {
      exists 1.
      split; [autorewrite with C_db;auto | ].
      intros [i Hi] [j Hj]; unfold get; simpl.
      destruct j; [clear Hj | lia].
      unfold scale.
      assert (s1 i O = 0).
      { apply Classical_Prop.NNPP; intro; apply H1; exists i; auto. }
      specialize (H0 i Hi).
      destruct H0 as [c [_ ?]].
      rewrite <- H0, H2.
      ring.
    }
    destruct H1 as [i [Hi Hs1i]].
    pose proof H0 i Hi as [c [Hc ?]].
    exists c; split; auto.
    intros [i' Hi'] [j Hj]; unfold get; simpl.
    destruct j; [clear Hj | lia].
    unfold scale.
    pose proof H0 i' Hi' as [c' [Hc' ?]].
    specialize (H ltac:(exists i; auto) ltac:(exists i'; auto)).
    unfold get in H; simpl in H.
    unfold Mmult, adjoint in H; simpl in H.
    ring_simplify in H.
    rewrite <- H1, <- H2, Cconj_mult_distr in H.
    rewrite <- H2.
    destruct (Classical_Prop.classic (s1 i' O = 0)) as [| Hs1i'].
    { rewrite H3; ring. }
    assert (c * c' ^* = 1).
    {
      transitivity
         (c * s1 i 0%nat * (c' ^* * (s1 i' 0%nat) ^*) /
         (s1 i 0%nat * (s1 i' 0%nat) ^*)).
      { field. split; auto. intro. apply Cconj_eq_0 in H3; tauto. }
      rewrite <- H.
      field. split; auto. intro. apply Cconj_eq_0 in H3; tauto.
    }
    assert (c' ^* * c'= 1).
    {
      rewrite <- Cmod_Cconj.
      rewrite Hc'.
      unfold RtoC.
      f_equal.
      ring.
    }
    rewrite <- (Cmult_1_l c).
    rewrite <- H4.
    rewrite <- (Cmult_1_l c') at 3.
    rewrite <- H3.
    ring.
Qed.

Declare Scope Q_Operator.
Declare Scope Q_State.
Delimit Scope Q_Operator with QO.
Delimit Scope Q_State with QS.
Bind Scope Q_Operator with Operator.
Bind Scope Q_State with State.
Local Open Scope Q_Operator.
Local Open Scope Q_State.

Notation "A * B" := (Compose A B): Q_Operator.
Infix "≈" := OperatorEquiv (at level 70): Q_Operator.
Infix "≈" := StateEquiv (at level 70): Q_State.
Coercion Apply: Operator >-> Funclass.

Ltac by_def1 := exists 1%C; split; [autorewrite with C_db;auto | rewrite Mscale_1_l].
Ltac by_def c := exists c; split.
Ltac by_effect := rewrite OperatorEquiv_spec; intros.
Ltac by_den := rewrite StateEquiv_spec; intros.

Ltac state_reduce:=
let Hs := fresh "Hs" in
match goal with
| |-context [ @Mmult ?n 1 ?n 
(@Mmult ?n1 ?m ?n2 ?A ?B) (@adjoint ?m1 1 ?C ) ≡
  @Mmult  ?n 1 ?n ?D (@adjoint ?n 1 ?D)] =>
      match C with
      | @Mmult ?n2 ?m2 ?o ?A ?B=>
       assert (@Mmult n2 m2 o  A B ≡ D) as Hs
      end
end;
  [ |  repeat rewrite Hs; reflexivity].

Declare Scope QE.
Local Open Scope QE.

Ltac gen_equiv A B :=
  match type of A with
  | Matrix ?n ?m =>
      let n' := eval compute in n in
      let m' := eval compute in m in
      match constr:(@pair nat nat n' m') with
      | (64, 64)%nat => exact (@OperatorEquiv 6 A B)
      | (32, 32)%nat => exact (@OperatorEquiv 5 A B)
      | (16, 16)%nat => exact (@OperatorEquiv 4 A B)
      | (8, 8)%nat => exact (@OperatorEquiv 3 A B)
      | (4, 4)%nat => exact (@OperatorEquiv 2 A B)
      | (2, 2)%nat => exact (@OperatorEquiv 1 A B)
      | (16, 1)%nat => exact (@StateEquiv 4 A B)
      | (8, 1)%nat => exact (@StateEquiv 3 A B)
      | (4, 1)%nat => exact (@StateEquiv 2 A B)
      | (2, 1)%nat => exact (@StateEquiv 1 A B)
      end
  | Operator ?n =>
     exact (@OperatorEquiv n A B)
  | State ?n =>
     exact (@StateEquiv n A B)
  end.

Notation "A ≈ B" := (ltac:(gen_equiv A B)) (only parsing): QE.

Lemma Foo: H × H ≈ H.
Abort.

Lemma Foo: B0 ⊗ B0 ≈ H ⊗ H.
Abort.

Lemma Foo: B0 ⊗ (B0 ⊗ B0) ≈ (H ⊗ H) ⊗ H.
Abort.

Lemma Foo: B0 ⊗ (B0 ⊗ B0) × (∣0⟩ ⊗∣0⟩ ⊗∣0⟩) ≈ (H ⊗ H) ⊗ H × (∣0⟩ ⊗∣0⟩ ⊗∣0⟩).
Abort.

Goal forall (F: Operator 5) (X: State 5),
  Apply (F * F) X ≈ Apply F (Apply F X).
Proof.
  intros.
  by_def 1.
Abort.

Goal forall (F: Operator 5) (X: State 5),
  Apply (F * F) X ≈ Apply F (Apply F X).
Proof.
  intros.
  by_def1.
Abort.

Goal forall (F: Operator 5) (X: State 5),
  Apply (F * F) X ≈ Apply F (Apply F X).
Proof.
  intros.
  by_den.
Abort.

Goal forall (F: Operator 5),
  ((F * F) ≈ F).
Proof.
  intros.
  by_effect.
Abort.








