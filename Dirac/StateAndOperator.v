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

Lemma StateEquiv_spec: forall {n} (s1 s2: State n),
  StateEquiv s1 s2 <->
  @Mmult (Nat.pow 2 n) 1 (Nat.pow 2 n) s1 (s1 †) ≡
  @Mmult (Nat.pow 2 n) 1 (Nat.pow 2 n) s2 (s2 †) .
Admitted.

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
  ((F * F) ≈ F)%QO.
Proof.
  intros.
  by_effect.
Abort.














