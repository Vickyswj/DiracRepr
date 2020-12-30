Require Import Psatz.
Require Import Setoid.
Require Import Arith.
Require Import Bool.
Require Import Program.
Require Export reComplex.
Require Import Omega.
Require Import NArith.
Require Import Morphisms.

(* Require Import Psatz.
Require Import Program.
Require Import NArith.
Require Export Complex.
(* Require Import BinNat. *)
Require Import Omega.
Require Import List.
Require Import Setoid.
Require Import Coq.Classes.Morphisms. *)


(*******************************************)
(** Matrix Definitions and Equivalence **)
(*******************************************)

Declare Scope matrix_scope.
Delimit Scope matrix_scope with M.
Open Scope matrix_scope.

Local Open Scope N_scope.

Definition Matrix (m n : N) := N -> N -> C.

Notation Vector n := (Matrix n 1).
Notation Square n := (Matrix n n).

Definition mat_equiv {m n : N} (A B : Matrix m n) : Prop :=
  forall x y, x < m -> y < n -> A x y = B x y.

Infix "≡" := mat_equiv (at level 70) : matrix_scope.

Lemma mat_equiv_refl : forall m n (A : Matrix m n),  A ≡ A.
Proof. unfold mat_equiv; auto. Qed.

Lemma mat_equiv_symm : forall m n (A B : Matrix m n), A ≡ B <-> B ≡ A .
Proof.
  unfold mat_equiv. 
  split; intros; rewrite H; auto.
Qed.

Lemma mat_equiv_trans : forall m n (A B C : Matrix m n), 
      A ≡ B -> B ≡ C -> A ≡ C.
Proof.
  unfold mat_equiv. intros.
  rewrite H. rewrite H0. all: auto.
Qed.

Instance mat_equiv_equiv (m n: N) : Equivalence (@mat_equiv m n).
Proof.
  constructor;
  hnf; intros.
  - apply mat_equiv_refl.
  - apply mat_equiv_symm; auto.
  - eapply mat_equiv_trans; eauto.
Qed.

(*****************************)
(** Operands and Operations **)
(*****************************)

(* Notation "m =? n" := (N.eqb m n) (at level 70) : matrix_scope.
Notation "m <? n" := (N.ltb m n) (at level 70) : matrix_scope.
Notation "m <=? n" := (N.leb m n) (at level 70) : matrix_scope. *)

Definition Zero {m n} : Matrix m n := fun x y => C0.

Definition I (n : N) : Square n := fun x y => if (x =? y) && (x <? n) then C1 else C0.

(* This isn't used, but is interesting *)
Definition I__inf := fun x y => if x =? y then C1 else C0.
Notation "I∞" := I__inf : matrix_scope.

(*
Parameter Inline recursion : forall A : Type, A -> (t -> A -> A) -> t -> A.
Implicit Arguments recursion [A].

Declare Instance recursion_wd (A : Type) (Aeq : relation A) :
 Proper (Aeq ==> (eq==>Aeq==>Aeq) ==> eq ==> Aeq) (@recursion A).

Axiom recursion_0 :
  forall (A : Type) (a : A) (f : t -> A -> A), recursion a f 0 = a.

Axiom recursion_succ :
  forall (A : Type) (Aeq : relation A) (a : A) (f : t -> A -> A),
    Aeq a a -> Proper (eq==>Aeq==>Aeq) f ->
      forall n, Aeq (recursion a f (S n)) (f n (recursion a f n)).
*)

Check N.peano_rect .
Check N.recursion.

Definition Csum (f : N -> C) (n : N) : C := 
  @N.recursion C C0 (fun x y => (y + (f x))%C) n.

(* Fixpoint Csum (f : nat -> C) (n : nat) : C := 
  match n with
  | 0 => C0
  | S n' => (Csum f n' +  f n')%C
  end. *)

Definition trace {n} (A : Square n) :=
  Csum (fun x => A x x) n.

Definition scale {m n} (c : C) (A : Matrix m n) : Matrix m n :=
  fun x y => (c * A x y)%C.

Definition dot {n} (A : Vector n) (B : Vector n) : C :=
  Csum (fun x => A x 0 * B x 0)%C n.

Definition Mplus {m n} (A B : Matrix m n) : Matrix m n :=
  fun x y => (A x y + B x y)%C.

Definition Mmult {m n o} (A : Matrix m n) (B : Matrix n o) : Matrix m o :=
  fun x z => Csum (fun y => A x y * B y z)%C n.

(* Only well-defined when o and p are non-zero *)
Definition kron {m n o p} (A : Matrix m n) (B : Matrix o p) : Matrix (m*o) (n*p) :=
  fun x y => Cmult (A (x / o) (y / p)) (B (x mod o) (y mod p)).

Definition transpose {m n} (A : Matrix m n) : Matrix n m :=
  fun x y => A y x.

Definition adjoint {m n} (A : Matrix m n) : Matrix n m :=
  fun x y => (A y x)^*.

Definition inner_product {n} (u v : Vector n) : C :=
  Mmult (adjoint u) (v) 0 0.

Definition outer_product {n} (u v : Vector n) : Square n :=
  Mmult u (adjoint v).

Definition kron_n {m1 m2} (A : Matrix m1 m2) n : Matrix (m1^n) (m2^n) :=
  @N.recursion (Matrix (m1^n) (m2^n)) (I 1) (fun x y => kron y A) n.

Definition kron_n' {m1 m2} (f : N -> Matrix m1 m2) n : Matrix (m1^n) (m2^n) :=
  @N.recursion (Matrix (m1^n) (m2^n)) (I 1) (fun x y => kron y (f x)) n.

(* Fixpoint kron_n n {m1 m2} (A : Matrix m1 m2) : Matrix (m1^n) (m2^n) :=
  match n with
  | 0    => I 1
  | S n' => kron (kron_n n' A) A
  end. *)

Infix "∘" := dot (at level 40, left associativity) : matrix_scope.
Infix ".+" := Mplus (at level 50, left associativity) : matrix_scope.
Infix ".*" := scale (at level 40, left associativity) : matrix_scope.
Infix "×" := Mmult (at level 40, left associativity) : matrix_scope.
Infix "⊗" := kron (at level 40, left associativity) : matrix_scope.
Notation "A ⊤" := (transpose A) (at level 0) : matrix_scope. 
Notation "A †" := (adjoint A) (at level 0) : matrix_scope.
Notation "Σ^ n f" := (Csum f n) (at level 60) : matrix_scope.
Notation "⟨ A , B ⟩" := (inner_product A B) : matrix_scope.
Notation "n ⨂ A" := (kron_n n A) (at level 30, no associativity) : matrix_scope.

Hint Unfold Zero I trace scale dot Mplus Mmult kron transpose adjoint : U_db.


(******************************)
(** Proofs about finite sums **)
(******************************)

Local Open Scope C.

Lemma Csum_succ : forall f n,
  Csum f (N.succ n) = (Csum f n) + f n.
Proof.
  intros.
  unfold Csum.
  rewrite N.recursion_succ.
  - auto.
  - auto.
  - unfold Morphisms.Proper.
    unfold Morphisms.respectful.
    intros; subst; auto.
Qed.

(* Lemma Csum_0 : forall f n, (forall x, x < n -> f x = C0) -> Csum f n = C0.
Proof.
  intros f n. 
  N.induct n;intros.
    - auto.
    - rewrite Csum_succ.  rewrite H. rewrite H0.
       lca. lia. intros. apply H0. lia.
Qed. *)

Lemma Csum_0 : forall f n, (forall x,  f x = C0) -> Csum f n = C0.
Proof.
  intros. N.induct n.
  - auto.
  - intros. rewrite Csum_succ.
    rewrite H. rewrite H0. lca.
Qed. 


Lemma Csum_plus : forall (f g : N -> C) (n : N),
    Csum (fun x => f x + g x) n = Csum f n + Csum g n.
Proof. 
  intros.  N.induct n.
  - lca.
  - intros. repeat rewrite Csum_succ.
     rewrite H. lca.
Qed.

Lemma Csum_mult_l : forall (c : C) (f : N -> C) (n : N),
    c * Csum f n = Csum (fun x => c * f x) n.
Proof.
  intros.  N.induct n.
  - lca.
  - intros. repeat rewrite Csum_succ.
    rewrite Cmult_plus_distr_l.
    rewrite H. auto.
Qed.


(** Basic Matrix Lemmas **)
Lemma Zero_l :forall (n : N) (A : Matrix 0 n),  A ≡ Zero.
Proof.
  unfold mat_equiv,Zero. intros.
  destruct x; exfalso; lia.
Qed.

Lemma Zero_r :forall (n : N) (A : Matrix n 0), A ≡ Zero.
Proof.
  unfold mat_equiv,Zero. intros.
  destruct y; exfalso; lia.
Qed.

Lemma Zero_Zero :forall (A : Matrix 0 0), A ≡ Zero.
Proof.
  unfold mat_equiv,Zero. intros.
  destruct y; exfalso; lia.
Qed.

Lemma trace_plus_dist : forall (n : N) (A B : Square n),
    trace (A .+ B) = trace A + trace B.
Proof.
  unfold trace, Mplus. intros.
  rewrite Csum_plus.
  auto.
Qed.

Lemma trace_mult_dist : forall n p (A : Square n), trace (p .* A) = p * trace A.
Proof.
  unfold trace, scale. intros.
  rewrite Csum_mult_l.
  auto.
Qed.

Lemma Mplus_0_l : forall (m n : N) (A : Matrix m n), Zero .+ A ≡ A.
Proof. 
  unfold mat_equiv,Mmult, Zero. 
  intros. lca.
Qed.

Lemma Mplus_0_r : forall (m n : N) (A : Matrix m n), A .+ Zero ≡ A.
Proof. 
  unfold mat_equiv,Mmult, Zero. 
  intros. lca.
Qed.

Lemma Mmult_0_l : forall (m n o : N) (A : Matrix n o), @Zero m n × A ≡ Zero.
Proof.
  unfold mat_equiv,Mmult, Zero. intros.
  apply Csum_0. intros. lca.
Qed.

Lemma Mmult_0_r : forall (m n o : N) (A : Matrix m n), A × @Zero n o ≡ Zero.
Proof.
  unfold mat_equiv,Mmult, Zero. intros.
  apply Csum_0. intros. lca.
Qed.

Lemma Mmult_1_l_gen: forall (m n : N) (A : Matrix m n) (x z k : N), 
  k <= m ->
  (k <= x -> Csum (fun y => I m x y * A y z) k = C0) /\
  (k > x -> Csum (fun y => I m x y * A y z) k = A x z).
Proof.
  intros m n A x z k.
  N.induct k; intros.
  * simpl. split. reflexivity. lia.
  * destruct H as [IHl IHr]. lia.
     rewrite Csum_succ. split.
    + intros. unfold I. destruct (N.eq_dec x n0).
        - lia.
        - apply N.eqb_neq in n1. rewrite n1.
           autorewrite with C_db. apply IHl. lia.
    + intros. unfold I in *. destruct (x =? n0) eqn:E1.
       - destruct (x <? m) eqn:E2.
          { apply N.eqb_eq in E1. subst.
             autorewrite with C_db. rewrite IHl by lia. lca. }
          { apply N.eqb_eq in E1. subst.
             rewrite N.ltb_ge in E2. lia. }
      - destruct (x <? m) eqn:E2.
          { apply N.eqb_neq in E1. rewrite N.ltb_lt in E2.
             autorewrite with C_db. rewrite IHr by lia. lca. }
          { apply N.eqb_neq in E1.
             autorewrite with C_db. rewrite IHr by lia. lca. }
Qed.

Lemma Mmult_1_l : forall (m n : N) (A : Matrix m n), I m × A ≡ A.
Proof.
  unfold mat_equiv, Mmult. intros.
  edestruct (@Mmult_1_l_gen m n) as [Hl Hr].
  + apply N.le_refl. 
  + apply Hr. lia.
Qed.

(* Lemma Csum_unique : forall (f : N -> C) (k : C) (n x : N), 
   x < n -> f x = k ->
  (forall x', x <> x' -> f x' =0%R) ->
  Csum f n = k.
Proof.
  intros f k n. N.induct n; intros.
  - lia.
  - rewrite Csum_succ. destruct (N.eq_dec n x).
    + subst. rewrite Csum_0. lca. intros; apply H2. lia.
    + rewrite H2. rewrite (H x). lca. lia. auto. auto. auto.
Qed.

Lemma Mmult_1_l : forall (m n : N) (A : Matrix m n), I m × A ≡ A.
Proof.
  intros m n A i j Hi Hj.
  unfold Mmult.
  eapply Csum_unique. apply Hi.
  unfold I. rewrite N.eqb_refl.
  assert (i <? m = true)%N.
  apply N.ltb_lt. auto. rewrite H. lca.
  intros. unfold I.
  apply N.eqb_neq in H.
  rewrite H. lca.
Qed. *)

Lemma Mmult_1_r_gen: forall (m n : N) (A : Matrix m n) (x z k : N), 
  (k <= n) ->
  (k <= z -> Csum (fun y => A x y * (I n) y z) k = C0) /\
  (k > z -> Csum (fun y => A x y * (I n) y z) k = A x z).
Proof.
  intros m n A x z k.
  N.induct k; intros.
  * simpl. split. reflexivity. lia.
  * destruct H as [IHl IHr]. lia.
     rewrite Csum_succ. split.
    + intros. unfold I. destruct (N.eq_dec n0 z).
        - lia.
        - apply N.eqb_neq in n1. rewrite n1.
           autorewrite with C_db. apply IHl. lia.
    + intros. unfold I in *. destruct (n0 =? z) eqn:E1.
       - destruct (n0 <? n) eqn:E2.
          { apply N.eqb_eq in E1. subst.
             autorewrite with C_db. rewrite IHl by lia. lca. }
          { apply N.eqb_eq in E1. subst.
             rewrite N.ltb_ge in E2. lia. }
      - destruct (n0 <? n) eqn:E2.
          { apply N.eqb_neq in E1. rewrite N.ltb_lt in E2.
             autorewrite with C_db. rewrite IHr by lia. lca. }
          { apply N.eqb_neq in E1.
             autorewrite with C_db. rewrite IHr by lia. lca. }
Qed.

Lemma Mmult_1_r : forall (m n : N) (A : Matrix m n), A × I n ≡ A.
Proof.
  unfold mat_equiv, Mmult. intros.
  edestruct (@Mmult_1_r_gen m n) as [Hl Hr].
  + apply N.le_refl. 
  + apply Hr. lia.
Qed.

Lemma kron_0_l : forall (m n o p : N) (A : Matrix o p), 
  @Zero m n ⊗ A ≡ Zero.
Proof.
  unfold mat_equiv, kron, Zero.
  unfold mat_equiv. intros.
  rewrite Cmult_0_l. auto.
Qed.

Lemma kron_0_r : forall (m n o p : N) (A : Matrix m n), 
   A ⊗ @Zero o p ≡ Zero.
Proof.
  unfold mat_equiv, kron, Zero.
  unfold mat_equiv. intros.
  rewrite Cmult_0_r. auto.
Qed.

Lemma kron_1_r : forall (m n : N) (A : Matrix m n), A ⊗ I 1 ≡ A.
Proof.
  unfold mat_equiv, I, kron. intros.
  rewrite 2 N.div_1_r.
  rewrite 2 N.mod_1_r.
  autorewrite with C_db. auto.
Qed.

Lemma kron_1_l : forall (m n : N) (A : Matrix m n), I 1 ⊗ A ≡ A.
Proof.
  intros m n A.
  unfold mat_equiv,I,kron. intros.
    destruct (N.eq_dec m 0). subst. lia.
    destruct (N.eq_dec n 0). subst. lia.
  destruct (x / m <? 1)eqn:E1. rewrite N.ltb_lt in E1.
  destruct (x / m =? y / n) eqn:E2;simpl.  rewrite N.eqb_eq in E2.
  + assert (x / m = 0)%N. apply N.lt_1_r. auto. clear E1. rename H1 into E1.
    rewrite E1 in E2. symmetry in E2.
    rewrite N.div_small_iff in E2 by lia.
    rewrite N.div_small_iff in E1 by lia.
    rewrite 2 N.mod_small; trivial. lca.
  + apply N.lt_1_r in E1. 
    assert (x / m = 0)%N by lia. clear E1.
    rewrite H1 in E2. clear H1.
    assert (y / n <> 0)%N. apply N.eqb_neq. auto. clear E2.
    rewrite N.div_small_iff in H1 by lia.
    rewrite Cmult_0_l. exfalso. lia.
  + rewrite andb_false_r. apply N.ltb_ge in E1.
    assert (x / m  <> 0)%N by lia. clear E1.
    rewrite N.div_small_iff in H1 by lia.
    rewrite Cmult_0_l. exfalso. lia.
Qed.

Theorem transpose_involutive : forall (m n : N) (A : Matrix m n), (A⊤)⊤ ≡ A.
Proof.
  unfold mat_equiv,transpose.
  intros.  auto.
Qed.

Theorem adjoint_involutive : forall (m n : N) (A : Matrix m n), A†† ≡ A.
Proof.
  unfold mat_equiv,adjoint.
  intros. lca.
Qed.

Lemma id_transpose_eq : forall n, (I n)⊤ ≡ (I n).
Proof.
  unfold mat_equiv,transpose, I.
  intros. destruct (N.eq_dec x y).
  + subst. auto.
  + apply N.eqb_neq in n0. 
     rewrite N.eqb_sym. 
     rewrite n0. auto.
Qed.

Lemma zero_transpose_eq : forall m n, (@Zero m n)⊤ ≡ @Zero m n.
Proof.
  unfold mat_equiv,transpose.
  intros. auto.
Qed.


Lemma id_adjoint_eq : forall n, (I n)† ≡ (I n).
Proof.
  unfold mat_equiv,adjoint, I.
  intros. destruct (N.eq_dec x y).
   + subst. apply N.ltb_lt in H0.
       rewrite N.eqb_refl,H0. lca.
   + apply N.eqb_neq in n0.
      apply N.ltb_lt in H0.
      rewrite N.eqb_sym,n0. lca.
Qed.
