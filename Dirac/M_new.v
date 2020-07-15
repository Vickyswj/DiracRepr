Require Import Psatz.
Require Import String.
Require Import Program.
Require Export Complex.
Require Import BinNat.
Require Import List.
Require Coq.Setoids.Setoid.
Require Import Coq.Classes.Morphisms.


Declare Scope matrix_scope.
Delimit Scope matrix_scope with M.
Open Scope matrix_scope.
Local Open Scope nat_scope.

Definition Matrix (m n : N) := nat -> nat -> C.

(* Definition M2MM {n m} (A : Matrix n m) : M.Matrix (N.to_nat n) (N.to_nat m) :=
fun x y => A x y.

Definition MM2M {n m} (A : M.Matrix n m) : Matrix (N.of_nat n) (N.of_nat m) :=
fun x y => A x y. *)

Notation Vector n := (Matrix n 1).

Notation Square n := (Matrix n n).

(* Showing equality via functional extensionality *)
Ltac prep_matrix_equality :=
  let x := fresh "x" in 
  let y := fresh "y" in 
  apply functional_extensionality; intros x;
  apply functional_extensionality; intros y.

(* Lemma idM {n m} (A : Matrix n m) : MM2M (M2MM A) = A.
Proof.
unfold M2MM,MM2M.
prep_matrix_equality.
auto.
Qed.

Lemma idMM {n m} (A : M.Matrix n m) : M2MM (MM2M A) = A.
Proof.
unfold M2MM,MM2M.
prep_matrix_equality.
auto.
Qed. *)

(* Matrix Equivalence *)
Definition get {m n} (A : Matrix m n) (a : nat | a < (N.to_nat m)) (b : nat | b < (N.to_nat n)) := 
  A (`a) (`b).

Definition mat_equiv {m n : N} (A B : Matrix m n) : Prop := 
  forall (x : nat | x < (N.to_nat m)) (y : nat | y < (N.to_nat n)), get A x y = get B x y.

Lemma mat_equiv_refl : forall m n (A : Matrix m n), mat_equiv A A.
Proof. unfold mat_equiv; reflexivity. Qed.

Lemma mat_equiv_symm : forall m n (A B : Matrix m n), mat_equiv A B <-> mat_equiv B A .
Proof.
  unfold mat_equiv. split.
  intros. rewrite H. auto.
  intros. rewrite H. auto.
Qed.

Lemma mat_equiv_trans : forall m n (A B C : Matrix m n), 
      mat_equiv A B -> mat_equiv B C -> mat_equiv A C.
Proof.
  unfold mat_equiv. intros.
  rewrite H. rewrite H0. auto.
Qed.

Instance mat_equiv_equiv (m n: N) : Equivalence (@mat_equiv m n).
Proof.
constructor.
hnf; intros.
apply mat_equiv_refl.
hnf; intros.
apply mat_equiv_symm; auto.
hnf; intros.
eapply mat_equiv_trans; eauto.
Qed.

(* Printing *)

Parameter print_C : C -> string.
Fixpoint print_row {m n} (i j : nat) (A : Matrix m n) : string :=
  match j with
  | 0   => "\n"
  | S j' => print_C (A i j') ++ ", " ++ print_row i j' A
  end.

Fixpoint print_rows {m n} (i j : nat) (A : Matrix m n) : string :=
  match i with
  | 0   => ""
  | S i' => print_row i' (N.to_nat n) A ++ print_rows i' (N.to_nat n) A
  end.

Definition print_matrix {m n} (A : Matrix m n) : string :=
  print_rows (N.to_nat m) (N.to_nat n) A.

(*****************************)
(** Operands and Operations **)
(*****************************)
Definition Zero {m n} : Matrix m n :=
 fun x y => 0%R.

Definition I (n : N) : Square n :=
fun x y => if (x =? y) && (x <? (N.to_nat n)) then C1 else C0.

(* This isn't used, but is interesting *)
Definition I__inf := fun x y => if x =? y then C1 else C0.
Notation "I∞" := I__inf : matrix_scope.


(* sum to n exclusive *)
Fixpoint Csum (f : nat -> C) (n : nat) : C := 
  match n with
  | 0 => C0
  | S n' => (Csum f n' +  f n')%C
  end.

Definition trace {n} (A : Square n) := 
  Csum (fun x => A x x) (N.to_nat n).

Definition scale {m n} (r : C) (A : Matrix m n) : Matrix m n := 
  fun x y => (r * A x y)%C.

Definition dot {n} (A : Vector n) (B : Vector n) : C :=
  Csum (fun x => A x 0  * B x 0)%C (N.to_nat n).

Definition Mplus {m n} (A B : Matrix m n) : Matrix m n :=
  fun x y => (A x y + B x y)%C.

Definition Mmult {m n o} (A : Matrix m n) (B : Matrix n o) : Matrix m o := 
  fun x z => Csum (fun y => A x y * B y z)%C (N.to_nat n).

(* Only well-defined when o and p are non-zero *)
Definition kron {m n o p} (A : Matrix m n) (B : Matrix o p) : 
  Matrix (m*o) (n*p) :=
  fun x y => Cmult (A (x / (N.to_nat o)) (y / (N.to_nat p))) (B (x mod (N.to_nat o)) (y mod (N.to_nat p))).

Definition transpose {m n} (A : Matrix m n) : Matrix n m := 
  fun x y => A y x.

Definition adjoint {m n} (A : Matrix m n) : Matrix n m := 
  fun x y => (A y x)^*.

Definition inner_product {n} (u v : Vector n) : C := 
  Mmult (adjoint u) (v) 0 0.

Definition outer_product {n} (u v : Vector n) : Square n := 
  Mmult u (adjoint v).

(* Kronecker of n copies of A *)
Fixpoint kron_n (n:nat) {m1 m2} (A : Matrix m1 m2) : Matrix (m1^(N.of_nat n)) (m2^(N.of_nat n)) :=
  match n with
  | 0    => I 1
  | S n' => kron A (kron_n n' A)
  end.

(* Kronecker product of a list *)
Fixpoint big_kron {m n} (As : list (Matrix m n)) : 
  Matrix (m^(N.of_nat (length As))) (n^(N.of_nat (length As))) := 
  match As with
  | [] => I 1
  | A :: As' => kron A (big_kron As')
  end.

Infix "∘" := dot (at level 40, left associativity) : matrix_scope.
Infix ".+" := Mplus (at level 50, left associativity) : matrix_scope.
Infix ".*" := scale (at level 40, left associativity) : matrix_scope.
Infix "×" := Mmult (at level 40, left associativity) : matrix_scope.
Infix "⊗" := kron (at level 40, left associativity) : matrix_scope.
Infix "≡" := mat_equiv (at level 70) : matrix_scope.
Notation "A ⊤" := (transpose A) (at level 0) : matrix_scope. 
Notation "A †" := (adjoint A) (at level 0) : matrix_scope.
Notation "Σ^ n f" := (Csum f n) (at level 60) : matrix_scope.
Notation "n ⨂ A" := (kron_n n A) (at level 30, no associativity) : matrix_scope.
Notation "⨂ A" := (big_kron A) (at level 60): matrix_scope.
Hint Unfold Zero I trace dot Mplus scale Mmult kron mat_equiv transpose 
            adjoint : U_db.


(* Lemma mat_equiv_trans2 : forall{m n} (A B C : Matrix m n),
    A ≡ B -> A ≡ C -> B ≡ C.
Proof.
  intros m n A B C HAB HAC.
  rewrite <- HAB.
  apply HAC.
Qed. *)

Ltac destruct_m_1 :=
  match goal with
  | [ |- context[match ?x with 
                 | 0   => _
                 | S _ => _
                 end] ] => is_var x; destruct x
  end.
Ltac destruct_m_eq := repeat (destruct_m_1; simpl).

Ltac bdestruct_all :=
  repeat match goal with
  | |- context[?a <? ?b] => bdestruct (a <? b)
  | |- context[?a <=? ?b] => bdestruct (a <=? b)
  | |- context[?a =? ?b] => bdestruct (a =? b)
  end; try (exfalso; lia).

Ltac lma :=
  autounfold with U_db;
  prep_matrix_equality;
  destruct_m_eq; 
  lca.

(******************************)
(** Proofs about finite sums **)
(******************************)

Local Close Scope nat_scope.

Lemma Csum_0 : forall f n, (forall x, f x = C0) -> Csum f n = 0. 
Proof.
  intros.
  induction n.
  - reflexivity.
  - simpl.
    rewrite IHn, H. 
    lca.
Qed.

Lemma Csum_1 : forall f n, (forall x, f x = C1) -> Csum f n = INR n. 
Proof.
  intros.
  induction n.
  - reflexivity.
  - simpl.
    rewrite IHn, H.
    destruct n; lca.
Qed.

Lemma Csum_constant : forall c n, Csum (fun x => c) n = INR n * c.
Proof.
  intros c n.
  induction n.
  + simpl; lca.
  + simpl.
    rewrite IHn.
    destruct n; lca.
Qed.

Lemma Csum_eq : forall f g n, f = g -> Csum f n = Csum g n.
Proof. intros f g n H. subst. reflexivity. Qed.

Lemma Csum_0_bounded : forall f n, (forall x, (x < n)%nat -> f x = C0) -> Csum f n = 0. 
Proof.
  intros.
  induction n.
  - reflexivity.
  - simpl.
    rewrite IHn, H.
    lca.
    lia.
    intros.
    apply H.
    lia.
Qed.

Lemma Csum_eq_bounded : forall f g n, (forall x, (x < n)%nat -> f x = g x) -> Csum f n = Csum g n.
Proof. 
  intros f g n H. 
  induction n.
  + simpl. reflexivity.
  + simpl. 
    rewrite H by lia.
    rewrite IHn by (intros; apply H; lia).
    reflexivity.
Qed.

Lemma Csum_plus : forall f g n, Csum (fun x => f x + g x) n = Csum f n + Csum g n.
Proof.
  intros f g n.
  induction n.
  + simpl. lca.
  + simpl. rewrite IHn. lca.
Qed.

Lemma Csum_mult_l : forall c f n, c * Csum f n = Csum (fun x => c * f x) n.
Proof.
  intros c f n.
  induction n.
  + simpl; lca.
  + simpl.
    rewrite Cmult_plus_distr_l.
    rewrite IHn.
    reflexivity.
Qed.

Lemma Csum_mult_r : forall c f n, Csum f n * c = Csum (fun x => f x * c) n.
Proof.
  intros c f n.
  induction n.
  + simpl; lca.
  + simpl.
    rewrite Cmult_plus_distr_r.
    rewrite IHn.
    reflexivity.
Qed.

Lemma Csum_conj_distr : forall f n, (Csum f n) ^* = Csum (fun x => (f x)^*) n.
Proof. 
  intros f n.
  induction n.
  + simpl; lca.
  + simpl. 
    rewrite Cconj_plus_distr.
    rewrite IHn.
    reflexivity.
Qed.
    
Lemma Csum_extend_r : forall n f, Csum f n + f n = Csum f (S n).
Proof. reflexivity. Qed.

Lemma Csum_extend_l : forall n f, f O + Csum (fun x => f (S x)) n = Csum f (S n).
Proof.
  intros n f.
  induction n.
  + simpl; lca.
  + simpl.
    rewrite Cplus_assoc.
    rewrite IHn.
    simpl.
    reflexivity.
Qed.

Lemma Csum_unique : forall k (f : nat -> C) n, 
  (exists x, (x < n)%nat /\ f x = k /\ (forall x', x <> x' -> f x' = 0)) ->
  Csum f n = k.
Proof.                    
  intros k f n [x [L [Eq Unique]]].
  induction n; try lia.
  Search Csum.
  rewrite <- Csum_extend_r.
  destruct (Nat.eq_dec x n).
  - subst. 
    rewrite Csum_0_bounded.
    lca.
    intros.
    apply Unique.
    lia.
  - rewrite Unique by easy.
    Csimpl.
    apply IHn.
    lia.
Qed.    

Lemma Csum_sum : forall m n f, Csum f (m + n) = 
                          Csum f m + Csum (fun x => f (m + x)%nat) n. 
Proof.    
  intros m n f.
  induction m.
  + simpl. rewrite Cplus_0_l. reflexivity. 
  + simpl.
    rewrite IHm.
    repeat rewrite <- Cplus_assoc.
    remember (fun y => f (m + y)%nat) as g.
    replace (f m) with (g O) by (subst; rewrite plus_0_r; reflexivity).
    replace (f (m + n)%nat) with (g n) by (subst; reflexivity).
    replace (Csum (fun x : nat => f (S (m + x))) n) with
            (Csum (fun x : nat => g (S x)) n).
    2:{ apply Csum_eq. subst. apply functional_extensionality.
    intros; rewrite <- plus_n_Sm. reflexivity. }
    rewrite Csum_extend_l.
    rewrite Csum_extend_r.
    reflexivity.
Qed.

Lemma Csum_product : forall m n f g, n <> O ->
                              Csum f m * Csum g n = 
                              Csum (fun x => f (x / n)%nat * g (x mod n)%nat) (m * n). 
Proof.
  intros.
  induction m.
  + simpl; lca.
  + simpl.      
    rewrite Cmult_plus_distr_r.
    rewrite IHm. clear IHm.
    rewrite Csum_mult_l.    
    remember ((fun x : nat => f (x / n)%nat * g (x mod n)%nat)) as h.
    replace (Csum (fun x : nat => f m * g x) n) with
            (Csum (fun x : nat => h ((m * n) + x)%nat) n). 
    2:{
      subst.
      apply Csum_eq_bounded.
      intros x Hx.
      rewrite Nat.div_add_l by assumption.
      rewrite Nat.div_small; trivial.
      rewrite plus_0_r.
      rewrite Nat.add_mod by assumption.
      rewrite Nat.mod_mul by assumption.
      rewrite plus_0_l.
      repeat rewrite Nat.mod_small; trivial. }
    rewrite <- Csum_sum.
    rewrite plus_comm.
    reflexivity.
Qed.

Lemma Csum_ge_0 : forall f n, (forall x, 0 <= fst (f x)) -> 0 <= fst (Csum f n).
Proof.
  intros f n H.
  induction n.
  - simpl. lra. 
  - simpl in *.
    rewrite <- Rplus_0_r at 1.
    apply Rplus_le_compat; easy.
Qed.

Lemma Csum_member_le : forall (f : nat -> C) (n : nat), (forall x, 0 <= fst (f x)) -> 
                      (forall x, (x < n)%nat -> fst (f x) <= fst (Csum f n)).
Proof.
  intros f.
  induction n.
  - intros H x Lt. inversion Lt.
  - intros H x Lt.
    bdestruct (Nat.ltb x n).
    + simpl.
      rewrite <- Rplus_0_r at 1.
      apply Rplus_le_compat.
      apply IHn; easy.
      apply H.
    + assert (E: x = n) by lia.
      rewrite E.
      simpl.
      rewrite <- Rplus_0_l at 1.
      apply Rplus_le_compat. 
      apply Csum_ge_0; easy.
      lra.
Qed.
(***************************************)
(* Tactics for showing well-formedness *)
(***************************************)

Local Open Scope nat.
Local Open Scope R.
Local Open Scope C.

(** Basic Matrix Lemmas **)
Lemma Zero_l :forall (n : nat) (A : Matrix 0 (N.of_nat n)),  A ≡ Zero.
Proof.
  intros n A.
  unfold mat_equiv,Zero,get.
  intros.
  destruct x. exfalso. lia.
Qed.

Lemma Zero_r :forall (n : nat) (A : Matrix (N.of_nat n) 0), A ≡ Zero.
Proof.
  intros n A.
  unfold mat_equiv,Zero,get.
  intros.
  destruct y. exfalso. lia.
Qed.

Lemma Zero_Zero :forall (A : Matrix 0 0), A ≡ Zero.
Proof.
  intros n A.
  unfold mat_equiv,Zero,get.
  intros.
  destruct y. exfalso. lia.
Qed.

Lemma trace_plus_dist : forall (n : N) (A B : Square n), 
    trace (A .+ B) = (trace A + trace B)%C. 
Proof.
  intros.
  unfold trace, Mplus.
  induction (N.to_nat n).
  - simpl. lca.
  - simpl. rewrite IHn0. lca.
Qed.

Lemma trace_mult_dist : forall n p (A : Square n), trace (p .* A) = (p * trace A)%C. 
Proof.
  intros.
  unfold trace, scale.
  induction (N.to_nat n).
  - simpl. lca.
  - simpl. rewrite IHn0. lca.
Qed.

Lemma Mplus_0_l : forall (m n : N) (A : Matrix m n), Zero .+ A = A.
Proof. intros. lma. Qed.

Lemma Mplus_0_r : forall (m n : N) (A : Matrix m n), A .+ Zero = A.
Proof. intros. lma. Qed.

Lemma Mmult_0_l : forall (m n o : N) (A : Matrix n o), @Zero m n × A = Zero.
Proof.
  intros m n o A. 
  unfold Mmult, Zero.
  prep_matrix_equality.
  induction (N.to_nat n).
  + simpl. reflexivity.
  + simpl in *.
    autorewrite with C_db.
    apply IHn0.
Qed.

Lemma Mmult_0_r : forall (m n o : N) (A : Matrix m n), A × @Zero n o = Zero.
Proof.
  intros m n o A. 
  unfold Zero, Mmult.
  prep_matrix_equality.
  induction (N.to_nat n).
  + simpl. reflexivity.
  + simpl. 
    autorewrite with C_db.
    apply IHn0.
Qed.

(* using <= because our form Csum is exclusive. *)

Lemma Mmult_1_l_gen: forall (m n : N) (A : Matrix m n) (x z k : nat), 
  (k <= (N.to_nat m))%nat ->
  ((k <= x)%nat -> Csum (fun y : nat => I m x y * A y z) k = 0) /\
  ((k > x)%nat -> Csum (fun y : nat => I m x y * A y z) k = A x z).
Proof.  
  intros m n A x z k B.
  induction k.
  * simpl. split. reflexivity. lia.
  * destruct IHk as [IHl IHr]. lia.
    split.
    + intros leSkx.
      simpl.
      unfold I.
      bdestruct (x =? k); try lia.
      autorewrite with C_db.
      apply IHl.
      lia.
    + intros gtSkx.
      simpl in *.
      unfold I in *.
      bdestruct_all; subst; try lia.
      rewrite IHl by lia; simpl; lca.
      rewrite IHr by lia; simpl; lca.
Qed.

Lemma Mmult_1_l : forall (m n : N) (A : Matrix m n), I m × A ≡ A.
Proof.
  intros m n A x y.
  destruct x as [x Px], y as [y Py].
  simpl. 
  unfold Mmult.
  edestruct (@Mmult_1_l_gen m n) as [Hl Hr].
  apply Nat.le_refl.
  unfold get.
  apply Hr.
  simpl in *.
  lia.
Qed.

Lemma Mmult_1_r_gen: forall (m n : N) (A : Matrix m n) (x z k : nat), 
  (k <= (N.to_nat n))%nat ->
  ((k <= z)%nat -> Csum (fun y : nat => A x y * (I n) y z) k = 0) /\
  ((k > z)%nat -> Csum (fun y : nat => A x y * (I n) y z) k = A x z).
Proof.
  intros m n A x z k B.
  induction k.
  simpl. split. reflexivity. lia.
  destruct IHk as [IHl IHr].
  lia.
  split.
  + intros leSkz.
    simpl in *.
    unfold I.
    bdestruct (k =? z); try lia.
    autorewrite with C_db.
    apply IHl; lia.
  + intros gtSkz.
    simpl in *.
    unfold I in *.
      bdestruct_all; subst; try lia.
      rewrite IHl by lia; simpl; lca.
      rewrite IHr by lia; simpl; lca.
Qed.

Lemma Mmult_1_r : forall (m n : N) (A : Matrix m n), A × I n ≡ A.
Proof.
  intros m n A x y.
  destruct x as [x Px], y as [y Py].
  simpl. 
  unfold Mmult.
  edestruct (@Mmult_1_r_gen m n) as [Hl Hr].
  apply Nat.le_refl.
  unfold get; simpl.
  apply Hr.
  lia.
Qed.

Lemma kron_0_l : forall (m n o p : N) (A : Matrix o p), 
  @Zero m n ⊗ A = Zero.
Proof.
  intros m n o p A.
  prep_matrix_equality.
  unfold Zero, kron.
  rewrite Cmult_0_l.
  reflexivity.
Qed.

Lemma kron_0_r : forall (m n o p : N) (A : Matrix m n), 
   A ⊗ @Zero o p = Zero.
Proof.
  intros m n o p A.
  prep_matrix_equality.
  unfold Zero, kron.
  rewrite Cmult_0_r.
  reflexivity.
Qed.

Lemma kron_1_r : forall (m n : N) (A : Matrix m n), A ⊗ I 1 = A.
Proof.
  intros m n A.
  prep_matrix_equality.
  unfold I, kron.
  rewrite 2 Nat.div_1_r.
  rewrite 2 Nat.mod_1_r.
  simpl.
  autorewrite with C_db.
  reflexivity.
Qed.

(* This side is more limited *)
Lemma kron_1_l : forall (m n : N) (A : Matrix m n), I 1 ⊗ A ≡ A.
Proof.
  intros m n A.
  unfold mat_equiv,I,kron.
  intros x1 y1.
    bdestruct ((N.to_nat m) =? 0). destruct x1. exfalso. lia.
    bdestruct ((N.to_nat n) =? 0). destruct y1. exfalso. lia.
  destruct x1 as [x Px], y1 as [y Py].
  unfold get.
  simpl. replace (Pos.to_nat 1) with 1%nat by auto.
  bdestruct (x / (N.to_nat m) <? 1); rename H1 into Eq1. 
  bdestruct (x / (N.to_nat m) =? y / (N.to_nat n)); rename H1 into Eq2; simpl.
  + assert (x / (N.to_nat m) = 0)%nat by lia. clear Eq1. rename H1 into Eq1.
    rewrite Eq1 in Eq2.
    symmetry in Eq2.
    rewrite Nat.div_small_iff in Eq2 by lia.
    Check Nat.div_small_iff.
    Check Nat.mod_small.
    rewrite Nat.div_small_iff in Eq1 by lia.
    rewrite 2 Nat.mod_small; trivial.
    lca.
  + assert (x / (N.to_nat m) = 0)%nat by lia. clear Eq1.
    rewrite H1 in Eq2. clear H1.
    assert (y / (N.to_nat n) <> 0)%nat by lia. clear Eq2.
    rewrite Nat.div_small_iff in H1 by lia.
    rewrite Cmult_0_l.
    exfalso. lia.
  + rewrite andb_false_r.
    assert (x / (N.to_nat m)  <> 0)%nat by lia. clear Eq1.
    rewrite Nat.div_small_iff in H1 by lia.
    rewrite Cmult_0_l.
    exfalso. lia.
Qed.

Theorem transpose_involutive : forall (m n : N) (A : Matrix m n), (A⊤)⊤ = A.
Proof. reflexivity. Qed.

Theorem adjoint_involutive : forall (m n : N) (A : Matrix m n), A†† = A.
Proof. intros. lma. Qed.  

Lemma id_transpose_eq : forall n, (I n)⊤ = (I n).
Proof.
  intros n. unfold transpose, I.
  prep_matrix_equality.
  bdestruct_all; reflexivity.
Qed.

Lemma zero_transpose_eq : forall m n, (@Zero m n)⊤ = @Zero m n.
Proof. reflexivity. Qed.


Lemma id_adjoint_eq : forall n, (I n)† = (I n).
Proof.
  intros n.
  unfold adjoint, I.
  prep_matrix_equality.
  bdestruct_all;
    try lia; lca.
Qed.

Lemma zero_adjoint_eq : forall m n, (@Zero m n)† = @Zero n m.
Proof. unfold adjoint, Zero. rewrite Cconj_0. reflexivity. Qed.

Theorem Mplus_comm : forall (m n : N) (A B : Matrix m n), A .+ B = B .+ A.
Proof. intros. lma. Qed.

Theorem Mplus_assoc : forall (m n : N) (A B C : Matrix m n), A .+ B .+ C = A .+ (B .+ C).
Proof. intros. lma. Qed.


Theorem Mmult_assoc : forall {m n o p : N} (A : Matrix m n) (B : Matrix n o) 
  (C: Matrix o p), A × B × C = A × (B × C).
Proof.
  intros m n o p A B C.
  unfold Mmult.
  prep_matrix_equality.
  induction (N.to_nat n).
  + simpl.
    clear B.
    induction (N.to_nat o). reflexivity.
    simpl. rewrite IHn0. lca.
  + simpl. 
    rewrite <- IHn0.
    simpl.
    rewrite Csum_mult_l.
    rewrite <- Csum_plus.
    apply Csum_eq.
    apply functional_extensionality. intros z.
    rewrite Cmult_plus_distr_r.
    rewrite Cmult_assoc.
    reflexivity.
Qed.

Lemma Mmult_plus_distr_l : forall (m n o : N) (A : Matrix m n) (B C : Matrix n o), 
                           A × (B .+ C) = A × B .+ A × C.
Proof. 
  intros m n o A B C.
  unfold Mplus, Mmult.
  prep_matrix_equality.
  rewrite <- Csum_plus.
  apply Csum_eq.
  apply functional_extensionality. intros z.
  rewrite Cmult_plus_distr_l. 
  reflexivity.
Qed.

Lemma Mmult_plus_distr_r : forall (m n o : N) (A B : Matrix m n) (C : Matrix n o), 
                           (A .+ B) × C = A × C .+ B × C.
Proof. 
  intros m n o A B C.
  unfold Mplus, Mmult.
  prep_matrix_equality.
  rewrite <- Csum_plus.
  apply Csum_eq.
  apply functional_extensionality. intros z.
  rewrite Cmult_plus_distr_r. 
  reflexivity.
Qed.

Lemma kron_plus_distr_l : forall (m n o p : N) (A : Matrix m n) (B C : Matrix o p), 
                           A ⊗ (B .+ C) = A ⊗ B .+ A ⊗ C.
Proof. 
  intros m n o p A B C.
  unfold Mplus, kron.
  prep_matrix_equality.
  rewrite Cmult_plus_distr_l.
  easy.
Qed.

Lemma kron_plus_distr_r : forall (m n o p : N) (A B : Matrix m n) (C : Matrix o p), 
                           (A .+ B) ⊗ C = A ⊗ C .+ B ⊗ C.
Proof. 
  intros m n o p A B C.
  unfold Mplus, kron.
  prep_matrix_equality.
  rewrite Cmult_plus_distr_r. 
  reflexivity.
Qed.

Lemma Mscale_0_l : forall (m n : N) (A : Matrix m n), C0 .* A = Zero.
Proof.
  intros m n A.
  prep_matrix_equality.
  unfold Zero, scale.
  rewrite Cmult_0_l.
  reflexivity.
Qed.

Lemma Mscale_0_r : forall (m n : N) (c : C), c .* @Zero m n = Zero.
Proof.
  intros m n c.
  prep_matrix_equality.
  unfold Zero, scale.
  rewrite Cmult_0_r.
  reflexivity.
Qed.

Lemma Mscale_1_l : forall (m n : N) (A : Matrix m n), C1 .* A = A.
Proof.
  intros m n A.
  prep_matrix_equality.
  unfold scale.
  rewrite Cmult_1_l.
  reflexivity.
Qed.

Lemma Mscale_1_r : forall (n : N) (c : C),
    c .* I n = fun x y => if (x =? y) && (x <? (N.to_nat n)) then c else C0.
Proof.
  intros n c.
  prep_matrix_equality.
  unfold scale, I.
  destruct ((x =? y) && (x <? (N.to_nat n))).
  rewrite Cmult_1_r; reflexivity.
  rewrite Cmult_0_r; reflexivity.
Qed.

Lemma Mscale_assoc : forall (m n : N) (x y : C) (A : Matrix m n),
  x .* (y .* A) = (x * y) .* A.
Proof.
  intros. unfold scale. prep_matrix_equality.
  rewrite Cmult_assoc; reflexivity.
Qed.

Lemma Mscale_plus_distr_l : forall (m n : N) (x y : C) (A : Matrix m n),
  (x + y) .* A = x .* A .+ y .* A.
Proof.
  intros. unfold Mplus, scale.
(*   unfold mat_equiv.
  intros .apply Cmult_plus_distr_r *)
  prep_matrix_equality. apply Cmult_plus_distr_r.
Qed.

Lemma Mscale_plus_distr_r : forall (m n : N) (x : C) (A B : Matrix m n),
  x .* (A .+ B) = x .* A .+ x .* B.
Proof.
  intros. unfold Mplus, scale. prep_matrix_equality. apply Cmult_plus_distr_l.
Qed.

Lemma Mscale_mult_dist_l : forall (m n o : N) (x : C) (A : Matrix m n) (B : Matrix n o), 
    ((x .* A) × B) = x .* (A × B).
Proof.
  intros m n o x A B.
  unfold scale, Mmult.
  prep_matrix_equality.
  rewrite Csum_mult_l.
  apply Csum_eq.
  apply functional_extensionality. intros z.
  rewrite Cmult_assoc.
  reflexivity.
Qed.

Lemma Mscale_mult_dist_r : forall (m n o : N) (x : C) (A : Matrix m n) (B : Matrix n o),
    (A × (x .* B)) = x .* (A × B).
Proof.
  intros m n o x A B.
  unfold scale, Mmult.
  prep_matrix_equality.
  rewrite Csum_mult_l.
  apply Csum_eq.
  apply functional_extensionality. intros z.
  repeat rewrite Cmult_assoc.
  rewrite (Cmult_comm _ x).
  reflexivity.
Qed.

Lemma Mscale_kron_dist_l : forall (m n o p : N) (x : C) (A : Matrix m n) (B : Matrix o p), 
    ((x .* A) ⊗ B) = x .* (A ⊗ B).
Proof.
  intros m n o p x A B.
  unfold scale, kron.
  prep_matrix_equality.
  rewrite Cmult_assoc.
  reflexivity.
Qed.

Lemma Mscale_kron_dist_r : forall (m n o p : N) (x : C) (A : Matrix m n) (B : Matrix o p), 
    (A ⊗ (x .* B)) = x .* (A ⊗ B).
Proof.
  intros m n o p x A B.
  unfold scale, kron.
  prep_matrix_equality.
  rewrite Cmult_assoc.  
  rewrite (Cmult_comm (A _ _) x).
  rewrite Cmult_assoc.  
  reflexivity.
Qed.

Lemma Mscale_trans : forall (m n : N) (x : C) (A : Matrix m n),
    (x .* A)⊤ = x .* A⊤.
Proof. reflexivity. Qed.

Lemma Mscale_adj : forall (m n : N) (x : C) (A : Matrix m n),
    (x .* A)† = x^* .* A†.
Proof.
  intros m n x A.
  unfold scale, adjoint.
  prep_matrix_equality.
  rewrite Cconj_mult_distr.
  reflexivity.
Qed.

Local Open Scope nat_scope.

Instance Scale_proper(m n : N): Proper (eq ==> mat_equiv ==> mat_equiv) (@scale m n).
Proof.
hnf;intros k1 k2 H1.
hnf;intros A B H2.
unfold mat_equiv,scale,get in *.
intros. rewrite H1,H2. reflexivity.
Qed. 

Instance Mplus_proper(m n : N): Proper (mat_equiv ==> mat_equiv ==> mat_equiv) (@Mplus m n).
Proof.
hnf;intros A C H1.
hnf;intros B D H2.
unfold mat_equiv,Mplus,get in *.
intros. rewrite H1,H2. reflexivity.
Qed. 


Instance mult_proper(m n o : N): Proper (mat_equiv ==> mat_equiv ==> mat_equiv) (@Mmult m n o).
Proof.
hnf;intros A C H1.
hnf;intros B D H2.
unfold mat_equiv,Mmult,get in * .
intros.
    bdestruct ((N.to_nat m) =? 0). destruct x. exfalso. lia.
    bdestruct ((N.to_nat o) =? 0). destruct y. exfalso. lia.
destruct x as [x Px], y as [y Py].
simpl.
apply Csum_eq_bounded.
intros z Pz.
specialize (H1 (exist _ x Px) (exist _ z Pz)).
specialize (H2 (exist _ z Pz) (exist _ y Py)).
simpl in H1.
simpl in H2.
rewrite H1.
rewrite H2.
auto.
Qed.



Instance kron_proper(m n o p : N): Proper (mat_equiv ==> mat_equiv ==> mat_equiv) (@kron m n o p ).
Proof.
hnf;intros A C H1.
hnf;intros B D H2.
unfold mat_equiv,kron,get in *.
intros.
    bdestruct ((N.to_nat m) =? 0). destruct x. exfalso. rewrite Nnat.N2Nat.inj_mul in l. rewrite H in l. lia.
    bdestruct ((N.to_nat o) =? 0). destruct x. exfalso. rewrite Nnat.N2Nat.inj_mul in l. rewrite H0 in l. lia.
    bdestruct ((N.to_nat n) =? 0). destruct y. exfalso. rewrite Nnat.N2Nat.inj_mul in l. rewrite H3 in l. lia.
    bdestruct ((N.to_nat p) =? 0). destruct y. exfalso. rewrite Nnat.N2Nat.inj_mul in l. rewrite H4 in l. lia.
destruct x as [x Px], y as [y Py].
simpl.
pose proof Nat.div_lt_upper_bound x (N.to_nat o) (N.to_nat m) H0 ltac:(nia).
pose proof Nat.div_lt_upper_bound y (N.to_nat p) (N.to_nat n) H4 ltac:(nia).
specialize (H1 (exist _ (x/(N.to_nat o)) H5) (exist _ (y/(N.to_nat p)) H6)).
pose proof Nat.mod_upper_bound x (N.to_nat o) H0.
pose proof Nat.mod_upper_bound y (N.to_nat p) H4.
specialize (H2 (exist _ (x mod (N.to_nat o)) H7) (exist _ (y mod (N.to_nat p)) H8)).
simpl in H1.
simpl in H2.
rewrite H1.
rewrite H2.
auto.
Qed.

Instance adjoint_proper(m n : N) : Proper (mat_equiv ==> mat_equiv) (@adjoint m n).
Proof.
hnf;intros A C H1.
unfold mat_equiv,adjoint,get in *.
intros. rewrite H1. reflexivity.
Qed. 


(* Inverses of square matrices *)
Definition Minv {n : N} (A B : Square n) : Prop := A × B ≡ I n /\ B × A ≡ I n.
Lemma Minv_unique : forall (n : N) (A B C : Square n), 
                      Minv A B -> Minv A C -> B ≡ C.
Proof.
  intros n A B C [HAB HBA] [HAC HCA].
  rewrite <- Mmult_1_r.
  rewrite <- HAC.
  rewrite <- (Mmult_1_l n n C) at 2.
  rewrite <- HBA.
  rewrite Mmult_assoc.
  reflexivity.
Qed.

Lemma Minv_symm : forall (n : N) (A B : Square n), Minv A B -> Minv B A.
Proof. unfold Minv; intuition. Qed.


Local Open Scope nat_scope.

Lemma kron_assoc : forall {m n p q r s : N}
  (A : Matrix m n) (B : Matrix p q) (C : Matrix r s),
  (A ⊗ B ⊗ C) ≡ (A ⊗ (B ⊗ C):  Matrix (m*p*r)(n*q*s)).
Proof.
  intros.
  intros [i Hi] [j Hj]; unfold get; simpl.
  unfold kron; simpl.
  rewrite !Cmult_assoc.
  assert ((N.to_nat m) <> 0) by (intro; subst; lia).
  assert ((N.to_nat n) <> 0) by (intro; subst; lia).
  assert ((N.to_nat p) <> 0) by (intro; subst; lia).
  assert ((N.to_nat q) <> 0) by (intro; subst; lia).
  assert ((N.to_nat r) <> 0) by (intro; subst; lia).
  assert ((N.to_nat s) <> 0) by (intro; subst; lia).
  f_equal; [f_equal |]; f_equal.
  + rewrite Nat.div_div by auto.
    rewrite Nat.mul_comm. rewrite Nnat.N2Nat.inj_mul.  auto.
  + rewrite Nat.div_div by auto.
    rewrite Nat.mul_comm; rewrite Nnat.N2Nat.inj_mul.  auto.
  + rewrite Nnat.N2Nat.inj_mul.
    rewrite Nat.mul_comm.
    rewrite Nat.mod_mul_r by auto.
    rewrite Nat.mul_comm.
    rewrite Nat.div_add by auto.
    pose proof Nat.mod_upper_bound i (N.to_nat r) ltac:(auto).
    rewrite (Nat.div_small (i mod (N.to_nat r)) (N.to_nat r)) by auto.
    lia.
  + rewrite Nnat.N2Nat.inj_mul.
    rewrite Nat.mul_comm.
    rewrite Nat.mod_mul_r by auto.
    rewrite Nat.mul_comm.
    rewrite Nat.div_add by auto.
    pose proof Nat.mod_upper_bound j (N.to_nat s) ltac:(auto).
    rewrite (Nat.div_small (j mod (N.to_nat s)) (N.to_nat s)) by auto.
    lia.
  + rewrite Nnat.N2Nat.inj_mul.
    rewrite Nat.mul_comm.
    rewrite Nat.mod_mul_r by auto.
    rewrite Nat.mul_comm.
    rewrite Nat.mod_add by auto.
    rewrite Nat.mod_mod by auto.
    auto.
  + rewrite Nnat.N2Nat.inj_mul.
    rewrite Nat.mul_comm.
    rewrite Nat.mod_mul_r by auto.
    rewrite Nat.mul_comm.
    rewrite Nat.mod_add by auto.
    rewrite Nat.mod_mod by auto.
    auto.
Qed.
  
Lemma kron_mixed_product : forall {m n o p q r : N} (A : Matrix m n) (B : Matrix p q ) 
  (C : Matrix n o) (D : Matrix q r), (A ⊗ B) × (C ⊗ D) = (A × C) ⊗ (B × D).
Proof.
  intros m n o p q r A B C D.
  unfold kron, Mmult.
  prep_matrix_equality.
  rewrite Nnat.N2Nat.inj_mul.
  destruct (N.to_nat q).
  + rewrite mult_0_r.
    simpl.
    rewrite Cmult_0_r.
    reflexivity. 
  + rewrite Csum_product.
    apply Csum_eq.
    apply functional_extensionality.
    intros; lca.
    lia.
Qed.

Lemma Mplus_tranpose : forall (m n : N) (A : Matrix m n) (B : Matrix m n),
  (A .+ B)⊤ = A⊤ .+ B⊤.
Proof. reflexivity. Qed.

Lemma Mmult_tranpose : forall (m n o : N) (A : Matrix m n) (B : Matrix n o),
      (A × B)⊤ = B⊤ × A⊤.
Proof.
  intros m n o A B.
  unfold Mmult, transpose.
  prep_matrix_equality.
  apply Csum_eq.  
  apply functional_extensionality. intros z.
  rewrite Cmult_comm.
  reflexivity.
Qed.

Lemma kron_transpose : forall (m n o p : N) (A : Matrix m n) (B : Matrix o p ),
  (A ⊗ B)⊤ = A⊤ ⊗ B⊤.
Proof. reflexivity. Qed.


Lemma Mplus_adjoint : forall (m n : N) (A : Matrix m n) (B : Matrix m n),
  (A .+ B)† = A† .+ B†.
Proof.  
  intros m n A B.
  unfold Mplus, adjoint.
  prep_matrix_equality.
  rewrite Cconj_plus_distr.
  reflexivity.
Qed.

Lemma Mmult_adjoint : forall {m n o : N} (A : Matrix m n) (B : Matrix n o),
      (A × B)† = B† × A†.
Proof.
  intros m n o A B.
  unfold Mmult, adjoint.
  prep_matrix_equality.
  rewrite Csum_conj_distr.
  apply Csum_eq.  
  apply functional_extensionality. intros z.
  rewrite Cconj_mult_distr.
  rewrite Cmult_comm.
  reflexivity.
Qed.

Lemma kron_adjoint : forall {m n o p : N} (A : Matrix m n) (B : Matrix o p),
  (A ⊗ B)† = A† ⊗ B†.
Proof. 
  intros. unfold adjoint, kron. 
  prep_matrix_equality.
  rewrite Cconj_mult_distr.
  reflexivity.
Qed.

Lemma id_kron : forall (m n : N),  I m ⊗ I n = I (m * n).
Proof.
  intros.
  unfold I, kron.
  prep_matrix_equality.
  rewrite Nnat.N2Nat.inj_mul.
  bdestruct (x =? y); rename H into Eq; subst.
  + repeat rewrite <- beq_nat_refl; simpl.
    destruct (N.to_nat n).
    - simpl.
      rewrite mult_0_r.
      bdestruct (y <? 0); try lia.
      autorewrite with C_db; reflexivity.
    - bdestruct (y mod S n0 <? S n0). 
      2: specialize (Nat.mod_upper_bound y (S n0)); intros; lia. 
      rewrite Cmult_1_r.
      destruct (y / S n0 <? (N.to_nat m)) eqn:L1, (y <? (N.to_nat m) * S n0) eqn:L2; trivial.
      * apply Nat.ltb_lt in L1. 
        apply Nat.ltb_nlt in L2. 
        contradict L2. 
        (* Why doesn't this lemma exist??? *)
        destruct (N.to_nat m).
        lia.
        apply Nat.div_small_iff.
        simpl. apply Nat.neq_succ_0. 
        apply Nat.div_small in L1.
        rewrite Nat.div_div in L1; try lia.
        rewrite mult_comm.
        assumption.
      * apply Nat.ltb_nlt in L1. 
        apply Nat.ltb_lt in L2. 
        contradict L1. 
        apply Nat.div_lt_upper_bound. lia.
        rewrite mult_comm.
        assumption.
  + simpl.
    bdestruct (x / (N.to_nat n) =? y / (N.to_nat n)); simpl; try lca.
    bdestruct (x mod (N.to_nat n) =? y mod (N.to_nat n)); simpl; try lca.
    destruct (N.to_nat n); try lca.
    contradict Eq.
    rewrite (Nat.div_mod x (S n0)) by lia.
    rewrite (Nat.div_mod y (S n0)) by lia.
    rewrite H, H0; reflexivity.
Qed.

Lemma outer_product_eq : forall m (φ ψ : Matrix m 1),
 φ = ψ -> outer_product φ φ = outer_product ψ ψ.
Proof. congruence. Qed.

Lemma outer_product_kron : forall m n (φ : Matrix m 1) (ψ : Matrix n 1), 
    outer_product φ φ ⊗ outer_product ψ ψ = outer_product (φ ⊗ ψ) (φ ⊗ ψ).
Proof. 
  intros. unfold outer_product. 
  specialize (kron_adjoint φ ψ) as KT. 
  simpl in *. rewrite KT.
  specialize (kron_mixed_product φ ψ (φ†) (ψ†)) as KM. 
  simpl in *. rewrite KM.
  reflexivity.
Qed.