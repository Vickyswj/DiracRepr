Require Import Psatz.
Require Import String.
Require Import Program.
Require Export Complex.
Require Import BinNat.
Require Import List.
Require Coq.Setoids.Setoid.
Require Import Coq.Classes.Morphisms.

Require M_notWF.
Module M := M_notWF.


Declare Scope matrix_scope.
Delimit Scope matrix_scope with M.
Open Scope matrix_scope.
Local Open Scope N_scope.

Definition Matrix (m n : N) := N -> N -> C.
Print M.Matrix.
Print Matrix.


Definition M2MM {n m} (A : Matrix n m) : M.Matrix (N.to_nat n) (N.to_nat m) :=
fun x y => A (N.of_nat x) (N.of_nat y).

Definition MM2M {n m} (A : M.Matrix n m) : Matrix (N.of_nat n) (N.of_nat m) :=
fun x y => A (N.to_nat x) (N.to_nat y).

Notation Vector n := (Matrix n 1).

Notation Square n := (Matrix n n).

(* Showing equality via functional extensionality *)
Ltac prep_matrix_equality :=
  let x := fresh "x" in 
  let y := fresh "y" in 
  apply functional_extensionality; intros x;
  apply functional_extensionality; intros y.

Lemma idM {n m} (A : Matrix n m) : MM2M (M2MM A) = A.
Proof.
unfold M2MM,MM2M.
prep_matrix_equality.
repeat rewrite Nnat.N2Nat.id.
reflexivity.
Qed.

Lemma idMM {n m} (A : M.Matrix n m) : M2MM (MM2M A) = A.
Proof.
unfold M2MM,MM2M.
prep_matrix_equality.
repeat rewrite Nnat.Nat2N.id.
reflexivity.
Qed.

(* Matrix Equivalence *)
Definition get {m n} (A : Matrix m n) (a : N | a < m) (b : N | b < n) := 
M.get (M2MM A).

Definition mat_equiv {m n : N} (A B : Matrix m n) : Prop := 
  forall (x : N | x < m) (y : N | y < n), get A x y = get B x y.

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
Fixpoint print_row {m n} (i j : N) (A : Matrix m n) : string :=
M.print_row (N.to_nat i) (N.to_nat j) (M2MM A).

Fixpoint print_rows {m n} (i j : N) (A : Matrix m n) : string :=
M.print_rows (N.to_nat i) (N.to_nat j) (M2MM A).

Definition print_matrix {m n} (A : Matrix m n) : string :=
M.print_matrix (M2MM A).

(*****************************)
(** Operands and Operations **)
(*****************************)
Check M.Zero.
Definition Zero {m n : N} : Matrix m n :=
 fun x y => 0%R.

Definition I (n : N) : Square n := 
MM2M (M.I (N.to_nat n)).
 (*  (fun x y => if (x =? y) && (x <? n) then C1 else C0). *)

(* Optional coercion to scalar (should be limited to 1 × 1 matrices):
Definition to_scalar (m n : nat) (A: Matrix m n) : C := A 0 0.

Coercion to_scalar : Matrix >-> C.
 *)


  (*
Definition I (n : nat) : Square n := 
  (fun x y => if (x =? y) && (x <? n) then C1 else C0).
Definition I1 := I (2^0).
Notation "I  n" := (I n) (at level 10).
*)

(* This isn't used, but is interesting *)
Definition I__inf := fun x y => if x =? y then C1 else C0.
Notation "I∞" := I__inf : matrix_scope.


(* sum to n exclusive *)
(* Fixpoint Csum (f : nat -> C) (n : N) : C := 
 M.Csum f (N.to_nat n).    Lemma sums will be wrong *)
Fixpoint Csum (f : nat -> C) (n : nat) : C := 
  match n with
  | 0%nat => C0
  | S n' => (Csum f n' +  f n')%C
  end.

Definition trace {n : N} (A : Square n) := 
M.trace (M2MM A).

Definition scale {m n : N} (r : C) (A : Matrix m n) : Matrix m n :=
MM2M (M.scale r (M2MM A)).
(*   fun x y => (r * A x y)%C. *)

Definition dot {n : N} (A : Vector n) (B : Vector n) : C :=
M.dot (M2MM A) (M2MM B).
(*   Csum (fun x => A (N.of_nat x) 0  * B (N.of_nat x) 0)%C n. *)

Definition Mplus {m n : N} (A B : Matrix m n) : Matrix m n :=
MM2M (M.Mplus (M2MM A) (M2MM B)).
(*   fun x y => (A x y + B x y)%C. *)

Definition Mmult {m n o : N} (A : Matrix m n) (B : Matrix n o) : Matrix m o :=
MM2M (M.Mmult (M2MM A) (M2MM B)).
(*   fun x z => Csum (fun y => A x (N.of_nat y) * B (N.of_nat y) z)%C n. *)

(* Only well-defined when o and p are non-zero *)
Definition kron {m n o p : N} (A : Matrix m n) (B : Matrix o p) : Matrix (m*o) (n*p) :=
MM2M (M.kron (M2MM A) (M2MM B)).
(*   fun x y => Cmult (A (x / o) (y / p)) (B (x mod o) (y mod p)). *)

Definition transpose {m n} (A : Matrix m n) : Matrix n m :=
MM2M (M.transpose (M2MM A)).
(*   fun x y => A y x. *)

Definition adjoint {m n} (A : Matrix m n) : Matrix n m :=
MM2M (M.adjoint (M2MM A)).
(*   fun x y => (A y x)^*. *)

Definition inner_product {n} (u v : Vector n) : C :=
M.inner_product (M2MM u) (M2MM v).
(*   Mmult (adjoint u) (v) 0 0. *)

Definition outer_product {n} (u v : Vector n) : Square n :=
MM2M (M.outer_product (M2MM u) (M2MM v)).
(*   Mmult u (adjoint v). *)

(* Kronecker of n copies of A *)
Fixpoint kron_n n {m1 m2} (A : Matrix m1 m2) : Matrix (m1^n) (m2^n) :=
MM2M (M.kron_n (N.to_nat n) (M2MM A)).
(*   match n with
  | 0    => I 1
  | S n' => kron A (kron_n n' A)
  end. *)

(* Kronecker product of a list *)
(* Fixpoint big_kron {m n} (As : list (Matrix m n)) : 
  Matrix (m^(N.of_nat (length As))) (n^(N.of_nat (length As))) := 
  match As with
  | [] => I 1
  | A :: As' => kron A (big_kron As')
  end. *)

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
(* Notation "⨂ A" := (big_kron A) (at level 60): matrix_scope. *)
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
                 | 0%nat   => _
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

Local Close Scope N_scope.

Lemma Csum_0 : forall f (n:nat), (forall x, f x = C0) -> Csum f n = 0. 
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
Lemma Zero_l :forall (n : N) (A : Matrix 0 n),  A ≡ Zero.
Proof.
  intros n A.
  unfold mat_equiv,Zero,get.
  intros.
  destruct x. exfalso. lia.
Qed.

Lemma Zero_r :forall (n : N) (A : Matrix n 0), A ≡ Zero.
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


(* Lemma rr5 : forall (n m : N) (A B : Matrix n m), MM2M (M2MM A) .+ MM2M (M2MM B) = MM2M (M.Mplus (M2MM A) (M2MM B)) .
Proof.
intros.
unfold Mplus.
repeat rewrite Nnat.N2Nat.id.
repeat rewrite idM.
auto.
Qed. *)

Lemma rr6 : forall (n m : N) (A B : Matrix n m), M.Mplus (M2MM A)  (M2MM B) = M2MM (A .+ B) .
Proof.
intros.
unfold Mplus.
replace (@M2MM n m (@MM2M (N.to_nat n) (N.to_nat m) 
        (@M.Mplus (N.to_nat n) (N.to_nat m) (@M2MM n m A) (@M2MM n m B)))) with
(@M2MM (N.of_nat(N.to_nat n)) (N.of_nat(N.to_nat m)) 
        (@MM2M (N.to_nat n) (N.to_nat m) 
                (@M.Mplus (N.to_nat n) (N.to_nat m) (@M2MM n m A) (@M2MM n m B))))
                        by (repeat rewrite Nnat.N2Nat.id; auto).
rewrite idMM. auto.
Qed.


Lemma trace_plus_dist : forall (n : N) (A B : Square n), 
    trace (A .+ B) = (trace A + trace B)%C. 
Proof.
intros.
unfold trace,Mplus.
rewrite rr6.
replace (@M.trace (N.to_nat n) (@M2MM n n 
        (@MM2M (N.to_nat n) (N.to_nat n) (@M2MM n n (A .+ B)))))with
(@M.trace (N.to_nat n) (@M2MM (N.of_nat(N.to_nat n)) (N.of_nat(N.to_nat n))
        (@MM2M (N.to_nat n) (N.to_nat n) (@M2MM n n (A .+ B)))))
                        by (repeat rewrite Nnat.N2Nat.id; auto).
rewrite idMM.
rewrite <- rr6.
rewrite M.trace_plus_dist.
auto.
Qed.

Lemma Mplus_0_l : forall (m n : N) (A : Matrix m n), Zero .+ A = A.
Proof.
intros.
unfold Mplus.
rewrite M.Mplus_0_l.
rewrite idM.
auto.
Qed.

Lemma Mplus_0_r : forall (m n : N) (A : Matrix m n), A .+ Zero = A.
Proof.
intros.
unfold Mplus.
rewrite M.Mplus_0_r.
rewrite idM.
auto.
Qed.

Lemma Mmult_0_l : forall (m n o : N) (A : Matrix n o), @Zero m n × A = Zero.
Proof.
intros. 
unfold Mmult. 
rewrite M.Mmult_0_l.
auto.
Qed.

Lemma Mmult_0_r : forall (m n o : N) (A : Matrix m n), A × @Zero n o = Zero.
Proof.
intros. 
unfold Mmult. 
rewrite M.Mmult_0_r.
auto.
Qed.

(* using <= because our form Csum is exclusive. *)

Lemma tt : forall n, 
exists a,
N.to_nat n = a.
Proof.
intros.
exists (N.to_nat n). auto.
Qed.

Lemma Mmult_1_l : forall (m n : N) (A : Matrix m n), I m × A ≡ A.
Proof.
intros.
unfold Mmult.
unfold mat_equiv,get.
intros.
prep_matrix_equality.
unfold I.
replace (@M.get (N.to_nat m) (N.to_nat n)
  (@M2MM m n (@MM2M (N.to_nat m) (N.to_nat n)
    (@M.Mmult (N.to_nat m) (N.to_nat m) (N.to_nat n)
      (@M2MM m m (@MM2M (N.to_nat m) (N.to_nat m) (M.I (N.to_nat m))))
        (@M2MM m n A)))) x0 y0) 
with (@M.get (N.to_nat m) (N.to_nat n)
    (@M2MM (N.of_nat(N.to_nat m)) (N.of_nat(N.to_nat n)) (@MM2M (N.to_nat m) (N.to_nat n)
      (@M.Mmult (N.to_nat m) (N.to_nat m) (N.to_nat n)
        (@M2MM (N.of_nat(N.to_nat m)) (N.of_nat(N.to_nat m)) (@MM2M (N.to_nat m) (N.to_nat m) (M.I (N.to_nat m))))
          (@M2MM m n A)))) x0 y0) 
            by (repeat rewrite Nnat.N2Nat.id; auto).
repeat rewrite idMM.
rewrite M.Mmult_1_l.
auto.
Qed.

Lemma Mmult_1_r : forall (m n : N) (A : Matrix m n), A × I n ≡ A.
Proof.
intros.
unfold Mmult.
unfold mat_equiv,get.
intros.
prep_matrix_equality.
unfold I.
replace (@M.get (N.to_nat m) (N.to_nat n)
  (@M2MM m n (@MM2M (N.to_nat m) (N.to_nat n)
    (@M.Mmult (N.to_nat m) (N.to_nat n) (N.to_nat n)
      (@M2MM m n A)
        (@M2MM n n (@MM2M (N.to_nat n) (N.to_nat n) (M.I (N.to_nat n))))))) x0 y0) 
with (@M.get (N.to_nat m) (N.to_nat n)
  (@M2MM (N.of_nat(N.to_nat m)) (N.of_nat(N.to_nat n)) (@MM2M (N.to_nat m) (N.to_nat n)
    (@M.Mmult (N.to_nat m) (N.to_nat n) (N.to_nat n)
      (@M2MM m n A)
        (@M2MM (N.of_nat(N.to_nat n)) (N.of_nat(N.to_nat n)) (@MM2M (N.to_nat n) (N.to_nat n) (M.I (N.to_nat n))))))) x0 y0)
            by (repeat rewrite Nnat.N2Nat.id; auto).
repeat rewrite idMM.
rewrite M.Mmult_1_r.
auto.
Qed.

Lemma kron_0_l : forall (m n o p : N) (A : Matrix o p), 
  @Zero m n ⊗ A = Zero.
Proof.
  intros.
  unfold kron.
  rewrite M.kron_0_l.
  auto.
Qed.

Lemma kron_0_r : forall (m n o p : N) (A : Matrix m n), 
   A ⊗ @Zero o p = Zero.
Proof.
  intros.
  unfold kron.
  rewrite M.kron_0_r.
  auto.
Qed.
Lemma rr :  N.to_nat 1=1%nat .
Proof. auto. Qed.
(* Lemma rr1 : forall n: N, (N.to_nat n * N.to_nat 1)%nat=N.to_nat n .
Proof.
rewrite rr.
 rewrite mult_1_r.

Qed. *)


Lemma kron_1_r : forall (m n : N) (A : Matrix m n), A ⊗ I 1 = A.
Proof.
  intros.
  unfold kron. 
  unfold I.
  replace  (@M2MM 1 1 (@MM2M (N.to_nat 1) (N.to_nat 1) (M.I (N.to_nat 1)))) with
    (@M2MM (N.of_nat(N.to_nat 1)) (N.of_nat(N.to_nat 1)) (@MM2M (N.to_nat 1) (N.to_nat 1) (M.I (N.to_nat 1))))
      by (repeat rewrite Nnat.N2Nat.id; auto).
  rewrite (idMM (M.I (N.to_nat 1))).
  rewrite M.kron_1_r.
(* Print Nnat.N2Nat.inj_mul. *)
  repeat rewrite mult_1_r.
  rewrite idM.
  auto.
Qed.

(* This side is more limited *)
Lemma kron_1_l : forall (m n : N) (A : Matrix m n), I 1 ⊗ A ≡ A.
Proof.
  intros.
  unfold kron.
  unfold mat_equiv,get.
intros.
unfold I.
    replace  (@M.get (N.to_nat (1 * m)) (N.to_nat (1 * n))
  (@M2MM (1 * m) (1 * n)
     (@MM2M (N.to_nat 1 * N.to_nat m) (N.to_nat 1 * N.to_nat n)
        (@M.kron (N.to_nat 1) (N.to_nat 1) (N.to_nat m) (N.to_nat n)
           (@M2MM 1 1 (@MM2M (N.to_nat 1) (N.to_nat 1) (M.I (N.to_nat 1)))) 
           (@M2MM m n A))))) 
with (@M.get (N.to_nat (1 * m)) (N.to_nat (1 * n))
  (@M2MM (N.of_nat (N.to_nat 1 * N.to_nat m)) (N.of_nat (N.to_nat 1 * N.to_nat n))
     (@MM2M (N.to_nat 1 * N.to_nat m) (N.to_nat 1 * N.to_nat n)
        (@M.kron (N.to_nat 1) (N.to_nat 1) (N.to_nat m) (N.to_nat n)
           (@M2MM (N.of_nat(N.to_nat 1))  (N.of_nat(N.to_nat 1)) (@MM2M (N.to_nat 1) (N.to_nat 1) (M.I (N.to_nat 1)))) 
           (@M2MM m n A)))))
      by (repeat rewrite Nnat.N2Nat.id; auto).
repeat rewrite idMM.
replace (N.to_nat (1 * m)) with ((N.to_nat 1) * (N.to_nat m))%nat by (rewrite Nnat.N2Nat.inj_mul;auto).
replace (N.to_nat (1 * n)) with ((N.to_nat 1) * (N.to_nat n))%nat by (rewrite Nnat.N2Nat.inj_mul;auto).
rewrite rr.
prep_matrix_equality.
rewrite M.kron_1_l.
auto.
Qed.

Theorem transpose_involutive : forall (m n : N) (A : Matrix m n), (A⊤)⊤ = A.
Proof. 
intros.
unfold transpose. 
replace (@MM2M (N.to_nat m) (N.to_nat n)
  (@M.transpose (N.to_nat n) (N.to_nat m)
     (@M2MM n m
        (@MM2M (N.to_nat n) (N.to_nat m)
           (@M.transpose (N.to_nat m) (N.to_nat n)
              (@M2MM m n A)))))) 
with (@MM2M (N.to_nat m) (N.to_nat n)
  (@M.transpose (N.to_nat n) (N.to_nat m)
     (@M2MM (N.of_nat (N.to_nat n)) (N.of_nat (N.to_nat m))
        (@MM2M (N.to_nat n) (N.to_nat m)
           (@M.transpose (N.to_nat m) (N.to_nat n)
              (@M2MM m n A))))))
      by (repeat rewrite Nnat.N2Nat.id; auto).
repeat rewrite idMM.
rewrite M.transpose_involutive. 
rewrite idM. 
auto.
Qed.


Theorem adjoint_involutive : forall (m n : N) (A : Matrix m n), A†† = A.
Proof.
intros.
unfold adjoint. 
replace (@MM2M (N.to_nat m) (N.to_nat n)
  (@M.adjoint (N.to_nat n) (N.to_nat m)
     (@M2MM n m
        (@MM2M (N.to_nat n) (N.to_nat m)
           (@M.adjoint (N.to_nat m) (N.to_nat n)
              (@M2MM m n A))))))
with (@MM2M (N.to_nat m) (N.to_nat n)
  (@M.adjoint (N.to_nat n) (N.to_nat m)
     (@M2MM (N.of_nat (N.to_nat n)) (N.of_nat (N.to_nat m))
        (@MM2M (N.to_nat n) (N.to_nat m)
           (@M.adjoint (N.to_nat m) (N.to_nat n)
              (@M2MM m n A))))))
      by (repeat rewrite Nnat.N2Nat.id; auto).
repeat rewrite idMM.
rewrite M.adjoint_involutive. 
rewrite idM. 
auto.
Qed.

Lemma id_transpose_eq : forall n, (I n)⊤ = (I n).
Proof.
  intros n. unfold transpose, I.
replace (@MM2M (N.to_nat n) (N.to_nat n)
  (@M.transpose (N.to_nat n) (N.to_nat n)
     (@M2MM n n
        (@MM2M (N.to_nat n) (N.to_nat n) (M.I (N.to_nat n))))))
with (@MM2M (N.to_nat n) (N.to_nat n)
  (@M.transpose (N.to_nat n) (N.to_nat n)
     (@M2MM (N.of_nat (N.to_nat n)) (N.of_nat (N.to_nat n))
        (@MM2M (N.to_nat n) (N.to_nat n) (M.I (N.to_nat n))))))
      by (repeat rewrite Nnat.N2Nat.id; auto).
repeat rewrite idMM.
rewrite M.id_transpose_eq.
auto.
Qed.

Lemma zero_transpose_eq : forall m n, (@Zero m n)⊤ = @Zero m n.
Proof. reflexivity. Qed.


Lemma id_adjoint_eq : forall n, (I n)† = (I n).
Proof.
  intros n. unfold adjoint, I.
replace (@MM2M (N.to_nat n) (N.to_nat n)
  (@M.adjoint (N.to_nat n) (N.to_nat n)
     (@M2MM n n
        (@MM2M (N.to_nat n) (N.to_nat n) (M.I (N.to_nat n))))))
with (@MM2M (N.to_nat n) (N.to_nat n)
  (@M.adjoint (N.to_nat n) (N.to_nat n)
     (@M2MM (N.of_nat (N.to_nat n)) (N.of_nat (N.to_nat n))
        (@MM2M (N.to_nat n) (N.to_nat n) (M.I (N.to_nat n))))))
      by (repeat rewrite Nnat.N2Nat.id; auto).
repeat rewrite idMM.
rewrite M.id_adjoint_eq.
auto.
Qed.

Lemma zero_adjoint_eq : forall m n, (@Zero m n)† = @Zero n m.
Proof. intros. lma. Qed.
(* unfold adjoint, Zero.
replace (@MM2M (N.to_nat n) (N.to_nat m)
  (@M.adjoint (N.to_nat m) (N.to_nat n)
     (@M2MM m n (fun _ _ : N => 0)))) with  (fun _ _ : N => 0 ^*  ) by auto.
 rewrite Cconj_0. reflexivity. Qed. *)

Theorem Mplus_comm : forall (m n : N) (A B : Matrix m n), A .+ B = B .+ A.
Proof. intros. lma. Qed.


Lemma rr7 : forall (m n : nat) (A B : M.Matrix n m), MM2M A .+ MM2M B = MM2M (M.Mplus A B).
Proof.
intros.
unfold Mplus.
repeat rewrite idMM.
repeat rewrite Nnat.Nat2N.id.
auto.
Qed.

(* Lemma rr8 : forall (m n : N) (A B: Matrix m n),  MM2M (M2MM A) .+ MM2M (M2MM B) = MM2M (M.Mplus (M2MM A) (M2MM B)) .
Proof.
intros.
rewrite rr7.
auto.
Qed. *)

Theorem Mplus_assoc : forall {m n : N} (A B C : Matrix m n), A .+ B .+ C = A .+ (B .+ C).
Proof.
intros.
replace A with (MM2M (M2MM A)) by apply idM.
replace B with (MM2M (M2MM B)) by apply idM.
replace C with (MM2M (M2MM C)) by apply idM.
replace (@Mplus m n (@Mplus m n (MM2M (M2MM A)) (MM2M (M2MM B))) (MM2M (M2MM C)))  with
                           (@Mplus (N.of_nat(N.to_nat m)) (N.of_nat(N.to_nat n)) (@Mplus (N.of_nat(N.to_nat m)) (N.of_nat(N.to_nat n)) (MM2M(M2MM A)) (MM2M (M2MM B))) (MM2M (M2MM C)))
      by (repeat rewrite Nnat.N2Nat.id; auto).
rewrite rr7. rewrite rr7.
rewrite M.Mplus_assoc.
replace (@Mplus m n  (MM2M (M2MM A)) (@Mplus m n (MM2M (M2MM B)) (MM2M (M2MM C))))  with
                           (@Mplus (N.of_nat(N.to_nat m)) (N.of_nat(N.to_nat n)) (MM2M (M2MM A)) (@Mplus (N.of_nat(N.to_nat m)) (N.of_nat(N.to_nat n)) (MM2M (M2MM B)) (MM2M (M2MM C))))  
      by (repeat rewrite Nnat.N2Nat.id; auto).
rewrite rr7. rewrite rr7.
auto.
Qed.


Lemma rr3 : forall (m n o: nat) (A : M.Matrix m n) (B : M.Matrix n o),  MM2M A × MM2M B = MM2M (M.Mmult A B) .
Proof.
intros.
unfold Mmult.
repeat rewrite idMM.
repeat rewrite Nnat.Nat2N.id.
auto.
Qed.

(* Lemma rr5 : forall (m n o: N) (A : Matrix m n) (B : Matrix n o),  MM2M (M2MM A) × MM2M (M2MM B) = MM2M (M.Mmult (M2MM A) (M2MM B)) .
Proof.
intros.
rewrite rr3.
auto.
Qed. *)

Theorem Mmult_assoc : forall {m n o p : N} (A : Matrix m n) (B : Matrix n o) 
  (C: Matrix o p), A × B × C = A × (B × C).
Proof.
intros.
replace A with (MM2M (M2MM A)) by apply idM.
replace B with (MM2M (M2MM B)) by apply idM.
replace C with (MM2M (M2MM C)) by apply idM.
replace (@Mmult m o p (@Mmult m n o (MM2M (M2MM A)) (MM2M (M2MM B))) (MM2M (M2MM C)))  with
                           (@Mmult (N.of_nat(N.to_nat m)) (N.of_nat(N.to_nat o)) (N.of_nat(N.to_nat p)) (@Mmult (N.of_nat(N.to_nat m)) (N.of_nat(N.to_nat n)) (N.of_nat(N.to_nat o)) (MM2M(M2MM A)) (MM2M (M2MM B))) (MM2M (M2MM C)))
      by (repeat rewrite Nnat.N2Nat.id; auto).
rewrite rr3. rewrite rr3.
(* repeat rewrite Nnat.N2Nat.id. *)
rewrite M.Mmult_assoc.
replace (@Mmult m n p (MM2M (M2MM A)) (@Mmult n o p (MM2M (M2MM B)) (MM2M (M2MM C)))) with
(@Mmult (N.of_nat(N.to_nat m)) (N.of_nat(N.to_nat n)) (N.of_nat(N.to_nat p)) (MM2M (M2MM A)) (@Mmult (N.of_nat(N.to_nat n)) (N.of_nat(N.to_nat o)) (N.of_nat(N.to_nat p)) (MM2M (M2MM B)) (MM2M (M2MM C))))
      by (repeat rewrite Nnat.N2Nat.id; auto).
rewrite rr3. rewrite rr3.
auto.
Qed.

Lemma Mmult_plus_distr_l : forall (m n o : N) (A : Matrix m n) (B C : Matrix n o), 
                           A × (B .+ C) = A × B .+ A × C.
Proof. 
intros.
replace A with (MM2M (M2MM A)) by apply idM.
replace B with (MM2M (M2MM B)) by apply idM.
replace C with (MM2M (M2MM C)) by apply idM.
replace (@Mmult m n o (MM2M (M2MM A)) (@Mplus n o (MM2M (M2MM B)) (MM2M (M2MM C))))  with
                           (@Mmult (N.of_nat(N.to_nat m)) (N.of_nat(N.to_nat n)) (N.of_nat(N.to_nat o)) (MM2M (M2MM A)) (@Mplus (N.of_nat(N.to_nat n)) (N.of_nat(N.to_nat o)) (MM2M (M2MM B)) (MM2M (M2MM C))))
      by (repeat rewrite Nnat.N2Nat.id; auto).
rewrite rr7.
rewrite rr3.
rewrite M.Mmult_plus_distr_l.
replace (@Mplus m o (@Mmult m n o (MM2M (M2MM A)) (MM2M (M2MM B))) (@Mmult m n o (MM2M (M2MM A)) (MM2M (M2MM C)))) with
(@Mplus (N.of_nat(N.to_nat m))(N.of_nat(N.to_nat o)) (@Mmult (N.of_nat(N.to_nat m)) (N.of_nat(N.to_nat n)) (N.of_nat(N.to_nat o)) (MM2M (M2MM A)) (MM2M (M2MM B))) (@Mmult (N.of_nat(N.to_nat m)) (N.of_nat(N.to_nat n)) (N.of_nat(N.to_nat o)) (MM2M (M2MM A)) (MM2M (M2MM C))))
      by (repeat rewrite Nnat.N2Nat.id; auto).
rewrite rr3.
rewrite rr3.
rewrite rr7.
auto.
Qed.

Lemma Mmult_plus_distr_r : forall (m n o : N) (A B : Matrix m n) (C : Matrix n o), 
                           (A .+ B) × C = A × C .+ B × C.
Proof. 
intros.
replace A with (MM2M (M2MM A)) by apply idM.
replace B with (MM2M (M2MM B)) by apply idM.
replace C with (MM2M (M2MM C)) by apply idM.
replace (@Mmult m n o (@Mplus m n (MM2M (M2MM A)) (MM2M (M2MM B))) (MM2M (M2MM C)))  with
                           (@Mmult (N.of_nat(N.to_nat m)) (N.of_nat(N.to_nat n)) (N.of_nat(N.to_nat o)) (@Mplus (N.of_nat(N.to_nat m)) (N.of_nat(N.to_nat n)) (MM2M (M2MM A)) (MM2M (M2MM B))) (MM2M (M2MM C)))
      by (repeat rewrite Nnat.N2Nat.id; auto).
rewrite rr7.
rewrite rr3.
rewrite M.Mmult_plus_distr_r.
replace (@Mplus m o (@Mmult m n o (MM2M (M2MM A)) (MM2M (M2MM C))) (@Mmult m n o (MM2M (M2MM B)) (MM2M (M2MM C)))) with
(@Mplus (N.of_nat(N.to_nat m))(N.of_nat(N.to_nat o)) (@Mmult (N.of_nat(N.to_nat m)) (N.of_nat(N.to_nat n)) (N.of_nat(N.to_nat o)) (MM2M (M2MM A)) (MM2M (M2MM C))) (@Mmult (N.of_nat(N.to_nat m)) (N.of_nat(N.to_nat n)) (N.of_nat(N.to_nat o)) (MM2M (M2MM B)) (MM2M (M2MM C))))
      by (repeat rewrite Nnat.N2Nat.id; auto).
rewrite rr3.
rewrite rr3.
rewrite rr7.
auto.
Qed.

Lemma rr1 : forall (m n o p: nat) (A : M.Matrix m n) (B : M.Matrix o p),  MM2M A ⊗ MM2M B = MM2M (M.kron A B).
Proof.
intros.
unfold kron.
repeat rewrite idMM.
repeat rewrite Nnat.Nat2N.id.
auto.
Qed.

Lemma kron_plus_distr_l : forall (m n o p : N) (A : Matrix m n) (B C : Matrix o p), 
                           A ⊗ (B .+ C) = A ⊗ B .+ A ⊗ C.
Proof. 
intros.
replace A with (MM2M (M2MM A)) by apply idM.
replace B with (MM2M (M2MM B)) by apply idM.
replace C with (MM2M (M2MM C)) by apply idM.
replace (@kron m n o p (MM2M (M2MM A)) (@Mplus o p (MM2M (M2MM B)) (MM2M (M2MM C))))  with
                           (@kron (N.of_nat(N.to_nat m)) (N.of_nat(N.to_nat n)) (N.of_nat(N.to_nat o)) (N.of_nat(N.to_nat p)) (MM2M (M2MM A)) (@Mplus (N.of_nat(N.to_nat o)) (N.of_nat(N.to_nat p)) (MM2M (M2MM B)) (MM2M (M2MM C))))
      by (repeat rewrite Nnat.N2Nat.id; auto).
rewrite rr7.
rewrite rr1.
rewrite M.kron_plus_distr_l.
replace (@Mplus (m*o) (n*p) (@kron m n o p (MM2M (M2MM A)) (MM2M (M2MM B))) (@kron m n o p (MM2M (M2MM A)) (MM2M (M2MM C)))) with
(@Mplus (N.of_nat (N.to_nat m * N.to_nat o)) (N.of_nat (N.to_nat n * N.to_nat p)) (@kron (N.of_nat(N.to_nat m)) (N.of_nat(N.to_nat n)) (N.of_nat(N.to_nat o)) (N.of_nat(N.to_nat p)) (MM2M (M2MM A)) (MM2M (M2MM B))) (@kron (N.of_nat(N.to_nat m)) (N.of_nat(N.to_nat n)) (N.of_nat(N.to_nat o)) (N.of_nat(N.to_nat p)) (MM2M (M2MM A)) (MM2M (M2MM C))))
by (repeat rewrite Nnat.N2Nat.id; auto). 
rewrite rr1.
rewrite rr1.
rewrite rr7.
auto.
Qed.

Lemma kron_plus_distr_r : forall (m n o p : N) (A B : Matrix m n) (C : Matrix o p), 
                           (A .+ B) ⊗ C = A ⊗ C .+ B ⊗ C.
Proof. 
intros.
replace A with (MM2M (M2MM A)) by apply idM.
replace B with (MM2M (M2MM B)) by apply idM.
replace C with (MM2M (M2MM C)) by apply idM.
replace (@kron m n o p (@Mplus m n (MM2M (M2MM A)) (MM2M (M2MM B))) (MM2M (M2MM C)))  with
                           (@kron (N.of_nat(N.to_nat m)) (N.of_nat(N.to_nat n)) (N.of_nat(N.to_nat o)) (N.of_nat(N.to_nat p)) (@Mplus (N.of_nat(N.to_nat m)) (N.of_nat(N.to_nat n)) (MM2M (M2MM A)) (MM2M (M2MM B))) (MM2M (M2MM C)))
      by (repeat rewrite Nnat.N2Nat.id; auto).
rewrite rr7.
rewrite rr1.
rewrite M.kron_plus_distr_r.
replace (@Mplus (m*o) (n*p) (@kron m n o p (MM2M (M2MM A)) (MM2M (M2MM C))) (@kron m n o p (MM2M (M2MM B)) (MM2M (M2MM C)))) with
(@Mplus (N.of_nat (N.to_nat m * N.to_nat o)) (N.of_nat (N.to_nat n * N.to_nat p)) (@kron (N.of_nat(N.to_nat m)) (N.of_nat(N.to_nat n)) (N.of_nat(N.to_nat o)) (N.of_nat(N.to_nat p)) (MM2M (M2MM A)) (MM2M (M2MM C))) (@kron (N.of_nat(N.to_nat m)) (N.of_nat(N.to_nat n)) (N.of_nat(N.to_nat o)) (N.of_nat(N.to_nat p)) (MM2M (M2MM B)) (MM2M (M2MM C))))
by (repeat rewrite Nnat.N2Nat.id; auto). 
rewrite rr1.
rewrite rr1.
rewrite rr7.
auto.
Qed.

Lemma Mscale_0_l : forall (m n : N) (A : Matrix m n), C0 .* A = Zero.
Proof.  intros. lma. Qed.

Lemma Mscale_0_r : forall (m n : N) (c : C), c .* @Zero m n = Zero.
Proof.  intros. lma. Qed.

Lemma Mscale_1_l : forall (m n : N) (A : Matrix m n), C1 .* A = A.
Proof.
  intros.
  unfold scale.
  rewrite M.Mscale_1_l.
  rewrite idM.
  auto.
Qed.

(* Lemma Mscale_1_r : forall (n : N) (c : C),
    c .* I n = fun x y => if ((N.to_nat x) =? (N.to_nat y)) && ((N.to_nat x) <?(N.to_nat n)) then c else C0.
Proof.
  intros n c.
  prep_matrix_equality.
  unfold scale, I.
  destruct ((x =? y) && (x <? n)).
  rewrite Cmult_1_r; reflexivity.
  rewrite Cmult_0_r; reflexivity.
Qed. *)

Lemma Mscale_assoc : forall (m n : N) (x y : C) (A : Matrix m n),
  x .* (y .* A) = (x * y) .* A.
Proof.
  intros. unfold scale.
replace (@MM2M (N.to_nat m) (N.to_nat n)
  (@M.scale (N.to_nat m) (N.to_nat n) x
     (@M2MM m n
        (@MM2M (N.to_nat m) (N.to_nat n)
           (@M.scale (N.to_nat m) (N.to_nat n) y (@M2MM m n A))))))
with (@MM2M (N.to_nat m) (N.to_nat n)
  (@M.scale (N.to_nat m) (N.to_nat n) x
     (@M2MM (N.of_nat(N.to_nat m)) (N.of_nat(N.to_nat n))
        (@MM2M (N.to_nat m) (N.to_nat n)
           (@M.scale (N.to_nat m) (N.to_nat n) y (@M2MM m n A))))))
      by (repeat rewrite Nnat.N2Nat.id; auto).
rewrite idMM.
rewrite M.Mscale_assoc.
auto.
Qed.

Lemma Mscale_plus_distr_l : forall (m n : N) (x y : C) (A : Matrix m n),
  (x + y) .* A = x .* A .+ y .* A.
Proof.
  intros.  unfold scale.
rewrite M.Mscale_plus_distr_l.
unfold Mplus.
replace (@MM2M (N.to_nat m) (N.to_nat n)
  (@M.Mplus (N.to_nat m) (N.to_nat n)
     (@M2MM m n
        (@MM2M (N.to_nat m) (N.to_nat n)
           (@M.scale (N.to_nat m) (N.to_nat n) x (@M2MM m n A))))
     (@M2MM m n
        (@MM2M (N.to_nat m) (N.to_nat n)
           (@M.scale (N.to_nat m) (N.to_nat n) y (@M2MM m n A))))))
with (@MM2M (N.to_nat m) (N.to_nat n)
  (@M.Mplus (N.to_nat m) (N.to_nat n)
     (@M2MM (N.of_nat(N.to_nat m)) (N.of_nat(N.to_nat n))
        (@MM2M (N.to_nat m) (N.to_nat n)
           (@M.scale (N.to_nat m) (N.to_nat n) x (@M2MM m n A))))
     (@M2MM (N.of_nat(N.to_nat m)) (N.of_nat(N.to_nat n))
        (@MM2M (N.to_nat m) (N.to_nat n)
           (@M.scale (N.to_nat m) (N.to_nat n) y (@M2MM m n A))))))
      by (repeat rewrite Nnat.N2Nat.id; auto).
repeat rewrite idMM.
auto.
Qed.

Lemma Mscale_plus_distr_r : forall (m n : N) (x : C) (A B : Matrix m n),
  x .* (A .+ B) = x .* A .+ x .* B.
Proof. intros. lma. Qed.

Lemma Mscale_mult_dist_l : forall (m n o : N) (x : C) (A : Matrix m n) (B : Matrix n o), 
    ((x .* A) × B) = x .* (A × B).
Proof.
  intros.
  unfold scale,Mmult.
 replace (@MM2M (N.to_nat m) (N.to_nat o)
  (@M.scale (N.to_nat m) (N.to_nat o) x
     (@M2MM m o
        (@MM2M (N.to_nat m) (N.to_nat o)
           (@M.Mmult (N.to_nat m) (N.to_nat n) (N.to_nat o) 
              (@M2MM m n A) (@M2MM n o B))))))
with (@MM2M (N.to_nat m) (N.to_nat o)
  (@M.scale (N.to_nat m) (N.to_nat o) x
     (@M2MM (N.of_nat(N.to_nat m)) (N.of_nat(N.to_nat o))
        (@MM2M (N.to_nat m) (N.to_nat o)
           (@M.Mmult (N.to_nat m) (N.to_nat n) (N.to_nat o) 
              (@M2MM m n A) (@M2MM n o B))))))
      by (repeat rewrite Nnat.N2Nat.id; auto).
rewrite idMM.
rewrite <- M.Mscale_mult_dist_l.
replace (@MM2M (N.to_nat m) (N.to_nat o)
  (@M.Mmult (N.to_nat m) (N.to_nat n) (N.to_nat o)
     (@M2MM m n
        (@MM2M (N.to_nat m) (N.to_nat n)
           (@M.scale (N.to_nat m) (N.to_nat n) x (@M2MM m n A))))
     (@M2MM n o B)))
with (@MM2M (N.to_nat m) (N.to_nat o)
  (@M.Mmult (N.to_nat m) (N.to_nat n) (N.to_nat o)
     (@M2MM (N.of_nat(N.to_nat m)) (N.of_nat(N.to_nat n))
        (@MM2M (N.to_nat m) (N.to_nat n)
           (@M.scale (N.to_nat m) (N.to_nat n) x (@M2MM m n A))))
     (@M2MM n o B)))
      by (repeat rewrite Nnat.N2Nat.id; auto).
rewrite idMM.
auto.
Qed.

Lemma Mscale_mult_dist_r : forall (m n o : N) (x : C) (A : Matrix m n) (B : Matrix n o),
    (A × (x .* B)) = x .* (A × B).
Proof.
  intros.
  unfold scale,Mmult.
 replace (@M2MM m o)
with (@M2MM (N.of_nat(N.to_nat m)) (N.of_nat(N.to_nat o)))
      by (repeat rewrite Nnat.N2Nat.id; auto).
 replace (@M2MM n o)
with (@M2MM (N.of_nat(N.to_nat n)) (N.of_nat(N.to_nat o)))
      by (repeat rewrite Nnat.N2Nat.id; auto).
repeat rewrite idMM.
rewrite <- M.Mscale_mult_dist_r.
auto.
Qed.

Lemma Mscale_kron_dist_l : forall (m n o p : N) (x : C) (A : Matrix m n) (B : Matrix o p), 
    ((x .* A) ⊗ B) = x .* (A ⊗ B).
Proof.
  intros.
  unfold scale,kron.
 replace (@M2MM m n)
with (@M2MM (N.of_nat(N.to_nat m)) (N.of_nat(N.to_nat n)))
      by (repeat rewrite Nnat.N2Nat.id; auto).
repeat rewrite idMM.
(*  replace (@M2MM (m * o) (n * p))
with (@M2MM (N.of_nat (N.to_nat (m * o))) (N.of_nat (N.to_nat (n * p))))
      by (repeat rewrite Nnat.N2Nat.id; auto). *)
replace (@M2MM (m * o) (n * p))
with (@M2MM (N.of_nat (N.to_nat m * N.to_nat o)) (N.of_nat (N.to_nat n * N.to_nat p)))
      by (repeat rewrite Nnat.N2Nat.id; auto).
repeat rewrite idMM.
rewrite M.Mscale_kron_dist_l .
auto.
Qed.

Lemma Mscale_kron_dist_r : forall (m n o p : N) (x : C) (A : Matrix m n) (B : Matrix o p), 
    (A ⊗ (x .* B)) = x .* (A ⊗ B).
Proof.
  intros.
  unfold scale,kron.
 replace (@M2MM o p)
with (@M2MM (N.of_nat(N.to_nat o)) (N.of_nat(N.to_nat p)))
      by (repeat rewrite Nnat.N2Nat.id; auto).
replace (@M2MM (m * o) (n * p))
with (@M2MM (N.of_nat (N.to_nat m * N.to_nat o)) (N.of_nat (N.to_nat n * N.to_nat p)))
      by (repeat rewrite Nnat.N2Nat.id; auto).
repeat rewrite idMM.
rewrite M.Mscale_kron_dist_r .
auto.
Qed.

Lemma Mscale_trans : forall (m n : N) (x : C) (A : Matrix m n),
    (x .* A)⊤ = x .* A⊤.
Proof. reflexivity. Qed.

Lemma Mscale_adj : forall (m n : N) (x : C) (A : Matrix m n),
    (x .* A)† = x^* .* A†.
Proof.
  intros m n x A. lma.
Qed.

Local Open Scope N_scope.

Instance Scale_proper(m n :N): Proper (eq ==> mat_equiv ==> mat_equiv) (@scale m n).
Proof.
hnf;intros k1 k2 H1.
hnf;intros A B H2.
unfold mat_equiv,scale,get in *.
intros.
rewrite H1.
replace (@M2MM m n) with (@M2MM (N.of_nat(N.to_nat m)) (N.of_nat(N.to_nat n))) 
      by (repeat rewrite Nnat.N2Nat.id; auto).
 repeat rewrite idMM.
repeat rewrite Nnat.N2Nat.id.
prep_matrix_equality.
rewrite M.Scale_proper.
auto. auto.
unfold M.mat_equiv. intros. rewrite H2. auto. auto. auto.
Qed.


Instance Mplus_proper(m n:N): Proper (mat_equiv ==> mat_equiv ==> mat_equiv) (@Mplus m n).
Proof.
hnf;intros A C H1.
hnf;intros B D H2.
unfold mat_equiv,Mplus,get in *.
intros.
replace (@M2MM m n) with (@M2MM (N.of_nat(N.to_nat m)) (N.of_nat(N.to_nat n))) 
      by (repeat rewrite Nnat.N2Nat.id; auto).
 repeat rewrite idMM.
repeat rewrite Nnat.N2Nat.id.
prep_matrix_equality.
rewrite M.Mplus_proper.
auto.
unfold M.mat_equiv. intros. rewrite H1. auto. auto. auto.
unfold M.mat_equiv. intros. rewrite H2. auto. auto. auto.
Qed.


Instance mult_proper(m n o:N): Proper (mat_equiv ==> mat_equiv ==> mat_equiv) (@Mmult m n o).
Proof.
hnf;intros A C H1.
hnf;intros B D H2.
unfold mat_equiv,Mmult,get in *.
intros.
replace (@M2MM m o) with (@M2MM (N.of_nat(N.to_nat m)) (N.of_nat(N.to_nat o))) 
      by (repeat rewrite Nnat.N2Nat.id; auto).
 repeat rewrite idMM.
prep_matrix_equality.
(* unfold M.Mmult.
apply Csum_eq_bounded.
intros z Pz.
destruct x0 as [x0 Px0], y0 as [y0 Py0].
specialize (H1 (exist _ x0 Px0) (exist _ z0 Pz0)). *)
rewrite M.mult_proper.
auto.
Admitted.
(* unfold M.mat_equiv. intros. rewrite H1. auto. auto. auto.
unfold M.mat_equiv. intros. rewrite H2. auto. auto. auto. *)


Instance kron_proper(m n o p:N): Proper (mat_equiv ==> mat_equiv ==> mat_equiv) (@kron m n o p ).
Proof.
hnf;intros A C H1.
hnf;intros B D H2.
unfold mat_equiv,kron,get in *.
intros.
replace (@M2MM (m * o) (n * p)) with (@M2MM (N.of_nat((N.to_nat m * N.to_nat o))) (N.of_nat((N.to_nat n * N.to_nat p)))) 
      by (repeat rewrite Nnat.N2Nat.id; auto).
 repeat rewrite idMM.
replace (N.to_nat (m * o)) with ((N.to_nat m) * (N.to_nat o))%nat by (rewrite Nnat.N2Nat.inj_mul;auto).
replace (N.to_nat (n * p)) with ((N.to_nat n) * (N.to_nat p))%nat by (rewrite Nnat.N2Nat.inj_mul;auto).
prep_matrix_equality.
rewrite M.kron_proper.
auto.
Admitted.


Instance adjoint_proper(m n:N) : Proper (mat_equiv ==> mat_equiv) (@adjoint m n).
Proof.
hnf;intros A C H1.
unfold mat_equiv,adjoint,get in *.
intros.
replace (@M2MM n m) with (@M2MM (N.of_nat(N.to_nat n)) (N.of_nat(N.to_nat m))) 
      by (repeat rewrite Nnat.N2Nat.id; auto).
 repeat rewrite idMM.
prep_matrix_equality.
rewrite M.adjoint_proper.
auto.
unfold M.mat_equiv. intros. rewrite H1. auto. auto. auto.
Qed.

(* Inverses of square matrices *)

Local Open Scope N_scope.

Lemma kron_assoc : forall {m n p q r s : N}
  (A : Matrix m n) (B : Matrix p q) (C : Matrix r s),
  (A ⊗ B ⊗ C) ≡ (A ⊗ (B ⊗ C):  Matrix (m*p*r)(n*q*s)).
Proof.
  intros.
  unfold mat_equiv,kron,get in *.
intros.





replace (@M2MM (m * p) (n * q)) with (@M2MM (N.of_nat((N.to_nat m * N.to_nat p))) (N.of_nat((N.to_nat n * N.to_nat q)))) 
      by (repeat rewrite Nnat.N2Nat.id; auto).
replace (@M2MM (p * r) (q * s)) with (@M2MM (N.of_nat((N.to_nat p * N.to_nat r))) (N.of_nat((N.to_nat q * N.to_nat s)))) 
      by (repeat rewrite Nnat.N2Nat.id; auto).
repeat rewrite idMM.



replace (N.to_nat (m * p * r)) with ((N.to_nat m) * (N.to_nat p) * (N.to_nat r))%nat by (repeat rewrite Nnat.N2Nat.inj_mul;auto).
replace (N.to_nat (n * q * s)) with ((N.to_nat n) * (N.to_nat q) * (N.to_nat s))%nat by (repeat rewrite Nnat.N2Nat.inj_mul;auto).
replace (@M2MM (m * p * r) (n * q * s)) with (@M2MM (N.of_nat((N.to_nat m * N.to_nat p * N.to_nat r))) (N.of_nat((N.to_nat n * N.to_nat q * N.to_nat s)))) 
      by (repeat rewrite Nnat.N2Nat.id; auto).
replace (N.to_nat (m * p)) with ((N.to_nat m) * (N.to_nat p))%nat by (rewrite Nnat.N2Nat.inj_mul;auto).
replace (N.to_nat (n * q)) with ((N.to_nat n) * (N.to_nat q))%nat by (rewrite Nnat.N2Nat.inj_mul;auto).
repeat rewrite idMM.
replace (N.to_nat (p * r)) with ((N.to_nat p) * (N.to_nat r))%nat by (rewrite Nnat.N2Nat.inj_mul;auto).
replace (N.to_nat (q * s)) with ((N.to_nat q) * (N.to_nat s))%nat by (rewrite Nnat.N2Nat.inj_mul;auto).
replace ((N.to_nat m) * (N.to_nat p * N.to_nat r))%nat with (N.to_nat m * N.to_nat p * N.to_nat r)%nat by lia.
replace ((N.to_nat n) * (N.to_nat q * N.to_nat s))%nat with (N.to_nat n * N.to_nat q * N.to_nat s)%nat by lia.
repeat rewrite idMM.
Admitted.
(* rewrite M.kron_assoc.
auto.
Qed. *)

Lemma kron_mixed_product : forall {m n o p q r : N} (A : Matrix m n) (B : Matrix p q ) 
  (C : Matrix n o) (D : Matrix q r), (A ⊗ B) × (C ⊗ D) = (A × C) ⊗ (B × D).
Proof.
  intros.
  unfold kron, Mmult.
replace (@M2MM (m * p) (n * q)) with (@M2MM (N.of_nat((N.to_nat m * N.to_nat p))) (N.of_nat((N.to_nat n * N.to_nat q)))) 
      by (repeat rewrite Nnat.N2Nat.id; auto).
replace (@M2MM (n * q) (o * r)) with (@M2MM (N.of_nat((N.to_nat n * N.to_nat q))) (N.of_nat((N.to_nat o * N.to_nat r)))) 
      by (repeat rewrite Nnat.N2Nat.id; auto).
replace (@M2MM m o) with (@M2MM (N.of_nat (N.to_nat m)) (N.of_nat (N.to_nat o)))
      by (repeat rewrite Nnat.N2Nat.id; auto).
replace (@M2MM p r) with (@M2MM (N.of_nat (N.to_nat p)) (N.of_nat (N.to_nat r )))
      by (repeat rewrite Nnat.N2Nat.id; auto).
repeat rewrite idMM.
replace (N.to_nat (m * p)) with ((N.to_nat m) * (N.to_nat p))%nat by (rewrite Nnat.N2Nat.inj_mul;auto).
replace (N.to_nat (n * q)) with ((N.to_nat n) * (N.to_nat q))%nat by (rewrite Nnat.N2Nat.inj_mul;auto).
replace (N.to_nat (o * r)) with ((N.to_nat o) * (N.to_nat r))%nat by (rewrite Nnat.N2Nat.inj_mul;auto).
(* replace (N.to_nat (p * r)) with ((N.to_nat p) * (N.to_nat r))%nat by (rewrite Nnat.N2Nat.inj_mul;auto).
replace (N.to_nat (q * s)) with ((N.to_nat q) * (N.to_nat s))%nat by (rewrite Nnat.N2Nat.inj_mul;auto). *)
rewrite M.kron_mixed_product.
auto.
Qed.


Lemma Mplus_tranpose : forall (m n : N) (A : Matrix m n) (B : Matrix m n),
  (A .+ B)⊤ = A⊤ .+ B⊤.
Proof. intros. reflexivity. Qed.

Lemma Mmult_tranpose : forall (m n o : N) (A : Matrix m n) (B : Matrix n o),
      (A × B)⊤ = B⊤ × A⊤.
Proof.
  intros m n o A B.
  unfold Mmult, transpose.
replace (@M2MM m o) with (@M2MM (N.of_nat (N.to_nat m)) (N.of_nat (N.to_nat o)))
      by (repeat rewrite Nnat.N2Nat.id; auto).
replace (@M2MM o n) with (@M2MM (N.of_nat (N.to_nat o)) (N.of_nat (N.to_nat n)))
      by (repeat rewrite Nnat.N2Nat.id; auto).
replace (@M2MM n m) with (@M2MM (N.of_nat (N.to_nat n)) (N.of_nat (N.to_nat m)))
      by (repeat rewrite Nnat.N2Nat.id; auto).
repeat rewrite idMM.
rewrite M.Mmult_tranpose.
auto.
Qed.

Lemma kron_transpose : forall (m n o p : N) (A : Matrix m n) (B : Matrix o p ),
  (A ⊗ B)⊤ = A⊤ ⊗ B⊤.
Proof.
intros.
unfold kron, transpose.
replace (@M2MM (m * o) (n * p)) with (@M2MM (N.of_nat((N.to_nat m * N.to_nat o))) (N.of_nat((N.to_nat n * N.to_nat p)))) 
      by (repeat rewrite Nnat.N2Nat.id; auto).
replace (@M2MM n m) with (@M2MM (N.of_nat (N.to_nat n)) (N.of_nat (N.to_nat m)))
      by (repeat rewrite Nnat.N2Nat.id; auto).
replace (@M2MM p o) with (@M2MM (N.of_nat (N.to_nat p)) (N.of_nat (N.to_nat o )))
      by (repeat rewrite Nnat.N2Nat.id; auto).
repeat rewrite idMM.
replace (N.to_nat (m * o)) with ((N.to_nat m) * (N.to_nat o))%nat by (rewrite Nnat.N2Nat.inj_mul;auto).
replace (N.to_nat (n * p)) with ((N.to_nat n) * (N.to_nat p))%nat by (rewrite Nnat.N2Nat.inj_mul;auto).
rewrite M.kron_transpose.
auto.
Qed.


Lemma Mplus_adjoint : forall (m n : N) (A : Matrix m n) (B : Matrix m n),
  (A .+ B)† = A† .+ B†.
Proof. intros. lma. Qed.

Lemma Mmult_adjoint : forall {m n o : N} (A : Matrix m n) (B : Matrix n o),
      (A × B)† = B† × A†.
Proof.
  intros.
  unfold Mmult, adjoint.
replace (@M2MM m o) with (@M2MM (N.of_nat (N.to_nat m)) (N.of_nat (N.to_nat o)))
      by (repeat rewrite Nnat.N2Nat.id; auto).
replace (@M2MM o n) with (@M2MM (N.of_nat (N.to_nat o)) (N.of_nat (N.to_nat n)))
      by (repeat rewrite Nnat.N2Nat.id; auto).
replace (@M2MM n m) with (@M2MM (N.of_nat (N.to_nat n)) (N.of_nat (N.to_nat m)))
      by (repeat rewrite Nnat.N2Nat.id; auto).
repeat rewrite idMM.
rewrite M.Mmult_adjoint.
auto.
Qed.

Lemma kron_adjoint : forall {m n o p : N} (A : Matrix m n) (B : Matrix o p),
  (A ⊗ B)† = A† ⊗ B†.
Proof.
  intros. unfold adjoint, kron.
replace (@M2MM (m * o) (n * p)) with (@M2MM (N.of_nat((N.to_nat m * N.to_nat o))) (N.of_nat((N.to_nat n * N.to_nat p)))) 
      by (repeat rewrite Nnat.N2Nat.id; auto).
replace (@M2MM n m) with (@M2MM (N.of_nat (N.to_nat n)) (N.of_nat (N.to_nat m)))
      by (repeat rewrite Nnat.N2Nat.id; auto).
replace (@M2MM p o) with (@M2MM (N.of_nat (N.to_nat p)) (N.of_nat (N.to_nat o)))
      by (repeat rewrite Nnat.N2Nat.id; auto).
repeat rewrite idMM.
replace (N.to_nat (m * o)) with ((N.to_nat m) * (N.to_nat o))%nat by (rewrite Nnat.N2Nat.inj_mul;auto).
replace (N.to_nat (n * p)) with ((N.to_nat n) * (N.to_nat p))%nat by (rewrite Nnat.N2Nat.inj_mul;auto).
rewrite M.kron_adjoint.
auto.
Qed.

Lemma id_kron : forall (m n : N),  I m ⊗ I n = I (m * n).
Proof.
  intros.
  unfold kron,I.
replace (@M2MM m m) with (@M2MM (N.of_nat (N.to_nat m)) (N.of_nat (N.to_nat m)))
      by (repeat rewrite Nnat.N2Nat.id; auto).
replace (@M2MM n n) with (@M2MM (N.of_nat (N.to_nat n)) (N.of_nat (N.to_nat n)))
      by (repeat rewrite Nnat.N2Nat.id; auto).
repeat rewrite idMM.
rewrite M.id_kron.
replace (N.to_nat (m * n)) with ((N.to_nat m) * (N.to_nat n))%nat by (rewrite Nnat.N2Nat.inj_mul;auto).
auto.
Qed.

Definition ket0 : Vector 2 := 
  fun x y => match x, y with 
          | 0, 0 => C1
          | 1, 0 => C0
          | _, _ => C0
          end.
Definition ket1 : Vector 2 := 
  fun x y => match x, y with 
          | 0, 0 => C0
          | 1, 0 => C1
          | _, _ => C0
          end.

Notation "∣0⟩" := ket0.
Notation "∣1⟩" := ket1.
Notation "⟨0∣" := ∣0⟩†.
Notation "⟨1∣" := ∣1⟩†.

Definition B0 := ∣0⟩ × ⟨0∣.
Definition B3 := ∣1⟩ × ⟨1∣.

Definition I_2 := B0 .+ B3.
Goal
  (I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2)
  ≡ I_2.
Proof.
  repeat rewrite kron_assoc.
Abort.

