Require Export Dirac.


Variable n : nat.

Local Open Scope N_scope.

(* Fixpoint kron_n (n:nat) {m1 m2} (A : Matrix m1 m2) : Matrix (m1^(N.of_nat n)) (m2^(N.of_nat n)) :=
  match n with
  | 0%nat    => I 1
  | S n' => kron A (kron_n n' A)
  end. *)

Definition ket0_n' n := kron_n n ket0.

Fixpoint ket0_n n : Matrix (2^(N.of_nat n)) 1  :=
match n with
| 0%nat  => I 1
| S n' => ket0 ⊗ ket0_n n'
end.

Lemma ket0_n_eq : kron_n n ket0 = ket0_n n .
Proof.
induction n.
simpl. reflexivity.
simpl.  rewrite IHn0.  rewrite N.pow_1_l. auto.
Qed.

Definition H_n' n := kron_n n H.

(* Fixpoint H_n'' (n : nat) : Matrix (2^(N.of_nat n)) (2^(N.of_nat n)):= 
  match n with
  | 0 => I 1
  | S n' => H_n n' ⊗ H
  end.
 *)

Fixpoint H_n n : Matrix (2^(N.of_nat n)) (2^(N.of_nat n)):= 
  match n with
  | 0%nat  => I 1
  | S n' => H ⊗ H_n n' 
  end.

Lemma H_n_eq : kron_n n H = H_n n .
Proof.
induction n.
simpl. reflexivity.
simpl.  rewrite IHn0.  auto.
Qed.


Definition ketp_n' n := kron_n n ketp.

Fixpoint ketp_n n : Matrix (2^(N.of_nat n)) 1 :=
match n with
| 0%nat  => I 1
| S n' => ketp ⊗ ketp_n n'
end.

Lemma ketp_n_eq : kron_n n ketp = ketp_n n .
Proof.
induction n.
simpl. reflexivity.
simpl.  rewrite IHn0.
autorewrite with nz.
(*  rewrite N.pow_1_l. *)
auto. lia.
Qed.

Lemma p1 : forall (n0:nat) (n:N),
(n ^ (Npos (Pos.of_succ_nat n0))) = n * n ^ N.of_nat n0.
Proof.
intros.
assert (N.pos (Pos.of_succ_nat n0) = (N.of_nat n0 + 1)%N) by lia.
rewrite H.
rewrite N.pow_add_r. autorewrite with nz.
rewrite N.mul_comm. auto.
Qed.


Theorem QFT_ket0_n' :
ketp_n n ≡ H_n n × ket0_n n.
Proof.
Opaque N.pow.
intros.
induction n.
 -  simpl. rewrite Mmult_1_l. reflexivity.
 -  simpl. rewrite p1.
     rewrite IHn0.
     assert ((N.mul (Npos xH) (Npos xH)) = (Npos xH)) by lia.
     rewrite <- H.
     rewrite kron_mixed_product.
     operate_reduce.
Qed.


Theorem QFT_ket0_n :
kron_n n ketp ≡ kron_n n H × kron_n n ket0 .
Proof.
intros.
induction n.
 - simpl.  rewrite Mmult_1_l. reflexivity.
 - simpl. repeat rewrite p1.
     rewrite IHn0.
     rewrite kron_mixed_product.
     operate_reduce.
Qed.

Theorem QFT_ketp_n : forall n0:nat,
kron_n n0 ket0 ≡ kron_n n0 H × kron_n n0 ketp .
Proof.
intros.
induction n0.
 - simpl.  rewrite Mmult_1_l. reflexivity.
 - simpl. repeat rewrite p1.
     rewrite IHn0.
     rewrite kron_mixed_product.
     operate_reduce.
Qed.



Lemma DJ_0 :
((kron_n n H) ⊗ H) × ((kron_n n ∣0⟩) ⊗ ∣1⟩) ≡ ((kron_n n  ∣+⟩) ⊗ ∣-⟩).
Proof.
rewrite kron_mixed_product.
rewrite QFT_ket0_n. operate_reduce.
Qed.


(* Fixpoint Uf (n:nat) : Matrix (2 ^ (N.of_nat n + 1)) (2 ^ (N.of_nat n + 1))  :=
  match n with
  | O => I 2
  | S n' =>    @Mmult _ _ (2 ^ (N.of_nat n + 1)) (I (2 ^ N.of_nat n') ⊗ CX) ((Uf n') ⊗ I 2)
  end. *)

(* Fixpoint Uf' (n:nat) : Matrix (2^((N.of_nat n)+1)) (2^((N.of_nat n)+1))  :=
  match n with
  | O => I 2
  | S n' =>    @Mmult _ _ (2 ^ ((N.of_nat n) + 1))  (I 2 ⊗ (Uf' n')) (CX ⊗ I (2^ (N.of_nat n')))
end. *)

Fixpoint Uf (n:nat) : Matrix (2 * 2 ^ (N.of_nat n)) (2 * 2 ^ (N.of_nat n))  :=
  match n with
  | O => I 2
  | S n' =>    @Mmult _ _ (2 * 2 ^ (N.of_nat n))  (I 2 ⊗ (Uf n')) (CX ⊗ I (2^ (N.of_nat n')))
end.
(*which argument*)



Lemma p2 : forall (n0:nat) (n:N),
n ^ (Npos (Pos.succ (Pos.of_succ_nat n0))) = n * (n * n ^ N.of_nat n0).
Proof.
intros.
assert (Npos (Pos.succ (Pos.of_succ_nat n0)) = (N.of_nat n0 + 1 + 1)%N) by lia.
rewrite H.
rewrite N.pow_add_r.
rewrite N.pow_add_r. autorewrite with nz.
rewrite N.mul_comm.
rewrite (N.mul_comm _ n1).  auto.
Qed.

Lemma p3 : forall (n0:nat) (n:N),
n * n * n ^ N.of_nat n0 * n = n * n * (n * n ^ N.of_nat n0).
Proof. lia. Qed.

Lemma p4 : forall (n0:nat) (n:N),
n * n * (n ^ N.of_nat n0 * n) = n * (n * n ^ N.of_nat n0 * n).
Proof. lia. Qed.

Lemma p5 : forall (n0:nat) (n:N),
n * (n * (n * n ^ N.of_nat n0)) = n * (n ^ N.of_nat n0 * n) * n.
Proof. lia. Qed.

Lemma p6 : forall (n0:nat) (n:N),
n ^ N.of_nat n0 * n * n = n * (n * n ^ N.of_nat n0).
Proof. lia. Qed.


Lemma DJ_1 :
(n > 0)%nat ->
@Mmult _ _ (1 ^ (N.of_nat n) * 1)  (Uf n) ((kron_n n ∣+⟩) ⊗ ∣-⟩) ≡ ((kron_n (n-1)  ∣+⟩) ⊗ ∣-⟩ ⊗ ∣-⟩).
Proof.
Opaque N.mul.
intros. destruct n; try lia.
simpl. rewrite Nat.sub_0_r.
induction n0.
- simpl.
   repeat rewrite kron_1_r.
   rewrite id_kron.
   rewrite Mmult_1_l.
   rewrite (kron_1_l _ _ ∣-⟩).
   operate_reduce.
- simpl.
   repeat rewrite p1 in *.
   repeat rewrite p2.
   rewrite Mmult_assoc.
   rewrite (N.mul_comm 2 (2 * (2 * 2 ^ N.of_nat n0))).
   rewrite (N.mul_assoc 1 1 (1^ N.of_nat n0)).
   rewrite (N.mul_assoc 2 2 (2^ N.of_nat n0)) in *.
   rewrite <- kron_assoc.
   rewrite kron_assoc.
   repeat rewrite p3.
   rewrite (N.mul_comm (2^ N.of_nat n0) 2) in *.
   rewrite (N.mul_comm (1^ N.of_nat n0) 1) in *.
   rewrite kron_mixed_product.
   rewrite Mmult_1_l.
   rewrite CXpp.
   rewrite kron_assoc.
   rewrite (N.mul_comm 2 (2^ N.of_nat n0)) in *.
   rewrite (N.mul_comm 1 (1^ N.of_nat n0)) in *.
   rewrite (N.mul_assoc 1 (1^ N.of_nat n0) 1).
   rewrite (N.mul_assoc 2 (2^ N.of_nat n0) 2).
   repeat rewrite p4.
   rewrite <- (kron_assoc ∣+⟩ (kron_n n0 ∣+⟩) ∣-⟩).
   rewrite (N.mul_comm (1 * 1 ^ N.of_nat n0) 1).
   rewrite (N.mul_comm (2 * 2 ^ N.of_nat n0) 2).
   rewrite <- (N.mul_assoc 2 2 (2^ N.of_nat n0)) in *.
   rewrite kron_mixed_product.
   repeat rewrite p6 in *.
   rewrite IHn0 by lia.
   rewrite Mmult_1_l.
   repeat rewrite p5.
   repeat rewrite <- p6 in *.
   rewrite <- kron_assoc.
   rewrite (N.mul_assoc 1 (1^ N.of_nat n0) 1).
   rewrite (N.mul_assoc 2 (2^ N.of_nat n0) 2).
   rewrite <- (kron_assoc ∣+⟩ (kron_n n0 ∣+⟩) ∣-⟩).
   rewrite (N.mul_comm (2^ N.of_nat n0) 2).
   rewrite (N.mul_comm (1^ N.of_nat n0) 1).
   reflexivity.
Qed.

Lemma yy : Dirac.H ⊗ Dirac.H × (∣-⟩ ⊗ ∣-⟩) ≡ ∣1⟩ ⊗ ∣1⟩.
Proof.
operate_reduce.
Qed.

Lemma DJ_2 :
(n > 0)%nat ->
((kron_n (n-1) H) ⊗ H ⊗ H) × ((kron_n (n-1)  ∣+⟩) ⊗ ∣-⟩ ⊗ ∣-⟩) ≡ (kron_n (n-1)  ∣0⟩) ⊗ ∣1⟩ ⊗ ∣1⟩.
Proof.
  intros.
  intros. destruct n; try lia.
  simpl. rewrite Nat.sub_0_r.
  repeat rewrite kron_assoc.
  rewrite <- (N.mul_assoc (2^ N.of_nat n0) 2 2) in *.
  rewrite <- (N.mul_assoc (1^ N.of_nat n0) 1 1) in *.
  rewrite kron_mixed_product.
  rewrite yy. rewrite <- QFT_ketp_n.
  reflexivity.
Qed.



