Require Export Dirac.
Require Export StateAndOperator.
Declare Scope QE.
Local Open Scope QE.


Fixpoint kron_n n {m1 m2} (A : Matrix m1 m2) : Matrix (m1^n) (m2^n) :=
  match n with
  | 0    => I 1
  | S n' => kron (kron_n n' A) A
  end.

Fixpoint ket0_n' (n : nat) := kron_n n ket0.
Fixpoint ket0_n (n : nat) : Matrix (2^n) 1 :=
match n with
| 0 => I 1
| S n' => ket0 ⊗ ket0_n n'
end.

Fixpoint H_n' (n : nat) := kron_n n H.
Fixpoint H_n'' (n : nat) : Matrix (2^n) (2^n):= 
  match n with
  | 0 => I 1
  | S n' => H_n n' ⊗ H
  end.

Fixpoint H_n (n : nat) : Matrix (2^n) (2^n):= 
  match n with
  | 0 => I 1
  | S n' => H ⊗ H_n n' 
  end.

Fixpoint ketp_n' (n : nat) := kron_n n ketp.
Fixpoint ketp_n (n : nat) : Matrix (2^n) 1 :=
match n with
| 0 => I 1
| S n' => ketp ⊗ ketp_n n'
end.


Theorem QFT_ket0_n : forall n : nat,
ketp_n n ≡ H_n n × ket0_n n .
Proof.
intros.
induction n.
 -  simpl. rewrite Mmult_1_r. reflexivity.
 -  simpl. rewrite IHn. mult_kron. rewrite Mmult_H0. reflexivity.
 Qed.



(* 3-qubits QFT on  ∣0,0,0⟩ *)


(*Step-by-step*)

(*Vector*)
Definition CIT :=  B0 ⊗ I_2 ⊗ I_2 .+ B3 ⊗ I_2 ⊗ PT.

Definition φ0 := ∣0,0,0⟩.
Definition φ1 := (I_2 ⊗ I_2 ⊗ H) × φ0.
Definition φ2 := (I_2 ⊗ CS) × φ1.
Definition φ3 := CIT × φ2.
Definition φ4 := (I_2 ⊗ H ⊗ I_2) × φ3.
Definition φ5 := (CS ⊗ I_2) × φ4.
Definition φ6 := (H ⊗ I_2 ⊗ I_2) × φ5.


Lemma step1 : φ1 ≡ ∣0⟩ ⊗ ∣0⟩ ⊗ ∣+⟩.
Proof.
unfold φ1,φ0.
operate_reduce.
Qed.

Lemma step2 : φ2 ≡ ∣0⟩ ⊗ ∣0⟩ ⊗ ∣+⟩.
Proof.
unfold φ2,CS.
rewrite step1.
operate_reduce.
Qed.

Lemma step3 : φ3 ≡ ∣0⟩ ⊗ ∣0⟩ ⊗ ∣+⟩.
Proof.
unfold φ3,CIT.
rewrite step2.
operate_reduce.
Qed.

Lemma step4 : φ4 ≡ ∣0⟩ ⊗ ∣+⟩ ⊗ ∣+⟩.
Proof.
unfold φ4.
rewrite step3.
operate_reduce.
Qed.

Lemma step5 : φ5 ≡ ∣0⟩ ⊗ ∣+⟩ ⊗ ∣+⟩.
Proof.
unfold φ5,CS.
rewrite step4.
operate_reduce.
Qed.

Lemma step6 : φ6 ≡ ∣+⟩ ⊗ ∣+⟩ ⊗ ∣+⟩.
Proof.
unfold φ6.
rewrite step5.
operate_reduce.
Qed.


(*Density*)
Definition ρ0 := φ0 × φ0†.
Definition ρ1 := super (I_2 ⊗ I_2 ⊗ H) ρ0.
Definition ρ2 := super (I_2 ⊗ CS) ρ1.
Definition ρ3 := super CIT ρ2.
Definition ρ4 := super (I_2 ⊗ H ⊗ I_2) ρ3.
Definition ρ5 := super (CS ⊗ I_2) ρ4.
Definition ρ6 := super (H ⊗ I_2 ⊗ I_2) ρ5.

Lemma Dstep1 : ρ1 ≡ φ1 × φ1†.
Proof.
unfold ρ1,ρ0,super.
super_reduce.
Qed.

Lemma Dstep2 : ρ2 ≡ φ2 × φ2†.
Proof.
unfold ρ2,super.
rewrite Dstep1.
super_reduce.
Qed.

Lemma Dstep3 : ρ3 ≡ φ3 × φ3†.
Proof.
unfold ρ3,super.
rewrite Dstep2.
super_reduce.
Qed.

Lemma Dstep4 : ρ4 ≡ φ4 × φ4†.
Proof.
unfold ρ4,super.
rewrite Dstep3.
super_reduce.
Qed.

Lemma Dstep5 : ρ5 ≡ φ5 × φ5†.
Proof.
unfold ρ5,super.
rewrite Dstep4.
super_reduce.
Qed.

Lemma Dstep6 : ρ6 ≡ φ6 × φ6†.
Proof.
unfold ρ6,super.
rewrite Dstep5.
super_reduce.
Qed.



(* One-time *)

Lemma QFT_ket0_3' : (H ⊗ I_2 ⊗ I_2) × (CS ⊗ I_2) × (I_2 ⊗ H ⊗ I_2) × CIT ×  (I_2 ⊗ CS) × (I_2 ⊗ I_2 ⊗ H) × ∣0,0,0⟩ ≡ ∣+⟩ ⊗ ∣+⟩ ⊗ ∣+⟩.
Proof.
unfold CIT.
operate_reduce.
Qed.

Lemma QFT_ket0_3 : (H ⊗ I_2 ⊗ I_2) × (CS ⊗ I_2) × (I_2 ⊗ H ⊗ I_2) × CIT ×  (I_2 ⊗ CS) × (I_2 ⊗ I_2 ⊗ H) × ∣0,0,0⟩ ≈ ∣+⟩ ⊗ ∣+⟩ ⊗ ∣+⟩.
Proof.
by_den.
state_reduce.
rewrite QFT_ket0_3';reflexivity.
Qed.


Lemma DQFT_ket0_3' : super ((H ⊗ I_2 ⊗ I_2) × (CS ⊗ I_2) × (I_2 ⊗ H ⊗ I_2) × CIT ×  (I_2 ⊗ CS) × (I_2 ⊗ I_2 ⊗ H)) (density ∣0,0,0⟩) ≡ density (∣+⟩ ⊗ ∣+⟩ ⊗ ∣+⟩).
Proof.
unfold CIT.
super_reduce.
Qed.

Lemma DQFT_ket0_3 : super ((H ⊗ I_2 ⊗ I_2) × (CS ⊗ I_2) × (I_2 ⊗ H ⊗ I_2) × CIT ×  (I_2 ⊗ CS) × (I_2 ⊗ I_2 ⊗ H)) (density ∣0,0,0⟩) ≈ density (∣+⟩ ⊗ ∣+⟩ ⊗ ∣+⟩).
Proof.
by_def1.
rewrite DQFT_ket0_3';reflexivity.
Qed.


(* 2-qubits QFT on  ∣0,0⟩ *)

Lemma QFT_ket0_2' : (H ⊗ I_2) × CS × (I_2 ⊗ H) × (∣0,0⟩) ≡ ∣+⟩ ⊗ ∣+⟩.
Proof. operate_reduce. Qed.

Lemma QFT_ket0_2 : (H ⊗ I_2) × CS × (I_2 ⊗ H) × (∣0,0⟩) ≈ ∣+⟩ ⊗ ∣+⟩.
Proof.
by_den.
state_reduce.
rewrite QFT_ket0_2';reflexivity.
Qed.


Lemma DQFT_ket0_2' : super ((H ⊗ I_2) × CS × (I_2 ⊗ H)) (density ∣0,0⟩) ≡ density  (∣+⟩ ⊗ ∣+⟩) .
Proof. super_reduce. Qed.

Lemma DQFT_ket0_2 : super ((H ⊗ I_2) × CS × (I_2 ⊗ H)) (density ∣0,0⟩) ≈ density  (∣+⟩ ⊗ ∣+⟩) .
Proof.
by_def1.
rewrite DQFT_ket0_2';reflexivity.
Qed.


(* try 4-qubits QFT on  ∣0,0,0,0⟩ *)
(* Definition PK := B0 .+ Cexp (PI/8)  .* B3.
Definition CIS :=  B0 ⊗ I_2 ⊗ I_2 .+ B3 ⊗ I_2 ⊗ PS.
Definition CIIK :=  B0 ⊗ I_2 ⊗ I_2 ⊗ I_2 .+ B3 ⊗ I_2 ⊗ I_2 ⊗ PK.
Lemma QFT_ket0_4 : (H ⊗ I_2 ⊗ I_2 ⊗ I_2) × (CS ⊗ I_2 ⊗ I_2) × (I_2 ⊗ H ⊗ I_2 ⊗ I_2) × (CIT ⊗ I_2) × (I_2 ⊗ CS ⊗ I_2) × (I_2 ⊗ I_2 ⊗ H ⊗ I_2) ×
                                     CIIK ×  (I_2 ⊗ CIT) × (I_2 ⊗ I_2 ⊗ CS) × (I_2 ⊗ I_2 ⊗ I_2 ⊗ H) × ∣0,0,0,0⟩ ≡ ∣+⟩ ⊗ ∣+⟩ ⊗ ∣+⟩ ⊗ ∣+⟩.
Proof.
unfold CIT,CIIK,PK,CS.
operate_reduce.
Qed. *)

