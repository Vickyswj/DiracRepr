Require Export Dirac.

Definition GHZ := /√2 .* (∣0,0,0⟩) .+ /√2 .* (∣1,1,1⟩).
Definition φ (a b : C) : Vector 2 := a .* ∣0⟩ .+ b .* ∣1⟩.
(* Step-by-step *)

Lemma ss0 :  forall (a b : C),
(M0 ⊗ M0 ⊗ M0 ⊗ I_2) × (I_2 ⊗ H ⊗ H ⊗ I_2) × (XC ⊗ I_2 ⊗ I_2) × (φ a b⊗ GHZ) ≡ / √ 2 * / 2  .* ∣0⟩ ⊗ ∣0⟩ ⊗ ∣0⟩ ⊗ (φ a b) .
Proof.
intros. unfold GHZ,φ.
operate_reduce.
Qed.

Lemma ss1 :  forall (a b : C),
(I_2 ⊗ I_2 ⊗ I_2 ⊗ σZ) × (M0 ⊗ M0 ⊗ M1 ⊗ I_2) × (I_2 ⊗ H ⊗ H ⊗ I_2) × (XC ⊗ I_2 ⊗ I_2) × (φ a b⊗ GHZ) ≡ / √ 2 * / 2  .* ∣0⟩ ⊗ ∣0⟩ ⊗ ∣1⟩ ⊗ (φ a b) .
Proof.
intros. unfold GHZ,φ.
operate_reduce.
Qed.

Lemma ss2 :  forall (a b : C),
(I_2 ⊗ I_2 ⊗ I_2 ⊗ σZ) × (M0 ⊗ M1 ⊗ M0 ⊗ I_2) × (I_2 ⊗ H ⊗ H ⊗ I_2) × (XC ⊗ I_2 ⊗ I_2) × (φ a b⊗ GHZ) ≡ / √ 2 * / 2  .* ∣0⟩ ⊗ ∣1⟩ ⊗ ∣0⟩ ⊗  (φ a b) .
Proof.
intros. unfold GHZ,φ.
operate_reduce.
Qed.

Lemma ss3 :  forall (a b : C),
(I_2 ⊗ I_2 ⊗ I_2 ⊗ σZ) × (I_2 ⊗ I_2 ⊗ I_2 ⊗ σZ) × (M0 ⊗ M1 ⊗ M1 ⊗ I_2) × (I_2 ⊗ H ⊗ H ⊗ I_2) × (XC ⊗ I_2 ⊗ I_2) × (φ a b⊗ GHZ) ≡ / √ 2 * / 2  .* ∣0⟩ ⊗ ∣1⟩ ⊗ ∣1⟩ ⊗  (φ a b) .
Proof.
intros. unfold GHZ,φ.
operate_reduce.
Qed.

Lemma ss4 :  forall (a b : C),
(I_2 ⊗ I_2 ⊗ I_2 ⊗ σX) × (M1 ⊗ M0 ⊗ M0 ⊗ I_2) × (I_2 ⊗ H ⊗ H ⊗ I_2) × (XC ⊗ I_2 ⊗ I_2) × (φ a b⊗ GHZ) ≡ / √ 2 * / 2  .* ∣1⟩ ⊗ ∣0⟩ ⊗ ∣0⟩ ⊗  (φ a b) .
Proof.
intros. unfold GHZ,φ.
operate_reduce.
Qed.

Lemma ss5 :  forall (a b : C),
(I_2 ⊗ I_2 ⊗ I_2 ⊗ σX) × (I_2 ⊗ I_2 ⊗ I_2 ⊗ σZ) × (M1 ⊗ M0 ⊗ M1 ⊗ I_2) × (I_2 ⊗ H ⊗ H ⊗ I_2) × (XC ⊗ I_2 ⊗ I_2) × (φ a b⊗ GHZ) ≡ / √ 2 * / 2  .* ∣1⟩ ⊗ ∣0⟩ ⊗ ∣1⟩ ⊗  (φ a b) .
Proof.
intros. unfold GHZ,φ.
operate_reduce.
Qed.

Lemma ss6 :  forall (a b : C),
(I_2 ⊗ I_2 ⊗ I_2 ⊗ σX) × (I_2 ⊗ I_2 ⊗ I_2 ⊗ σZ) × (M1 ⊗ M1 ⊗ M0 ⊗ I_2) × (I_2 ⊗ H ⊗ H ⊗ I_2) × (XC ⊗ I_2 ⊗ I_2) × (φ a b⊗ GHZ) ≡ / √ 2 * / 2  .* ∣1⟩ ⊗ ∣1⟩ ⊗ ∣0⟩ ⊗  (φ a b) .
Proof.
intros. unfold GHZ,φ.
operate_reduce.
Qed.

Lemma ss7 :  forall (a b : C),
(I_2 ⊗ I_2 ⊗ I_2 ⊗ σX) × (I_2 ⊗ I_2 ⊗ I_2 ⊗ σZ) × (I_2 ⊗ I_2 ⊗ I_2 ⊗ σZ) × (M1 ⊗ M1 ⊗ M1 ⊗ I_2) × (I_2 ⊗ H ⊗ H ⊗ I_2) × (XC ⊗ I_2 ⊗ I_2) × (φ a b⊗ GHZ) ≡ / √ 2 * / 2  .* ∣1⟩ ⊗ ∣1⟩ ⊗ ∣1⟩ ⊗  (φ a b) .
Proof.
intros. unfold GHZ,φ.
operate_reduce.
Qed.




(* Density *)
Lemma Dss0 :  forall (a b : C),
super ((M0 ⊗ M0 ⊗ M0 ⊗ I_2) × (I_2 ⊗ H ⊗ H ⊗ I_2) × (XC ⊗ I_2 ⊗ I_2)) (density ((φ a b) ⊗ GHZ)) ≡ density (/ √ 2 * / 2  .* ∣0⟩ ⊗ ∣0⟩  ⊗ ∣0⟩ ⊗ (φ a b)).
Proof.
intros. unfold GHZ,φ,super.
super_reduce.
Qed.

Lemma Dss1 :  forall (a b : C),
super ((I_2 ⊗ I_2 ⊗ I_2 ⊗ σZ) × (M0 ⊗ M0 ⊗ M1 ⊗ I_2) × (I_2 ⊗ H ⊗ H ⊗ I_2) × (XC ⊗ I_2 ⊗ I_2)) (density ((φ a b) ⊗ GHZ)) ≡ density (/ √ 2 * / 2  .* ∣0⟩ ⊗ ∣0⟩  ⊗ ∣1⟩ ⊗ (φ a b)).
Proof.
intros. unfold GHZ,φ,super.
super_reduce.
Qed.

Lemma Dss2 :  forall (a b : C),
super ((I_2 ⊗ I_2 ⊗ I_2 ⊗ σZ) × (M0 ⊗ M1 ⊗ M0 ⊗ I_2) × (I_2 ⊗ H ⊗ H ⊗ I_2) × (XC ⊗ I_2 ⊗ I_2)) (density ((φ a b) ⊗ GHZ)) ≡ density (/ √ 2 * / 2  .* ∣0⟩ ⊗ ∣1⟩  ⊗ ∣0⟩ ⊗ (φ a b)).
Proof.
intros. unfold GHZ,φ,super.
super_reduce.
Qed.

Lemma Dss3 :  forall (a b : C),
super ((I_2 ⊗ I_2 ⊗ I_2 ⊗ σZ) × (I_2 ⊗ I_2 ⊗ I_2 ⊗ σZ) × (M0 ⊗ M1 ⊗ M1 ⊗ I_2) × (I_2 ⊗ H ⊗ H ⊗ I_2) × (XC ⊗ I_2 ⊗ I_2)) (density ((φ a b) ⊗ GHZ)) ≡ density (/ √ 2 * / 2  .* ∣0⟩ ⊗ ∣1⟩  ⊗ ∣1⟩ ⊗ (φ a b)).
Proof.
intros. unfold GHZ,φ,super.
super_reduce.
Qed.

Lemma Dss4 :  forall (a b : C),
super ((I_2 ⊗ I_2 ⊗ I_2 ⊗ σX) × (M1 ⊗ M0 ⊗ M0 ⊗ I_2) × (I_2 ⊗ H ⊗ H ⊗ I_2) × (XC ⊗ I_2 ⊗ I_2)) (density ((φ a b) ⊗ GHZ)) ≡ density (/ √ 2 * / 2  .* ∣1⟩ ⊗ ∣0⟩  ⊗ ∣0⟩ ⊗ (φ a b)).
Proof.
intros. unfold GHZ,φ,super.
super_reduce.
Qed.

Lemma Dss5 :  forall (a b : C),
super ((I_2 ⊗ I_2 ⊗ I_2 ⊗ σX) × (I_2 ⊗ I_2 ⊗ I_2 ⊗ σZ) × (M1 ⊗ M0 ⊗ M1 ⊗ I_2) × (I_2 ⊗ H ⊗ H ⊗ I_2) × (XC ⊗ I_2 ⊗ I_2)) (density ((φ a b) ⊗ GHZ)) ≡ density (/ √ 2 * / 2  .* ∣1⟩ ⊗ ∣0⟩  ⊗ ∣1⟩ ⊗ (φ a b)).
Proof.
intros. unfold GHZ,φ,super.
super_reduce.
Qed.

Lemma Dss6 :  forall (a b : C),
super ((I_2 ⊗ I_2 ⊗ I_2 ⊗ σX) × (I_2 ⊗ I_2 ⊗ I_2 ⊗ σZ) × (M1 ⊗ M1 ⊗ M0 ⊗ I_2) × (I_2 ⊗ H ⊗ H ⊗ I_2) × (XC ⊗ I_2 ⊗ I_2)) (density ((φ a b) ⊗ GHZ)) ≡ density (/ √ 2 * / 2  .* ∣1⟩ ⊗ ∣1⟩  ⊗ ∣0⟩ ⊗ (φ a b)).
Proof.
intros. unfold GHZ,φ,super.
super_reduce.
Qed.

Lemma Dss7 :  forall (a b : C),
super ((I_2 ⊗ I_2 ⊗ I_2 ⊗ σX) × (I_2 ⊗ I_2 ⊗ I_2 ⊗ σZ) × (I_2 ⊗ I_2 ⊗ I_2 ⊗ σZ) × (M1 ⊗ M1 ⊗ M1 ⊗ I_2) × (I_2 ⊗ H ⊗ H ⊗ I_2) × (XC ⊗ I_2 ⊗ I_2)) (density ((φ a b) ⊗ GHZ)) ≡ density (/ √ 2 * / 2  .* ∣1⟩ ⊗ ∣1⟩  ⊗ ∣1⟩ ⊗ (φ a b)).
Proof.
intros. unfold GHZ,φ,super.
super_reduce.
Qed.

