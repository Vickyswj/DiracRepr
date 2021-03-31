Require Export Dirac.
Require Export Equival.


Definition GHZ := /√2 .* (∣0,0,0⟩) .+ /√2 .* (∣1,1,1⟩).
Definition φ (a b : C) : Vector 2 := a .* ∣0⟩ .+ b .* ∣1⟩.


Lemma ss0 :  forall (a b : C),
(M0 ⊗ M0 ⊗ M0 ⊗ I_2) × (I_2 ⊗ H ⊗ H ⊗ I_2) × (XC ⊗ I_2 ⊗ I_2) × (φ a b ⊗ GHZ) ≡ / √ 2 * / 2  .* ∣0⟩ ⊗ ∣0⟩ ⊗ ∣0⟩ ⊗ φ a b .
Proof.
intros.
unfold φ,GHZ.
operate_reduce.
Qed.

Lemma Dss0 :  forall (a b : C),
super ((M0 ⊗ M0 ⊗ M0 ⊗ I_2) × (I_2 ⊗ H ⊗ H ⊗ I_2) × (XC ⊗ I_2 ⊗ I_2)) (density (φ a b ⊗ GHZ)) ≡ density (/ √ 2 * / 2  .* ∣0⟩ ⊗ ∣0⟩  ⊗ ∣0⟩ ⊗ φ a b).
Proof.
intros.
unfold φ,GHZ.
Time super_reduce.
Qed.

Lemma ss0' :  forall (a b : C),
(M0 ⊗ M0 ⊗ M0 ⊗ I_2) × (I_2 ⊗ H ⊗ H ⊗ I_2) × (XC ⊗ I_2 ⊗ I_2) × (φ a b ⊗ GHZ) ≈ / √ 2 * / 2  .* ∣0⟩ ⊗ ∣0⟩ ⊗ ∣0⟩ ⊗ φ a b .
Proof.
intros.
by_den.
rewrite ss0; reflexivity.
Qed.



Lemma ss1 :  forall (a b : C),
(I_2 ⊗ I_2 ⊗ I_2 ⊗ σZ) × (M0 ⊗ M0 ⊗ M1 ⊗ I_2) × (I_2 ⊗ H ⊗ H ⊗ I_2) × (XC ⊗ I_2 ⊗ I_2) × (φ a b ⊗ GHZ) ≡ / √ 2 * / 2  .* ∣0⟩ ⊗ ∣0⟩ ⊗ ∣1⟩ ⊗ φ a b .
Proof.
intros.
unfold φ,GHZ.
operate_reduce.
Qed.

Lemma Dss1 :  forall (a b : C),
super ((I_2 ⊗ I_2 ⊗ I_2 ⊗ σZ) × (M0 ⊗ M0 ⊗ M1 ⊗ I_2) × (I_2 ⊗ H ⊗ H ⊗ I_2) × (XC ⊗ I_2 ⊗ I_2)) (density (φ a b ⊗ GHZ)) ≡ density (/ √ 2 * / 2  .* ∣0⟩ ⊗ ∣0⟩  ⊗ ∣1⟩ ⊗ φ a b).
Proof.
intros.
unfold φ,GHZ.
Time super_reduce.
Qed.

Lemma ss1' :  forall (a b : C),
(I_2 ⊗ I_2 ⊗ I_2 ⊗ σZ) × (M0 ⊗ M0 ⊗ M1 ⊗ I_2) × (I_2 ⊗ H ⊗ H ⊗ I_2) × (XC ⊗ I_2 ⊗ I_2) × (φ a b ⊗ GHZ) ≈ / √ 2 * / 2  .* ∣0⟩ ⊗ ∣0⟩ ⊗ ∣1⟩ ⊗ φ a b .
Proof.
intros.
by_den.
rewrite ss1; reflexivity.
Qed.



Lemma ss2 :  forall (a b : C),
(I_2 ⊗ I_2 ⊗ I_2 ⊗ σZ) × (M0 ⊗ M1 ⊗ M0 ⊗ I_2) × (I_2 ⊗ H ⊗ H ⊗ I_2) × (XC ⊗ I_2 ⊗ I_2) × (φ a b ⊗ GHZ) ≡ / √ 2 * / 2  .* ∣0⟩ ⊗ ∣1⟩ ⊗ ∣0⟩ ⊗  φ a b .
Proof.
intros.
unfold φ,GHZ.
operate_reduce.
Qed.

Lemma Dss2 :  forall (a b : C),
super ((I_2 ⊗ I_2 ⊗ I_2 ⊗ σZ) × (M0 ⊗ M1 ⊗ M0 ⊗ I_2) × (I_2 ⊗ H ⊗ H ⊗ I_2) × (XC ⊗ I_2 ⊗ I_2)) (density (φ a b ⊗ GHZ)) ≡ density (/ √ 2 * / 2  .* ∣0⟩ ⊗ ∣1⟩  ⊗ ∣0⟩ ⊗ φ a b).
Proof.
intros.
unfold φ,GHZ.
Time super_reduce.
Qed.

Lemma ss2' :  forall (a b : C),
(I_2 ⊗ I_2 ⊗ I_2 ⊗ σZ) × (M0 ⊗ M1 ⊗ M0 ⊗ I_2) × (I_2 ⊗ H ⊗ H ⊗ I_2) × (XC ⊗ I_2 ⊗ I_2) × (φ a b ⊗ GHZ) ≈ / √ 2 * / 2  .* ∣0⟩ ⊗ ∣1⟩ ⊗ ∣0⟩ ⊗  φ a b .
Proof.
intros.
by_den.
rewrite ss2; reflexivity.
Qed.



Lemma ss3 :  forall (a b : C),
(I_2 ⊗ I_2 ⊗ I_2 ⊗ σZ) × (I_2 ⊗ I_2 ⊗ I_2 ⊗ σZ) × (M0 ⊗ M1 ⊗ M1 ⊗ I_2) × (I_2 ⊗ H ⊗ H ⊗ I_2) × (XC ⊗ I_2 ⊗ I_2) × (φ a b ⊗ GHZ) ≡ / √ 2 * / 2  .* ∣0⟩ ⊗ ∣1⟩ ⊗ ∣1⟩ ⊗  φ a b .
Proof.
intros.
unfold φ,GHZ.
operate_reduce.
Qed.

Lemma Dss3 :  forall (a b : C),
super ((I_2 ⊗ I_2 ⊗ I_2 ⊗ σZ) × (I_2 ⊗ I_2 ⊗ I_2 ⊗ σZ) × (M0 ⊗ M1 ⊗ M1 ⊗ I_2) × (I_2 ⊗ H ⊗ H ⊗ I_2) × (XC ⊗ I_2 ⊗ I_2)) (density (φ a b ⊗ GHZ)) ≡ density (/ √ 2 * / 2  .* ∣0⟩ ⊗ ∣1⟩  ⊗ ∣1⟩ ⊗ φ a b).
Proof.
intros.
unfold φ,GHZ.
Time super_reduce.
Qed.

Lemma ss3' :  forall (a b : C),
(I_2 ⊗ I_2 ⊗ I_2 ⊗ σZ) × (I_2 ⊗ I_2 ⊗ I_2 ⊗ σZ) × (M0 ⊗ M1 ⊗ M1 ⊗ I_2) × (I_2 ⊗ H ⊗ H ⊗ I_2) × (XC ⊗ I_2 ⊗ I_2) × (φ a b ⊗ GHZ) ≈ / √ 2 * / 2  .* ∣0⟩ ⊗ ∣1⟩ ⊗ ∣1⟩ ⊗  φ a b .
Proof.
intros.
by_den.
rewrite ss3; reflexivity.
Qed.



Lemma ss4 :  forall (a b : C),
(I_2 ⊗ I_2 ⊗ I_2 ⊗ σX) × (M1 ⊗ M0 ⊗ M0 ⊗ I_2) × (I_2 ⊗ H ⊗ H ⊗ I_2) × (XC ⊗ I_2 ⊗ I_2) × (φ a b ⊗ GHZ) ≡ / √ 2 * / 2  .* ∣1⟩ ⊗ ∣0⟩ ⊗ ∣0⟩ ⊗  φ a b .
Proof.
intros.
unfold φ,GHZ.
operate_reduce.
Qed.

Lemma Dss4 :  forall (a b : C),
super ((I_2 ⊗ I_2 ⊗ I_2 ⊗ σX) × (M1 ⊗ M0 ⊗ M0 ⊗ I_2) × (I_2 ⊗ H ⊗ H ⊗ I_2) × (XC ⊗ I_2 ⊗ I_2)) (density (φ a b ⊗ GHZ)) ≡ density (/ √ 2 * / 2  .* ∣1⟩ ⊗ ∣0⟩  ⊗ ∣0⟩ ⊗ φ a b).
Proof.
intros.
unfold φ,GHZ.
Time super_reduce.
Qed.

Lemma ss4' :  forall (a b : C),
(I_2 ⊗ I_2 ⊗ I_2 ⊗ σX) × (M1 ⊗ M0 ⊗ M0 ⊗ I_2) × (I_2 ⊗ H ⊗ H ⊗ I_2) × (XC ⊗ I_2 ⊗ I_2) × (φ a b ⊗ GHZ) ≈ / √ 2 * / 2  .* ∣1⟩ ⊗ ∣0⟩ ⊗ ∣0⟩ ⊗  φ a b .
Proof.
intros.
by_den.
rewrite ss4; reflexivity.
Qed.



Lemma ss5 :  forall (a b : C),
(I_2 ⊗ I_2 ⊗ I_2 ⊗ σX) × (I_2 ⊗ I_2 ⊗ I_2 ⊗ σZ) × (M1 ⊗ M0 ⊗ M1 ⊗ I_2) × (I_2 ⊗ H ⊗ H ⊗ I_2) × (XC ⊗ I_2 ⊗ I_2) × (φ a b ⊗ GHZ) ≡ / √ 2 * / 2  .* ∣1⟩ ⊗ ∣0⟩ ⊗ ∣1⟩ ⊗  φ a b .
Proof.
intros.
unfold φ,GHZ.
operate_reduce.
Qed.

Lemma Dss5 :  forall (a b : C),
super ((I_2 ⊗ I_2 ⊗ I_2 ⊗ σX) × (I_2 ⊗ I_2 ⊗ I_2 ⊗ σZ) × (M1 ⊗ M0 ⊗ M1 ⊗ I_2) × (I_2 ⊗ H ⊗ H ⊗ I_2) × (XC ⊗ I_2 ⊗ I_2)) (density (φ a b ⊗ GHZ)) ≡ density (/ √ 2 * / 2  .* ∣1⟩ ⊗ ∣0⟩  ⊗ ∣1⟩ ⊗ φ a b).
Proof.
intros.
unfold φ,GHZ.
Time super_reduce.
Qed.

Lemma ss5' :  forall (a b : C),
(I_2 ⊗ I_2 ⊗ I_2 ⊗ σX) × (I_2 ⊗ I_2 ⊗ I_2 ⊗ σZ) × (M1 ⊗ M0 ⊗ M1 ⊗ I_2) × (I_2 ⊗ H ⊗ H ⊗ I_2) × (XC ⊗ I_2 ⊗ I_2) × (φ a b ⊗ GHZ) ≈ / √ 2 * / 2  .* ∣1⟩ ⊗ ∣0⟩ ⊗ ∣1⟩ ⊗  φ a b .
Proof.
intros.
by_den.
rewrite ss5; reflexivity.
Qed.



Lemma ss6 :  forall (a b : C),
(I_2 ⊗ I_2 ⊗ I_2 ⊗ σX) × (I_2 ⊗ I_2 ⊗ I_2 ⊗ σZ) × (M1 ⊗ M1 ⊗ M0 ⊗ I_2) × (I_2 ⊗ H ⊗ H ⊗ I_2) × (XC ⊗ I_2 ⊗ I_2) × (φ a b ⊗ GHZ) ≡ / √ 2 * / 2  .* ∣1⟩ ⊗ ∣1⟩ ⊗ ∣0⟩ ⊗  φ a b .
Proof.
intros.
unfold φ,GHZ.
operate_reduce.
Qed.

Lemma Dss6 :  forall (a b : C),
super ((I_2 ⊗ I_2 ⊗ I_2 ⊗ σX) × (I_2 ⊗ I_2 ⊗ I_2 ⊗ σZ) × (M1 ⊗ M1 ⊗ M0 ⊗ I_2) × (I_2 ⊗ H ⊗ H ⊗ I_2) × (XC ⊗ I_2 ⊗ I_2)) (density (φ a b ⊗ GHZ)) ≡ density (/ √ 2 * / 2  .* ∣1⟩ ⊗ ∣1⟩  ⊗ ∣0⟩ ⊗ φ a b).
Proof.
intros.
unfold φ,GHZ.
Time super_reduce.
Qed.

Lemma ss6' :  forall (a b : C),
(I_2 ⊗ I_2 ⊗ I_2 ⊗ σX) × (I_2 ⊗ I_2 ⊗ I_2 ⊗ σZ) × (M1 ⊗ M1 ⊗ M0 ⊗ I_2) × (I_2 ⊗ H ⊗ H ⊗ I_2) × (XC ⊗ I_2 ⊗ I_2) × (φ a b ⊗ GHZ) ≈ / √ 2 * / 2  .* ∣1⟩ ⊗ ∣1⟩ ⊗ ∣0⟩ ⊗  φ a b .
Proof.
intros.
by_den.
rewrite ss6; reflexivity.
Qed.



Lemma ss7 :  forall (a b : C),
(I_2 ⊗ I_2 ⊗ I_2 ⊗ σX) × (I_2 ⊗ I_2 ⊗ I_2 ⊗ σZ) × (I_2 ⊗ I_2 ⊗ I_2 ⊗ σZ) × (M1 ⊗ M1 ⊗ M1 ⊗ I_2) × (I_2 ⊗ H ⊗ H ⊗ I_2) × (XC ⊗ I_2 ⊗ I_2) × (φ a b ⊗ GHZ) ≡ / √ 2 * / 2  .* ∣1⟩ ⊗ ∣1⟩ ⊗ ∣1⟩ ⊗  φ a b .
Proof.
intros.
unfold φ,GHZ.
operate_reduce.
Qed.

Lemma Dss7 :  forall (a b : C),
super ((I_2 ⊗ I_2 ⊗ I_2 ⊗ σX) × (I_2 ⊗ I_2 ⊗ I_2 ⊗ σZ) × (I_2 ⊗ I_2 ⊗ I_2 ⊗ σZ) × (M1 ⊗ M1 ⊗ M1 ⊗ I_2) × (I_2 ⊗ H ⊗ H ⊗ I_2) × (XC ⊗ I_2 ⊗ I_2)) (density (φ a b ⊗ GHZ)) ≡ density (/ √ 2 * / 2  .* ∣1⟩ ⊗ ∣1⟩  ⊗ ∣1⟩ ⊗ φ a b).
Proof.
intros.
unfold φ,GHZ.
Time super_reduce.
Qed.

Lemma ss7' :  forall (a b : C),
(I_2 ⊗ I_2 ⊗ I_2 ⊗ σX) × (I_2 ⊗ I_2 ⊗ I_2 ⊗ σZ) × (I_2 ⊗ I_2 ⊗ I_2 ⊗ σZ) × (M1 ⊗ M1 ⊗ M1 ⊗ I_2) × (I_2 ⊗ H ⊗ H ⊗ I_2) × (XC ⊗ I_2 ⊗ I_2) × (φ a b ⊗ GHZ) ≈ / √ 2 * / 2  .* ∣1⟩ ⊗ ∣1⟩ ⊗ ∣1⟩ ⊗  φ a b .
Proof.
intros.
by_den.
rewrite ss7; reflexivity.
Qed.

(* 
Finished transaction in 37.559 secs (37.375u,0.046s) (successful)
Finished transaction in 48.964 secs (48.671u,0.015s) (successful)
Finished transaction in 49.244 secs (49.015u,0.015s) (successful)
Finished transaction in 60.381 secs (60.046u,0.062s) (successful)
Finished transaction in 48.188 secs (48.078u,0.s) (successful)
Finished transaction in 57.792 secs (57.484u,0.078s) (successful)
Finished transaction in 59.737 secs (59.484u,0.015s) (successful)
Finished transaction in 70.623 secs (70.234u,0.031s) (successful) *)
