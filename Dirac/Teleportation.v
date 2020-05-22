Require Export Dirac.
Require Export StateAndOperator.
Declare Scope QE.
Local Open Scope QE.


Definition bell00 := /√2 .* (∣0,0⟩) .+ /√2 .* (∣1,1⟩).
Definition bell01 := /√2 .* (∣0,1⟩) .+ /√2 .* (∣1,0⟩).
Definition bell10 := /√2 .* (∣0,0⟩) .+ (-/√2) .* (∣1,1⟩).
Definition bell11 := /√2 .* (∣0,1⟩) .+ (-/√2) .* (∣1,0⟩).

(* Step-by-step *)

(* Vector *)
Definition state0 := ∣0,0⟩.
Definition state1 := (H ⊗ I_2) × state0.
Definition state2 := CX × state1.

Lemma pre_bell00 : bell00 ≡ state2.
Proof.
unfold state2,state1,state0,bell00.
operate_reduce.
Qed.

Definition φ0 := ∣+⟩ ⊗ bell00.
Definition φ1 := (CX ⊗ I_2) × φ0.
Definition φ2 := (H ⊗ I_2 ⊗ I_2) × φ1.

Lemma step1 : φ1 ≡ /2 .*  (∣0,0,0⟩) .+ /2 .*  (∣0,1,1⟩) .+ /2 .*  (∣1,1,0⟩) .+ /2 .*  (∣1,0,1⟩).
Proof.
unfold φ1,φ0,bell00.
operate_reduce.
Qed.

Lemma step2 : φ2 ≡ / 2 .* (∣+⟩ ⊗ (∣0⟩ ⊗ ∣0⟩))  .+ / 2 .* (∣+⟩ ⊗ (∣1⟩ ⊗ ∣1⟩))
                                .+ / 2 .* (∣-⟩ ⊗ (∣1⟩ ⊗ ∣0⟩))  .+ / 2 .* (∣-⟩ ⊗ (∣0⟩ ⊗ ∣1⟩)) .
Proof.
unfold φ2.
rewrite step1.
operate_reduce.
Qed.

Lemma step2' : φ2 ≡ / 2 .* (∣+⟩ ⊗ (∣0⟩ ⊗ ∣0⟩))  .+ / 2 .* (∣+⟩ ⊗ (∣1⟩ ⊗ ∣1⟩))
                                .+ / 2 .* (∣-⟩ ⊗ (∣1⟩ ⊗ ∣0⟩))  .+ / 2 .* (∣-⟩ ⊗ (∣0⟩ ⊗ ∣1⟩)) .
Proof.
unfold φ2,φ1,φ0,bell00.
operate_reduce.
Qed.


Definition φ30 := (M0 ⊗ M0 ⊗ I_2) × φ2.
Definition φ31 := (M0 ⊗ M1 ⊗ I_2) × φ2.
Definition φ32 := (M1 ⊗ M0 ⊗ I_2) × φ2.
Definition φ33 := (M1 ⊗ M1 ⊗ I_2) × φ2.


Lemma step30 : φ30 ≡  / 2  .* (∣0⟩ ⊗ ∣0⟩ ⊗ (/√2 .* ∣0⟩ .+ /√2 .* ∣1⟩)).
Proof.
unfold φ30.
rewrite step2.
operate_reduce.
Qed.

Lemma step31 : φ31 ≡ / 2  .* (∣0⟩ ⊗ ∣1⟩) ⊗ (/√2 .* ∣1⟩ .+ /√2 .* ∣0⟩).
Proof.
unfold φ31.
rewrite step2.
operate_reduce.
Qed.

Lemma step32 : φ32 ≡ / 2  .* (∣1⟩ ⊗ ∣0⟩) ⊗ (/√2 .* ∣0⟩ .+ -/√2 .* ∣1⟩).
Proof.
unfold φ32.
rewrite step2.
operate_reduce.
Qed.

Lemma step33 : φ33 ≡ / 2  .* (∣1⟩ ⊗ ∣1⟩) ⊗ (/√2 .* ∣1⟩ .+ -/√2 .* ∣0⟩).
Proof.
unfold φ33.
rewrite step2.
operate_reduce.
Qed.


Definition φ40 := φ30.
Definition φ41 := (I_2 ⊗ I_2 ⊗ σX) × φ31.
Definition φ42 := (I_2 ⊗ I_2 ⊗ σZ) × φ32.

Lemma step40 : φ40 ≡ / 2  .* (∣0⟩ ⊗ ∣0⟩ ⊗ ∣+⟩).
Proof.
unfold φ40.
rewrite step30.
reflexivity.
Qed.

Lemma step41 : φ41 ≡ / 2  .* (∣0⟩ ⊗ ∣1⟩ ⊗ ∣+⟩).
Proof.
unfold φ41.
rewrite step31.
operate_reduce.
Qed.

Lemma step42 : φ42 ≡ / 2  .* (∣1⟩ ⊗ ∣0⟩ ⊗ ∣+⟩).
Proof.
unfold φ42.
rewrite step32.
operate_reduce.
Qed.

Definition φ43 := (I_2 ⊗ I_2 ⊗ σZ) × (I_2 ⊗ I_2 ⊗ σX) × φ33.
Lemma step43 : φ43 ≡ / 2  .* (∣1⟩ ⊗ ∣1⟩ ⊗ ∣+⟩).
Proof.
unfold φ43.
rewrite step33.
operate_reduce.
Qed.

Definition φ431 := (I_2 ⊗ I_2 ⊗ σX) × φ33.
Lemma step431 : φ431 ≡ / 2  .* (∣1⟩ ⊗ ∣1⟩) ⊗ (/√2 .* ∣0⟩ .+ -/ √ 2  .* ∣1⟩).
Proof.
unfold φ431.
rewrite step33.
operate_reduce.
Qed.

Definition φ432 := (I_2 ⊗ I_2 ⊗ σZ) × φ431.
Lemma step432 : φ432 ≡ / 2  .* (∣1⟩ ⊗ ∣1⟩) ⊗ ∣+⟩.
Proof.
unfold φ432.
rewrite step431.
operate_reduce.
Qed.



(* Density *)
Definition s0 := ∣0⟩ ⊗ ∣0⟩.
Definition s1 := (H ⊗ I_2) × s0.
Definition s2 := CX × s1.


Lemma pre_bell00'' :  super CX (density (∣+⟩ ⊗ ∣0⟩)) ≡ density bell00.
Proof.
unfold super,bell00.
super_reduce.
Qed.


Definition ρ0 := density φ0.
Definition ρ1 := super (CX ⊗ I_2) ρ0.
Definition ρ2 := super (H ⊗ I_2 ⊗ I_2) ρ1.

Lemma Dstep1 : ρ1 ≡ density φ1.
Proof.
unfold ρ1,ρ0,super.
super_reduce.
Qed.

Lemma Dstep2 : ρ2 ≡ density φ2.
Proof.
unfold ρ2,super.
rewrite Dstep1.
super_reduce.
Qed.


Definition ρ30 := super (M0 ⊗ M0 ⊗ I_2) ρ2.
Definition ρ31 := super (M0 ⊗ M1 ⊗ I_2) ρ2.
Definition ρ32 := super (M1 ⊗ M0 ⊗ I_2) ρ2.
Definition ρ33 := super (M1 ⊗ M1 ⊗ I_2) ρ2.


Lemma Dstep30 : ρ30 ≡ density φ30.
Proof.
unfold ρ30,super.
rewrite Dstep2.
super_reduce.
Qed.

Lemma Dstep31 : ρ31 ≡ density φ31.
Proof.
unfold ρ31,super.
rewrite Dstep2.
super_reduce.
Qed.

Lemma Dstep32 : ρ32 ≡ density φ32.
Proof.
unfold ρ32,super.
rewrite Dstep2.
super_reduce.
Qed.

Lemma Dstep33 : ρ33 ≡ density φ33.
Proof.
unfold ρ33,super.
rewrite Dstep2.
super_reduce.
Qed.


Definition ρ40 := ρ30.
Definition ρ41 := super (I_2 ⊗ I_2 ⊗ σX) ρ31.
Definition ρ42 := super (I_2 ⊗ I_2 ⊗ σZ) ρ32.

Lemma Dstep40 : ρ40 ≡ density φ40.
Proof.
unfold ρ40,super.
rewrite Dstep30.
reflexivity.
Qed.

Lemma Dstep41 : ρ41 ≡ density φ41.
Proof.
unfold ρ41,super.
rewrite Dstep31.
super_reduce.
Qed.

Lemma Dstep42 : ρ42 ≡ density φ42.
Proof.
unfold ρ42,super.
rewrite Dstep32.
super_reduce.
Qed.


Definition ρ43 := super ((I_2 ⊗ I_2 ⊗ σZ) × (I_2 ⊗ I_2 ⊗ σX))  ρ33.
Lemma Dstep43 : ρ43 ≡ density φ43.
Proof.
unfold ρ43,super.
rewrite Dstep33.
super_reduce.
Qed.

Definition ρ431 := super (I_2 ⊗ I_2 ⊗ σX) ρ33.
Lemma Dstep431 : ρ431 ≡ density φ431.
Proof.
unfold ρ431,super.
rewrite Dstep33.
super_reduce.
Qed.

Definition ρ432 := super (I_2 ⊗ I_2 ⊗ σZ) ρ431.
Lemma Dstep432 : ρ432 ≡ density φ432.
Proof.
unfold ρ432,super.
rewrite Dstep431.
super_reduce.
Qed.



(* One-time *)
(* Vector *)

(* Definition φ40' := (M0 ⊗ M0 ⊗ I_2) × (H ⊗ I_2 ⊗ I_2) × (CX ⊗ I_2) × φ0.
Lemma tele0 : φ40' ≡ / 2  .* (∣0⟩ ⊗ ∣0⟩ ⊗ ∣+⟩). *)
Lemma tele0'' : (M0 ⊗ M0 ⊗ I_2) × (H ⊗ I_2 ⊗ I_2) × (CX ⊗ I_2) × φ0 ≡ / 2  .* (∣0⟩ ⊗ ∣0⟩ ⊗ ∣+⟩).
Proof.
unfold φ0,bell00.
operate_reduce.
Qed.

Lemma tele1'' : (I_2 ⊗ I_2 ⊗ σX) × (M0 ⊗ M1 ⊗ I_2) × (H ⊗ I_2 ⊗ I_2) × (CX ⊗ I_2) × φ0 ≡ / 2  .* (∣0⟩ ⊗ ∣1⟩ ⊗ ∣+⟩).
Proof.
unfold φ0,bell00.
operate_reduce.
Qed.

Lemma tele2'' :  (I_2 ⊗ I_2 ⊗ σZ) × (M1 ⊗ M0 ⊗ I_2) × (H ⊗ I_2 ⊗ I_2) × (CX ⊗ I_2) × φ0 ≡ / 2  .* (∣1⟩ ⊗ ∣0⟩ ⊗ ∣+⟩).
Proof.
unfold φ0,bell00.
operate_reduce.
Qed.

Lemma tele3'' : (I_2 ⊗ I_2 ⊗ σZ) × (I_2 ⊗ I_2 ⊗ σX) × (M1 ⊗ M1 ⊗ I_2) × (H ⊗ I_2 ⊗ I_2) × (CX ⊗ I_2) × φ0 ≡ / 2  .* (∣1⟩ ⊗ ∣1⟩ ⊗ ∣+⟩).
Proof.
unfold φ0,bell00.
operate_reduce.
Qed.


(* Density *)
Lemma Dtele0'' : super ((M0 ⊗ M0 ⊗ I_2) × (H ⊗ I_2 ⊗ I_2) × (CX ⊗ I_2)) ρ0 ≡ density (/ 2  .* (∣0⟩ ⊗ ∣0⟩ ⊗ ∣+⟩)).
Proof.
unfold ρ0,φ0,bell00,super.
super_reduce.
Qed.

Lemma Dtelel'' : super ((I_2 ⊗ I_2 ⊗ σX) × (M0 ⊗ M1 ⊗ I_2) × (H ⊗ I_2 ⊗ I_2) × (CX ⊗ I_2)) ρ0 ≡ density (/ 2  .* (∣0⟩ ⊗ ∣1⟩ ⊗ ∣+⟩)).
Proof.
unfold ρ0,φ0,bell00,super.
super_reduce.
Qed.

Lemma Dtele2'' : super ((I_2 ⊗ I_2 ⊗ σZ) × (M1 ⊗ M0 ⊗ I_2) × (H ⊗ I_2 ⊗ I_2) × (CX ⊗ I_2)) ρ0 ≡ density (/ 2  .* (∣1⟩ ⊗ ∣0⟩ ⊗ ∣+⟩)).
Proof.
unfold ρ0,φ0,bell00,super.
super_reduce.
Qed.

Lemma Dtele3'' : super ((I_2 ⊗ I_2 ⊗ σZ) × (I_2 ⊗ I_2 ⊗ σX) × (M1 ⊗ M1 ⊗ I_2) × (H ⊗ I_2 ⊗ I_2) × (CX ⊗ I_2)) ρ0 ≡ density (/ 2  .* (∣1⟩ ⊗ ∣1⟩ ⊗ ∣+⟩)).
Proof.
unfold ρ0,φ0,bell00,super.
super_reduce.
Qed.



(* parameterize *)
Definition φ (a b : C) : Vector 2 := a .* ∣0⟩ .+ b .* ∣1⟩.

Lemma tele0 :  forall (a b : C),
(M0 ⊗ M0 ⊗ I_2) × (H ⊗ I_2 ⊗ I_2) × (CX ⊗ I_2) × ((φ a b) ⊗ bell00) ≡ / 2  .* ∣0⟩ ⊗ ∣0⟩ ⊗ (φ a b).
Proof.
intros.
unfold φ,bell00.
operate_reduce.
Qed.

Lemma Dtele0 :  forall (a b : C),
super ((M0 ⊗ M0 ⊗ I_2) × (H ⊗ I_2 ⊗ I_2) × (CX ⊗ I_2)) (density ((φ a b) ⊗ bell00)) ≡ density (/ 2  .* ∣0⟩ ⊗ ∣0⟩ ⊗ (φ a b)).
Proof.
intros.
unfold φ,bell00.
super_reduce.
Qed.

Lemma tele0' :  forall (a b : C),
(M0 ⊗ M0 ⊗ I_2) × (H ⊗ I_2 ⊗ I_2) × (CX ⊗ I_2) × ((φ a b) ⊗ bell00) ≈ / 2  .* ∣0⟩ ⊗ ∣0⟩ ⊗ (φ a b) .
Proof.
intros.
by_den.
rewrite tele0; reflexivity.
Qed.



Lemma tele1 :  forall (a b : C),
(I_2 ⊗ I_2 ⊗ σX) × (M0 ⊗ M1 ⊗ I_2) × (H ⊗ I_2 ⊗ I_2) × (CX ⊗ I_2) × ((φ a b) ⊗ bell00) ≡ / 2  .* ∣0⟩ ⊗ ∣1⟩ ⊗ (φ a b) .
Proof.
intros.
unfold φ,bell00.
operate_reduce.
Qed.

Lemma Dtele1 :  forall (a b : C),
super ((I_2 ⊗ I_2 ⊗ σX) × (M0 ⊗ M1 ⊗ I_2) × (H ⊗ I_2 ⊗ I_2) × (CX ⊗ I_2)) (density ((φ a b) ⊗ bell00)) ≡ density (/ 2  .* ∣0⟩ ⊗ ∣1⟩ ⊗ (φ a b)).
Proof.
intros.
unfold φ,bell00.
super_reduce.
Qed.

Lemma tele1' :  forall (a b : C),
(I_2 ⊗ I_2 ⊗ σX) × (M0 ⊗ M1 ⊗ I_2) × (H ⊗ I_2 ⊗ I_2) × (CX ⊗ I_2) × ((φ a b) ⊗ bell00) ≈ / 2  .* ∣0⟩ ⊗ ∣1⟩ ⊗ (φ a b) .
Proof.
intros.
by_den.
rewrite tele1; reflexivity.
Qed.



Lemma tele2 :  forall (a b : C),
(I_2 ⊗ I_2 ⊗ σZ) × (M1 ⊗ M0 ⊗ I_2) × (H ⊗ I_2 ⊗ I_2) × (CX ⊗ I_2) × ((φ a b) ⊗ bell00) ≡ / 2  .* ∣1⟩ ⊗ ∣0⟩ ⊗ (φ a b) .
Proof.
intros.
unfold φ,bell00.
operate_reduce.
Qed.

Lemma Dtele2 :  forall (a b : C),
super ((I_2 ⊗ I_2 ⊗ σZ) × (M1 ⊗ M0 ⊗ I_2) × (H ⊗ I_2 ⊗ I_2) × (CX ⊗ I_2)) (density ((φ a b) ⊗ bell00)) ≡ density (/ 2  .* ∣1⟩ ⊗ ∣0⟩ ⊗ (φ a b)).
Proof.
intros.
unfold φ,bell00.
super_reduce.
Qed.

Lemma tele2' :  forall (a b : C),
(I_2 ⊗ I_2 ⊗ σZ) × (M1 ⊗ M0 ⊗ I_2) × (H ⊗ I_2 ⊗ I_2) × (CX ⊗ I_2) × ((φ a b) ⊗ bell00) ≈ / 2  .* ∣1⟩ ⊗ ∣0⟩ ⊗ (φ a b) .
Proof.
intros.
by_den.
rewrite tele2; reflexivity.
Qed.


Lemma tele3 :  forall (a b : C),
(I_2 ⊗ I_2 ⊗ σZ) × (I_2 ⊗ I_2 ⊗ σX) × (M1 ⊗ M1 ⊗ I_2) × (H ⊗ I_2 ⊗ I_2) × (CX ⊗ I_2) × ((φ a b) ⊗ bell00) ≡ / 2  .* ∣1⟩ ⊗ ∣1⟩ ⊗ (φ a b) .
Proof.
intros.
unfold φ,bell00.
operate_reduce.
Qed.

Lemma Dtele3 :  forall (a b : C),
super ((I_2 ⊗ I_2 ⊗ σZ) × (I_2 ⊗ I_2 ⊗ σX) × (M1 ⊗ M1 ⊗ I_2) × (H ⊗ I_2 ⊗ I_2) × (CX ⊗ I_2)) (density ((φ a b) ⊗ bell00)) ≡ density (/ 2  .* ∣1⟩ ⊗ ∣1⟩ ⊗ (φ a b)).
Proof.
intros.
unfold φ,bell00.
super_reduce.
Qed.

Lemma tele3' :  forall (a b : C),
(I_2 ⊗ I_2 ⊗ σZ) × (I_2 ⊗ I_2 ⊗ σX) × (M1 ⊗ M1 ⊗ I_2) × (H ⊗ I_2 ⊗ I_2) × (CX ⊗ I_2) × ((φ a b) ⊗ bell00) ≈ / 2  .* ∣1⟩ ⊗ ∣1⟩ ⊗ (φ a b) .
Proof.
intros.
by_den.
rewrite tele3; reflexivity.
Qed.

