Require Export Dirac.


(*Step-by-step*)

(*Vector*)

Definition state0 := ∣0⟩ ⊗ ∣0⟩.
Definition state1 := (H ⊗ I_2) × state0.
Definition state2 := CX × state1.

Lemma pre_bell00 : bell00 = state2.
Proof.
unfold state2,state1,state0,bell00.
operate_reduce.
Qed.


Definition φ0 := ∣+⟩ ⊗ bell00.
Definition φ1 := (CX ⊗ I_2) × φ0.
Definition φ2 := (H ⊗ I_2 ⊗ I_2) × φ1.


Lemma step1 : φ1 = /2 .*  (∣0⟩ ⊗ ∣0⟩ ⊗ ∣0⟩) .+ /2 .*  (∣0⟩ ⊗ ∣1⟩ ⊗ ∣1⟩) .+ /2 .*  (∣1⟩ ⊗ ∣1⟩ ⊗ ∣0⟩) .+ /2 .*  (∣1⟩ ⊗ ∣0⟩ ⊗ ∣1⟩).
Proof.
unfold φ1,φ0,bell00.
autounfold with G2_db.
operate_reduce.
Qed.

Lemma step2 : φ2 = / 2 .* (∣+⟩ ⊗ (∣0⟩ ⊗ ∣0⟩))  .+ / 2 .* (∣+⟩ ⊗ (∣1⟩ ⊗ ∣1⟩))
                                .+ / 2 .* (∣-⟩ ⊗ (∣1⟩ ⊗ ∣0⟩))  .+ / 2 .* (∣-⟩ ⊗ (∣0⟩ ⊗ ∣1⟩)) .
Proof.
unfold φ2.
rewrite step1.
operate_reduce.
Qed.


Lemma step2' : φ2 = / 2 .* (∣+⟩ ⊗ (∣0⟩ ⊗ ∣0⟩))  .+ / 2 .* (∣+⟩ ⊗ (∣1⟩ ⊗ ∣1⟩))
                                .+ / 2 .* (∣-⟩ ⊗ (∣1⟩ ⊗ ∣0⟩))  .+ / 2 .* (∣-⟩ ⊗ (∣0⟩ ⊗ ∣1⟩)) .
Proof.
unfold φ2,φ1,φ0.
unfold CX,bell00.
operate_reduce.
Qed.


Definition φ30 := (M0 ⊗ M0 ⊗ I_2) × φ2.
Definition φ31 := (M0 ⊗ M1 ⊗ I_2) × φ2.
Definition φ32 := (M1 ⊗ M0 ⊗ I_2) × φ2.
Definition φ33 := (M1 ⊗ M1 ⊗ I_2) × φ2.


Lemma step30 : φ30 = / 2  .* (∣0⟩ ⊗ ∣0⟩ ⊗ (/√2 .* ∣0⟩ .+ /√2 .* ∣1⟩)).
Proof.
unfold φ30.
rewrite step2.
operate_reduce.
Qed.

Lemma step31 : φ31 = / 2  .* (∣0⟩ ⊗ ∣1⟩) ⊗ (/√2 .* ∣1⟩ .+ /√2 .* ∣0⟩).
Proof.
unfold φ31.
rewrite step2.
operate_reduce.
Qed.

Lemma step32 : φ32 = / 2  .* (∣1⟩ ⊗ ∣0⟩) ⊗ (/√2 .* ∣0⟩ .+ -/√2 .* ∣1⟩).
Proof.
unfold φ32.
rewrite step2.
operate_reduce.
Qed.

Lemma step33 : φ33 = / 2  .* (∣1⟩ ⊗ ∣1⟩) ⊗ (/√2 .* ∣1⟩ .+ -/√2 .* ∣0⟩).
Proof.
unfold φ33.
rewrite step2.
operate_reduce.
Qed.


Definition φ40 := φ30.
Definition φ41 := (I_2 ⊗ I_2 ⊗ σX) × φ31.
Definition φ42 := (I_2 ⊗ I_2 ⊗ σZ) × φ32.

Lemma step40 : φ40 = / 2  .* (∣0⟩ ⊗ ∣0⟩ ⊗ ∣+⟩).
Proof.
unfold φ40.
rewrite step30.
auto.
Qed.

Lemma step41 : φ41 = / 2  .* (∣0⟩ ⊗ ∣1⟩ ⊗ ∣+⟩).
Proof.
unfold φ41.
rewrite step31.
operate_reduce.
Qed.

Lemma step42 : φ42 = / 2  .* (∣1⟩ ⊗ ∣0⟩ ⊗ ∣+⟩).
Proof.
unfold φ42.
rewrite step32.
operate_reduce.
Qed.

Definition φ43 := (I_2 ⊗ I_2 ⊗ σZ) × (I_2 ⊗ I_2 ⊗ σX) × φ33.
Lemma step43 : φ43 = / 2  .* (∣1⟩ ⊗ ∣1⟩ ⊗ ∣+⟩).
Proof.
unfold φ43.
rewrite step33.
operate_reduce.
Qed.

Definition φ431 := (I_2 ⊗ I_2 ⊗ σX) × φ33.
Lemma step431 : φ431 = / 2  .* (∣1⟩ ⊗ ∣1⟩) ⊗ (/√2 .* ∣0⟩ .+ -/ √ 2  .* ∣1⟩).
Proof.
unfold φ431.
rewrite step33.
operate_reduce.
Qed.

Definition φ432 := (I_2 ⊗ I_2 ⊗ σZ) × φ431.
Lemma step432 : φ432 = / 2  .* (∣1⟩ ⊗ ∣1⟩) ⊗ ∣+⟩.
Proof.
unfold φ432.
rewrite step431.
operate_reduce.
Qed.


(*Density*)

Definition s0 := ∣0⟩ ⊗ ∣0⟩.
Definition s1 := (H ⊗ I_2) × s0.
Definition s2 := CX × s1.


Lemma pre_bell00' :  super (H ⊗ I_2) ((∣0⟩ ⊗ ∣0⟩) × (∣0⟩ ⊗ ∣0⟩)†) = (∣+⟩ ⊗ ∣0⟩) × (∣+⟩ ⊗ ∣0⟩)†.
Proof.
unfold  super,bell00.
super_reduce.
Qed.

Lemma pre_bell00'' :  super CX ((∣+⟩ ⊗ ∣0⟩) × (∣+⟩ ⊗ ∣0⟩)†) = bell00 × bell00†.
Proof.
unfold  super,bell00.
super_reduce.
Qed.


(*Density matrix*)

Definition ρ0 := φ0 × φ0†.
Definition ρ1 := super (CX ⊗ I_2) ρ0.
Definition ρ2 := super (H ⊗ I_2 ⊗ I_2) ρ1.

Lemma Dstep1 : ρ1 = φ1 × φ1†.
Proof.
unfold ρ1,ρ0,super.
super_reduce.
Qed.

Lemma Dstep2 : ρ2 = φ2 × φ2†.
Proof.
unfold ρ2,super.
rewrite Dstep1.
super_reduce.
Qed.


Definition ρ30 := super (M0 ⊗ M0 ⊗ I_2) ρ2.
Definition ρ31 := super (M0 ⊗ M1 ⊗ I_2) ρ2.
Definition ρ32 := super (M1 ⊗ M0 ⊗ I_2) ρ2.
Definition ρ33 := super (M1 ⊗ M1 ⊗ I_2) ρ2.


Lemma Dstep30 : ρ30 = φ30 × φ30†.
Proof.
unfold ρ30,super.
rewrite Dstep2.
super_reduce.
Qed.

Lemma Dstep31 : ρ31 = φ31 × φ31†.
Proof.
unfold ρ31,super.
rewrite Dstep2.
super_reduce.
Qed.

Lemma Dstep32 : ρ32 = φ32 × φ32†.
Proof.
unfold ρ32,super.
rewrite Dstep2.
super_reduce.
Qed.

Lemma Dstep33 : ρ33 = φ33 × φ33†.
Proof.
unfold ρ33,super.
rewrite Dstep2.
super_reduce.
Qed.


Definition ρ40 := ρ30.
Definition ρ41 := super (I_2 ⊗ I_2 ⊗ σX) ρ31.
Definition ρ42 := super (I_2 ⊗ I_2 ⊗ σZ) ρ32.

Lemma Dstep40 : ρ40 = φ40 × φ40†.
Proof.
unfold ρ40,super.
rewrite Dstep30.
auto.
Qed.

Lemma Dstep41 : ρ41 = φ41 × φ41†.
Proof.
unfold ρ41,super.
rewrite Dstep31.
super_reduce.
Qed.

Lemma Dstep42 : ρ42 = φ42 × φ42†.
Proof.
unfold ρ42,super.
rewrite Dstep32.
super_reduce.
Qed.


Definition ρ43 := super ((I_2 ⊗ I_2 ⊗ σZ) × (I_2 ⊗ I_2 ⊗ σX))  ρ33.
Lemma Dstep43 : ρ43 = φ43 × φ43†.
Proof.
unfold ρ43,super.
rewrite Dstep33.
super_reduce.
Qed.

Definition ρ431 := super (I_2 ⊗ I_2 ⊗ σX) ρ33.
Lemma Dstep431 : ρ431 = φ431 × φ431†.
Proof.
unfold ρ431,super.
rewrite Dstep33.
super_reduce.
Qed.

Definition ρ432 := super (I_2 ⊗ I_2 ⊗ σZ) ρ431.
Lemma Dstep432 : ρ432 = φ432 × φ432†.
Proof.
unfold ρ432,super.
rewrite Dstep431.
super_reduce.
Qed.


(*One-time*)

Definition φ40' := (M0 ⊗ M0 ⊗ I_2) × (H ⊗ I_2 ⊗ I_2) × (CX ⊗ I_2) × φ0.
Lemma tele0 : φ40' = / 2  .* (∣0⟩ ⊗ ∣0⟩ ⊗ ∣+⟩).
Proof.
unfold φ40'.
unfold φ0.
unfold bell00.
operate_reduce.
Qed.

Definition φ41' := (I_2 ⊗ I_2 ⊗ σX) × (M0 ⊗ M1 ⊗ I_2) × (H ⊗ I_2 ⊗ I_2) × (CX ⊗ I_2) × φ0.
Lemma tele1 : φ41' = / 2  .* (∣0⟩ ⊗ ∣1⟩ ⊗ ∣+⟩).
Proof.
unfold φ41'.
unfold φ0.
unfold bell00.
operate_reduce.
Qed.

Definition φ42' := (I_2 ⊗ I_2 ⊗ σZ) × (M1 ⊗ M0 ⊗ I_2) × (H ⊗ I_2 ⊗ I_2) × (CX ⊗ I_2) × φ0.
Lemma tele2 : φ42' = / 2  .* (∣1⟩ ⊗ ∣0⟩ ⊗ ∣+⟩).
Proof.
unfold φ42'.
unfold φ0.
unfold bell00.
operate_reduce.
Qed.

Definition φ43' := (I_2 ⊗ I_2 ⊗ σZ) × (I_2 ⊗ I_2 ⊗ σX) × (M1 ⊗ M1 ⊗ I_2) × (H ⊗ I_2 ⊗ I_2) × (CX ⊗ I_2) × φ0.
Lemma tele3 : φ43' = / 2  .* (∣1⟩ ⊗ ∣1⟩ ⊗ ∣+⟩).
Proof.
unfold φ43'.
unfold φ0.
unfold bell00.
operate_reduce.
Qed.


Lemma Dtele0 : super ((M0 ⊗ M0 ⊗ I_2) × (H ⊗ I_2 ⊗ I_2) × (CX ⊗ I_2)) ρ0 = φ40' × φ40'†.
Proof.
unfold ρ0.
unfold super.
super_reduce.
Qed.

Lemma Dtele1 : super ((I_2 ⊗ I_2 ⊗ σX) × (M0 ⊗ M1 ⊗ I_2) × (H ⊗ I_2 ⊗ I_2) × (CX ⊗ I_2)) ρ0 = φ41' × φ41'†.
Proof.
unfold ρ0.
unfold super.
super_reduce.
Qed.

Lemma Dtele2 : super ((I_2 ⊗ I_2 ⊗ σZ) × (M1 ⊗ M0 ⊗ I_2) × (H ⊗ I_2 ⊗ I_2) × (CX ⊗ I_2)) ρ0 = φ42' × φ42'†.
Proof.
unfold ρ0.
unfold super.
super_reduce.
Qed.

Lemma Dtele3 : super ((I_2 ⊗ I_2 ⊗ σZ) × (I_2 ⊗ I_2 ⊗ σX) × (M1 ⊗ M1 ⊗ I_2) × (H ⊗ I_2 ⊗ I_2) × (CX ⊗ I_2)) ρ0 = φ43' × φ43'†.
Proof.
unfold ρ0.
unfold super.
super_reduce.
Qed.

Lemma coefficient : forall a: C, / √ 2 * (/ √ 2 * a) = a */2 .
Proof.
intros.
rewrite Cmult_assoc.
autorewrite with C_db.
rewrite Cmult_comm. auto.
Qed.

Definition φ (a b : C) : Vector 2 := a .* ∣0⟩ .+ b .* ∣1⟩.
Lemma tele0' :  forall (a b : C),
(M0 ⊗ M0 ⊗ I_2) × (H ⊗ I_2 ⊗ I_2) × (CX ⊗ I_2) × (φ a b⊗ bell00) = / 2  .* ∣0⟩ ⊗ ∣0⟩ ⊗ (φ a b) .
Proof.
intros. unfold bell00,φ.
operate_reduce.
rewrite Cmult_comm.
rewrite coefficient;auto.
rewrite coefficient;auto.
Qed.


