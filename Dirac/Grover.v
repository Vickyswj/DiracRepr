Require Export Dirac.

(*Search space 4 and query for 4 *)

(*Step-by-step*)

(*Vector*)
Definition TOF := (B0 ⊗ B0 ⊗ I_2) .+ (B1 ⊗ B1 ⊗ I_2) .+ (B2 ⊗ B2 ⊗ I_2) .+ (B3 ⊗ B3 ⊗ σX).
Definition GPS := 2 .* B0 .+ (-1) .* I_2.

Definition φ0 := ∣0⟩ ⊗ ∣0⟩ ⊗ ∣1⟩.
Definition φ1 := (H ⊗ H ⊗ H) × φ0.
Definition φ2 := TOF × φ1.
Definition φ3 := (H ⊗ H ⊗ I_2) × φ2.
Definition φ4 := (GPS ⊗ GPS ⊗ I_2) × φ3.
Definition φ5 := (H ⊗ H ⊗ H) × φ4.


Lemma step1 : φ1 ≡ ∣+⟩ ⊗ ∣+⟩ ⊗ ∣-⟩.
Proof.
unfold φ1,φ0.
operate_reduce.
Qed.

Lemma step2 : φ2 ≡ ∣0⟩ ⊗ ∣0⟩ ⊗ ∣-⟩.
Proof.
unfold φ2,TOF.
rewrite step1.
operate_reduce.
Qed.

Lemma step3 : φ3 ≡ ∣+⟩ ⊗ ∣+⟩ ⊗ ∣-⟩.
Proof.
unfold φ3.
rewrite step2.
operate_reduce.
Qed.

Lemma coefficient : forall a: C, / √ 2 * a * / √ 2 = a */2 .
Proof.
intros.
rewrite Cmult_comm.
rewrite Cmult_assoc.
autorewrite with C_db.
rewrite Cmult_comm. auto.
Qed.


Lemma C2 : 2 * 2 * / √ 2 * / √ 2 = 2.
Proof.
rewrite <- Cmult_assoc.
autorewrite with C_db.
lca.
Qed.

Lemma C1 : 2 * / √ 2 * / √ 2 * / √ 2 = / √ 2 .
Proof.
rewrite <- Cmult_assoc;autorewrite with C_db.
rewrite Cmult_comm. rewrite Cmult_assoc. autorewrite with C_db. auto.
Qed.

Hint Rewrite C1 C2 : C_db.


Lemma step4 : φ4 ≡ ∣-⟩ ⊗ ∣-⟩ ⊗ ∣-⟩.
Proof.
unfold φ4.
rewrite step3.
unfold GPS.
operate_reduce.
Qed.

Lemma step5 : φ5 ≡ ∣1⟩ ⊗ ∣1⟩ ⊗ ∣1⟩.
Proof.
unfold φ5.
rewrite step4.
operate_reduce.
Qed.


(*Density*)
Definition ρ0 := φ0 × φ0†.
Definition ρ1 := super (H ⊗ H ⊗ H) ρ0.
Definition ρ2 := super TOF ρ1.
Definition ρ3 := super  (H ⊗ H ⊗ I_2) ρ2.
Definition ρ4 := super  (GPS ⊗ GPS ⊗ I_2) ρ3.
Definition ρ5 := super  (H ⊗ H ⊗ H) ρ4.

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


(* One-time *)

Lemma Grover_2_4 : (H ⊗ H ⊗ H) × (GPS ⊗ GPS ⊗ I_2) ×  (H ⊗ H ⊗ I_2) × TOF × (H ⊗ H ⊗ H) × (∣0⟩ ⊗ ∣0⟩ ⊗ ∣1⟩) ≡ ∣1⟩ ⊗ ∣1⟩ ⊗ ∣1⟩.
Proof.
unfold TOF,GPS.
operate_reduce.
Qed.

Lemma DGrover_2_4 : super ((H ⊗ H ⊗ H) × (GPS ⊗ GPS ⊗ I_2) ×  (H ⊗ H ⊗ I_2) × TOF × (H ⊗ H ⊗ H)) ρ0 ≡ (∣1⟩ ⊗ ∣1⟩ ⊗ ∣1⟩) × (∣1⟩ ⊗ ∣1⟩ ⊗ ∣1⟩)†.
Proof.
unfold ρ0,φ0,TOF,GPS,super.
super_reduce.
Qed.

