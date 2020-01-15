Require Export Dirac.


Definition TOF := (B0 ⊗ B0 ⊗ I_2) .+ (B1 ⊗ B1 ⊗ I_2) .+ (B2 ⊗ B2 ⊗ I_2) .+ (B3 ⊗ B3 ⊗ σX).
Definition GPS := 2 .* (B0 ⊗ B0) .+ (-1) .* (I_2 ⊗ I_2).

Definition φ0 := ∣0⟩ ⊗ ∣0⟩ ⊗ ∣1⟩.
Definition φ1 := (H ⊗ H ⊗ H) × φ0.
Definition φ2 := TOF × φ1.
Definition φ3 := (H ⊗ H ⊗ I_2) × φ2.
Definition φ4 := (GPS ⊗ I_2) × φ3.
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
rewrite Mplus_assoc.
repeat rewrite <- Mscale_plus_distr_l.
reduce_scale.
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

Lemma step4 : φ4 ≡ ∣-⟩ ⊗ ∣-⟩ ⊗ ∣-⟩.
Proof.
unfold φ4.
rewrite step3.
unfold GPS.
operate_reduce.
unified_base.
Admitted.

Lemma step5 : φ5 ≡ ∣1⟩ ⊗ ∣1⟩ ⊗ ∣1⟩.
Proof.
unfold φ5.
rewrite step4.
operate_reduce.
Qed.

Lemma ll : / √ 2 * (2 * / √ 2 * / √ 2 * / √ 2) = /2 .
Proof.
repeat (rewrite Cmult_comm;
rewrite <- Cmult_assoc;
autorewrite with C_db).
auto.
Qed.


Lemma Grover_2_4 : (H ⊗ H ⊗ H) × (GPS ⊗ I_2) ×  (H ⊗ H ⊗ I_2) × TOF × (H ⊗ H ⊗ H) × (∣0⟩ ⊗ ∣0⟩ ⊗ ∣1⟩) ≡ ∣1⟩ ⊗ ∣1⟩ ⊗ ∣1⟩.
Proof.
unfold TOF,GPS.
operate_reduce.
rewrite ll.
Admitted.
