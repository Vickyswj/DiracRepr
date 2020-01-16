Require Export Dirac.

Definition φ0 := ∣0⟩ ⊗ ∣1⟩.
Definition φ1 := (H ⊗ H) × φ0.
Definition φ2 := CX × φ1.
Definition φ3 := (H ⊗ I_2) × φ2.

Lemma step1 : φ1 ≡ ∣+⟩ ⊗ ∣-⟩.
Proof.
unfold φ1,φ0.
operate_reduce.
Qed.

Lemma step2 : φ2 ≡ ∣-⟩ ⊗ ∣-⟩.
Proof.
unfold φ2.
rewrite step1.
operate_reduce.
unified_base.
Qed.


Lemma step3 : φ3 ≡ ∣1⟩ ⊗ ∣-⟩.
Proof.
unfold φ3.
rewrite step2.
operate_reduce.
Qed.



Lemma tele0 : (H ⊗ I_2) × CX × (H ⊗ H) × (∣0⟩ ⊗ ∣1⟩) ≡ ∣1⟩ ⊗ ∣-⟩ .
Proof.
operate_reduce.
unified_base.
rewrite
Qed.

















