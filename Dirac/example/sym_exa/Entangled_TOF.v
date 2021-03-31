Require Export Dirac.


Lemma t4 :
(I_2 ⊗ TOF)
× (TOF ⊗ I_2)
× (CX ⊗ I_2 ⊗ I_2)
× (H ⊗ I_2 ⊗ I_2 ⊗ I_2)
× ∣0,0,0,0⟩
≡  / √ 2 .* ∣0,0,0,0⟩  .+ / √ 2 .* ∣1,1,1,1⟩.
Proof.
Time operate_reduce.
Qed.

Lemma t5 :
(I_2 ⊗ I_2 ⊗ TOF)
× (I_2 ⊗ TOF ⊗ I_2)
× (TOF ⊗ I_2 ⊗ I_2)
× (CX ⊗ I_2 ⊗ I_2 ⊗ I_2)
× (H ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2)
× ∣0,0,0,0,0⟩
≡  / √ 2 .* ∣0,0,0,0,0⟩  .+ / √ 2 .* ∣1,1,1,1,1⟩.
Proof.
Time operate_reduce.
Qed.

Lemma t6 :
(I_2 ⊗ I_2 ⊗ I_2 ⊗ TOF)
× (I_2 ⊗ I_2 ⊗ TOF ⊗ I_2)
× (I_2 ⊗ TOF ⊗ I_2 ⊗ I_2)
× (TOF ⊗ I_2 ⊗ I_2 ⊗ I_2)
× (CX ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2)
× (H ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2)
× ∣0,0,0,0,0,0⟩
≡  / √ 2 .* ∣0,0,0,0,0,0⟩  .+ / √ 2 .* ∣1,1,1,1,1,1⟩.
Proof.
Time operate_reduce.
Qed.

Lemma t7 :
(I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ TOF)
× (I_2 ⊗ I_2 ⊗ I_2 ⊗ TOF ⊗ I_2)
× (I_2 ⊗ I_2 ⊗ TOF ⊗ I_2 ⊗ I_2)
× (I_2 ⊗ TOF ⊗ I_2 ⊗ I_2 ⊗ I_2)
× (TOF ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2)
× (CX ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2)
× (H ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2)
× ∣0,0,0,0,0,0,0⟩
≡  / √ 2 .* ∣0,0,0,0,0,0,0⟩  .+ / √ 2 .* ∣1,1,1,1,1,1,1⟩.
Proof.
Time operate_reduce.
Qed.



Lemma t8 :
(I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ TOF)
× (I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ TOF ⊗ I_2)
× (I_2 ⊗ I_2 ⊗ I_2 ⊗ TOF ⊗ I_2 ⊗ I_2)
× (I_2 ⊗ I_2 ⊗ TOF ⊗ I_2 ⊗ I_2 ⊗ I_2)
× (I_2 ⊗ TOF ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2)
× (TOF ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2)
× (CX ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2)
× (H ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2)
× ∣0,0,0,0,0,0,0,0⟩
≡  / √ 2 .* ∣0,0,0,0,0,0,0,0⟩  .+ / √ 2 .* ∣1,1,1,1,1,1,1,1⟩.
Proof.
Time operate_reduce.
Qed.

Lemma t9 :
(I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ TOF)
× (I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ TOF ⊗ I_2)
× (I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ TOF ⊗ I_2 ⊗ I_2)
× (I_2 ⊗ I_2 ⊗ I_2 ⊗ TOF ⊗ I_2 ⊗ I_2 ⊗ I_2)
× (I_2 ⊗ I_2 ⊗ TOF ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2)
× (I_2 ⊗ TOF ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2)
× (TOF ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2)
× (CX ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2)
× (H ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2)
× ∣0,0,0,0,0,0,0,0,0⟩
≡  / √ 2 .* ∣0,0,0,0,0,0,0,0,0⟩  .+ / √ 2 .* ∣1,1,1,1,1,1,1,1,1⟩.
Proof.
Time operate_reduce.
Qed.

Lemma t10 :
(I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ TOF)
× (I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ TOF ⊗ I_2)
× (I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ TOF ⊗ I_2 ⊗ I_2)
× (I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ TOF ⊗ I_2 ⊗ I_2 ⊗ I_2)
× (I_2 ⊗ I_2 ⊗ I_2 ⊗ TOF ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2)
× (I_2 ⊗ I_2 ⊗ TOF ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2)
× (I_2 ⊗ TOF ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2)
× (TOF ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2)
× (CX ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2)
× (H ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2)
× ∣0,0,0,0,0,0,0,0,0,0⟩
≡  / √ 2 .* ∣0,0,0,0,0,0,0,0,0,0⟩  .+ / √ 2 .* ∣1,1,1,1,1,1,1,1,1,1⟩.
Proof.
Time operate_reduce.
Qed.

Lemma t11 :
(I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ TOF)
× (I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ TOF ⊗ I_2)
× (I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ TOF ⊗ I_2 ⊗ I_2)
× (I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ TOF ⊗ I_2 ⊗ I_2 ⊗ I_2)
× (I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ TOF ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2)
× (I_2 ⊗ I_2 ⊗ I_2 ⊗ TOF ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2)
× (I_2 ⊗ I_2 ⊗ TOF ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2)
× (I_2 ⊗ TOF ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2)
× (TOF ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2)
× (CX ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2)
× (H ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2)
× ∣0,0,0,0,0,0,0,0,0,0,0⟩
≡  / √ 2 .* ∣0,0,0,0,0,0,0,0,0,0,0⟩  .+ / √ 2 .* ∣1,1,1,1,1,1,1,1,1,1,1⟩.
Proof.
Time operate_reduce.
Qed.

Lemma t12:
(I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ TOF)
× (I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ TOF ⊗ I_2)
× (I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ TOF ⊗ I_2 ⊗ I_2)
× (I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ TOF ⊗ I_2 ⊗ I_2 ⊗ I_2)
× (I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ TOF ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2)
× (I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ TOF ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2)
× (I_2 ⊗ I_2 ⊗ I_2 ⊗ TOF ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2)
× (I_2 ⊗ I_2 ⊗ TOF ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2)
× (I_2 ⊗ TOF ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2)
× (TOF ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2)
× (CX ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2)
× (H ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2)
× ∣0,0,0,0,0,0,0,0,0,0,0,0⟩
≡  / √ 2 .* ∣0,0,0,0,0,0,0,0,0,0,0,0⟩  .+ / √ 2 .* ∣1,1,1,1,1,1,1,1,1,1,1,1⟩.
Proof.
Time operate_reduce.
Qed.

Lemma t13 :
(I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ TOF)
× (I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ TOF ⊗ I_2)
× (I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ TOF ⊗ I_2 ⊗ I_2)
× (I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ TOF ⊗ I_2 ⊗ I_2 ⊗ I_2)
× (I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ TOF ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2)
× (I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ TOF ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2)
× (I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ TOF ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2)
× (I_2 ⊗ I_2 ⊗ I_2 ⊗ TOF ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2)
× (I_2 ⊗ I_2 ⊗ TOF ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2)
× (I_2 ⊗ TOF ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2)
× (TOF ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2)
× (CX ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2)
× (H ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2)
× ∣0,0,0,0,0,0,0,0,0,0,0,0,0⟩
≡  / √ 2 .* ∣0,0,0,0,0,0,0,0,0,0,0,0,0⟩  .+ / √ 2 .* ∣1,1,1,1,1,1,1,1,1,1,1,1,1⟩.
Proof.
Time operate_reduce.
Qed.

Lemma t14 :
(I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ TOF)
× (I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ TOF ⊗ I_2)
× (I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ TOF ⊗ I_2 ⊗ I_2)
× (I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ TOF ⊗ I_2 ⊗ I_2 ⊗ I_2)
× (I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ TOF ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2)
× (I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ TOF ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2)
× (I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ TOF ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2)
× (I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ TOF ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2)
× (I_2 ⊗ I_2 ⊗ I_2 ⊗ TOF ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2)
× (I_2 ⊗ I_2 ⊗ TOF ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2)
× (I_2 ⊗ TOF ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2)
× (TOF ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2)
× (CX ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2)
× (H ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2)
× ∣0,0,0,0,0,0,0,0,0,0,0,0,0,0⟩
≡  / √ 2 .* ∣0,0,0,0,0,0,0,0,0,0,0,0,0,0⟩  .+ / √ 2 .* ∣1,1,1,1,1,1,1,1,1,1,1,1,1,1⟩.
Proof.
operate_reduce.
Qed.

Finished transaction in 40.489 secs (39.984u,0.171s) (successful)
Finished transaction in 75.822 secs (75.234u,0.093s) (successful)
Finished transaction in 146.741 secs (146.421u,0.062s) (successful)
Finished transaction in 253.366 secs (252.953u,0.078s) (successful)
Finished transaction in 408.839 secs (408.078u,0.187s) (successful)
Finished transaction in 602.075 secs (601.609u,0.265s) (successful)
Finished transaction in 959.732 secs (907.312u,0.171s) (successful)
Finished transaction in 1203.851 secs (1202.843u,0.64s) (successful)
