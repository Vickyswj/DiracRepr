Require Export Dirac.
Require Export Equival.



(* s = 10*)

(*Step-by-step*)

(*Vector*)
Definition φ20 := ∣0,0,0,0⟩.
Definition φ21 := (H ⊗ H ⊗ I_2 ⊗ σX) × φ20.
Definition φ22 := (I_2 ⊗ CX ⊗ I_2) × φ21.
Definition φ23 := (H ⊗ H ⊗ I_2 ⊗ I_2) × φ22.

Lemma step21 : φ21 ≡ ∣+⟩ ⊗ ∣+⟩ ⊗ ∣0⟩ ⊗ ∣1⟩.
Proof.
unfold φ21,φ20.
operate_reduce.
Qed.

Lemma step22 : φ22 ≡ /√2 .* (∣+⟩ ⊗ ∣0⟩ ⊗ ∣0⟩ ⊗ ∣1⟩) .+ /√2 .* (∣+⟩ ⊗ ∣1⟩ ⊗ ∣1⟩ ⊗ ∣1⟩).
Proof.
unfold φ22.
rewrite step21.
operate_reduce.
Qed.

Lemma step23 : φ23 ≡ /2 .* ∣0,0,0,1⟩ .+ /2 .* ∣0,1,0,1⟩ .+ /2 .* ∣0,0,1,1⟩ .+ - /2 .* ∣0,1,1,1⟩.
Proof.
unfold φ23.
rewrite step22.
operate_reduce.
Qed.


(*Density*)
Definition ρ20 := φ20 × φ20†.
Definition ρ21 := super (H ⊗ H ⊗ I_2 ⊗ σX) ρ20.
Definition ρ22 := super (I_2 ⊗ CX ⊗ I_2) ρ21.
Definition ρ23 := super (H ⊗ H ⊗ I_2 ⊗ I_2) ρ22.

Lemma Dstep21 : ρ21 ≡ φ21 × φ21†.
Proof.
unfold ρ21,ρ20,super.
super_reduce.
Qed.

Lemma Dstep22 : ρ22 ≡ φ22 × φ22†.
Proof.
unfold ρ22,super.
rewrite Dstep21.
super_reduce.
Qed.

Lemma Dstep23 : ρ23 ≡ φ23 × φ23†.
Proof.
unfold ρ23,super.
rewrite Dstep22.
super_reduce.
Qed.

(* 
(*One-time*)
Lemma simon2 : (H ⊗ H ⊗ I_2 ⊗ I_2) × (I_2 ⊗ CX ⊗ I_2) × (H ⊗ H ⊗ I_2 ⊗ σX) × ∣0,0,0,0⟩ ≡ /2 .* ∣0,0,0,1⟩ .+ /2 .* ∣0,1,0,1⟩ .+ /2 .* ∣0,0,1,1⟩ .+ - /2 .* ∣0,1,1,1⟩.
Proof. operate_reduce. Qed.

Lemma Dsimon2 : super ((H ⊗ H ⊗ I_2 ⊗ I_2) × (I_2 ⊗ CX ⊗ I_2) × (H ⊗ H ⊗ I_2 ⊗ σX)) (density ∣0,0,0,0⟩) ≡ density (/2 .* ∣0,0,0,1⟩ .+ /2 .* ∣0,1,0,1⟩ .+ /2 .* ∣0,0,1,1⟩ .+ - /2 .* ∣0,1,1,1⟩).
Proof. super_reduce. Qed.

Lemma simon2' : (H ⊗ H ⊗ I_2 ⊗ I_2) × (I_2 ⊗ CX ⊗ I_2) × (H ⊗ H ⊗ I_2 ⊗ σX) × ∣0,0,0,0⟩ ≈ /2 .* ∣0,0,0,1⟩ .+ /2 .* ∣0,1,0,1⟩ .+ /2 .* ∣0,0,1,1⟩ .+ - /2 .* ∣0,1,1,1⟩.
Proof.
by_den.
rewrite simon2.
reflexivity.
Qed. *)



(* s = 11*)

(*Step-by-step*)

(*Vector*)
Definition CIX := B0 ⊗ I_2 ⊗ I_2 .+ B3 ⊗ I_2 ⊗ σX.
Global Hint Unfold  CIX : Gn_db.

Definition φ30 := ∣0,0,0,0⟩.
Definition φ31 := (H ⊗ H ⊗ I_2 ⊗ I_2) × φ30.
Definition φ32 := (CIX ⊗ σX) × φ31.
Definition φ33 := (I_2 ⊗ CX ⊗ I_2) × φ32.
Definition φ34 := (H ⊗ H ⊗ I_2 ⊗ I_2) × φ33.

Lemma step31 : φ31 ≡ ∣+⟩ ⊗ ∣+⟩ ⊗ ∣0⟩ ⊗ ∣0⟩.
Proof.
unfold φ31,φ30.
operate_reduce.
Qed.

Lemma step32 : φ32 ≡ /√2 .* (∣0⟩ ⊗ ∣+⟩ ⊗ ∣0⟩ ⊗ ∣1⟩) .+ /√2 .* (∣1⟩ ⊗ ∣+⟩ ⊗ ∣1⟩ ⊗ ∣1⟩).
Proof.
unfold φ32.
rewrite step31.
operate_reduce.
Qed.

Lemma step33 : φ33 ≡ /2 .* ∣0,0,0,1⟩ .+ /2 .* ∣0,1,1,1⟩ .+ /2 .* ∣1,0,1,1⟩ .+ /2 .* ∣1,1,0,1⟩.
Proof.
unfold φ33.
rewrite step32.
operate_reduce.
Qed.

Lemma step34 : φ34 ≡ /2 .* ∣0,0,0,1⟩ .+ /2 .* ∣1,1,0,1⟩ .+ /2 .* ∣0,0,1,1⟩ .+ - /2 .* ∣1,1,1,1⟩.
Proof.
unfold φ34.
rewrite step33.
operate_reduce.
Qed.


(*Density*)
Definition ρ30 := φ30 × φ30†.
Definition ρ31 := super (H ⊗ H ⊗ I_2 ⊗ I_2) ρ30.
Definition ρ32 := super (CIX ⊗ σX) ρ31.
Definition ρ33 := super (I_2 ⊗ CX ⊗ I_2) ρ32.
Definition ρ34 := super (H ⊗ H ⊗ I_2 ⊗ I_2) ρ33.

Lemma Dstep31 : ρ31 ≡ φ31 × φ31†.
Proof.
unfold ρ31,ρ30,super.
super_reduce.
Qed.

Lemma Dstep32 : ρ32 ≡ φ32 × φ32†.
Proof.
unfold ρ32,super,CIX.
rewrite Dstep31.
super_reduce.
Qed.

Lemma Dstep33 : ρ33 ≡ φ33 × φ33†.
Proof.
unfold ρ33,super.
rewrite Dstep32.
super_reduce.
Qed.

Lemma Dstep34 : ρ34 ≡ φ34 × φ34†.
Proof.
unfold ρ34,super.
rewrite Dstep33.
super_reduce.
Qed.


(*One-time*)
Lemma simon3 : (H ⊗ H ⊗ I_2 ⊗ I_2) × (I_2 ⊗ CX ⊗ I_2) × (CIX ⊗ σX) × (H ⊗ H ⊗ I_2 ⊗ I_2) × ∣0,0,0,0⟩ ≡ /2 .* ∣0,0,0,1⟩ .+ /2 .* ∣1,1,0,1⟩ .+ /2 .* ∣0,0,1,1⟩ .+ - /2 .* ∣1,1,1,1⟩.
Proof. operate_reduce. Qed.
Lemma Dsimon3 : super ((H ⊗ H ⊗ I_2 ⊗ I_2) × (I_2 ⊗ CX ⊗ I_2) × (CIX ⊗ σX) × (H ⊗ H ⊗ I_2 ⊗ I_2)) (density ∣0,0,0,0⟩) ≡ density (/2 .* ∣0,0,0,1⟩ .+ /2 .* ∣1,1,0,1⟩ .+ /2 .* ∣0,0,1,1⟩ .+ - /2 .* ∣1,1,1,1⟩).
Proof.
Time super_reduce.
Qed.


Lemma simon3' : (H ⊗ H ⊗ I_2 ⊗ I_2) × (I_2 ⊗ CX ⊗ I_2) × (CIX ⊗ σX) × (H ⊗ H ⊗ I_2 ⊗ I_2) × ∣0,0,0,0⟩ ≈ /2 .* ∣0,0,0,1⟩ .+ /2 .* ∣1,1,0,1⟩ .+ /2 .* ∣0,0,1,1⟩ .+ - /2 .* ∣1,1,1,1⟩.
Proof.
by_den.
rewrite simon3.
reflexivity.
Qed.

(* Finished transaction in 48.84 secs (48.578u,0.062s) (successful)*)
