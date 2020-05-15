Require Export Dirac.
Require Export StateAndOperator.
Declare Scope QE.
Local Open Scope QE.


(* f(0) =  f(1) = 0 *)

(*Step-by-step*)

(*Vector*)
Definition φ00 := ∣0⟩ ⊗ ∣1⟩.
Definition φ01 := (H ⊗ H) × φ00.
Definition φ02 := (I_2 ⊗ I_2) × φ01.
Definition φ03 := (H ⊗ I_2) × φ02.

Lemma step01' : φ01 ≡ ∣+⟩ ⊗ ∣-⟩.
Proof.
unfold φ01,φ00.
operate_reduce.
Qed.
Lemma step01 : φ01 ≈ ∣+⟩ ⊗ ∣-⟩.
Proof.
sta_yes.
apply step01'.
Qed.

Lemma step02' : φ02 ≡ ∣+⟩ ⊗ ∣-⟩.
Proof.
unfold φ02.
rewrite step01'.
operate_reduce.
Qed.
Lemma step02 : φ02 ≈ ∣+⟩ ⊗ ∣-⟩.
Proof.
sta_yes.
apply step02'.
Qed.

Lemma step03' : φ03 ≡ ∣0⟩ ⊗ ∣-⟩.
Proof.
unfold φ03.
rewrite step02'.
operate_reduce.
Qed.
Lemma step03 : φ03 ≈ ∣0⟩ ⊗ ∣-⟩.
Proof.
sta_yes.
apply step03'.
Qed.


(*Density*)
Definition ρ00 := density φ00.
Definition ρ01 := super (H ⊗ H) ρ00.
Definition ρ02 := super (I_2 ⊗ I_2) ρ01.
Definition ρ03 := super (H ⊗ I_2) ρ02.

Lemma Dstep01 : ρ01 ≡ density φ01.
Proof.
unfold ρ01,ρ00.
super_reduce.
Qed.

Lemma Dstep02 : ρ02 ≡ density φ02.
Proof.
unfold ρ02,super.
rewrite Dstep01.
super_reduce.
Qed.

Lemma Dstep03 : ρ03 ≡ density φ03.
Proof.
unfold ρ03,super.
rewrite Dstep02.
super_reduce.
Qed.

(*One-time*)
Lemma deutsch0' : (H ⊗ I_2) × (I_2 ⊗ I_2) × (H ⊗ H) × (∣0⟩ ⊗ ∣1⟩) ≡ ∣0⟩ ⊗ ∣-⟩ .
Proof. operate_reduce. Qed.

Lemma deutsch0 : (H ⊗ I_2) × (I_2 ⊗ I_2) × (H ⊗ H) × (∣0⟩ ⊗ ∣1⟩) ≈ ∣0⟩ ⊗ ∣-⟩ .
Proof.
by_den.
state_reduce.
operate_reduce.
Qed.

(* Lemma deutsch0'' : (H ⊗ I_2) × (I_2 ⊗ I_2) × (H ⊗ H) × (∣0⟩ ⊗ ∣1⟩) ≈ ∣0⟩ ⊗ ∣-⟩ .
Proof.
sta_yes.
operate_reduce.
Qed. *)


Lemma Ddeutsch0' : (super ((H ⊗ I_2) × (I_2 ⊗ I_2) × (H ⊗ H)) (density (∣0⟩ ⊗ ∣1⟩)) ≡ density  (∣0⟩ ⊗ ∣-⟩)).
Proof. super_reduce. Qed.
Lemma Ddeutsch0 : (super ((H ⊗ I_2) × (I_2 ⊗ I_2) × (H ⊗ H)) (density (∣0⟩ ⊗ ∣1⟩)) ≈ density  (∣0⟩ ⊗ ∣-⟩)).
Proof.
by_def1.
super_reduce.
Qed.


(* f(0) =  f(1) = 1 *)

(*Step-by-step*)

(*Vector*)
Definition φ10 := ∣0⟩ ⊗ ∣1⟩.
Definition φ11 := (H ⊗ H) × φ10.
Definition φ12 := (I_2 ⊗ σX) × φ11.
Definition φ13 := (H ⊗ I_2) × φ12.

Lemma step11 : φ11 ≡ ∣+⟩ ⊗ ∣-⟩.
Proof.
unfold φ11,φ10.
operate_reduce.
Qed.


Lemma step12 : φ12 ≡ -1 .* ∣+⟩ ⊗ ∣-⟩.
Proof.
unfold φ12.
rewrite step11.
operate_reduce.
Qed.


Lemma step13 : φ13 ≡ -1 .* ∣0⟩ ⊗ ∣-⟩.
Proof.
unfold φ13.
rewrite step12.
operate_reduce.
Qed.

Lemma step13' : φ13 ≈ ∣0⟩ ⊗ ∣-⟩.
Proof.
sta_m1.
rewrite step13.
isolate_scale.
reduce_scale.
Qed.


(*Density*)
Definition ρ10 := density φ10.
Definition ρ11 := super (H ⊗ H) ρ10.
Definition ρ12 := super (I_2 ⊗ σX) ρ11.
Definition ρ13 := super (H ⊗ I_2) ρ12.

Lemma Dstep11 : ρ11 ≡ density φ11.
Proof.
unfold ρ11,ρ10,super.
super_reduce.
Qed.

Lemma Dstep12 : ρ12 ≡ density φ12.
Proof.
unfold ρ12,super.
rewrite Dstep11.
super_reduce.
Qed.

Lemma Dstep13 : ρ13 ≡ density φ13.
Proof.
unfold ρ13,super.
rewrite Dstep12.
super_reduce.
Qed.


(*One-time*)
Lemma deutsch1' : (H ⊗ I_2) × (I_2 ⊗ σX) × (H ⊗ H) × (∣0⟩ ⊗ ∣1⟩) ≡ -1 .* ∣0⟩ ⊗ ∣-⟩ .
Proof. operate_reduce. Qed.

Lemma deutsch1 : (H ⊗ I_2) × (I_2 ⊗ σX) × (H ⊗ H) × (∣0⟩ ⊗ ∣1⟩) ≈ ∣0⟩ ⊗ ∣-⟩ .
Proof. 
by_den.
rewrite deutsch1'.
isolate_scale.
rewrite Mscale_adj.
isolate_scale.
reduce_scale.
Qed.


Lemma Ddeutsch1' : super ((H ⊗ I_2) × (I_2 ⊗ σX) × (H ⊗ H)) (density (∣0⟩ ⊗ ∣1⟩))  ≡ density (-1 .* (∣0⟩ ⊗ ∣-⟩)).
Proof. super_reduce. Qed.

Lemma Ddeutsch1 : super ((H ⊗ I_2) × (I_2 ⊗ σX) × (H ⊗ H)) (density (∣0⟩ ⊗ ∣1⟩)) ≈ density (∣0⟩ ⊗ ∣-⟩).
Proof.
by_def1.
rewrite Ddeutsch1'.
unfold density.
rewrite Mscale_adj.
isolate_scale.
reduce_scale.
Qed.


(* f(0) = 0, f(1) = 1 *)

(*Step-by-step*)

(*Vector*)
Definition φ20 := ∣0⟩ ⊗ ∣1⟩.
Definition φ21 := (H ⊗ H) × φ20.
Definition φ22 := CX × φ21.
Definition φ23 := (H ⊗ I_2) × φ22.

Lemma step21 : φ21 ≡ ∣+⟩ ⊗ ∣-⟩.
Proof.
unfold φ21,φ20.
operate_reduce.
Qed.

Lemma step22 : φ22 ≡ ∣-⟩ ⊗ ∣-⟩.
Proof.
unfold φ22.
rewrite step21.
operate_reduce.
Qed.

Lemma step23 : φ23 ≡ ∣1⟩ ⊗ ∣-⟩.
Proof.
unfold φ23.
rewrite step22.
operate_reduce.
Qed.


(*Density*)
Definition ρ20 := density φ20.
Definition ρ21 := super (H ⊗ H) ρ20.
Definition ρ22 := super CX ρ21.
Definition ρ23 := super (H ⊗ I_2) ρ22.

Lemma Dstep21 : ρ21 ≡ density φ21.
Proof.
unfold ρ21,ρ20,super.
super_reduce.
Qed.

Lemma Dstep22 : ρ22 ≡ density φ22.
Proof.
unfold ρ22,super.
rewrite Dstep21.
super_reduce.
Qed.

Lemma Dstep23 : ρ23 ≡ density φ23.
Proof.
unfold ρ23,super.
rewrite Dstep22.
super_reduce.
Qed.


(*One-time*)
Lemma deutsch2' : (H ⊗ I_2) × CX × (H ⊗ H) × (∣0⟩ ⊗ ∣1⟩) ≡ ∣1⟩ ⊗ ∣-⟩ .
Proof. operate_reduce. Qed.

Lemma deutsch2 : (H ⊗ I_2) × CX × (H ⊗ H) × (∣0⟩ ⊗ ∣1⟩) ≈ ∣1⟩ ⊗ ∣-⟩ .
Proof. 
by_den.
state_reduce.
operate_reduce.
Qed.


Lemma Ddeutsch2' : super ((H ⊗ I_2) × CX × (H ⊗ H)) (density (∣0⟩ ⊗ ∣1⟩)) ≡ density (∣1⟩ ⊗ ∣-⟩).
Proof. super_reduce. Qed.

Lemma Ddeutsch2 : super ((H ⊗ I_2) × CX × (H ⊗ H)) (density (∣0⟩ ⊗ ∣1⟩)) ≈ density (∣1⟩ ⊗ ∣-⟩).
Proof. by_def1. super_reduce. Qed.


(* f(0) = 1, f(1) = 0 *)

(*Step-by-step*)

(*Vector*)
Definition φ30 := ∣0⟩ ⊗ ∣1⟩.
Definition φ31 := (H ⊗ H) × φ30.
Definition φ32 := not_CX × φ31.
Definition φ33 := (H ⊗ I_2) × φ32.

Lemma step31 : φ31 ≡ ∣+⟩ ⊗ ∣-⟩.
Proof.
unfold φ31,φ30.
operate_reduce.
Qed.

Lemma step32 : φ32 ≡ -1 .* ∣-⟩ ⊗ ∣-⟩.
Proof.
unfold φ32.
rewrite step31.
unfold not_CX.
operate_reduce.
Qed.

Lemma step33 : φ33 ≡ -1 .* ∣1⟩ ⊗ ∣-⟩.
Proof.
unfold φ33.
rewrite step32.
operate_reduce.
Qed.

Lemma step33' : φ33 ≈ ∣1⟩ ⊗ ∣-⟩.
Proof.
sta_m1.
rewrite step33.
isolate_scale.
reduce_scale.
Qed.


(*Density*)
Definition ρ30 := density φ30.
Definition ρ31 := super (H ⊗ H) ρ30.
Definition ρ32 := super not_CX ρ31.
Definition ρ33 := super (H ⊗ I_2) ρ32.

Lemma Dstep31 : ρ31 ≡ density  φ31.
Proof.
unfold ρ31,ρ30,super.
super_reduce.
Qed.

Lemma Dstep32 : ρ32 ≡ density φ32.
Proof.
unfold ρ32,super.
rewrite Dstep31.
super_reduce.
Qed.

Lemma Dstep33 : ρ33 ≡ density φ33.
Proof.
unfold ρ33,super.
rewrite Dstep32.
super_reduce.
Qed.


(*One-time*)
Lemma deutsch3' : (H ⊗ I_2) × not_CX × (H ⊗ H) × (∣0⟩ ⊗ ∣1⟩) ≡ -1 .* ∣1⟩ ⊗ ∣-⟩.
Proof. operate_reduce. Qed.

Lemma deutsch3 : (H ⊗ I_2) × not_CX × (H ⊗ H) × (∣0⟩ ⊗ ∣1⟩) ≈ ∣1⟩ ⊗ ∣-⟩ .
Proof.
by_den.
rewrite deutsch3'.
isolate_scale.
rewrite Mscale_adj.
isolate_scale.
reduce_scale.
Qed.


Lemma Ddeutsch3' : super ((H ⊗ I_2) × not_CX × (H ⊗ H)) (density(∣0⟩ ⊗ ∣1⟩)) ≡ density (-1 .* (∣1⟩ ⊗ ∣-⟩)).
Proof. super_reduce. Qed.

Lemma Ddeutsch3 : super ((H ⊗ I_2) × not_CX × (H ⊗ H)) (density(∣0⟩ ⊗ ∣1⟩)) ≈ density (∣1⟩ ⊗ ∣-⟩).
Proof.
by_def1.
rewrite Ddeutsch3'.
unfold density.
rewrite Mscale_adj.
isolate_scale.
reduce_scale.
Qed.
