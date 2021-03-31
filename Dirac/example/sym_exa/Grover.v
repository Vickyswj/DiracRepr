Require Export Dirac.
Require Export Equival.

(*Step-by-step*)

(*Search space 4 and query for 0 *)

(*Vector*)
Definition not_CX := B0 ⊗ σX .+ B3 ⊗ I_2 .
Definition ORA0 := B0 ⊗ not_CX .+ B3 ⊗ I_2 ⊗ I_2.
Definition MI := (B0 .+ B1 .+ B2 .+ B3)⊗ (B0 .+ B1 .+ B2 .+ B3).
Definition CPS := (((/2 .* MI) .+ (-1) .* (I_2 ⊗ I_2)) ⊗ I_2).
Global Hint Unfold  CPS MI ORA0 not_CX : Gn_db.

Definition φ00 := ∣0,0,1⟩.
Definition φ01 := (H ⊗ H ⊗ H) × φ00.
Definition φ02 := ORA0 × φ01.
Definition φ03 := CPS × φ02.
Definition φ04 := (I_2 ⊗ I_2 ⊗ H) × φ03.

Lemma step01 : φ01 ≡ ∣+⟩ ⊗ ∣+⟩ ⊗ ∣-⟩.
Proof.
unfold φ01,φ00.
operate_reduce.
Qed.

Lemma step02 : φ02 ≡ / √ 2 .* (∣+⟩ ⊗ ∣1⟩ .+ - 1 .* ∣-⟩ ⊗ ∣0⟩) ⊗ ∣-⟩.
Proof.
unfold φ02.
rewrite step01.
operate_reduce.
Qed.

Lemma step03 : φ03 ≡ ∣0⟩ ⊗ ∣0⟩ ⊗ ∣-⟩.
Proof.
unfold φ03.
rewrite step02.
operate_reduce.
Qed.

Lemma step04 : φ04 ≡ (∣0⟩ ⊗ ∣0⟩ ⊗ ∣1⟩).
Proof.
unfold φ04.
rewrite step03.
operate_reduce.
Qed.


(*Density*)
Definition ρ00 := density φ00.
Definition ρ01 := super (H ⊗ H ⊗ H) ρ00.
Definition ρ02 := super ORA0 ρ01.
Definition ρ03 := super  CPS ρ02.
Definition ρ04 := super  (I_2 ⊗ I_2 ⊗ H) ρ03.

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

Lemma Dstep04 : ρ04 ≡ density φ04.
Proof.
unfold ρ04,super.
rewrite Dstep03.
super_reduce.
Qed.




(*Search space 4 and query for 1 *)

(*Vector*)
Definition ORA1 := B0 ⊗ CX .+ B3 ⊗ I_2 ⊗ I_2.
Global Hint Unfold  ORA1 : Gn_db.

Definition φ10 := ∣0,0,1⟩.
Definition φ11 := (H ⊗ H ⊗ H) × φ10.
Definition φ12 := ORA1 × φ11.
Definition φ13 := CPS × φ12.
Definition φ14 := (I_2 ⊗ I_2 ⊗ H) × φ13.

Lemma step11 : φ11 ≡ ∣+⟩ ⊗ ∣+⟩ ⊗ ∣-⟩.
Proof.
unfold φ11,φ10.
operate_reduce.
Qed.

Lemma step12 : φ12 ≡ / √ 2 .* (∣0⟩ ⊗ ∣-⟩ .+ ∣1⟩ ⊗ ∣+⟩) ⊗ ∣-⟩.
Proof.
unfold φ12.
rewrite step11.
operate_reduce.
Qed.

Lemma step13 : φ13 ≡ ∣0⟩ ⊗ ∣1⟩ ⊗ ∣-⟩.
Proof.
unfold φ13.
rewrite step12.
operate_reduce.
Qed.

Lemma step14 : φ14 ≡ (∣0⟩ ⊗ ∣1⟩ ⊗ ∣1⟩).
Proof.
unfold φ14.
rewrite step13.
operate_reduce.
Qed.


(*Density*)
Definition ρ10 := density φ10.
Definition ρ11 := super (H ⊗ H ⊗ H) ρ10.
Definition ρ12 := super ORA1 ρ11.
Definition ρ13 := super  CPS ρ12.
Definition ρ14 := super  (I_2 ⊗ I_2 ⊗ H) ρ13.

Lemma Dstep11 : ρ11 ≡ density φ11.
Proof.
unfold ρ11,ρ10.
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

Lemma Dstep14 : ρ14 ≡ density φ14.
Proof.
unfold ρ14,super.
rewrite Dstep13.
super_reduce.
Qed.




(*Search space 4 and query for 2 *)

(*Vector*)
Definition ORA2 := B0 ⊗ I_2 ⊗ I_2 .+ B3 ⊗ not_CX.
Global Hint Unfold  ORA2 : Gn_db.

Definition φ20 := ∣0,0,1⟩.
Definition φ21 := (H ⊗ H ⊗ H) × φ20.
Definition φ22 := ORA2× φ21.
Definition φ23 := CPS × φ22.
Definition φ24 := (I_2 ⊗ I_2 ⊗ H) × φ23.

Lemma step21 : φ21 ≡ ∣+⟩ ⊗ ∣+⟩ ⊗ ∣-⟩.
Proof.
unfold φ21,φ20.
operate_reduce.
Qed.

Lemma step22 : φ22 ≡ / √ 2 .* (∣0⟩ ⊗ ∣+⟩ .+ -  1 .* ∣1⟩ ⊗ ∣-⟩) ⊗ ∣-⟩.
Proof.
unfold φ22.
rewrite step21.
operate_reduce.
Qed.

Lemma step23 : φ23 ≡ ∣1⟩ ⊗ ∣0⟩ ⊗ ∣-⟩.
Proof.
unfold φ23.
rewrite step22.
operate_reduce.
Qed.

Lemma step24 : φ24 ≡ (∣1⟩ ⊗ ∣0⟩ ⊗ ∣1⟩).
Proof.
unfold φ24.
rewrite step23.
operate_reduce.
Qed.


(*Density*)
Definition ρ20 := density φ20.
Definition ρ21 := super (H ⊗ H ⊗ H) ρ20.
Definition ρ22 := super ORA2 ρ21.
Definition ρ23 := super  CPS ρ22.
Definition ρ24 := super  (I_2 ⊗ I_2 ⊗ H) ρ23.

Lemma Dstep21 : ρ21 ≡ density φ21.
Proof.
unfold ρ21,ρ20.
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

Lemma Dstep24 : ρ24 ≡ density φ24.
Proof.
unfold ρ24,super.
rewrite Dstep23.
super_reduce.
Qed.



(*Search space 4 and query for 3 *)

(*Vector*)
Definition ORA3 := B0 ⊗ I_2 ⊗ I_2 .+ B3 ⊗ CX.
(* Definition TOF := B0 ⊗ I_2 ⊗ I_2 .+ B3 ⊗ CX. *)
(* Definition ORA := (B0 ⊗ B0 ⊗ I_2) .+ (B1 ⊗ B1 ⊗ I_2) .+ (B2 ⊗ B2 ⊗ I_2) .+ (B3 ⊗ B3 ⊗ σX). *)
Global Hint Unfold  ORA3 : Gn_db.

Definition φ0 := ∣0,0,1⟩.
Definition φ1 := (H ⊗ H ⊗ H) × φ0.
Definition φ2 := ORA3 × φ1.
Definition φ3 := CPS × φ2.
Definition φ4 := (I_2 ⊗ I_2 ⊗ H) × φ3.

Lemma step1 : φ1 ≡ ∣+⟩ ⊗ ∣+⟩ ⊗ ∣-⟩.
Proof.
unfold φ1,φ0.
operate_reduce.
Qed.

Lemma step2 : φ2 ≡ / √ 2 .* (∣+⟩ ⊗ ∣0⟩ .+ ∣-⟩ ⊗ ∣1⟩) ⊗ ∣-⟩.
Proof.
unfold φ2.
rewrite step1.
operate_reduce.
Qed.

Lemma step3 : φ3 ≡ ∣1⟩ ⊗ ∣1⟩ ⊗ ∣-⟩.
Proof.
unfold φ3.
rewrite step2.
operate_reduce.
Qed.

Lemma step4 : φ4 ≡ (∣1⟩ ⊗ ∣1⟩ ⊗ ∣1⟩).
Proof.
unfold φ4.
rewrite step3.
operate_reduce.
Qed.


(*Density*)
Definition ρ0 := density φ0.
Definition ρ1 := super (H ⊗ H ⊗ H) ρ0.
Definition ρ2 := super ORA3 ρ1.
Definition ρ3 := super  CPS ρ2.
Definition ρ4 := super  (I_2 ⊗ I_2 ⊗ H) ρ3.

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

Lemma Dstep3 : ρ3 ≡ density φ3.
Proof.
unfold ρ3,super.
rewrite Dstep2.
super_reduce.
Qed.

Lemma Dstep4 : ρ4 ≡ density φ4.
Proof.
unfold ρ4,super.
rewrite Dstep3.
super_reduce.
Qed.



(* One-time *)
Lemma Grover_2_0 : (I_2 ⊗ I_2 ⊗ H) × CPS × ORA0× (H ⊗ H ⊗ H) × ∣0,0,1⟩ ≡ ∣0,0,1⟩.
Proof.
operate_reduce.
Qed.

Lemma DGrover_2_0 : super ((I_2 ⊗ I_2 ⊗ H) × CPS × ORA0 × (H ⊗ H ⊗ H)) (density ∣0,0,1⟩) ≡ density ∣0,0,1⟩.
Proof.
Time super_reduce.
Qed.

Lemma Grover_2_0' : (I_2 ⊗ I_2 ⊗ H) × CPS × ORA0× (H ⊗ H ⊗ H) × ∣0,0,1⟩ ≈ ∣0,0,1⟩.
Proof.
by_den.
rewrite Grover_2_0;reflexivity.
Qed.



Lemma Grover_2_1 : (I_2 ⊗ I_2 ⊗ H) × CPS × ORA1 × (H ⊗ H ⊗ H) × ∣0,0,1⟩ ≡ ∣0,1,1⟩.
Proof.
operate_reduce.
Qed.

Lemma DGrover_2_1 : super ((I_2 ⊗ I_2 ⊗ H) × CPS × ORA1 × (H ⊗ H ⊗ H)) (density ∣0,0,1⟩) ≡ density ∣0,1,1⟩.
Proof.
Time super_reduce.
Qed.

Lemma Grover_2_1' : (I_2 ⊗ I_2 ⊗ H) × CPS × ORA1 × (H ⊗ H ⊗ H) × ∣0,0,1⟩ ≈ ∣0,1,1⟩.
Proof.
by_den.
rewrite Grover_2_1;reflexivity.
Qed.



Lemma Grover_2_2 : (I_2 ⊗ I_2 ⊗ H) × CPS × ORA2 × (H ⊗ H ⊗ H) × ∣0,0,1⟩ ≡ ∣1,0,1⟩.
Proof.
operate_reduce.
Qed.

Lemma DGrover_2_2 : super ((I_2 ⊗ I_2 ⊗ H) × CPS × ORA2 × (H ⊗ H ⊗ H)) (density ∣0,0,1⟩) ≡ density ∣1,0,1⟩.
Proof.
Time super_reduce.
Qed.

Lemma Grover_2_2' : (I_2 ⊗ I_2 ⊗ H) × CPS × ORA2 × (H ⊗ H ⊗ H) × ∣0,0,1⟩ ≈ ∣1,0,1⟩.
Proof.
by_den.
state_reduce.
rewrite Grover_2_2;reflexivity.
Qed.



Lemma Grover_2_3 : (I_2 ⊗ I_2 ⊗ H) × CPS × ORA3 × (H ⊗ H ⊗ H) × ∣0,0,1⟩ ≡ ∣1,1,1⟩.
Proof.
operate_reduce.
Qed.

Lemma DGrover_2_3 : super ((I_2 ⊗ I_2 ⊗ H) × CPS × ORA3 × (H ⊗ H ⊗ H)) (density ∣0,0,1⟩) ≡ density ∣1,1,1⟩.
Proof.
Time super_reduce.
Qed.

Lemma Grover_2_3' : (I_2 ⊗ I_2 ⊗ H) × CPS × ORA3 × (H ⊗ H ⊗ H) × ∣0,0,1⟩ ≈ ∣1,1,1⟩.
Proof.
by_den.
state_reduce.
rewrite Grover_2_3;reflexivity.
Qed.

(* 
Finished transaction in 121.71 secs (120.781u,0.031s) (successful)
Finished transaction in 122.279 secs (121.734u,0.031s) (successful)
Finished transaction in 122.089 secs (121.375u,0.046s) (successful)
Finished transaction in 121.582 secs (120.89u,0.093s) (successful) *)
