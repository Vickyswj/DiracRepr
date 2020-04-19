Require Export Dirac.


(* Initial state *)
Definition init_00 := ∣0⟩ ⊗ ∣0⟩.

Definition φ_1 (a b : C) : Vector 2 := a .* ∣0⟩ .+ b .* ∣1⟩.

Definition φ_2(a b c d: C) : Vector 4 := a .* ∣0,0⟩ .+ b .* ∣0,1⟩ .+ c .* ∣1,0⟩ .+ d .* ∣1,1⟩.

Definition φ_3(a b c d e f g h : C) : Vector 8 := a .* ∣0,0,0⟩ .+ b .* ∣0,0,1⟩ .+ c .* ∣0,1,0⟩ .+ d .* ∣0,1,1⟩
                                                                            .+ e .* ∣1,0,0⟩ .+ f .* ∣1,0,1⟩ .+ g .* ∣1,1,0⟩ .+ h .* ∣1,1,1⟩ .


(* Unitary *)
Lemma unit_X : forall (a b : C),  σX × σX × (φ_1  a b)  ≡  (φ_1  a b).
Proof.
intros.
unfold φ_1.
operate_reduce.
Qed.

Lemma unit_X' : forall (a b : C),  super (σX × σX) (density (φ_1 a b))  ≡ (density (φ_1  a b)).
Proof.
intros.
unfold φ_1,super,density.
super_reduce.
Qed.

Lemma unit_Y : forall (a b : C),  σY × σY × (φ_1  a b)  ≡  (φ_1  a b).
Proof.
intros.
unfold φ_1.
operate_reduce.
Qed.

Lemma ii : σY × σY ≡ I_2 .
Proof.
autounfold with G1_db.
base_reduce.

autounfold with G1_db.
distribute_plus.
isolate_scale.
assoc_right.
autorewrite with B_db.
reduce_scale;
unified_base.
operate_reduce.
Qed.


Lemma unit_Z : forall (a b : C),  σZ × σZ × (φ_1  a b)  ≡  (φ_1  a b).
Proof.
intros.
unfold φ_1.
operate_reduce.
Qed.

Lemma unit_H : forall (a b : C),  H × H × (φ_1  a b)  ≡  (φ_1  a b).
Proof.
intros.
unfold φ_1.
operate_reduce.
Qed.

Lemma unit_CX : forall (a b c d : C),  CX × CX × (φ_2 a b c d)  ≡  (φ_2 a b c d).
Proof.
intros.
unfold φ_2.
operate_reduce.
Qed.

Lemma unit_CX' : forall (a b : C),  CX × CX × ((φ_1  a b) ⊗ (φ_1  a b))  ≡  ((φ_1  a b) ⊗ (φ_1  a b)).
Proof.
intros.
unfold φ_1.
operate_reduce.
Qed.



(* Equation *)
(* One qubit *)
(* 160 *)
Lemma equel1 : forall (a b : C), /√2 .* (σX .+ σZ) × (φ_1  a b) ≡  H × (φ_1  a b).
Proof.
intros.
unfold φ_1.
operate_reduce.
Qed.

(* 162 *)
Lemma equel2 : forall (a b : C), (H × σX × H) × (φ_1  a b) ≡  σZ × (φ_1  a b).
Proof.
intros.
unfold φ_1.
operate_reduce.
Qed.

Lemma equel3 : forall (a b : C), (H × σY × H) × (φ_1  a b) ≡ -1 .* σY × (φ_1  a b).
Proof.
intros.
unfold φ_1.
operate_reduce.
Qed.

Lemma equel4 : forall (a b : C), (H × σZ × H) × (φ_1  a b) ≡  σX × (φ_1  a b).
Proof.
intros.
unfold φ_1.
operate_reduce.
Qed.


(* Two qubits *)
(* Definition SWAP :=  B0 ⊗ B0 .+ B1 ⊗ B2 .+ B2 ⊗ B1 .+ B3 ⊗ B3.
Definition CA_1 {n} (A : Matrix n n) := B0 ⊗ I_2 .+ B3 ⊗ A.
Definition AC_1 {n} (A : Matrix n n) := A ⊗ B3 .+ I_2 ⊗ B0. *)
(* 22 *)
Lemma equel5 : forall (a b c d : C), SWAP × (φ_2  a b c d) ≡  (CX × XC × CX) × (φ_2  a b c d).
Proof.
intros.
unfold φ_2.
operate_reduce.
Qed.

(* 164 *)
Lemma equel6 : forall (a b c d : C), CZ × (φ_2  a b c d) ≡ ZC × (φ_2  a b c d).
Proof.
intros.
unfold φ_2.
operate_reduce.
Qed.

(* 164 *)
Lemma equel7 : forall (a b c d : C), CZ × (φ_2  a b c d) ≡ (I_2 ⊗ H) × CX × (I_2 ⊗ H) × (φ_2  a b c d).
Proof.
intros.
unfold φ_2.
operate_reduce.
Qed.

(* 171 *)
Lemma equel8 : forall (a b c d : C), CX × (σX ⊗ I_2) × CX × (φ_2  a b c d) ≡  (σX ⊗ σX) × (φ_2  a b c d).
Proof.
intros.
unfold φ_2.
operate_reduce.
Qed.

Lemma equel9 : forall (a b c d : C), CX × (σY ⊗ I_2) × CX × (φ_2  a b c d) ≡  (σY ⊗ σX) × (φ_2  a b c d).
Proof.
intros.
unfold φ_2.
operate_reduce.
Qed.

Lemma equel10 : forall (a b c d : C), CX × (σZ ⊗ I_2) × CX × (φ_2  a b c d) ≡  (σZ ⊗ I_2) × (φ_2  a b c d).
Proof.
intros.
unfold φ_2.
operate_reduce.
Qed.

Lemma equel11 : forall (a b c d : C), CX × (I_2 ⊗ σX) × CX × (φ_2  a b c d) ≡  (I_2 ⊗ σX) × (φ_2  a b c d).
Proof.
intros.
unfold φ_2.
operate_reduce.
Qed.

Lemma equel12 : forall (a b c d : C), CX × (I_2 ⊗ σY) × CX × (φ_2  a b c d) ≡  (σZ ⊗ σY) × (φ_2  a b c d).
Proof.
intros.
unfold φ_2.
operate_reduce.
Qed.

Lemma equel13 : forall (a b c d : C), CX × (I_2 ⊗ σZ) × CX × (φ_2  a b c d) ≡  (σZ ⊗ σZ) × (φ_2  a b c d).
Proof.
intros.
unfold φ_2.
operate_reduce.
Qed.

Lemma equel14 : forall (a b c d : C), CZ × (φ_2  a b c d) ≡ (I_2 ⊗ H) × CX × (I_2 ⊗ H) × (φ_2  a b c d).
Proof.
intros.
unfold φ_2.
operate_reduce.
Qed.

(* 165 *)
Definition CE (u: R) := B0 ⊗ I_2 .+ B3 ⊗ (Cexp u .* B0 .+ Cexp u .* B3).
Lemma equel15 : forall (a b c d : C) (u: R), CE u × (φ_2  a b c d) ≡ ((B0 .+ Cexp u .* B3) ⊗ I_2) × (φ_2  a b c d).
Proof.
intros.
unfold φ_2,CE.
operate_reduce.
Qed.

(* 169 *)
Definition not_CX := B0 ⊗ σX .+ B3 ⊗ I_2 .
Lemma equel16 : forall (a b c d : C), CX × (φ_2  a b c d) ≡ (σX ⊗ I_2) × not_CX × (σX ⊗ I_2) × (φ_2  a b c d).
Proof.
intros.
unfold φ_2,not_CX.
operate_reduce.
Qed.


(* Three qubits *)
(* 170 *)
Definition CXX := B0 ⊗ I_2 ⊗ I_2 .+ B3 ⊗ σX ⊗ σX.
Definition CIX := B0 ⊗ I_2 ⊗ I_2 .+ B3 ⊗ I_2 ⊗ σX.
Lemma equel17 : forall (a b c d e f g h : C),
          CXX × (φ_3  a b c d e f g h) ≡ CIX × (CX ⊗ I_2) × (φ_3  a b c d e f g h).
Proof.
intros.
unfold φ_3,CXX,CIX.
operate_reduce.
Qed.






(* Bell Preparation *)
(* 24*)
Definition bell00 := /√2 .* (∣0⟩ ⊗ ∣0⟩) .+ /√2 .* (∣1⟩ ⊗ ∣1⟩).
Definition bell01 := /√2 .* (∣0⟩ ⊗ ∣1⟩) .+ /√2 .* (∣1⟩ ⊗ ∣0⟩).
Definition bell10 := /√2 .* (∣0⟩ ⊗ ∣0⟩) .+ (-/√2) .* (∣1⟩ ⊗ ∣1⟩).
Definition bell11 := /√2 .* (∣0⟩ ⊗ ∣1⟩) .+ (-/√2) .* (∣1⟩ ⊗ ∣0⟩).


Lemma pre_bell00 : bell00 ≡  CX × (H ⊗ I_2) × (∣0⟩ ⊗ ∣0⟩).
Proof.
unfold bell00.
operate_reduce.
Qed. 

Lemma pre_bell00'' :  super (CX × (H ⊗ I_2)) (density (∣0⟩ ⊗ ∣0⟩)) ≡ density bell00.
Proof.
unfold bell00.
super_reduce.
Qed.

Lemma pre_bell01 : bell01 ≡ CX × (H ⊗ I_2) × (∣0⟩ ⊗ ∣1⟩).
Proof.
unfold bell01.
autounfold with G2_db.
distribute_plus.
isolate_scale.
assoc_right.
repeat mult_kron.
repeat (autorewrite with G1_db;
isolate_scale).
reduce_scale.
Qed.

Lemma pre_bell10 : bell10 ≡ CX × (H ⊗ I_2) × (∣1⟩ ⊗ ∣0⟩).
Proof.
unfold bell10.
autounfold with G2_db.
distribute_plus.
isolate_scale.
assoc_right.
repeat mult_kron.
repeat (autorewrite with G1_db;
isolate_scale).
reduce_scale.
Qed.

Lemma pre_bell11 : bell11 ≡ CX × (H ⊗ I_2) × (∣1⟩ ⊗ ∣1⟩).
Proof.
unfold bell00.
autounfold with G2_db.
distribute_plus.
isolate_scale.
assoc_right.
repeat mult_kron.
repeat (autorewrite with G1_db;
isolate_scale).
reduce_scale.
Qed.


(* GHZ Preparation *)
Lemma GHZ_ket0_3 : /√2 .* (∣0⟩ ⊗ ∣0⟩ ⊗ ∣0⟩) .+ /√2 .* (∣1⟩ ⊗ ∣1⟩ ⊗ ∣1⟩) ≡  (I_2 ⊗ CX) × (CX ⊗ I_2) × (H ⊗ I_2 ⊗ I_2) × (∣0⟩ ⊗ ∣0⟩ ⊗ ∣0⟩).
Proof.
autounfold with G2_db.
distribute_plus.
isolate_scale.
assoc_right.
repeat mult_kron.
repeat (autorewrite with G1_db;
isolate_scale).
reduce_scale.
Qed.


(* rotation *)
Check rotation_0.
Definition rX (ϕ : R) := cos (ϕ/2) .* I_2 .+ Ci * sin (ϕ/2) .* σX.
Definition rY (ϕ : R) := cos (ϕ/2) .* I_2 .+ Ci * sin (ϕ/2) .* σY.
Definition rZ (ϕ : R) := cos (ϕ/2) .* I_2 .+ Ci * sin (ϕ/2) .* σZ.
Definition rN (ϕ n1 n2 n3 : R):= cos (ϕ/2) .* I_2 .+ Ci * sin (ϕ/2) .* (n1 .* σX .+ n2 .* σY .+ n3 .* σZ).


Lemma equel18 : forall (a b: C), PT × (φ_1  a b) ≡ Cexp (PI/8) .* rZ (PI/4) × (φ_1  a b).
Proof.
intros.
unfold φ_1,rZ,PT.
operate_reduce.
Admitted.


(* Toffoli *)
Definition TOF := B0 ⊗ I_2 ⊗ I_2 .+ B3 ⊗ CX.

(* Fredkin *)
Definition FRE := B0 ⊗ I_2 ⊗ I_2 .+ B3 ⊗ SWAP.

