Require Export Dirac.


(* Initial state *)
Definition init_00 := ∣0⟩ ⊗ ∣0⟩.

Definition φ_1 (a b : C) : Vector 2 := a .* ∣0⟩ .+ b .* ∣1⟩.

Definition φ_2(a b c d: C) : Vector 4 := a .* ∣0,0⟩ .+ b .* ∣0,1⟩ .+ c .* ∣1,0⟩ .+ d .* ∣1,1⟩.

Definition φ_3(a b c d e f g h : C) : Vector 8 := a .* ∣0,0,0⟩ .+ b .* ∣0,0,1⟩ .+ c .* ∣0,1,0⟩ .+ d .* ∣0,1,1⟩
                                                                            .+ e .* ∣1,0,0⟩ .+ f .* ∣1,0,1⟩ .+ g .* ∣1,1,0⟩ .+ h .* ∣1,1,1⟩ .


(* See line 336 for a more concise representation *)

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

Lemma ux : σX × σX ≡ I_2 .
Proof.
unfold σX.
base_reduce.
Qed.

Lemma unit_Y : forall (a b : C),  σY × σY × (φ_1  a b)  ≡  (φ_1  a b).
Proof.
intros.
unfold φ_1.
operate_reduce.
Qed.

Lemma uY : σY × σY ≡ I_2 .
Proof.
unfold σY.
base_reduce.
Qed.

Lemma unit_Z : forall (a b : C),  σZ × σZ × (φ_1  a b)  ≡  (φ_1  a b).
Proof.
intros.
unfold φ_1.
operate_reduce.
Qed.

Lemma uz : σZ × σZ ≡ I_2 .
Proof.
unfold σZ.
base_reduce.
replace (- -1) with (- - (1)) by lca.
reduce_scale.
Qed.

Lemma unit_H : forall (a b : C),  H × H × (φ_1  a b)  ≡  (φ_1  a b).
Proof.
intros.
unfold φ_1.
operate_reduce.
Qed.

Lemma uh : H × H ≡ I_2 .
Proof.
unfold H,I_2.
base_reduce.
Qed.

Lemma unit_CX : forall (a b c d : C),  CX × CX × (φ_2 a b c d)  ≡  (φ_2 a b c d).
Proof.
intros.
unfold φ_2.
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

Lemma eq1 : /√2 .* (σX .+ σZ)  ≡ H .
Proof.
unfold H,σX,σZ.
base_reduce.
Qed.

(* 162 *)
Lemma equel2 : forall (a b : C), (H × σX × H) × (φ_1  a b) ≡  σZ × (φ_1  a b).
Proof.
intros.
unfold φ_1.
operate_reduce.
Qed.

Lemma eq2 : H × σX × H  ≡ σZ.
Proof.
unfold H,σX,σZ.
base_reduce.
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

Lemma equel15 : forall (a b c d : C), XC × (φ_2  a b c d) ≡ (H ⊗ H) × CX × (H ⊗ H) × (φ_2  a b c d).
Proof.
intros.
unfold φ_2.
operate_reduce.
Qed.

(* 165 *)
Definition CE (u: R) := B0 ⊗ I_2 .+ B3 ⊗ (Cexp u .* B0 .+ Cexp u .* B3).
Lemma equel16 : forall (a b c d : C) (u: R), CE u × (φ_2  a b c d) ≡ ((B0 .+ Cexp u .* B3) ⊗ I_2) × (φ_2  a b c d).
Proof.
intros.
unfold φ_2,CE.
operate_reduce.
Qed.

(* 169 *)
Definition not_CX := B0 ⊗ σX .+ B3 ⊗ I_2.
Lemma equel17 : forall (a b c d : C), CX × (φ_2  a b c d) ≡ (σX ⊗ I_2) × not_CX × (σX ⊗ I_2) × (φ_2  a b c d).
Proof.
intros.
unfold φ_2,not_CX.
operate_reduce.
Qed.


(* Three qubits *)
(* 170 *)
Definition CXX := B0 ⊗ I_2 ⊗ I_2 .+ B3 ⊗ σX ⊗ σX.
Definition CIX := B0 ⊗ I_2 ⊗ I_2 .+ B3 ⊗ I_2 ⊗ σX.
Lemma equel18 : forall (a b c d e f g h : C),
          CXX × (φ_3  a b c d e f g h) ≡ CIX × (CX ⊗ I_2) × (φ_3  a b c d e f g h).
Proof.
intros.
unfold φ_3,CXX,CIX.
operate_reduce.
Qed.


Lemma vq1 : forall v : Vector 2, exists a b : C, v ≡ a .* ∣0⟩ .+ b .* ∣1⟩ .
Proof.
intros v.
exists (v 0%nat 0%nat),(v 1%nat 0%nat).
autounfold with S_db;
autounfold with U_db.
intros x1 y1.
destruct x1 as [x Px], y1 as [y Py].
unfold get.
simpl.
destruct x,y. 
  + autorewrite with C_db; auto. 
  + exfalso; lia. 
  + destruct x.
     - autorewrite with C_db. auto.
     - exfalso. lia.
  + exfalso. lia.
Qed.

Lemma vq2 : forall v : Vector 4, exists v1 v2 : Vector 2, v ≡ ∣0⟩ ⊗ v1 .+ ∣1⟩ ⊗ v2.
Proof.
intros.
exists ((v 0%nat 0%nat) .* ∣0⟩ .+ (v 1%nat 0%nat) .* ∣1⟩),((v 2%nat 0%nat) .* ∣0⟩ .+ (v 3%nat 0%nat) .* ∣1⟩).
autounfold with S_db;
autounfold with U_db.
intros x1 y1.
destruct x1 as [x Px], y1 as [y Py].
unfold get.
intros.
simpl.
destruct x,y. 
  + autorewrite with C_db; auto. 
  + exfalso; lia. 
  + destruct x.
     - autorewrite with C_db. auto.
     - destruct x.
        * autorewrite with C_db. auto.
        * destruct x.
              { autorewrite with C_db. auto. }
              { exfalso. lia. }
  + exfalso. lia.
Qed.

Lemma vq3 : forall v : Vector 8, exists v1 v2 : Vector 4, v ≡ ∣0⟩ ⊗ v1 .+ ∣1⟩ ⊗ v2.
Proof.
intros.
exists ((v 0%nat 0%nat) .* ∣0,0⟩ .+ (v 1%nat 0%nat) .* ∣0,1⟩ .+ (v 2%nat 0%nat) .* ∣1,0⟩ .+ (v 3%nat 0%nat) .* ∣1,1⟩),
              ((v 4%nat 0%nat) .* ∣0,0⟩ .+ (v 5%nat 0%nat) .* ∣0,1⟩ .+ (v 6%nat 0%nat) .* ∣1,0⟩ .+ (v 7%nat 0%nat) .* ∣1,1⟩).
autounfold with S_db;
autounfold with U_db.
intros x1 y1.
destruct x1 as [x Px], y1 as [y Py].
unfold get.
intros.
simpl.
destruct x,y. 
  + autorewrite with C_db; auto. 
  + exfalso; lia. 
  + destruct x.
     - autorewrite with C_db. auto.
     - destruct x.
        * autorewrite with C_db. auto.
        * destruct x.
              { autorewrite with C_db. auto. }
              { destruct x.
                 - autorewrite with C_db. auto.
                 - destruct x.
                     * autorewrite with C_db. auto.
                     * destruct x.
                        { autorewrite with C_db. auto. }
                        { destruct x.
                            - autorewrite with C_db. auto.
                            - exfalso. lia. } }
  + exfalso. lia.
Qed.

Lemma unit_X' : forall v : Vector 2, σX × σX × v  ≡  v.
Proof.
intros.
pose proof vq1 v.
destruct H as [a [b H]].
rewrite H.

operate_reduce.
Qed.

Lemma eq2' : forall v : Vector 2,  (H × σX × H) × v ≡  σZ × v.
Proof.
intros.
pose proof vq1 v.
destruct H as [a [b H]].
rewrite H.

operate_reduce.
Qed.

Lemma equel5' : forall v : SWAP × v ≡  (CX × XC × CX) × v.
Proof.
intros.
pose proof vq2 v.
destruct H as [v1 [v2 H]].
rewrite H.
pose proof vq1 v1.
destruct H0 as [a [b H1]].
pose proof vq1 v2.
destruct H0 as [c [d H2]].
rewrite H1,H2.

operate_reduce.
Qed.

Lemma equel6' : forall v : Vector 4,  CZ × v ≡  ZC × v.
Proof.
intros.
pose proof vq2 v.
destruct H as [v1 [v2 H]].
rewrite H.
pose proof vq1 v1.
destruct H0 as [a [b H1]].
pose proof vq1 v2.
destruct H0 as [c [d H2]].
rewrite H1,H2.

operate_reduce.
Qed.

Lemma equel16' : forall (a b c d : C) (u: R), CE u × (φ_2  a b c d) ≡ ((B0 .+ Cexp u .* B3) ⊗ I_2) × (φ_2  a b c d).
Proof.
intros.
unfold φ_2,CE.
operate_reduce.
Qed.

(* 169 *)
Lemma equel17' : forall (a b c d : C), CX × (φ_2  a b c d) ≡ (σX ⊗ I_2) × not_CX × (σX ⊗ I_2) × (φ_2  a b c d).
Proof.
intros.
unfold φ_2,not_CX.
operate_reduce.
Qed.

Lemma equel18' : forall v : Vector 8,  CXX × v ≡  CIX × (CX ⊗ I_2) × v.
Proof.
intros.
pose proof vq3 v.
destruct H as [v21 [v22 H]].
rewrite H.
pose proof vq2 v21.
destruct H0 as [v1 [v2 H21]].
pose proof vq2 v22.
destruct H0 as [v3 [v4 H22]].
rewrite H21,H22.
pose proof vq1 v1.
destruct H0 as [a [b H1]].
pose proof vq1 v2.
destruct H0 as [c [d H2]].
pose proof vq1 v3.
destruct H0 as [e [f H3]].
pose proof vq1 v4.
destruct H0 as [g [h H4]].
rewrite H1,H2,H3,H4.

unfold CXX,CIX.
operate_reduce.
Qed.

Lemma vqn : forall (n : nat) (v :Vector (2*n)),exists  v1 v2 : Vector n, v ≡  ∣0⟩ ⊗ v1  .+  ∣1⟩ ⊗ v2 .
Proof.
intros.
induction n.
  * exists v,v. unfold mat_equiv,get. simpl in *. intros. destruct x. exfalso. lia.
  *
Admitted.


(* Bell Preparation *)
(* 24*)
Definition bell00 := /√2 .* (∣0,0⟩) .+ /√2 .* (∣1,1⟩).
Definition bell01 := /√2 .* (∣0,1⟩) .+ /√2 .* (∣1,0⟩).
Definition bell10 := /√2 .* (∣0,0⟩) .+ (-/√2) .* (∣1,1⟩).
Definition bell11 := /√2 .* (∣0,1⟩) .+ (-/√2) .* (∣1,0⟩).


Lemma pre_bell00 : bell00 ≡  CX × (H ⊗ I_2) × (∣0,0⟩).
Proof.
unfold bell00.
operate_reduce.
Qed.

Lemma pre_bell00'' :  super (CX × (H ⊗ I_2)) (density (∣0,0⟩)) ≡ density bell00.
Proof.
unfold bell00.
super_reduce.
Qed.

Lemma pre_bell01 : bell01 ≡ CX × (H ⊗ I_2) × (∣0,1⟩).
Proof.
unfold bell01.
operate_reduce.
Qed.

Lemma pre_bell10 : bell10 ≡ CX × (H ⊗ I_2) × (∣1,0⟩).
Proof.
unfold bell10.
operate_reduce.
Qed.

Lemma pre_bell11 : bell11 ≡ CX × (H ⊗ I_2) × (∣1,1⟩).
Proof.
unfold bell11.
operate_reduce.
Qed.


(* GHZ Preparation *)
Lemma GHZ_ket0_3 : /√2 .* (∣0,0,0⟩) .+ /√2 .* (∣1,1,1⟩) ≡  (I_2 ⊗ CX) × (CX ⊗ I_2) × (H ⊗ I_2 ⊗ I_2) × (∣0,0,0⟩).
Proof.
autounfold with G2_db.
operate_reduce.
Qed.


(* rotation *)
Check rotation_0.
Definition rX (ϕ : R) := cos (ϕ/2) .* I_2 .+ Ci * sin (ϕ/2) .* σX.
Definition rY (ϕ : R) := cos (ϕ/2) .* I_2 .+ Ci * sin (ϕ/2) .* σY.
Definition rZ (ϕ : R) := cos (ϕ/2) .* I_2 .+ Ci * sin (ϕ/2) .* σZ.
Definition rN (ϕ n1 n2 n3 : R):= cos (ϕ/2) .* I_2 .+ Ci * sin (ϕ/2) .* (n1 .* σX .+ n2 .* σY .+ n3 .* σZ).


Lemma equel19 : forall (a b: C), PT × (φ_1  a b) ≡ Cexp (PI/8) .* rZ (PI/4) × (φ_1  a b).
Proof.
intros.
unfold φ_1,rZ,PT.
operate_reduce.
replace (PI / 4 / 2)%R with (PI / 8)%R by lra.
Admitted.


(* Fredkin *)
Definition FRE := B0 ⊗ I_2 ⊗ I_2 .+ B3 ⊗ SWAP.


(* Toffoli *)
(* 167 *)
Definition TOF := B0 ⊗ I_2 ⊗ I_2 .+ B3 ⊗ CX.
(* Definition PS := B0 .+ Ci .* B3.
Definition PT := B0 .+ (/√2 + /√2 * Ci) .* B3. *)


(* Fredkin *)
Definition FRE := B0 ⊗ I_2 ⊗ I_2 .+ B3 ⊗ SWAP.

