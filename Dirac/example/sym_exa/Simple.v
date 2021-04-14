 Require Export Dirac.
 Require Export Equival.

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
  + autorewrite with C_db; auto; exfalso; lia.
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




(* Unitary *)
Lemma unit_X' : forall v : Vector 2,  σX × σX × v ≡ I_2 × v.
Proof.
intros.
pose proof vq1 v.
destruct H as [a [b H]].
rewrite H.

operate_reduce.
Qed.

Lemma unit_X : σX × σX ≡ I_2.
Proof.
rewrite MatrixEquiv_spec.
apply unit_X'.
Qed.

Lemma unit_X_d : forall  v : Vector 2,   σX × σX × v × (σX × σX × v) † ≡ I_2 × v × (I_2 × v) †.
Proof.
intros.
rewrite unit_X'.
reflexivity.
Qed.

Lemma unit_X_s : forall  v : Vector 2,   σX × σX × v  ≈ I_2 × v.
Proof.
intros.
by_den.
apply unit_X_d.
Qed.

Lemma unit_X_o : σX × σX ≈ I_2.
Proof.
by_effect.
apply unit_X_s.
Qed.



Lemma unit_Y' : forall v : Vector 2,  σY × σY × v ≡ I_2 × v.
Proof.
intros.
pose proof vq1 v.
destruct H as [a [b H]].
rewrite H.

operate_reduce.
Qed.

Lemma unit_Y : σY × σY ≡ I_2.
Proof.
rewrite MatrixEquiv_spec.
apply unit_Y'.
Qed.

Lemma unit_Y_o : σY × σY ≈ I_2.
Proof.
by_effect.
by_def1.
apply unit_Y'.
Qed.



Lemma unit_Z' : forall v : Vector 2,  σZ × σZ × v ≡ I_2 × v.
Proof.
intros.
pose proof vq1 v.
destruct H as [a [b H]].
rewrite H.

operate_reduce.
Qed.

Lemma unit_Z : σZ × σZ  ≡  I_2.
Proof.
rewrite MatrixEquiv_spec.
apply unit_Z'.
Qed.

Lemma unit_Z_o : σZ × σZ  ≈  I_2.
Proof.
by_effect.
by_def1.
apply unit_Z'.
Qed.



Lemma unit_H' : forall v : Vector 2,  H × H × v ≡ I_2 × v.
Proof.
intros.
pose proof vq1 v.
destruct H as [a [b H]].
rewrite H.

operate_reduce.
Qed.

Lemma unit_H : H × H ≡ I_2.
Proof.
rewrite MatrixEquiv_spec.
apply unit_H'.
Qed.

Lemma unit_H_o : H × H ≈ I_2.
Proof.
by_effect.
by_def1.
apply unit_H'.
Qed.



Lemma unit_CX' : forall v : Vector 4,  CX × CX × v ≡ (I_2 ⊗ I_2) × v.
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


Lemma unit_CX : CX × CX ≡ (I_2 ⊗ I_2).
Proof.
rewrite MatrixEquiv_spec.
apply unit_CX'.
Qed.

Lemma unit_CX_o : CX × CX ≈ (I_2 ⊗ I_2).
Proof.
by_effect.
by_def1.
apply unit_CX'.
Qed.



(* Equation *)

(* One qubit *)

(* 174 *)
Lemma Eq1' : forall v : Vector 2, /√2 .* (σX .+ σZ) × v ≡  H × v.
Proof.
intros.
pose proof vq1 v.
destruct H as [a [b H]].
rewrite H.

operate_reduce.
Qed.

Lemma Eq1 : /√2 .* (σX .+ σZ) ≡ H.
Proof.
rewrite MatrixEquiv_spec.
apply Eq1'.
Qed.

Lemma Eq1_o : /√2 .* (σX .+ σZ) ≈ H.
Proof.
by_effect.
by_def1.
apply Eq1'.
Qed.



(* 177 *)
Lemma Eq2' : forall v : Vector 2, (H × σX × H) × v ≡ σZ × v.
Proof.
intros.
pose proof vq1 v.
destruct H as [a [b H]].
rewrite H.

operate_reduce.
Qed.

Lemma Eq2 : H × σX × H ≡ σZ.
Proof.
rewrite MatrixEquiv_spec.
apply Eq2'.
Qed.

Lemma Eq2_o : H × σX × H ≈ σZ.
Proof.
by_effect.
by_def1.
apply Eq2'.
Qed.



Lemma Eq3' : forall v : Vector 2, (H × σY × H) × v ≡ -1 .* σY × v.
Proof.
intros.
pose proof vq1 v.
destruct H as [a [b H]].
rewrite H.

operate_reduce.
Qed.

Lemma Eq3 : H × σY × H ≡ -1 .* σY.
Proof.
rewrite MatrixEquiv_spec.
apply Eq3'.
Qed.

Lemma Eq3_o : H × σY × H ≈ -1 .* σY.
Proof.
by_effect.
by_def1.
apply Eq3'.
Qed.



Lemma Eq4' : forall v : Vector 2, (H × σZ × H) × v ≡ σX × v.
Proof.
intros.
pose proof vq1 v.
destruct H as [a [b H]].
rewrite H.

operate_reduce.
Qed.

Lemma Eql4 : H × σZ × H ≡ σX.
Proof.
rewrite MatrixEquiv_spec.
apply Eq4'.
Qed.

Lemma Eq4_o : H × σZ × H ≈ σX.
Proof.
by_effect.
by_def1.
apply Eq4'.
Qed.



(* Two qubits *)

(* Definition SWAP :=  B0 ⊗ B0 .+ B1 ⊗ B2 .+ B2 ⊗ B1 .+ B3 ⊗ B3.
Definition CA_1 {n} (A : Matrix n n) := B0 ⊗ I_2 .+ B3 ⊗ A.
Definition AC_1 {n} (A : Matrix n n) := A ⊗ B3 .+ I_2 ⊗ B0. *)
(* 179 *)
Lemma Eq5' : forall v : Vector 4, CZ × v ≡ (I_2 ⊗ H) × CX × (I_2 ⊗ H) × v.
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

Lemma Eq5 : CZ ≡ (I_2 ⊗ H) × CX × (I_2 ⊗ H).
Proof.
rewrite MatrixEquiv_spec.
apply Eq5'.
Qed.

Lemma Eq5_o : CZ ≈ (I_2 ⊗ H) × CX × (I_2 ⊗ H).
Proof.
by_effect.
by_def1.
apply Eq5'.
Qed.



(* 185 *)
Lemma Eq6' : forall v : Vector 4, CX × (σX ⊗ I_2) × CX × v ≡  (σX ⊗ σX) × v.
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

Lemma Eq6 : CX × (σX ⊗ I_2) × CX ≡ (σX ⊗ σX).
Proof.
rewrite MatrixEquiv_spec.
apply Eq6'.
Qed.

Lemma Eq6_o : CX × (σX ⊗ I_2) × CX ≈ (σX ⊗ σX).
Proof.
by_effect.
by_def1.
apply Eq6'.
Qed.



Lemma Eq7' : forall v : Vector 4, CX × (σY ⊗ I_2) × CX × v ≡  (σY ⊗ σX) × v.
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

Lemma Eq7 : CX × (σY ⊗ I_2) × CX ≡ (σY ⊗ σX).
Proof.
rewrite MatrixEquiv_spec.
apply Eq7'.
Qed.

Lemma Eq7_o : CX × (σY ⊗ I_2) × CX ≈ (σY ⊗ σX).
Proof.
by_effect.
by_def1.
apply Eq7'.
Qed.



Lemma Eq8' : forall v : Vector 4, CX × (σZ ⊗ I_2) × CX × v ≡  (σZ ⊗ I_2) × v.
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

Lemma Eq8 : CX × (σZ ⊗ I_2) × CX ≡ (σZ ⊗ I_2).
Proof.
rewrite MatrixEquiv_spec.
apply Eq8'.
Qed.

Lemma Eq8_o : CX × (σZ ⊗ I_2) × CX ≈ (σZ ⊗ I_2).
Proof.
by_effect.
by_def1.
apply Eq8'.
Qed.



Lemma Eq9' : forall v : Vector 4, CX × (I_2 ⊗ σX) × CX × v ≡  (I_2 ⊗ σX) × v.
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

Lemma Eq9 : CX × (I_2 ⊗ σX) × CX ≡ (I_2 ⊗ σX).
Proof.
rewrite MatrixEquiv_spec.
apply Eq9'.
Qed.

Lemma Eq9_o : CX × (I_2 ⊗ σX) × CX ≈ (I_2 ⊗ σX).
Proof.
by_effect.
by_def1.
apply Eq9'.
Qed.



Lemma Eq10' : forall v : Vector 4, CX × (I_2 ⊗ σY) × CX × v ≡  (σZ ⊗ σY) × v.
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

Lemma Eq10 : CX × (I_2 ⊗ σY) × CX ≡ (σZ ⊗ σY).
Proof.
rewrite MatrixEquiv_spec.
apply Eq10'.
Qed.

Lemma Eq10_o : CX × (I_2 ⊗ σY) × CX ≈ (σZ ⊗ σY).
Proof.
by_effect.
by_def1.
apply Eq10'.
Qed.



Lemma Eq11' : forall v : Vector 4, CX × (I_2 ⊗ σZ) × CX × v ≡  (σZ ⊗ σZ) × v.
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

Lemma Eq11 : CX × (I_2 ⊗ σZ) × CX ≡ (σZ ⊗ σZ).
Proof.
rewrite MatrixEquiv_spec.
apply Eq11'.
Qed.

Lemma Eq11_o : CX × (I_2 ⊗ σZ) × CX ≈ (σZ ⊗ σZ).
Proof.
by_effect.
by_def1.
apply Eq11'.
Qed.



Lemma Eq12' : forall v : Vector 4, XC × v ≡ (H ⊗ H) × CX × (H ⊗ H) × v.
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

Lemma Eq12 : XC ≡ (H ⊗ H) × CX × (H ⊗ H).
Proof.
rewrite MatrixEquiv_spec.
apply Eq12'.
Qed.

Lemma Eq12_o : XC ≈ (H ⊗ H) × CX × (H ⊗ H).
Proof.
by_effect.
by_def1.
apply Eq12'.
Qed.



(* 179 *)
Lemma Eq13' : forall v : Vector 4, CZ × v ≡ ZC × v.
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

Lemma Eq13 : CZ ≡ ZC.
Proof.
rewrite MatrixEquiv_spec.
apply Eq13'.
Qed.

Lemma Eq13_o : CZ ≈ ZC.
Proof.
by_effect.
by_def1.
apply Eq13'.
Qed.



Lemma Eq14' : forall v : Vector 4, XC × v ≡ (H ⊗ H) × CX × (H ⊗ H) × v.
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

Lemma Eq14 : XC ≡ (H ⊗ H) × CX × (H ⊗ H).
Proof.
rewrite MatrixEquiv_spec.
apply Eq14'.
Qed.

Lemma Eq14_o : XC ≈ (H ⊗ H) × CX × (H ⊗ H).
Proof.
by_effect.
by_def1.
apply Eq14'.
Qed.



(* 23 *)
Lemma Eq15' : forall v : Vector 4, SWAP × v ≡  (CX × XC × CX) × v.
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

Lemma Eq15 : SWAP ≡ CX × XC × CX.
Proof.
rewrite MatrixEquiv_spec.
apply Eq15'.
Qed.

Lemma Eq15_o : SWAP ≈ CX × XC × CX.
Proof.
by_effect.
by_def1.
apply Eq15'.
Qed.



(* 185 *)
Lemma Eq16' : forall v : Vector 4, not_CX × v ≡ (σX ⊗ I_2) × CX × (σX ⊗ I_2) × v.
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

Lemma Eq16 : not_CX ≡ (σX ⊗ I_2) × CX × (σX ⊗ I_2).
Proof.
rewrite MatrixEquiv_spec.
apply Eq16'.
Qed.

Lemma Eq16_o : not_CX ≈ (σX ⊗ I_2) × CX × (σX ⊗ I_2).
Proof.
by_effect.
by_def1.
apply Eq16'.
Qed.



(* 180 *)
Definition CE (u: R) := B0 ⊗ I_2 .+ B3 ⊗ (Cexp u .* B0 .+ Cexp u .* B3).
Global Hint Unfold  CE : Gn_db.
Lemma Eq17' : forall (v : Vector 4) (u: R), CE u × v ≡ ((B0 .+ Cexp u .* B3) ⊗ I_2) × v.
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

Lemma Eq17 : forall (u:R), CE u ≡ ((B0 .+ Cexp u .* B3) ⊗ I_2).
Proof.
intros.
rewrite MatrixEquiv_spec.
intros.
apply Eq17'.
Qed.

Lemma Eq17_o : forall (u:R), CE u ≈ ((B0 .+ Cexp u .* B3) ⊗ I_2).
Proof.
intros.
by_effect.
by_def1.
apply Eq17'.
Qed.



(* Three qubits *)

(* 186 *)
Definition CXX := B0 ⊗ I_2 ⊗ I_2 .+ B3 ⊗ σX ⊗ σX.
Definition CIX := B0 ⊗ I_2 ⊗ I_2 .+ B3 ⊗ I_2 ⊗ σX.
Global Hint Unfold  CXX CIX : Gn_db.
Lemma Eq18' : forall (v : Vector 8),
          CXX × v ≡ CIX × (CX ⊗ I_2) × v.
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

operate_reduce.
Qed.

Lemma Eq18 : CXX ≡ CIX × (CX ⊗ I_2).
Proof.
rewrite MatrixEquiv_spec.
apply Eq18'.
Qed.

Lemma Eq18_o : CXX ≈ CIX × (CX ⊗ I_2).
Proof.
by_effect.
by_def1.
apply Eq18'.
Qed.


Lemma vqn : forall (n : nat) (v :Vector (2*(N.of_nat n))),exists  v1 v2 : Vector (N.of_nat n), v ≡  ∣0⟩ ⊗ v1  .+  ∣1⟩ ⊗ v2 .
Proof.
intros.
induction n.
  * exists v,v. unfold mat_equiv,get. simpl in *. intros. destruct x. exfalso. lia.
  *
Admitted.



(* Bell Preparation *)
(* 24*)
Definition bl00 := /√2 .* (∣0,0⟩) .+ /√2 .* (∣1,1⟩).
Definition bl01 := /√2 .* (∣0,1⟩) .+ /√2 .* (∣1,0⟩).
Definition bl10 := /√2 .* (∣0,0⟩) .+ (-/√2) .* (∣1,1⟩).
Definition bl11 := /√2 .* (∣0,1⟩) .+ (-/√2) .* (∣1,0⟩).


Lemma pb00' : bl00 ≡  CX × (H ⊗ I_2) × (∣0,0⟩).
Proof.
unfold bl00.
operate_reduce.
Qed.

Lemma pb00'' : bl00 ≈  CX × (H ⊗ I_2) × (∣0,0⟩).
Proof.
by_def1.
apply pb00'.
Qed.

Lemma pb00 :  super (CX × (H ⊗ I_2)) (density (∣0,0⟩)) ≡ density bl00.
Proof.
unfold bl00.
super_reduce.
Qed.

Lemma pb01'' : bl01 ≈ CX × (H ⊗ I_2) × (∣0,1⟩).
Proof.
by_def1.
unfold bl01.
operate_reduce.
Qed.

Lemma pb01 :  super (CX × (H ⊗ I_2)) (density (∣0,1⟩)) ≡ density bl01.
Proof.
unfold bl01.
super_reduce.
Qed.

Lemma pb10'' : bl10 ≈ CX × (H ⊗ I_2) × (∣1,0⟩).
Proof.
by_def1.
unfold bl10.
operate_reduce.
Qed.

Lemma pb10 :  super (CX × (H ⊗ I_2)) (density (∣1,0⟩)) ≡ density bl10.
Proof.
unfold bl10.
super_reduce.
Qed.

Lemma pb11'' : bl11 ≈ CX × (H ⊗ I_2) × (∣1,1⟩).
Proof.
by_def1.
unfold bl11.
operate_reduce.
Qed.

Lemma pb11 :  super (CX × (H ⊗ I_2)) (density (∣1,1⟩)) ≡ density bl11.
Proof.
unfold bl11.
super_reduce.
Qed.



(* GHZ Preparation *)
Lemma GHZ_ket0_3 : /√2 .* (∣0,0,0⟩) .+ /√2 .* (∣1,1,1⟩) ≈  (I_2 ⊗ CX) × (CX ⊗ I_2) × (H ⊗ I_2 ⊗ I_2) × (∣0,0,0⟩).
Proof.
by_def1.
operate_reduce.
Qed.
(* Finished transaction in 15.83 secs (15.578u,0.031s) (successful) *)



(* rotation *)
Definition rX (ϕ : R) := cos (ϕ/2) .* I_2 .+ Ci * sin (ϕ/2) .* σX.
Definition rY (ϕ : R) := cos (ϕ/2) .* I_2 .+ Ci * sin (ϕ/2) .* σY.
Definition rZ (ϕ : R) := cos (ϕ/2) .* I_2 .+ Ci * sin (ϕ/2) .* σZ.
Definition rN (ϕ n1 n2 n3 : R):= cos (ϕ/2) .* I_2 .+ Ci * sin (ϕ/2) .* (n1 .* σX .+ n2 .* σY .+ n3 .* σZ).


Lemma Eq19 : forall (v : Vector 2), PT × v ≡ Cexp (PI/8) .* rZ (PI/4) × v.
Proof.
intros.
pose proof vq1 v.
destruct H as [a [b H]].
rewrite H.

unfold rZ,PT.
operate_reduce.
replace (PI / 4 / 2)%R with (PI / 8)%R by lra.
Admitted.



(* Toffoli *)
(* 167 *)
Definition TOF := B0 ⊗ I_2 ⊗ I_2 .+ B3 ⊗ CX.
(* Definition PS := B0 .+ Ci .* B3.
Definition PT := B0 .+ (/√2 + /√2 * Ci) .* B3. *)


(* Fredkin *)
Definition FRE := B0 ⊗ I_2 ⊗ I_2 .+ B3 ⊗ SWAP.
