Require Export Dirac.
Require Export StateAndOperator.
Declare Scope QE.
Local Open Scope QE.


Definition GHZ := /√2 .* (∣0,0,0⟩) .+ /√2 .* (∣1,1,1⟩).
Definition φ (a b : C) : Vector 2 := a .* ∣0⟩ .+ b .* ∣1⟩.
(* Step-by-step *)

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

Lemma ss0' :  forall (v : Vector 2),
(M0 ⊗ M0 ⊗ M0 ⊗ I_2) × (I_2 ⊗ H ⊗ H ⊗ I_2) × (XC ⊗ I_2 ⊗ I_2) × (v ⊗ GHZ) ≡ / √ 2 * / 2  .* ∣0⟩ ⊗ ∣0⟩ ⊗ ∣0⟩ ⊗ v .
Proof.
intros.
pose proof vq1 v.
destruct H as [a [b H]].
rewrite H.

unfold GHZ.
operate_reduce.
Qed.

Lemma ss0 :  forall (v : Vector 2),
(M0 ⊗ M0 ⊗ M0 ⊗ I_2) × (I_2 ⊗ H ⊗ H ⊗ I_2) × (XC ⊗ I_2 ⊗ I_2) × (v ⊗ GHZ) ≈ / √ 2 * / 2  .* ∣0⟩ ⊗ ∣0⟩ ⊗ ∣0⟩ ⊗ v .
Proof.
intros.
by_den.
pose proof vq1 v.
destruct H as [a [b H]].
rewrite H.

rewrite ss0'; reflexivity.
Qed.


Lemma ss1' :  forall (v : Vector 2),
(I_2 ⊗ I_2 ⊗ I_2 ⊗ σZ) × (M0 ⊗ M0 ⊗ M1 ⊗ I_2) × (I_2 ⊗ H ⊗ H ⊗ I_2) × (XC ⊗ I_2 ⊗ I_2) × (v⊗ GHZ) ≡ / √ 2 * / 2  .* ∣0⟩ ⊗ ∣0⟩ ⊗ ∣1⟩ ⊗ v .
Proof.
intros.
pose proof vq1 v.
destruct H as [a [b H]].
rewrite H.

unfold GHZ.
operate_reduce.
Qed.

Lemma ss1 :  forall (v : Vector 2),
(I_2 ⊗ I_2 ⊗ I_2 ⊗ σZ) × (M0 ⊗ M0 ⊗ M1 ⊗ I_2) × (I_2 ⊗ H ⊗ H ⊗ I_2) × (XC ⊗ I_2 ⊗ I_2) × (v⊗ GHZ) ≈ / √ 2 * / 2  .* ∣0⟩ ⊗ ∣0⟩ ⊗ ∣1⟩ ⊗ v .
Proof.
intros.
by_den.
pose proof vq1 v.
destruct H as [a [b H]].
rewrite H.

rewrite ss1'; reflexivity.
Qed.


Lemma ss2' :  forall (v : Vector 2),
(I_2 ⊗ I_2 ⊗ I_2 ⊗ σZ) × (M0 ⊗ M1 ⊗ M0 ⊗ I_2) × (I_2 ⊗ H ⊗ H ⊗ I_2) × (XC ⊗ I_2 ⊗ I_2) × (v⊗ GHZ) ≡ / √ 2 * / 2  .* ∣0⟩ ⊗ ∣1⟩ ⊗ ∣0⟩ ⊗  v .
Proof.
intros.
pose proof vq1 v.
destruct H as [a [b H]].
rewrite H.

unfold GHZ.
operate_reduce.
Qed.

Lemma ss2 :  forall (v : Vector 2),
(I_2 ⊗ I_2 ⊗ I_2 ⊗ σZ) × (M0 ⊗ M1 ⊗ M0 ⊗ I_2) × (I_2 ⊗ H ⊗ H ⊗ I_2) × (XC ⊗ I_2 ⊗ I_2) × (v ⊗ GHZ) ≈ / √ 2 * / 2  .* ∣0⟩ ⊗ ∣1⟩ ⊗ ∣0⟩ ⊗  v .
Proof.
intros.
by_den.
pose proof vq1 v.
destruct H as [a [b H]].
rewrite H.

rewrite ss2'; reflexivity.
Qed.


Lemma ss3' :  forall (v : Vector 2),
(I_2 ⊗ I_2 ⊗ I_2 ⊗ σZ) × (I_2 ⊗ I_2 ⊗ I_2 ⊗ σZ) × (M0 ⊗ M1 ⊗ M1 ⊗ I_2) × (I_2 ⊗ H ⊗ H ⊗ I_2) × (XC ⊗ I_2 ⊗ I_2) × (v ⊗ GHZ) ≡ / √ 2 * / 2  .* ∣0⟩ ⊗ ∣1⟩ ⊗ ∣1⟩ ⊗  v .
Proof.
intros.
pose proof vq1 v.
destruct H as [a [b H]].
rewrite H.

unfold GHZ.
operate_reduce.
Qed.

Lemma ss3 :  forall (v : Vector 2),
(I_2 ⊗ I_2 ⊗ I_2 ⊗ σZ) × (I_2 ⊗ I_2 ⊗ I_2 ⊗ σZ) × (M0 ⊗ M1 ⊗ M1 ⊗ I_2) × (I_2 ⊗ H ⊗ H ⊗ I_2) × (XC ⊗ I_2 ⊗ I_2) × (v ⊗ GHZ) ≈ / √ 2 * / 2  .* ∣0⟩ ⊗ ∣1⟩ ⊗ ∣1⟩ ⊗  v .
Proof.
intros.
by_den.
pose proof vq1 v.
destruct H as [a [b H]].
rewrite H.

rewrite ss3'; reflexivity.
Qed.


Lemma ss4' :  forall (v : Vector 2),
(I_2 ⊗ I_2 ⊗ I_2 ⊗ σX) × (M1 ⊗ M0 ⊗ M0 ⊗ I_2) × (I_2 ⊗ H ⊗ H ⊗ I_2) × (XC ⊗ I_2 ⊗ I_2) × (v ⊗ GHZ) ≡ / √ 2 * / 2  .* ∣1⟩ ⊗ ∣0⟩ ⊗ ∣0⟩ ⊗  v .
Proof.
intros.
pose proof vq1 v.
destruct H as [a [b H]].
rewrite H.

unfold GHZ.
operate_reduce.
Qed.

Lemma ss4 :  forall (v : Vector 2),
(I_2 ⊗ I_2 ⊗ I_2 ⊗ σX) × (M1 ⊗ M0 ⊗ M0 ⊗ I_2) × (I_2 ⊗ H ⊗ H ⊗ I_2) × (XC ⊗ I_2 ⊗ I_2) × (v ⊗ GHZ) ≈ / √ 2 * / 2  .* ∣1⟩ ⊗ ∣0⟩ ⊗ ∣0⟩ ⊗  v .
Proof.
intros.
by_den.
pose proof vq1 v.
destruct H as [a [b H]].
rewrite H.

rewrite ss4'; reflexivity.
Qed.


Lemma ss5' :  forall (v : Vector 2),
(I_2 ⊗ I_2 ⊗ I_2 ⊗ σX) × (I_2 ⊗ I_2 ⊗ I_2 ⊗ σZ) × (M1 ⊗ M0 ⊗ M1 ⊗ I_2) × (I_2 ⊗ H ⊗ H ⊗ I_2) × (XC ⊗ I_2 ⊗ I_2) × (v ⊗ GHZ) ≡ / √ 2 * / 2  .* ∣1⟩ ⊗ ∣0⟩ ⊗ ∣1⟩ ⊗  v .
Proof.
intros.
pose proof vq1 v.
destruct H as [a [b H]].
rewrite H.

unfold GHZ.
operate_reduce.
Qed.

Lemma ss5 :  forall (v : Vector 2),
(I_2 ⊗ I_2 ⊗ I_2 ⊗ σX) × (I_2 ⊗ I_2 ⊗ I_2 ⊗ σZ) × (M1 ⊗ M0 ⊗ M1 ⊗ I_2) × (I_2 ⊗ H ⊗ H ⊗ I_2) × (XC ⊗ I_2 ⊗ I_2) × (v ⊗ GHZ) ≈ / √ 2 * / 2  .* ∣1⟩ ⊗ ∣0⟩ ⊗ ∣1⟩ ⊗  v .
Proof.
intros.
by_den.
pose proof vq1 v.
destruct H as [a [b H]].
rewrite H.

rewrite ss5'; reflexivity.
Qed.


Lemma ss6' :  forall (v : Vector 2),
(I_2 ⊗ I_2 ⊗ I_2 ⊗ σX) × (I_2 ⊗ I_2 ⊗ I_2 ⊗ σZ) × (M1 ⊗ M1 ⊗ M0 ⊗ I_2) × (I_2 ⊗ H ⊗ H ⊗ I_2) × (XC ⊗ I_2 ⊗ I_2) × (v ⊗ GHZ) ≡ / √ 2 * / 2  .* ∣1⟩ ⊗ ∣1⟩ ⊗ ∣0⟩ ⊗  v .
Proof.
intros.
pose proof vq1 v.
destruct H as [a [b H]].
rewrite H.

unfold GHZ.
operate_reduce.
Qed.

Lemma ss6 :  forall (v : Vector 2),
(I_2 ⊗ I_2 ⊗ I_2 ⊗ σX) × (I_2 ⊗ I_2 ⊗ I_2 ⊗ σZ) × (M1 ⊗ M1 ⊗ M0 ⊗ I_2) × (I_2 ⊗ H ⊗ H ⊗ I_2) × (XC ⊗ I_2 ⊗ I_2) × (v ⊗ GHZ) ≈ / √ 2 * / 2  .* ∣1⟩ ⊗ ∣1⟩ ⊗ ∣0⟩ ⊗  v .
Proof.
intros.
by_den.
pose proof vq1 v.
destruct H as [a [b H]].
rewrite H.

rewrite ss6'; reflexivity.
Qed.


Lemma ss7' :  forall (v : Vector 2),
(I_2 ⊗ I_2 ⊗ I_2 ⊗ σX) × (I_2 ⊗ I_2 ⊗ I_2 ⊗ σZ) × (I_2 ⊗ I_2 ⊗ I_2 ⊗ σZ) × (M1 ⊗ M1 ⊗ M1 ⊗ I_2) × (I_2 ⊗ H ⊗ H ⊗ I_2) × (XC ⊗ I_2 ⊗ I_2) × (v ⊗ GHZ) ≡ / √ 2 * / 2  .* ∣1⟩ ⊗ ∣1⟩ ⊗ ∣1⟩ ⊗  v .
Proof.
intros.
pose proof vq1 v.
destruct H as [a [b H]].
rewrite H.

unfold GHZ.
operate_reduce.
Qed.

Lemma ss7 :  forall (v : Vector 2),
(I_2 ⊗ I_2 ⊗ I_2 ⊗ σX) × (I_2 ⊗ I_2 ⊗ I_2 ⊗ σZ) × (I_2 ⊗ I_2 ⊗ I_2 ⊗ σZ) × (M1 ⊗ M1 ⊗ M1 ⊗ I_2) × (I_2 ⊗ H ⊗ H ⊗ I_2) × (XC ⊗ I_2 ⊗ I_2) × (v ⊗ GHZ) ≈ / √ 2 * / 2  .* ∣1⟩ ⊗ ∣1⟩ ⊗ ∣1⟩ ⊗  v .
Proof.
intros.
by_den.
pose proof vq1 v.
destruct H as [a [b H]].
rewrite H.

rewrite ss7'; reflexivity.
Qed.



(* Density *)
Lemma Dss0' :  forall (v : Vector 2),
super ((M0 ⊗ M0 ⊗ M0 ⊗ I_2) × (I_2 ⊗ H ⊗ H ⊗ I_2) × (XC ⊗ I_2 ⊗ I_2)) (density (v ⊗ GHZ)) ≡ density (/ √ 2 * / 2  .* ∣0⟩ ⊗ ∣0⟩  ⊗ ∣0⟩ ⊗ v).
Proof.
intros.
pose proof vq1 v.
destruct H as [a [b H]].
unfold super,density.
rewrite H.

unfold GHZ.
super_reduce.
Qed.

Lemma Dss0 :  forall (v : Vector 2),
super ((M0 ⊗ M0 ⊗ M0 ⊗ I_2) × (I_2 ⊗ H ⊗ H ⊗ I_2) × (XC ⊗ I_2 ⊗ I_2)) (density (v ⊗ GHZ)) ≈ density (/ √ 2 * / 2  .* ∣0⟩ ⊗ ∣0⟩  ⊗ ∣0⟩ ⊗ v).
Proof.
intros.
by_def1.

rewrite Dss0';reflexivity.
Qed.


Lemma Dss1' :  forall (v : Vector 2),
super ((I_2 ⊗ I_2 ⊗ I_2 ⊗ σZ) × (M0 ⊗ M0 ⊗ M1 ⊗ I_2) × (I_2 ⊗ H ⊗ H ⊗ I_2) × (XC ⊗ I_2 ⊗ I_2)) (density (v ⊗ GHZ)) ≡ density (/ √ 2 * / 2  .* ∣0⟩ ⊗ ∣0⟩  ⊗ ∣1⟩ ⊗ v).
Proof.
intros.
pose proof vq1 v.
destruct H as [a [b H]].
unfold super,density.
rewrite H.

unfold GHZ.
super_reduce.
Qed.

Lemma Dss1 :  forall (v : Vector 2),
super ((I_2 ⊗ I_2 ⊗ I_2 ⊗ σZ) × (M0 ⊗ M0 ⊗ M1 ⊗ I_2) × (I_2 ⊗ H ⊗ H ⊗ I_2) × (XC ⊗ I_2 ⊗ I_2)) (density (v ⊗ GHZ)) ≈ density (/ √ 2 * / 2  .* ∣0⟩ ⊗ ∣0⟩  ⊗ ∣1⟩ ⊗ v).
Proof.
intros.
by_def1.

rewrite Dss1';reflexivity.
Qed.

Lemma Dss2' :  forall (v : Vector 2),
super ((I_2 ⊗ I_2 ⊗ I_2 ⊗ σZ) × (M0 ⊗ M1 ⊗ M0 ⊗ I_2) × (I_2 ⊗ H ⊗ H ⊗ I_2) × (XC ⊗ I_2 ⊗ I_2)) (density (v ⊗ GHZ)) ≡ density (/ √ 2 * / 2  .* ∣0⟩ ⊗ ∣1⟩  ⊗ ∣0⟩ ⊗ v).
Proof.
intros.
pose proof vq1 v.
destruct H as [a [b H]].
unfold super,density.
rewrite H.

unfold GHZ.
super_reduce.
Qed.

Lemma Dss2 :  forall (v : Vector 2),
super ((I_2 ⊗ I_2 ⊗ I_2 ⊗ σZ) × (M0 ⊗ M1 ⊗ M0 ⊗ I_2) × (I_2 ⊗ H ⊗ H ⊗ I_2) × (XC ⊗ I_2 ⊗ I_2)) (density (v ⊗ GHZ)) ≈ density (/ √ 2 * / 2  .* ∣0⟩ ⊗ ∣1⟩  ⊗ ∣0⟩ ⊗ v).
Proof.
intros.
by_def1.

rewrite Dss2';reflexivity.
Qed.


Lemma Dss3' :  forall (v : Vector 2),
super ((I_2 ⊗ I_2 ⊗ I_2 ⊗ σZ) × (I_2 ⊗ I_2 ⊗ I_2 ⊗ σZ) × (M0 ⊗ M1 ⊗ M1 ⊗ I_2) × (I_2 ⊗ H ⊗ H ⊗ I_2) × (XC ⊗ I_2 ⊗ I_2)) (density (v ⊗ GHZ)) ≡ density (/ √ 2 * / 2  .* ∣0⟩ ⊗ ∣1⟩  ⊗ ∣1⟩ ⊗ v).
Proof.
intros.
pose proof vq1 v.
destruct H as [a [b H]].
unfold super,density.
rewrite H.

unfold GHZ.
super_reduce.
Qed.

Lemma Dss3 :  forall (v : Vector 2),
super ((I_2 ⊗ I_2 ⊗ I_2 ⊗ σZ) × (I_2 ⊗ I_2 ⊗ I_2 ⊗ σZ) × (M0 ⊗ M1 ⊗ M1 ⊗ I_2) × (I_2 ⊗ H ⊗ H ⊗ I_2) × (XC ⊗ I_2 ⊗ I_2)) (density (v ⊗ GHZ)) ≈ density (/ √ 2 * / 2  .* ∣0⟩ ⊗ ∣1⟩  ⊗ ∣1⟩ ⊗ v).
Proof.
intros.
by_def1.

rewrite Dss3';reflexivity.
Qed.


Lemma Dss4' :  forall (v : Vector 2),
super ((I_2 ⊗ I_2 ⊗ I_2 ⊗ σX) × (M1 ⊗ M0 ⊗ M0 ⊗ I_2) × (I_2 ⊗ H ⊗ H ⊗ I_2) × (XC ⊗ I_2 ⊗ I_2)) (density (v ⊗ GHZ)) ≡ density (/ √ 2 * / 2  .* ∣1⟩ ⊗ ∣0⟩  ⊗ ∣0⟩ ⊗ v).
Proof.
intros.
pose proof vq1 v.
destruct H as [a [b H]].
unfold super,density.
rewrite H.

unfold GHZ.
super_reduce.
Qed.

Lemma Dss4 :  forall (v : Vector 2),
super ((I_2 ⊗ I_2 ⊗ I_2 ⊗ σX) × (M1 ⊗ M0 ⊗ M0 ⊗ I_2) × (I_2 ⊗ H ⊗ H ⊗ I_2) × (XC ⊗ I_2 ⊗ I_2)) (density (v ⊗ GHZ)) ≈ density (/ √ 2 * / 2  .* ∣1⟩ ⊗ ∣0⟩  ⊗ ∣0⟩ ⊗ v).
Proof.
intros.
by_def1.

rewrite Dss4';reflexivity.
Qed.


Lemma Dss5' :  forall (v : Vector 2),
super ((I_2 ⊗ I_2 ⊗ I_2 ⊗ σX) × (I_2 ⊗ I_2 ⊗ I_2 ⊗ σZ) × (M1 ⊗ M0 ⊗ M1 ⊗ I_2) × (I_2 ⊗ H ⊗ H ⊗ I_2) × (XC ⊗ I_2 ⊗ I_2)) (density (v ⊗ GHZ)) ≡ density (/ √ 2 * / 2  .* ∣1⟩ ⊗ ∣0⟩  ⊗ ∣1⟩ ⊗ v).
Proof.
intros.
pose proof vq1 v.
destruct H as [a [b H]].
unfold super,density.
rewrite H.

unfold GHZ.
super_reduce.
Qed.

Lemma Dss5 :  forall (v : Vector 2),
super ((I_2 ⊗ I_2 ⊗ I_2 ⊗ σX) × (I_2 ⊗ I_2 ⊗ I_2 ⊗ σZ) × (M1 ⊗ M0 ⊗ M1 ⊗ I_2) × (I_2 ⊗ H ⊗ H ⊗ I_2) × (XC ⊗ I_2 ⊗ I_2)) (density (v ⊗ GHZ)) ≈ density (/ √ 2 * / 2  .* ∣1⟩ ⊗ ∣0⟩  ⊗ ∣1⟩ ⊗ v).
Proof.
intros.
by_def1.

rewrite Dss5';reflexivity.
Qed.


Lemma Dss6' :  forall (v : Vector 2),
super ((I_2 ⊗ I_2 ⊗ I_2 ⊗ σX) × (I_2 ⊗ I_2 ⊗ I_2 ⊗ σZ) × (M1 ⊗ M1 ⊗ M0 ⊗ I_2) × (I_2 ⊗ H ⊗ H ⊗ I_2) × (XC ⊗ I_2 ⊗ I_2)) (density (v ⊗ GHZ)) ≡ density (/ √ 2 * / 2  .* ∣1⟩ ⊗ ∣1⟩  ⊗ ∣0⟩ ⊗ v).
Proof.
intros.
pose proof vq1 v.
destruct H as [a [b H]].
unfold super,density.
rewrite H.

unfold GHZ.
super_reduce.
Qed.

Lemma Dss6 :  forall (v : Vector 2),
super ((I_2 ⊗ I_2 ⊗ I_2 ⊗ σX) × (I_2 ⊗ I_2 ⊗ I_2 ⊗ σZ) × (M1 ⊗ M1 ⊗ M0 ⊗ I_2) × (I_2 ⊗ H ⊗ H ⊗ I_2) × (XC ⊗ I_2 ⊗ I_2)) (density (v ⊗ GHZ)) ≈ density (/ √ 2 * / 2  .* ∣1⟩ ⊗ ∣1⟩  ⊗ ∣0⟩ ⊗ v).
Proof.
intros.
by_def1.

rewrite Dss6';reflexivity.
Qed.


Lemma Dss7' :  forall (v : Vector 2),
super ((I_2 ⊗ I_2 ⊗ I_2 ⊗ σX) × (I_2 ⊗ I_2 ⊗ I_2 ⊗ σZ) × (I_2 ⊗ I_2 ⊗ I_2 ⊗ σZ) × (M1 ⊗ M1 ⊗ M1 ⊗ I_2) × (I_2 ⊗ H ⊗ H ⊗ I_2) × (XC ⊗ I_2 ⊗ I_2)) (density (v ⊗ GHZ)) ≡ density (/ √ 2 * / 2  .* ∣1⟩ ⊗ ∣1⟩  ⊗ ∣1⟩ ⊗ v).
Proof.
intros.
pose proof vq1 v.
destruct H as [a [b H]].
unfold super,density.
rewrite H.

unfold GHZ.
super_reduce.
Qed.

Lemma Dss7 :  forall (v : Vector 2),
super ((I_2 ⊗ I_2 ⊗ I_2 ⊗ σX) × (I_2 ⊗ I_2 ⊗ I_2 ⊗ σZ) × (I_2 ⊗ I_2 ⊗ I_2 ⊗ σZ) × (M1 ⊗ M1 ⊗ M1 ⊗ I_2) × (I_2 ⊗ H ⊗ H ⊗ I_2) × (XC ⊗ I_2 ⊗ I_2)) (density (v ⊗ GHZ)) ≈ density (/ √ 2 * / 2  .* ∣1⟩ ⊗ ∣1⟩  ⊗ ∣1⟩ ⊗ v).
Proof.
intros.
by_def1.

rewrite Dss7';reflexivity.
Qed.

