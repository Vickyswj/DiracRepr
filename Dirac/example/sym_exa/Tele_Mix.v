Require Export Dirac.

Definition bell00 := /√2 .* (∣0,0⟩) .+ /√2 .* (∣1,1⟩).
Definition bell01 := /√2 .* (∣0,1⟩) .+ /√2 .* (∣1,0⟩).
Definition bell10 := /√2 .* (∣0,0⟩) .+ (-/√2) .* (∣1,1⟩).
Definition bell11 := /√2 .* (∣0,1⟩) .+ (-/√2) .* (∣1,0⟩).


Variables (α β : C).
Hypothesis Normalise: Cmod α ^ 2 + Cmod β ^ 2 = 1.
(* Cmod a ^2 + Cmod b ^2 = 1. *)

Definition φ (α β : C) : Vector 2 := α .* ∣0⟩ .+ β .* ∣1⟩.
Definition φ' : Vector 2 := α .* ∣0⟩ .+ β .* ∣1⟩.

Definition φ0 := φ' ⊗ bell00.


Definition φ2 := (H ⊗ I_2 ⊗ I_2) × (CX ⊗ I_2) × φ0.

Lemma Dtele1 :  φ2 ≡ α .*  ∣+⟩ ⊗ bell00   .+  β .*  ∣-⟩ ⊗ bell01.
Proof.
intros.
unfold φ2,φ0,φ',bell00,bell01.
operate_reduce.
Qed.

Definition ρ2 := density ( α .*  ∣+⟩ ⊗ bell00   .+  β .*  ∣-⟩ ⊗ bell01).


Lemma Dtele21:
MeaDen 2 0 (* (density (α .*  ∣0⟩ ⊗ bell00   .+  β .*  ∣1⟩ ⊗ bell01))  *) ρ2.=

[(fst (trace((Mea0 2 0) × ρ2)),
Cinv (trace ((Mea0 2 0)× ρ2)) .* super (Mea0 2 0) ρ2) ;

(fst (trace((Mea1 2 0) × ρ2)),
Cinv (trace ((Mea1 2 0)× ρ2)) .* super (Mea1 2 0) ρ2)].
Proof.
intros. unfold MeaDen.
repeat (constructor; try reflexivity).
Qed.

Definition p21 := fst (trace((Mea0 2 0) × ρ2)).
Definition p22 := fst (trace((Mea1 2 0) × ρ2)).


Lemma k1 : trace((Mea0 2 0) × ρ2) = 1/2.
Proof.
unfold Mea0,ρ2,density,bell00,bell01,B0.
  autounfold with S_db;
  autounfold with U_db.
  simpl.
  autorewrite with C_db.
  group_radicals.
  repeat rewrite Cmult_assoc.
  repeat rewrite <- Cmult_assoc.
  repeat rewrite <- Cmult_plus_distr_l.
  repeat rewrite (Cmult_comm α (α ^*)).
  repeat rewrite (Cmult_comm β (β ^*)).
  repeat rewrite <- Cmod_sqr.
  rewrite <- Cplus_assoc.
  rewrite (Cplus_comm (Cmod β ^ 2) (Cmod α ^ 2)).
  rewrite Normalise. lca.
Qed.


Lemma k2 : trace((Mea1 2 0) × ρ2) = 1/2.
Proof.
unfold Mea1,ρ2,density,bell00,bell01,B3.
  autounfold with S_db;
  autounfold with U_db.
  simpl.
  autorewrite with C_db.
  group_radicals.
  repeat rewrite Cmult_assoc.
  repeat rewrite <- Cmult_assoc.
  repeat rewrite <- Cmult_plus_distr_l.
  repeat rewrite (Cmult_comm α (α ^*)).
  repeat rewrite (Cmult_comm β (β ^*)).
  repeat rewrite <- Cmod_sqr.
  rewrite <- Cplus_assoc.
  rewrite (Cplus_comm (Cmod β ^ 2) (Cmod α ^ 2)).
  rewrite Normalise. lca.
Qed.

Definition ρ21 := Cinv (trace ((Mea0 2 0)× ρ2)) .* super (Mea0 2 0) ρ2.
Definition ρ22 := Cinv (trace ((Mea1 2 0)× ρ2)) .* super (Mea1 2 0) ρ2.



Lemma k3 : super (Mea0 2 0) ρ2 ≡ density (/ √ 2 .* ∣0⟩ ⊗ (α .* bell00 .+ β .* bell01)).
Proof.
unfold Mea0,ρ2,bell00,bell01. (* no simpl  or Opaque N.mul.+simpl*)
assert (I (2 ^ 0) ⊗ B0 ⊗ I (2 ^ (2 - 0))  ≡ B0 ⊗ I_2 ⊗ I_2).
{ simpl. rewrite (kron_1_l _ _ B0).
   replace (N.pos (2 ^ 2)) with 4 %N by auto.
   rewrite <- I4_eq.
   replace 4%N with ((2 * 2)%N) by auto.
   rewrite <- kron_assoc. reflexivity. }
unfold super. rewrite H.
super_reduce.
Qed.

Lemma k4 : super (Mea1 2 0) ρ2 ≡ density (/ √ 2 .* ∣1⟩ ⊗ (α .* bell00 .+ - β .* bell01)).
Proof.
unfold Mea1,ρ2,bell00,bell01. (* no simpl  or Opaque N.mul.+simpl*)
assert (I (2 ^ 0) ⊗ B3 ⊗ I (2 ^ (2 - 0))  ≡ B3 ⊗ I_2 ⊗ I_2).
{ simpl. rewrite (kron_1_l _ _ B3).
   replace (N.pos (2 ^ 2)) with 4 %N by auto.
   rewrite <- I4_eq.
   replace 4%N with ((2 * 2)%N) by auto.
   rewrite <- kron_assoc. reflexivity. }
unfold super. rewrite H.
super_reduce.
Qed.

Lemma Dtele22' :
MeaMix 2 1 [(p21,ρ21); (p22,ρ22)]
.=
[((p21 * fst (trace((Mea0 2 1) × ρ21)))%R,
Cinv (trace ((Mea0 2 1)× ρ21)) .* super (Mea0 2 1) ρ21);

((p21 * fst (trace((Mea1 2 1) × ρ21)))%R,
Cinv (trace ((Mea1 2 1)× ρ21)) .* super (Mea1 2 1) ρ21);

((p22 * fst (trace((Mea0 2 1) × ρ22)))%R,
Cinv (trace ((Mea0 2 1)× ρ22)) .* super (Mea0 2 1) ρ22);

((p22 * fst (trace((Mea1 2 1) × ρ22)))%R,
Cinv (trace ((Mea1 2 1)× ρ22)) .* super (Mea1 2 1) ρ22)].
Proof.
intros. unfold MeaMix'.
repeat (constructor; try reflexivity).
Qed.

Definition p31 := (p21 * fst (trace((Mea0 2 1) × ρ21))).     (* 1/4 *)
Definition p32 := (p21 * fst (trace((Mea1 2 1) × ρ21))).
Definition p33 := (p22 * fst (trace((Mea0 2 1) × ρ22))).
Definition p34 := (p22 * fst (trace((Mea1 2 1) × ρ22))).

Definition p31' := (p21 * fst (trace((Mea0 2 1) × ρ21)))%R.


Lemma k5 : trace((Mea0 2 1) × ρ21) = / 2.
Proof.
unfold ρ21.
rewrite k1,k3.
unfold Mea0,B0,density,bell00,bell01.
  autounfold with S_db;
  autounfold with U_db.
  simpl.
  autorewrite with C_db.
  group_radicals.
  repeat rewrite (Cmult_comm _ (/ / C2)).
  repeat rewrite Cmult_assoc.
  repeat rewrite <- Cmult_assoc.
  repeat rewrite <- Cmult_plus_distr_l.
  repeat rewrite (Cmult_comm α (α ^*)).
  repeat rewrite (Cmult_comm β (β ^*)).
  repeat rewrite <- Cmod_sqr.
  rewrite Normalise.
   apply injective_projections; simpl; field.
Qed.


Lemma k5' : p31 = 1/4.
Proof.
unfold p31,p21.
(* rewrite k1,k5.  lca. *)
rewrite k1.
replace((trace (Mea0 2 1 × ρ21))) with (/2).
apply injective_projections; simpl; field.
  unfold ρ21.
  rewrite k1,k3.
  unfold Mea0,B0,density,bell00,bell01.
  autounfold with S_db;
  autounfold with U_db.
  simpl.
  autorewrite with C_db.
  group_radicals.
  repeat rewrite (Cmult_comm _ (/ / C2)).
  repeat rewrite Cmult_assoc.
  repeat rewrite <- Cmult_assoc.
  repeat rewrite <- Cmult_plus_distr_l.
  repeat rewrite (Cmult_comm α (α ^*)).
  repeat rewrite (Cmult_comm β (β ^*)).
  repeat rewrite <- Cmod_sqr.
  rewrite Normalise.
   apply injective_projections; simpl; field.
Qed.


Lemma k6 : trace((Mea1 2 1) × ρ21) = / 2.
Proof.
unfold ρ21.
rewrite k1,k3.
unfold Mea1,B3,density,bell00,bell01.
  autounfold with S_db;
  autounfold with U_db.
  simpl.
  autorewrite with C_db.
  group_radicals.
  repeat rewrite (Cmult_comm _ (/ / C2)).
  repeat rewrite Cmult_assoc.
  repeat rewrite <- Cmult_assoc.
  repeat rewrite <- Cmult_plus_distr_l.
  repeat rewrite (Cmult_comm α (α ^*)).
  repeat rewrite (Cmult_comm β (β ^*)).
  repeat rewrite <- Cmod_sqr.
  rewrite Cplus_comm in Normalise.
  rewrite Normalise.
   apply injective_projections; simpl; field.
Qed.


Lemma k6' : p32 = 1/4.
Proof.
unfold p32,p21.
(* rewrite k1,k5.  lca. *)
rewrite k1.
replace((trace (Mea1 2 1 × ρ21))) with (/2).
apply injective_projections; simpl; field.
  unfold ρ21.
  rewrite k1,k3.
  unfold Mea1,B3,density,bell00,bell01.
  autounfold with S_db;
  autounfold with U_db.
  simpl.
  autorewrite with C_db.
  group_radicals.
  repeat rewrite (Cmult_comm _ (/ / C2)).
  repeat rewrite Cmult_assoc.
  repeat rewrite <- Cmult_assoc.
  repeat rewrite <- Cmult_plus_distr_l.
  repeat rewrite (Cmult_comm α (α ^*)).
  repeat rewrite (Cmult_comm β (β ^*)).
  repeat rewrite <- Cmod_sqr.
  rewrite Cplus_comm in Normalise.
  rewrite Normalise.
   apply injective_projections; simpl; field.
Qed.

Lemma k7 : trace((Mea0 2 1) × ρ22) = / 2.
Proof.
unfold ρ22.
rewrite k2,k4.
unfold Mea0,B0,density,bell00,bell01.
  autounfold with S_db;
  autounfold with U_db.
  simpl.
  autorewrite with C_db.
  group_radicals.
  repeat rewrite (Cmult_comm _ (/ / C2)).
  repeat rewrite Cmult_assoc.
  repeat rewrite <- Cmult_assoc.
  repeat rewrite <- Cmult_plus_distr_l.
  repeat rewrite (Cmult_comm α (α ^*)).
  repeat rewrite (Cmult_comm β (β ^*)).
  repeat rewrite <- Cmod_sqr.
  rewrite Normalise.
   apply injective_projections; simpl; field.
Qed.


Lemma k7' : p33 = 1/4.
Proof.
unfold p33,p22.
(* rewrite k1,k5.  lca. *)
rewrite k2.
replace((trace (Mea0 2 1 × ρ22))) with (/2).
apply injective_projections; simpl; field.
  unfold ρ22.
  rewrite k2,k4.
  unfold Mea0,B0,density,bell00,bell01.
  autounfold with S_db;
  autounfold with U_db.
  simpl.
  autorewrite with C_db.
  group_radicals.
  repeat rewrite (Cmult_comm _ (/ / C2)).
  repeat rewrite Cmult_assoc.
  repeat rewrite <- Cmult_assoc.
  repeat rewrite <- Cmult_plus_distr_l.
  repeat rewrite (Cmult_comm α (α ^*)).
  repeat rewrite (Cmult_comm β (β ^*)).
  repeat rewrite <- Cmod_sqr.
  rewrite Normalise.
   apply injective_projections; simpl; field.
Qed.

Lemma k8 : trace((Mea1 2 1) × ρ22) = / 2.
Proof.
unfold ρ22.
rewrite k2,k4.
unfold Mea1,B3,density,bell00,bell01.
  autounfold with S_db;
  autounfold with U_db.
  simpl.
  autorewrite with C_db.
  group_radicals.
  repeat rewrite (Cmult_comm _ (/ / C2)).
  repeat rewrite Cmult_assoc.
  repeat rewrite <- Cmult_assoc.
  repeat rewrite <- Cmult_plus_distr_l.
  repeat rewrite (Cmult_comm α (α ^*)).
  repeat rewrite (Cmult_comm β (β ^*)).
  repeat rewrite <- Cmod_sqr.
  rewrite Cplus_comm in Normalise.
  rewrite Normalise.
   apply injective_projections; simpl; field.
Qed.


Lemma k8' : p34 = 1/4.
Proof.
unfold p34,p22.
(* rewrite k1,k5.  lca. *)
rewrite k2.
replace((trace (Mea1 2 1 × ρ22))) with (/2).
apply injective_projections; simpl; field.
  unfold ρ22.
  rewrite k2,k4.
  unfold Mea1,B3,density,bell00,bell01.
  autounfold with S_db;
  autounfold with U_db.
  simpl.
  autorewrite with C_db.
  group_radicals.
  repeat rewrite (Cmult_comm _ (/ / C2)).
  repeat rewrite Cmult_assoc.
  repeat rewrite <- Cmult_assoc.
  repeat rewrite <- Cmult_plus_distr_l.
  repeat rewrite (Cmult_comm α (α ^*)).
  repeat rewrite (Cmult_comm β (β ^*)).
  repeat rewrite <- Cmod_sqr.
  rewrite Cplus_comm in Normalise.
  rewrite Normalise.
   apply injective_projections; simpl; field.
Qed.


Definition ρ31 := Cinv (trace ((Mea0 2 1)× ρ21)) .* super (Mea0 2 1) ρ21.
Definition ρ32 := Cinv (trace ((Mea1 2 1)× ρ21)) .* super (Mea1 2 1) ρ21.
Definition ρ33 := Cinv (trace ((Mea0 2 1)× ρ22)) .* super (Mea0 2 1) ρ22.
Definition ρ34 := Cinv (trace ((Mea1 2 1)× ρ22)) .* super (Mea1 2 1) ρ22.


Lemma k9 : super (Mea0 2 1) ρ21 ≡ density (/√2 .* (∣0⟩ ⊗ ∣0⟩ ⊗ (α .* ∣0⟩ .+ β .* ∣1⟩))).
Proof.
unfold Mea0,ρ21.
rewrite k1. unfold super at 1.
rewrite k3. unfold bell00,bell01.
replace (I (2 ^ 1) ⊗ B0 ⊗ I (2 ^ (2 - 1))) with (I_2 ⊗ B0 ⊗ I_2 )
by (rewrite I2_eq; auto).
isolate_scale.
replace (density (/√2 .* (∣0⟩ ⊗ ∣0⟩ ⊗ (α .* ∣0⟩ .+ β .* ∣1⟩))))
with (/ (C1 / C2) .* density (/2  .* (∣0⟩ ⊗ ∣0⟩ ⊗ (α .* ∣0⟩ .+ β .* ∣1⟩)))).
2 :{ unfold density.
  repeat rewrite Mscale_adj.
  isolate_scale.
  replace (/ (C1 / C2) * / C2 * (/ C2) ^*) with (/ √ 2 * (/ √ 2) ^*)
    by (group_radicals; apply injective_projections; simpl ; field).
  auto. }
match goal with
  | |-context [/ (C1 / C2) .* ?M ≡ / (C1 / C2) .* ?N ] =>  assert (M ≡ N) as H
end.
replace ((2 ^ 1 * 2 * 2 ^ (2 - 1))%N)
with ((2 ^ 0 * 2 * 2 ^ (2 - 0))%N) by (simpl;lia).
super_reduce.
rewrite H. reflexivity.
Qed.


Lemma k10 : super (Mea1 2 1) ρ21 ≡ density (/√2 .* (∣0⟩ ⊗ ∣1⟩ ⊗ (α .* ∣1⟩ .+ β .* ∣0⟩))).
Proof.
unfold Mea1,ρ21.
rewrite k1. unfold super at 1.
rewrite k3. unfold bell00,bell01.
replace (I (2 ^ 1) ⊗ B3 ⊗ I (2 ^ (2 - 1))) with (I_2 ⊗ B3 ⊗ I_2 )
by (rewrite I2_eq; auto).
isolate_scale.
replace (density (/√2 .* (∣0⟩ ⊗ ∣1⟩ ⊗ (α .* ∣1⟩ .+ β .* ∣0⟩))))
with (/ (C1 / C2) .* density (/2  .* (∣0⟩ ⊗ ∣1⟩ ⊗ (α .* ∣1⟩ .+ β .* ∣0⟩)))).
2 :{ unfold density.
  repeat rewrite Mscale_adj.
  isolate_scale.
  replace (/ (C1 / C2) * / C2 * (/ C2) ^*) with (/ √ 2 * (/ √ 2) ^*)
    by (group_radicals; apply injective_projections; simpl ; field).
  auto. }
match goal with
  | |-context [/ (C1 / C2) .* ?M ≡ / (C1 / C2) .* ?N ] =>  assert (M ≡ N) as H
end.
replace ((2 ^ 1 * 2 * 2 ^ (2 - 1))%N)
with ((2 ^ 0 * 2 * 2 ^ (2 - 0))%N) by (simpl;lia).
super_reduce.
rewrite H. reflexivity.
Qed.

Lemma k11 : super (Mea0 2 1) ρ22 ≡ density (/√2 .* (∣1⟩ ⊗ ∣0⟩ ⊗ (α .* ∣0⟩ .+ - β .* ∣1⟩))).
Proof.
unfold Mea0,ρ22.
rewrite k2. unfold super at 1.
rewrite k4. unfold bell00,bell01.
replace (I (2 ^ 1) ⊗ B0 ⊗ I (2 ^ (2 - 1))) with (I_2 ⊗ B0 ⊗ I_2 )
by (rewrite I2_eq; auto).
isolate_scale.
replace (density (/√2 .* (∣1⟩ ⊗ ∣0⟩ ⊗ (α .* ∣0⟩ .+ - β .* ∣1⟩))))
with (/ (C1 / C2) .* density (/2  .* (∣1⟩ ⊗ ∣0⟩ ⊗ (α .* ∣0⟩ .+ - β .* ∣1⟩)))).
2 :{ unfold density.
  repeat rewrite Mscale_adj.
  isolate_scale.
  replace (/ (C1 / C2) * / C2 * (/ C2) ^*) with (/ √ 2 * (/ √ 2) ^*)
    by (group_radicals; apply injective_projections; simpl ; field).
  auto. }
match goal with
  | |-context [/ (C1 / C2) .* ?M ≡ / (C1 / C2) .* ?N ] =>  assert (M ≡ N) as H
end.
replace ((2 ^ 1 * 2 * 2 ^ (2 - 1))%N)
with ((2 ^ 0 * 2 * 2 ^ (2 - 0))%N) by (simpl;lia).
super_reduce.
rewrite H. reflexivity.
Qed.

Lemma k12 : super (Mea1 2 1) ρ22 ≡ density (/√2 .* (∣1⟩ ⊗ ∣1⟩ ⊗ (α .* ∣1⟩ .+ - β .* ∣0⟩))).
Proof.
unfold Mea1,ρ22.
rewrite k2. unfold super at 1.
rewrite k4. unfold bell00,bell01.
replace (I (2 ^ 1) ⊗ B3 ⊗ I (2 ^ (2 - 1))) with (I_2 ⊗ B3 ⊗ I_2 )
by (rewrite I2_eq; auto).
isolate_scale.
replace (density (/√2 .* (∣1⟩ ⊗ ∣1⟩ ⊗ (α .* ∣1⟩ .+ - β .* ∣0⟩))))
with (/ (C1 / C2) .* density (/2  .* (∣1⟩ ⊗ ∣1⟩ ⊗ (α .* ∣1⟩ .+ - β .* ∣0⟩)))).
2 :{ unfold density.
  repeat rewrite Mscale_adj.
  isolate_scale.
  replace (/ (C1 / C2) * / C2 * (/ C2) ^*) with (/ √ 2 * (/ √ 2) ^*)
    by (group_radicals; apply injective_projections; simpl ; field).
  auto. }
match goal with
  | |-context [/ (C1 / C2) .* ?M ≡ / (C1 / C2) .* ?N ] =>  assert (M ≡ N) as H
end.
replace ((2 ^ 1 * 2 * 2 ^ (2 - 1))%N)
with ((2 ^ 0 * 2 * 2 ^ (2 - 0))%N) by (simpl;lia).
super_reduce.
rewrite H. reflexivity.
Qed.


Lemma Dtele3 :
[(fst p31, ρ31); (fst p32, super (I_2 ⊗ I_2 ⊗ σX) ρ32); (fst p33, super (I_2 ⊗ I_2 ⊗ σZ) ρ33); (fst p34, super ((I_2 ⊗ I_2 ⊗ σZ) × (I_2 ⊗ I_2 ⊗ σX)) ρ34)]
.=
[((/4)%R, density (∣0⟩ ⊗ ∣0⟩ ⊗ φ')); ((/4)%R, density ((∣0⟩ ⊗ ∣1⟩ ⊗ φ'))); ((/4)%R, density ((∣1⟩ ⊗ ∣0⟩ ⊗ φ'))); ((/4)%R, density ((∣1⟩ ⊗ ∣1⟩ ⊗ φ')))].
Proof.
intros.
repeat (constructor; try reflexivity).
rewrite k5'. simpl. lra.
  unfold ρ31,φ'. rewrite k5. rewrite k9.
  unfold density.
  repeat rewrite Mscale_adj.
  isolate_scale. group_radicals.
  replace (/ C2 * / / C2 ) with C1
    by (apply injective_projections; simpl ; field).
  rewrite Mscale_1_l. reflexivity.
rewrite k6'. simpl. lra.
  unfold ρ32,φ'. rewrite k6. 
  unfold super at 1.  rewrite k10.
  isolate_scale.
  replace (density (∣0⟩ ⊗ ∣1⟩ ⊗ (α .* ∣0⟩ .+ β .* ∣1⟩)))
  with (/ / C2 .* density (/ √ 2 .* (∣0⟩ ⊗ ∣1⟩ ⊗ (α .* ∣0⟩ .+ β .* ∣1⟩)))).
  2 : { unfold density. repeat rewrite Mscale_adj.
           isolate_scale. group_radicals. 
             replace (/ C2 * / / C2 ) with C1
             by (apply injective_projections; simpl ; field).
           rewrite Mscale_1_l. reflexivity. }
  match goal with
    | |-context [/ / C2 .* ?M ≡ / / C2 .* ?N ] =>  assert (M ≡ N) as H
  end.
  replace ((2 ^ 1) * 2 * 2 ^ (2 - 1))%N with (2 * 2 * 2)%N by (simpl; lia).
  super_reduce. rewrite H. reflexivity.
rewrite k7'. simpl. lra.
  unfold ρ33,φ'. rewrite k7. 
  unfold super at 1.  rewrite k11.
  isolate_scale.
  replace (density (∣1⟩ ⊗ ∣0⟩ ⊗ (α .* ∣0⟩ .+ β .* ∣1⟩)))
  with (/ / C2 .* density (/ √ 2 .* (∣1⟩ ⊗ ∣0⟩ ⊗ (α .* ∣0⟩ .+ β .* ∣1⟩)))).
  2 : { unfold density. repeat rewrite Mscale_adj.
           isolate_scale. group_radicals. 
             replace (/ C2 * / / C2 ) with C1
             by (apply injective_projections; simpl ; field).
           rewrite Mscale_1_l. reflexivity. }
  match goal with
    | |-context [/ / C2 .* ?M ≡ / / C2 .* ?N ] =>  assert (M ≡ N) as H
  end.
  replace ((2 ^ 1) * 2 * 2 ^ (2 - 1))%N with (2 * 2 * 2)%N by (simpl; lia).
  super_reduce. rewrite H. reflexivity.
rewrite k8'. simpl. lra.
  unfold ρ34,φ'. rewrite k8. 
  unfold super at 1.  rewrite k12.
  isolate_scale.
  replace (density (∣1⟩ ⊗ ∣1⟩ ⊗ (α .* ∣0⟩ .+ β .* ∣1⟩)))
  with (/ / C2 .* density (/ √ 2 .* (∣1⟩ ⊗ ∣1⟩ ⊗ (α .* ∣0⟩ .+ β .* ∣1⟩)))).
  2 : { unfold density. repeat rewrite Mscale_adj.
           isolate_scale. group_radicals. 
             replace (/ C2 * / / C2 ) with C1
             by (apply injective_projections; simpl ; field).
           rewrite Mscale_1_l. reflexivity. }
  match goal with
    | |-context [/ / C2 .* ?M ≡ / / C2 .* ?N ] =>  assert (M ≡ N) as H
  end.
  replace ((2 ^ 1) * 2 * 2 ^ (2 - 1))%N with (2 * 2 * 2)%N by (simpl; lia).
  super_reduce. rewrite H. reflexivity.
Qed.