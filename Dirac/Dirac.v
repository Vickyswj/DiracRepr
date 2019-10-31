Require Export Quantum.

Definition ket0 := ∣0⟩.
Definition ket1 := ∣1⟩.
Definition bra0 := ⟨0∣.
Definition bra1 := ⟨0∣.

Definition ketp := /√2 .* ∣0⟩ .+ /√2 .* ∣1⟩.
Definition ketn := /√2 .* ∣0⟩ .+ (-/√2) .* ∣1⟩.

Notation "∣+⟩" := ketp.
Notation "∣-⟩" := ketn.
Notation "⟨+∣" := ketp†.
Notation "⟨-∣" := ketn†.

Definition bell00 := /√2 .* (∣0⟩ ⊗ ∣0⟩) .+ /√2 .* (∣1⟩ ⊗ ∣1⟩).
Definition bell01 := /√2 .* (∣0⟩ ⊗ ∣1⟩) .+ /√2 .* (∣1⟩ ⊗ ∣0⟩).
Definition bell10 := /√2 .* (∣0⟩ ⊗ ∣0⟩) .+ (-/√2) .* (∣1⟩ ⊗ ∣1⟩).
Definition bell11 := /√2 .* (∣0⟩ ⊗ ∣1⟩) .+ (-/√2) .* (∣1⟩ ⊗ ∣0⟩).

Module toy_automation.

Lemma Mmult_bra0_ket0 : ⟨0∣ × ∣0⟩ = 1 .* I 1.
Proof. solve_matrix. Qed.
Lemma Mmult_bra0_ket1 : ⟨0∣ × ∣1⟩ = 0 .* I 1. (* /Zero *)
Proof. solve_matrix. Qed.
Lemma Mmult_bra1_ket0 : ⟨1∣ × ∣0⟩ = 0 .* I 1.
Proof. solve_matrix. Qed.
Lemma Mmult_bra1_ket1 : ⟨1∣ × ∣1⟩ = 1 .* I 1.
Proof. solve_matrix. Qed.

Lemma Mmult_1_l : forall (m n : nat) (A : Matrix m n), I m × A = A.
Admitted.

Lemma Mmult_1_r : forall (m n : nat) (A : Matrix m n),  A × I n = A.
Admitted.

Ltac distrubute_plus:=
repeat rewrite ?Mmult_plus_distr_r, ?Mmult_plus_distr_l,?Mscale_plus_distr_r,?kron_plus_distr_r,?kron_plus_distr_l.

Ltac isolate_scale:=
repeat rewrite ?Mscale_mult_dist_l,?Mscale_mult_dist_r,?Mscale_kron_dist_r,?Mscale_kron_dist_l,?Mscale_assoc.

Ltac reduce_scale:=
Csimpl;
repeat rewrite ?Mscale_0_l,?Mplus_0_l,?Mplus_0_r,?Cinv_sqrt2_sqrt;
auto.

Ltac assoc_right:=
repeat rewrite ?Mmult_assoc, ?kron_assoc.

Ltac kron_mult:=
repeat rewrite <- kron_mixed_product.

Ltac mult_kron:=
repeat rewrite kron_mixed_product.

Inductive fake_eq {n m}: Matrix n m -> Matrix n m -> Prop :=
| fake_eq_intro: forall A B, A = B -> fake_eq A B.

Lemma mult_reduce1 : forall n A B x, fake_eq (@Mmult 1 n 1 A B) x -> @Mmult 1 n 1 A B = x.
Proof.
  intros.
  inversion H; subst; auto.
Qed.

Lemma mult_reduce2 : forall n m A B C x, fake_eq (@Mmult 1 n 1 A B) x -> @Mmult 1 n m A (@Mmult n 1 m B C) = @Mmult 1 1 m x C.
Proof.
  intros.
  inversion H; subst; auto.
  rewrite Mmult_assoc.
  auto.
Qed.


(* Hint Extern 1 (fake_eq (@Mmult _ _ _ _ _) _) => apply fake_eq_intro; apply Mmult_bra0_ket0: matrix_reduce.
Hint Extern 1 (fake_eq (@Mmult _ _ _ _ _) _) => apply fake_eq_intro; apply Mmult_bra0_ket1: matrix_reduce.
Hint Extern 1 (fake_eq (@Mmult _ _ _ _ _) _) => apply fake_eq_intro; apply Mmult_bra1_ket0: matrix_reduce.
Hint Extern 1 (fake_eq (@Mmult _ _ _ _ _) _) => apply fake_eq_intro; apply Mmult_bra1_ket1: matrix_reduce.


Ltac matrix_mult_reduce:=
match goal with
| |-context [ @Mmult 1 ?n 1 ?A ?B] =>
         match B with
        | @Mmult _ _ _ _ _ => fail 1
        | _ => erewrite (mult_reduce1 n A B); [| auto with matrix_reduce]
        end
| |-context [ @Mmult 1 ?n ?m ?A (@Mmult ?n 1 ?m ?B ?C)] => erewrite (mult_reduce2 n m A B C); [| auto with matrix_reduce]
end;
isolate_scale;
repeat rewrite ?Mmult_1_l, ?Mmult_1_r. *)


Lemma Mmult_bra000_ket000 : (⟨0∣ ⊗ ⟨0∣ ⊗ ⟨0∣ × (∣0⟩ ⊗ ∣0⟩ ⊗ ∣0⟩)) = 1 .* I 1.
Proof.
mult_kron.
rewrite Mmult_bra0_ket0.
isolate_scale;
repeat rewrite ?Mmult_1_l, ?Mmult_1_r.
repeat rewrite id_kron.
reduce_scale.
Qed.


Ltac mult_kron1 :=
  match goal with
  | |- context [@Mmult ?m1o1 ?n1p1 ?n2p2 (@kron ?m1 ?n1 ?o1 ?p1 ?A ?B) (@kron ?m2 ?n2 ?o2 ?p2 ?C ?D)] =>
             change (@Mmult m1o1 n1p1 n2p2 (@kron m1 n1 o1 p1 A B) (@kron m2 n2 o2 p2 C D)) with
                           (@Mmult (m1 * o1) (n1 * p1) (n2 * p2) (@kron m1 n1 o1 p1 A B) (@kron n1 n2 p1 p2 C D));
             rewrite (@kron_mixed_product m1 n1 n2 o1 p1 p2 A B C D)
  end.

Ltac mult_result_gen :=
  repeat mult_kron1;
  repeat rewrite ?Mmult_bra0_ket0, ?Mmult_bra0_ket1, ?Mmult_bra1_ket0, ?Mmult_bra1_ket1,
                            ?Mmult_bra000_ket000;  (* make it more extensible later.*)
  isolate_scale;
  repeat rewrite id_kron;
  apply fake_eq_intro; reflexivity.

Ltac matrix_mult_reduce :=
match goal with
| |-context [ @Mmult ?one1 ?n ?one2 ?A ?B] =>
         match B with
        | @Mmult _ _ _ _ _ => fail 1
        | _ => change (@Mmult one1 n one2 A B) with
                                (@Mmult 1 n 1 A B);
                   erewrite (mult_reduce1 n A B) by (mult_result_gen; fail 2 "mult_result_gen fail")
        end
| |-context [ @Mmult ?one1 ?n ?m ?A (@Mmult ?n ?one2 ?m ?B ?C)] =>
         change (@Mmult one1 n m A (@Mmult n one2 m B C)) with
                       (@Mmult 1 n m A (@Mmult n 1 m B C));
          erewrite (mult_reduce2 n m A B C) by (mult_result_gen; fail 2 "mult_result_gen fail")
end;
isolate_scale;
repeat rewrite ?Mmult_1_l, ?Mmult_1_r.

Ltac matrix_reduce :=
distrubute_plus;
isolate_scale;
kron_mult;
assoc_right;
repeat matrix_mult_reduce;
reduce_scale.


(* 
Lemma Mmult_bra000_ket000 : (⟨0∣ ⊗ ⟨0∣ ⊗ ⟨0∣ × (∣0⟩ ⊗ ∣0⟩ ⊗ ∣0⟩)) = 1 .* I 1.
Proof.
mult_kron.
repeat matrix_mult_reduce.
repeat rewrite id_kron.
reduce_scale.
Qed.
 *)


Definition H := /√2 .* ((∣0⟩ .+ ∣1⟩) × ⟨0∣ .+ (∣0⟩ .+  (-1) .* ∣1⟩) × ⟨1∣).
Definition H' := /√2 .* (∣0⟩ × ⟨0∣) .+ /√2 .* (∣0⟩ × ⟨1∣)  .+ /√2 .* (∣1⟩ × ⟨0∣) .+ (-/√2) .* (∣1⟩ × ⟨1∣).

Definition I_2 := ∣0⟩ × ⟨0∣ .+ ∣1⟩ × ⟨1∣.

Definition CNOT := (∣0⟩ ⊗ ∣0⟩) × (⟨0∣ ⊗ ⟨0∣) .+ (∣0⟩ ⊗ ∣1⟩) × (⟨0∣ ⊗ ⟨1∣)
                              .+ (∣1⟩ ⊗ ∣0⟩) × (⟨1∣ ⊗ ⟨1∣) .+ (∣1⟩ ⊗ ∣1⟩) × (⟨1∣ ⊗ ⟨0∣).

Definition state0 := ∣0⟩ ⊗ ∣0⟩.
Definition state1 := (H ⊗ I_2) × state0.
Definition state2 := CNOT × state1.

Lemma H_ket0 : H × ∣0⟩ = (/√2 .* ∣0⟩ .+ /√2 .* ∣1⟩).
Proof.
unfold H.
matrix_reduce.
Qed.


Lemma pre_bell00 : bell00 = state2.
Proof.
unfold bell00,state2,state1,state0,H,I_2.

(* solve_matrix. *)
distrubute_plus.
isolate_scale.
kron_mult.
assoc_right.
repeat matrix_mult_reduce.
matrix_mult_reduce.
reduce_scale.
Qed.


Definition φ0 := ketp ⊗ bell00.
Definition φ1 := (CNOT ⊗ I_2) × φ0.
Definition φ2 := (H ⊗ I_2 ⊗ I_2) × φ1.

Lemma step1 : φ1 = /2 .*  (∣0⟩ ⊗ ∣0⟩ ⊗ ∣0⟩) .+ /2 .*  (∣0⟩ ⊗ ∣1⟩ ⊗ ∣1⟩) .+ /2 .*  (∣1⟩ ⊗ ∣0⟩ ⊗ ∣1⟩) .+ /2 .*  (∣1⟩ ⊗ ∣1⟩ ⊗ ∣0⟩).
Proof.
unfold φ1,CNOT,I_2,φ0,ketp,bell00.
distrubute_plus.
isolate_scale.
kron_mult.
assoc_right.
repeat matrix_mult_reduce.
reduce_scale.
(* assert ( H : / 2 .* (∣1⟩ ⊗ (∣0⟩ ⊗ ∣1⟩)) .+ / 2 .* (∣1⟩ ⊗ (∣1⟩ ⊗ ∣0⟩)) = / 2 .* (∣1⟩ ⊗ (∣1⟩ ⊗ ∣0⟩)) .+ / 2 .* (∣1⟩ ⊗ (∣0⟩ ⊗ ∣1⟩))).
{ apply Mplus_comm. }
rewrite Mplus_assoc.
rewrite -> H.
reflexivity.
Admitted. *)
Qed.

Lemma step1' : φ1 = /2 .*  (∣0⟩ ⊗ ∣0⟩ ⊗ ∣0⟩) .+ /2 .*  (∣0⟩ ⊗ ∣1⟩ ⊗ ∣1⟩) .+ /2 .*  (∣1⟩ ⊗ ∣1⟩ ⊗ ∣0⟩) .+ /2 .*  (∣1⟩ ⊗ ∣0⟩ ⊗ ∣1⟩).
Proof. Admitted.

(* Lemma step1 : φ1 = /2 .*  ∣0,0,0⟩ .+ /2 .*  ∣0,1,1⟩ .+ /2 .*  ∣1,0,1⟩ .+ /2 .*  ∣1,1,0⟩.
Proof.
unfold φ1,CNOT,I_2,φ0,ketp,bell00.
distrubute_plus.
isolate_scale.
kron_mult.
assoc_right.
repeat matrix_mult_reduce.
reduce_scale.
Qed. *)

(* Lemma ttte :/√2 * -1  = - /√2 .
Proof.
reflexivity.
Lemma ttte :/ 2 * (/ √ 2 * -1)  =/ 2 * - / √ 2 .
Proof.
Qed.
/ 2 * (/ √ 2 * -1) .* (∣1⟩ ⊗ (∣0⟩ ⊗ ∣1⟩)) =/ 2 * - / √ 2 .* (∣1⟩ ⊗ (∣0⟩ ⊗ ∣1⟩)) *)


(* Lemma step2' : φ2 = /2 .* ((∣0⟩ ⊗ ∣0⟩) ⊗  (/√2 .* ∣0⟩ .+ /√2 .* ∣1⟩)
                                           .+ (∣0⟩ ⊗ ∣1⟩) ⊗  (/√2 .* ∣1⟩ .+ /√2 .* ∣0⟩)
                                           .+ (∣1⟩ ⊗ ∣0⟩) ⊗  (/√2 .* ∣0⟩ .+ (-/√2)  .* ∣1⟩)
                                           .+ (∣0⟩ ⊗ ∣0⟩) ⊗  (/√2 .* ∣1⟩ .+ (-/√2)  .* ∣0⟩)). *)
(* Lemma step2'' : φ2 = /2 .* ((∣0⟩ ⊗ ∣0⟩) ⊗  (/√2 .* ∣0⟩ .+ /√2 .* ∣1⟩)
                                           .+ (∣0⟩ ⊗ ∣1⟩) ⊗  (/√2 .* ∣1⟩ .+ /√2 .* ∣0⟩)
                                           .+ (∣1⟩ ⊗ ∣0⟩) ⊗  (/√2 .* ∣0⟩ .+ (/√2 * -1) .* ∣1⟩)
                                           .+ (∣1⟩ ⊗ ∣1⟩) ⊗  (/√2 .* ∣1⟩ .+ (/√2 * -1) .* ∣0⟩)). *)
Lemma step2 : φ2 = / 2 * / √ 2 .* (∣0⟩ ⊗ (∣0⟩ ⊗ ∣0⟩)) .+ / 2 * / √ 2 .* (∣1⟩ ⊗ (∣0⟩ ⊗ ∣0⟩))
                               .+ (/ 2 * / √ 2 .* (∣0⟩ ⊗ (∣1⟩ ⊗ ∣1⟩)) .+ / 2 * / √ 2 .* (∣1⟩ ⊗ (∣1⟩ ⊗ ∣1⟩)))
                               .+ (/ 2 * / √ 2 .* (∣0⟩ ⊗ (∣0⟩ ⊗ ∣1⟩)) .+ / 2 * (/ √ 2 * -1) .* (∣1⟩ ⊗ (∣0⟩ ⊗ ∣1⟩)))
                               .+ (/ 2 * / √ 2 .* (∣0⟩ ⊗ (∣1⟩ ⊗ ∣0⟩)) .+ / 2 * (/ √ 2 * -1) .* (∣1⟩ ⊗ (∣1⟩ ⊗ ∣0⟩))).
Proof.
unfold φ2,H,I_2.
(* rewrite step1'. *)
rewrite step1.
(* solve_matrix. *)
distrubute_plus.
isolate_scale.
kron_mult.
assoc_right.
repeat matrix_mult_reduce.
reduce_scale.
Qed.

Definition M0 := ∣0⟩ × ⟨0∣.
Definition M1 := ∣1⟩ × ⟨1∣.
Definition φ30 := (M0 ⊗ M0 ⊗ I_2) × φ2.
Definition φ31 := (M0 ⊗ M1 ⊗ I_2) × φ2.
Definition φ32 := (M1 ⊗ M0 ⊗ I_2) × φ2.
Definition φ33 := (M1 ⊗ M1 ⊗ I_2) × φ2.

Lemma step30 : φ30 = / 2  .* (∣0⟩ ⊗ ∣0⟩) ⊗ (/√2 .* (∣0⟩ .+ ∣1⟩)).
Proof.
unfold φ30,M0,M1,I_2.
(* rewrite step1'. *)
rewrite step2.
(* solve_matrix. *)
distrubute_plus.
isolate_scale.
kron_mult.
assoc_right.
repeat matrix_mult_reduce.
reduce_scale.
rewrite Cmult_comm.
auto.
Qed.

Lemma step31 : φ31 = / 2  .* (∣0⟩ ⊗ ∣1⟩) ⊗ (/√2 .* (∣1⟩ .+ ∣0⟩)).
Proof.
unfold φ31,M0,M1,I_2.
(* rewrite step1'. *)
rewrite step2.
(* solve_matrix. *)
distrubute_plus.
isolate_scale.
kron_mult.
assoc_right.
repeat matrix_mult_reduce.
reduce_scale.
rewrite Cmult_comm.
auto.
Qed.

Lemma step32 : φ32 = / 2  .* (∣1⟩ ⊗ ∣0⟩) ⊗ (/√2 .* ∣0⟩ .+ (/ √ 2 * -1) .* ∣1⟩).
Proof.
unfold φ32,M0,M1,I_2.
(* rewrite step1'. *)
rewrite step2.
distrubute_plus.
isolate_scale.
kron_mult.
assoc_right.
repeat matrix_mult_reduce.
reduce_scale.
rewrite Mplus_comm.
rewrite Cmult_comm.
rewrite Mplus_comm.
rewrite Cmult_comm.
auto.
Qed.

Lemma step33 : φ33 = / 2  .* (∣1⟩ ⊗ ∣1⟩) ⊗ (/√2 .* ∣1⟩ .+(/ √ 2 * -1) .* ∣0⟩).
Proof.
unfold φ33,M0,M1,I_2.
(* rewrite step1'. *)
rewrite step2.
distrubute_plus.
isolate_scale.
kron_mult.
assoc_right.
repeat matrix_mult_reduce.
reduce_scale.
rewrite Mplus_comm.
rewrite Cmult_comm.
rewrite Mplus_comm.
rewrite Cmult_comm.
auto.
Qed.

Definition X := ∣0⟩ × ⟨1∣ .+ ∣1⟩ × ⟨0∣.
Definition X' :=  ∣1⟩ × ⟨0∣ .+ ∣0⟩ × ⟨1∣.
Definition Z := ∣0⟩ × ⟨0∣ .+ (-1) .* (∣1⟩ × ⟨1∣).
Definition φ40 := φ30.
Definition φ41 := (I_2 ⊗ I_2 ⊗ X) × φ31.
Definition φ42 := (I_2 ⊗ I_2 ⊗ Z) × φ32.

Lemma step40 : φ40 = / 2  .* (∣0⟩ ⊗ ∣0⟩) ⊗ ketp.
Proof.
unfold ketp,φ40.
rewrite step30.
distrubute_plus.
auto.
Qed.

Lemma step41 : φ41 = / 2  .* (∣0⟩ ⊗ ∣1⟩) ⊗ ketp.
Proof.
unfold ketp,φ41,I_2,Z,X.
rewrite step31.
distrubute_plus.
isolate_scale.
kron_mult.
assoc_right.
repeat matrix_mult_reduce.
reduce_scale.
Qed.

Lemma Cmult_op1_r (x : C) : x * -1 = -x.
Proof. apply injective_projections ; simpl ; ring. Qed.
Lemma Cmult_op1_l (x : C) : -1 * x = -x.
Proof. apply injective_projections ; simpl ; ring. Qed.

Lemma step42 : φ42 = / 2  .* (∣1⟩ ⊗ ∣0⟩) ⊗ ketp.
Proof.
unfold ketp,φ42,I_2,Z,X.
rewrite step32.
distrubute_plus.
isolate_scale.
kron_mult.
assoc_right.
repeat matrix_mult_reduce.
reduce_scale.
rewrite Cmult_op1_l.
rewrite Cmult_op1_r.
rewrite Copp_mult_distr_l.
rewrite Copp_involutive.
auto.
Qed.

Definition φ43' := (I_2 ⊗ I_2 ⊗ X) × φ33.
Lemma step43' : φ43' = / 2  .* (∣1⟩ ⊗ ∣1⟩) ⊗ (/√2 .* ∣0⟩ .+(/ √ 2 * -1) .* ∣1⟩).
Proof.
unfold ketp,φ43',I_2,Z,X.
rewrite step33.
distrubute_plus.
isolate_scale.
kron_mult.
assoc_right.
repeat matrix_mult_reduce.
reduce_scale.
Qed.

Definition φ43 := (I_2 ⊗ I_2 ⊗ Z) × φ43'.
Lemma step43 : φ43 = / 2  .* (∣1⟩ ⊗ ∣1⟩) ⊗ ketp.
Proof.
unfold ketp,φ43,I_2,Z,X.
rewrite step43'.
distrubute_plus.
isolate_scale.
kron_mult.
assoc_right.
repeat matrix_mult_reduce.
reduce_scale.
rewrite Cmult_op1_l.
rewrite Cmult_op1_r.
rewrite Copp_mult_distr_l.
rewrite Copp_involutive.
auto.
Qed.


(* autorewrite with C_db; try lca. *)

(*ρ φ*)



