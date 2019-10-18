Require Export Quantum.

Definition ket0 := ∣0⟩.
Definition ket1 := ∣1⟩.
Definition bra0 := ⟨0∣.
Definition bra1 := ⟨0∣.
Definition bra0' := ket0†.
Definition bra1' := ket1†.
Check ket0.
Check bra0.
Check bra0'.
Lemma bra_eq : bra0 = bra0'.
Proof. 
unfold bra0,bra0'.
reflexivity.
Qed.

Lemma adjoint_ket0_bra0 : ∣0⟩ † = ⟨0∣.
Proof. solve_matrix. Qed.

Lemma adjoint_ket1_bra1 : ∣1⟩ † = ⟨1∣.
Proof. solve_matrix. Qed.


Lemma Mmult_bra0_ket0 : ⟨0∣ × ∣0⟩ = I 1.
Proof. solve_matrix. Qed.
Lemma Mmult_bra0_ket1 : ⟨0∣ × ∣1⟩ = Zero.
Proof. solve_matrix. Qed.
Lemma Mmult_bra1_ket0 : ⟨1∣ × ∣0⟩ = Zero.
Proof. solve_matrix. Qed.
Lemma Mmult_bra1_ket1 : ⟨1∣ × ∣1⟩ = I 1.
Proof. solve_matrix. Qed.


Lemma Mmult_bra00_ket00 :( ⟨0∣ ⊗ ⟨0∣) × (∣0⟩ ⊗ ∣0⟩) = I 1.
Proof.
rewrite kron_mixed_product.
rewrite Mmult_bra0_ket0.
rewrite id_kron.
reflexivity.
(* solve_matrix. *) Qed.
Lemma Mmult_bra00_ket01 :( ⟨0∣ ⊗ ⟨0∣) × (∣0⟩ ⊗ ∣1⟩) = Zero.
Proof.
rewrite kron_mixed_product.
rewrite Mmult_bra0_ket0.
rewrite Mmult_bra0_ket1.
rewrite kron_0_r.
reflexivity.
(* solve_matrix. *) Qed.
Lemma Mmult_bra00_ket10 :( ⟨0∣ ⊗ ⟨0∣) × (∣1⟩ ⊗ ∣0⟩) = Zero.
Proof.
rewrite kron_mixed_product.
rewrite Mmult_bra0_ket0.
rewrite Mmult_bra0_ket1.
rewrite kron_0_l.
reflexivity.
(* solve_matrix. *) Qed.
Lemma Mmult_bra00_ket11 :( ⟨0∣ ⊗ ⟨0∣) × (∣1⟩ ⊗ ∣1⟩) = Zero.
Proof.
rewrite kron_mixed_product.
rewrite Mmult_bra0_ket1.
rewrite kron_0_l.
reflexivity.
(* solve_matrix. *) Qed.
Lemma Mmult_bra01_ket00 :( ⟨0∣ ⊗ ⟨1∣) × (∣0⟩ ⊗ ∣0⟩) = Zero.
Proof.
rewrite kron_mixed_product.
rewrite Mmult_bra0_ket0.
rewrite Mmult_bra1_ket0.
rewrite kron_0_r.
reflexivity.
(* solve_matrix. *) Qed.
Lemma Mmult_bra01_ket01 :( ⟨0∣ ⊗ ⟨1∣) × (∣0⟩ ⊗ ∣1⟩) = I 1.
Proof.
rewrite kron_mixed_product.
rewrite Mmult_bra0_ket0.
rewrite Mmult_bra1_ket1.
rewrite id_kron.
reflexivity.
(* solve_matrix. *) Qed.
Lemma Mmult_bra01_ket10 :( ⟨0∣ ⊗ ⟨1∣) × (∣1⟩ ⊗ ∣0⟩) = Zero.
Proof.
rewrite kron_mixed_product.
rewrite Mmult_bra0_ket1.
rewrite Mmult_bra1_ket0.
rewrite kron_0_l.
reflexivity.
(* solve_matrix. *) Qed.
Lemma Mmult_bra01_ket11 :( ⟨0∣ ⊗ ⟨1∣) × (∣1⟩ ⊗ ∣1⟩) = Zero.
Proof.
rewrite kron_mixed_product.
rewrite Mmult_bra0_ket1.
rewrite Mmult_bra1_ket1.
rewrite kron_0_l.
reflexivity.
(* solve_matrix. *) Qed.
Lemma Mmult_bra10_ket00 :( ⟨1∣ ⊗ ⟨0∣) × (∣0⟩ ⊗ ∣0⟩) = Zero.
Proof.
rewrite kron_mixed_product.
rewrite Mmult_bra0_ket0.
rewrite Mmult_bra1_ket0.
rewrite kron_0_l. 
reflexivity.
(* solve_matrix. *) Qed.
Lemma Mmult_bra10_ket01 :( ⟨1∣ ⊗ ⟨0∣) × (∣0⟩ ⊗ ∣1⟩) = Zero.
Proof.
rewrite kron_mixed_product.
rewrite Mmult_bra1_ket0.
rewrite Mmult_bra0_ket1.
rewrite kron_0_l.
reflexivity.
(* solve_matrix. *) Qed.
Lemma Mmult_bra10_ket10 :( ⟨1∣ ⊗ ⟨0∣) × (∣1⟩ ⊗ ∣0⟩) = I 1.
Proof.
rewrite kron_mixed_product.
rewrite Mmult_bra1_ket1.
rewrite Mmult_bra0_ket0.
rewrite id_kron.
reflexivity.
(* solve_matrix. *) Qed.
Lemma Mmult_bra10_ket11 :( ⟨1∣ ⊗ ⟨0∣) × (∣1⟩ ⊗ ∣1⟩) = Zero.
Proof.
rewrite kron_mixed_product.
rewrite Mmult_bra0_ket1.
rewrite Mmult_bra1_ket1.
rewrite kron_0_r.
reflexivity.
(* solve_matrix. *) Qed.
Lemma Mmult_bra11_ket00 :( ⟨1∣ ⊗ ⟨1∣) × (∣0⟩ ⊗ ∣0⟩) = Zero.
Proof.
rewrite kron_mixed_product.
rewrite Mmult_bra1_ket0.
rewrite kron_0_r.
reflexivity.
(* solve_matrix. *) Qed.
Lemma Mmult_bra11_ket01 :( ⟨1∣ ⊗ ⟨1∣) × (∣0⟩ ⊗ ∣1⟩) = Zero.
Proof.
rewrite kron_mixed_product.
rewrite Mmult_bra1_ket0.
rewrite Mmult_bra1_ket1.
rewrite kron_0_l.
reflexivity.
(* solve_matrix. *) Qed.
Lemma Mmult_bra11_ket10 :( ⟨1∣ ⊗ ⟨1∣) × (∣1⟩ ⊗ ∣0⟩) = Zero.
Proof.
rewrite kron_mixed_product.
rewrite Mmult_bra1_ket1.
rewrite Mmult_bra1_ket0.
rewrite kron_0_r.
reflexivity.
(* solve_matrix. *) Qed.
Lemma Mmult_bra11_ket11 :( ⟨1∣ ⊗ ⟨1∣) × (∣1⟩ ⊗ ∣1⟩) = I 1.
Proof.
rewrite kron_mixed_product.
rewrite Mmult_bra1_ket1.
rewrite id_kron.
reflexivity.
(* solve_matrix. *) Qed.


Definition ketp := (/√2 .* ∣0⟩ .+ /√2 .* ∣1⟩).
Definition ketn := (/√2 .* ∣0⟩ .+ (-/√2) .* ∣1⟩).



Definition bell00' := /√2 .* ∣0,0⟩ .+ /√2 .* ∣1,1⟩.
Definition bell01' := /√2 .* ∣0,1⟩ .+ /√2 .* ∣1,0⟩.
Definition bell10' := /√2 .* ∣0,0⟩ .+ (-/√2) .* ∣1,1⟩.
Definition bell11' := /√2 .* ∣0,1⟩ .+ (-/√2) .* ∣1,0⟩.


Definition bell00 := /√2 .* (∣0⟩ ⊗ ∣0⟩) .+ /√2 .* (∣1⟩ ⊗ ∣1⟩).
Definition bell01 := /√2 .* (∣0⟩ ⊗ ∣1⟩) .+ /√2 .* (∣1⟩ ⊗ ∣0⟩).
Definition bell10 := /√2 .* (∣0⟩ ⊗ ∣0⟩) .+ (-/√2) .* (∣1⟩ ⊗ ∣1⟩).
Definition bell11 := /√2 .* (∣0⟩ ⊗ ∣1⟩) .+ (-/√2) .* (∣1⟩ ⊗ ∣0⟩).


Check bell00'.
Check bell00.
Lemma bell_eq : bell00 = bell00'.
Proof.
unfold bell00',bell00.
reflexivity.
Qed.

Module toy_automation.

Lemma Mmult_bra0_ket0 : ⟨0∣ × ∣0⟩ = 1 .* I 1.
Proof. solve_matrix. Qed.
Lemma Mmult_bra0_ket1 : ⟨0∣ × ∣1⟩ = 0 .* I 1.
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
repeat rewrite ?Mscale_mult_dist_l,?Mscale_mult_dist_r,?Mscale_kron_dist_r,?Mscale_kron_dist_l.

Ltac assoc_right:=
repeat rewrite Mmult_assoc.

Ltac group_kron:=
repeat rewrite <- kron_mixed_product.

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
  rewrite <- Mmult_assoc.
  auto.
Qed.

Hint Extern 1 (fake_eq (@Mmult _ _ _ _ _) _) => apply fake_eq_intro; apply Mmult_bra0_ket0: matrix_reduce.
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
repeat rewrite ?Mmult_1_l, ?Mmult_1_r.


Lemma rr :  ∣0⟩ × ⟨0∣ × (∣0⟩ × ⟨1∣) × ∣1⟩ = ∣0⟩ × ⟨1∣ × (∣0⟩ × ⟨1∣) × ∣0⟩.

assoc_right.
matrix_mult_reduce.
matrix_mult_reduce.
matrix_mult_reduce.
matrix_mult_reduce.

Abort.

Definition H := /√2 .*((∣0⟩ .+ ∣1⟩) × ⟨0∣ .+ (∣0⟩ .+  (-1).* ∣1⟩) × ⟨1∣).

Lemma H_ket0 : H × ∣0⟩ = (/√2 .* ∣0⟩ .+ /√2 .* ∣1⟩).
Proof.
unfold H.
distrubute_plus.
isolate_scale.

assoc_right.
repeat matrix_mult_reduce.
(* rewrite Mscale_mult_dist_l.
rewrite Mmult_plus_distr_r.
rewrite Mmult_assoc.
rewrite Mmult_bra0_ket0.
rewrite Mmult_1_r.
rewrite Mmult_assoc.
rewrite Mmult_bra1_ket0.
rewrite Mmult_0_r.
rewrite Mplus_assoc.
rewrite Mplus_0_r.
rewrite Mscale_plus_distr_r.
reflexivity.
show_wf. *)
Abort.

Definition H' := /√2 .* (∣0⟩ × ⟨0∣) .+ /√2 .* (∣0⟩ × ⟨1∣)
              .+ /√2 .* (∣1⟩ × ⟨0∣) .+ (-/√2) .* (∣1⟩ × ⟨1∣).


Definition I_2 := ∣0⟩ × ⟨0∣ .+ ∣1⟩ × ⟨1∣.

Definition X := ∣1⟩ × ⟨0∣ .+  ∣0⟩ × ⟨1∣.

Definition Z := ∣0⟩ × ⟨0∣ .+  (-1).* ∣1⟩ × ⟨1∣.

Definition Y := Ci .* ∣1⟩ × ⟨0∣ .+ (-Ci) .* ∣0⟩ × ⟨1∣.

Definition CNOT := (∣0⟩ ⊗ ∣0⟩) × (⟨0∣ ⊗ ⟨0∣)
                .+ (∣0⟩ ⊗ ∣1⟩) × (⟨0∣ ⊗ ⟨1∣)
                .+ (∣1⟩ ⊗ ∣0⟩) × (⟨1∣ ⊗ ⟨1∣)
                .+ (∣1⟩ ⊗ ∣1⟩) × (⟨1∣ ⊗ ⟨0∣).


Definition state0 := (∣0⟩ ⊗ ∣0⟩).
Definition state1 := ((H ⊗ (I_2)) × state0).
Definition state2 := CNOT × state1.



Lemma pre_bell00 : bell00 = state2.
Proof.
(* unfold state2,state1,state0,CNOT,bell00,H,I_2.
solve_matrix. *)
(*
unfold state2,state1,state0,CNOT,H,I_2.
distrubute_plus.
isolate_scale.
group_kron.
assoc_right.
repeat matrix_mult_reduce.
*)
unfold state2,state1,state0.
rewrite kron_mixed_product.
unfold H,I_2.
(*
rewrite kron_mixed_product.
rewrite Mmult_plus_distr_r.
rewrite Mmult_plus_distr_r.

rewrite Mmult_bra0_ket0.
rewrite Mmult_1_r.
rewrite Mmult_assoc.
rewrite Mmult_bra1_ket0.
rewrite Mmult_0_r.
rewrite Mplus_assoc.
rewrite Mplus_0_r.
rewrite Mscale_plus_distr_r.
reflexivity.



rewrite Mscale_mult_dist_l.
rewrite Mmult_plus_distr_r.
rewrite Mmult_assoc.
rewrite Mmult_bra0_ket0.
rewrite Mmult_1_r.
rewrite Mmult_assoc.
rewrite Mmult_bra1_ket0.
rewrite Mmult_0_r.
rewrite Mplus_assoc.
rewrite Mplus_0_r.
rewrite Mscale_plus_distr_r.
unfold I_2.
rewrite Mmult_plus_distr_r.
rewrite Mmult_assoc.
rewrite Mmult_bra0_ket0.
rewrite Mmult_assoc.
rewrite Mmult_bra1_ket0.
rewrite Mmult_1_r.
rewrite Mmult_0_r.
rewrite Mplus_0_r.
rewrite kron_plus_distr_r.
rewrite Mmult_plus_distr_l.





unfold H,I_2.
repeat rewrite kron_plus_distr_r.
repeat rewrite kron_plus_distr_l.
repeat rewrite Mscale_kron_dist_l.
repeat rewrite <- kron_mixed_product.
repeat rewrite Mmult_plus_distr_r.
repeat rewrite Mscale_mult_dist_l.
unfold state0.



*)
 (* solve_matrix. *) Admitted.


Definition bell00' : Matrix (2*2) 1 := 
  fun x y => match x, y with 
          | 0, 0 => (1 / √2)
          | 3, 0 => (1 / √2)
          | _, _ => 0
          end.

Lemma pre_bell00' : bell00' = state2.
Proof.
unfold bell00',state2,CNOT,state1,state0,I_2,H.
solve_matrix. Qed.

