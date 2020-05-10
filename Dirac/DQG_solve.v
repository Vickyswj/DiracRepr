Require Export Quantum.

Definition ketp : Vector 2 := 
  fun x y => match x, y with 
          | 0, 0 => /√2
          | 1, 0 => /√2
          | _, _ => C0
          end.
Definition ketn : Vector 2 := 
  fun x y => match x, y with 
          | 0, 0 => /√2
          | 1, 0 => -/√2
          | _, _ => C0
          end.

Notation "∣+⟩" := ketp.
Notation "∣-⟩" := ketn.
Notation "⟨+∣" := ketp†.
Notation "⟨-∣" := ketn†.


(* Deutsch *)

(* One-time *)

(* f(0) =  f(1) = 0 *)
Lemma deutsch0 : (hadamard ⊗ I 2) × (I 2 ⊗ I 2) × (hadamard ⊗ hadamard) × (∣0⟩ ⊗ ∣1⟩) = ∣0⟩ ⊗ ∣-⟩ .
Proof. solve_matrix. Qed.

Lemma Cmult_inv2_sqrt2 : 2 * (/ 2 * / √ 2) = / √ 2 .    Proof. lca. Qed.
Lemma Ceq1 : 2 * (/ √ 2 * / 2) * (2 * (/ √ 2 * / 2)) ^* = /2 .
Proof.
rewrite (Cmult_comm (/ √ 2) (/ 2)) .
rewrite Cmult_inv2_sqrt2.
autorewrite with C_db.
auto.
Qed.
Hint Rewrite Ceq1: C_db.

Lemma Ddeutsch0 : super ((hadamard ⊗ I 2) × (I 2 ⊗ I 2) × (hadamard ⊗ hadamard)) ((∣0⟩ ⊗ ∣1⟩) × (∣0⟩ ⊗ ∣1⟩)†)= (∣0⟩ ⊗ ∣-⟩) × (∣0⟩ ⊗ ∣-⟩)†.
Proof.
unfold super.
solve_matrix.
Qed.


(* f(0) =  f(1) = 1 *)
Lemma deutsch1 : (hadamard ⊗ I 2) × (I 2 ⊗ σx) × (hadamard ⊗ hadamard) × (∣0⟩ ⊗ ∣1⟩) = -1 .* ∣0⟩ ⊗ ∣-⟩ .
Proof. solve_matrix. Qed.

Lemma Ddeutsch1 : super ((hadamard ⊗ I 2) × (I 2 ⊗ σx) × (hadamard ⊗ hadamard)) ((∣0⟩ ⊗ ∣1⟩) × (∣0⟩ ⊗ ∣1⟩)†)= (-1 .* ∣0⟩ ⊗ ∣-⟩) × (-1 .* ∣0⟩ ⊗ ∣-⟩ )†.
Proof.
unfold super.
solve_matrix.
Qed.


(* f(0) = 0, f(1) = 1 *)
Lemma deutsch2 : (hadamard ⊗ I 2) × cnot × (hadamard ⊗ hadamard) × (∣0⟩ ⊗ ∣1⟩) = ∣1⟩ ⊗ ∣-⟩ .
Proof. solve_matrix. Qed.

Lemma Ddeutsch2 : super ((hadamard ⊗ I 2) × cnot × (hadamard ⊗ hadamard)) ((∣0⟩ ⊗ ∣1⟩) × (∣0⟩ ⊗ ∣1⟩)†) = (∣1⟩ ⊗ ∣-⟩) × (∣1⟩ ⊗ ∣-⟩ )†.
Proof.
unfold super.
solve_matrix.
Qed.


(* f(0) = 1, f(1) = 0 *)
Lemma deutsch3 : (hadamard ⊗ I 2) × notc × (hadamard ⊗ hadamard) × (∣0⟩ ⊗ ∣1⟩) = -1 .* ∣1⟩ ⊗ ∣-⟩ .
Proof. solve_matrix. Qed.

Lemma Ddeutsch3 : super ((hadamard ⊗ I 2) × notc × (hadamard ⊗ hadamard)) ((∣0⟩ ⊗ ∣1⟩) × (∣0⟩ ⊗ ∣1⟩)†) = (-1 .* ∣1⟩ ⊗ ∣-⟩) × (-1 .* ∣1⟩ ⊗ ∣-⟩)†.
Proof.
unfold super.
solve_matrix.
Qed.


(* QFT *)

Definition PS := phase_shift (PI/2).
Definition PT := phase_shift (PI/4).
Definition CS := control PS.
Definition CT := control PT.
Definition CIT :=  ∣0⟩⟨0∣ ⊗ I 2 ⊗ I 2 .+ ∣1⟩⟨1∣ ⊗ I 2 ⊗ PT.


(* One-time *)

Lemma QFT_ket0_3 : (hadamard ⊗ I 2 ⊗ I 2) × (CS ⊗ I 2) × (I 2 ⊗ hadamard ⊗ I 2) × CIT ×  (I 2 ⊗ CS) × (I 2 ⊗ I 2 ⊗ hadamard) × (∣0⟩ ⊗ ∣0⟩ ⊗ ∣0⟩) = ∣+⟩ ⊗ ∣+⟩ ⊗ ∣+⟩.
Proof.
unfold CIT.
solve_matrix.
Qed.

Lemma DQFT_ket0_3 : super (hadamard ⊗ I 2 ⊗ I 2) (super (CS ⊗ I 2) (super (I 2 ⊗ hadamard ⊗ I 2) (super CIT (super (I 2 ⊗ CS) (super (I 2 ⊗ I 2 ⊗ hadamard) ((∣0⟩ ⊗ ∣0⟩ ⊗ ∣0⟩) × (∣0⟩ ⊗ ∣0⟩ ⊗ ∣0⟩)†)))))) = (∣+⟩ ⊗ ∣+⟩ ⊗ ∣+⟩) × (∣+⟩ ⊗ ∣+⟩ ⊗ ∣+⟩)†.
Proof.
unfold CIT,CS,super.
solve_matrix.
Qed.

(* Lemma DQFT_ket0_3' : super ((hadamard ⊗ I 2 ⊗ I 2) × (CS ⊗ I 2) × (I 2 ⊗ hadamard ⊗ I 2) × CIT ×  (I 2 ⊗ CS) × (I 2 ⊗ I 2 ⊗ hadamard)) ρ0 = (∣+⟩ ⊗ ∣+⟩ ⊗ ∣+⟩) × (∣+⟩ ⊗ ∣+⟩ ⊗ ∣+⟩)†.
Proof.
unfold ρ0,φ0,CIT,CS,PS,PT,phase_shift,control,super.
unfold ketp,ketn.
solve_matrix.
Qed. *)



(* Grover *)

(*Step-by-step*)

(*Vector*)
Definition ORA : Matrix  8 8 :=
  fun x y => match x, y with 
          | 0, 0 => C1
          | 1, 1 => C1
          | 0, 6 => C1
          | 1, 7 => C1
          | 6, 0 => C1
          | 7, 1 => C1
          | 6, 7 => C1
          | 7, 6 => C1
          | _, _ => C0
          end.
Definition GPS : Matrix  2 2 :=
  fun x y => match x, y with 
          | 0, 0 => C1
          | 1, 1 => -C1
          | _, _ => C0
          end.

Definition φ0 := ∣0⟩ ⊗ ∣0⟩ ⊗ ∣1⟩.
Definition φ1 := (hadamard ⊗ hadamard ⊗ hadamard) × φ0.
Definition φ2 := ORA × φ1.
Definition φ3 := (hadamard ⊗ hadamard ⊗ I 2) × φ2.
Definition φ4 := (GPS ⊗ GPS ⊗ I 2) × φ3.
Definition φ5 := (hadamard ⊗ hadamard ⊗ hadamard) × φ4.


(*Density*)
Definition ρ0 := φ0 × φ0†.
Definition ρ1 := super (hadamard ⊗ hadamard ⊗ hadamard) ρ0.
Definition ρ2 := super ORA ρ1.
Definition ρ3 := super  (hadamard ⊗ hadamard ⊗ I 2) ρ2.
Definition ρ4 := super  (GPS ⊗ GPS ⊗ I 2) ρ3.
Definition ρ5 := super  (hadamard ⊗ hadamard ⊗ hadamard) ρ4.



Lemma Cconj_inv2_sqrt2: (/ 2 * / √ 2) ^* = (/ 2 * / √ 2).
Proof. lca. Qed.
Lemma Ceq2 : 2 * (/ 2 * / √ 2) * (2 * (/ 2 * / √ 2) ^*) =/2.
Proof.
rewrite Cconj_inv2_sqrt2.
rewrite Cmult_inv2_sqrt2.
autorewrite with C_db. lca.
Qed.

Hint Rewrite Ceq2: C_db.



(* One-time *)
Lemma Ceq3 : (/ 2 * / √ 2 * (/ 2 * (2 * (/ 2 * / √ 2)))) = /8 .
Proof.
rewrite <- Cmult_assoc.
rewrite (Cmult_comm (/√ 2) (/ 2 * (2 * (/ 2 * / √ 2)))).
repeat rewrite Cmult_assoc.
rewrite <- Cmult_assoc.
autorewrite with C_db.
lca.
Qed.
Hint Rewrite Ceq3: C_db.

Lemma Grover_2_4 : (hadamard ⊗ hadamard ⊗ hadamard) × (GPS ⊗ GPS ⊗ I 2) ×  (hadamard ⊗ hadamard ⊗ I 2) × ORA × (hadamard ⊗ hadamard ⊗ hadamard) × (∣0⟩ ⊗ ∣0⟩ ⊗ ∣1⟩) = ∣1⟩ ⊗ ∣1⟩ ⊗ ∣1⟩.
Proof. solve_matrix. Qed.


Lemma DGrover_2_4_test1 : super (hadamard ⊗ hadamard ⊗ hadamard) ((∣0⟩ ⊗ ∣0⟩ ⊗ ∣1⟩) × (∣0⟩ ⊗ ∣0⟩ ⊗ ∣1⟩)†) = (∣+⟩ ⊗ ∣+⟩ ⊗ ∣-⟩) × (∣+⟩ ⊗ ∣+⟩ ⊗ ∣-⟩)†.
Proof.
unfold ORA,GPS,hadamard,I,super.
solve_matrix.
(*   autounfold with U_db.
      prep_matrix_equality.
      simpl.
      destruct_m_eq'.
      simpl.
      Csimpl. (* basic rewrites only *) 
      try reflexivity.
      try solve_out_of_bounds. *)
Qed.

Lemma Cconj_inv2 :  (/ 2)^* = / 2.         Proof. lca. Qed.
Lemma Cconj_rad2 : (/ √2)^* = / √2.       Proof. lca. Qed.
Lemma Cconj_invrad2 : (/ 2 * / √ 2) ^* = (/ 2 * / √ 2) .
Proof.
rewrite Cconj_mult_distr.
rewrite Cconj_inv2,Cconj_rad2.
auto.
Qed.

Lemma pu1 : 2 * (2 * (/ 2 * / √ 2 * (/ 2 * / √ 2) ^*)) = / 2 .
Proof.
rewrite Cconj_mult_distr.
rewrite Cconj_inv2,Cconj_rad2.
rewrite (Cmult_assoc 2 (/ 2 * / √ 2)  (/ 2 * / √ 2)).
rewrite (Cmult_assoc 2 (/ 2)  (/ √ 2)).
autorewrite with C_db.
rewrite (Cmult_comm (/ 2) (/√ 2)).
rewrite (Cmult_assoc (/ √ 2) (/ √ 2) (/ 2)).
autorewrite with C_db.
rewrite Cmult_assoc.
autorewrite with C_db.
auto.
Qed.
Hint Rewrite pu1 : C_db.

Lemma DGrover_2_4_test2 : super ORA (super (hadamard ⊗ hadamard ⊗ hadamard) ((∣0⟩ ⊗ ∣0⟩ ⊗ ∣1⟩) × (∣0⟩ ⊗ ∣0⟩ ⊗ ∣1⟩)†)) = (∣0⟩ ⊗ ∣0⟩ ⊗ ∣-⟩) × (∣0⟩ ⊗ ∣0⟩ ⊗ ∣-⟩)†.
Proof.
unfold ORA,GPS,hadamard,I,super.
solve_matrix.
(* assoc_least;
    repeat reduce_matrix; try crunch_matrix.
    (* handle out-of-bounds *)
    unfold Nat.ltb; simpl; try rewrite andb_false_r.
    (* try to solve complex equalities *)
    autorewrite with C_db; try lca. *)
Qed.

Lemma DGrover_2_4_test3' : super (hadamard ⊗ hadamard ⊗ I 2)  ((∣0⟩ ⊗ ∣0⟩ ⊗ ∣-⟩) × (∣0⟩ ⊗ ∣0⟩ ⊗ ∣-⟩)†) = (∣+⟩ ⊗ ∣+⟩ ⊗ ∣-⟩) × (∣+⟩ ⊗ ∣+⟩ ⊗ ∣-⟩)†.
Proof.
unfold ORA,GPS,hadamard,I,super.
solve_matrix.
Qed.

Lemma DGrover_2_4_test3'' : super (hadamard ⊗ hadamard ⊗ I 2) (super ORA (super (hadamard ⊗ hadamard ⊗ hadamard) ((∣0⟩ ⊗ ∣0⟩ ⊗ ∣1⟩) × (∣0⟩ ⊗ ∣0⟩ ⊗ ∣1⟩)†))) = (∣+⟩ ⊗ ∣+⟩ ⊗ ∣-⟩) × (∣+⟩ ⊗ ∣+⟩ ⊗ ∣-⟩)†.
Proof.
rewrite DGrover_2_4_test2.
apply DGrover_2_4_test3'.
Qed.

Lemma pu2 :/ 2 * / 2 * (/ 2) ^* = / 2 * / √ 2 * (/ 2 * / √ 2) ^*.
Proof.
rewrite Cconj_inv2,Cconj_invrad2.
rewrite (Cmult_comm (/ 2) (/√ 2)) at 2.
rewrite <- Cmult_assoc. rewrite <- Cmult_assoc. rewrite Cmult_assoc.
rewrite (Cmult_assoc (/ √ 2) (/ √ 2) (/ 2)).
autorewrite with C_db. rewrite Cmult_assoc.
auto.
Qed.
Hint Rewrite pu2 : C_db.

Lemma DGrover_2_4_test3 : super (hadamard ⊗ hadamard ⊗ I 2) (super ORA (super (hadamard ⊗ hadamard ⊗ hadamard) ((∣0⟩ ⊗ ∣0⟩ ⊗ ∣1⟩) × (∣0⟩ ⊗ ∣0⟩ ⊗ ∣1⟩)†))) = (∣+⟩ ⊗ ∣+⟩ ⊗ ∣-⟩) × (∣+⟩ ⊗ ∣+⟩ ⊗ ∣-⟩)†.
Proof.
unfold ORA,GPS,hadamard,I,super.
solve_matrix.
Qed.
Lemma DGrover_2_4_test4 : super (GPS ⊗ GPS ⊗ I 2) (super (hadamard ⊗ hadamard ⊗ I 2) (super ORA (super (hadamard ⊗ hadamard ⊗ hadamard) ((∣0⟩ ⊗ ∣0⟩ ⊗ ∣1⟩) × (∣0⟩ ⊗ ∣0⟩ ⊗ ∣1⟩)†)))) = (∣-⟩ ⊗ ∣-⟩ ⊗ ∣-⟩) × (∣-⟩ ⊗ ∣-⟩ ⊗ ∣-⟩)†.
Proof.
unfold ORA,GPS,hadamard,I,super.
   assoc_least;
    repeat reduce_matrix; try crunch_matrix.
    (* handle out-of-bounds *)
    unfold Nat.ltb; simpl; try rewrite andb_false_r.
    (* try to solve complex equalities *)
    autorewrite with C_db; try lca. 

Lemma DGrover_2_4 : super (hadamard ⊗ hadamard ⊗ hadamard) (super (GPS ⊗ GPS ⊗ I 2) (super (hadamard ⊗ hadamard ⊗ I 2) (super ORA (super (hadamard ⊗ hadamard ⊗ hadamard) ((∣0⟩ ⊗ ∣0⟩ ⊗ ∣1⟩) × (∣0⟩ ⊗ ∣0⟩ ⊗ ∣1⟩)†))))) = (∣1⟩ ⊗ ∣1⟩ ⊗ ∣1⟩) × (∣1⟩ ⊗ ∣1⟩ ⊗ ∣1⟩)†.
Proof.
unfold ORA,GPS,hadamard,I,super .
solve_matrix.
Qed.
Lemma DGrover_2_4_test : super (hadamard ⊗ hadamard ⊗ hadamard) (super (GPS ⊗ GPS ⊗ I 2) (super (hadamard ⊗ hadamard ⊗ I 2) (super ORA (super (hadamard ⊗ hadamard ⊗ hadamard) ((∣0⟩ ⊗ ∣0⟩ ⊗ ∣1⟩) × (∣0⟩ ⊗ ∣0⟩ ⊗ ∣1⟩)†))))) = (∣1⟩ ⊗ ∣1⟩ ⊗ ∣1⟩) × (∣1⟩ ⊗ ∣1⟩ ⊗ ∣1⟩)†.
Proof.
unfold ORA,GPS,hadamard,I,super .
solve_matrix.
Qed.
