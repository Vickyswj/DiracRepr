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


Definition ORA0 : Matrix  8 8 :=
  fun x y => match x, y with 
          | 0, 1 => C1
          | 1, 0 => C1
          | 2, 2 => C1
          | 3, 3 => C1
          | 4, 4 => C1
          | 5, 5 => C1
          | 6, 6 => C1
          | 7, 7 => C1
          | _, _ => C0
          end.

Definition ORA1 : Matrix  8 8 :=
  fun x y => match x, y with 
          | 0, 0 => C1
          | 1, 1 => C1
          | 2, 3 => C1
          | 3, 2 => C1
          | 4, 4 => C1
          | 5, 5 => C1
          | 6, 6 => C1
          | 7, 7 => C1
          | _, _ => C0
          end.

Definition ORA2 : Matrix  8 8 :=
  fun x y => match x, y with 
          | 0, 0 => C1
          | 1, 1 => C1
          | 2, 2 => C1
          | 3, 3 => C1
          | 4, 5 => C1
          | 5, 4 => C1
          | 6, 6 => C1
          | 7, 7 => C1
          | _, _ => C0
          end.

Definition ORA3 : Matrix  8 8 :=
  fun x y => match x, y with 
          | 0, 0 => C1
          | 1, 1 => C1
          | 2, 2 => C1
          | 3, 3 => C1
          | 4, 4 => C1
          | 5, 5 => C1
          | 6, 7 => C1
          | 7, 6 => C1
          | _, _ => C0
          end.


Definition CPS : Matrix  8 8 :=
  fun x y => match x, y with 
          | 0, 0 => -1/2
          | 0, 1 => 0
          | 0, 2 => 1/2
          | 0, 3 => 0
          | 0, 4 => 1/2
          | 0, 5 => 0
          | 0, 6 => 1/2
          | 0, 7 => 0
          | 1, 0 => 0
          | 1, 1 => -1/2
          | 1, 2 => 0
          | 1, 3 => 1/2
          | 1, 4 => 0
          | 1, 5 => 1/2
          | 1, 6 => 0
          | 1, 7 => 1/2
          | 2, 0 => 1/2
          | 2, 1 => 0
          | 2, 2 => -1/2
          | 2, 3 => 0
          | 2, 4 => 1/2
          | 2, 5 => 0
          | 2, 6 => 1/2
          | 2, 7 => 0
          | 3, 0 => 0
          | 3, 1 => 1/2
          | 3, 2 => 0
          | 3, 3 => -1/2
          | 3, 4 => 0
          | 3, 5 => 1/2
          | 3, 6 => 0
          | 3, 7 => 1/2
          | 4, 0 => 1/2
          | 4, 1 => 0
          | 4, 2 => 1/2
          | 4, 3 => 0
          | 4, 4 => -1/2
          | 4, 5 => 0
          | 4, 6 => 1/2
          | 4, 7 => 0
          | 5, 0 => 0
          | 5, 1 => 1/2
          | 5, 2 => 0
          | 5, 3 => 1/2
          | 5, 4 => 0
          | 5, 5 => -1/2
          | 5, 6 => 0
          | 5, 7 => 1/2
          | 6, 0 => 1/2
          | 6, 1 => 0
          | 6, 2 => 1/2
          | 6, 3 => 0
          | 6, 4 => 1/2
          | 6, 5 => 0
          | 6, 6 => -1/2
          | 6, 7 => 0
          | 7, 0 => 0
          | 7, 1 => 1/2
          | 7, 2 => 0
          | 7, 3 => 1/2
          | 7, 4 => 0
          | 7, 5 => 1/2
          | 7, 6 => 0
          | 7, 7 => -1/2
          | _, _ => C0
          end.
Definition B0 := ∣0⟩ × ⟨0∣.
Definition B1 := ∣0⟩ × ⟨1∣.
Definition B2 := ∣1⟩ × ⟨0∣.
Definition B3 := ∣1⟩ × ⟨1∣.
Definition MI := (B0 .+ B1 .+ B2 .+ B3)⊗ (B0 .+ B1 .+ B2 .+ B3).
Definition GPS := (((/2 .* MI) .+ (-1) .* (I 2 ⊗ I 2)) ⊗ I 2).

Lemma ee : CPS = GPS .
Proof.
unfold CPS,GPS,MI.
solve_matrix.

Qed.

Definition not_CX := B0 ⊗ σx .+ B3 ⊗ I 2 .
Definition ORA0' := B0 ⊗ not_CX .+ B3 ⊗ I 2 ⊗ I 2.
Lemma e : ORA0 = ORA0' .
Proof.
unfold  ORA0,ORA0',not_CX,B0,B3.
solve_matrix.
Qed.

Hint Rewrite Cmult_plus_distr_l Cmult_plus_distr_r Copp_plus_distr Copp_mult_distr_l
              Copp_involutive : C_db.


Lemma DGrover_2_2 :super ((I 2 ⊗ I 2 ⊗ hadamard) × (CPS × (ORA2 × (hadamard ⊗ hadamard ⊗ hadamard)))) ((∣0,0,1⟩) × (∣0,0,1⟩)†)  = ((∣1,0,1⟩) × (∣1,0,1⟩)†).
Proof.
unfold ORA2,CPS,super.
solve_matrix.
Qed.

Lemma DGrover_2_3 :super ((I 2 ⊗ I 2 ⊗ hadamard) × (CPS × (ORA3 × (hadamard ⊗ hadamard ⊗ hadamard)))) ((∣0,0,1⟩) × (∣0,0,1⟩)†)  = ((∣1,1,1⟩) × (∣1,1,1⟩)†).
Proof.
unfold ORA3,CPS,super.
solve_matrix.
Qed.

Lemma DGrover_2_0 :super ((I 2 ⊗ I 2 ⊗ hadamard) × (CPS × (ORA0 × (hadamard ⊗ hadamard ⊗ hadamard)))) ((∣0,0,1⟩) × (∣0,0,1⟩)†)  = ((∣0,0,1⟩) × (∣0,0,1⟩)†).
Proof.
unfold ORA0,CPS,super.
solve_matrix.
Qed.

Lemma DGrover_2_1 :super ((I 2 ⊗ I 2 ⊗ hadamard) × (CPS × (ORA1 × (hadamard ⊗ hadamard ⊗ hadamard)))) ((∣0,0,1⟩) × (∣0,0,1⟩)†)  = ((∣0,1,1⟩) × (∣0,1,1⟩)†).
Proof.
unfold ORA1,CPS,super.
solve_matrix.
Qed.

Lemma DGrover_2_2 :super ((I 2 ⊗ I 2 ⊗ hadamard) × (CPS × (ORA2 × (hadamard ⊗ hadamard ⊗ hadamard)))) ((∣0,0,1⟩) × (∣0,0,1⟩)†)  = ((∣1,0,1⟩) × (∣1,0,1⟩)†).
Proof.
unfold ORA2,CPS,super.
solve_matrix.
Qed.

Lemma DGrover_2_3 :super ((I 2 ⊗ I 2 ⊗ hadamard) × (CPS × (ORA3 × (hadamard ⊗ hadamard ⊗ hadamard)))) ((∣0,0,1⟩) × (∣0,0,1⟩)†)  = ((∣1,1,1⟩) × (∣1,1,1⟩)†).
Proof.
unfold ORA3,CPS,super.
solve_matrix.
Qed.

Lemma DGrover_2_0 :super ((I 2 ⊗ I 2 ⊗ hadamard) × (GPS × (ORA0 × (hadamard ⊗ hadamard ⊗ hadamard)))) ((∣0,0,1⟩) × (∣0,0,1⟩)†)  = ((∣0,0,1⟩) × (∣0,0,1⟩)†).
Proof.
unfold ORA0,GPS,MI,B0,B1,B2,B3,super.
solve_matrix.
Qed.
(* Lemma DGrover_2_0 : super ((hadamard ⊗ hadamard ⊗ hadamard) × (σx ⊗ σx ⊗ I 2) × (I 2 ⊗ hadamard ⊗ I 2)
× (cnot ⊗ I 2) × (I 2 ⊗ hadamard ⊗ I 2) × (σx ⊗ σx ⊗ I 2) × (hadamard ⊗ hadamard ⊗ I 2)
 × ORA0 × (hadamard ⊗ hadamard ⊗ hadamard)) ((∣0,0,1⟩) × (∣0,0,1⟩)†)  = ((∣0,0,1⟩) × (∣0,0,1⟩)†).
Proof.
unfold ORA0,super.
solve_matrix.
Qed. *)

