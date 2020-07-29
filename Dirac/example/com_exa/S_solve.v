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

Definition CIX : Matrix  8 8 :=
  fun x y => match x, y with 
          | 0, 0 => C1
          | 1, 1 => C1
          | 2, 2 => C1
          | 3, 3 => C1
          | 4, 7 => C1
          | 5, 6 => C1
          | 6, 5 => C1
          | 7, 4 => C1
          | _, _ => C0
          end.

Lemma simon2 : (hadamard ⊗ hadamard ⊗ I 2 ⊗ I 2) × (I 2 ⊗ cnot ⊗ I 2) × (hadamard ⊗ hadamard ⊗ I 2 ⊗ σx) × ∣0,0,0,0⟩ = /2 .* ∣0,0,0,1⟩ .+ /2 .* ∣0,1,0,1⟩ .+ /2 .* ∣0,0,1,1⟩ .+ - /2 .* ∣0,1,1,1⟩.
Proof.
solve_matrix.
Qed.

Lemma Dsimon2 : super (hadamard ⊗ hadamard ⊗ I 2 ⊗ I 2) (super (I 2 ⊗ cnot ⊗ I 2) (super (hadamard ⊗ hadamard ⊗ I 2 ⊗ σx) ((∣0,0,0,0⟩) × (∣0,0,0,0⟩)†))) = (/2 .* ∣0,0,0,1⟩ .+ /2 .* ∣0,1,0,1⟩ .+ /2 .* ∣0,0,1,1⟩ .+ - /2 .* ∣0,1,1,1⟩) × (/2 .* ∣0,0,0,1⟩ .+ /2 .* ∣0,1,0,1⟩ .+ /2 .* ∣0,0,1,1⟩ .+ - /2 .* ∣0,1,1,1⟩)†.
Proof.
unfold super.
solve_matrix.
Qed.

(* Lemma Dsimon2' : super ((hadamard ⊗ hadamard ⊗ I 2 ⊗ I 2) × ((I 2 ⊗ cnot ⊗ I 2) × (hadamard ⊗ hadamard ⊗ I 2 ⊗ σx))) ((∣0,0,0,0⟩) × (∣0,0,0,0⟩)†) = (/2 .* ∣0,0,0,1⟩ .+ /2 .* ∣0,1,0,1⟩ .+ /2 .* ∣0,0,1,1⟩ .+ - /2 .* ∣0,1,1,1⟩) × (/2 .* ∣0,0,0,1⟩ .+ /2 .* ∣0,1,0,1⟩ .+ /2 .* ∣0,0,1,1⟩ .+ - /2 .* ∣0,1,1,1⟩)†.
Proof.
unfold super.
solve_matrix.
Qed. *)


Lemma simon3 : (hadamard ⊗ hadamard ⊗ I 2 ⊗ I 2) × (I 2 ⊗ cnot ⊗ I 2) × (CIX ⊗ σx) × (hadamard ⊗ hadamard ⊗ I 2 ⊗ I 2) × ∣0,0,0,0⟩ = /2 .* ∣0,0,0,1⟩ .+ /2 .* ∣1,1,0,1⟩ .+ /2 .* ∣0,0,1,1⟩ .+ - /2 .* ∣1,1,1,1⟩.
Proof.
unfold CIX.
solve_matrix.
Qed.

Lemma Dsimon3 : super (hadamard ⊗ hadamard ⊗ I 2 ⊗ I 2) (super (I 2 ⊗ cnot ⊗ I 2) (super (CIX ⊗ I 2) (super (hadamard ⊗ hadamard ⊗ I 2 ⊗ σx) ((∣0,0,0,0⟩) × (∣0,0,0,0⟩)†)))) = (/2 .* ∣0,0,0,1⟩ .+ /2 .* ∣1,1,0,1⟩ .+ /2 .* ∣0,0,1,1⟩ .+ - /2 .* ∣1,1,1,1⟩) × (/2 .* ∣0,0,0,1⟩ .+ /2 .* ∣1,1,0,1⟩ .+ /2 .* ∣0,0,1,1⟩ .+ - /2 .* ∣1,1,1,1⟩)†.
Proof.
unfold super.
solve_matrix.
Qed.

(* Lemma Dsimon3' : super ((hadamard ⊗ hadamard ⊗ I 2 ⊗ I 2) × ((I 2 ⊗ cnot ⊗ I 2) × ((CIX ⊗ I 2) × (hadamard ⊗ hadamard ⊗ I 2 ⊗ σx)))) ((∣0,0,0,0⟩) × (∣0,0,0,0⟩)†) = (/2 .* ∣0,0,0,1⟩ .+ /2 .* ∣1,1,0,1⟩ .+ /2 .* ∣0,0,1,1⟩ .+ - /2 .* ∣1,1,1,1⟩) × (/2 .* ∣0,0,0,1⟩ .+ /2 .* ∣1,1,0,1⟩ .+ /2 .* ∣0,0,1,1⟩ .+ - /2 .* ∣1,1,1,1⟩)†.
Proof.
unfold super.
solve_matrix.
Qed. *)
