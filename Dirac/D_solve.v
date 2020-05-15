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

Lemma Ddeutsch0 : super (hadamard ⊗ I 2) (super (I 2 ⊗ I 2) (super (hadamard ⊗ hadamard) ((∣0⟩ ⊗ ∣1⟩) × (∣0⟩ ⊗ ∣1⟩)†))) = (∣0⟩ ⊗ ∣-⟩) × (∣0⟩ ⊗ ∣-⟩)†.
Proof.
unfold super.
solve_matrix. 
Qed.

Lemma Ddeutsch0' : super ((hadamard ⊗ I 2) × (I 2 ⊗ I 2) × (hadamard ⊗ hadamard)) ((∣0⟩ ⊗ ∣1⟩) × (∣0⟩ ⊗ ∣1⟩)†)= (∣0⟩ ⊗ ∣-⟩) × (∣0⟩ ⊗ ∣-⟩)†.
Proof.
unfold super.
solve_matrix. 
Qed.


(* f(0) =  f(1) = 1 *)
Lemma deutsch1 : (hadamard ⊗ I 2) × (I 2 ⊗ σx) × (hadamard ⊗ hadamard) × (∣0⟩ ⊗ ∣1⟩) = -1 .* ∣0⟩ ⊗ ∣-⟩ .
Proof. solve_matrix. Qed.

Lemma Ddeutsch1 : super (hadamard ⊗ I 2) (super (I 2 ⊗ σx) (super (hadamard ⊗ hadamard) ((∣0⟩ ⊗ ∣1⟩) × (∣0⟩ ⊗ ∣1⟩)†)))= (-1 .* ∣0⟩ ⊗ ∣-⟩) × (-1 .* ∣0⟩ ⊗ ∣-⟩ )†.
Proof.
unfold super.
solve_matrix.
Qed.

Lemma Ddeutsch1' : super ((hadamard ⊗ I 2) × (I 2 ⊗ σx) × (hadamard ⊗ hadamard)) ((∣0⟩ ⊗ ∣1⟩) × (∣0⟩ ⊗ ∣1⟩)†)= (-1 .* ∣0⟩ ⊗ ∣-⟩) × (-1 .* ∣0⟩ ⊗ ∣-⟩ )†.
Proof.
unfold super.
solve_matrix.
Qed.


(* f(0) = 0, f(1) = 1 *)
Lemma deutsch2 : (hadamard ⊗ I 2) × cnot × (hadamard ⊗ hadamard) × (∣0⟩ ⊗ ∣1⟩) = ∣1⟩ ⊗ ∣-⟩ .
Proof. solve_matrix. Qed.

Lemma Ddeutsch2 : super (hadamard ⊗ I 2) (super cnot (super (hadamard ⊗ hadamard) ((∣0⟩ ⊗ ∣1⟩) × (∣0⟩ ⊗ ∣1⟩)†))) = (∣1⟩ ⊗ ∣-⟩) × (∣1⟩ ⊗ ∣-⟩ )†.
Proof.
unfold super.
solve_matrix.
Qed.

Lemma Ddeutsch2' : super ((hadamard ⊗ I 2) × cnot × (hadamard ⊗ hadamard)) ((∣0⟩ ⊗ ∣1⟩) × (∣0⟩ ⊗ ∣1⟩)†) = (∣1⟩ ⊗ ∣-⟩) × (∣1⟩ ⊗ ∣-⟩ )†.
Proof.
unfold super.
solve_matrix.
Qed.


(* f(0) = 1, f(1) = 0 *)
Lemma deutsch3 : (hadamard ⊗ I 2) × notc × (hadamard ⊗ hadamard) × (∣0⟩ ⊗ ∣1⟩) = -1 .* ∣1⟩ ⊗ ∣-⟩ .
Proof. solve_matrix. Qed.

Lemma Ddeutsch3 : super (hadamard ⊗ I 2) (super notc (super (hadamard ⊗ hadamard) ((∣0⟩ ⊗ ∣1⟩) × (∣0⟩ ⊗ ∣1⟩)†))) = (-1 .* ∣1⟩ ⊗ ∣-⟩) × (-1 .* ∣1⟩ ⊗ ∣-⟩)†.
Proof.
unfold super.
solve_matrix.
Qed.

Lemma Ddeutsch3' : super ((hadamard ⊗ I 2) × notc × (hadamard ⊗ hadamard)) ((∣0⟩ ⊗ ∣1⟩) × (∣0⟩ ⊗ ∣1⟩)†) = (-1 .* ∣1⟩ ⊗ ∣-⟩) × (-1 .* ∣1⟩ ⊗ ∣-⟩)†.
Proof.
unfold super.
solve_matrix.
Qed.

