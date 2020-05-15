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
unfold CIT,super.
solve_matrix.
Qed.

(* Lemma DQFT_ket0_3' : super ((hadamard ⊗ I 2 ⊗ I 2) × (CS ⊗ I 2) × (I 2 ⊗ hadamard ⊗ I 2) × CIT ×  (I 2 ⊗ CS) × (I 2 ⊗ I 2 ⊗ hadamard)) ρ0 = (∣+⟩ ⊗ ∣+⟩ ⊗ ∣+⟩) × (∣+⟩ ⊗ ∣+⟩ ⊗ ∣+⟩)†.
Proof.
unfold ρ0,φ0,CIT,CS,PS,PT,phase_shift,control,super.
unfold ketp,ketn.
solve_matrix.
Qed. *)