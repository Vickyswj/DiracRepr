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

Definition GHZ : Vector 8 := 
  fun x y => match x, y with 
          | 0, 0 => /√2
          | 7, 0 => /√2
          | _, _ => C0
          end.

Definition M0 : Matrix 2 2 := 
  fun x y => match x, y with 
          | 0, 0 => C1
          | _, _ => C0
          end.

Definition M1 : Matrix 2 2 := 
  fun x y => match x, y with 
          | 1, 1 => C1
          | _, _ => C0
          end.



Definition φ (a b : C) : Vector 2 := a .* ∣0⟩ .+ b .* ∣1⟩.


Lemma Dss0 :  forall (a b : C),
super ((M0 ⊗ M0 ⊗ M0 ⊗ I 2) × (I 2 ⊗ hadamard ⊗ hadamard ⊗ I 2) × (notc ⊗ I 2 ⊗ I 2)) ((φ a b ⊗ GHZ) × (φ a b⊗ GHZ)†) = (/ √ 2 * / 2  .* ∣0⟩ ⊗ ∣0⟩  ⊗ ∣0⟩ ⊗ (φ a b)) × (/ √ 2 * / 2  .* ∣0⟩ ⊗ ∣0⟩  ⊗ ∣0⟩ ⊗ (φ a b))†.
Proof.
intros. unfold GHZ,φ,super.
solve_matrix.
Qed.

Lemma Dtele0' :  forall (a b : C),
super (M0 ⊗ M0 ⊗ I 2) (super (hadamard ⊗ I 2 ⊗ I 2) (super (cnot ⊗ I 2) ((φ a b⊗ bell00) × (φ a b⊗ bell00)†))) = (/ 2  .* ∣0⟩ ⊗ ∣0⟩ ⊗ (φ a b)) × (/ 2  .* ∣0⟩ ⊗ ∣0⟩ ⊗ (φ a b))† .
Proof.
intros. unfold bell00,φ,super.
solve_matrix.
Qed.