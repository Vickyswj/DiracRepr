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

Definition XC : Matrix 4 4 := 
  fun x y => match x, y with 
          | 0, 0 => C1
          | 1, 3 => C1
          | 2, 2 => C1
          | 3, 1 => C1
          | _, _ => C0
          end.



Definition φ (a b : C) : Vector 2 := a .* ∣0⟩ .+ b .* ∣1⟩.

Lemma Dss0 :  forall (a b : C),
super (M0 ⊗ M0 ⊗ M0 ⊗ I 2) (super (I 2 ⊗ hadamard ⊗ hadamard ⊗ I 2) (super (XC ⊗ I 2 ⊗ I 2) ((φ a b ⊗ GHZ) × (φ a b⊗ GHZ)†))) = (/ √ 2 * / 2  .* ∣0⟩ ⊗ ∣0⟩  ⊗ ∣0⟩ ⊗ (φ a b)) × (/ √ 2 * / 2  .* ∣0⟩ ⊗ ∣0⟩  ⊗ ∣0⟩ ⊗ (φ a b))†.
Proof.
intros. unfold φ,super. 
solve_matrix.
Qed. 

Lemma Dss1 :  forall (a b : C),
super (I 2 ⊗ I 2 ⊗ I 2 ⊗ σz) (super (M0 ⊗ M0 ⊗ M1 ⊗ I 2) (super (I 2 ⊗ hadamard ⊗ hadamard ⊗ I 2) (super (XC ⊗ I 2 ⊗ I 2) ((φ a b ⊗ GHZ) × (φ a b⊗ GHZ)†)))) = (/ √ 2 * / 2  .* ∣0⟩ ⊗ ∣0⟩  ⊗ ∣1⟩ ⊗ (φ a b)) × (/ √ 2 * / 2  .* ∣0⟩ ⊗ ∣0⟩  ⊗ ∣1⟩ ⊗ (φ a b))†.
Proof.
intros. unfold φ,super.
solve_matrix.
Qed.

Lemma Dss2 :  forall (a b : C),
super (I 2 ⊗ I 2 ⊗ I 2 ⊗ σz) (super (M0 ⊗ M1 ⊗ M0 ⊗ I 2) (super (I 2 ⊗ hadamard ⊗ hadamard ⊗ I 2) (super (XC ⊗ I 2 ⊗ I 2) ((φ a b ⊗ GHZ) × (φ a b⊗ GHZ)†)))) = (/ √ 2 * / 2  .* ∣0⟩ ⊗ ∣1⟩  ⊗ ∣0⟩ ⊗ (φ a b)) × (/ √ 2 * / 2  .* ∣0⟩ ⊗ ∣1⟩  ⊗ ∣0⟩ ⊗ (φ a b))†.
Proof.
intros. unfold φ,super. 
solve_matrix.
Qed.

Lemma Dss3 :  forall (a b : C),
super (I 2 ⊗ I 2 ⊗ I 2 ⊗ σz) (super (I 2 ⊗ I 2 ⊗ I 2 ⊗ σz) (super (M0 ⊗ M1 ⊗ M1 ⊗ I 2) (super (I 2 ⊗ hadamard ⊗ hadamard ⊗ I 2) (super (XC ⊗ I 2 ⊗ I 2) ((φ a b ⊗ GHZ) × (φ a b⊗ GHZ)†))))) = (/ √ 2 * / 2  .* ∣0⟩ ⊗ ∣1⟩  ⊗ ∣1⟩ ⊗ (φ a b)) × (/ √ 2 * / 2  .* ∣0⟩ ⊗ ∣1⟩  ⊗ ∣1⟩ ⊗ (φ a b))†.
Proof.
intros. unfold φ,super. 
solve_matrix.
Qed.

Lemma Dss4 :  forall (a b : C),
super (I 2 ⊗ I 2 ⊗ I 2 ⊗ σx) (super (M1 ⊗ M0 ⊗ M0 ⊗ I 2) (super (I 2 ⊗ hadamard ⊗ hadamard ⊗ I 2) (super (XC ⊗ I 2 ⊗ I 2) ((φ a b ⊗ GHZ) × (φ a b⊗ GHZ)†)))) = (/ √ 2 * / 2  .* ∣1⟩ ⊗ ∣0⟩  ⊗ ∣0⟩ ⊗ (φ a b)) × (/ √ 2 * / 2  .* ∣1⟩ ⊗ ∣0⟩  ⊗ ∣0⟩ ⊗ (φ a b))†.
Proof.
intros. unfold φ,super.
solve_matrix.
Qed.

Lemma Dss5 :  forall (a b : C),
super (I 2 ⊗ I 2 ⊗ I 2 ⊗ σx) (super (I 2 ⊗ I 2 ⊗ I 2 ⊗ σz) (super (M1 ⊗ M0 ⊗ M1 ⊗ I 2) (super (I 2 ⊗ hadamard ⊗ hadamard ⊗ I 2) (super (XC ⊗ I 2 ⊗ I 2) ((φ a b ⊗ GHZ) × (φ a b⊗ GHZ)†))))) = (/ √ 2 * / 2  .* ∣1⟩ ⊗ ∣0⟩  ⊗ ∣1⟩ ⊗ (φ a b)) × (/ √ 2 * / 2  .* ∣1⟩ ⊗ ∣0⟩  ⊗ ∣1⟩ ⊗ (φ a b))†.
Proof.
intros. unfold φ,super. 
solve_matrix.
Qed.

Lemma Dss6 :  forall (a b : C),
super (I 2 ⊗ I 2 ⊗ I 2 ⊗ σx) (super (I 2 ⊗ I 2 ⊗ I 2 ⊗ σz) (super (M1 ⊗ M1 ⊗ M0 ⊗ I 2) (super (I 2 ⊗ hadamard ⊗ hadamard ⊗ I 2) (super (XC ⊗ I 2 ⊗ I 2) ((φ a b ⊗ GHZ) × (φ a b⊗ GHZ)†))))) = (/ √ 2 * / 2  .* ∣1⟩ ⊗ ∣1⟩  ⊗ ∣0⟩ ⊗ (φ a b)) × (/ √ 2 * / 2  .* ∣1⟩ ⊗ ∣1⟩  ⊗ ∣0⟩ ⊗ (φ a b))†.
Proof.
intros. unfold φ,super. 
solve_matrix.
Qed.


Lemma Dss7 :  forall (a b : C),
super (I 2 ⊗ I 2 ⊗ I 2 ⊗ σx) (super (I 2 ⊗ I 2 ⊗ I 2 ⊗ σz) (super (I 2 ⊗ I 2 ⊗ I 2 ⊗ σz) (super (M1 ⊗ M1 ⊗ M1 ⊗ I 2) (super (I 2 ⊗ hadamard ⊗ hadamard ⊗ I 2) (super (XC ⊗ I 2 ⊗ I 2) ((φ a b ⊗ GHZ) × (φ a b⊗ GHZ)†)))))) = (/ √ 2 * / 2  .* ∣1⟩ ⊗ ∣1⟩  ⊗ ∣1⟩ ⊗ (φ a b)) × (/ √ 2 * / 2  .* ∣1⟩ ⊗ ∣1⟩  ⊗ ∣1⟩ ⊗ (φ a b))†.
Proof.
intros. unfold φ,super. 
solve_matrix.
Qed.

