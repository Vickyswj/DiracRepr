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
super ((M0 ⊗ M0 ⊗ M0 ⊗ I 2) × (I 2 ⊗ hadamard ⊗ hadamard ⊗ I 2) × (XC ⊗ I 2 ⊗ I 2)) ((φ a b ⊗ GHZ) × (φ a b⊗ GHZ)†) = (/ √ 2 * / 2  .* ∣0⟩ ⊗ ∣0⟩  ⊗ ∣0⟩ ⊗ (φ a b)) × (/ √ 2 * / 2  .* ∣0⟩ ⊗ ∣0⟩  ⊗ ∣0⟩ ⊗ (φ a b))†.
Proof.
intros. unfold φ,super. 
Time solve_matrix.
Qed. 

Lemma Dss1 :  forall (a b : C),
super ((I 2 ⊗ I 2 ⊗ I 2 ⊗ σz) × (M0 ⊗ M0 ⊗ M1 ⊗ I 2) × (I 2 ⊗ hadamard ⊗ hadamard ⊗ I 2) × (XC ⊗ I 2 ⊗ I 2)) ((φ a b ⊗ GHZ) × (φ a b⊗ GHZ)†) = (/ √ 2 * / 2  .* ∣0⟩ ⊗ ∣0⟩  ⊗ ∣1⟩ ⊗ (φ a b)) × (/ √ 2 * / 2  .* ∣0⟩ ⊗ ∣0⟩  ⊗ ∣1⟩ ⊗ (φ a b))†.
Proof.
intros. unfold φ,super.
Time solve_matrix.
Qed.

Lemma Dss2 :  forall (a b : C),
super ((I 2 ⊗ I 2 ⊗ I 2 ⊗ σz) × (M0 ⊗ M1 ⊗ M0 ⊗ I 2) × (I 2 ⊗ hadamard ⊗ hadamard ⊗ I 2) × (XC ⊗ I 2 ⊗ I 2)) ((φ a b ⊗ GHZ) × (φ a b⊗ GHZ)†) = (/ √ 2 * / 2  .* ∣0⟩ ⊗ ∣1⟩  ⊗ ∣0⟩ ⊗ (φ a b)) × (/ √ 2 * / 2  .* ∣0⟩ ⊗ ∣1⟩  ⊗ ∣0⟩ ⊗ (φ a b))†.
Proof.
intros. unfold φ,super. 
Time solve_matrix.
Qed.

Lemma Dss3 :  forall (a b : C),
super ((I 2 ⊗ I 2 ⊗ I 2 ⊗ σz) × (I 2 ⊗ I 2 ⊗ I 2 ⊗ σz) × (M0 ⊗ M1 ⊗ M1 ⊗ I 2) × (I 2 ⊗ hadamard ⊗ hadamard ⊗ I 2) × (XC ⊗ I 2 ⊗ I 2)) ((φ a b ⊗ GHZ) × (φ a b⊗ GHZ)†) = (/ √ 2 * / 2  .* ∣0⟩ ⊗ ∣1⟩  ⊗ ∣1⟩ ⊗ (φ a b)) × (/ √ 2 * / 2  .* ∣0⟩ ⊗ ∣1⟩  ⊗ ∣1⟩ ⊗ (φ a b))†.
Proof.
intros. unfold φ,super. 
Time solve_matrix.
Qed.

Lemma Dss4 :  forall (a b : C),
super ((I 2 ⊗ I 2 ⊗ I 2 ⊗ σx) × (M1 ⊗ M0 ⊗ M0 ⊗ I 2) × (I 2 ⊗ hadamard ⊗ hadamard ⊗ I 2) × (XC ⊗ I 2 ⊗ I 2)) ((φ a b ⊗ GHZ) × (φ a b⊗ GHZ)†) = (/ √ 2 * / 2  .* ∣1⟩ ⊗ ∣0⟩  ⊗ ∣0⟩ ⊗ (φ a b)) × (/ √ 2 * / 2  .* ∣1⟩ ⊗ ∣0⟩  ⊗ ∣0⟩ ⊗ (φ a b))†.
Proof.
intros. unfold φ,super.
Time solve_matrix.
Qed.

Lemma Dss5 :  forall (a b : C),
super ((I 2 ⊗ I 2 ⊗ I 2 ⊗ σx) × (I 2 ⊗ I 2 ⊗ I 2 ⊗ σz) × (M1 ⊗ M0 ⊗ M1 ⊗ I 2) × (I 2 ⊗ hadamard ⊗ hadamard ⊗ I 2) × (XC ⊗ I 2 ⊗ I 2)) ((φ a b ⊗ GHZ) × (φ a b⊗ GHZ)†) = (/ √ 2 * / 2  .* ∣1⟩ ⊗ ∣0⟩  ⊗ ∣1⟩ ⊗ (φ a b)) × (/ √ 2 * / 2  .* ∣1⟩ ⊗ ∣0⟩  ⊗ ∣1⟩ ⊗ (φ a b))†.
Proof.
intros. unfold φ,super. 
Time solve_matrix.
Qed.

Lemma Dss6 :  forall (a b : C),
super ((I 2 ⊗ I 2 ⊗ I 2 ⊗ σx) × (I 2 ⊗ I 2 ⊗ I 2 ⊗ σz) × (M1 ⊗ M1 ⊗ M0 ⊗ I 2) × (I 2 ⊗ hadamard ⊗ hadamard ⊗ I 2) × (XC ⊗ I 2 ⊗ I 2)) ((φ a b ⊗ GHZ) × (φ a b⊗ GHZ)†) = (/ √ 2 * / 2  .* ∣1⟩ ⊗ ∣1⟩  ⊗ ∣0⟩ ⊗ (φ a b)) × (/ √ 2 * / 2  .* ∣1⟩ ⊗ ∣1⟩  ⊗ ∣0⟩ ⊗ (φ a b))†.
Proof.
intros. unfold φ,super. 
Time solve_matrix.
Qed.

Lemma Dss7 :  forall (a b : C),
super ((I 2 ⊗ I 2 ⊗ I 2 ⊗ σx) × (I 2 ⊗ I 2 ⊗ I 2 ⊗ σz) × (I 2 ⊗ I 2 ⊗ I 2 ⊗ σz) × (M1 ⊗ M1 ⊗ M1 ⊗ I 2) × (I 2 ⊗ hadamard ⊗ hadamard ⊗ I 2)) × (XC ⊗ I 2 ⊗ I 2) ((φ a b ⊗ GHZ) × (φ a b⊗ GHZ)†) = (/ √ 2 * / 2  .* ∣1⟩ ⊗ ∣1⟩  ⊗ ∣1⟩ ⊗ (φ a b)) × (/ √ 2 * / 2  .* ∣1⟩ ⊗ ∣1⟩  ⊗ ∣1⟩ ⊗ (φ a b))†.
Proof.
intros. unfold φ,super. 
Time solve_matrix.
Qed.

(* 
Finished transaction in 185.184 secs (178.5u,0.734s) (successful) 
Finished transaction in 222.828 secs (216.687u,0.687s) (successful)
Finished transaction in 230.579 secs (220.25u,1.14s) (successful)
Finished transaction in 289.962 secs (273.14u,2.75s) (successful)
Finished transaction in 252.799 secs (220.421u,10.656s) (successful)
Finished transaction in 313.513 secs (282.296u,11.984s) (successful)
Finished transaction in 313.564 secs (272.484u,13.671s) (successful)
Finished transaction in 389.349 secs (331.75u,19.39s) (successful) *)
