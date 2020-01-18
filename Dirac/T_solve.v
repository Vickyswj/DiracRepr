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

Definition bell00 : Vector 4 := 
  fun x y => match x, y with 
          | 0, 0 => /√2
          | 3, 0 => /√2
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


(* One-time *)

Lemma tele0 : (M0 ⊗ M0 ⊗ I 2) × (hadamard ⊗ I 2 ⊗ I 2) × (cnot ⊗ I 2) × (∣+⟩ ⊗ bell00) = / 2  .* (∣0⟩ ⊗ ∣0⟩ ⊗ ∣+⟩).
Proof.
unfold bell00.
solve_matrix.
Qed.

Lemma tele1 : (I 2 ⊗ I 2 ⊗ σx) × (M0 ⊗ M1 ⊗ I 2) × (hadamard ⊗ I 2 ⊗ I 2) × (cnot ⊗ I 2) × (∣+⟩ ⊗ bell00) = / 2  .* (∣0⟩ ⊗ ∣1⟩ ⊗ ∣+⟩).
Proof.
unfold bell00.
solve_matrix.
Qed.

Lemma tele2 :  (I 2 ⊗ I 2 ⊗ σz) × (M1 ⊗ M0 ⊗ I 2) × (hadamard ⊗ I 2 ⊗ I 2) × (cnot ⊗ I 2) × (∣+⟩ ⊗ bell00) = / 2  .* (∣1⟩ ⊗ ∣0⟩ ⊗ ∣+⟩).
Proof.
unfold bell00.
solve_matrix.
Qed.

Lemma tele3 : (I 2 ⊗ I 2 ⊗ σz) × (I 2 ⊗ I 2 ⊗ σx) × (M1 ⊗ M1 ⊗ I 2) × (hadamard ⊗ I 2 ⊗ I 2) × (cnot ⊗ I 2) × (∣+⟩ ⊗ bell00) = / 2  .* (∣1⟩ ⊗ ∣1⟩ ⊗ ∣+⟩).
Proof.
unfold bell00.
solve_matrix.
Qed.

Lemma Dtele0 : super (M0 ⊗ M0 ⊗ I 2) (super (hadamard ⊗ I 2 ⊗ I 2) (super (cnot ⊗ I 2) ((∣+⟩ ⊗ bell00) × (∣+⟩ ⊗ bell00)†))) = (/ 2  .* (∣0⟩ ⊗ ∣0⟩ ⊗ ∣+⟩)) × (/ 2  .* (∣0⟩ ⊗ ∣0⟩ ⊗ ∣+⟩))†.
Proof.
unfold bell00,super.
solve_matrix.
Qed.

Lemma Dtele1 : super (I 2 ⊗ I 2 ⊗ σx) (super (M0 ⊗ M1 ⊗ I 2) (super (hadamard ⊗ I 2 ⊗ I 2) (super (cnot ⊗ I 2) ((∣+⟩ ⊗ bell00) × (∣+⟩ ⊗ bell00)†)))) = (/ 2  .* (∣0⟩ ⊗ ∣1⟩ ⊗ ∣+⟩)) × (/ 2  .* (∣0⟩ ⊗ ∣1⟩ ⊗ ∣+⟩))†.
Proof.
unfold bell00,super.
solve_matrix.
Qed.

Lemma Dtele2 : super (I 2 ⊗ I 2 ⊗ σz) (super (M1 ⊗ M0 ⊗ I 2) (super (hadamard ⊗ I 2 ⊗ I 2) (super (cnot ⊗ I 2) ((∣+⟩ ⊗ bell00) × (∣+⟩ ⊗ bell00)†)))) = (/ 2  .* (∣1⟩ ⊗ ∣0⟩ ⊗ ∣+⟩)) × (/ 2  .* (∣1⟩ ⊗ ∣0⟩ ⊗ ∣+⟩))†.
Proof.
unfold bell00,super.
solve_matrix.
Qed.

Lemma Dtele3 : super (I 2 ⊗ I 2 ⊗ σz) (super (I 2 ⊗ I 2 ⊗ σx) (super (M1 ⊗ M1 ⊗ I 2) (super (hadamard ⊗ I 2 ⊗ I 2) (super (cnot ⊗ I 2) ((∣+⟩ ⊗ bell00) × (∣+⟩ ⊗ bell00)†))))) = (/ 2  .* (∣1⟩ ⊗ ∣1⟩ ⊗ ∣+⟩)) × (/ 2  .* (∣1⟩ ⊗ ∣1⟩ ⊗ ∣+⟩))†.
Proof.
unfold bell00,super.
solve_matrix.
Qed.



Lemma e1 : forall a:C,/ √ 2 * (a * / √ 2) = / 2 * a.
Proof.
intros.
rewrite Cmult_comm.
rewrite <- Cmult_assoc.
autorewrite with C_db.
rewrite Cmult_comm. auto.
Qed.
Lemma Cconj_inv2 :  (/ 2)^* = / 2.         Proof. lca. Qed.
Lemma e2 : forall a:C, ((a * / √ 2) ^* * / √ 2) =   (/ 2 * a) ^*.
Proof.
intros.
rewrite Cconj_mult_distr,Cconj_rad2.
rewrite Cconj_mult_distr,Cconj_inv2.
rewrite <- Cmult_assoc.
autorewrite with C_db.
rewrite Cmult_comm. auto.
Qed.
Lemma Ceq4 :forall a b: C, / √ 2 * (a * / √ 2) * ((b * / √ 2) ^* * / √ 2) = / 2 * a * (/ 2 * b) ^*.
Proof.
intros.
rewrite e1,e2. auto.
Qed.
Hint Rewrite Ceq4: C_db.


(* parameterize *)

Definition φ (a b : C) : Vector 2 := a .* ∣0⟩ .+ b .* ∣1⟩.
Lemma Dtele0' :  forall (a b : C),
super (M0 ⊗ M0 ⊗ I 2) (super (hadamard ⊗ I 2 ⊗ I 2) (super (cnot ⊗ I 2) ((φ a b⊗ bell00) × (φ a b⊗ bell00)†))) = (/ 2  .* ∣0⟩ ⊗ ∣0⟩ ⊗ (φ a b)) × (/ 2  .* ∣0⟩ ⊗ ∣0⟩ ⊗ (φ a b))† .
Proof.
intros. unfold bell00,φ,super.
solve_matrix.
Qed.

Lemma Dtele1' :  forall (a b : C),
super (I 2 ⊗ I 2 ⊗ σx) (super (M0 ⊗ M1 ⊗ I 2) (super (hadamard ⊗ I 2 ⊗ I 2) (super (cnot ⊗ I 2)  ((φ a b⊗ bell00) × (φ a b⊗ bell00)†)))) = (/ 2  .* ∣0⟩ ⊗ ∣1⟩ ⊗ (φ a b)) × (/ 2  .* ∣0⟩ ⊗ ∣1⟩ ⊗ (φ a b))† .
Proof.
intros. unfold bell00,φ,super.
solve_matrix.
Qed.

Lemma Dtele2' :  forall (a b : C),
super (I 2 ⊗ I 2 ⊗ σz) (super (M1 ⊗ M0 ⊗ I 2) (super (hadamard ⊗ I 2 ⊗ I 2) (super (cnot ⊗ I 2)  ((φ a b⊗ bell00) × (φ a b⊗ bell00)†)))) = (/ 2  .* ∣1⟩ ⊗ ∣0⟩ ⊗ (φ a b)) × (/ 2  .* ∣1⟩ ⊗ ∣0⟩ ⊗ (φ a b))† .
Proof.
intros. unfold bell00,φ,super.
solve_matrix.
Qed.

Lemma Dtele3' :  forall (a b : C),
super (I 2 ⊗ I 2 ⊗ σz) (super (I 2 ⊗ I 2 ⊗ σx) (super (M1 ⊗ M1 ⊗ I 2) (super (hadamard ⊗ I 2 ⊗ I 2) (super (cnot ⊗ I 2)  ((φ a b⊗ bell00) × (φ a b⊗ bell00)†))))) = (/ 2  .* ∣1⟩ ⊗ ∣1⟩ ⊗ (φ a b)) × (/ 2  .* ∣1⟩ ⊗ ∣1⟩ ⊗ (φ a b))† .
Proof.
intros. unfold bell00,φ,super.
solve_matrix.
Qed.
