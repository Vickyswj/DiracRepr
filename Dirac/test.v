Require Export Quantum.

Definition ha : Matrix 2 2 := 
  (fun x y => match x, y with
          | 0, 0 => (1 / √2)
          | 0, 1 => (1 / √2)
          | 1, 0 => (1 / √2)
          | 1, 1 => -(1 / √2)
          | _, _ => 0
          end).

Lemma H_ket0_3 : (ha ⊗ ha ⊗ ha) × (ha ⊗ ha ⊗ ha) × (∣0,0,0⟩) = (∣0,0,0⟩).
Proof.
(* solve_matrix. *)
assoc_least.
reduce_matrix.
reduce_matrix.
crunch_matrix;
unfold Nat.ltb; simpl; try rewrite andb_false_r; 
autorewrite with C_db; repeat group_radicals; try lca.
Qed.



(*
Lemma H_ket0_2 : (hadamard ⊗ hadamard) × (∣0⟩ ⊗ ∣0⟩) = (∣+⟩ ⊗ ∣+⟩) .
Proof.
                      simpl.
                      unfold list2D_to_matrix.
                      autounfold with U_db.
                      prep_matrix_equality.
                      simpl.
                      destruct_m_eq';
                      simpl;
                      Csimpl; (* basic rewrites only *) 
                      try reflexivity;
                      try solve_out_of_bounds.
Qed.

Lemma H_ket0_3 : (hadamard ⊗ hadamard) × (hadamard ⊗ hadamard) = I 2 ⊗ I 2.
Proof.
                      simpl.
                      unfold list2D_to_matrix.
                      autounfold with U_db.
                      prep_matrix_equality.
                      simpl.
                      destruct_m_eq';
                      simpl;
                      Csimpl; (* basic rewrites only *) 
                      try reflexivity;
                      try solve_out_of_bounds.
Qed.

Lemma H_ket0_3 : (hadamard ⊗ hadamard ⊗ hadamard) × (hadamard ⊗ hadamard ⊗ hadamard) = I 2 ⊗ I 2 ⊗ I 2.
Proof.
crunch_matrix.
assoc_least.
reduce_matrix.
reduce_matrix.
crunch_matrix.

                     unfold Nat.ltb; simpl; try rewrite andb_false_r; 
                     (* try to solve complex equalities *)
                     autorewrite with C_db; repeat group_radicals; try lca.
unfold Nat.ltb; simpl; try rewrite andb_false_r; 
                     (* try to solve complex equalities *)
                     autorewrite with C_db; repeat group_radicals; try lca.
unfold Nat.ltb; simpl; try rewrite andb_false_r; 
                     (* try to solve complex equalities *)
                     autorewrite with C_db; repeat group_radicals; try lca.
unfold Nat.ltb; simpl; try rewrite andb_false_r; 
                     (* try to solve complex equalities *)
                     autorewrite with C_db; repeat group_radicals; try lca.

                     repeat reduce_matrix. try crunch_matrix;
                     (* handle out-of-bounds *)
                     unfold Nat.ltb; simpl; try rewrite andb_false_r; 
                     (* try to solve complex equalities *)
                     autorewrite with C_db; repeat group_radicals; try lca.
Qed.


Lemma H_ket0_3 : ((hadamard ⊗ hadamard) ⊗ hadamard) × ((∣0⟩ ⊗ ∣0⟩) ⊗ ∣0⟩) =  ((∣+⟩ ⊗ ∣+⟩) ⊗ ∣+⟩) .
Proof.
                      simpl.
                      unfold list2D_to_matrix.
                      autounfold with U_db.
                      prep_matrix_equality.
                      simpl.
                      destruct_m_eq'.
                      simpl.
                      Csimpl. (* basic rewrites only *) 
                      try reflexivity.
                      try solve_out_of_bounds.
try solve_out_of_bounds.


                     (* handle out-of-bounds *)
                     unfold Nat.ltb; simpl; try rewrite andb_false_r; 
                     (* try to solve complex equalities *)
                     autorewrite with C_db; repeat group_radicals; try lca.

Qed.

Lemma H_ket0_3 : (hadamard ⊗ hadamard ⊗ hadamard) × (hadamard ⊗ hadamard ⊗ hadamard) × ∣0,0,0⟩ =  (I 8) × ∣0,0,0⟩ .
Proof.
assoc_least.
                     repeat reduce_matrix; try crunch_matrix;
                     (* handle out-of-bounds *)
                     unfold Nat.ltb; simpl; try rewrite andb_false_r; 
                     (* try to solve complex equalities *)
                     autorewrite with C_db; repeat group_radicals; try lca.
Qed.

Lemma H_ket0_3 : (hadamard ⊗ hadamard ⊗ hadamard)  ×  (hadamard ⊗ hadamard ⊗ hadamard) × ∣0,0,0⟩ =  (I 8) × ∣0,0,0⟩ .
Proof.
assoc_least.
                     repeat reduce_matrix; try crunch_matrix;
                     (* handle out-of-bounds *)
                     unfold Nat.ltb; simpl; try rewrite andb_false_r; 
                     (* try to solve complex equalities *)
                     autorewrite with C_db; repeat group_radicals; try lca.
Qed.

Lemma H_3 : (hadamard ⊗ hadamard)  ×  (hadamard ⊗ hadamard) × ∣0,0⟩ =  ∣0,0⟩.
Proof.
rewrite H_ket0_3.
solve_matrix.
Qed.






Lemma H_ket0_3 :  
 super ((hadamard ⊗ hadamard ⊗ hadamard)
×  (hadamard ⊗ hadamard ⊗ hadamard))  ((∣0,0,0⟩) × (∣0,0,0⟩)†) = ((∣0,0,0⟩) × (∣0,0,0⟩)†).
Proof.
unfold super.
assoc_least.
reduce_matrix.
reduce_matrix.
reduce_matrix.
reduce_matrix.
solve_matrix.


Lemma H_ket0_3 : super  (hadamard ⊗ hadamard ⊗ hadamard)
 ((∣0,0,0⟩) × (∣0,0,0⟩)†) = ((∣+⟩ ⊗ ∣+⟩ ⊗ ∣+⟩) × (∣+⟩ ⊗ ∣+⟩ ⊗ ∣+⟩)†).
Proof.
unfold super.
assoc_least

assoc_least.
reduce_matrix.
reduce_matrix.
reduce_matrix.
reduce_matrix.



                       repeat match goal with 
                              | [ |- context[?c :: _ ]] => cbv [c]; clear c
                              end.
try crunch_matrix;
                     (* handle out-of-bounds *)
                     unfold Nat.ltb; simpl; try rewrite andb_false_r; 
                     (* try to solve complex equalities *)
                     autorewrite with C_db; repeat group_radicals; try lca.



                       end;
                       repeat match goal with 
                              | [ |- context[?c :: _ ]] => cbv [c]; clear c
                              end.

  match M with 
  | ?A .+ ?B     => compound A; reduce_aux A
  | ?A .+ ?B     => compound B; reduce_aux B
  | ?A × ?B      => compound A; reduce_aux A
  | ?A × ?B      => compound B; reduce_aux B
  | @Mmult ?m ?n ?o ?A ?B      => let M' := evar_matrix m o in
                                 replace M with M';
                                 [| crunch_matrix ] 
  | @Mplus ?m ?n ?A ?B         => let M' := evar_matrix m n in
                                 replace M with M';
                                 [| crunch_matrix ] 
  end.

                     repeat reduce_matrix; try crunch_matrix;
                     (* handle out-of-bounds *)
                     unfold Nat.ltb; simpl; try rewrite andb_false_r; 
                     (* try to solve complex equalities *)
                     autorewrite with C_db; repeat group_radicals; try lca.
Qed.
*)