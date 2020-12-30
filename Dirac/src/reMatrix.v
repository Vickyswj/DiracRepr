Require Export reComplex.
Require Export Matrix.

Ltac distribute_adjoint':=
  repeat rewrite ?Mplus_adjoint, ?Mmult_adjoint, ? Mscale_adj, ?zero_adjoint_eq, ?id_adjoint_eq, ?adjoint_involutive.

Ltac solve_matrix' := distribute_adjoint';assoc_least;
                     repeat reduce_matrix; try crunch_matrix;
                     (* handle out-of-bounds *)
                     unfold Nat.ltb; simpl; try rewrite andb_false_r; 
                     (* try to solve complex equalities *)
                     autorewrite with C_db; repeat group_radicals; try lca.