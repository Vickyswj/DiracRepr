Require Export M_notWF.

Definition qubit0 : Vector 2 := 
  fun x y => match x, y with 
          | 0, 0 => C1
          | 1, 0 => C0
          | _, _ => C0
          end.
Definition qubit1 : Vector 2 := 
  fun x y => match x, y with 
          | 0, 0 => C0
          | 1, 0 => C1
          | _, _ => C0
          end.

Notation "∣0⟩" := qubit0.
Notation "∣1⟩" := qubit1.
Notation "⟨0∣" := qubit0†.
Notation "⟨1∣" := qubit1†.
Notation "∣0⟩⟨0∣" := (∣0⟩×⟨0∣).
Notation "∣1⟩⟨1∣" := (∣1⟩×⟨1∣).
Notation "∣1⟩⟨0∣" := (∣1⟩×⟨0∣).
Notation "∣0⟩⟨1∣" := (∣0⟩×⟨1∣).

Definition ket0 := ∣0⟩.
Definition ket1 := ∣1⟩.
Definition bra0 := ⟨0∣.
Definition bra1 := ⟨1∣.
Definition ketp := /√2 .* ∣0⟩ .+ /√2 .* ∣1⟩.
Definition brap := /√2 .* ⟨0∣ .+ /√2 .* ⟨1∣.
Definition ketn := /√2 .* ∣0⟩ .+ (-/√2) .* ∣1⟩.
Definition bran := /√2 .* ⟨0∣ .+ (-/√2) .* ⟨1∣.

Definition bell00 := /√2 .* (∣0⟩ ⊗ ∣0⟩) .+ /√2 .* (∣1⟩ ⊗ ∣1⟩).
Definition bell01 := /√2 .* (∣0⟩ ⊗ ∣1⟩) .+ /√2 .* (∣1⟩ ⊗ ∣0⟩).
Definition bell10 := /√2 .* (∣0⟩ ⊗ ∣0⟩) .+ (-/√2) .* (∣1⟩ ⊗ ∣1⟩).
Definition bell11 := /√2 .* (∣0⟩ ⊗ ∣1⟩) .+ (-/√2) .* (∣1⟩ ⊗ ∣0⟩).

Fixpoint ket0_n (n : nat) : Matrix (2^n) 1 :=
match n with
| 0 => I 1
| 1 => ket0
| S n' => ket0_n n' ⊗ ket0
end.

Notation "∣+⟩" := ketp.
Notation "∣-⟩" := ketn.
Notation "⟨+∣" := brap.
Notation "⟨-∣" := bran.

Hint Unfold qubit0 qubit1 : U_db.
Hint Unfold ketp ketn brap bran ket0_n bell00 bell01 bell10 bell11 : S_db.

Ltac Orthogonalization :=
  autounfold with S_db;
  autounfold with U_db;
  prep_matrix_equality;
  destruct_m_eq; autorewrite with C_db;auto;
  bdestruct_all;
  try rewrite andb_false_r;
  try lca.

Lemma Mmult_bra0_ket0 : ⟨0∣ × ∣0⟩ = 1 .* I 1.
Proof. Orthogonalization. Qed.
(*  autounfold with U_db.
  prep_matrix_equality.
  destruct_m_eq; autorewrite with C_db;auto.
  bdestruct_all;
   rewrite andb_false_r; lca.*)
(*  solve_matrix. Qed. *)
Lemma Mmult_bra0_ket1 : ⟨0∣ × ∣1⟩ = 0 .* I 1. (* /Zero *)
Proof. Orthogonalization. Qed.
Lemma Mmult_bra1_ket0 : ⟨1∣ × ∣0⟩ = 0 .* I 1.
Proof. Orthogonalization. Qed.
Lemma Mmult_bra1_ket1 : ⟨1∣ × ∣1⟩ = 1 .* I 1.
Proof. Orthogonalization. Qed.

Lemma Mmult_brap_ketp : ⟨+∣ × ∣+⟩ = 1 .* I 1.
Proof. Orthogonalization. Qed.
Lemma Mmult_brap_ketn : ⟨+∣ × ∣-⟩ = 0 .* I 1. (* /Zero *)
Proof. Orthogonalization. Qed.
Lemma Mmult_bran_ketp : ⟨-∣ × ∣+⟩ = 0 .* I 1.
Proof. Orthogonalization. Qed.
Lemma Mmult_bran_ketn : ⟨-∣ × ∣-⟩ = 1 .* I 1.
Proof. Orthogonalization. Qed.


Definition B0 := ∣0⟩ × ⟨0∣.
Definition B1 := ∣0⟩ × ⟨1∣.
Definition B2 := ∣1⟩ × ⟨0∣.
Definition B3 := ∣1⟩ × ⟨1∣.

Hint Unfold B0 B1 B2 B3 : B_db.

Definition σX := B1 .+ B2.
Definition σX' := ∣0⟩ × ⟨1∣ .+ ∣1⟩ × ⟨0∣.

Definition σY := - Ci .* B1 .+ Ci .* B2.
Definition σZ := B0 .+ (-1) .* B3.
Definition I_2 := B0 .+ B3.

Definition H := /√2 .* B0 .+ /√2 .* B1  .+ /√2 .* B2 .+ (-/√2) .* B3.
Definition H' := /√2 .* ((∣0⟩ .+ ∣1⟩) × ⟨0∣ .+ (∣0⟩ .+  (-1) .* ∣1⟩) × ⟨1∣).

Fixpoint H_n (n : nat) : Matrix (2^n) (2^n):= 
  match n with
  | 0 => I 1
  | S n' => H_n n' ⊗ H
  end.


Definition CNOT :=  B0 ⊗ I_2 .+ B3 ⊗ σX.
Definition CNOT' := (∣0⟩ ⊗ ∣0⟩) × (⟨0∣ ⊗ ⟨0∣) .+ (∣0⟩ ⊗ ∣1⟩) × (⟨0∣ ⊗ ⟨1∣)
                               .+ (∣1⟩ ⊗ ∣0⟩) × (⟨1∣ ⊗ ⟨1∣) .+ (∣1⟩ ⊗ ∣1⟩) × (⟨1∣ ⊗ ⟨0∣).

Definition M0 := B0.
Definition M1 := B3.

Hint Unfold  σX σY σZ I_2 H M0 M1 CNOT : G_db.

Lemma Mmult_1_l : forall (m n : nat) (A : Matrix m n), I m × A = A.
Admitted.

Lemma Mmult_1_r : forall (m n : nat) (A : Matrix m n),  A × I n = A.
Admitted.

Ltac distrubute_plus:=
repeat rewrite ?Mmult_plus_distr_r, ?Mmult_plus_distr_l,?Mscale_plus_distr_r,?kron_plus_distr_r,?kron_plus_distr_l.

Ltac isolate_scale:=
repeat rewrite ?Mscale_mult_dist_l,?Mscale_mult_dist_r,?Mscale_kron_dist_r,?Mscale_kron_dist_l,?Mscale_assoc.

Ltac assoc_right:=
repeat rewrite ?Mmult_assoc, ?kron_assoc.

Ltac kron_mult:=
repeat rewrite <- kron_mixed_product.

Ltac mult_kron:=
repeat rewrite kron_mixed_product.

Inductive fake_eq {n m}: Matrix n m -> Matrix n m -> Prop :=
| fake_eq_intro: forall A B, A = B -> fake_eq A B.

Lemma mult_reduce1 : forall n A B x, fake_eq (@Mmult 1 n 1 A B) x -> @Mmult 1 n 1 A B = x.
Proof.
  intros.
  inversion H0; subst; auto.
Qed.

Lemma mult_reduce2 : forall n m A B C x, fake_eq (@Mmult 1 n 1 A B) x -> @Mmult 1 n m A (@Mmult n 1 m B C) = @Mmult 1 1 m x C.
Proof.
  intros.
  inversion H0; subst; auto.
  rewrite Mmult_assoc.
  auto.
Qed.

(* Hint Extern 1 (fake_eq (@Mmult _ _ _ _ _) _) => apply fake_eq_intro; apply Mmult_bra0_ket0: matrix_reduce.
Hint Extern 1 (fake_eq (@Mmult _ _ _ _ _) _) => apply fake_eq_intro; apply Mmult_bra0_ket1: matrix_reduce.
Hint Extern 1 (fake_eq (@Mmult _ _ _ _ _) _) => apply fake_eq_intro; apply Mmult_bra1_ket0: matrix_reduce.
Hint Extern 1 (fake_eq (@Mmult _ _ _ _ _) _) => apply fake_eq_intro; apply Mmult_bra1_ket1: matrix_reduce.


Ltac matrix_mult_reduce:=
match goal with
| |-context [ @Mmult 1 ?n 1 ?A ?B] =>
         match B with
        | @Mmult _ _ _ _ _ => fail 1
        | _ => erewrite (mult_reduce1 n A B); [| auto with matrix_reduce]
        end
| |-context [ @Mmult 1 ?n ?m ?A (@Mmult ?n 1 ?m ?B ?C)] => erewrite (mult_reduce2 n m A B C); [| auto with matrix_reduce]
end;
isolate_scale;
repeat rewrite ?Mmult_1_l, ?Mmult_1_r. *)

Ltac kron_0 :=
  match goal with
  | |- context  [@kron ?m1 ?n1 ?o1 ?p1 ?A (@Zero ?m2 ?n2)] =>
             change  (@kron m1 n1 o1 p1 A (@Zero m2 n2))  with
                           (@kron m1 n1 o1 p1 A (@Zero o1 p1));
             rewrite (@kron_0_r m1 n1 o1 p1 A)
  | |- context  [@kron ?m1 ?n1 ?o1 ?p1 (@Zero ?m2 ?n2) ?A] =>
             change  (@kron m1 n1 o1 p1 (@Zero m2 n2) A)  with
                           (@kron m1 n1 o1 p1 (@Zero m1 n1) A);
             rewrite (@kron_0_l  m1 n1 o1 p1 A)
  end.

Ltac Mmult_0 :=
  match goal with
  | |- context  [@Mmult ?m1 ?n1 ?o1 ?A (@Zero ?n2 ?o2)] =>
             change  (@Mmult m1 n1 o1 A (@Zero n2 o2))  with
                           (@Mmult m1 n1 o1 A (@Zero n1 o1));
             rewrite (@Mmult_0_r m1 n1 o1 A)
  | |- context  [@Mmult ?m1 ?n1 ?o1 ?p1 (@Zero ?m2 ?n2) ?A] =>
             change  (@Mmult m1 n1 o1 p1 (@Zero m2 n2) A)  with
                           (@Mmult m1 n1 o1 p1 (@Zero m1 n1) A);
             rewrite (@Mmult_0_l  m1 n1 o1 p1 A)
  end.

Ltac Mplus_0 :=
  match goal with
  | |- context  [@Mplus ?m1 ?n1 ?A (@Zero ?m2 ?n2)] =>
             change  (@Mplus m1 n1 A (@Zero m2 n2))  with
                           (@Mplus m1 n1 A (@Zero m1 n1));
             rewrite (@Mplus_0_r m1 n1 A)
  | |- context  [@Mplus ?m1 ?n1 (@Zero ?m2 ?n2) ?A] =>
             change  (@Mplus m1 n1 (@Zero m2 n2) A)  with
                           (@Mplus m1 n1 (@Zero m1 n1) A);
             rewrite (@Mplus_0_l  m1 n1 A)
  end.

Ltac scale_0 :=
  match goal with
  | |- context  [@scale ?m1 ?n1 ?r (@Zero ?m2 ?n2)] =>
             change  (@scale m1 n1 r (@Zero m2 n2))  with
                           (@scale m1 n1 r (@Zero m1 n1));
             rewrite (@Mscale_0_r m1 n1 r)
  end.

Ltac cancel_0 :=
 try kron_0; try Mmult_0; try Mplus_0; try scale_0.


Ltac reduce_scale:=
autorewrite with C_db;
repeat rewrite ?Mscale_0_l,?Mscale_1_l,?Mscale_1_r,  (**************************)
                          ?Mplus_0_l,?Mplus_0_r,
                          ?Cinv_sqrt2_sqrt;
repeat cancel_0;
auto.


Ltac mult_kron1 :=
  match goal with
  | |- context [@Mmult ?m1o1 ?n1p1 ?n2p2 (@kron ?m1 ?n1 ?o1 ?p1 ?A ?B) (@kron ?m2 ?n2 ?o2 ?p2 ?C ?D)] =>
             change (@Mmult m1o1 n1p1 n2p2 (@kron m1 n1 o1 p1 A B) (@kron m2 n2 o2 p2 C D)) with
                           (@Mmult (m1 * o1) (n1 * p1) (n2 * p2) (@kron m1 n1 o1 p1 A B) (@kron n1 n2 p1 p2 C D));
             rewrite (@kron_mixed_product m1 n1 n2 o1 p1 p2 A B C D)
  end.

Ltac mult_result_gen :=
  repeat mult_kron1;
  repeat rewrite ?Mmult_bra0_ket0, ?Mmult_bra0_ket1, ?Mmult_bra1_ket0, ?Mmult_bra1_ket1;  (* make it more extensible later.*)
  isolate_scale;
  repeat rewrite id_kron;
  apply fake_eq_intro; reflexivity.

Ltac matrix_mult_reduce :=
match goal with
| |-context [ @Mmult ?one1 ?n ?one2 ?A ?B] =>
         match B with
        | @Mmult _ _ _ _ _ => fail 1
        | _ => change (@Mmult one1 n one2 A B) with
                                (@Mmult 1 n 1 A B);
                   erewrite (mult_reduce1 n A B) by (mult_result_gen; fail 2 "mult_result_gen fail")
        end
| |-context [ @Mmult ?one1 ?n ?m ?A (@Mmult ?n ?one2 ?m ?B ?C)] =>
         change (@Mmult one1 n m A (@Mmult n one2 m B C)) with
                       (@Mmult 1 n m A (@Mmult n 1 m B C));
          erewrite (mult_reduce2 n m A B C) by (mult_result_gen; fail 2 "mult_result_gen fail")
end;
isolate_scale;
repeat rewrite ?Mmult_1_l, ?Mmult_1_r.

Ltac matrix_reduce :=
distrubute_plus;
isolate_scale;
kron_mult;
assoc_right;
repeat matrix_mult_reduce;
reduce_scale.

Lemma Mmult_bra0_ketp : ⟨0∣ × ∣+⟩ = / √ 2 .* I 1.
Proof. autounfold with S_db. matrix_reduce. Qed.
Lemma Mmult_bra0_ketn : ⟨0∣ × ∣-⟩ = / √ 2 .* I 1.
Proof. autounfold with S_db. matrix_reduce. Qed.
Lemma Mmult_bra1_ketp : ⟨1∣ × ∣+⟩ = / √ 2 .* I 1.
Proof. autounfold with S_db. matrix_reduce. Qed.
Lemma Mmult_bra1_ketn : ⟨1∣ × ∣-⟩ = - / √ 2 .* I 1.
Proof. autounfold with S_db. matrix_reduce. Qed.

Lemma Mmult_brap_ket0 : ⟨+∣ × ∣0⟩ = / √ 2 .* I 1.
Proof. autounfold with S_db. matrix_reduce. Qed.
Lemma Mmult_brap_ket1 : ⟨+∣ × ∣1⟩ = / √ 2 .* I 1.
Proof. autounfold with S_db. matrix_reduce. Qed.
Lemma Mmult_bran_ket0 : ⟨-∣ × ∣0⟩ = / √ 2 .* I 1.
Proof. autounfold with S_db. matrix_reduce. Qed.
Lemma Mmult_bran_ket1 : ⟨-∣ × ∣1⟩ = - / √ 2 .* I 1.
Proof. autounfold with S_db. matrix_reduce. Qed.


Lemma B00 : B0 × ∣0⟩ = ∣0⟩.
Proof.
autounfold with B_db.
matrix_reduce.
Qed.

Lemma B01 : B0 × ∣1⟩ = @Zero 2 1.
Proof.
autounfold with B_db.
matrix_reduce.
Qed.


Lemma B0pos : B0 × ∣+⟩ = / √ 2 .* ∣0⟩.
Proof.
autounfold with B_db S_db.
matrix_reduce.
Qed.


Lemma B0neg : B0 × ∣-⟩ = / √ 2 .* ∣0⟩.
Proof.
autounfold with B_db S_db.
matrix_reduce.
Qed.

Lemma B10 : B1 × ∣0⟩ =@Zero 2 1.
Proof.
autounfold with B_db.
matrix_reduce.
Qed.


Lemma B11 : B1 × ∣1⟩ = ∣0⟩.
Proof.
autounfold with B_db.
matrix_reduce.
Qed.


Lemma B1pos : B1 × ∣+⟩ = / √ 2 .* ∣0⟩.
Proof.
autounfold with B_db S_db.
matrix_reduce.
Qed.


Lemma B1neg : B1 × ∣-⟩ = - / √ 2 .* ∣0⟩.
Proof.
autounfold with B_db S_db.
matrix_reduce.
Qed.

Lemma B20 : B2 × ∣0⟩ = ∣1⟩.
Proof.
autounfold with B_db.
matrix_reduce.
Qed.


Lemma B21 : B2 × ∣1⟩ = @Zero 2 1.
Proof.
autounfold with B_db.
matrix_reduce.
Qed.


Lemma B2pos : B2 × ∣+⟩ = / √ 2 .* ∣1⟩.
Proof.
autounfold with B_db S_db.
matrix_reduce.
Qed.


Lemma B2neg : B2 × ∣-⟩ = / √ 2 .* ∣1⟩.
Proof.
autounfold with B_db S_db.
matrix_reduce.
Qed.

Lemma B30 : B3 × ∣0⟩ = @Zero 2 1.
Proof.
autounfold with B_db.
matrix_reduce.
Qed.


Lemma B31 : B3 × ∣1⟩ = ∣1⟩.
Proof.
autounfold with B_db.
matrix_reduce.
Qed.


Lemma B3pos : B3 × ∣+⟩ = / √ 2 .* ∣1⟩.
Proof.
autounfold with B_db S_db.
matrix_reduce.
Qed.


Lemma B3neg : B3 × ∣-⟩ = - / √ 2 .* ∣1⟩.
Proof.
autounfold with B_db S_db.
matrix_reduce.
Qed.

Hint Rewrite B00 B01 B0pos B0neg
                         B10 B11 B1pos B1neg
                         B20 B21 B2pos B2neg
                         B30 B31 B3pos B3neg : B_db.

Lemma I0 : I_2 × ∣0⟩ = ∣0⟩.
Proof.
autounfold with G_db B_db.
matrix_reduce.
Qed.

Lemma I1 : I_2 × ∣1⟩ = ∣1⟩.
Proof.
autounfold with G_db B_db.
matrix_reduce.
Qed.

Lemma Ipos : I_2 × ∣+⟩ = ∣+⟩.
Proof.
autounfold with G_db B_db S_db.
matrix_reduce.
Qed.

Lemma Ineg : I_2 × ∣-⟩ = ∣-⟩.
Proof.
autounfold with G_db B_db S_db.
matrix_reduce.
Qed.


Lemma σX0 : σX × ∣0⟩ = ∣1⟩.
Proof.
autounfold with G_db B_db.
matrix_reduce.
Qed.

Lemma σX1 : σX × ∣1⟩ = ∣0⟩.
Proof.
autounfold with G_db B_db.
matrix_reduce.
Qed.

Lemma σXpos : σX × ∣+⟩ = ∣+⟩.
Proof.
autounfold with G_db B_db S_db.
matrix_reduce.
Qed.

Lemma σXneg : σX × ∣-⟩ = -1 .* ∣-⟩.
Proof.
autounfold with G_db B_db S_db.
matrix_reduce.
Qed.


Lemma σZ0 : σZ × ∣0⟩ = ∣0⟩.
Proof.
autounfold with G_db B_db S_db.
matrix_reduce.
Qed.

Lemma σZ1 : σZ × ∣1⟩ = -1 .* ∣1⟩.
Proof.
autounfold with G_db B_db S_db.
matrix_reduce.
Qed.

Lemma σZpos : σZ × ∣+⟩ = ∣-⟩.
Proof.
autounfold with G_db B_db S_db.
matrix_reduce.
Qed.

Lemma σZneg : σZ × ∣-⟩ = ∣+⟩.
Proof.
autounfold with G_db B_db S_db.
matrix_reduce.
Qed.


Lemma σY0 : σY × ∣0⟩ = Ci .* ∣1⟩.
Proof.
autounfold with G_db B_db S_db.
matrix_reduce.
Qed.

Lemma σY1 : σY × ∣1⟩ = -Ci .* ∣0⟩.
Proof.
autounfold with G_db B_db S_db.
matrix_reduce.
Qed.


Lemma H0 : H × ∣0⟩ = ∣+⟩.
Proof.
autounfold with G_db B_db S_db.
matrix_reduce.
Qed.

Lemma H1 : H × ∣1⟩ = ∣-⟩.
Proof.
autounfold with G_db B_db S_db.
matrix_reduce.
Qed.

Lemma Hpos : H × ∣+⟩ = ∣0⟩.
Proof.
autounfold with G_db B_db S_db.
matrix_reduce.
rewrite Mplus_assoc.
repeat rewrite <- Mscale_plus_distr_l.
reduce_scale.
Qed.

Lemma Hneg : H × ∣-⟩ = ∣1⟩.
Proof.
autounfold with G_db B_db S_db.
matrix_reduce.
rewrite Mplus_assoc.
repeat rewrite <- Mscale_plus_distr_l.
reduce_scale.
Qed.

Hint Rewrite I0 I1 Ipos Ineg
                         σX0 σX1 σXpos σXneg
                         σZ0 σZ1 σZpos σZneg
                         σY0 σY1
                         H0 H1 Hpos Hneg : G_db.

Lemma CNOT00 : CNOT × (∣0⟩ ⊗ ∣0⟩) = ∣0⟩ ⊗ ∣0⟩.
Proof.
(* unfold CNOT.
distrubute_plus.
mult_kron.
autorewrite with B_db G_db.
matrix_reduce.
cancel_0.
auto. *)

autounfold with G_db B_db.
matrix_reduce.
Qed.

Lemma CNOT01 : CNOT × (∣0⟩ ⊗ ∣1⟩) = ∣0⟩ ⊗ ∣1⟩.
Proof.
(* unfold CNOT.
distrubute_plus.
mult_kron.
autorewrite with B_db G_db.
cancel_0.
auto. *)
repeat autounfold with G_db B_db.
matrix_reduce.
Qed.

Lemma CNOT10 : CNOT × (∣1⟩ ⊗ ∣0⟩) = ∣1⟩ ⊗ ∣1⟩.
Proof.
autounfold with G_db B_db.
matrix_reduce.
Qed.

Lemma CNOT11 : CNOT × (∣1⟩ ⊗ ∣1⟩) = ∣1⟩ ⊗ ∣0⟩.
Proof.
autounfold with G_db B_db.
matrix_reduce.
Qed.

Lemma CNOTp0 : CNOT × (∣+⟩ ⊗ ∣0⟩) = bell00.
Proof.
(* unfold CNOT.
autounfold with S_db.
distrubute_plus.
isolate_scale.
mult_kron.
autorewrite with B_db G_db.
repeat cancel_0.
auto. *)
autounfold with G_db B_db S_db.
matrix_reduce.
Qed.


Hint Rewrite CNOT00 CNOT01 CNOT10 CNOT11
                         CNOTp0 : G_db.

Ltac unfold_gate :=
autorewrite with B_db G_db;
isolate_scale.

Ltac gate_reduce :=
distrubute_plus;
isolate_scale;
assoc_right;
repeat mult_kron1;
repeat unfold_gate;
reduce_scale.

Definition state0 := ∣0⟩ ⊗ ∣0⟩.
Definition state1 := (H ⊗ I_2) × state0.
Definition state2 := CNOT × state1.

Lemma pre_bell00 : bell00 = state2.
Proof.
(* unfold state2,state1,state0.
repeat autounfold with G_db.
autounfold with S_db.
matrix_reduce. *)
unfold state2,state1,state0.
gate_reduce.
Qed.

Definition φ0 := ∣+⟩ ⊗ bell00.
Definition φ1 := (CNOT ⊗ I_2) × φ0.
Definition φ2 := (H ⊗ I_2 ⊗ I_2) × φ1.

Lemma step1 : φ1 = /2 .*  (∣0⟩ ⊗ ∣0⟩ ⊗ ∣0⟩) .+ /2 .*  (∣0⟩ ⊗ ∣1⟩ ⊗ ∣1⟩) .+ /2 .*  (∣1⟩ ⊗ ∣1⟩ ⊗ ∣0⟩) .+ /2 .*  (∣1⟩ ⊗ ∣0⟩ ⊗ ∣1⟩).
Proof.
unfold φ1,φ0.
unfold CNOT,bell00.
gate_reduce.
rewrite <- Mplus_assoc;auto.
Qed.

Lemma step2 : φ2 = / 2 .* (∣+⟩ ⊗ (∣0⟩ ⊗ ∣0⟩))  .+ / 2 .* (∣+⟩ ⊗ (∣1⟩ ⊗ ∣1⟩))
                                .+ / 2 .* (∣-⟩ ⊗ (∣1⟩ ⊗ ∣0⟩))  .+ / 2 .* (∣-⟩ ⊗ (∣0⟩ ⊗ ∣1⟩)) .
Proof.
unfold φ2,φ1,φ0.
unfold CNOT,bell00.
gate_reduce.
rewrite <- Mplus_assoc;auto.
Qed.

Lemma step2' :  / 2 .* (∣+⟩ ⊗ (∣0⟩ ⊗ ∣0⟩))  .+ / 2 .* (∣+⟩ ⊗ (∣1⟩ ⊗ ∣1⟩))
                                .+ / 2 .* (∣-⟩ ⊗ (∣1⟩ ⊗ ∣0⟩))  .+ / 2 .* (∣-⟩ ⊗ (∣0⟩ ⊗ ∣1⟩)) =

                            / 2 .* (∣0⟩ ⊗ ∣0⟩ ⊗ ∣+⟩)  .+ / 2 .*  ∣1⟩ ⊗ ∣1⟩ ⊗ (/√2 .* ∣1⟩ .+ -/√2 .* ∣0⟩)
                                .+ / 2 .*  ∣1⟩ ⊗ ∣0⟩ ⊗ (/√2 .* ∣0⟩ .+ -/√2 .* ∣1⟩) .+ / 2 .* ∣0⟩ ⊗ ∣1⟩ ⊗ (/√2 .* (∣1⟩ .+ ∣0⟩)).
Proof.
autounfold with S_db.
distrubute_plus.
isolate_scale.
Admitted.

Definition φ30 := (M0 ⊗ M0 ⊗ I_2) × φ2.
Definition φ31 := (M0 ⊗ M1 ⊗ I_2) × φ2.
Definition φ32 := (M1 ⊗ M0 ⊗ I_2) × φ2.
Definition φ33 := (M1 ⊗ M1 ⊗ I_2) × φ2.

Lemma step30 : φ30 = / 2  .* (∣0⟩ ⊗ ∣0⟩ ⊗ ∣+⟩).
Proof.
unfold φ30.
rewrite step2.
rewrite step2'.
unfold M0,M1.
gate_reduce.
Qed.

Lemma step31 : φ31 = / 2  .* (∣0⟩ ⊗ ∣1⟩) ⊗ (/√2 .* (∣1⟩ .+ ∣0⟩)).
Proof.
unfold φ31.
rewrite step2.
rewrite step2'.
unfold M0,M1.
gate_reduce.
Qed.

Lemma step32 : φ32 = / 2  .* (∣1⟩ ⊗ ∣0⟩) ⊗ (/√2 .* ∣0⟩ .+ -/√2 .* ∣1⟩).
Proof.
unfold φ32.
rewrite step2.
rewrite step2'.
unfold M0,M1.
gate_reduce.
Qed.

Lemma step33 : φ33 = / 2  .* (∣1⟩ ⊗ ∣1⟩) ⊗ (/√2 .* ∣1⟩ .+ -/√2 .* ∣0⟩).
Proof.
unfold φ33.
rewrite step2.
rewrite step2'.
unfold M0,M1.
gate_reduce.
Qed.


Definition φ40 := φ30.
Definition φ41 := (I_2 ⊗ I_2 ⊗ σX) × φ31.
Definition φ42 := (I_2 ⊗ I_2 ⊗ σZ) × φ32.

Lemma step40 : φ40 = / 2  .* (∣0⟩ ⊗ ∣0⟩ ⊗ ∣+⟩).
Proof.
unfold φ40.
rewrite step30.
auto.
Qed.

Lemma step41 : φ41 = / 2  .* (∣0⟩ ⊗ ∣1⟩ ⊗ ∣+⟩).
Proof.
unfold φ41.
rewrite step31.
autounfold with S_db.
gate_reduce.
rewrite Cmult_comm;auto.
Qed.

Lemma step42 : φ42 = / 2  .* (∣1⟩ ⊗ ∣0⟩ ⊗ ∣+⟩).
Proof.
unfold φ42.
rewrite step32.
autounfold with S_db.
gate_reduce.
rewrite Cmult_comm;auto.
Qed.

Definition φ43 := (I_2 ⊗ I_2 ⊗ σZ) × (I_2 ⊗ I_2 ⊗ σX) × φ33.
Lemma step43 : φ43 = / 2  .* (∣1⟩ ⊗ ∣1⟩) ⊗ ketp.
Proof.
unfold φ43.
rewrite step33.
autounfold with S_db.
gate_reduce.
Qed.

Definition φ431 := (I_2 ⊗ I_2 ⊗ σX) × φ33.
Lemma step431 : φ431 = / 2  .* (∣1⟩ ⊗ ∣1⟩) ⊗ (/√2 .* ∣0⟩ .+ -/ √ 2  .* ∣1⟩).
Proof.
unfold φ431.
rewrite step33.
autounfold with S_db.
gate_reduce.
Qed.

Definition φ432 := (I_2 ⊗ I_2 ⊗ σZ) × φ431.
Lemma step432 : φ432 = / 2  .* (∣1⟩ ⊗ ∣1⟩) ⊗ ketp.
Proof.
unfold φ432.
rewrite step431.
autounfold with S_db.
gate_reduce.
Qed.

(* Definition φ0 := ketp ⊗ bell00.
Definition φ1 := (CNOT ⊗ I_2) × φ0.
Definition φ2 := (H ⊗ I_2 ⊗ I_2) × φ1.

Definition φ30 := (M0 ⊗ M0 ⊗ I_2) × φ2.
Definition φ31 := (M0 ⊗ M1 ⊗ I_2) × φ2.
Definition φ32 := (M1 ⊗ M0 ⊗ I_2) × φ2.
Definition φ33 := (M1 ⊗ M1 ⊗ I_2) × φ2.

Definition φ40 := φ30.
Definition φ41 := (I_2 ⊗ I_2 ⊗ σX) × φ31.
Definition φ42 := (I_2 ⊗ I_2 ⊗ σZ) × φ32.

Definition φ43 := (I_2 ⊗ I_2 ⊗ σZ) × (I_2 ⊗ I_2 ⊗ σX) × φ33. *)


Lemma tele0 :  (M0 ⊗ M0 ⊗ I_2) × (H ⊗ I_2 ⊗ I_2) × (CNOT ⊗ I_2) × (∣+⟩ ⊗ bell00) = / 2  .* ∣0⟩ ⊗ ∣0⟩ ⊗ ∣+⟩ .
Proof.
autounfold with S_db.
unfold CNOT,M0,M1.
gate_reduce.
rewrite Cmult_comm;auto.
Qed.

Lemma tele1 : (I_2 ⊗ I_2 ⊗ σX) × (M0 ⊗ M1 ⊗ I_2) × (H ⊗ I_2 ⊗ I_2) × (CNOT ⊗ I_2) × (∣+⟩ ⊗ bell00) = / 2  .* ∣0⟩ ⊗ ∣1⟩ ⊗ ∣+⟩ .
Proof.
autounfold with S_db.
unfold CNOT,M0,M1.
gate_reduce.
rewrite Cmult_comm;auto.
Qed.

Lemma tele2 : (I_2 ⊗ I_2 ⊗ σZ) × (M1 ⊗ M0 ⊗ I_2) × (H ⊗ I_2 ⊗ I_2) × (CNOT ⊗ I_2) × (∣+⟩ ⊗ bell00) = / 2  .* ∣1⟩ ⊗ ∣0⟩ ⊗ ∣+⟩ .
Proof.
autounfold with S_db.
unfold CNOT,M0,M1.
gate_reduce.
rewrite Cmult_comm;auto.
Qed.

Lemma tele3 : (I_2 ⊗ I_2 ⊗ σZ) × (I_2 ⊗ I_2 ⊗ σX) × (M1 ⊗ M1 ⊗ I_2) × (H ⊗ I_2 ⊗ I_2) × (CNOT ⊗ I_2) × (∣+⟩ ⊗ bell00) = / 2  .* ∣1⟩ ⊗ ∣1⟩ ⊗ ∣+⟩ .
Proof.
autounfold with S_db.
unfold CNOT,M0,M1.
gate_reduce.
rewrite Cmult_comm;auto.
Qed.

Lemma gg : (CNOT ⊗ I_2) × (∣0⟩ ⊗ ∣0⟩ ⊗ ∣0⟩) = (∣0⟩ ⊗ ∣0⟩ ⊗ ∣0⟩) .
Proof.
unfold CNOT.
gate_reduce.
Qed.

Lemma ggg : (CNOT ⊗ I_2) × (CNOT ⊗ I_2) × (∣0⟩ ⊗ ∣0⟩ ⊗ ∣0⟩) = (∣0⟩ ⊗ ∣0⟩ ⊗ ∣0⟩) .
Proof.
unfold CNOT at 2.
gate_reduce.
unfold CNOT.
gate_reduce.
Qed.

Lemma ii : / √ 2 * / √ 2
   .* (I_2 ⊗ (I_2 ⊗ σZ)
       × (I_2 ⊗ (I_2 ⊗ σX)
          × (B3 ⊗ (B3 ⊗ I_2)
             × (H ⊗ (I_2 ⊗ I_2)
                × (B3 ⊗ (σX ⊗ I_2) × (∣0⟩ ⊗ (∣0⟩ ⊗ ∣0⟩))))))) = Zero .
Proof.
(* repeat mult_kron1.
autorewrite with B_db G_db.
isolate_scale.
reduce_scale. *)
mult_kron1.
rewrite B30.
repeat cancel_0.
auto.
Qed.
