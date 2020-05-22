Require Export M_notWF.


(* The matrix representations of the ground states ∣0⟩ and ∣1⟩*)
Definition ket0 : Vector 2 := 
  fun x y => match x, y with 
          | 0, 0 => C1
          | 1, 0 => C0
          | _, _ => C0
          end.
Definition ket1 : Vector 2 := 
  fun x y => match x, y with 
          | 0, 0 => C0
          | 1, 0 => C1
          | _, _ => C0
          end.


(* The Notation between ∣0⟩ and ∣1⟩*)
Notation "∣0⟩" := ket0.
Notation "∣1⟩" := ket1.
Notation "⟨0∣" := ∣0⟩†.
Notation "⟨1∣" := ∣1⟩†.
Notation "∣0⟩⟨0∣" := (∣0⟩×⟨0∣).
Notation "∣0⟩⟨1∣" := (∣0⟩×⟨1∣).
Notation "∣1⟩⟨0∣" := (∣1⟩×⟨0∣).
Notation "∣1⟩⟨1∣" := (∣1⟩×⟨1∣).


(* Define and signify  the other orthogonal  basis ∣+⟩ and ∣-⟩ *)
Definition ketp := /√2 .* ∣0⟩ .+ /√2 .* ∣1⟩.
Definition brap := /√2 .* ⟨0∣ .+ /√2 .* ⟨1∣.
Definition ketn := /√2 .* ∣0⟩ .+ (-/√2) .* ∣1⟩.
Definition bran := /√2 .* ⟨0∣ .+ (-/√2) .* ⟨1∣.

Notation "∣+⟩" := ketp.
Notation "∣-⟩" := ketn.
Notation "⟨+∣" := brap.
Notation "⟨-∣" := bran.


(* Recursively define the n qubits of 'ket0' and 'ket1' *)
Fixpoint ket0_n (n : nat) : Matrix (2^n) 1 :=
match n with
| 0 => I 1
| S n' => ket0 ⊗ ket0_n n'
end.
Definition ket0_n' (n : nat) := kron_n n ket0.

Fixpoint ket1_n (n : nat) : Matrix (2^n) 1 :=
match n with
| 0 => I 1
| S n' => ket1 ⊗ ket1_n n'
end.
Definition ket1_n' (n : nat) := kron_n n ket1.

Hint Unfold ket0 ket1 : U_db.
Hint Unfold ketp ketn brap bran ket0_n ket1_n : S_db.



Ltac orthogonal_reduce :=
  autounfold with S_db;
  autounfold with U_db;
  prep_matrix_equality;
  destruct_m_eq; autorewrite with C_db;auto;
  bdestruct_all;
  try rewrite andb_false_r;
  try lca.


(* Proof orthogonal lemma between ⟨0∣, ⟨1∣, ∣0⟩ and ∣1⟩ *)
Lemma Mmult_bra0_ket0 : ⟨0∣ × ∣0⟩ = I 1. (*  1 .* I 1  *)
Proof. orthogonal_reduce. Qed.
Lemma Mmult_bra0_ket1 : ⟨0∣ × ∣1⟩ = Zero. (*  0 .* I 1  *)
Proof. orthogonal_reduce. Qed.
Lemma Mmult_bra1_ket0 : ⟨1∣ × ∣0⟩ = Zero.
Proof. orthogonal_reduce. Qed.
Lemma Mmult_bra1_ket1 : ⟨1∣ × ∣1⟩ = I 1.
Proof. orthogonal_reduce. Qed.


(* For more efficiency *)
(* other 'orthogonal' lemma *)
Lemma Mmult_brap_ketp : ⟨+∣ × ∣+⟩ = 1 .* I 1.
Proof. orthogonal_reduce. Qed.
Lemma Mmult_brap_ketn : ⟨+∣ × ∣-⟩ = Zero.
Proof. orthogonal_reduce. Qed.
Lemma Mmult_bran_ketp : ⟨-∣ × ∣+⟩ = Zero.
Proof. orthogonal_reduce. Qed.
Lemma Mmult_bran_ketn : ⟨-∣ × ∣-⟩ = 1 .* I 1.
Proof. orthogonal_reduce. Qed.

Lemma Mmult_bra0_ketp : ⟨0∣ × ∣+⟩ = / √ 2 .* I 1.
Proof. orthogonal_reduce. Qed.
Lemma Mmult_bra0_ketn : ⟨0∣ × ∣-⟩ = / √ 2 .* I 1.
Proof. orthogonal_reduce. Qed.
Lemma Mmult_bra1_ketp : ⟨1∣ × ∣+⟩ = / √ 2 .* I 1.
Proof. orthogonal_reduce. Qed.
Lemma Mmult_bra1_ketn : ⟨1∣ × ∣-⟩ = - / √ 2 .* I 1.
Proof. orthogonal_reduce. Qed.

Lemma Mmult_brap_ket0 : ⟨+∣ × ∣0⟩ = / √ 2 .* I 1.
Proof. orthogonal_reduce. Qed.
Lemma Mmult_brap_ket1 : ⟨+∣ × ∣1⟩ = / √ 2 .* I 1.
Proof. orthogonal_reduce. Qed.
Lemma Mmult_bran_ket0 : ⟨-∣ × ∣0⟩ = / √ 2 .* I 1.
Proof. orthogonal_reduce. Qed.
Lemma Mmult_bran_ket1 : ⟨-∣ × ∣1⟩ = - / √ 2 .* I 1.
Proof. orthogonal_reduce. Qed.

Lemma Mplus01 : ∣0⟩⟨0∣ .+ ∣1⟩⟨1∣ = I 2.
Proof. orthogonal_reduce. Qed.
Lemma Mplus10 : ∣1⟩⟨1∣ .+ ∣0⟩⟨0∣ = I 2.
Proof. orthogonal_reduce. Qed.

Hint Rewrite Mmult_bra0_ket0 Mmult_bra0_ket1 Mmult_bra1_ket0 Mmult_bra1_ket1
(*                          Mmult_brap_ketp Mmult_brap_ketn Mmult_bran_ketp Mmult_bran_ketn
                         Mmult_bra0_ketp Mmult_bra1_ketp Mmult_bra0_ketn Mmult_bra1_ketn
                         Mmult_brap_ket0 Mmult_brap_ket1 Mmult_bran_ket0 Mmult_bran_ket1 *) : S_db.




(* U Operators *)


(*Base Operators*)
Definition B0 := ∣0⟩ × ⟨0∣.
Definition B1 := ∣0⟩ × ⟨1∣.
Definition B2 := ∣1⟩ × ⟨0∣.
Definition B3 := ∣1⟩ × ⟨1∣.

Hint Unfold B0 B1 B2 B3 : B_db.


(*Pauli Operators*)
Definition σX := B1 .+ B2.
Definition σY := - Ci .* B1 .+ Ci .* B2.
Definition σZ := B0 .+ (-1) .* B3.
Definition I_2 := B0 .+ B3.

Lemma I2_eq : I_2 = I 2 .
Proof. 
  unfold I_2.
  autounfold with B_db.
  orthogonal_reduce.
Qed.
Lemma I4_eq : I_2 ⊗ I_2 = I 4 .
Proof.
  rewrite I2_eq.
  rewrite id_kron.
  simpl; auto.
Qed.


(*H Operators*)
Definition H := /√2 .* B0 .+ /√2 .* B1  .+ /√2 .* B2 .+ (-/√2) .* B3.

Fixpoint H_n (n : nat) : Matrix (2^n) (2^n):= 
  match n with
  | 0 => I 1
  | S n' => H ⊗ H_n n'
  end.
Definition H_n' (n : nat) := kron_n n H.


(*Phase Operators*)
Definition PS := B0 .+ Ci .* B3.
Definition PT := B0 .+ (/√2 + /√2 * Ci) .* B3.

Definition Pg (ϕ : R) := B0 .+ Cexp ϕ .* B3.


Lemma PS_eq : PS = Pg (PI/2).
Proof.
unfold PS,Pg.
autorewrite * with Cexp_db.
auto.
Qed.

Lemma PT_eq : PT = Pg (PI/4).
Proof.
unfold PT,Pg.
autorewrite * with Cexp_db.
auto.
Qed.

Lemma PZ_eq : σZ = Pg PI.
Proof.
unfold Pg.
autorewrite * with Cexp_db.
auto.
Qed.

Lemma PZn_eq : σZ = Pg (-PI) .
Proof.
unfold Pg,σZ.
autorewrite * with Cexp_db.
replace (/ -1) with (Copp (RtoC 1)) by lca.
rewrite Copp_1.
auto.
Qed.


Lemma PS_sa : (PS†) = B0 .+ - Ci .* B3.
Proof. lma. Qed.

Lemma PT_sa : (PT†) = B0 .+ (/√2 + (-/√2) * Ci) .* B3.
Proof. lma. Qed.


(*Measure Operators*)
Definition M0 := B0.
Definition M1 := B3.


(*Control Operators*)
Definition CX :=  B0 ⊗ I_2 .+ B3 ⊗ σX.
Definition CZ :=  B0 ⊗ I_2 .+ B3 ⊗ σZ.
Definition CS :=  B0 ⊗ I_2 .+ B3 ⊗ PS.
Definition CT :=  B0 ⊗ I_2 .+ B3 ⊗ PT.

Definition XC :=  I_2 ⊗ B0 .+ σX ⊗ B3.
Definition ZC :=  I_2 ⊗ B0 .+ σZ ⊗ B3.
Definition PC :=  I_2 ⊗ B0 .+ PS ⊗ B3.
Definition TC :=  I_2 ⊗ B0 .+ PT ⊗ B3.

Definition not_CX := B0 ⊗ σX .+ B3 ⊗ I_2.

Definition Cg_1 {n} (A : Matrix n n) := B0 ⊗ I_2 .+ B3 ⊗ A.
Definition gC_1 {n} (A : Matrix n n) := A ⊗ B3 .+ I_2 ⊗ B0.
Definition CX' :=  Cg_1 σX.
Definition CZ' :=  Cg_1 σZ.
Definition CS' :=  Cg_1 PS.
Definition CT' :=  Cg_1 PT.


Lemma CX_eq : CX' = CX .
Proof. unfold CX',CX,Cg_1. auto. Qed.
Lemma CZ_eq : CZ' = CZ .
Proof. unfold CZ',CZ,Cg_1. auto. Qed.
Lemma CS_eq : CS' = CS .
Proof. unfold CS',CS,Cg_1. auto. Qed.
Lemma CP_eq : CT' = CT .
Proof. unfold CT',CT,Cg_1. auto. Qed.


Definition SWAP :=  B0 ⊗ B0 .+ B1 ⊗ B2 .+ B2 ⊗ B1 .+ B3 ⊗ B3.


Hint Unfold  σX σY σZ I_2 H M0 M1 : G1_db.
Hint Unfold  CZ CX CS CT XC ZC PC TC SWAP not_CX : G2_db.



(* Hermitian *)
Definition id_sa := id_adjoint_eq.

Lemma braket0_sa : ∣0⟩⟨0∣† = ∣0⟩⟨0∣. Proof. lma. Qed.
Lemma braket1_sa : ∣1⟩⟨1∣† = ∣1⟩⟨1∣. Proof. lma. Qed.

Lemma B0_sa : B0† = B0.
Proof. lma. Qed.

Lemma B1_sa : B1† = B2.
Proof. lma. Qed.

Lemma B2_sa : B2† = B1.
Proof. lma. Qed.

Lemma B3_sa : B3† = B3.
Proof. lma. Qed.

Lemma I_sa : I_2† = I_2.
Proof. lma. Qed.

Lemma H_sa : H† = H.
Proof. lma. Qed.

Lemma σX_sa : σX† = σX.
Proof. lma. Qed.

Lemma σY_sa : σY† = σY.
Proof. lma. Qed.

Lemma σZ_sa : σZ† = σZ.
Proof. lma. Qed.

Lemma CX_sa : CX† = CX.
Proof. lma. Qed.

Hint Rewrite I_sa H_sa σX_sa σY_sa σZ_sa CX_sa
                         braket0_sa braket1_sa : A_db.



(* Unitary *)
Lemma MmultII : I_2 × I_2 = I_2.
Proof. lma. Qed.
Lemma MmultXII' : I_2† × I_2 = I 2.
Proof.
  rewrite I_sa.
  rewrite MmultII.
  rewrite I2_eq;auto.
Qed.

Lemma MmultXX : σX × σX = I_2.
Proof. lma. Qed.
Lemma MmultXX' : σX† × σX = I 2.
Proof. 
  rewrite σX_sa.
  rewrite MmultXX.
  rewrite I2_eq;auto.
Qed.

Lemma MmultYY : σY × σY = I_2.
Proof. lma. Qed.
Lemma MmultYY' : σY† × σY = I 2.
Proof. 
  rewrite σY_sa.
  rewrite MmultYY.
  rewrite I2_eq;auto.
Qed.

Lemma MmultZZ : σZ × σZ = I_2.
Proof. lma. Qed.
Lemma MmultZZ' : σZ† × σZ = I 2.
Proof. 
  rewrite σZ_sa.
  rewrite MmultZZ.
  rewrite I2_eq;auto.
Qed.

Lemma MmultCXCX : CX × CX = I_2 ⊗ I_2 .
Proof. lma. Qed.
Lemma MmultCXCX' : CX† × CX =  I 4 .
Proof.
  rewrite CX_sa.
  rewrite MmultCXCX.
  rewrite I4_eq;auto.
Qed.



(* Preliminary strategy *)
Ltac distribute_plus:=
repeat rewrite ?Mmult_plus_distr_r, ?Mmult_plus_distr_l,?Mscale_plus_distr_r,?kron_plus_distr_r,?kron_plus_distr_l;
try repeat rewrite<- Mplus_assoc.


Ltac isolate_scale:=
repeat rewrite ?Mscale_mult_dist_l,?Mscale_mult_dist_r,?Mscale_kron_dist_r,?Mscale_kron_dist_l,?Mscale_assoc.


Ltac kron_mult:=
repeat rewrite <- kron_mixed_product.


Ltac assoc_right:=
repeat rewrite ?Mmult_assoc, ?kron_assoc.


Ltac distribute_adjoint:=
repeat rewrite ?adjoint_involutive, ?id_adjoint_eq,?zero_adjoint_eq,
                          ?Mscale_adj,?Mplus_adjoint,?Mmult_adjoint,?kron_adjoint.


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

Ltac mult_kron :=
  match goal with
  | |- context [@Mmult ?m1o1 ?n1p1 ?n2p2 (@kron ?m1 ?n1 ?o1 ?p1 ?A ?B) (@kron ?m2 ?n2 ?o2 ?p2 ?C ?D)] =>
             change (@Mmult m1o1 n1p1 n2p2 (@kron m1 n1 o1 p1 A B) (@kron m2 n2 o2 p2 C D)) with
                           (@Mmult (m1 * o1) (n1 * p1) (n2 * p2) (@kron m1 n1 o1 p1 A B) (@kron n1 n2 p1 p2 C D));
             rewrite (@kron_mixed_product m1 n1 n2 o1 p1 p2 A B C D)
  end.

Ltac mult_result :=
  repeat mult_kron;
  autorewrite with S_db;
  isolate_scale;
  repeat rewrite id_kron;
  apply fake_eq_intro; reflexivity.


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
  | |- context  [@Mmult ?m1 ?n1 ?o1 (@Zero ?m2 ?n2) ?A] =>
             change  (@Mmult m1 n1 o1 (@Zero m2 n2) A)  with
                           (@Mmult m1 n1 o1 (@Zero m1 n1) A);
             rewrite (@Mmult_0_l  m1 n1 o1 A)
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

Ltac Mmult_1 :=
  match goal with
  | |- context  [@Mmult ?m1 ?n1 ?o1 ?A (@I ?p1)] =>
             change  (@Mmult m1 n1 o1 A (@I p1))  with
                           (@Mmult m1 n1 n1 A (@I n1));
             rewrite (@Mmult_1_r m1 n1 A)
  | |- context  [@Mmult ?m1 ?n1 ?o1 (@I ?p1) ?A] =>
             change  (@Mmult m1 n1 o1 (@I p1) A)  with
                           (@Mmult n1 n1 o1 (@I n1) A);
             rewrite (@Mmult_1_l  n1 o1 A)
  end.


Ltac mult_reduce :=
match goal with
| |-context [ @Mmult ?one1 ?n ?one2 ?A ?B] =>
         match B with
        | @Mmult _ _ _ _ _ => fail 1
        | _ => change (@Mmult one1 n one2 A B) with
                                (@Mmult 1 n 1 A B);
                   unify one1 1%nat;
                   unify one2 1%nat;
                   erewrite (mult_reduce1 n A B) by (mult_result; fail 2 "mult_result_gen fail")
        end
| |-context [ @Mmult ?one1 ?n ?m ?A (@Mmult ?n ?one2 ?m ?B ?C)] =>
         change (@Mmult one1 n m A (@Mmult n one2 m B C)) with
                       (@Mmult 1 n m A (@Mmult n 1 m B C));
          erewrite (mult_reduce2 n m A B C) by (mult_result; fail 2 "mult_result_gen fail")
end;
isolate_scale;
repeat Mmult_1;
repeat cancel_0.



(**********************************************************)
(** Tactics for solving equalities of matrix polymonials. *)
(** Work for equalities with the same number of terms     *)
(** between LHS and RHS. Canceling terms with 0-scale is  *)
(** necessary before applying [cancel_common_factor]      *)
(** TODO:                                                 *)
(** group/ring/field tactics should be applicable?        *)
(**********************************************************)
Lemma f_equal2_Mplus:
  forall m n (A A' B B': Matrix m n), A = A' -> B = B' -> A .+ B = A' .+ B'.
Proof. congruence. Qed.

Lemma f_equal_Mmult:
  forall m n (A : Matrix m  n) s1 s2,
    s1 = s2 -> s1 .* A = s2 .* A.
Proof. congruence. Qed.

Ltac shift_target_in_RHS x y :=
  match x with
  | _ .* ?z =>
    (* Here we assume factor is of form <scale factor> .* <matrix> *)
    let target := fresh "target" in
    remember (x .+ y); remember z as target;
    (* if target at the end of RHS, i.e. (_ + target) *)
    try match goal with
        | |- context[_ .+ _ .* target] => rewrite (Mplus_comm _ _ _ (_ .* target))
        end;
    (* otherwise target in the middle of RHS, i.e. (_ + (target + _)); or is the head, in which case we are done *)
    repeat
      (rewrite <- (Mplus_assoc _ _ _ (_ .* target ) _);
       rewrite (Mplus_comm _ _ _ (_ .* target));
       repeat rewrite Mplus_assoc)
  end.

Ltac cancel_common_factor :=
  repeat rewrite Mplus_assoc;
  match goal with
  | |- ?x .+ ?y = _ => shift_target_in_RHS x y; subst 
  end;
  (* cancel head *) apply f_equal2_Mplus;
  (* solve scale equality *)
  auto using f_equal_Mmult, Cmult_comm.
(*, Cmult_opp1_r, Cmult_opp1_l,
  Copp_involutive, Cplus_opp_r. *)

Ltac normalize := distribute_plus; isolate_scale; assoc_right.
(**********************************************************)


Lemma aux: RtoC (IZR (Zneg xH)) = - (RtoC (IZR (Zpos xH))).
Proof.
  rewrite <- RtoC_opp.
  f_equal.
Qed.

Lemma move_one_side: forall n m (X Y: Matrix n m), X .+ (- (RtoC (IZR (Zpos xH)))) .* Y .+ Zero ≡ Zero -> X ≡ Y.
Proof.
  intros.
  rewrite Mplus_0_r in H0.
  rewrite <- (Mplus_0_r _ _ X).
  rewrite <- (Mplus_0_l _ _ Y).
  rewrite <- (Mscale_1_l _ _ Y).
  rewrite <- H0 at 2.
  rewrite Mplus_assoc.
  rewrite <- Mscale_plus_distr_l.
  apply Mplus_proper; [reflexivity |].
  rewrite <- (Mscale_0_l _ _ Y).
  apply Scale_proper; [| reflexivity].
  ring.
Qed.

Lemma shrink_one: forall n m (X Y Z: Matrix n m) k1 k2,
  (k1 + k2) .* X .+ Y ≡ Z ->
  k1 .* X .+ (k2 .* X .+ Y) ≡ Z.
Proof.
  intros.
  rewrite <- Mplus_assoc.
  rewrite <- Mscale_plus_distr_l.
  auto.
Qed.

Lemma give_up_one: forall n m (X Y Z W: Matrix n m) k,
  X .+ Z ≡ W .+ ((-1) * k .* Y) ->
  X .+ (k .* Y .+ Z) ≡ W.
Proof.
  intros.
  rewrite (Mplus_comm _ _ _ Z).
  rewrite <- Mplus_assoc.
  rewrite H0.
  rewrite Mplus_assoc.
  rewrite <- (Mplus_0_r _ _ W) at 2.
  apply Mplus_proper; [reflexivity |].  
  rewrite <- Mscale_plus_distr_l.
  rewrite <- (Mscale_0_l _ _ Y).
  apply Scale_proper; [| reflexivity].
  rewrite aux.
  ring.
Qed.

Lemma reverse_one: forall n m (Y Z W: Matrix n m) k,
  k .* Y .+ Z ≡ W ->
  Z ≡ W .+ ((-1) * k .* Y).
Proof.
  intros.
  rewrite <- H0.
  rewrite (Mplus_comm _ _ _ Z).
  rewrite Mplus_assoc.
  rewrite <- (Mplus_0_r _ _ Z) at 1.
  apply Mplus_proper; [reflexivity |].  
  rewrite <- Mscale_plus_distr_l.
  rewrite <- (Mscale_0_l _ _ Y).
  apply Scale_proper; [| reflexivity].
  rewrite aux.
  ring.
Qed.

Lemma finish_one_stage: forall n m (X Y Z: Matrix n m) (k: C),
  k = 0 ->
  Y ≡ Z ->
  k .* X .+ Y ≡ Z.
Proof.
  intros.
  rewrite H0, H1.
  rewrite (Mscale_0_l _ _ X).
  rewrite Mplus_0_l.
  reflexivity.
Qed.

Ltac linear_solver' :=
  first
    [ reflexivity
    | repeat first [apply shrink_one | apply give_up_one];
      apply finish_one_stage; [try ring | repeat apply reverse_one; linear_solver']].

Ltac linear_solver :=
  apply move_one_side;
  repeat rewrite Mscale_plus_distr_r;
  repeat rewrite Mscale_assoc;
  repeat rewrite Mplus_assoc;
  linear_solver';
  lca.

Ltac reduce_scale:=
autorewrite with C_db;
repeat group_radicals;
repeat rewrite ?Mscale_0_l,?Mscale_1_l;
repeat cancel_0;
try linear_solver;
try reflexivity.

Ltac unified_base :=
autounfold with S_db;
distribute_plus;
isolate_scale;
reduce_scale.



(* Symbolic Reasoning Strategy of Base Operate *)
Ltac base_reduce :=
autounfold with B_db S_db;
distribute_plus;
isolate_scale;
assoc_right;
repeat mult_reduce;
reduce_scale.


(*Base-Operators_reduce *)
Lemma Mmult_B00 : B0 × ∣0⟩ ≡ ∣0⟩.
Proof. base_reduce. Qed.
Lemma Mmult_0B0 : ⟨0∣ × B0 ≡ ⟨0∣.
Proof. base_reduce. Qed.

Lemma Mmult_B01 : B0 × ∣1⟩ ≡ Zero.
Proof. base_reduce. Qed.
Lemma Mmult_1B0 : ⟨1∣ × B0 ≡ Zero.
Proof. base_reduce. Qed.

Lemma Mmult_B0pos : B0 × ∣+⟩ ≡ / √ 2 .* ∣0⟩.
Proof. base_reduce. Qed.
Lemma Mmult_posB0 : ⟨+∣ × B0 ≡ / √ 2 .* ⟨0∣.
Proof. base_reduce. Qed.

Lemma Mmult_B0neg : B0 × ∣-⟩ ≡ / √ 2 .* ∣0⟩.
Proof. base_reduce. Qed.
Lemma Mmult_negB0 : ⟨-∣ × B0 ≡ / √ 2 .* ⟨0∣.
Proof. base_reduce. Qed.

Lemma Mmult_B10 : B1 × ∣0⟩ ≡ Zero.
Proof. base_reduce. Qed.
Lemma Mmult_0B1 : ⟨0∣ × B1 ≡ ⟨1∣.
Proof. base_reduce.  Qed.

Lemma Mmult_B11 : B1 × ∣1⟩ ≡ ∣0⟩.
Proof. base_reduce. Qed.
Lemma Mmult_1B1 : ⟨1∣ × B1 ≡ Zero.
Proof. base_reduce. Qed.

Lemma Mmult_B1pos : B1 × ∣+⟩ ≡ / √ 2 .* ∣0⟩.
Proof. base_reduce. Qed.
Lemma Mmult_posB1 : ⟨+∣ × B1 ≡ / √ 2 .* ⟨1∣.
Proof. base_reduce.  Qed.

Lemma Mmult_B1neg : B1 × ∣-⟩ ≡ - / √ 2 .* ∣0⟩.
Proof. base_reduce. Qed.
Lemma Mmult_negB1 : ⟨-∣ × B1 ≡ / √ 2 .* ⟨1∣.
Proof. base_reduce. Qed.

Lemma Mmult_B20 : B2 × ∣0⟩ ≡ ∣1⟩.
Proof. base_reduce. Qed.
Lemma Mmult_0B2 : ⟨0∣ × B2 ≡ Zero.
Proof. base_reduce. Qed.

Lemma Mmult_B21 : B2 × ∣1⟩ ≡ Zero.
Proof. base_reduce. Qed.
Lemma Mmult_1B2 : ⟨1∣ × B2 ≡ ⟨0∣.
Proof. base_reduce. Qed.

Lemma Mmult_B2pos : B2 × ∣+⟩ ≡ / √ 2 .* ∣1⟩.
Proof. base_reduce. Qed.
Lemma Mmult_posB2 : ⟨+∣ × B2 ≡ / √ 2 .* ⟨0∣.
Proof. base_reduce. Qed.

Lemma Mmult_B2neg : B2 × ∣-⟩ ≡ / √ 2 .* ∣1⟩.
Proof. base_reduce. Qed.
Lemma Mmult_negB2 : ⟨-∣ × B2 ≡ - / √ 2 .* ⟨0∣.
Proof. base_reduce. Qed.


Lemma Mmult_B30 : B3 × ∣0⟩ ≡ Zero.
Proof. base_reduce. Qed.
Lemma Mmult_0B3 : ⟨0∣ × B3 ≡ Zero.
Proof. base_reduce. Qed.

Lemma Mmult_B31 : B3 × ∣1⟩ ≡ ∣1⟩.
Proof. base_reduce. Qed.
Lemma Mmult_1B3 : ⟨1∣ × B3 ≡ ⟨1∣.
Proof. base_reduce. Qed.

Lemma Mmult_B3pos : B3 × ∣+⟩ ≡ / √ 2 .* ∣1⟩.
Proof. base_reduce. Qed.
Lemma Mmult_posB3 : ⟨+∣ × B3 ≡ / √ 2 .* ⟨1∣.
Proof. base_reduce. Qed.

Lemma Mmult_B3neg : B3 × ∣-⟩ ≡ - / √ 2 .* ∣1⟩.
Proof. base_reduce. Qed.
Lemma Mmult_negB3 : ⟨-∣ × B3 ≡ - / √ 2 .* ⟨1∣.
Proof. base_reduce. Qed.

Hint Rewrite Mmult_B00 Mmult_B01 Mmult_B0pos Mmult_B0neg
                              Mmult_B10 Mmult_B11 Mmult_B1pos Mmult_B1neg
                              Mmult_B20 Mmult_B21 Mmult_B2pos Mmult_B2neg
                              Mmult_B30 Mmult_B31 Mmult_B3pos Mmult_B3neg
                              Mmult_0B0 Mmult_1B0 Mmult_posB0 Mmult_negB0
                              Mmult_0B1 Mmult_1B1 Mmult_posB1 Mmult_negB1
                              Mmult_0B2 Mmult_1B2 Mmult_posB2 Mmult_negB2
                              Mmult_0B3 Mmult_1B3 Mmult_posB3 Mmult_negB3 : B_db.



(* Symbolic Reasoning Strategy of Pauli and H operate *)
Ltac gate_reduce :=
autounfold with G1_db;
distribute_plus;
isolate_scale;
assoc_right;
autorewrite with B_db;
reduce_scale;
unified_base.

(*Pauli-Operators_reduce *)
Lemma Mmult_I0 : I_2 × ∣0⟩ ≡ ∣0⟩.
Proof. gate_reduce. Qed.
Lemma Mmult_0I : ⟨0∣ × I_2 ≡ ⟨0∣.
Proof. gate_reduce. Qed.

Lemma Mmult_I1 : I_2 × ∣1⟩ ≡ ∣1⟩.
Proof. gate_reduce. Qed.
Lemma Mmult_1I : ⟨1∣ × I_2 ≡ ⟨1∣.
Proof. gate_reduce.  Qed.

Lemma Mmult_Ipos : I_2 × ∣+⟩ ≡ ∣+⟩.
Proof. gate_reduce. Qed.
Lemma Mmult_posI : ⟨+∣ × I_2 ≡ ⟨+∣.
Proof. gate_reduce.  Qed.

Lemma Mmult_Ineg : I_2 × ∣-⟩ ≡ ∣-⟩.
Proof. gate_reduce. Qed.
Lemma Mmult_negI : ⟨-∣ × I_2 ≡ ⟨-∣.
Proof. gate_reduce.  Qed.

Lemma Mmult_σX0 : σX × ∣0⟩ ≡ ∣1⟩.
Proof. gate_reduce. Qed.
Lemma Mmult_0σX : ⟨0∣ × σX ≡ ⟨1∣.
Proof. gate_reduce.  Qed.

Lemma Mmult_σX1 : σX × ∣1⟩ ≡ ∣0⟩.
Proof. gate_reduce. Qed.
Lemma Mmult_1σX : ⟨1∣ × σX ≡ ⟨0∣.
Proof. gate_reduce.  Qed.

Lemma Mmult_σXpos : σX × ∣+⟩ ≡ ∣+⟩.
Proof. gate_reduce. Qed.
Lemma Mmult_posσX : ⟨+∣ × σX ≡ ⟨+∣.
Proof. gate_reduce. Qed.

Lemma Mmult_σXneg : σX × ∣-⟩ ≡ -1 .* ∣-⟩.
Proof. gate_reduce. Qed.
Lemma Mmult_negσX : ⟨-∣ × σX ≡ -1 .* ⟨-∣.
Proof. gate_reduce. Qed.

Lemma Mmult_σZ0 : σZ × ∣0⟩ ≡ ∣0⟩.
Proof. gate_reduce. Qed.
Lemma Mmult_0σZ : ⟨0∣ × σZ ≡ ⟨0∣.
Proof. gate_reduce.  Qed.

Lemma Mmult_σZ1 : σZ × ∣1⟩ ≡ -1 .* ∣1⟩.
Proof. gate_reduce. Qed.
Lemma Mmult_1σZ : ⟨1∣ × σZ ≡ -1 .* ⟨1∣.
Proof. gate_reduce.  Qed.

Lemma Mmult_σZpos : σZ × ∣+⟩ ≡ ∣-⟩.
Proof. gate_reduce. Qed.
Lemma Mmult_posσZ : ⟨+∣ × σZ ≡ ⟨-∣.
Proof. gate_reduce.  Qed.

Lemma Mmult_σZneg : σZ × ∣-⟩ ≡ ∣+⟩.
Proof. gate_reduce. Qed.
Lemma Mmult_negσZ : ⟨-∣ × σZ ≡ ⟨+∣.
Proof. gate_reduce.  Qed.

Lemma Mmult_σY0 : σY × ∣0⟩ ≡ Ci .* ∣1⟩.
Proof. gate_reduce. Qed.
Lemma Mmult_0σY : ⟨0∣ × σY ≡ -Ci .* ⟨1∣.
Proof. gate_reduce.  Qed.

Lemma Mmult_σY1 : σY × ∣1⟩ ≡ -Ci .* ∣0⟩.
Proof. gate_reduce. Qed.
Lemma Mmult_1σY : ⟨1∣ × σY ≡ Ci .* ⟨0∣.
Proof. gate_reduce.  Qed.

Lemma Mmult_σYpos : σY × ∣+⟩ ≡ -Ci .* ∣-⟩.
Proof. gate_reduce. Qed.
Lemma Mmult_posσY : ⟨+∣ × σY ≡ Ci .* ⟨-∣.
Proof. gate_reduce. Qed.

Lemma Mmult_σYneg : σY × ∣-⟩ ≡ Ci .* ∣+⟩.
Proof. gate_reduce. Qed.
Lemma Mmult_negσY : ⟨-∣ × σY ≡ -Ci .* ⟨+∣.
Proof. gate_reduce. Qed.


(*H-Operators_reduce *)
Lemma Mmult_H0 : H × ∣0⟩ ≡ ∣+⟩.
Proof. gate_reduce. Qed.

Lemma Mmult_0H : ⟨0∣ × H ≡ ⟨+∣.
Proof. gate_reduce. Qed.

Lemma Mmult_H1 : H × ∣1⟩ ≡ ∣-⟩.
Proof. gate_reduce. Qed.
Lemma Mmult_1H : ⟨1∣ × H ≡ ⟨-∣.
Proof. gate_reduce. Qed.

Lemma Mmult_Hpos : H × ∣+⟩ ≡ ∣0⟩.
Proof. gate_reduce. Qed.
Lemma Mmult_posH : ⟨+∣ × H ≡ ⟨0∣.
Proof. gate_reduce. Qed.

Lemma Mmult_Hneg : H × ∣-⟩ ≡ ∣1⟩.
Proof. gate_reduce. Qed.
Lemma Mmult_negH : ⟨-∣ × H ≡ ⟨1∣.
Proof. gate_reduce. Qed.

Lemma Mmult_M00 : M0 × ∣0⟩ ≡ ∣0⟩.
Proof. gate_reduce. Qed.
Lemma Mmult_0M0 : ⟨0∣ × M0 ≡ ⟨0∣.
Proof. gate_reduce. Qed.

Lemma Mmult_M01 : M0 × ∣1⟩ ≡ Zero.
Proof. gate_reduce. Qed.
Lemma Mmult_1M0 : ⟨1∣ × M0 ≡ Zero.
Proof. gate_reduce. Qed.

Lemma Mmult_M0pos : M0 × ∣+⟩ ≡ / √ 2 .* ∣0⟩.
Proof. gate_reduce. Qed.
Lemma Mmult_posM0 : ⟨+∣ × M0 ≡ / √ 2 .* ⟨0∣.
Proof. gate_reduce. Qed.

Lemma Mmult_M0neg : M0 × ∣-⟩ ≡ / √ 2 .* ∣0⟩.
Proof. gate_reduce. Qed.
Lemma Mmult_negM0 : ⟨-∣ × M0 ≡ / √ 2 .* ⟨0∣.
Proof. gate_reduce. Qed.

Lemma Mmult_M10 : M1× ∣0⟩ ≡ Zero.
Proof. gate_reduce. Qed.
Lemma Mmult_0M1 : ⟨0∣ × M1 ≡ Zero.
Proof. gate_reduce. Qed.

Lemma Mmult_M11 : M1 × ∣1⟩ ≡ ∣1⟩.
Proof. gate_reduce. Qed.
Lemma Mmult_1M1 : ⟨1∣ × M1 ≡ ⟨1∣.
Proof. gate_reduce. Qed.

Lemma Mmult_M1pos : M1 × ∣+⟩ ≡ / √ 2 .* ∣1⟩.
Proof. gate_reduce. Qed.
Lemma Mmult_posM1 : ⟨+∣ × M1 ≡ / √ 2 .* ⟨1∣.
Proof. gate_reduce. Qed.

Lemma Mmult_M1neg : M1 × ∣-⟩ ≡ -/ √ 2 .* ∣1⟩.
Proof. gate_reduce. Qed.
Lemma Mmult_negM1 : ⟨-∣ × M1 ≡ -/ √ 2 .* ⟨1∣.
Proof. gate_reduce. Qed.

Hint Rewrite Mmult_I0 Mmult_I1 Mmult_Ipos Mmult_Ineg
                              Mmult_σX0 Mmult_σX1 Mmult_σXpos Mmult_σXneg
                              Mmult_σZ0 Mmult_σZ1 Mmult_σZpos Mmult_σZneg
                              Mmult_σY0 Mmult_σY1 Mmult_σYpos Mmult_σYneg
                              Mmult_H0 Mmult_H1 Mmult_Hpos Mmult_Hneg
                              Mmult_M00 Mmult_M01 Mmult_M0pos Mmult_M0neg
                              Mmult_M10 Mmult_M11 Mmult_M1pos Mmult_M1neg
                              Mmult_B00 Mmult_B01 Mmult_B0pos Mmult_B0neg
                              Mmult_B10 Mmult_B11 Mmult_B1pos Mmult_B1neg
                              Mmult_B20 Mmult_B21 Mmult_B2pos Mmult_B2neg
                              Mmult_B30 Mmult_B31 Mmult_B3pos Mmult_B3neg
                              Mmult_0B0 Mmult_1B0 Mmult_posB0 Mmult_negB0
                              Mmult_0B1 Mmult_1B1 Mmult_posB1 Mmult_negB1
                              Mmult_0B2 Mmult_1B2 Mmult_posB2 Mmult_negB2
                              Mmult_0B3 Mmult_1B3 Mmult_posB3 Mmult_negB3  : G1_db.



(* Symbolic Reasoning Strategy of states in the vector form *)
Ltac operate_reduce :=
autounfold with G2_db;
distribute_plus;
isolate_scale;
assoc_right;
repeat mult_kron;
repeat (autorewrite with G1_db;
isolate_scale);
reduce_scale;
unified_base.


(* Notation for kron of ∣0⟩ and ∣1⟩ *)
Definition bra (x : nat) : Matrix 1 2 := if x =? 0 then ⟨0∣ else ⟨1∣.
Definition ket (x : nat) : Matrix 2 1 := if x =? 0 then ∣0⟩ else ∣1⟩.
Notation "'∣' x '⟩'" := (ket x).
Notation "'⟨' x '∣'" := (bra x).

Notation "∣ x , y , .. , z ⟩" := (kron .. (kron ∣x⟩ ∣y⟩) .. ∣z⟩) (at level 0).


Lemma CX00 : CX × ∣0,0⟩ ≡ ∣0,0⟩.
Proof. operate_reduce. Qed.

Lemma CX01 : CX × ∣0,1⟩ ≡ ∣0,1⟩.
Proof. operate_reduce. Qed.

Lemma CX10 : CX × ∣1,0⟩ ≡ ∣1,1⟩.
Proof. operate_reduce. Qed.

Lemma CX11 : CX × ∣1,1⟩ ≡ ∣1,0⟩.
Proof. operate_reduce. Qed.

Lemma CXp0 : CX × (∣+⟩ ⊗ ∣0⟩) ≡ /√2 .* ∣0,0⟩ .+ /√2 .* ∣1,1⟩.
Proof. operate_reduce. Qed.

Lemma CXp1 : CX × (∣+⟩ ⊗ ∣1⟩) ≡ /√2 .* ∣0,1⟩ .+ /√2 .* ∣1,0⟩.
Proof. operate_reduce. Qed.

Lemma CXn0 : CX × (∣-⟩ ⊗ ∣0⟩) ≡ /√2 .* ∣0,0⟩ .+ - /√2 .* ∣1,1⟩.
Proof. operate_reduce. Qed.

Lemma CXn1 : CX × (∣-⟩ ⊗ ∣1⟩) ≡ /√2 .* ∣0,1⟩ .+ - /√2 .* ∣1,0⟩.
Proof. operate_reduce. Qed.

Lemma CX0p : CX × (∣0⟩ ⊗ ∣+⟩) ≡ /√2 .* ∣0,0⟩ .+ /√2 .* ∣0,1⟩.
(* Lemma CX0p : CX × (∣0⟩ ⊗ ∣+⟩) ≡ ∣0⟩ ⊗ ∣+⟩. *)
Proof. operate_reduce. Qed.


(* Lemma CX0n : CX × (∣0⟩ ⊗ ∣-⟩) ≡ /√2 .* (∣0⟩ ⊗ ∣0⟩) .+ - /√2 .* (∣0⟩ ⊗ ∣1⟩). *)
Lemma CX0n : CX × (∣0⟩ ⊗ ∣-⟩) ≡ ∣0⟩ ⊗ ∣-⟩.
Proof. operate_reduce. Qed.

(* Lemma CX1p : CX × (∣1⟩ ⊗ ∣+⟩) ≡ /√2 .* (∣1⟩ ⊗ ∣0⟩) .+ /√2 .* (∣1⟩ ⊗ ∣1⟩). *)
Lemma CX1p : CX × (∣1⟩ ⊗ ∣+⟩) ≡ ∣1⟩ ⊗ ∣+⟩.
Proof. operate_reduce. Qed.

(* Lemma CX1n : CX × (∣1⟩ ⊗ ∣-⟩) ≡ /√2 .* (∣1⟩ ⊗ ∣1⟩) .+ - /√2 .* (∣1⟩ ⊗ ∣0⟩). *)
Lemma CX1n : CX × (∣1⟩ ⊗ ∣-⟩) ≡ - 1 .* ∣1⟩ ⊗ ∣-⟩ .
Proof. operate_reduce. Qed.

(* Lemma CXpp : CX × (∣+⟩ ⊗ ∣+⟩) ≡ /2 .* ∣0⟩ ⊗ ∣0⟩ .+ /2 .* ∣0⟩ ⊗ ∣1⟩ .+ /2 .* ∣1⟩ ⊗ ∣0⟩ .+ /2 .* ∣1⟩ ⊗ ∣1⟩. *)
Lemma CXpp : CX × (∣+⟩ ⊗ ∣+⟩) ≡  / √ 2 .* ∣0⟩ ⊗ ∣+⟩ .+ / √ 2 .* ∣1⟩ ⊗ ∣+⟩.
Proof. operate_reduce. Qed.


Lemma CXpn : CX × (∣+⟩ ⊗ ∣-⟩) ≡ /√2 .* (∣0⟩ ⊗ ∣-⟩) .+ - /√2 .* (∣1⟩ ⊗ ∣-⟩).
Proof. operate_reduce. Qed.

Lemma CXnp : CX × (∣-⟩ ⊗ ∣+⟩) ≡ /√2 .* (∣0⟩ ⊗ ∣+⟩) .+ - /√2 .* (∣1⟩ ⊗ ∣+⟩).
Proof. operate_reduce. Qed.

Lemma CXnn : CX × (∣-⟩ ⊗ ∣-⟩) ≡ /√2 .* (∣0⟩ ⊗ ∣-⟩) .+ /√2 .* (∣1⟩ ⊗ ∣-⟩).
Proof. operate_reduce. Qed.


Hint Rewrite CX00 CX01 CX10 CX11
                              CX0p CX1p CX1n CX0n
                              CXp0 CXp1 CXn0 CXn1
                             CXpp CXpn CXnp CXnn : G2_db.


Lemma GHZ_ket0_3 : /√2 .* ∣0,0,0⟩ .+ /√2 .* ∣1,1,1⟩ ≡  (I_2 ⊗ CX) × (CX ⊗ I_2) × (H ⊗ I_2 ⊗ I_2) × ∣0,0,0⟩.
Proof.
autounfold with G2_db.
distribute_plus.
isolate_scale.
assoc_right.
repeat mult_kron.
repeat (autorewrite with G1_db;
isolate_scale).
reduce_scale.
Qed.


(* Symbolic Reasoning Strategy of states in the density matrix form *)
Notation Density n := (Matrix n n) (only parsing).
Definition density {n} (φ : Matrix n 1) : Density n := φ × φ†.
Definition super {m n} (M : Matrix m n) : Density n -> Density m := fun ρ => 
  M × ρ × M†.

Ltac super_reduce:=
unfold super,density;                                                                   (* expand super and density *)
match goal with                                                                              (* match the pattern of the target *)
| |-context [ @Mmult ?n ?m ?n                                                  (*  if likes U × φ × φ† × U† *)
                       (@Mmult ?n ?m ?m ?A ?B)
                        (@adjoint ?n ?m ?A)] =>
     match B with
    | @Mmult ?m ?one ?m ?C 
     (@adjoint ?m ?one ?C) => 
           transitivity (@Mmult n one n                                        (* cast uniform types *)
          (@Mmult n m one A C) (@Mmult one m m 
          (@adjoint m one C) (@adjoint n m A)))
     end
end;
  [repeat rewrite <- Mmult_assoc; reflexivity| ..];
rewrite <- Mmult_adjoint;                                                         (* extract adjoint to become U × φ × (U × φ) *)
let Hs := fresh "Hs" in
match goal with
| |-context [ @Mmult ?n ?o ?n 
(@Mmult ?n ?m ?o ?A ?B) (@adjoint ?m ?o ?C ) ≡ 
  @Mmult  ?n ?p ?n ?D (@adjoint ?n ?p ?D)] =>
      match C with
      | @Mmult ?n ?m ?o ?A ?B=>
       assert (@Mmult n m o A B ≡ D) as Hs
      end
end;
  [try reflexivity; try operate_reduce |                                   (* use operate_reduce to proof vector form states *)
    repeat rewrite Hs; reflexivity].                                            (*  rewrite it back in density matrix form*)






Definition phase_equiv {m n : nat} (A B : Matrix m n) : Prop := 
  exists c : C, Cmod c = R1 /\  c .* A ≡ B.

Infix "≈" := phase_equiv (at level 70) : matrix_scope.

(* Ltac sta_yes :=
unfold sta_equiv;
exists 1;
split;
autorewrite with C_db;auto;
rewrite Mscale_1_l.

Ltac sta_m1 :=
unfold sta_equiv;
exists (-(1));
split;
autorewrite with C_db;auto. *)

Definition operator_apply {m} (A: Matrix m m)(B: Vector m) : Vector m:=
Mmult A B.

Require Import Morphisms.
Instance Mmult_phase_proper m n o: Proper (phase_equiv ==> phase_equiv ==>phase_equiv) (@Mmult m n o).
Proof.
hnf;intros A C H1.
hnf;intros B D H2.
unfold phase_equiv,operator_apply,get in * .
inversion H1. inversion H0.
inversion H2. inversion H5.
exists (x0*x).
rewrite <- Mscale_mult_dist_l.
rewrite <- Mscale_assoc.
rewrite Mscale_mult_dist_l.
rewrite <- Mscale_mult_dist_r.
rewrite H7,H4.
split.
 rewrite Cmod_mult. rewrite H3,H6. lra.
 reflexivity.
Qed.





Lemma mod1_not_0: forall c, Cmod c = R1 -> c <> 0.
Proof.
  intros; intro.
  subst.
  rewrite Cmod_0 in H0.
  lra.
Qed.

Instance phase_equiv_equiv m n: Equivalence (@phase_equiv m n).
Proof.
  constructor.
  + hnf; intros A.
    exists 1.
    split; [autorewrite with C_db;auto | rewrite Mscale_1_l].
    reflexivity.
  + hnf; intros.
    destruct H0 as [c [? ?]]; exists (Cinv c); split.
    - rewrite Cmod_inv by (apply mod1_not_0; auto).
      rewrite H0. field.
    - rewrite <- H1.
      rewrite Mscale_assoc, Cinv_l by (apply mod1_not_0; auto).
      rewrite Mscale_1_l.
      reflexivity.
  + hnf; intros.
    destruct H0 as [c [? ?]], H1 as [c0 [? ?]].
    exists (c * c0); split.
    - rewrite Cmod_mult, H0, H1.
      lra.
    - rewrite <- H3, <- H2.
      rewrite Mscale_assoc, Cmult_comm.
      reflexivity.
Qed.



Lemma mat_equiv_by_Mmult: forall m n (A B: Matrix m n),
  (forall v : Matrix n 1, Mmult A v ≡ Mmult B v) ->
  A ≡ B.
Proof.
  intros m n A B HAB.
    assert (forall j, (j < n)%nat ->
            forall i, (i < m)%nat -> A i j = B i j)
      as HAB'.
 { 
    intros j Hj.
    specialize
      (HAB (fun j' _ => if (j' =? j) && (j' <? n) then 1 else 0)).
    intros.
    specialize (HAB ltac:(exists i; auto)
                     ltac:(exists 0%nat; lia)).
    pose proof Mmult_1_r _ _ A
                 ltac:(exists i; auto)
                 ltac:(exists j; auto)
            as HAj.
    pose proof Mmult_1_r _ _ B
                 ltac:(exists i; auto)
                 ltac:(exists j; auto)
            as HBj.
    unfold scale in HAB.
    unfold Mmult, get, I in HAB, HAj, HBj; simpl in HAB, HAj, HBj.
    rewrite HAj, HBj in HAB.
    auto. 
    }
  assert (forall j j', (j < n)%nat -> (j' < n)%nat ->
          forall x x': C,
            forall i, (i < m)%nat ->
               (A i j * x + A i j' * x') = B i j * x + B i j' * x')
      as HAB''.
{
    intros j j' Hj Hj' x x'.
    specialize
      (HAB (fun j'' _ => x * (if (j'' =? j) && (j'' <? n) then 1 else 0) +
                         x' * (if (j'' =? j') && (j'' <? n) then 1 else 0))).
    intros i Hi.
    specialize (HAB ltac:(exists i; auto)
                       ltac:(exists 0%nat; lia)).
    pose proof Mmult_1_r _ _ A
                 ltac:(exists i; auto)
                 ltac:(exists j; auto)
            as HAj.
    pose proof Mmult_1_r _ _ A
                 ltac:(exists i; auto)
                 ltac:(exists j'; auto)
            as HAj'.
    pose proof Mmult_1_r _ _ B
                 ltac:(exists i; auto)
                 ltac:(exists j; auto)
            as HBj.
    pose proof Mmult_1_r _ _ B
                 ltac:(exists i; auto)
                 ltac:(exists j'; auto)
            as HBj'.
    unfold scale in HAB.
    unfold Mmult, get, I in HAB, HAj, HAj', HBj, HBj';
    simpl in HAB, HAj, HAj', HBj, HBj'.
    assert (forall K,
            (fun y : nat =>
               K y * (x * (if (y =? j) && (y <? n) then 1 else 0) +
                      x' * (if (y =? j') && (y <? n) then 1 else 0))) =
            (fun y : nat =>
               (K y * (if (y =? j) && (y <? n) then 1 else 0)) * x +
               (K y * (if (y =? j') && (y <? n) then 1 else 0)) * x')).
    {
      intros.
      apply functional_extensionality.
      intros j''.
      ring.
    }
    rewrite (Csum_eq _ _ n (H0 (A i))),
            (Csum_eq _ _ n (H0 (B i))),
            !Csum_plus, <- !Csum_mult_r,
            HAj, HAj', HBj, HBj'  in HAB.
    auto.
  }
    pose proof Classical_Prop.classic
               (exists i j, (i < m)%nat /\
                            (j < n)%nat /\
                            A i j <> 0)
          as [[i [j [Hi [Hj HAij]]]] | CONTRA].
  2: {
    intros [i Hi] [j Hj].
    unfold get; simpl.
    assert (A i j = 0).
    {
      apply Classical_Prop.NNPP.
      intro; apply CONTRA.
      exists i, j; auto.
    }
    assert (B i j = 0).
    {
      specialize (HAB' j ltac:(auto)).
      specialize (HAB' i ltac:(auto)).
      rewrite H0 in HAB'.
      rewrite <- HAB'.
      ring.
    }
    rewrite H0, H1; reflexivity.
  }
  pose proof HAB' j Hj as Hcj.
  intros [i' Hi'] [j' Hj']; unfold get; simpl.
  revert i' Hi'.
  pose proof HAB' j' Hj' as Hc'j'.
  destruct (Classical_Prop.classic
            (exists i, (i < m)%nat /\
                       A i j <> 0 /\ A i j' <> 0))
    as [|].
  {
    clear dependent i.
    clear HAB'.
      intros.
      rewrite <- Hc'j' by auto.
      f_equal.
    }
  destruct (Classical_Prop.classic
            (exists i, (i < m)%nat /\ A i j' <> 0))
    as [| CONTRA].
  { auto. }
  {
    clear dependent i.
    clear H0.
    intros i Hi.
    assert (A i j' = 0).
    {
      apply Classical_Prop.NNPP; intro; apply CONTRA.
      exists i; auto.
    }
    assert (B i j' = 0).
    {
      rewrite <- Hc'j' by auto.
      rewrite H0.
      ring.
    }
    rewrite H0, H1.
    ring.
  }
Qed.



Lemma sta_equiv_by_Mmult: forall m n (A B: Matrix m n),
  (forall v : Matrix n 1, Mmult A v ≈ Mmult B v) ->
  A ≈ B.
Proof.
  intros m n A B HAB.
  assert (forall j, (j < n)%nat -> exists c,
            Cmod c = 1 /\
            forall i, (i < m)%nat -> c * A i j = B i j)
      as HAB'.
  {
    intros j Hj.
    specialize
      (HAB (fun j' _ => if (j' =? j) && (j' <? n) then 1 else 0)).
    destruct HAB as [c [Hc HABj]]; exists c; split; auto.
    intros.
    specialize (HABj ltac:(exists i; auto)
                     ltac:(exists 0%nat; lia)).
    pose proof Mmult_1_r _ _ A
                 ltac:(exists i; auto)
                 ltac:(exists j; auto)
            as HAj.
    pose proof Mmult_1_r _ _ B
                 ltac:(exists i; auto)
                 ltac:(exists j; auto)
            as HBj.
    unfold scale in HABj.
    unfold Mmult, get, I in HABj, HAj, HBj; simpl in HABj, HAj, HBj.
    rewrite HAj, HBj in HABj.
    auto.
  }
  assert (forall j j', (j < n)%nat -> (j' < n)%nat ->
          forall x x': C,
          exists c,
            Cmod c = 1 /\
            forall i, (i < m)%nat ->
               c * (A i j * x + A i j' * x') = B i j * x + B i j' * x')
      as HAB''.
  {
    intros j j' Hj Hj' x x'.
    specialize
      (HAB (fun j'' _ => x * (if (j'' =? j) && (j'' <? n) then 1 else 0) +
                         x' * (if (j'' =? j') && (j'' <? n) then 1 else 0))).
    destruct HAB as [c [Hc HABjj']]; exists c; split; auto.
    intros i Hi.
    specialize (HABjj' ltac:(exists i; auto)
                       ltac:(exists 0%nat; lia)).
    pose proof Mmult_1_r _ _ A
                 ltac:(exists i; auto)
                 ltac:(exists j; auto)
            as HAj.
    pose proof Mmult_1_r _ _ A
                 ltac:(exists i; auto)
                 ltac:(exists j'; auto)
            as HAj'.
    pose proof Mmult_1_r _ _ B
                 ltac:(exists i; auto)
                 ltac:(exists j; auto)
            as HBj.
    pose proof Mmult_1_r _ _ B
                 ltac:(exists i; auto)
                 ltac:(exists j'; auto)
            as HBj'.
    unfold scale in HABjj'.
    unfold Mmult, get, I in HABjj', HAj, HAj', HBj, HBj';
    simpl in HABjj', HAj, HAj', HBj, HBj'.
    assert (forall K,
            (fun y : nat =>
               K y * (x * (if (y =? j) && (y <? n) then 1 else 0) +
                      x' * (if (y =? j') && (y <? n) then 1 else 0))) =
            (fun y : nat =>
               (K y * (if (y =? j) && (y <? n) then 1 else 0)) * x +
               (K y * (if (y =? j') && (y <? n) then 1 else 0)) * x')).
    {
      intros.
      apply functional_extensionality.
      intros j''.
      ring.
    }
    rewrite (Csum_eq _ _ n (H0 (A i))),
            (Csum_eq _ _ n (H0 (B i))),
            !Csum_plus, <- !Csum_mult_r,
            HAj, HAj', HBj, HBj'  in HABjj'.
    auto.
  }
  pose proof Classical_Prop.classic
               (exists i j, (i < m)%nat /\
                            (j < n)%nat /\
                            A i j <> 0)
          as [[i [j [Hi [Hj HAij]]]] | CONTRA].
  2: {
    exists 1.
    split; [autorewrite with C_db;auto | rewrite Mscale_1_l].
    intros [i Hi] [j Hj].
    unfold get; simpl.
    assert (A i j = 0).
    {
      apply Classical_Prop.NNPP.
      intro; apply CONTRA.
      exists i, j; auto.
    }
    assert (B i j = 0).
    {
      specialize (HAB' j ltac:(auto)).
      destruct HAB' as [c [_ HH]].
      specialize (HH i ltac:(auto)).
      rewrite H0 in HH.
      rewrite <- HH.
      ring.
    }
    rewrite H0, H1; reflexivity.
  }
  pose proof HAB' j Hj as [c [Hc Hcj]].
  exists c; split; auto.
  unfold scale.
  intros [i' Hi'] [j' Hj']; unfold get; simpl.
  revert i' Hi'.
  pose proof HAB' j' Hj' as [c' [Hc' Hc'j']].
  destruct (Classical_Prop.classic
            (exists i, (i < m)%nat /\
                       A i j <> 0 /\ A i j' <> 0))
    as [|].
  {
    clear dependent i.
    clear HAB'.
    assert (c/c' = 1).
    2: {
      intros.
      rewrite <- Hc'j' by auto.
      f_equal.
      rewrite <- (Cmult_1_l c').
      rewrite <- H1.
      field.
      apply mod1_not_0.
      auto.
    }
    destruct H0 as [i [Hi [HAij HAij']]].
    assert (forall x,
              Cmod (A i j * x + A i j') =
              Cmod ((c/c') * A i j * x + A i j'))
         as General.
    {
      clear HAij HAij'.
      intros x.
      specialize (HAB'' j j' ltac:(auto) ltac:(auto) x 1).
      destruct HAB'' as [k [Hk HH]].
      specialize (HH i Hi).
      transitivity (Cmod (k * (A i j * x + A i j' * 1))).
      {
        rewrite Cmod_mult.
        rewrite Hk.
        rewrite Rmult_1_l.
        f_equal.
        ring.
      }
      rewrite HH.
      rewrite <- Hcj, <- Hc'j' by auto.
      transitivity (Cmod (c' * (c / c' * A i j * x + A i j'))).
      {
        f_equal.
        field.
        apply mod1_not_0; auto.
      }
      rewrite Cmod_mult, Hc'.
      ring.
    }
    pose proof General (A i j' / A i j) as HH.
    assert (A i j * (A i j' / A i j) + A i j' = (1+1) * A i j').
    { field; auto. }
    rewrite H0 in HH; clear H0.
    assert (c / c' * A i j * (A i j' / A i j) + A i j' = (c / c' + 1) * A i j').
    { set (s:= c/c'). field; auto. }
    rewrite H0 in HH; clear H0.
    rewrite !Cmod_mult in HH.
    apply Rmult_eq_reg_r in HH.
    2: { intro. apply Cmod_eq_0 in H0. tauto. }
    clear - Hc Hc' HH.
    assert (Cmod (c/c') = 1) as Hs.
    {
      rewrite Cmod_div by (apply mod1_not_0; auto).
      rewrite Hc, Hc'; field.
    }
    set (s := c/c') in *.
    clearbody s; clear c c' Hc Hc'.
    destruct s.
    unfold C1 in HH.
    unfold Cplus in HH; simpl in HH.
    unfold Cmod in HH, Hs; simpl in HH, Hs.
    apply sqrt_inj in HH.
    2:{ nra. }
    2:{ set (rr := (r+1)%R). set (rr0 := (r0+0)%R). nra. }
    apply sqrt_lem_0 in Hs.
    2:{ nra. }
    2:{ nra. }
    ring_simplify in HH.
    ring_simplify in Hs.
    assert (r = 1)%R by lra.
    subst.
    assert (r0 ^ 2 = 0)%R by lra.
    assert (r0 = 0) by nra.
    subst.
    reflexivity.
  }
  destruct (Classical_Prop.classic
            (exists i, (i < m)%nat /\ A i j' <> 0))
    as [| CONTRA].
  {
    assert (c = c').
    2: { subst c; auto. }
    destruct H1 as [i' [Hi' HAi'j']].
    assert (A i j' = 0) as HAij'.
    {
      apply Classical_Prop.NNPP; intro; apply H0.
      exists i.
      tauto.
    }
    assert (A i' j = 0) as HAi'j.
    {
      apply Classical_Prop.NNPP; intro; apply H0.
      exists i'.
      tauto.
    }
    specialize (HAB'' j j' Hj Hj' 1 1).
    destruct HAB'' as [k [Hk HAB'']].
    pose proof HAB'' i Hi.
    pose proof HAB'' i' Hi'.
    rewrite <- Hcj in H1, H2 by auto.
    rewrite <- Hc'j' in H1, H2 by auto.
    rewrite HAij' in H1.
    rewrite HAi'j in H2.
    ring_simplify in H1.
    ring_simplify in H2.
    transitivity ((c * A i j) * (k * A i' j') / (k * A i j * A i' j')).
    {
      field.
      split; [| split]; auto.
      apply mod1_not_0; auto.
    }
    transitivity ((c' * A i' j') * (k * A i j) / (k * A i j * A i' j')).
    2: {
      field.
      split; [| split]; auto.
      apply mod1_not_0; auto.
    }
    rewrite H1, H2.
    f_equal.
    ring.
  }
  {
    clear dependent i.
    clear H0.
    intros i Hi.
    assert (A i j' = 0).
    {
      apply Classical_Prop.NNPP; intro; apply CONTRA.
      exists i; auto.
    }
    assert (B i j' = 0).
    {
      rewrite <- Hc'j' by auto.
      rewrite H0.
      ring.
    }
    rewrite H0, H1.
    ring.
  }
Qed.

