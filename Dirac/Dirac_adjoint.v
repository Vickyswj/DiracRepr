Require Export M_notWF.


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

Notation "∣0⟩" := ket0.
Notation "∣1⟩" := ket1.
Notation "⟨0∣" := ∣0⟩†.
Notation "⟨1∣" := ∣1⟩†.
Notation "∣0⟩⟨0∣" := (∣0⟩×⟨0∣).
Notation "∣1⟩⟨1∣" := (∣1⟩×⟨1∣).
Notation "∣1⟩⟨0∣" := (∣1⟩×⟨0∣).
Notation "∣0⟩⟨1∣" := (∣0⟩×⟨1∣).


Definition bra (x : nat) : Matrix 1 2 := if x =? 0 then ⟨0∣ else ⟨1∣.
Definition ket (x : nat) : Matrix 2 1 := if x =? 0 then ∣0⟩ else ∣1⟩.

(* Note the 'mid' symbol for these *)
Notation "'∣' x '⟩'" := (ket x).
Notation "'⟨' x '∣'" := (bra x). (* This gives the Coq parser headaches *)

Notation "∣ x , y , .. , z ⟩" := (kron .. (kron ∣x⟩ ∣y⟩) .. ∣z⟩) (at level 0).

Check ∣ 1 , 0 , 0 ⟩.

(* Definition bool_to_ket (b : bool) : Matrix 2 1 := if b then ∣1⟩ else ∣0⟩.

Definition bool_to_matrix (b : bool) : Matrix 2 2 := if b then ∣1⟩⟨1∣ else ∣0⟩⟨0∣.

Lemma bool_to_ket_matrix_eq : forall b,
    outer_product (bool_to_ket b) (bool_to_ket b) = bool_to_matrix b.
Proof. unfold outer_product. destruct b; simpl; reflexivity. Qed.

Definition bools_to_matrix (l : list bool) : Square (2^(length l)) := 
  big_kron (map bool_to_matrix l).
 *)


Definition ketp := /√2 .* ∣0⟩ .+ /√2 .* ∣1⟩.
Definition brap := /√2 .* ⟨0∣ .+ /√2 .* ⟨1∣.
Definition ketn := /√2 .* ∣0⟩ .+ (-/√2) .* ∣1⟩.
Definition bran := /√2 .* ⟨0∣ .+ (-/√2) .* ⟨1∣.

Notation "∣+⟩" := ketp.
Notation "∣-⟩" := ketn.
Notation "⟨+∣" := brap.
Notation "⟨-∣" := bran.

Definition bell00 := /√2 .* (∣0⟩ ⊗ ∣0⟩) .+ /√2 .* (∣1⟩ ⊗ ∣1⟩).
Definition bell01 := /√2 .* (∣0⟩ ⊗ ∣1⟩) .+ /√2 .* (∣1⟩ ⊗ ∣0⟩).
Definition bell10 := /√2 .* (∣0⟩ ⊗ ∣0⟩) .+ (-/√2) .* (∣1⟩ ⊗ ∣1⟩).
Definition bell11 := /√2 .* (∣0⟩ ⊗ ∣1⟩) .+ (-/√2) .* (∣1⟩ ⊗ ∣0⟩).

Fixpoint ket0_n (n : nat) : Matrix (2^n) 1 :=
match n with
| 0 => I 1
| 1 => ket0
| S n' => ket0 ⊗ ket0_n n' 
end.

Hint Unfold ket0 ket1 : U_db.
Hint Unfold ketp ketn brap bran ket0_n bell00 bell01 bell10 bell11 : S_db.
Hint Unfold bell00 bell01 bell10 bell11 : Bell_db.

Ltac base_reduce :=
  autounfold with S_db;
  autounfold with U_db;
  prep_matrix_equality;
  destruct_m_eq; autorewrite with C_db;auto;
  bdestruct_all;
  try rewrite andb_false_r;
  try lca.

Lemma Mmult_bra0_ket0 : ⟨0∣ × ∣0⟩ = 1 .* I 1.
Proof. base_reduce. Qed.
Lemma Mmult_bra0_ket1 : ⟨0∣ × ∣1⟩ = 0 .* I 1. (* /Zero *)
Proof. base_reduce. Qed.
Lemma Mmult_bra1_ket0 : ⟨1∣ × ∣0⟩ = 0 .* I 1.
Proof. base_reduce. Qed.
Lemma Mmult_bra1_ket1 : ⟨1∣ × ∣1⟩ = 1 .* I 1.
Proof. base_reduce. Qed.

Lemma Mmult_brap_ketp : ⟨+∣ × ∣+⟩ = 1 .* I 1.
Proof. base_reduce. Qed.
Lemma Mmult_brap_ketn : ⟨+∣ × ∣-⟩ = 0 .* I 1. (* /Zero *)
Proof. base_reduce. Qed.
Lemma Mmult_bran_ketp : ⟨-∣ × ∣+⟩ = 0 .* I 1.
Proof. base_reduce. Qed.
Lemma Mmult_bran_ketn : ⟨-∣ × ∣-⟩ = 1 .* I 1.
Proof. base_reduce. Qed.

Lemma Mmult_bra0_ketp : ⟨0∣ × ∣+⟩ = / √ 2 .* I 1.
Proof. base_reduce. Qed.
Lemma Mmult_bra0_ketn : ⟨0∣ × ∣-⟩ = / √ 2 .* I 1.
Proof. base_reduce. Qed.
Lemma Mmult_bra1_ketp : ⟨1∣ × ∣+⟩ = / √ 2 .* I 1.
Proof. base_reduce. Qed.
Lemma Mmult_bra1_ketn : ⟨1∣ × ∣-⟩ = - / √ 2 .* I 1.
Proof. base_reduce. Qed.

Lemma Mmult_brap_ket0 : ⟨+∣ × ∣0⟩ = / √ 2 .* I 1.
Proof. base_reduce. Qed.
Lemma Mmult_brap_ket1 : ⟨+∣ × ∣1⟩ = / √ 2 .* I 1.
Proof. base_reduce. Qed.
Lemma Mmult_bran_ket0 : ⟨-∣ × ∣0⟩ = / √ 2 .* I 1.
Proof. base_reduce. Qed.
Lemma Mmult_bran_ket1 : ⟨-∣ × ∣1⟩ = - / √ 2 .* I 1.
Proof. base_reduce. Qed.

Lemma Mplus01 : ∣0⟩⟨0∣ .+ ∣1⟩⟨1∣ = I 2.
Proof. base_reduce. Qed.
Lemma Mplus10 : ∣1⟩⟨1∣ .+ ∣0⟩⟨0∣ = I 2.
Proof. base_reduce. Qed.


Hint Rewrite Mmult_bra0_ket0 Mmult_bra0_ket1 Mmult_bra1_ket0 Mmult_bra1_ket1
                         Mmult_brap_ketp Mmult_brap_ketn Mmult_bran_ketp Mmult_bran_ketn
                         Mmult_bra0_ketp Mmult_bra1_ketp Mmult_bra0_ketn Mmult_bra1_ketn
                         Mmult_brap_ket0 Mmult_brap_ket1 Mmult_bran_ket0 Mmult_bran_ket1 : S_db.

(* GATE *)

Definition B0 := ∣0⟩ × ⟨0∣.
Definition B1 := ∣0⟩ × ⟨1∣.
Definition B2 := ∣1⟩ × ⟨0∣.
Definition B3 := ∣1⟩ × ⟨1∣.

Hint Unfold B0 B1 B2 B3 : B_db.

Definition σX := B1 .+ B2.


Definition σY := - Ci .* B1 .+ Ci .* B2.
Definition σZ := B0 .+ (-1) .* B3.
Definition I_2 := B0 .+ B3.

Definition H := /√2 .* B0 .+ /√2 .* B1  .+ /√2 .* B2 .+ (-/√2) .* B3.

Fixpoint H_n (n : nat) : Matrix (2^n) (2^n):= 
  match n with
  | 0 => I 1
  | S n' => H ⊗ H_n n' 
  end.

Definition Pg (ϕ : R) := B0 .+ Cexp ϕ .* B3.
Definition PS := Pg (PI/2).
Definition PT := Pg (PI/4).
Definition PZ := Pg PI.
Definition PZn := Pg (-PI).

Lemma PS_eq : PS = B0 .+ Ci .* B3 .
Proof.
unfold PS,Pg.
autorewrite * with Cexp_db.
auto.
Qed.

Lemma PT_eq : PT = B0 .+ (/√2 + /√2 * Ci) .* B3 .
Proof.
unfold PT,Pg.
autorewrite * with Cexp_db.
auto.
Qed.

Lemma PZ_eq : PZ = σZ .
Proof.
unfold PZ,Pg.
autorewrite * with Cexp_db.
auto.
Qed.

Lemma PZn_eq : PZn = σZ .
Proof.
unfold PZn,Pg,σZ.
autorewrite * with Cexp_db.
replace (/ -1) with (Copp (RtoC 1)) by lca.
rewrite Copp_1.
auto.
Qed.

Definition M0 := B0.
Definition M1 := B3.

Definition Cg_1 {n} (A : Matrix n n) := B0 ⊗ I_2 .+ B3 ⊗ A.
Definition CX' :=  Cg_1 σX.
Definition CZ' :=  Cg_1 σZ.
Definition CS' :=  Cg_1 PS.
Definition CT' :=  Cg_1 PT.


Definition CX :=  B0 ⊗ I_2 .+ B3 ⊗ σX.
(* Definition CX :=  B0 ⊗ I 2 .+ B3 ⊗ σX. *)
Definition CZ :=  B0 ⊗ I_2 .+ B3 ⊗ σZ.

Definition XC :=  B0 ⊗ σX .+ B3 ⊗ I_2.

Lemma CX_eq : CX' = CX .
Proof. unfold CX',CX,Cg_1. auto. Qed.

Definition SWAP :=  B0 ⊗ B0 .+ B1 ⊗ B2 .+ B2 ⊗ B1 .+ B3 ⊗ B3.

Hint Unfold  σX σY σZ I_2 H M0 M1 : G1_db.
Hint Unfold  CZ CX : G2_db.

(* Hermitian *)

Definition id_sa := id_adjoint_eq.

Lemma braket0_sa : ∣0⟩⟨0∣† = ∣0⟩⟨0∣. Proof. lma. Qed.
Lemma braket1_sa : ∣1⟩⟨1∣† = ∣1⟩⟨1∣. Proof. lma. Qed.

Lemma B0_sa : B0† = B0.
Proof. base_reduce. Qed.

Lemma B1_sa : B1† = B2.
Proof. base_reduce. Qed.

Lemma B2_sa : B2† = B1.
Proof. base_reduce. Qed.

Lemma B3_sa : B3† = B3.
Proof. base_reduce. Qed.

Lemma I_sa : I_2† = I_2.
Proof. base_reduce. Qed.

Lemma H_sa : H† = H.
Proof. base_reduce. Qed.

Lemma σX_sa : σX† = σX.
Proof. base_reduce. Qed.

Lemma σY_sa : σY† = σY.
Proof. base_reduce. Qed.

Lemma σZ_sa : σZ† = σZ.
Proof. base_reduce. Qed.

Lemma CX_sa : CX† = CX.
Proof. base_reduce. Qed.

Hint Rewrite B0_sa B1_sa B2_sa B3_sa I_sa H_sa σX_sa σY_sa σZ_sa CX_sa
             braket0_sa braket1_sa : A_db.


(* Unitary *)

Lemma MmultII : I_2 × I_2 = I_2.
Proof. base_reduce. Qed.
Lemma MmultXII' : I_2 × I_2 = I 2.
Proof. rewrite MmultII. apply Mplus01. Qed.

Lemma MmultXX : σX × σX = I_2.
Proof. base_reduce. Qed.
Lemma MmultXX' : σX × σX = I 2.
Proof. rewrite MmultXX. apply Mplus01. Qed.

Lemma MmultYY : σY × σY = I_2.
Proof. base_reduce. Qed.
Lemma MmultYY' : σY × σY = I 2.
Proof. rewrite MmultYY. apply Mplus01. Qed.

Lemma MmultZZ : σZ × σZ = I_2.
Proof. base_reduce. Qed.
Lemma MmultZZ' : σZ × σZ = I 2.
Proof. rewrite MmultZZ. apply Mplus01. Qed.


(*BaseGate_reduce *)
Lemma Mmult_B00 : B0 × ∣0⟩ = ∣0⟩.
Proof. base_reduce. Qed.
Lemma Mmult_0B0 : ⟨0∣ × B0 = ⟨0∣.
Proof. base_reduce. Qed.
Lemma Mmult_0B0' : (B0 × ∣0⟩)† = ∣0⟩†.
Proof. base_reduce. Qed.

(* Lemma Mmult_B01 : B0 × ∣1⟩ = @Zero 2 1. *)
Lemma Mmult_B01 : B0 × ∣1⟩ = Zero.
Proof. base_reduce. Qed.
Lemma Mmult_1B0 : ⟨1∣ × B0 = Zero.
Proof. base_reduce. Qed.

Lemma Mmult_B0pos : B0 × ∣+⟩ = / √ 2 .* ∣0⟩.
Proof. base_reduce. Qed.
Lemma Mmult_posB0 : ⟨+∣ × B0 = / √ 2 .* ⟨0∣.
Proof. base_reduce. Qed.

Lemma Mmult_B0neg : B0 × ∣-⟩ = / √ 2 .* ∣0⟩.
Proof. base_reduce. Qed.
Lemma Mmult_negB0 : ⟨-∣ × B0 = / √ 2 .* ⟨0∣.
Proof. base_reduce. Qed.

Lemma Mmult_B10 : B1 × ∣0⟩ = Zero.
Proof. base_reduce. Qed.
Lemma Mmult_0B1 : ⟨0∣ × B1 = ⟨1∣.
Proof. base_reduce.  Qed.

Lemma Mmult_B11 : B1 × ∣1⟩ = ∣0⟩.
Proof. base_reduce. Qed.
Lemma Mmult_1B1 : ⟨1∣ × B1 = Zero.
Proof. base_reduce.  Qed.

Lemma Mmult_B1pos : B1 × ∣+⟩ = / √ 2 .* ∣0⟩.
Proof. base_reduce. Qed.
Lemma Mmult_posB1 : ⟨+∣ × B1 = / √ 2 .* ⟨1∣.
Proof. base_reduce.  Qed.

Lemma Mmult_B1neg : B1 × ∣-⟩ = - / √ 2 .* ∣0⟩.
Proof. base_reduce. Qed.
Lemma Mmult_negB1 : ⟨-∣ × B1 = / √ 2 .* ⟨1∣.
Proof. base_reduce.  Qed.

Lemma Mmult_B20 : B2 × ∣0⟩ = ∣1⟩.
Proof. base_reduce. Qed.
Lemma Mmult_0B2 : ⟨0∣ × B2 = Zero.
Proof. base_reduce.  Qed.

Lemma Mmult_B21 : B2 × ∣1⟩ = Zero.
Proof. base_reduce. Qed.
Lemma Mmult_1B2 : ⟨1∣ × B2 = ⟨0∣.
Proof. base_reduce.  Qed.

Lemma Mmult_B2pos : B2 × ∣+⟩ = / √ 2 .* ∣1⟩.
Proof. base_reduce. Qed.
Lemma Mmult_posB2 : ⟨+∣ × B2 =/ √ 2 .* ⟨0∣.
Proof. base_reduce.  Qed.

Lemma Mmult_B2neg : B2 × ∣-⟩ = / √ 2 .* ∣1⟩.
Proof. base_reduce. Qed.
Lemma Mmult_negB2 : ⟨-∣ × B2 = - / √ 2 .* ⟨0∣.
Proof. base_reduce.  Qed.


Lemma Mmult_B30 : B3 × ∣0⟩ = Zero.
Proof. base_reduce. Qed.
Lemma Mmult_0B3 : ⟨0∣ × B3 = Zero.
Proof. base_reduce.  Qed.

Lemma Mmult_B31 : B3 × ∣1⟩ = ∣1⟩.
Proof. base_reduce. Qed.
Lemma Mmult_1B3 : ⟨1∣ × B3 = ⟨1∣.
Proof. base_reduce.  Qed.

Lemma Mmult_B3pos : B3 × ∣+⟩ = / √ 2 .* ∣1⟩.
Proof. base_reduce. Qed.
Lemma Mmult_posB3 : ⟨+∣ × B3 = / √ 2 .* ⟨1∣.
Proof. base_reduce.  Qed.

Lemma Mmult_B3neg : B3 × ∣-⟩ = - / √ 2 .* ∣1⟩.
Proof. base_reduce. Qed.
Lemma Mmult_negB3 : ⟨-∣ × B3 = - / √ 2 .* ⟨1∣.
Proof. base_reduce.  Qed.

(* Hint Rewrite Mmult_B01 Mmult_B10 Mmult_B21 Mmult_B30 : B0_db. *)
Hint Rewrite Mmult_B00 Mmult_B01 Mmult_B0pos Mmult_B0neg
                         Mmult_B10 Mmult_B11 Mmult_B1pos Mmult_B1neg
                         Mmult_B20 Mmult_B21 Mmult_B2pos Mmult_B2neg
                         Mmult_B30 Mmult_B31 Mmult_B3pos Mmult_B3neg
(*                          
                         Mmult_0B0 Mmult_1B0 Mmult_posB0 Mmult_negB0
                         Mmult_0B1 Mmult_1B1 Mmult_posB1 Mmult_negB1
                         Mmult_0B2 Mmult_1B2 Mmult_posB2 Mmult_negB2
                         Mmult_0B3 Mmult_1B3 Mmult_posB3 Mmult_negB3 *) : B_db.




Lemma Mmult_I0 : I_2 × ∣0⟩ = ∣0⟩.
Proof. base_reduce. Qed.
Lemma Mmult_0I : ⟨0∣ × I_2 = ⟨0∣.
Proof. base_reduce.  Qed.

Lemma Mmult_I1 : I_2 × ∣1⟩ = ∣1⟩.
Proof. base_reduce. Qed.
Lemma Mmult_1I : ⟨1∣ × I_2 = ⟨1∣.
Proof. base_reduce.  Qed.

Lemma Mmult_Ipos : I_2 × ∣+⟩ = ∣+⟩.
Proof. base_reduce. Qed.
Lemma Mmult_posI : ⟨+∣ × I_2 = ⟨+∣.
Proof. base_reduce.  Qed.

Lemma Mmult_Ineg : I_2 × ∣-⟩ = ∣-⟩.
Proof. base_reduce. Qed.
Lemma Mmult_negI : ⟨-∣ × I_2 = ⟨-∣.
Proof. base_reduce.  Qed.

Lemma Mmult_σX0 : σX × ∣0⟩ = ∣1⟩.
Proof. base_reduce. Qed.
Lemma Mmult_0σX : ⟨0∣ × σX = ⟨1∣.
Proof. base_reduce.  Qed.

Lemma Mmult_σX1 : σX × ∣1⟩ = ∣0⟩.
Proof. base_reduce. Qed.
Lemma Mmult_1σX : ⟨1∣ × σX = ⟨0∣.
Proof. base_reduce.  Qed.

Lemma Mmult_σXpos : σX × ∣+⟩ = ∣+⟩.
Proof. base_reduce. Qed.
Lemma Mmult_posσX : ⟨+∣ × σX = ⟨+∣.
Proof. base_reduce.  Qed.

Lemma Mmult_σXneg : σX × ∣-⟩ = -1 .* ∣-⟩.
Proof. base_reduce. Qed.
Lemma Mmult_negσX : ⟨-∣ × σX = -1 .* ⟨-∣.
Proof. base_reduce.  Qed.

Lemma σx_on_right0 : forall (q : Vector 2), (q × ⟨0∣) × σX = q × ⟨1∣.
Proof. intros. rewrite Mmult_assoc, Mmult_0σX. reflexivity. Qed.

Lemma Mmult_σZ0 : σZ × ∣0⟩ = ∣0⟩.
Proof. base_reduce. Qed.
Lemma Mmult_0σZ : ⟨0∣ × σZ = ⟨0∣.
Proof. base_reduce.  Qed.

Lemma Mmult_σZ1 : σZ × ∣1⟩ = -1 .* ∣1⟩.
Proof. base_reduce. Qed.
Lemma Mmult_1σZ : ⟨1∣ × σZ = -1 .* ⟨1∣.
Proof. base_reduce.  Qed.

Lemma Mmult_σZpos : σZ × ∣+⟩ = ∣-⟩.
Proof. base_reduce. Qed.
Lemma Mmult_posσZ : ⟨+∣ × σZ = ⟨-∣.
Proof. base_reduce.  Qed.

Lemma Mmult_σZneg : σZ × ∣-⟩ = ∣+⟩.
Proof. base_reduce. Qed.
Lemma Mmult_negσZ : ⟨-∣ × σZ = ⟨+∣.
Proof. base_reduce.  Qed.

Lemma Mmult_σY0 : σY × ∣0⟩ = Ci .* ∣1⟩.
Proof. base_reduce. Qed.
Lemma Mmult_0σY : ⟨0∣ × σY = -Ci .* ⟨1∣.
Proof. base_reduce.  Qed.

Lemma Mmult_σY1 : σY × ∣1⟩ = -Ci .* ∣0⟩.
Proof. base_reduce. Qed.
Lemma Mmult_1σY : ⟨1∣ × σY = Ci .* ⟨0∣.
Proof. base_reduce.  Qed.

Lemma Mmult_σYpos : σY × ∣+⟩ = -Ci .* ∣-⟩.
Proof. base_reduce. Qed.
Lemma Mmult_posσY : ⟨+∣ × σY = Ci .* ⟨-∣.
Proof. base_reduce.  Qed.

Lemma Mmult_σYneg : σY × ∣-⟩ = Ci .* ∣+⟩.
Proof. base_reduce. Qed.
Lemma Mmult_negσY : ⟨-∣ × σY = -Ci .* ⟨+∣.
Proof. base_reduce.  Qed.


Lemma Mmult_H0 : H × ∣0⟩ = ∣+⟩.
Proof. base_reduce. Qed.
Lemma Mmult_0H : ⟨0∣ × H = ⟨+∣.
Proof. base_reduce. Qed.

Lemma Mmult_H1 : H × ∣1⟩ = ∣-⟩.
Proof. base_reduce. Qed.
Lemma Mmult_1H : ⟨1∣ × H = ⟨-∣.
Proof. base_reduce. Qed.

(* Lemma y :/ 2 .* ∣0⟩ .+ / 2 .* ∣1⟩ .+ -/ 2 .* ∣1⟩ .+ / 2 .* ∣0⟩ = ∣0⟩ .
Proof.

Qed. *)

Lemma Mmult_Hpos : H × ∣+⟩ = ∣0⟩.
Proof.
unfold H.
autounfold with B_db.
base_reduce. Qed.
Lemma Mmult_posH : ⟨+∣ × H = ⟨0∣.
Proof.
unfold H.
autounfold with B_db.
base_reduce. Qed.

Lemma Mmult_Hneg : H × ∣-⟩ = ∣1⟩.
Proof.
unfold H.
autounfold with B_db.
base_reduce. Qed.
Lemma Mmult_negH : ⟨-∣ × H = ⟨1∣.
Proof.
unfold H.
autounfold with B_db.
base_reduce. Qed.


Lemma Mmult_M00 : M0 × ∣0⟩ = ∣0⟩.
Proof. base_reduce. Qed.
Lemma Mmult_0M0 : ⟨0∣ × M0 = ⟨0∣.
Proof. base_reduce. Qed.

(* Lemma Mmult_M01 : M0 × ∣1⟩ = @Zero 2 1. *)
Lemma Mmult_M01 : M0 × ∣1⟩ = Zero.
Proof. base_reduce. Qed.
Lemma Mmult_1M0 : ⟨1∣ × M0 = Zero.
Proof. base_reduce. Qed.

Lemma Mmult_M0pos : M0 × ∣+⟩ = / √ 2 .* ∣0⟩.
Proof. base_reduce. Qed.
Lemma Mmult_posM0 : ⟨+∣ × M0 = / √ 2 .* ⟨0∣.
Proof. base_reduce. Qed.

Lemma Mmult_M0neg : M0 × ∣-⟩ = / √ 2 .* ∣0⟩.
Proof. base_reduce. Qed.
Lemma Mmult_negM0 : ⟨-∣ × M0 = / √ 2 .* ⟨0∣.
Proof. base_reduce. Qed.


Lemma Mmult_M10 : M1× ∣0⟩ = Zero.
Proof. base_reduce. Qed.
Lemma Mmult_0M1 : ⟨0∣ × M1 = Zero.
Proof. base_reduce. Qed.


Lemma Mmult_M11 : M1 × ∣1⟩ = ∣1⟩.
Proof. base_reduce. Qed.
Lemma Mmult_1M1 : ⟨1∣ × M1 = ⟨1∣.
Proof. base_reduce. Qed.


Lemma Mmult_M1pos : M1 × ∣+⟩ = / √ 2 .* ∣1⟩.
Proof. base_reduce. Qed.
Lemma Mmult_posM1 : ⟨+∣ × M1 = / √ 2 .* ⟨1∣.
Proof. base_reduce. Qed.


Lemma Mmult_M1neg : M1 × ∣-⟩ = -/ √ 2 .* ∣1⟩.
Proof. base_reduce. Qed.
Lemma Mmult_negM1 : ⟨-∣ × M1 = -/ √ 2 .* ⟨1∣.
Proof. base_reduce. Qed.


Hint Rewrite Mmult_I0 Mmult_I1 Mmult_Ipos Mmult_Ineg
                         Mmult_σX0 Mmult_σX1 Mmult_σXpos Mmult_σXneg
                         Mmult_σZ0 Mmult_σZ1 Mmult_σZpos Mmult_σZneg
                         Mmult_σY0 Mmult_σY1
                         Mmult_H0 Mmult_H1 Mmult_Hpos Mmult_Hneg
                         Mmult_M00 Mmult_M01 Mmult_M0pos Mmult_M0neg
                         Mmult_M10 Mmult_M11 Mmult_M1pos Mmult_M1neg
(*                          
                         Mmult_0I Mmult_1I Mmult_posI Mmult_negI
                         Mmult_0σX Mmult_1σX Mmult_posσX Mmult_negσX
                         Mmult_0σZ Mmult_1σZ Mmult_posσZ Mmult_negσZ
                         Mmult_0σY Mmult_1σY Mmult_posσY Mmult_negσY
                         Mmult_0H Mmult_1H Mmult_Hpos Mmult_negH
                         Mmult_0M0 Mmult_1M0 Mmult_posM0 Mmult_negM0
                         Mmult_0M1 Mmult_1M1 Mmult_posM1 Mmult_negM1 *)
                       : G1_db.



(* Lemma CX00 : CX × (∣0⟩ ⊗ ∣0⟩) = ∣0⟩ ⊗ ∣0⟩.
Proof.
autounfold with G2_db G1_db B_db.
Mmult_reduce.
Qed.

Lemma CX01 : CX × (∣0⟩ ⊗ ∣1⟩) = ∣0⟩ ⊗ ∣1⟩.
Proof.
autounfold with G2_db G1_db B_db.
Mmult_reduce.
Qed.

Lemma CX10 : CX × (∣1⟩ ⊗ ∣0⟩) = ∣1⟩ ⊗ ∣1⟩.
Proof.
autounfold with G2_db G1_db B_db.
Mmult_reduce.
Qed.

Lemma CX11 : CX × (∣1⟩ ⊗ ∣1⟩) = ∣1⟩ ⊗ ∣0⟩.
Proof.
autounfold with G2_db G1_db B_db.
Mmult_reduce.
Qed.

Lemma CXp0 : CX × (∣+⟩ ⊗ ∣0⟩) = /√2 .* (∣0⟩ ⊗ ∣0⟩) .+ /√2 .* (∣1⟩ ⊗ ∣1⟩).
Proof.
autounfold with G2_db G1_db B_db.
Mmult_reduce.
Qed.

Lemma CXp1 : CX × (∣+⟩ ⊗ ∣1⟩) = /√2 .* (∣0⟩ ⊗ ∣1⟩) .+ /√2 .* (∣1⟩ ⊗ ∣0⟩).
autounfold with G2_db G1_db B_db.
Mmult_reduce.
Qed.

Hint Rewrite CX00 CX01 CX10 CX11
                         CXp0 CXp1 : G2_db. *)


(* Lemma Mmult_1_l : forall (m n : nat) (A : Matrix m n), I m × A = A.
Admitted.

Lemma Mmult_1_r : forall (m n : nat) (A : Matrix m n),  A × I n = A.
Admitted. *)

Ltac distrubute_plus:=
repeat rewrite ?Mmult_plus_distr_r, ?Mmult_plus_distr_l,?Mscale_plus_distr_r,?kron_plus_distr_r,?kron_plus_distr_l.

Ltac isolate_scale:=
repeat rewrite ?Mscale_mult_dist_l,?Mscale_mult_dist_r,?Mscale_kron_dist_r,?Mscale_kron_dist_l,?Mscale_assoc.

Ltac assoc_right:=
repeat rewrite ?Mmult_assoc, ?kron_assoc.

Ltac kron_mult:=
repeat rewrite <- kron_mixed_product.


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

Lemma Mmult_1_l : forall (m n : nat) (A : Matrix m n), I m × A = A.
Admitted.

Lemma Mmult_1_r : forall (m n : nat) (A : Matrix m n),  A × I n = A.
Admitted.

(* Ltac Mmult_1 :=
  match goal with
  | |- context  [@Mmult ?m1 ?n1 ?n1 ?A (@I ?n2)] =>
             change  (@Mmult m1 n1 n1 A (@I n2))  with
                           (@Mmult m1 n1 n1 A (@I n2));
             rewrite (@Mmult_1_r m1 n1 A)
  | |- context  [@Mmult ?m1 ?m1 ?o1 (@I ?m2) ?A] =>
             change  (@Mmult m1 m1 o1 (@I m2) A)  with
                           (@Mmult m1 m1 o1 (@I m1) A);
             rewrite (@Mmult_1_l  m1 m1 A)
  end. *)

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
(* repeat Mmult_1. *)
repeat rewrite ?Mmult_1_l, ?Mmult_1_r.


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

Ltac normalize := distrubute_plus; isolate_scale; assoc_right.
(**********************************************************)

Ltac reduce_scale:=
autorewrite with C_db;
repeat rewrite ?Mscale_0_l,?Mscale_1_l;
repeat cancel_0;
try rewrite Cmult_comm;
repeat cancel_common_factor;
auto.

Ltac Mmult_reduce :=
distrubute_plus;
isolate_scale;
kron_mult;
assoc_right;
repeat mult_reduce;
reduce_scale.


(* (* (* Lemma pp : I 1  × (⟨0∣ ⊗ (⟨0∣ ⊗ ⟨0∣)) = ⟨0∣ ⊗ (⟨0∣ ⊗ ⟨0∣) .
Proof. rewrite Mmult_1_l. M *) *) *)


(* Lemma CX00 : CX × (∣0⟩ ⊗ ∣0⟩) = ∣0⟩ ⊗ ∣0⟩.
Proof.
autounfold with G2_db G1_db B_db.
Mmult_reduce.
Qed.

Lemma CX01 : CX × (∣0⟩ ⊗ ∣1⟩) = ∣0⟩ ⊗ ∣1⟩.
Proof.
autounfold with G2_db G1_db B_db.
Mmult_reduce.
Qed.

Lemma CX10 : CX × (∣1⟩ ⊗ ∣0⟩) = ∣1⟩ ⊗ ∣1⟩.
Proof.
autounfold with G2_db G1_db B_db.
Mmult_reduce.
Qed.

Lemma CX11 : CX × (∣1⟩ ⊗ ∣1⟩) = ∣1⟩ ⊗ ∣0⟩.
Proof.
autounfold with G2_db G1_db B_db.
Mmult_reduce.
Qed.

Lemma CXp0 : CX × (∣+⟩ ⊗ ∣0⟩) = /√2 .* (∣0⟩ ⊗ ∣0⟩) .+ /√2 .* (∣1⟩ ⊗ ∣1⟩).
Proof.
autounfold with G2_db G1_db B_db.
Mmult_reduce.
Qed.

Lemma CXp1 : CX × (∣+⟩ ⊗ ∣1⟩) = /√2 .* (∣0⟩ ⊗ ∣1⟩) .+ /√2 .* (∣1⟩ ⊗ ∣0⟩).
autounfold with G2_db G1_db B_db.
Mmult_reduce.
Qed.

Hint Rewrite CX00 CX01 CX10 CX11
                         CXp0 CXp1 : G2_db. *)



Ltac rewrite_gate :=
autorewrite with B_db G1_db;
isolate_scale.

Ltac gate_reduce :=
distrubute_plus;
isolate_scale;
assoc_right;
repeat mult_kron;
repeat rewrite_gate;
reduce_scale.


Notation Density n := (Matrix n n) (only parsing).

Definition Classical {n} (ρ : Density n) := forall i j, i <> j -> ρ i j = 0.

Definition Pure_State_Vector' {n} (φ : Vector n): Prop := φ† × φ ≡ I  1.
Definition Pure_State_Vector {n} (φ : Vector n): Prop := φ† × φ = I  1.


Definition Pure_State' {n} (ρ : Density n) : Prop := exists φ, Pure_State_Vector' φ /\ ρ ≡ φ × φ†.
Definition Pure_State {n} (ρ : Density n) : Prop := exists φ, Pure_State_Vector φ /\ ρ = φ × φ†.

Inductive Mixed_State {n} : Matrix n n -> Prop :=
| Pure_S : forall ρ, Pure_State' ρ -> Mixed_State ρ
| Mix_S : forall (p : R) ρ1 ρ2, 0 < p < 1 -> Mixed_State ρ1 -> Mixed_State ρ2 ->
                                       Mixed_State (p .* ρ1 .+ (1-p)%R .* ρ2).


Lemma pure0 : Pure_State' ∣0⟩⟨0∣.
Proof.
exists ∣0⟩. intuition. 
unfold Pure_State_Vector'.
rewrite Mmult_bra0_ket0.
rewrite Mscale_1_l.
reflexivity.
Qed.

Lemma pure1 : Pure_State' ∣1⟩⟨1∣.
Proof.
exists ∣1⟩. intuition. 
unfold Pure_State_Vector'.
rewrite Mmult_bra1_ket1.
rewrite Mscale_1_l.
reflexivity.
Qed.


Lemma pure_id1 : Pure_State' (I  1).
Proof.
 exists (I  1).
 unfold Pure_State_Vector'. split;
 rewrite id_adjoint_eq; rewrite Mmult_1_l; reflexivity.
Qed.

Lemma pure_dim1 : forall (ρ : Square 1), Pure_State' ρ -> ρ ≡ I  1.
Proof.
  intros ρ [φ [ IP1 Eρ]].
  unfold Pure_State_Vector' in IP1.
  apply Minv_flip in IP1.
  rewrite Eρ; easy.
Qed.

(* Lemma mixed_dim1 : forall (ρ : Square 1), Mixed_State ρ -> ρ ≡ I  1.
Proof.
  intros.  
  induction H0.
  + apply pure_dim1. trivial.
  + rewrite IHMixed_State1, IHMixed_State2.
    prep_matrix_equality.
    lca.
Qed.   *)


Lemma pure_state_kron : forall m n (ρ : Square m) (φ : Square n),
  Pure_State' ρ -> Pure_State' φ -> Pure_State' (ρ ⊗ φ).
Proof.
  intros m n ρ φ [u [Pu Eρ]] [v [Pv Eφ]].
  exists (u ⊗ v).
  split.
  - unfold Pure_State_Vector' in *.
Admitted.
(*     rewrite (kron_adjoint u v).
     replace (S O) with (S O * S O)%nat by reflexivity.
    apply WF_kron; auto.
  - Msimpl. rewrite Pv, Pu. Msimpl. easy.
  - Msimpl. subst. easy.
Qed. *)

Lemma mixed_state_kron : forall m n (ρ : Square m) (φ : Square n),
  Mixed_State ρ -> Mixed_State φ -> Mixed_State (ρ ⊗ φ).
Proof.
  intros m n ρ φ Mρ Mφ.
  induction Mρ.
  induction Mφ.
  - apply Pure_S. apply pure_state_kron; easy.
  - rewrite kron_plus_distr_l.
    rewrite 2 Mscale_kron_dist_r.
    apply Mix_S; easy.
  - rewrite kron_plus_distr_r.
    rewrite 2 Mscale_kron_dist_l.
    apply Mix_S; easy.
Qed.


Lemma pure_state_trace_1 : forall {n} (ρ : Density n), Pure_State' ρ -> trace ρ = 1.
Proof.
  intros n ρ [u [Uu E]].
  unfold Pure_State_Vector' in Uu.
Admitted.
(*   rewrite E.
  subst.
  clear -Uu.
  unfold trace.
  simpl in *.
  match goal with
    [H : ?f = ?g |- _] => assert (f O O = g O O) by (rewrite <- H; easy)
  end.
  unfold I in H0; simpl in H0.
  rewrite <- H0.
  apply Csum_eq.
  apply functional_extensionality.
  intros x.
  rewrite Cplus_0_l, Cmult_comm.
  easy.
Qed. *)

Lemma mixed_state_trace_1 : forall {n} (ρ : Density n), Mixed_State ρ -> trace ρ = 1.
Proof.
  intros n ρ H. 
  induction H. 
  - apply pure_state_trace_1. easy.
  - rewrite trace_plus_dist.
    rewrite 2 trace_mult_dist.
    rewrite IHMixed_State1, IHMixed_State2.
    lca.
Qed.


Definition Superoperator m n := Density m -> Density n.

Definition WF_Superoperator {m n} (f : Superoperator m n) := 
  (forall ρ, Mixed_State ρ -> Mixed_State (f ρ)).

Definition super {m n} (M : Matrix m n) : Superoperator n m := fun ρ => 
  M × ρ × M†.


Ltac super_reduce1:=
match goal with
| |-context [ @Mmult ?n ?m ?n (@Mmult ?n ?m ?m ?A ?B) (@adjoint ?n ?m ?A)] =>
     match B with
    | @Mmult ?m ?one ?m ?C (@adjoint ?m ?one ?C) => 
         transitivity (@Mmult n one n (@Mmult n m one A C) (@Mmult one m m (@adjoint m one C) (@adjoint n m A)))
     end
end;
repeat rewrite <- Mmult_assoc; auto.

Ltac super_reduce2:=
rewrite Mmult_assoc;
rewrite <- Mmult_adjoint;
match goal with
| |-context [ @Mmult ?n ?one ?n (@Mmult ?n ?m ?one ?A ?B) (@adjoint ?n ?one ?C) = @Mmult ?n ?one ?n ?D (@adjoint ?n ?one ?D)] =>
    match C with
    | @Mmult ?n ?m ?one ?A ?B=> assert (@Mmult n m one A B = D) as H
    end
end.

Ltac super_reduce:=
super_reduce1;
super_reduce2.

Ltac adjoint_tras:=
repeat rewrite ?Mplus_adjoint, ?Mmult_adjoint, ?kron_adjoint.

Definition ρ0 := (∣0⟩ ⊗ ∣0⟩) × (∣0⟩ ⊗ ∣0⟩)†.
Lemma tt : super CX ρ0 =  (∣0⟩ ⊗ ∣0⟩) × (∣0⟩ ⊗ ∣0⟩)†.
Proof.
unfold super,CX,ρ0.
super_reduce.
gate_reduce.
rewrite H. auto.
Qed.

Lemma nn : super H (∣0⟩ × ∣0⟩†) = ∣+⟩ × ∣+⟩† .
Proof.
unfold super.
super_reduce.
gate_reduce.
rewrite H. auto.
Qed.



(* Definition ρ0 := (∣0⟩ ⊗ ∣0⟩) × (∣0⟩ ⊗ ∣0⟩)†.
Lemma tt : super CX ρ0 =  (∣0⟩ ⊗ ∣0⟩) × (∣0⟩ ⊗ ∣0⟩)†.
Proof.
unfold super,CX,ρ0.
transitivity (((B0 ⊗ I_2 .+ B3 ⊗ σX) × (∣0⟩ ⊗ ∣0⟩)) × ((∣0⟩ ⊗ ∣0⟩) † × (B0 ⊗ I_2 .+ B3 ⊗ σX) †)).
{ repeat rewrite <- Mmult_assoc.
  auto.
}
rewrite <- Mmult_adjoint.
assert ((B0 ⊗ I_2 .+ B3 ⊗ σX) × (∣0⟩ ⊗ ∣0⟩) = ∣0⟩ ⊗ ∣0⟩) as HH; [| rewrite HH; auto].
gate_reduce.
Qed.


Lemma nn : super H (∣0⟩ × ∣0⟩†) = ∣+⟩ × ∣+⟩† .
Proof.
unfold super.
transitivity (H × ∣0⟩ × (∣0⟩† × H †)) .
{ repeat rewrite <- Mmult_assoc.
auto. }
rewrite <- Mmult_adjoint.
assert ((H × ∣0⟩) = ∣+⟩) as HH; [| rewrite HH; auto].
gate_reduce.
Qed. *)

Lemma gg : (CX ⊗ I_2) × (∣0⟩ ⊗ ∣0⟩ ⊗ ∣0⟩) = (∣0⟩ ⊗ ∣0⟩ ⊗ ∣0⟩) .
Proof.
unfold CX.
gate_reduce.
Qed.

Lemma ggg : (CX ⊗ I_2) × (CX ⊗ I_2) × (∣0⟩ ⊗ ∣0⟩ ⊗ ∣0⟩) = (∣0⟩ ⊗ ∣0⟩ ⊗ ∣0⟩) .
Proof.
unfold CX at 2.
gate_reduce.
unfold CX.
gate_reduce.
Qed.

