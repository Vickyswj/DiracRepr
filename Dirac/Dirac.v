Require Export Quantum.

Definition ket0 := ∣0⟩.
Definition ket1 := ∣1⟩.
Definition bra0 := ⟨0∣.
Definition bra1 := ⟨0∣.

Definition ketp := /√2 .* ∣0⟩ .+ /√2 .* ∣1⟩.
Definition ketn := /√2 .* ∣0⟩ .+ (-/√2) .* ∣1⟩.

Notation "∣+⟩" := ketp.
Notation "∣-⟩" := ketn.
Notation "⟨+∣" := ketp†.
Notation "⟨-∣" := ketn†.

Definition bell00 := /√2 .* (∣0⟩ ⊗ ∣0⟩) .+ /√2 .* (∣1⟩ ⊗ ∣1⟩).
Definition bell01 := /√2 .* (∣0⟩ ⊗ ∣1⟩) .+ /√2 .* (∣1⟩ ⊗ ∣0⟩).
Definition bell10 := /√2 .* (∣0⟩ ⊗ ∣0⟩) .+ (-/√2) .* (∣1⟩ ⊗ ∣1⟩).
Definition bell11 := /√2 .* (∣0⟩ ⊗ ∣1⟩) .+ (-/√2) .* (∣1⟩ ⊗ ∣0⟩).

Module toy_automation.

Lemma Mmult_bra0_ket0 : ⟨0∣ × ∣0⟩ = 1 .* I 1.
Proof. solve_matrix. Qed.
Lemma Mmult_bra0_ket1 : ⟨0∣ × ∣1⟩ = 0 .* I 1. (* /Zero *)
Proof. solve_matrix. Qed.
Lemma Mmult_bra1_ket0 : ⟨1∣ × ∣0⟩ = 0 .* I 1.
Proof. solve_matrix. Qed.
Lemma Mmult_bra1_ket1 : ⟨1∣ × ∣1⟩ = 1 .* I 1.
Proof. solve_matrix. Qed.

Lemma Mmult_1_l : forall (m n : nat) (A : Matrix m n), I m × A = A.
Admitted.

Lemma Mmult_1_r : forall (m n : nat) (A : Matrix m n),  A × I n = A.
Admitted.

Ltac distrubute_plus:=
repeat rewrite ?Mmult_plus_distr_r, ?Mmult_plus_distr_l,?Mscale_plus_distr_r,?kron_plus_distr_r,?kron_plus_distr_l.

Ltac isolate_scale:=
repeat rewrite ?Mscale_mult_dist_l,?Mscale_mult_dist_r,?Mscale_kron_dist_r,?Mscale_kron_dist_l,?Mscale_assoc.

Ltac reduce_scale:=
Csimpl;
repeat rewrite ?Mscale_0_l,?Mplus_0_l,?Mplus_0_r,?Cinv_sqrt2_sqrt;
auto.

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
  inversion H; subst; auto.
Qed.

Lemma mult_reduce2 : forall n m A B C x, fake_eq (@Mmult 1 n 1 A B) x -> @Mmult 1 n m A (@Mmult n 1 m B C) = @Mmult 1 1 m x C.
Proof.
  intros.
  inversion H; subst; auto.
  rewrite Mmult_assoc.
  auto.
Qed.


(* Hint Extern 1 (fake_eq (@Mmult _ _ _ _ _) _) => apply fake_eq_intro; 
    try apply Mmult_bra0_ket0; try apply Mmult_bra0_ket1; try apply Mmult_bra1_ket0; try apply Mmult_bra1_ket1: matrix_reduce.*)
    
    
(* Lemma Mmult_bra000_ket000 :(⟨0∣ ⊗ (⟨0∣ ⊗ ⟨0∣) × (∣0⟩ ⊗ (∣0⟩ ⊗ ∣0⟩))) = 1 .* I 1.
Proof.
rewrite kron_mixed_product.
rewrite kron_mixed_product.
rewrite Mmult_bra0_ket0.
isolate_scale.
repeat rewrite id_kron.
Csimpl.
reflexivity.
Qed. *)



Hint Extern 1 (fake_eq (@Mmult _ _ _ _ _) _) => apply fake_eq_intro; apply Mmult_bra0_ket0: matrix_reduce.
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
repeat rewrite ?Mmult_1_l, ?Mmult_1_r.

Lemma mult_kron_reduce1 : forall n m A B C D x,
 fake_eq (@Mmult 1 (n*m) 1 (@kron 1 n 1 m A B) (@kron n 1 m 1 C D)) x
                         -> @Mmult 1 (n*m) 1 (@kron 1 n 1 m A B)  (@kron n 1 m 1 C D) = x.
Proof.
  intros.
  inversion H; subst; auto.
Qed.

Lemma mult_kron_reduce2 : forall n m l A B C D E x,
 fake_eq (@Mmult 1 (n*m) 1 (@kron 1 n 1 m A B) (@kron n 1 m 1 C D)) x
                         -> @Mmult 1 (n*m) l (@kron 1 n 1 m A B) (@Mmult (n*m) 1 l (@kron n 1 m 1 C D) E) = @Mmult 1 1 l x E.
Proof.
  intros.
  inversion H; subst; auto.
  rewrite Mmult_assoc. auto.
Qed.

Ltac matrix_mult_kron_reduce:=
match goal with
| |-context [ @Mmult 1 (?n*?m) 1 (@kron 1 ?n 1 ?m ?A ?B) C] =>
         match C with
        | @Mmult _ _ _ _ _ => fail 1
        | @kron ?n 1 ?m 1 ?C ?D => erewrite (mult_kron_reduce1 n m A B C D); [| auto with matrix_reduce1]
         end
| |-context [ @Mmult 1 (?n*?m) ?l (@kron 1 ?n 1 ?m ?A ?B) (@Mmult (?n*?m) 1 ?l (@kron ?n 1 ?m 1 ?C ?D) ?E)] => erewrite (mult_kron_reduce2 n m l A B C D E); [| auto with matrix_reduce]
end;
isolate_scale;
repeat rewrite ?Mmult_1_l, ?Mmult_1_r.

Lemma kron_reduce1 : forall n m A B C, fake_eq (@kron 1 n 1 m A B) C -> @kron 1 n 1 m A B = C.
Proof.
  intros.
  inversion H; subst; auto.
Qed.

Lemma kron_reduce2 : forall n m l A B C D, fake_eq (@kron 1 n 1 m A B) D -> @kron 1 n 1 (m*l) A (@kron 1 m 1 l B C) = @kron 1 (n*m) 1 l D C.
Proof.
  intros.
  inversion H; subst; auto.
  Check kron_assoc.
(*   rewrite kron_assoc.
  auto.
Qed. *)
Admitted.
Lemma kron_reduce3 : forall n m l A B C D, fake_eq (@kron 1 n 1 m A B) D -> @kron 1 n 1 (m*l) A (@kron 1 m 1 l B C) = @kron 1 (n*m) 1 l D C.
Proof.
  intros.
  inversion H; subst; auto.
  Check kron_assoc.
(*   rewrite kron_assoc.
  auto.
Qed. *)
Admitted.

Ltac matrix_kron_reduce:=
match goal with
| |-context [ @kron 1 ?n 1 ?m ?A ?B] =>
         match B with
        | @kron _ _ _ _ _ _ => fail 1
        | @Mmult _ _ _ _ _ => fail 1
        | _ => erewrite (kron_reduce1 n m A B); [| auto with matrix_reduce]
        end
| |-context [ @kron 1 ?n 1 ?m ?A (@kron 1 ?l 1 ?k ?B ?C)] => erewrite (mult_reduce2 n m A B C); [| auto with matrix_reduce]
| |-context [ @kron 1 ?n 1 ?m ?A (@Mmult ?o ?p ?q ?B ?C)] => erewrite (mult_reduce2 n m A B C); [| auto with matrix_reduce]
end.
(*isolate_scale;
repeat rewrite ?Mmult_1_l, ?Mmult_1_r. *)



Lemma Mmult_bra00_ket00 :(⟨0∣ ⊗ ⟨0∣) × (∣0⟩ ⊗ ∣0⟩) = 1 .* I 1.
Proof.
(*
matrix_kron_reduce.
2:{ apply fake_eq_intro. auto. }
*)
mult_kron.
repeat matrix_mult_reduce.
rewrite id_kron.
reduce_scale.
(* solve_matrix. *) Qed.
Lemma Mmult_bra00_ket01 :(⟨0∣ ⊗ ⟨0∣) × (∣0⟩ ⊗ ∣1⟩) = 0 .* I 1.
Proof.
mult_kron.
repeat matrix_mult_reduce.
rewrite id_kron.
reduce_scale.
(* solve_matrix. *) Qed.
Lemma Mmult_bra00_ket10 :(⟨0∣ ⊗ ⟨0∣) × (∣1⟩ ⊗ ∣0⟩) = 0 .* I 1.
Proof.
mult_kron.
repeat matrix_mult_reduce.
rewrite id_kron.
reduce_scale.
(* solve_matrix. *) Qed.
Lemma Mmult_bra00_ket11 :(⟨0∣ ⊗ ⟨0∣) × (∣1⟩ ⊗ ∣1⟩) = 0 .* I 1.
Proof.
mult_kron.
repeat matrix_mult_reduce.
rewrite id_kron.
reduce_scale.
(* solve_matrix. *) Qed.
Lemma Mmult_bra01_ket00 :(⟨0∣ ⊗ ⟨1∣) × (∣0⟩ ⊗ ∣0⟩) = 0 .* I 1.
Proof.
mult_kron.
repeat matrix_mult_reduce.
rewrite id_kron.
reduce_scale.
(* solve_matrix. *) Qed.
Lemma Mmult_bra01_ket01 :(⟨0∣ ⊗ ⟨1∣) × (∣0⟩ ⊗ ∣1⟩) = 1 .* I 1.
Proof.
mult_kron.
repeat matrix_mult_reduce.
rewrite id_kron.
reduce_scale.
(* solve_matrix. *) Qed.
Lemma Mmult_bra01_ket10 :(⟨0∣ ⊗ ⟨1∣) × (∣1⟩ ⊗ ∣0⟩) = 0 .* I 1.
Proof.
mult_kron.
repeat matrix_mult_reduce.
rewrite id_kron.
reduce_scale.
(* solve_matrix. *) Qed.
Lemma Mmult_bra01_ket11 :(⟨0∣ ⊗ ⟨1∣) × (∣1⟩ ⊗ ∣1⟩) = 0 .* I 1.
Proof.
mult_kron.
repeat matrix_mult_reduce.
rewrite id_kron.
reduce_scale.
(* solve_matrix. *) Qed.
Lemma Mmult_bra10_ket00 :(⟨1∣ ⊗ ⟨0∣) × (∣0⟩ ⊗ ∣0⟩) = 0 .* I 1.
Proof.
mult_kron.
repeat matrix_mult_reduce.
rewrite id_kron.
reduce_scale.
(* solve_matrix. *) Qed.
Lemma Mmult_bra10_ket01 :(⟨1∣ ⊗ ⟨0∣) × (∣0⟩ ⊗ ∣1⟩) = 0 .* I 1.
Proof.
mult_kron.
repeat matrix_mult_reduce.
rewrite id_kron.
reduce_scale.
(* solve_matrix. *) Qed.
Lemma Mmult_bra10_ket10 :(⟨1∣ ⊗ ⟨0∣) × (∣1⟩ ⊗ ∣0⟩) = 1 .* I 1.
Proof.
mult_kron.
repeat matrix_mult_reduce.
rewrite id_kron.
reduce_scale.
(* solve_matrix. *) Qed.
Lemma Mmult_bra10_ket11 :(⟨1∣ ⊗ ⟨0∣) × (∣1⟩ ⊗ ∣1⟩) = 0 .* I 1.
Proof.
mult_kron.
repeat matrix_mult_reduce.
rewrite id_kron.
reduce_scale.
(* solve_matrix. *) Qed.

(* Lemma Mmult_bra000_ket000 : (⟨0∣ ⊗ ⟨0∣ ⊗ ⟨0∣ × (∣0⟩ ⊗ ∣0⟩ ⊗ ∣0⟩)) = 1 .* I 1.
Proof.
mult_kron.
repeat matrix_mult_reduce.
repeat rewrite id_kron.
reduce_scale.
Qed.
*)
Lemma Mmult_bra000_ket000' : (⟨0∣ ⊗ (⟨0∣ ⊗ ⟨0∣) × (∣0⟩ ⊗ (∣0⟩ ⊗ ∣0⟩))) = 1 .* I 1.
Proof.
mult_kron.
repeat matrix_mult_reduce.
repeat rewrite id_kron.
reduce_scale.
Qed.

Lemma Mmult_bra11_ket00 :(⟨1∣ ⊗ ⟨1∣) × (∣0⟩ ⊗ ∣0⟩) = 0 .* I 1.
Proof.
mult_kron.
repeat matrix_mult_reduce.
rewrite id_kron.
reduce_scale.
(* solve_matrix. *) Qed.
Lemma Mmult_bra11_ket01 :(⟨1∣ ⊗ ⟨1∣) × (∣0⟩ ⊗ ∣1⟩) = 0 .* I 1.
Proof.
mult_kron.
repeat matrix_mult_reduce.
rewrite id_kron.
reduce_scale.
(* solve_matrix. *) Qed.
Lemma Mmult_bra11_ket10 :(⟨1∣ ⊗ ⟨1∣) × (∣1⟩ ⊗ ∣0⟩) = 0 .* I 1.
Proof.
mult_kron.
repeat matrix_mult_reduce.
rewrite id_kron.
reduce_scale.
(* solve_matrix. *) Qed.
Lemma Mmult_bra11_ket11 :(⟨1∣ ⊗ ⟨1∣) × (∣1⟩ ⊗ ∣1⟩) = 1 .* I 1.
Proof.
mult_kron.
repeat matrix_mult_reduce.
rewrite id_kron.
reduce_scale.
(* solve_matrix. *) Qed.

Hint Extern 1 (fake_eq (@Mmult _ (_*_) _ (@kron _ _ _ _ _ _) (@kron _ _ _ _ _ _)) _) => apply fake_eq_intro; apply Mmult_bra00_ket00: matrix_reduce1.
Hint Extern 1 (fake_eq (@Mmult _ _ _ _ _) _) => apply fake_eq_intro; apply Mmult_bra00_ket01: matrix_reduce1.
Hint Extern 1 (fake_eq (@Mmult _ _ _ _ _) _) => apply fake_eq_intro; apply Mmult_bra00_ket10: matrix_reduce1.
Hint Extern 1 (fake_eq (@Mmult _ _ _ _ _) _) => apply fake_eq_intro; apply Mmult_bra00_ket11: matrix_reduce1.


Lemma kron_reduce1' : forall n m A B C, fake_eq (@kron 1 n 1 m A B) C -> @kron 1 n 1 m A B = C.
Proof.
  intros.
  inversion H; subst; auto.
Qed.

Lemma kron_reduce2' : forall n m l A B C D, fake_eq (@kron 1 n 1 m A B) D -> @kron 1 n 1 (m*l) A (@kron 1 m 1 l B C) = @kron 1 (n*m) 1 l D C.
Proof.
  intros.
  inversion H; subst; auto.
  Check kron_assoc.
(*   rewrite kron_assoc.
  auto.
Qed. *)
Admitted.

Ltac matrix_kron_reduce':=
match goal with
| |-context [ @kron 1 ?n 1 ?m ?A ?B] =>
         match B with
        | @kron _ _ _ _ _ => fail 1
        | _ => erewrite (kron_reduce1' n m A B); [| auto with matrix_reduce]
        end
(* | |-context [ @kron 1 ?n 1 ?m ?A (@kron 1 ?l 1 ?k ?B ?C)] => erewrite (mult_reduce2 n m A B C); [| auto with matrix_reduce] *)
end.
(*isolate_scale;
repeat rewrite ?Mmult_1_l, ?Mmult_1_r. *)

Definition H := /√2 .* ((∣0⟩ .+ ∣1⟩) × ⟨0∣ .+ (∣0⟩ .+  (-1) .* ∣1⟩) × ⟨1∣).
Definition H' := /√2 .* (∣0⟩ × ⟨0∣) .+ /√2 .* (∣0⟩ × ⟨1∣)  .+ /√2 .* (∣1⟩ × ⟨0∣) .+ (-/√2) .* (∣1⟩ × ⟨1∣).

Definition I_2 := ∣0⟩ × ⟨0∣ .+ ∣1⟩ × ⟨1∣.

Definition CNOT := (∣0⟩ ⊗ ∣0⟩) × (⟨0∣ ⊗ ⟨0∣) .+ (∣0⟩ ⊗ ∣1⟩) × (⟨0∣ ⊗ ⟨1∣)
                              .+ (∣1⟩ ⊗ ∣0⟩) × (⟨1∣ ⊗ ⟨1∣) .+ (∣1⟩ ⊗ ∣1⟩) × (⟨1∣ ⊗ ⟨0∣).

Definition state0 := (∣0⟩ ⊗ ∣0⟩).
Definition state1 := ((H ⊗ (I_2)) × state0).
Definition state2 := CNOT × state1.
Definition state3 := ketp ⊗ bell00.
Definition state4 := (CNOT ⊗ (I_2)) × (ketp ⊗ bell00).


Lemma H_ket0 : H × ∣0⟩ = (/√2 .* ∣0⟩ .+ /√2 .* ∣1⟩).
Proof.
unfold H.
distrubute_plus.
isolate_scale.
assoc_right.
(*
erewrite mult_reduce1.
2:{apply fake_eq_intro. apply Mmult_bra0_ket0. }
isolate_scale. rewrite Mmult_1_r. *)

(* rewrite Mmult_bra0_ket0. *)
repeat matrix_mult_reduce.
reduce_scale.
(*rewrite Mscale_mult_dist_l.
rewrite Mmult_plus_distr_r.
rewrite Mmult_assoc.
rewrite Mmult_bra0_ket0.
rewrite Mmult_1_r.
rewrite Mmult_assoc.
rewrite Mmult_bra1_ket0.
rewrite Mmult_0_r.
rewrite Mplus_assoc.
rewrite Mplus_0_r.
rewrite Mscale_plus_distr_r.
reflexivity.
show_wf. *)
Qed.

Lemma pre_bell00 : bell00 = state2.
Proof.
unfold state2,state1,state0,CNOT,H,I_2,bell00.
distrubute_plus.
isolate_scale.
kron_mult.
assoc_right.
(*
 matrix_kron_reduce.

erewrite mult_reduce1.
2: { apply fake_eq_intro.
erewrite mult_reduce2.
2: { apply fake_eq_intro.
apply Mmult_bra00_ket00.
}
isolate_scale.
repeat rewrite ?Mmult_1_l, ?Mmult_1_r.
auto. }
erewrite mult_reduce1.
2: { apply fake_eq_intro.
apply Mmult_bra00_ket00.
}
isolate_scale.
repeat rewrite ?Mmult_1_l, ?Mmult_1_r.
reduce_scale.
*)
mult_kron.
repeat matrix_mult_reduce.
reduce_scale.
Qed.

(*

(*                    / √ 2 * / √ 2 .* (∣0⟩ ⊗ ∣0⟩ ⊗ ∣0⟩ × (⟨0∣ ⊗ ⟨0∣ ⊗ ⟨0∣ × (∣0⟩ ⊗ ∣0⟩ ⊗ ∣0⟩))) = / 2 .* ∣ 0 , 0 , 0 ⟩ *)
Lemma vv :  / √ 2 * / √ 2 .* (∣0⟩ ⊗ ∣0⟩ ⊗ ∣0⟩ × (⟨0∣ ⊗ ⟨0∣ ⊗ ⟨0∣ × (∣0⟩ ⊗ ∣0⟩ ⊗ ∣0⟩))) = / 2 .* (∣0⟩ ⊗ ∣0⟩ ⊗ ∣0⟩).
Proof.
rewrite Mmult_bra000_ket000.
isolate_scale. rewrite Mmult_1_r. reduce_scale.
Qed.

Lemma vvv : / √ 2 * / √ 2 .* (∣0⟩ ⊗ ∣0⟩ × (⟨0∣ ⊗ ⟨0∣) ⊗ ∣0⟩⟨0∣  × (∣0⟩ ⊗ (∣0⟩ ⊗ ∣0⟩))) = /2 .* (∣0⟩ ⊗ ∣0⟩ ⊗ ∣0⟩).
Proof.
kron_mult. rewrite <- kron_assoc. mult_assoc_right.
(* rewrite vv. *)
(* rewrite <- vv. reflexivity. *)
apply vv.
Qed.

 *)

Lemma test2 : state4 = /2 .*  (∣0⟩ ⊗ ∣0⟩ ⊗ ∣0⟩) .+ /2 .*  (∣0⟩ ⊗ ∣1⟩ ⊗ ∣1⟩) .+ /2 .*  (∣1⟩ ⊗ ∣1⟩ ⊗ ∣0⟩) .+ /2 .*  (∣1⟩ ⊗ ∣0⟩ ⊗ ∣1⟩).
Proof.
unfold state4,CNOT,I_2,ketp,bell00.
distrubute_plus.
isolate_scale.
kron_mult.
assoc_right.
mult_kron.
erewrite mult_reduce1.
2:{ apply fake_eq_intro;apply Mmult_bra000_ket000'. }
isolate_scale. rewrite Mmult_1_r.
reduce_scale.
mult_kron.
repeat matrix_mult_reduce.
reduce_scale.


rewrite Mmult_bra000_ket000.


erewrite mult_reduce1.
2:{ apply fake_eq_intro;apply Mmult_bra000_ket000'. }


mult_kron.


rewrite Mmult_bra000_ket000. 


mult_assoc_right.
kron_assoc_right.

mult_kron.
matrix_kron_reduce.
(* rewrite Mmult_bra0_ket0. *)
erewrite mult_kron_reduce1.
2: {
apply fake_eq_intro; apply Mmult_bra00_ket00. }
isolate_scale. rewrite kron_1_r. 
erewrite mult_reduce1.
2: {
apply fake_eq_intro; apply Mmult_bra0_ket0. }
isolate_scale. rewrite Mmult_1_r.
reduce_scale.

}



(* Lemma dd : ∣1⟩ ⊗ (∣1⟩ ⊗ ∣1⟩) = ∣1⟩ ⊗ ∣1⟩ ⊗ ∣1⟩.
Proof. rewrite kron_assoc. auto. Qed. *)

rewrite Mmult_bra000_ket000.

repeat rewrite kron_assoc.
    mult_kron.
    
  rewrite Mmult_bra0_ket0.
      mult_kron.
    rewrite Mmult_ket0
    repeat matrix_mult_reduce.
  repeat rewrite kron_assoc.

  mult_kron.
  repeat matrix_mult_reduce.
Qed.






