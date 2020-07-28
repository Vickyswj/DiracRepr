Require Export Dirac_new.

Lemma aux_lm1:
  forall m n o (A A': Matrix m n) (B B': Matrix n o) (C: Matrix m o),
    A ≡ A' ->
    B ≡ B' ->
    Mmult A B ≡ C ->
    Mmult A' B' ≡ C.
Proof.
  intros. rewrite H, H0 in H1. auto.
Qed.

Lemma aux_lm2:
   forall m n o (A A': Matrix m n) (B B': Matrix n o) (C: Matrix m o),
     A ≡ A' ->
     B ≡ B' ->
     C ≡ Mmult A B ->
     C ≡ Mmult A' B'.
Proof.
  intros. rewrite H, H0 in H1. auto.
Qed.

Lemma aux_lm3:
  forall m n (A A': Matrix m n) (B B': Matrix m n) (C: Matrix m n),
    A ≡ A' ->
    B ≡ B' ->
    Mplus A B ≡ C ->
    Mplus A' B' ≡ C.
Proof.
  intros. rewrite H, H0 in H1. auto.
Qed.

Lemma aux_lm4:
  forall m n (A A': Matrix m n) (B B': Matrix m n) (C: Matrix m n),
    A ≡ A' ->
    B ≡ B' ->
    C ≡ Mplus A B ->
    C ≡ Mplus A' B'.
Proof.
  intros. rewrite H, H0 in H1. auto.
Qed.

Ltac apply_aux_lm2 :=
  match goal with
  | |- _ ≡ ?A × ?B => eapply aux_lm2; [ apply_aux_lm2 | apply_aux_lm2 | ]
  | _ => idtac
  end.


Ltac kron_assoc_LHS :=
  try eapply aux_lm1;
  apply_aux_lm2;
  try rewrite !kron_assoc;
  try eapply mat_equiv_refl.

Ltac kron_assoc_RHS :=
  apply_aux_lm2;
  try rewrite !kron_assoc;
  try eapply mat_equiv_refl.

Ltac mult_kron_LHS :=
  try eapply aux_lm1;
  repeat match goal with
         | |- _ ≡ ?A × ?B × ?C => eapply aux_lm2;[|eapply mat_equiv_refl|]
         | |- _ ≡ ?A × ?B => repeat mult_kron
         | |- _ ≡ _ => eapply mat_equiv_refl
         end;
  try eapply mat_equiv_refl.

Ltac mult_kron_LHS_after_assoc :=
  try eapply aux_lm1;
  repeat match goal with
         | |- _ ≡ ?A × (?B × ?C) => eapply aux_lm2;[eapply mat_equiv_refl| |]
         | |- _ ≡ ?A × ?B => repeat mult_kron
         | |- _ ≡ _ => eapply mat_equiv_refl
         end;
  try eapply mat_equiv_refl.


Lemma CX00 : CX × (∣0⟩ ⊗ ∣0⟩) ≡ ∣0⟩ ⊗ ∣0⟩.
Proof. operate_reduce. Qed.

Lemma CX10 : CX × (∣1⟩ ⊗ ∣0⟩) ≡ ∣1⟩ ⊗ ∣1⟩.
Proof. operate_reduce. Qed.
                               
Lemma e3 :
(I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ CX)
× (I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ CX ⊗ I_2)
× (I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ CX ⊗ I_2 ⊗ I_2)
× (I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ CX ⊗ I_2 ⊗ I_2 ⊗ I_2)
× (I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ CX ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2)
× (I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ CX ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2)
× (I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ CX ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2)
× (I_2 ⊗ I_2 ⊗ I_2 ⊗ CX ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2)
× (I_2 ⊗ I_2 ⊗ CX ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2)
× (I_2 ⊗ CX ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2)
× (CX ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2)
× (H ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2)
× ∣0,0,0,0,0,0,0,0,0,0,0,0⟩ 
≡  / √ 2 .* ∣0,0,0,0,0,0,0,0,0,0,0,0⟩  .+ / √ 2 .* ∣1,1,1,1,1,1,1,1,1,1,1,1⟩.
Proof.

  
  rewrite Mmult_assoc; eapply aux_lm1;
    [|rewrite <- !kron_assoc; repeat mult_kron; rewrite !Mmult_I0, !Mmult_H0;
     unfold ketp; rewrite !kron_plus_distr_r  |];
    try eapply mat_equiv_refl.

  repeat (try rewrite Mmult_assoc; eapply aux_lm1;
    [|
     rewrite ?Mmult_plus_distr_r, ?Mmult_plus_distr_l; isolate_scale;
     eapply aux_lm4;
     repeat match goal with
            | _ => mult_kron
            | _ =>
              match goal with
              | |- context[@kron ?l ?m ?n ?o (@kron ?p ?q ?r ?s ?A ?B) ?C] =>
                assert (H: @kron l m n o (@kron p q r s A B) C ≡ (A ⊗ (B ⊗ C)))
                  by (rewrite <- kron_assoc; reflexivity);
                rewrite H; clear H; simpl
              end
            end;
     rewrite ?CX00, ?CX10, ?Mmult_I0, ?Mmult_I1;
     repeat match goal with
            | |- context[@kron ?l ?m ?n ?o ?A (@kron ?p ?q ?r ?s ?B ?C)] =>
              assert (H: @kron l m n o A (@kron p q r s B C) ≡ (A ⊗ B ⊗ C))
                by (rewrite kron_assoc; reflexivity);
              rewrite H; clear H; simpl
            end
     |]; try eapply mat_equiv_refl).

  
  rewrite ?Mmult_plus_distr_r, ?Mmult_plus_distr_l; isolate_scale.
  eapply aux_lm3;
  repeat match goal with
         | _ => mult_kron
         | _ =>
           match goal with
           | |- context[@kron ?l ?m ?n ?o (@kron ?p ?q ?r ?s ?A ?B) ?C] =>
             assert (H: @kron l m n o (@kron p q r s A B) C ≡ (A ⊗ (B ⊗ C)))
               by (rewrite <- kron_assoc; reflexivity);
               rewrite H; clear H; simpl
           end
         end;
  rewrite ?CX00, ?CX10, ?Mmult_I0, ?Mmult_I1.
  all: try eapply mat_equiv_refl.
Qed.
