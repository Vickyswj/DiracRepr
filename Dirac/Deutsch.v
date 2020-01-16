Require Export Dirac.

Definition φ0 := ∣0⟩ ⊗ ∣1⟩.
Definition φ1 := (H ⊗ H) × φ0.
Definition φ2 := CX × φ1.
Definition φ3 := (H ⊗ I_2) × φ2.

Lemma step1 : φ1 ≡ ∣+⟩ ⊗ ∣-⟩.
Proof.
unfold φ1,φ0.
operate_reduce.
Qed.

Lemma step2 : φ2 ≡ ∣-⟩ ⊗ ∣-⟩.
Proof.
unfold φ2.
rewrite step1.
operate_reduce.
unified_base.
Qed.


Lemma step3 : φ3 ≡ ∣1⟩ ⊗ ∣-⟩.
Proof.
unfold φ3.
rewrite step2.
operate_reduce.
Qed.

Lemma aux: RtoC (IZR (Zneg xH)) = - (RtoC (IZR (Zpos xH))).
Proof.
  rewrite <- RtoC_opp.
  f_equal.
Qed.

Lemma move_one_side: forall n m (X Y: Matrix n m), X .+ (- (RtoC (IZR (Zpos xH)))) .* Y .+ Zero ≡ Zero -> X ≡ Y.
Proof.
  intros.
  rewrite Mplus_0_r in H.
  rewrite <- (Mplus_0_r _ _ X).
  rewrite <- (Mplus_0_l _ _ Y).
  rewrite <- (Mscale_1_l _ _ Y).
  rewrite <- H at 2.
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
  rewrite H.
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
  rewrite <- H.
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
  rewrite H, H0.
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
  linear_solver'.

Lemma tele0 : (H ⊗ I_2) × CX × (H ⊗ H) × (∣0⟩ ⊗ ∣1⟩) ≡ ∣1⟩ ⊗ ∣-⟩ .
Proof.
operate_reduce.
unified_base.
linear_solver.
Abort.
