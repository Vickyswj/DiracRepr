Require Export Dirac.

Lemma t10 :
(I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2)×∣0,0,0,0,0,0,0,0,0,0,0,0,0,0⟩
  ≡ ∣0,0,0,0,0,0,0,0,0,0,0,0⟩.
Proof.
  Time repeat rewrite kron_assoc.
Admitted.
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
Time assoc_right.
Time repeat mult_kron.
rewrite Mmult_I0,Mmult_H0. repeat cancel_0.
Admitted.


Definition TOF := B0 ⊗ I_2 ⊗ I_2 .+ B3 ⊗ CX.


Ltac kron_plus_distr:=
repeat rewrite ?kron_plus_distr_r,?kron_plus_distr_l.

Ltac Mmult_plus_distr:=
repeat rewrite ?Mmult_plus_distr_r, ?Mmult_plus_distr_l.

Ltac unfold_gate M :=
match M with
| ?A × ?B=>
(*idtac B;*)
unfold_gate B
| @Mmult ?m ?n ?o ?A ?B =>
idtac A B;
set (ol :=M);
autounfold with Gn_db in ol;
subst ol
end.

Ltac unfold_operator :=
match goal with 
 | [ |- ?M ≡ _] => unfold_gate M
end.


Ltac tactic1 :=
unfold_operator;
kron_plus_distr;
assoc_right;
try rewrite Mmult_plus_distr_l;
try repeat rewrite Mmult_plus_distr_r;
isolate_scale;
repeat mult_kron;
try rewrite Mmult_I0,Mmult_H0;
try rewrite Mmult_I0,Mmult_σX0,Mmult_B0pos,Mmult_B3pos;
try rewrite Mmult_B30,Mmult_B01; repeat cancel_0;
try rewrite Mmult_I0,Mmult_I1,Mmult_σX0,Mmult_B31,Mmult_B00;
(* repeat (autorewrite with G1_db;
isolate_scale); *)
reduce_scale.

Lemma t10 :
(* (I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ CX)
× (I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ CX ⊗ I_2)
× (I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ I_2 ⊗ CX ⊗ I_2 ⊗ I_2)*)
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
Time assoc_right.
repeat tactic1.



unfold_operator;
kron_plus_distr;
assoc_right;
try rewrite Mmult_plus_distr_l;
try repeat rewrite Mmult_plus_distr_r;
isolate_scale;
repeat mult_kron;
try rewrite Mmult_I0,Mmult_H0;
try rewrite Mmult_I0,Mmult_σX0,Mmult_B0pos,Mmult_B3pos;
try rewrite Mmult_B30,Mmult_B01; repeat cancel_0;
try rewrite Mmult_I0,Mmult_I1,Mmult_σX0,Mmult_B31,Mmult_B00;
(* repeat (autorewrite with G1_db;
isolate_scale); *)
reduce_scale. *)



Time assoc_right.
Time repeat mult_kron.
rewrite Mmult_I0,Mmult_H0. repeat cancel_0.


unfold CX at 11.
repeat kron_plus_distr.
assoc_right.
rewrite Mmult_plus_distr_r.
isolate_scale.
repeat mult_kron.
rewrite Mmult_I0,Mmult_σX0,Mmult_B0pos,Mmult_B3pos.

unfold CX at 10.
repeat kron_plus_distr.
assoc_right.
rewrite Mmult_plus_distr_l.
rewrite Mmult_plus_distr_r.
rewrite Mmult_plus_distr_r.
isolate_scale.
repeat mult_kron.
rewrite Mmult_B30,Mmult_B01. repeat cancel_0.
rewrite Mmult_I0,Mmult_I1,Mmult_σX0,Mmult_B31,Mmult_B00.

unfold CX at 9.
repeat kron_plus_distr.
assoc_right.
rewrite Mmult_plus_distr_l.
rewrite Mmult_plus_distr_r.
rewrite Mmult_plus_distr_r.
isolate_scale.
repeat mult_kron.
rewrite Mmult_B30,Mmult_B01. repeat cancel_0.
rewrite Mmult_I0,Mmult_σX0,Mmult_B00,Mmult_B31,Mmult_I1.

unfold CX at 8.
repeat kron_plus_distr.
assoc_right.
rewrite Mmult_plus_distr_l.
rewrite Mmult_plus_distr_r.
rewrite Mmult_plus_distr_r.
isolate_scale.
repeat mult_kron.
rewrite Mmult_B30,Mmult_B01. repeat cancel_0.
rewrite Mmult_I0,Mmult_σX0,Mmult_B00,Mmult_B31,Mmult_I1.


unfold CX at 7.
repeat kron_plus_distr.
assoc_right.
rewrite Mmult_plus_distr_l.
rewrite Mmult_plus_distr_r.
rewrite Mmult_plus_distr_r.
isolate_scale.
repeat mult_kron.
rewrite Mmult_B30,Mmult_B01. repeat cancel_0.
rewrite Mmult_I0,Mmult_σX0,Mmult_B00,Mmult_B31,Mmult_I1.

unfold CX at 6.
repeat kron_plus_distr.
assoc_right.
rewrite Mmult_plus_distr_l.
rewrite Mmult_plus_distr_r.
rewrite Mmult_plus_distr_r.
isolate_scale.
repeat mult_kron.
rewrite Mmult_B30,Mmult_B01. repeat cancel_0.
rewrite Mmult_I0,Mmult_σX0,Mmult_B00,Mmult_B31,Mmult_I1.

unfold CX at 5.
repeat kron_plus_distr.
assoc_right.
rewrite Mmult_plus_distr_l.
rewrite Mmult_plus_distr_r.
rewrite Mmult_plus_distr_r.
isolate_scale.
repeat mult_kron.
rewrite Mmult_B30,Mmult_B01. repeat cancel_0.
rewrite Mmult_I0,Mmult_σX0,Mmult_B00,Mmult_B31,Mmult_I1.

unfold CX at 4.
repeat kron_plus_distr.
assoc_right.
rewrite Mmult_plus_distr_l.
rewrite Mmult_plus_distr_r.
rewrite Mmult_plus_distr_r.
isolate_scale.
repeat mult_kron.
rewrite Mmult_B30,Mmult_B01. repeat cancel_0.
rewrite Mmult_I0,Mmult_σX0,Mmult_B00,Mmult_B31,Mmult_I1.

unfold CX at 3.
repeat kron_plus_distr.
assoc_right.
rewrite Mmult_plus_distr_l.
rewrite Mmult_plus_distr_r.
rewrite Mmult_plus_distr_r.
isolate_scale.
repeat mult_kron.
rewrite Mmult_B30,Mmult_B01. repeat cancel_0.
rewrite Mmult_I0,Mmult_σX0,Mmult_B00,Mmult_B31,Mmult_I1.

unfold CX at 2.
repeat kron_plus_distr.
assoc_right.
rewrite Mmult_plus_distr_l.
rewrite Mmult_plus_distr_r.
rewrite Mmult_plus_distr_r.
isolate_scale.
repeat mult_kron.
rewrite Mmult_B30,Mmult_B01. repeat cancel_0.
rewrite Mmult_I0,Mmult_σX0,Mmult_B00,Mmult_B31,Mmult_I1.

unfold CX.
repeat kron_plus_distr.
assoc_right.
rewrite Mmult_plus_distr_l.
rewrite Mmult_plus_distr_r.
rewrite Mmult_plus_distr_r.
isolate_scale.
repeat mult_kron.
rewrite Mmult_B30,Mmult_B01. repeat cancel_0.
rewrite Mmult_I0,Mmult_σX0,Mmult_B00,Mmult_B31,Mmult_I1.
reduce_scale.
Qed.