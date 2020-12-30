Require Export Complex.


Lemma Cmod_n1 : Cmod (-(1)) = R1.
Proof.
rewrite Cmod_opp.
rewrite Cmod_1.
easy.
Qed.

Lemma Cmult_m1_r (x : C) : x * -1 = -x.
Proof. lca. Qed.

Lemma Cmult_m1_l (x : C) : -1 * x = -x.
Proof. lca. Qed.

Lemma Copp_1 : Copp 1 = -1.
Proof. lca. Qed.

Lemma Copp_involutive_1 : - (-1) = C1 .
Proof. lca. Qed. 

Lemma Cconj_Ci : Ci^* = -Ci.
Proof. lca. Qed.

(* '/' to C *)
(* '√' to R *)
Lemma Cconj_inv2 :  (/ 2)^* = / 2.
Proof. lca. Qed.

Lemma Cplus_opp : 1 + -1 = 0.
Proof. lca. Qed.

Lemma C2_sqrt2_inv : 2 * / √ 2 = √ 2.
Proof.
 eapply c_proj_eq; simpl; try lra.
 autorewrite with R_db. 
  rewrite <- Rmult_assoc. 
  rewrite Rmult_comm.
  rewrite <- Rmult_assoc.
  lra.
Qed.

Hint Rewrite Cconj_0 Cconj_Ci Cconj_inv2 Cplus_opp
     (* Csqrt2_sqrt *) (* Csqrt2_sqrt2_inv *) Csqrt2_inv_sqrt2 Csqrt2_inv_sqrt2_inv
          Copp_1  Cconj_involutive Cconj_plus_distr Cconj_mult_distr Copp_involutive_1
         Cmult_m1_l Cmult_m1_r : C_db.

Hint Rewrite  Cmod_0 Cmod_1 Cmod_opp Cmod_mult Cmod_m1  : C_db.

Hint Rewrite Csqrt_sqrt_inv using Psatz.lra : C_db.
