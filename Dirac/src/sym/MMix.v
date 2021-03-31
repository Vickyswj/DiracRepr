Require Export Dirac.
Require Import Morphisms.


(* Definition Density n := Matrix n n. *)
Definition Pure n  :=(R * (Density n))%type.   (* (prod R (Density n))%type. *)


Definition Mix n :=  (list (R * (Density n)))%type.
Definition Mix' n :=  (list (Pure n))%type.


Definition DtoP {n} (ρ : Density n) : Pure n := (1,  ρ).
Coercion DtoP  : Density >-> Pure.
Example DtoP0 :  DtoP (density ∣0⟩) = (1, density ∣0⟩).
Proof. reflexivity. Qed.


Definition PtoM {n}  (p : Pure n) : Mix n := [p].
Coercion PtoM : Pure >-> Mix.
Example PtoM0 : PtoM (1, density ∣0⟩) = [(1, density ∣0⟩)].
Proof. reflexivity. Qed.


Definition DtoM {n} (ρ : Density n) : Mix n  := [(1 , ρ)].
Coercion DtoM : Density >-> Mix.
Example DtoM0 : DtoM (density ∣0⟩) = [(1, density ∣0⟩)].
Proof. reflexivity. Qed.

(* Fixpoint UnitPure {n} (A :  Density n) (u : list (Density n)): list (Density n) :=
match u with
| [] => []
| a :: b => (super A a) :: (UnitPure A b)
end.


Definition UnitMix {n} (A :  Density n) (m : Mix n): Mix n :=
combine (fst (List.split m))  (UnitPure A (snd (List.split m))). *)



Definition UnitPure {n} (A :  Density n) (u : Pure n): Pure n := (* If Definition Density n , Why not Density n *)
match u with
| (x , y) => (x , super A y)
end.

Fixpoint UnitMix {n} (A :  Density n) (l : Mix n): Mix n :=
match l with
| [] => []
| a :: b => (UnitPure A a) :: (UnitMix  A b)
end.

Fixpoint UnitMix' {n} (A :  Density n) (m : Mix n): Mix n :=
match m with
| [] => []
| a :: b =>
    (match a with
      | (x , y) => (x , super A y)
      end) :: (UnitMix'  A b)
end.


Example t2:
  UnitMix' H [((1/2)%R , density ∣0⟩) ; (((1/2)%R , density ∣1⟩))] = [((1 / 2)%R, super H (density ∣0⟩)); ((1 / 2)%R, super H (density ∣1⟩))].
Proof.
simpl.
reflexivity.
Qed.


Lemma i : [density ∣+⟩] = [density ∣+⟩].
Proof. reflexivity. Qed.

Lemma i1 : super H (density ∣0⟩) ≡ (density ∣+⟩).
Proof.
super_reduce.
Qed.

Lemma i2 : super H (density ∣1⟩) ≡ (density ∣-⟩).
Proof.
super_reduce.
Qed.

(* Example t3:
  [((1 / 2)%R, super H (density ∣0⟩)); ((1 / 2)%R, super H (density ∣1⟩))] = [((1 / 2)%R, density ∣+⟩); ((1 / 2)%R, density ∣-⟩)].
Proof.
rewrite i1,i2.
reflexivity.
Qed. *)



Inductive eqLD {n} : list (Density n) -> list (Density n) -> Prop :=
  | eqLD_nil : eqLD nil nil
  | eqLD_cons : forall x x' l l',
       x ≡ x' -> eqLD l l' -> eqLD (x::l) (x'::l').

Infix ";=" := eqLD (at level 50).

Lemma eqLD_refl : forall n (A : list (Density n)), eqLD A A.
Proof. intros.
induction A as [|a tail].
apply eqLD_nil.
apply eqLD_cons.
reflexivity.
apply IHtail.
Qed.

Check Density 2.

Lemma eqLD_symm : forall n (A B: list (Density n)), eqLD A B <-> eqLD B A .
Proof. intros.
split. intros.
induction H.
- apply eqLD_nil.
- apply eqLD_cons. rewrite H. reflexivity. apply IHeqLD.
- intros. induction H.
  + apply eqLD_nil.
  + apply eqLD_cons. rewrite H. reflexivity. apply IHeqLD.
Qed.

Lemma eqLD_trans : forall n (A B C : list (Density n)), 
      eqLD A B -> eqLD B C -> eqLD A C.
Proof. intros.
generalize dependent A.
induction H0.
- intros. inversion H. apply eqLD_nil.
- intros. inversion H1. apply eqLD_cons.
     + rewrite <- H. apply H5.
     + apply IHeqLD. apply H6.
Qed.


Instance eqLD_equiv  {n: N} : @Equivalence (list (Density n))(@eqLD n).
Proof.
  constructor.
  hnf; intros.
  apply eqLD_refl.
  hnf; intros.
  apply eqLD_symm; auto.
  hnf; intros.
  eapply eqLD_trans; eauto.
Qed.


Definition DtoL {n} (ρ : Density n) : list (Density n) :=
[ρ].


Instance DtoL_proper {n:N}:
    Proper (mat_equiv  ==> eqLD) (@DtoL n).
Proof.
  hnf;intros ρ1 ρ2 H1.
  unfold DtoL.
  apply eqLD_cons.
  apply H1.
  apply eqLD_nil.
Qed.


Example o : DtoL (super H (density ∣1⟩)) ;= [density ∣-⟩].
(* Proof. 
unfold DtoL.
apply eqLD_cons.
rewrite i2. reflexivity.
apply eqLD_nil.
Qed. *)
Proof.
rewrite i2.
reflexivity.
Qed.


Definition DappL {n} (ρ : Density n)  (l : list (Density n)) : list (Density n) :=
ρ :: l.

Instance DappL_proper {n:N}:
    Proper (mat_equiv ==> eqLD  ==> eqLD) (@DappL n).
Proof.
  hnf;intros ρ1 ρ2 H1.
  hnf;intros l1 l2 H2.
  unfold DappL.
  apply eqLD_cons.
  apply H1. apply H2.
Qed.

Lemma iii : DappL (super H (density ∣1⟩)) [super H (density ∣0⟩)] ;= [density ∣-⟩ ; density ∣+⟩].
Proof.
rewrite i2,i1.
reflexivity.
Qed.

Lemma iiie : [super H (density ∣0⟩)] ;= [density ∣+⟩].
Proof. 
unfold DtoL.
rewrite i1.
apply eqLD_cons.
reflexivity.
apply eqLD_nil.
Qed.


Inductive eq_Mix {n} : Mix n ->Mix n -> Prop :=
  | eq_Mix_nil : eq_Mix nil nil
  | eq_Mix_cons : forall r ρ r' ρ' l l',
       r = r' -> ρ ≡ ρ' -> eq_Mix l l' -> eq_Mix ((r,ρ)::l) ((r',ρ')::l').

Definition eq_Mix' {n : N} (a b : Mix n) : Prop :=
fst (List.split a) = fst (List.split b) /\ (snd (List.split a)) ;= (snd (List.split b)).

Infix ".=" := eq_Mix (at level 70).
Infix ".='" := eq_Mix' (at level 70).

Example t3:
  [((1 / 2)%R, super H (density ∣0⟩)); ((1 / 2)%R, super H (density ∣1⟩))] .= [((1 / 2)%R, density ∣+⟩); ((1 / 2)%R, density ∣-⟩)].
Proof.
apply eq_Mix_cons. auto.
rewrite i1. reflexivity.
apply eq_Mix_cons. auto.
rewrite i2. reflexivity.
apply eq_Mix_nil.
Qed.

Example t3':
  [((1 / 2)%R, super H (density ∣0⟩)); ((1 / 2)%R, super H (density ∣1⟩))] .=' [((1 / 2)%R, density ∣+⟩); ((1 / 2)%R, density ∣-⟩)].
Proof.
unfold eq_Mix'. split. 
simpl. auto. simpl.
rewrite i1,i2.
repeat (constructor; try reflexivity).
Qed.


Definition Pro {n} (u : Pure n) :=  fst u.
Definition Sta {n} (u : Pure n) :=  snd u.

Definition Prolist {n} (a : Mix n) :=  fst (List.split a).
Definition Stalist {n} (a : Mix n) :=  snd (List.split a).



Definition Mea0 (n k : N) :=  (I (2^k) ⊗ B0 ⊗ I (2^(n-k))).
Definition Mea1 (n k : N) :=  (I (2^k) ⊗ B3 ⊗ I (2^(n-k))).
Definition Mea (n k : N) :=  (I (2^k) ⊗ (B0 .+ B3) ⊗ I (2^(n-k))).


Definition bell00 := /√2 .* (∣0,0⟩) .+ /√2 .* (∣1,1⟩).
Definition bell01 := /√2 .* (∣0,1⟩) .+ /√2 .* (∣1,0⟩).
Definition bell10 := /√2 .* (∣0,0⟩) .+ (-/√2) .* (∣1,1⟩).
Definition bell11 := /√2 .* (∣0,1⟩) .+ (-/√2) .* (∣1,0⟩).



Section h.

Variables (α β : C).
Hypothesis Normalise: Cmod α ^ 2 + Cmod β ^ 2 = 1.
(* Cmod a ^2 + Cmod b ^2 = 1. *)

Definition φ (α β : C) : Vector 2 := α .* ∣0⟩ .+ β .* ∣1⟩.
Definition φ' : Vector 2 := α .* ∣0⟩ .+ β .* ∣1⟩.

Definition φ0 := φ' ⊗ bell00.


Definition φ2 := (H ⊗ I_2 ⊗ I_2) × (CX ⊗ I_2) × φ0.

Lemma Dtele1 :  φ2 ≡ α .*  ∣+⟩ ⊗ bell00   .+  β .*  ∣-⟩ ⊗ bell01.
Proof.
intros.
unfold φ2,φ0,φ',bell00,bell01.
operate_reduce.
Qed.


Definition MeaDen {n} (m k : N) (ρ : Density n) : Mix n :=
[(fst (trace((Mea0 m k) × ρ)), Cinv (trace ((Mea0 m k)× ρ)) .* super (Mea0 m k) ρ) ; (fst (trace((Mea1 m k) × ρ)), Cinv (trace ((Mea1 m k)× ρ)) .* super (Mea1 m k) ρ)].

Definition MeaPure {n} (m k : N) (u : Pure n) : Mix n :=
match u with
| (x, y) => [((x * fst (trace((Mea0 m k) × y)))%R, Cinv (trace ((Mea0 m k)× y)) .* super (Mea0 m k) y) ; ((x * fst (trace((Mea1 m k) × y)))%R, Cinv (trace ((Mea1 m k)× y)) .* super (Mea1 m k) y)]
end.

Fixpoint MeaMix {n} (m k : N) (l : Mix n) : Mix n :=
match l with
| [] => []
| a :: b => (MeaPure m k a) ++ (MeaMix m k b)
end.

Fixpoint MeaMix' {n} (m k : N) (l : Mix n) : Mix n :=
match l with
| [] => []
| a :: b => match a with
                    | (x , y) => [((x * fst (trace((Mea0 m k) × y)))%R, Cinv (trace ((Mea0 m k)× y)) .* super (Mea0 m k) y) ; ((x * fst (trace((Mea1 m k) × y)))%R, Cinv (trace ((Mea1 m k)× y)) .* super (Mea1 m k) y)]
                    end ++ (MeaMix' m k b)
                    end.


Definition ρ2 := density ( α .*  ∣+⟩ ⊗ bell00   .+  β .*  ∣-⟩ ⊗ bell01).


Lemma Dtele21':
MeaDen 2 0 (* (density (α .*  ∣0⟩ ⊗ bell00   .+  β .*  ∣1⟩ ⊗ bell01))  *) ρ2.=

[(fst (trace((Mea0 2 0) × ρ2)),
Cinv (trace ((Mea0 2 0)× ρ2)) .* super (Mea0 2 0) ρ2) ;

(fst (trace((Mea1 2 0) × ρ2)),
Cinv (trace ((Mea1 2 0)× ρ2)) .* super (Mea1 2 0) ρ2)].
Proof.
intros. unfold MeaDen.
repeat (constructor; try reflexivity).
Qed.

Definition p21 := fst (trace((Mea0 2 0) × ρ2)).
Definition p22 := fst (trace((Mea1 2 0) × ρ2)).


Lemma k1 : trace((Mea0 2 0) × ρ2) = 1/2.
Proof.
unfold Mea0,ρ2,density,bell00,bell01,B0.
  autounfold with S_db;
  autounfold with U_db.
  simpl.
  autorewrite with C_db.
  group_radicals.
  repeat rewrite Cmult_assoc.
  repeat rewrite <- Cmult_assoc.
  repeat rewrite <- Cmult_plus_distr_l.
  repeat rewrite (Cmult_comm α (α ^*)).
  repeat rewrite (Cmult_comm β (β ^*)).
  repeat rewrite <- Cmod_sqr.
  rewrite <- Cplus_assoc.
  rewrite (Cplus_comm (Cmod β ^ 2) (Cmod α ^ 2)).
  rewrite Normalise. lca.
Qed.


Lemma k2 : trace((Mea1 2 0) × ρ2) = 1/2.
Proof.
unfold Mea1,ρ2,density,bell00,bell01,B3.
  autounfold with S_db;
  autounfold with U_db.
  simpl.
  autorewrite with C_db.
  group_radicals.
  repeat rewrite Cmult_assoc.
  repeat rewrite <- Cmult_assoc.
  repeat rewrite <- Cmult_plus_distr_l.
  repeat rewrite (Cmult_comm α (α ^*)).
  repeat rewrite (Cmult_comm β (β ^*)).
  repeat rewrite <- Cmod_sqr.
  rewrite <- Cplus_assoc.
  rewrite (Cplus_comm (Cmod β ^ 2) (Cmod α ^ 2)).
  rewrite Normalise. lca.
Qed.

Definition ρ21 := Cinv (trace ((Mea0 2 0)× ρ2)) .* super (Mea0 2 0) ρ2.
Definition ρ22 := Cinv (trace ((Mea1 2 0)× ρ2)) .* super (Mea1 2 0) ρ2.



Lemma k3 : super (Mea0 2 0) ρ2 ≡ density (/ √ 2 .* ∣0⟩ ⊗ (α .* bell00 .+ β .* bell01)).
Proof.
unfold Mea0,ρ2,bell00,bell01. (* no simpl  or Opaque N.mul.+simpl*)
assert (I (2 ^ 0) ⊗ B0 ⊗ I (2 ^ (2 - 0))  ≡ B0 ⊗ I_2 ⊗ I_2).
{ simpl. rewrite (kron_1_l _ _ B0).
   replace (N.pos (2 ^ 2)) with 4 %N by auto.
   rewrite <- I4_eq.
   replace 4%N with ((2 * 2)%N) by auto.
   rewrite <- kron_assoc. reflexivity. }
unfold super. rewrite H.
super_reduce.
Qed.

Lemma k4 : super (Mea1 2 0) ρ2 ≡ density (/ √ 2 .* ∣1⟩ ⊗ (α .* bell00 .+ - β .* bell01)).
Proof.
unfold Mea1,ρ2,bell00,bell01. (* no simpl  or Opaque N.mul.+simpl*)
assert (I (2 ^ 0) ⊗ B3 ⊗ I (2 ^ (2 - 0))  ≡ B3 ⊗ I_2 ⊗ I_2).
{ simpl. rewrite (kron_1_l _ _ B3).
   replace (N.pos (2 ^ 2)) with 4 %N by auto.
   rewrite <- I4_eq.
   replace 4%N with ((2 * 2)%N) by auto.
   rewrite <- kron_assoc. reflexivity. }
unfold super. rewrite H.
super_reduce.
Qed.

Lemma Dtele22' :
MeaMix' 2 1 [(p21,ρ21); (p22,ρ22)]
.=
[((p21 * fst (trace((Mea0 2 1) × ρ21)))%R,
Cinv (trace ((Mea0 2 1)× ρ21)) .* super (Mea0 2 1) ρ21);

((p21 * fst (trace((Mea1 2 1) × ρ21)))%R,
Cinv (trace ((Mea1 2 1)× ρ21)) .* super (Mea1 2 1) ρ21);

((p22 * fst (trace((Mea0 2 1) × ρ22)))%R,
Cinv (trace ((Mea0 2 1)× ρ22)) .* super (Mea0 2 1) ρ22);

((p22 * fst (trace((Mea1 2 1) × ρ22)))%R,
Cinv (trace ((Mea1 2 1)× ρ22)) .* super (Mea1 2 1) ρ22)].
Proof.
intros. unfold MeaMix'.
repeat (constructor; try reflexivity).
Qed.

Definition p31 := (p21 * fst (trace((Mea0 2 1) × ρ21))).     (* 1/4 *)
Definition p32 := (p21 * fst (trace((Mea1 2 1) × ρ21))).
Definition p33 := (p22 * fst (trace((Mea0 2 1) × ρ22))).
Definition p34 := (p22 * fst (trace((Mea1 2 1) × ρ22))).

Definition p31' := (p21 * fst (trace((Mea0 2 1) × ρ21)))%R.


Lemma k5 : trace((Mea0 2 1) × ρ21) = / 2.
Proof.
unfold ρ21.
rewrite k1,k3.
unfold Mea0,B0,density,bell00,bell01.
  autounfold with S_db;
  autounfold with U_db.
  simpl.
  autorewrite with C_db.
  group_radicals.
  repeat rewrite (Cmult_comm _ (/ / C2)).
  repeat rewrite Cmult_assoc.
  repeat rewrite <- Cmult_assoc.
  repeat rewrite <- Cmult_plus_distr_l.
  repeat rewrite (Cmult_comm α (α ^*)).
  repeat rewrite (Cmult_comm β (β ^*)).
  repeat rewrite <- Cmod_sqr.
  rewrite Normalise.
   apply injective_projections; simpl; field.
Qed.


Lemma k5' : p31 = 1/4.
Proof.
unfold p31,p21.
(* rewrite k1,k5.  lca. *)
rewrite k1.
replace((trace (Mea0 2 1 × ρ21))) with (/2).
apply injective_projections; simpl; field.
  unfold ρ21.
  rewrite k1,k3.
  unfold Mea0,B0,density,bell00,bell01.
  autounfold with S_db;
  autounfold with U_db.
  simpl.
  autorewrite with C_db.
  group_radicals.
  repeat rewrite (Cmult_comm _ (/ / C2)).
  repeat rewrite Cmult_assoc.
  repeat rewrite <- Cmult_assoc.
  repeat rewrite <- Cmult_plus_distr_l.
  repeat rewrite (Cmult_comm α (α ^*)).
  repeat rewrite (Cmult_comm β (β ^*)).
  repeat rewrite <- Cmod_sqr.
  rewrite Normalise.
   apply injective_projections; simpl; field.
Qed.


Lemma k6 : trace((Mea1 2 1) × ρ21) = / 2.
Proof.
unfold ρ21.
rewrite k1,k3.
unfold Mea1,B3,density,bell00,bell01.
  autounfold with S_db;
  autounfold with U_db.
  simpl.
  autorewrite with C_db.
  group_radicals.
  repeat rewrite (Cmult_comm _ (/ / C2)).
  repeat rewrite Cmult_assoc.
  repeat rewrite <- Cmult_assoc.
  repeat rewrite <- Cmult_plus_distr_l.
  repeat rewrite (Cmult_comm α (α ^*)).
  repeat rewrite (Cmult_comm β (β ^*)).
  repeat rewrite <- Cmod_sqr.
  rewrite Cplus_comm in Normalise.
  rewrite Normalise.
   apply injective_projections; simpl; field.
Qed.


Lemma k6' : p32 = 1/4.
Proof.
unfold p32,p21.
(* rewrite k1,k5.  lca. *)
rewrite k1.
replace((trace (Mea1 2 1 × ρ21))) with (/2).
apply injective_projections; simpl; field.
  unfold ρ21.
  rewrite k1,k3.
  unfold Mea1,B3,density,bell00,bell01.
  autounfold with S_db;
  autounfold with U_db.
  simpl.
  autorewrite with C_db.
  group_radicals.
  repeat rewrite (Cmult_comm _ (/ / C2)).
  repeat rewrite Cmult_assoc.
  repeat rewrite <- Cmult_assoc.
  repeat rewrite <- Cmult_plus_distr_l.
  repeat rewrite (Cmult_comm α (α ^*)).
  repeat rewrite (Cmult_comm β (β ^*)).
  repeat rewrite <- Cmod_sqr.
  rewrite Cplus_comm in Normalise.
  rewrite Normalise.
   apply injective_projections; simpl; field.
Qed.

Lemma k7 : trace((Mea0 2 1) × ρ22) = / 2.
Proof.
unfold ρ22.
rewrite k2,k4.
unfold Mea0,B0,density,bell00,bell01.
  autounfold with S_db;
  autounfold with U_db.
  simpl.
  autorewrite with C_db.
  group_radicals.
  repeat rewrite (Cmult_comm _ (/ / C2)).
  repeat rewrite Cmult_assoc.
  repeat rewrite <- Cmult_assoc.
  repeat rewrite <- Cmult_plus_distr_l.
  repeat rewrite (Cmult_comm α (α ^*)).
  repeat rewrite (Cmult_comm β (β ^*)).
  repeat rewrite <- Cmod_sqr.
  rewrite Normalise.
   apply injective_projections; simpl; field.
Qed.


Lemma k7' : p33 = 1/4.
Proof.
unfold p33,p22.
(* rewrite k1,k5.  lca. *)
rewrite k2.
replace((trace (Mea0 2 1 × ρ22))) with (/2).
apply injective_projections; simpl; field.
  unfold ρ22.
  rewrite k2,k4.
  unfold Mea0,B0,density,bell00,bell01.
  autounfold with S_db;
  autounfold with U_db.
  simpl.
  autorewrite with C_db.
  group_radicals.
  repeat rewrite (Cmult_comm _ (/ / C2)).
  repeat rewrite Cmult_assoc.
  repeat rewrite <- Cmult_assoc.
  repeat rewrite <- Cmult_plus_distr_l.
  repeat rewrite (Cmult_comm α (α ^*)).
  repeat rewrite (Cmult_comm β (β ^*)).
  repeat rewrite <- Cmod_sqr.
  rewrite Normalise.
   apply injective_projections; simpl; field.
Qed.

Lemma k8 : trace((Mea1 2 1) × ρ22) = / 2.
Proof.
unfold ρ22.
rewrite k2,k4.
unfold Mea1,B3,density,bell00,bell01.
  autounfold with S_db;
  autounfold with U_db.
  simpl.
  autorewrite with C_db.
  group_radicals.
  repeat rewrite (Cmult_comm _ (/ / C2)).
  repeat rewrite Cmult_assoc.
  repeat rewrite <- Cmult_assoc.
  repeat rewrite <- Cmult_plus_distr_l.
  repeat rewrite (Cmult_comm α (α ^*)).
  repeat rewrite (Cmult_comm β (β ^*)).
  repeat rewrite <- Cmod_sqr.
  rewrite Cplus_comm in Normalise.
  rewrite Normalise.
   apply injective_projections; simpl; field.
Qed.


Lemma k8' : p34 = 1/4.
Proof.
unfold p34,p22.
(* rewrite k1,k5.  lca. *)
rewrite k2.
replace((trace (Mea1 2 1 × ρ22))) with (/2).
apply injective_projections; simpl; field.
  unfold ρ22.
  rewrite k2,k4.
  unfold Mea1,B3,density,bell00,bell01.
  autounfold with S_db;
  autounfold with U_db.
  simpl.
  autorewrite with C_db.
  group_radicals.
  repeat rewrite (Cmult_comm _ (/ / C2)).
  repeat rewrite Cmult_assoc.
  repeat rewrite <- Cmult_assoc.
  repeat rewrite <- Cmult_plus_distr_l.
  repeat rewrite (Cmult_comm α (α ^*)).
  repeat rewrite (Cmult_comm β (β ^*)).
  repeat rewrite <- Cmod_sqr.
  rewrite Cplus_comm in Normalise.
  rewrite Normalise.
   apply injective_projections; simpl; field.
Qed.


Definition ρ31 := Cinv (trace ((Mea0 2 1)× ρ21)) .* super (Mea0 2 1) ρ21.
Definition ρ32 := Cinv (trace ((Mea1 2 1)× ρ21)) .* super (Mea1 2 1) ρ21.
Definition ρ33 := Cinv (trace ((Mea0 2 1)× ρ22)) .* super (Mea0 2 1) ρ22.
Definition ρ34 := Cinv (trace ((Mea1 2 1)× ρ22)) .* super (Mea1 2 1) ρ22.


Lemma k9 : super (Mea0 2 1) ρ21 ≡ density (/√2 .* (∣0⟩ ⊗ ∣0⟩ ⊗ (α .* ∣0⟩ .+ β .* ∣1⟩))).
Proof.
unfold Mea0,ρ21.
rewrite k1. unfold super at 1.
rewrite k3. unfold bell00,bell01.
replace (I (2 ^ 1) ⊗ B0 ⊗ I (2 ^ (2 - 1))) with (I_2 ⊗ B0 ⊗ I_2 )
by (rewrite I2_eq; auto).
isolate_scale.
replace (density (/√2 .* (∣0⟩ ⊗ ∣0⟩ ⊗ (α .* ∣0⟩ .+ β .* ∣1⟩))))
with (/ (C1 / C2) .* density (/2  .* (∣0⟩ ⊗ ∣0⟩ ⊗ (α .* ∣0⟩ .+ β .* ∣1⟩)))).
2 :{ unfold density.
  repeat rewrite Mscale_adj.
  isolate_scale.
  replace (/ (C1 / C2) * / C2 * (/ C2) ^*) with (/ √ 2 * (/ √ 2) ^*)
    by (group_radicals; apply injective_projections; simpl ; field).
  auto. }
match goal with
  | |-context [/ (C1 / C2) .* ?M ≡ / (C1 / C2) .* ?N ] =>  assert (M ≡ N) as H
end.
replace ((2 ^ 1 * 2 * 2 ^ (2 - 1))%N)
with ((2 ^ 0 * 2 * 2 ^ (2 - 0))%N) by (simpl;lia).
super_reduce.
rewrite H. reflexivity.
Qed.


Lemma k10 : super (Mea1 2 1) ρ21 ≡ density (/√2 .* (∣0⟩ ⊗ ∣1⟩ ⊗ (α .* ∣1⟩ .+ β .* ∣0⟩))).
Proof.
unfold Mea1,ρ21.
rewrite k1. unfold super at 1.
rewrite k3. unfold bell00,bell01.
replace (I (2 ^ 1) ⊗ B3 ⊗ I (2 ^ (2 - 1))) with (I_2 ⊗ B3 ⊗ I_2 )
by (rewrite I2_eq; auto).
isolate_scale.
replace (density (/√2 .* (∣0⟩ ⊗ ∣1⟩ ⊗ (α .* ∣1⟩ .+ β .* ∣0⟩))))
with (/ (C1 / C2) .* density (/2  .* (∣0⟩ ⊗ ∣1⟩ ⊗ (α .* ∣1⟩ .+ β .* ∣0⟩)))).
2 :{ unfold density.
  repeat rewrite Mscale_adj.
  isolate_scale.
  replace (/ (C1 / C2) * / C2 * (/ C2) ^*) with (/ √ 2 * (/ √ 2) ^*)
    by (group_radicals; apply injective_projections; simpl ; field).
  auto. }
match goal with
  | |-context [/ (C1 / C2) .* ?M ≡ / (C1 / C2) .* ?N ] =>  assert (M ≡ N) as H
end.
replace ((2 ^ 1 * 2 * 2 ^ (2 - 1))%N)
with ((2 ^ 0 * 2 * 2 ^ (2 - 0))%N) by (simpl;lia).
super_reduce.
rewrite H. reflexivity.
Qed.

Lemma k11 : super (Mea0 2 1) ρ22 ≡ density (/√2 .* (∣1⟩ ⊗ ∣0⟩ ⊗ (α .* ∣0⟩ .+ - β .* ∣1⟩))).
Proof.
unfold Mea0,ρ22.
rewrite k2. unfold super at 1.
rewrite k4. unfold bell00,bell01.
replace (I (2 ^ 1) ⊗ B0 ⊗ I (2 ^ (2 - 1))) with (I_2 ⊗ B0 ⊗ I_2 )
by (rewrite I2_eq; auto).
isolate_scale.
replace (density (/√2 .* (∣1⟩ ⊗ ∣0⟩ ⊗ (α .* ∣0⟩ .+ - β .* ∣1⟩))))
with (/ (C1 / C2) .* density (/2  .* (∣1⟩ ⊗ ∣0⟩ ⊗ (α .* ∣0⟩ .+ - β .* ∣1⟩)))).
2 :{ unfold density.
  repeat rewrite Mscale_adj.
  isolate_scale.
  replace (/ (C1 / C2) * / C2 * (/ C2) ^*) with (/ √ 2 * (/ √ 2) ^*)
    by (group_radicals; apply injective_projections; simpl ; field).
  auto. }
match goal with
  | |-context [/ (C1 / C2) .* ?M ≡ / (C1 / C2) .* ?N ] =>  assert (M ≡ N) as H
end.
replace ((2 ^ 1 * 2 * 2 ^ (2 - 1))%N)
with ((2 ^ 0 * 2 * 2 ^ (2 - 0))%N) by (simpl;lia).
super_reduce.
rewrite H. reflexivity.
Qed.

Lemma k12 : super (Mea1 2 1) ρ22 ≡ density (/√2 .* (∣1⟩ ⊗ ∣1⟩ ⊗ (α .* ∣1⟩ .+ - β .* ∣0⟩))).
Proof.
unfold Mea1,ρ22.
rewrite k2. unfold super at 1.
rewrite k4. unfold bell00,bell01.
replace (I (2 ^ 1) ⊗ B3 ⊗ I (2 ^ (2 - 1))) with (I_2 ⊗ B3 ⊗ I_2 )
by (rewrite I2_eq; auto).
isolate_scale.
replace (density (/√2 .* (∣1⟩ ⊗ ∣1⟩ ⊗ (α .* ∣1⟩ .+ - β .* ∣0⟩))))
with (/ (C1 / C2) .* density (/2  .* (∣1⟩ ⊗ ∣1⟩ ⊗ (α .* ∣1⟩ .+ - β .* ∣0⟩)))).
2 :{ unfold density.
  repeat rewrite Mscale_adj.
  isolate_scale.
  replace (/ (C1 / C2) * / C2 * (/ C2) ^*) with (/ √ 2 * (/ √ 2) ^*)
    by (group_radicals; apply injective_projections; simpl ; field).
  auto. }
match goal with
  | |-context [/ (C1 / C2) .* ?M ≡ / (C1 / C2) .* ?N ] =>  assert (M ≡ N) as H
end.
replace ((2 ^ 1 * 2 * 2 ^ (2 - 1))%N)
with ((2 ^ 0 * 2 * 2 ^ (2 - 0))%N) by (simpl;lia).
super_reduce.
rewrite H. reflexivity.
Qed.


Lemma Dtele3 :
[(fst p31, ρ31); (fst p32, super (I_2 ⊗ I_2 ⊗ σX) ρ32); (fst p33, super (I_2 ⊗ I_2 ⊗ σZ) ρ33); (fst p34, super ((I_2 ⊗ I_2 ⊗ σZ) × (I_2 ⊗ I_2 ⊗ σX)) ρ34)]
.=
[((/4)%R, density (∣0⟩ ⊗ ∣0⟩ ⊗ φ')); ((/4)%R, density ((∣0⟩ ⊗ ∣1⟩ ⊗ φ'))); ((/4)%R, density ((∣1⟩ ⊗ ∣0⟩ ⊗ φ'))); ((/4)%R, density ((∣1⟩ ⊗ ∣1⟩ ⊗ φ')))].
Proof.
intros.
repeat (constructor; try reflexivity).
rewrite k5'. simpl. lra.
  unfold ρ31,φ'. rewrite k5. rewrite k9.
  unfold density.
  repeat rewrite Mscale_adj.
  isolate_scale. group_radicals.
  replace (/ C2 * / / C2 ) with C1
    by (apply injective_projections; simpl ; field).
  rewrite Mscale_1_l. reflexivity.
rewrite k6'. simpl. lra.
  unfold ρ32,φ'. rewrite k6. 
  unfold super at 1.  rewrite k10.
  isolate_scale.
  replace (density (∣0⟩ ⊗ ∣1⟩ ⊗ (α .* ∣0⟩ .+ β .* ∣1⟩)))
  with (/ / C2 .* density (/ √ 2 .* (∣0⟩ ⊗ ∣1⟩ ⊗ (α .* ∣0⟩ .+ β .* ∣1⟩)))).
  2 : { unfold density. repeat rewrite Mscale_adj.
           isolate_scale. group_radicals. 
             replace (/ C2 * / / C2 ) with C1
             by (apply injective_projections; simpl ; field).
           rewrite Mscale_1_l. reflexivity. }
  match goal with
    | |-context [/ / C2 .* ?M ≡ / / C2 .* ?N ] =>  assert (M ≡ N) as H
  end.
  replace ((2 ^ 1) * 2 * 2 ^ (2 - 1))%N with (2 * 2 * 2)%N by (simpl; lia).
  super_reduce. rewrite H. reflexivity.
rewrite k7'. simpl. lra.
  unfold ρ33,φ'. rewrite k7. 
  unfold super at 1.  rewrite k11.
  isolate_scale.
  replace (density (∣1⟩ ⊗ ∣0⟩ ⊗ (α .* ∣0⟩ .+ β .* ∣1⟩)))
  with (/ / C2 .* density (/ √ 2 .* (∣1⟩ ⊗ ∣0⟩ ⊗ (α .* ∣0⟩ .+ β .* ∣1⟩)))).
  2 : { unfold density. repeat rewrite Mscale_adj.
           isolate_scale. group_radicals. 
             replace (/ C2 * / / C2 ) with C1
             by (apply injective_projections; simpl ; field).
           rewrite Mscale_1_l. reflexivity. }
  match goal with
    | |-context [/ / C2 .* ?M ≡ / / C2 .* ?N ] =>  assert (M ≡ N) as H
  end.
  replace ((2 ^ 1) * 2 * 2 ^ (2 - 1))%N with (2 * 2 * 2)%N by (simpl; lia).
  super_reduce. rewrite H. reflexivity.
rewrite k8'. simpl. lra.
  unfold ρ34,φ'. rewrite k8. 
  unfold super at 1.  rewrite k12.
  isolate_scale.
  replace (density (∣1⟩ ⊗ ∣1⟩ ⊗ (α .* ∣0⟩ .+ β .* ∣1⟩)))
  with (/ / C2 .* density (/ √ 2 .* (∣1⟩ ⊗ ∣1⟩ ⊗ (α .* ∣0⟩ .+ β .* ∣1⟩)))).
  2 : { unfold density. repeat rewrite Mscale_adj.
           isolate_scale. group_radicals. 
             replace (/ C2 * / / C2 ) with C1
             by (apply injective_projections; simpl ; field).
           rewrite Mscale_1_l. reflexivity. }
  match goal with
    | |-context [/ / C2 .* ?M ≡ / / C2 .* ?N ] =>  assert (M ≡ N) as H
  end.
  replace ((2 ^ 1) * 2 * 2 ^ (2 - 1))%N with (2 * 2 * 2)%N by (simpl; lia).
  super_reduce. rewrite H. reflexivity.
Qed.















Section LD_element.

Fixpoint LD {m} n (f : nat -> Density m): (list (Density m)) :=
match n with
| 0 => nil
| S n' => f (S n') :: LD n' f
end.


Check LD 2 (fun x => density ∣0⟩).

Example LD2 : LD 2 (fun x => density ∣0⟩) = [density ∣0⟩;density ∣0⟩].
Proof. reflexivity. Qed.

Example LD22 : LD 2 (fun x => 
match x with
| 1 => density ∣0⟩
| 2 => density ∣1⟩
| _ => Zero
end) = [density ∣1⟩;density ∣0⟩].
Proof. reflexivity. Qed.


End LD_element.



Section eqLD_bool_error.

Variables (n : N).
Hypothesis Meq_dec : forall x y : Matrix n n, {x ≡ y} + {x <> y}.


Fixpoint eq_LD (l1 l2 : list (Matrix n n)) : bool :=
  match l1 with
  |nil => match l2 with
          |nil =>true
          |h2 :: t2 =>false
          end
  |h1 :: t1 => match l2 with
               |nil => false
               |h2 :: t2 => match Meq_dec h1 h2 with
                            |left _ => eq_LD t1 t2
                            |right_ => false
                            end
               end
end.

Definition eq_LD' {n : N} (a b : list (Matrix n n)) : Prop :=
eq_LD  a b = true.

Definition eq_Mix1' {n : N} (a b : Mix n) : Prop :=
fst (List.split a) = fst (List.split b) /\ eq_LD  (snd (List.split a))  (snd (List.split b)) = true.

(* Definition eq_Mix {n : N} (a b : Mix n) : Prop :=
fst (List.split a) = fst (List.split b) /\ snd (List.split a) = snd (List.split b). *)

Infix "='" := eq_LD' (at level 70).


Lemma iii' : [super H (density ∣0⟩)] =' [density ∣+⟩].
Proof.
unfold eq_LD'.
unfold eq_LD.
destruct Meq_dec.
auto.
Abort.

End eqLD_bool_error.



