Require Export Dirac.
Require Import Morphisms.


Lemma Cmod_Cconj: forall c, RtoC((Cmod c)^2)%R = c^* * c.
Proof.
  intros.
  unfold RtoC.
  simpl.
  rewrite Rmult_1_r.
  destruct c; unfold Cconj, Cmult, Cmod, RtoC.
  simpl fst; simpl snd.
  f_equal; [| ring].
  rewrite sqrt_def by nra.
  ring.
Qed.

Lemma mod1_Cconj: forall c, (Cmod c = 1)%R -> c^* * c = 1.
Proof.
  intros.
  rewrite <- Cmod_Cconj.
  rewrite H.
  simpl.
  unfold RtoC.
  f_equal.
  ring.
Qed.

Lemma Cconj_eq_0: forall c, Cconj c = 0 -> c = 0.
Proof.
  intros.
  destruct c; simpl in H.
  inversion H.
  unfold RtoC.
  f_equal.
  lra.
Qed.


(* Matrix equivalence *)

Lemma mat_equiv_by_Mmult: forall m n (A B: Matrix m n),
  (forall v : Matrix n 1, Mmult A v ≡ Mmult B v) ->
  A ≡ B.
Proof.
  intros m n A B HAB.
    assert (forall j, (j < (N.to_nat n))%nat ->
            forall i, (i < (N.to_nat m))%nat -> A i j = B i j)
      as HAB'.
 { 
    intros j Hj.
    specialize
      (HAB (fun j' _ => if (j' =? j) && (j' <? (N.to_nat n)) then 1 else 0)).
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
  assert (forall j j', (j < (N.to_nat n))%nat -> (j' < (N.to_nat n))%nat ->
          forall x x': C,
            forall i, (i < (N.to_nat m))%nat ->
               (A i j * x + A i j' * x') = B i j * x + B i j' * x')
      as HAB''.
{
    intros j j' Hj Hj' x x'.
    specialize
      (HAB (fun j'' _ => x * (if (j'' =? j) && (j'' <? (N.to_nat n)) then 1 else 0) +
                         x' * (if (j'' =? j') && (j'' <? (N.to_nat n)) then 1 else 0))).
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
               K y * (x * (if (y =? j) && (y <? (N.to_nat n)) then 1 else 0) +
                      x' * (if (y =? j') && (y <? (N.to_nat n)) then 1 else 0))) =
            (fun y : nat =>
               (K y * (if (y =? j) && (y <? (N.to_nat n)) then 1 else 0)) * x +
               (K y * (if (y =? j') && (y <? (N.to_nat n)) then 1 else 0)) * x')).
    {
      intros.
      apply functional_extensionality.
      intros j''.
      ring.
    }
    rewrite (Csum_eq _ _ (N.to_nat n) (H (A i))),
            (Csum_eq _ _ (N.to_nat n) (H (B i))),
            !Csum_plus, <- !Csum_mult_r,
            HAj, HAj', HBj, HBj'  in HAB.
    auto.
  }
    pose proof Classical_Prop.classic
               (exists i j, (i < (N.to_nat m))%nat /\
                            (j < (N.to_nat n))%nat /\
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
      rewrite H in HAB'.
      rewrite <- HAB'.
      ring.
    }
    rewrite H, H0; reflexivity.
  }
  pose proof HAB' j Hj as Hcj.
  intros [i' Hi'] [j' Hj']; unfold get; simpl.
  revert i' Hi'.
  pose proof HAB' j' Hj' as Hc'j'.
  destruct (Classical_Prop.classic
            (exists i, (i < (N.to_nat m))%nat /\
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
            (exists i, (i < (N.to_nat m))%nat /\ A i j' <> 0))
    as [| CONTRA].
  { auto. }
  {
    clear dependent i.
    clear H.
    intros i Hi.
    assert (A i j' = 0).
    {
      apply Classical_Prop.NNPP; intro; apply CONTRA.
      exists i; auto.
    }
    assert (B i j' = 0).
    {
      rewrite <- Hc'j' by auto.
      rewrite H.
      ring.
    }
    rewrite H, H0.
    ring.
  }
Qed.


Lemma MatrixEquiv_spec: forall {n} (A B: Matrix n n),
		  A ≡ B <-> (forall v: Vector n, A × v ≡ B × v).
Proof.
  intros.
  split; intros.
  + rewrite H.
    reflexivity.
  + apply mat_equiv_by_Mmult.
     auto.
Qed.




(* Observational equivalence *)

Lemma sta_equiv_by_Mmult: forall m n (A B: Matrix m n),
  (forall v : Matrix n 1, Mmult A v ≈ Mmult B v) ->
  A ≈ B.
Proof.
  intros m n A B HAB.
  assert (forall j, (j < (N.to_nat n))%nat -> exists c,
            Cmod c = 1 /\
            forall i, (i < (N.to_nat m))%nat -> c * A i j = B i j)
      as HAB'.
  {
    intros j Hj.
    specialize
      (HAB (fun j' _ => if (j' =? j) && (j' <? (N.to_nat n)) then 1 else 0)).
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
  assert (forall j j', (j < (N.to_nat n))%nat -> (j' < (N.to_nat n))%nat ->
          forall x x': C,
          exists c,
            Cmod c = 1 /\
            forall i, (i < (N.to_nat m))%nat ->
               c * (A i j * x + A i j' * x') = B i j * x + B i j' * x')
      as HAB''.
  {
    intros j j' Hj Hj' x x'.
    specialize
      (HAB (fun j'' _ => x * (if (j'' =? j) && (j'' <? (N.to_nat n)) then 1 else 0) +
                         x' * (if (j'' =? j') && (j'' <? (N.to_nat n)) then 1 else 0))).
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
               K y * (x * (if (y =? j) && (y <? (N.to_nat n)) then 1 else 0) +
                      x' * (if (y =? j') && (y <? (N.to_nat n)) then 1 else 0))) =
            (fun y : nat =>
               (K y * (if (y =? j) && (y <? (N.to_nat n)) then 1 else 0)) * x +
               (K y * (if (y =? j') && (y <? (N.to_nat n)) then 1 else 0)) * x')).
    {
      intros.
      apply functional_extensionality.
      intros j''.
      ring.
    }
    rewrite (Csum_eq _ _ (N.to_nat n) (H (A i))),
            (Csum_eq _ _ (N.to_nat n) (H (B i))),
            !Csum_plus, <- !Csum_mult_r,
            HAj, HAj', HBj, HBj'  in HABjj'.
    auto.
  }
  pose proof Classical_Prop.classic
               (exists i j, (i < (N.to_nat m))%nat /\
                            (j < (N.to_nat n))%nat /\
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
      rewrite H in HH.
      rewrite <- HH.
      ring.
    }
    rewrite H, H0; reflexivity.
  }
  pose proof HAB' j Hj as [c [Hc Hcj]].
  exists c; split; auto.
  unfold scale.
  intros [i' Hi'] [j' Hj']; unfold get; simpl.
  revert i' Hi'.
  pose proof HAB' j' Hj' as [c' [Hc' Hc'j']].
  destruct (Classical_Prop.classic
            (exists i, (i < (N.to_nat m))%nat /\
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
      rewrite <- H0.
      field.
      apply mod1_not_0.
      auto.
    }
    destruct H as [i [Hi [HAij HAij']]].
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
    rewrite H in HH; clear H.
    assert (c / c' * A i j * (A i j' / A i j) + A i j' = (c / c' + 1) * A i j').
    { set (s:= c/c'). field; auto. }
    rewrite H in HH; clear H.
    rewrite !Cmod_mult in HH.
    apply Rmult_eq_reg_r in HH.
    2: { intro. apply Cmod_eq_0 in H. tauto. }
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
            (exists i, (i < (N.to_nat m))%nat /\ A i j' <> 0))
    as [| CONTRA].
  {
    assert (c = c').
    2: { subst c; auto. }
    destruct H0 as [i' [Hi' HAi'j']].
    assert (A i j' = 0) as HAij'.
    {
      apply Classical_Prop.NNPP; intro; apply H.
      exists i.
      tauto.
    }
    assert (A i' j = 0) as HAi'j.
    {
      apply Classical_Prop.NNPP; intro; apply H.
      exists i'.
      tauto.
    }
    specialize (HAB'' j j' Hj Hj' 1 1).
    destruct HAB'' as [k [Hk HAB'']].
    pose proof HAB'' i Hi.
    pose proof HAB'' i' Hi'.
    rewrite <- Hcj in H0, H1 by auto.
    rewrite <- Hc'j' in H0, H1 by auto.
    rewrite HAij' in H0.
    rewrite HAi'j in H1.
    ring_simplify in H0.
    ring_simplify in H1.
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
    rewrite H0, H1.
    f_equal.
    ring.
  }
  {
    clear dependent i.
    clear H.
    intros i Hi.
    assert (A i j' = 0).
    {
      apply Classical_Prop.NNPP; intro; apply CONTRA.
      exists i; auto.
    }
    assert (B i j' = 0).
    {
      rewrite <- Hc'j' by auto.
      rewrite H.
      ring.
    }
    rewrite H, H0.
    ring.
  }
Qed.


Lemma ObsEquiv_operator: forall {n} (A B: Matrix n n),
   A ≈ B <->
  (forall φ: Matrix n 1, A × φ ≈  B × φ).

Proof.
  intros.
  split; intros.
  + rewrite H.
    reflexivity.
  + apply sta_equiv_by_Mmult.
    auto.
Qed.

 Lemma ObsEquiv_state: forall {n} (φ ρ: Matrix n 1),
   φ ≈ ρ <-> φ × (φ †) ≡ ρ × (ρ †) .
Proof.
  intros; split; intros.
  + unfold obs_equiv in H.
    destruct H as [c [Hc HH]].
    rewrite <- HH.
    rewrite Mscale_adj.
    rewrite Mscale_mult_dist_r.
    rewrite Mscale_mult_dist_l.
    rewrite Mscale_assoc.
    rewrite mod1_Cconj by auto.
    rewrite Mscale_1_l.
    reflexivity.
  + unfold obs_equiv.
    revert φ ρ H.
(*     set (m := (Nat.pow (S (S O)) n)).
    clearbody m; clear n. *)
    intros.
    unfold obs_equiv.
    assert (forall i, (i < (N.to_nat n))%nat -> exists c, Cmod c = R1 /\ c * (φ i O) = ρ i O).
    {
      intros i Hi.
      specialize (H ltac:(exists i; auto) ltac:(exists i; auto)).
      unfold get in H.
      simpl in H.
      unfold adjoint, Mmult in H; simpl in H.
      ring_simplify in H.
      rewrite Cmult_comm, <- Cmod_Cconj in H.
      rewrite Cmult_comm, <- Cmod_Cconj in H.
      assert (Cmod (φ i 0%nat) = Cmod (ρ i 0%nat)).
      {
        inversion H.
        ring_simplify in H1.
        pose proof Cmod_ge_0 (φ i O).
        pose proof Cmod_ge_0 (ρ i O).
        nra.
      }
      clear H.
      destruct (Classical_Prop.classic (φ i O = 0)).
      {
        exists 1.
        split; [autorewrite with C_db;auto | ].
        rewrite H in H0.
        rewrite Cmod_0 in H0.
        symmetry in H0.
        apply Cmod_eq_0 in H0.
        rewrite H0, H.
        ring.
      }
      exists ((ρ i O)/(φ i O)).
      split.
      + rewrite Cmod_div by auto.
        rewrite <- H0.
        field.
        intro.
        apply Cmod_eq_0 in H1; tauto.
      + field.
        auto.
    }
    destruct (Classical_Prop.classic (exists i, (i < (N.to_nat n))%nat /\ φ i O <> 0)).
    2: {
      exists 1.
      split; [autorewrite with C_db;auto | ].
      intros [i Hi] [j Hj]; unfold get; simpl.
      destruct j; [clear Hj | lia].
      unfold scale.
      assert (φ i O = 0).
      { apply Classical_Prop.NNPP; intro; apply H1; exists i; auto. }
      specialize (H0 i Hi).
      destruct H0 as [c [_ ?]].
      rewrite <- H0, H2.
      ring.
    }
    destruct H1 as [i [Hi Hs1i]].
    pose proof H0 i Hi as [c [Hc ?]].
    exists c; split; auto.
    intros [i' Hi'] [j Hj]; unfold get; simpl.
    destruct j; [clear Hj | lia].
    unfold scale.
    pose proof H0 i' Hi' as [c' [Hc' ?]].
    specialize (H ltac:(exists i; auto) ltac:(exists i'; auto)).
    unfold get in H; simpl in H.
    unfold Mmult, adjoint in H; simpl in H.
    ring_simplify in H.
    rewrite <- H1, <- H2, Cconj_mult_distr in H.
    rewrite <- H2.
    destruct (Classical_Prop.classic (φ i' O = 0)) as [| Hs1i'].
    { rewrite H3; ring. }
    assert (c * c' ^* = 1).
    {
      transitivity
         (c * φ i 0%nat * (c' ^* * (φ i' 0%nat) ^*) /
         (φ i 0%nat * (φ i' 0%nat) ^*)).
      { field. split; auto. intro. apply Cconj_eq_0 in H3; tauto. }
      rewrite <- H.
      field. split; auto. intro. apply Cconj_eq_0 in H3; tauto.
    }
    assert (c' ^* * c'= 1).
    {
      rewrite <- Cmod_Cconj.
      rewrite Hc'.
      unfold RtoC.
      f_equal.
      ring.
    }
    rewrite <- (Cmult_1_l c).
    rewrite <- H4.
    rewrite <- (Cmult_1_l c') at 3.
    rewrite <- H3.
    ring.
Qed.


Ltac by_def1 := exists 1%C; split; [autorewrite with C_db;auto | rewrite Mscale_1_l].
Ltac by_def c := exists c; split.
Ltac by_effect := rewrite ObsEquiv_operator; intros.
Ltac by_den := rewrite ObsEquiv_state; intros.

Ltac state_reduce:=
let Hs := fresh "Hs" in
match goal with
| |-context [ @Mmult ?n 1 ?n 
(@Mmult ?n1 ?m ?n2 ?A ?B) (@adjoint ?m1 1 ?C ) ≡
  @Mmult  ?n 1 ?n ?D (@adjoint ?n 1 ?D)] =>
      match C with
      | @Mmult ?n2 ?m2 ?o ?A ?B=>
       assert (@Mmult n2 m2 o  A B ≡ D) as Hs
      end
end;
  [ |  repeat rewrite Hs; reflexivity].



