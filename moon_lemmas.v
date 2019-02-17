Require Import Reals.
Require Import Omega.
Require Import Fourier.
Open Scope R_scope.

(** Stuff contributed by Charlie Murphy **)

Definition I (n : nat) : R :=
  if eq_nat_dec (n mod 3) 0 then Rpower 3 ((INR n) / 3)
  else if eq_nat_dec (n mod 3) 1 then 4 * (Rpower 3 (((INR n) - 4)/3))
       else 2 * (Rpower 3 (((INR n) - 2) / 3)).



Lemma mod3_eq_2 : forall (a : nat),
    (a mod 3 <> 0 -> a mod 3 <> 1 -> a mod 3 = 2)%nat.
Proof.
  intros.
  assert (3 <> 0)%nat.
  auto.
  assert (forall (n : nat), n <> n -> False).
  intros;
    apply H2;
    reflexivity.
  assert (H3 := Nat.mod_upper_bound a 3 H1).
  destruct (a mod 3);
    [ apply H2 in H |
      destruct n;
      [ apply H2 in H0|]]; try contradiction.
  destruct n; auto.
  unfold lt in H3.
  repeat apply le_S_n in H3.
  apply le_n_0_eq in H3.
  inversion H3.
Qed.

Theorem I_unfold: forall (n : nat),
    (I n) * 3 = I (n + 3).
Proof.
  intros. assert ((n + 3) mod 3 = n mod 3).
  rewrite <- Nat.add_mod_idemp_r; auto.
  assert (INR 3 = 3). simpl; Rcompute.
  unfold I; rewrite H.
  destruct (eq_nat_dec (n mod 3) 0).
  { unfold Rdiv. rewrite plus_INR. rewrite H0.
    rewrite Rmult_plus_distr_r.
    rewrite Rinv_r; discrR.
    rewrite Rpower_plus.
    rewrite Rpower_1; prove_sup; auto.
  } destruct (eq_nat_dec (n mod 3) 1).
  { unfold Rdiv. rewrite plus_INR. rewrite H0.
    unfold Rminus. rewrite (Rplus_assoc _ 3).
    rewrite (Rplus_comm 3). rewrite <- (Rplus_assoc _ _ 3).
    rewrite (Rmult_plus_distr_r _ 3 (/3)).
    rewrite Rinv_r; discrR.
    rewrite Rpower_plus.
    rewrite Rpower_1; prove_sup. ring.
  } assert (H1 := Nat.mod_le n 3).
  rewrite (mod3_eq_2 _ n0 n1) in H1.
  rewrite plus_comm. replace (INR (3 + n)) with (3 + (INR n)).
  replace ((3 + INR n - 2) / 3) with ((3/3)+(INR n -2)/3).
  replace (Rpower 3 (3 / 3 + (INR n - 2) / 3)) with ((Rpower 3 (3/3))*(Rpower 3 ((INR n - 2) / 3) )). 
  replace (3/3) with (1).
  rewrite Rpower_1.
  field.
  fourier.
  field.
  symmetry.
  apply Rpower_plus.
  field.
  replace (3) with (INR 3) at 1.
  symmetry.
  apply plus_INR.
Qed.


Require Import Wellfounded.
Theorem strong_induction : forall (P : nat -> Prop),
    (P 0 ->
     (forall n, (forall m, m <= n -> P m) -> P (S n)) ->
     forall n, P n)%nat.
Proof.
  intros.
  induction n using (well_founded_induction lt_wf).
  destruct n; auto.
  apply H0.
  intros.
  assert (m < S n)%nat.
  omega.
  apply H1 in H3; auto.
Qed.

Theorem I_n_q : forall (n : nat),
    I n <= Rpower 3 ((INR n)/3).
Proof.
  intros n. induction n using strong_induction.
  { unfold I; simpl. apply Rle_refl.
  } assert (S n = 1 \/ S n = 2 \/ exists m, S n = m + 3)%nat.
  destruct n. auto. destruct n. auto. right. right. exists n. omega.
  destruct H0.
  { inversion H0; subst. unfold I. simpl. unfold Rdiv.
    assert ((1 - 4) * / 3 = -1). field. rewrite H1.
    rewrite Rmult_1_l. 
    assert ((IZR (Zneg xH)) = (Ropp (IZR (Zpos xH)))).
    {
      auto.
    }
    rewrite H2.
    rewrite Rpower_Ropp.
    clear H2.
    rewrite Rpower_1; prove_sup.
    assert (4 * / 3 = Rpower (64*/27) (/3)).
    assert (64 */27 = Rpower (4*/3) (INR 3)).
    rewrite Rpower_pow; try fourier; field.
    rewrite H2. rewrite Rpower_mult. simpl.
    field_simplify.
    replace (1 + 1 + 1) with 3; [|ring].
    replace (3 * / 3) with 1; [|field].
    rewrite Rpower_1; [auto | fourier].
    rewrite H2. apply Rle_Rpower_l; [|split]; fourier.
  } destruct H0.
  { inversion H0; subst. unfold I; simpl.
    unfold Rdiv. replace (1+1-2) with 0 by field.
    rewrite Rmult_0_l.
    rewrite Rpower_O; prove_sup. rewrite Rmult_1_r.
    rewrite <- Rpower_mult. assert (Rpower 3 (INR 2) = 9).
    rewrite Rpower_pow; prove_sup. field.
    simpl in H1; rewrite H1. assert (2 = Rpower 8 (/3)).
    assert (8 = Rpower 2 (INR 3)).
    rewrite Rpower_pow; prove_sup; field. rewrite H2.
    rewrite Rpower_mult. simpl.
    field_simplify.
    replace (2/1) with 2 by field.
    replace (1 +1 + 1) with 3; [|ring].
    replace (3 * / 3) with 1; [|field].
    rewrite Rpower_1; [auto | fourier].
    rewrite H2 at 1. apply Rle_Rpower_l; [|split]; fourier. 
  } destruct H0 as [m H0]. assert (m <= n)%nat. omega.
  apply H in H1. rewrite H0. rewrite <- I_unfold.
  unfold Rdiv. rewrite plus_INR. rewrite Rmult_plus_distr_r.
  rewrite Rpower_plus. simpl. 
  replace (1 + 1 + 1) with 3; [|ring].
  replace (3 * / 3) with 1; [|field].
  rewrite Rpower_1; [auto | fourier].
  apply Rmult_le_compat_r; auto; fourier.
Qed.

Open Scope R_scope.

Lemma n_q' : forall (n : nat),
    (3 <= n)%nat -> 1 <= (Rpower 3 ((INR (S n))/3)) - (Rpower 3 ((INR n)/3)).
Proof.
  intros. assert (3 = INR 3). simpl; Rcompute. induction H.
  { unfold Rdiv. rewrite <- H0. rewrite Rinv_r; discrR.
    rewrite Rpower_1; prove_sup. unfold Rminus.
    apply (Rplus_le_reg_r 3 _ _). rewrite Rplus_assoc.
    rewrite Rplus_opp_l. rewrite Rplus_0_r.
    assert (1+3 = 4). Rcompute. rewrite H.
    rewrite <- Rpower_mult. rewrite Rpower_pow; prove_sup.
    assert (3^4 = 81)%R. simpl. Rcompute.
    rewrite H1. assert (4 = Rpower 64 (/3)).
    assert (64 = Rpower 4 3). rewrite H0.
    rewrite Rpower_pow; prove_sup; ring.
    rewrite H2. rewrite Rpower_mult.
    rewrite Rinv_r; discrR.
    rewrite Rpower_1; prove_sup; auto.
    rewrite H2 at 1. apply Rle_Rpower_l;
                       [left; apply Rinv_0_lt_compat | split; [|left]]; prove_sup.
  } rewrite S_INR. rewrite S_INR at 2. unfold Rdiv.
  repeat rewrite Rmult_plus_distr_r. rewrite Rmult_1_l.
  repeat rewrite Rpower_plus. unfold Rminus.
  rewrite Ropp_mult_distr_l. rewrite <- Rmult_plus_distr_r.
  assert (1 <= (Rpower 3 (/3))). assert (1 = Rpower 1 (/3)).
  assert (1 = (Rpower 1 3)). rewrite H0.
  rewrite Rpower_pow; prove_sup; simpl; Rcompute.
  rewrite H1 at 2. rewrite Rpower_mult.
  rewrite Rinv_r; discrR.
  rewrite Rpower_1; prove_sup; auto.
  rewrite H1 at 1. apply Rle_Rpower_l;
                     [left; apply Rinv_0_lt_compat | split; [|left]]; prove_sup.
  rewrite <- Rmult_1_r at 1.
  apply Rmult_le_compat; try (left; prove_sup; fail); assumption. Qed.


Theorem n_q : forall (n : nat),
    INR n <= Rpower 3 ((INR n)/3).
Proof.
  assert (3 = INR 3). simpl; Rcompute. destruct n.
  { simpl. unfold Rdiv. rewrite Rmult_0_l.
    rewrite Rpower_O; prove_sup; apply Rle_0_1.
  } destruct n. {
    simpl. unfold Rdiv. rewrite Rmult_1_l.
    assert (1 = Rpower 1 (/3)).
    assert (1 = (Rpower 1 3)). rewrite H.
    rewrite Rpower_pow; prove_sup; simpl; Rcompute.
    rewrite H0 at 2. rewrite Rpower_mult.
    rewrite Rinv_r; discrR.
    rewrite Rpower_1; prove_sup; auto.
    rewrite H0 at 1. apply Rle_Rpower_l;
                       [left; apply Rinv_0_lt_compat | split; [|left]]; prove_sup.
  } destruct n. {
    unfold Rdiv. rewrite <- Rpower_mult.
    rewrite Rpower_pow; prove_sup.
    assert (3^2 = 9)%R. simpl; Rcompute. rewrite H0. simpl.
    assert (2 = Rpower 8 (/3)). assert (8 = Rpower 2 3).
    rewrite H. rewrite Rpower_pow; prove_sup; simpl; Rcompute.
    rewrite H1. rewrite Rpower_mult. rewrite Rinv_r; discrR.
    rewrite Rpower_1; prove_sup; auto.
    rewrite H1 at 1; apply Rle_Rpower_l;
      [left; apply Rinv_0_lt_compat | split; [|left]]; prove_sup.
  } induction n. {
    rewrite <- H. unfold Rdiv. rewrite Rinv_r; discrR.
    rewrite Rpower_1; prove_sup; apply Rle_refl.
  } remember (S (S (S n))) as m.
  rewrite S_INR at 1. rewrite Rplus_comm.
  apply Rle_minus in IHn.
  apply (Rplus_le_reg_r (Ropp (Rpower 3 ((INR m)/3))) _ _).
  rewrite Rplus_assoc. fold (Rminus (INR m) (Rpower 3 ((INR m)/3))).
  fold (Rminus (Rpower 3 ((INR (S m))/3)) (Rpower 3 ((INR m)/3))).
  apply (Rle_trans _ 1 _). rewrite <- Rplus_0_r.
  apply Rplus_le_compat; auto; apply Rle_refl.
  apply n_q'. rewrite Heqm. repeat apply le_n_S. apply Nat.le_0_l.
Qed.

(*************************************)

Require Import MIS_basics.
Require Import graph_basics.
Require Import Coq.Program.Equality.

Lemma lGraph_vert_ind :
  forall P : lGraph -> Prop,
    P nil_lGraph ->
    (forall n, (forall G, lV G = n -> P G) ->
               forall G', lV G' = S n -> P G') ->
    forall G, P G.
Proof.
  intros.
  destruct G.
  dependent induction lV.
  + rewrite <- fix_LiftGraph. simpl lV.
    rewrite least_LiftGraph. auto.
  + apply (H0 lV). intros.
    destruct G. simpl in H1. subst. apply IHlV. auto.
Qed.
Open Scope nat_scope.
Lemma lGraph_vert_str_ind :
  forall P : lGraph -> Prop,
    P nil_lGraph ->
    (forall n, (forall G, lV G < n -> P G) ->
               forall G', lV G' = n -> P G') ->
    forall G, P G.
Proof.
  intros.
  destruct G.
  dependent induction lV using (well_founded_ind lt_wf).
  apply (H0 lV); try auto.
  intros.
  destruct G. apply H1. apply H2.
Qed.
Import graphs_nondep.
Require Import List.
Open Scope R_scope.

Lemma helper_1 : forall n : nat,
    4 * Rpower 3 (((INR n)-4) / 3) <= (I n).
Proof.
  induction n using strong_induction.
  {
    simpl.
    unfold I.
    simpl.
    assert ((0-4) / 3 = (-(4/3))) by field.
    rewrite H.
    assert (64 */27 = Rpower (4*/3) (INR 3)).
    rewrite Rpower_pow; try fourier; field.
    assert (4 / 3 = Rpower (64*/27) (/3)).
    {
      rewrite H0. rewrite Rpower_mult. simpl.
      replace (1 + 1 + 1) with 3; [|ring].
      replace (3 * / 3) with 1; [|field].
      rewrite Rpower_1; [ auto  | fourier ].
    }
    assert (H2 : Rpower (64 * / 27) (/ 3) <= Rpower 3 (/ 3)) 
      by (apply Rle_Rpower_l; [|split]; fourier).
    rewrite H1.
    replace (0/3) with (0) by field.
    rewrite Rpower_O; [ prove_sup| ].
    rewrite Rpower_Ropp.
    field_simplify.
    {
      replace (1/1) with (1) by field.
      rewrite <- H1.
      pose proof (I_n_q 4).
      replace (INR 4) with 4 in H3; [|simpl; ring].
      unfold I in H3.
      simpl in H3.
      replace ((1 + 1 + 1 + 1 - 4) / 3) with 0 in H3 by field.
      rewrite Rpower_O in H3; try fourier.
      ring_simplify in H3.
      generalize dependent (Rpower 3 (4 / 3)).
      intros.
      unfold Rdiv.
      apply Rmult_le_reg_r with (r := r); [
        try fourier|].
      ring_simplify.
      field_simplify;
        [fourier | intros Hnot; fourier].
    }
    {
      rewrite <- H1.
      clear.
      pose proof (I_n_q 4).
      unfold I in H; simpl in H.
      intros Hnot.
      replace ((1 + 1 + 1 + 1 - 4) / 3) with 0 in H by field.
      replace ((1 + 1 + 1 + 1)) with (4) in H by (simpl; ring).
      rewrite Rpower_O in H; ring_simplify in H; try fourier.
    }
    fourier.
  }
  (* Inductive Step *)
  {
    assert (H0 : (S n = 1 \/ S n = 2 \/ exists m, S n = ( m + 3) )%nat).
    {
      do 2 (destruct n;
            auto); do 2 right;
        exists n; omega.
    }
    destruct H0.
    { inversion H0; subst. unfold I. simpl. unfold Rdiv.
      assert ((1 - 4) * / 3 = -1). field. rewrite H1.
      assert ((IZR (Zneg xH)) = (Ropp (IZR (Zpos xH)))).
      {
        auto.
      }
      rewrite H2.
      rewrite Rpower_Ropp.
      (* clear H2.
      rewrite Rpower_1; prove_sup.*)
      apply Rle_refl.
    }
    destruct H0.
    {
    rewrite H0.
      unfold I; simpl.
      unfold Rdiv. 
      replace (1+1-2) with 0 by ring.
      rewrite Rmult_0_l.
      rewrite Rpower_O; prove_sup. rewrite Rmult_1_r.
      rewrite <- Rpower_mult.
      assert (Rpower 3 (INR 2) = 9).
      {
        rewrite Rpower_pow; prove_sup. field.
      }
      replace (1 + 1 - 4) with (-(2)) by (simpl; field).
      replace (-(2) * / 3) with (- ( 2 * / 3)) by (simpl; field).
      rewrite Rpower_Ropp.
      replace (INR 2) with 2 in H1 by (simpl; field).
      replace (2) with (4 * (/2)) by (simpl; field).
      apply Rmult_le_compat_l; prove_sup.
      fourier.
      rewrite <- Rpower_Ropp.
      rewrite Rpower_mult.
      replace (- (4 * / 2) * / 3) with (- ((4 * / 2) * / 3)) by
          (simpl; field).
      rewrite Rpower_Ropp.
      replace (4 * /2) with 2 by
          (simpl; field).
      apply Rinv_le_contravar.
      fourier.
      pose proof (n_q 2).
      replace (INR 2) with 2 in H2 by
          (simpl; field).
      auto.
    }
    {
      destruct H0 as [m H0]. assert (m <= n)%nat. omega.
      apply H in H1. rewrite H0. rewrite <- I_unfold.
      rewrite plus_INR.
      ring_simplify.
      replace (INR m + INR 3 - 4) with (INR m - 4 +  INR 3)
        by (simpl; ring).
      rewrite Rdiv_plus_distr.
      replace (INR 3) with 3 by (simpl; ring).
      rewrite Rpower_plus. 
      replace (3 /3) with 1 by field.
      simpl. rewrite Rpower_1; try fourier.
      ring_simplify.
      replace 12 with (3 * 4) by ring.
      fourier.
    }
  }
Qed.

(* Dr Juedes Contribution *)
Theorem exp_vs_3: forall x:R, 0<x -> exp x <= Rpower 3 x.
Proof.
intros.
unfold Rpower.
assert (1<=ln 3).
assert (ln (exp 1) = 1).
apply ln_exp.
rewrite <-H0 at 1.
unfold Rle.
assert (exp 1 <= 3).
apply exp_le_3.
unfold Rle in H1.
destruct H1.
left.
apply ln_increasing.
assert (1+1 < exp 1).
apply exp_ineq1.
fourier.
assert (0<2).
fourier.
apply (Rlt_trans 0 2 (exp 1)).
exact H3.
exact H2.
exact H1.
right.
apply exp_inv.
assert ((exp (ln 3)) = 3).
apply exp_ln.
fourier.
rewrite H0.
rewrite H2.
exact H1.
unfold Rle.
unfold Rle in H0.
destruct H0.
left.
assert (x< x*ln 3).
assert (x*1 = x).
assert (x*1 = 1*x).
apply Rmult_comm.
rewrite H1.
apply Rmult_1_l.
rewrite <-H1 at 1.
apply Rmult_lt_compat_l.
exact H.
exact H0.
apply exp_increasing.
exact H1.
right.
assert (x*ln 3 = x).
rewrite <-H0.
ring.
rewrite H1.
reflexivity.
Qed.

Theorem three_x_1: forall x:R, 0<x -> 1+x < Rpower 3 x.
Proof.
intros.
assert ((exp x) <= (Rpower 3 x)).
apply exp_vs_3.
exact H.
assert (1+x < exp x).
apply exp_ineq1.
exact H.
destruct H0.
apply (Rlt_trans (1+x) (exp x) (Rpower 3 x)).
exact H1.
exact H0.
rewrite <-H0.
exact H1.
Qed.

Theorem ln_one_pos: forall x:R, 1<x -> 0 < ln x.
Proof.
assert (ln 1 = 0).
apply ln_1.
intros.
rewrite <-H.
apply ln_increasing.
fourier.
exact H0.
Qed.

Theorem pos_pow: forall a b :R, 1<=a -> 0< b -> 0< (Rpower a b).
Proof.
intros.
unfold Rpower.
assert (0 <= ln a).
unfold Rle in H.
destruct H.
unfold Rle.
left.
apply ln_one_pos.
exact H.
unfold Rle.
right.
assert (ln a = 0).
rewrite <-H.
apply ln_1.
rewrite H1.
reflexivity.
unfold Rle in H1.
destruct H1.
assert (0<b* ln a).
apply Rmult_lt_0_compat; auto.
assert (0 < 1 + (b*ln a)).
assert (0 < 1).
fourier.
apply Rplus_lt_0_compat; auto.
assert (1+(b*ln a) < exp (b*ln a)).
apply exp_ineq1.
exact H2.
apply (Rlt_trans 0 (1+ b*ln a) (exp (b * ln a))).
exact H3.
exact H4.
rewrite <-H1.
assert (b*0 = 0).
apply Rmult_0_r.
rewrite H2.
rewrite exp_0.
fourier.
Qed.

Theorem simple2: forall n:nat, forall x y:R, 0<y-> y=x -> y^n =x^n.
Proof.
induction n.
intros.
simpl; auto.
intros.
simpl.
rewrite H0.
reflexivity.
Qed.



Theorem simple1: forall n:nat, forall x y:R, 0<y-> y<=x -> y^n <=x^n.
Proof.
induction n.

intros.
assert (0<x).
fourier.
simpl.
fourier.
intros.
assert (0<x).
fourier.
assert (y^(S n) = y*y^n).
simpl.
reflexivity.
assert (x^(S n) = x*x^n).
simpl.
reflexivity.
assert (y^n <=x^n).
apply IHn.
exact H.
exact H0.
assert (y*y^n <= x*y^n).
rewrite Rmult_comm.
(* rewrite Rmult_comm at 2. *)
assert (x*y^n = y^n*x).
rewrite Rmult_comm.
reflexivity.
rewrite H5.
SearchAbout Rle.
Print Rfourier_le.
assert (0<y^n).
generalize n.
induction n0.
simpl.
fourier.
simpl.
apply Rmult_lt_0_compat; auto.
apply (Rfourier_le y x (y^n));auto.
simpl.
assert (x*y^n <= x*x^n).
apply (Rfourier_le (y^n) (x^n) x);auto.
fourier.
Qed.

Theorem Real_roots: forall n:nat, forall x y:R, 0<x-> 0<y-> y^n<x^n -> y<x.
Proof.
intros.
(* Proof by contradiction. *)
assert ( x<y \/ x=y \/ x>y).
apply Rtotal_order.
destruct H2.
assert (x^n <= y^n).
assert (x<=y).
unfold Rle.
left.
exact H2.

apply simple1.
exact H.
exact H3.
fourier.
destruct H2.
assert (y^n=x^n).
apply simple2.
exact H0.
rewrite H2.
auto.
fourier.
exact H2.
Qed.

Theorem two_le_3_two_over_threea: 2< (Rpower 3 (2/3)).
Proof.
assert (2^3%nat < (Rpower 3 (2/3))^3%nat).
assert ((Rpower (Rpower 3 (2/3)) (INR 3))=(Rpower 3 (2/3))^3%nat).
apply Rpower_pow.
apply pos_pow.
fourier.
fourier.
assert ((Rpower (Rpower 3 (2/3) ) (INR 3)) = (Rpower 3 2)).
assert ((Rpower 3 2) = (Rpower 3 ((2/3)*(INR 3)))).
assert (2/3*(INR 3) = 2).
assert (2/3*(INR 3) = (2*(/3*(INR 3)))).
unfold Rdiv.
assert ((INR 3) = 3).
unfold INR.
ring.
rewrite H0.

apply Rmult_assoc.
assert ((/3*3)=1).
apply Rinv_l.
apply Rgt_not_eq.
fourier.
assert ((INR 3)=3).
unfold INR.
ring.
rewrite H0.
rewrite H2.
rewrite H1.
ring.
rewrite H0.
reflexivity.
assert ((Rpower (Rpower 3 (2/3) ) (INR 3)) = (Rpower 3 ((2/3)*(INR 3)))).
rewrite (Rpower_mult 3 (2/3) (INR 3)).
reflexivity.
rewrite H1.
rewrite H0.
reflexivity.
rewrite <-H.
rewrite H0.
assert (INR 2 = 2).
unfold INR.
reflexivity.
assert ((Rpower 3 (INR 2)) = 3^2).
apply Rpower_pow.
fourier.
replace (INR 2) with 2 in H2 by (simpl; ring).
rewrite H2.
unfold pow.
fourier.
apply Real_roots in H; try fourier.
apply pos_pow.
fourier.
fourier.
Qed.

Theorem n_vs_3n: forall n:nat, INR n <= (Rpower 3 ((INR n)/3)).
Proof.
intros.
assert ((n=0)\/ (n=1) \/ (n=2) \/ (n=3) \/ (4<=n))%nat.
omega. (* I love omega! *)
destruct H.
rewrite H.
simpl.
assert (0/3 = 0).
field.
rewrite H0.
assert ((Rpower 3 0) = 1).
apply Rpower_O.
fourier.
rewrite H1.
fourier. (* Case 0 is done *)
destruct H.
rewrite H.
assert (INR 1<= (1+1/3)).
simpl.
fourier.
assert ((1+1/3) <= (Rpower 3 ((INR 1)/3))).
left.
apply three_x_1.
simpl. 
fourier.
apply (Rle_trans (INR 1) (1+(1/3)) (Rpower 3 (INR 1 / 3)));auto.
destruct H.
rewrite H.
assert (INR 2 = 2).
simpl;auto.
rewrite H0.
left.
apply two_le_3_two_over_threea.
destruct H.
rewrite H.
assert (INR 3 / 3 = 1).
simpl.
field.
rewrite H0.
assert (Rpower 3 1 = 3).
apply Rpower_1.
fourier.
rewrite H1.
simpl.
fourier.
apply n_q.
Qed.

Theorem Nate_Help: forall n:nat, INR(4+n)/4 <= Rpower 3 ((INR n)/3).
Proof.
induction n.
{ 
  simpl.
  assert (0/3 = 0).
  { field. }
  rewrite H.
  assert (Rpower 3 0 = 1).
  {
    apply Rpower_O.
    fourier.
  }
  rewrite H0.
  fourier.
}
{
  assert (4+ (S n)%nat = 1+(4+n))%nat.
  simpl.
  omega.
  rewrite H.
  assert (INR(1+(4+n)) = INR(1)+INR(4+n)).    
  SearchAbout INR.
  apply plus_INR.
  rewrite H0.
  assert (INR (S n) = INR(n) + INR(1)).
  rewrite S_INR.
  assert(INR 1 = 1).
  unfold INR.
  reflexivity.
  rewrite H1.
  reflexivity.
  rewrite H1.
  assert ((INR n + INR 1)/3 = INR n/3 + INR 1 /3).
  field.
  rewrite H2.
  assert ((INR 1 + (INR (4+n)))/4 = INR 1/4 + INR(4+n)/4).
  field.
  rewrite H3.
  assert ((Rpower 3 ((INR n)/3 + (INR 1)/3)) = (Rpower 3 ((INR n)/3) ) * (Rpower 3 ((INR 1)/3))).
  apply Rpower_plus.
  rewrite H4.
  assert (1+(1/3) < Rpower 3 (1/3)).
  
  apply three_x_1 with (x:=1/3).
  fourier.
  assert ((INR 1) = 1).
  unfold INR.
  reflexivity.
  rewrite H6.
  assert (1/4 + (INR (4+n))/4 <= (INR (4+n))/4 * (1+(1/3))).
  assert ((INR (4+n))/4 * (1+(1/3)) = (1+(1/3))*((INR (4+n))/4)).
  field.
  rewrite H7.
  assert ((1+(1/3))*((INR (4+n))/4) = (INR(4+n)/4) + (1/3)*(INR (4+n)/4)).
  field.
  rewrite H8.
  assert (1 <= (INR (4+n) / 4)).
  assert (INR (4+n) = 4 + INR n).
  rewrite plus_INR.
  assert (INR 4 = 4).
  unfold INR.
  field.
  rewrite H9.
  reflexivity.
  rewrite H9.
  assert ((4+ INR n)/4 = 1 + INR n/4).
  field.
  rewrite H10.
  assert (0<=INR n).
  apply pos_INR.
  assert (0 <= INR n / 4).
  {
    clear - H11.
    fourier.
  } (* Note: without clear this won't work!!! *)
  {
    clear - H12.
    fourier.
  }
  {
    assert (1/3 <= (1/3* (INR (4 + n) / 4))). 
    { 
    clear - H9.
    assert (1/3 = (1/3) * 1).
    {
      field.
    }
    rewrite H at 1.
    apply Rfourier_le.
    exact H9.
    fourier.
  }
  assert (((1 / 4) + INR (4 + n) / 4) = INR (4 + n) / 4 + (1/4)).
  field.
  rewrite H11.
  apply Rplus_le_compat_l with (r:= INR (4 + n) / 4 ) (r1:=1/4) (r2:= (1/3 * (INR (4 + n) / 4))).
  {
    clear - H10.    
    fourier.
  }
  }
  assert ((INR (4+n)/4 )* (1+1/3) <= Rpower 3 (INR n / 3) * Rpower 3 (1 / 3)).
  {
    clear - IHn H5.
    assert (1<=(1+ (1/3))).
    fourier.
    assert (INR (4 + n) / 4 * (1 + 1 / 3) <= Rpower 3 (INR n / 3)* (1+(1/3))).
    rewrite Rmult_comm.
    assert (Rpower 3 (INR n / 3) * (1 + 1 / 3) = (1+1/3)*Rpower 3 (INR n / 3)).
    rewrite Rmult_comm.
    reflexivity.
    rewrite H0.
    apply Rfourier_le.
    exact IHn.
    fourier.
    assert (Rpower 3 (INR n / 3) * (1 + 1 / 3) <= Rpower 3 (INR n / 3) * Rpower 3 (1 / 3)).
    apply Rfourier_le.
    left.
    exact H5.
    SearchAbout Rpower.
    {
      induction n.
      {
        assert (INR 0/3 = 0).
        unfold INR.
        field.
        rewrite H1.
        rewrite Rpower_O.
        fourier.
        fourier.
      }{
        assert (0 < INR (S n)).
        apply lt_0_INR.
        omega.
        assert (INR (S n)<= Rpower 3 (INR (S n) / 3)).
        SearchAbout Rpower.
        apply n_vs_3n.
        fourier.
      }
      }
      fourier.
      }
      clear - H7 H8.
      fourier.
  }
Qed.
(************************************)
Lemma three_le_d_2 : forall d n,
 (3 <= d)%nat ->
 (3 <= n)%nat ->
 (d <= n)%nat ->
 (INR d + 1) * Rpower 3 ((INR n - INR d -1)/3) <=
 4 * Rpower 3 ((INR n -4)/3).
Proof.
    clear.
    intros.
    replace (INR d + 1) with (((INR d+1)/4) * 4) by field.
    assert (exists (eps : nat), INR d + 1 = 4 + INR eps).
    {
      clear H0 H1.
      induction d.
      omega.
      inversion H.
      subst.
      exists O; simpl; ring.
      subst.
      apply IHd in H1.
      destruct H1.
      exists (S x).
      do 2 rewrite S_INR.      
      rewrite H0.
      ring.
    }
    destruct H2 as [eps H2].
    replace (INR n - INR d - 1) with
        (INR n - (INR d + 1)) by ring.
    rewrite -> H2 in *.
    ring_simplify.
    replace (INR n - (4 + INR eps)) with
        ((INR n - 4) + -(INR eps)) by ring.
    replace ((INR n - 4 + - INR eps) / 3) with
        (((INR n - 4)/3) + (-(INR eps /3))) by field.
    rewrite Rpower_plus.
    ring_simplify.
    pose proof (Nate_Help eps).
    rewrite plus_INR in H3.
    replace (INR 4) with 4 in H3 by (simpl; ring).
    replace (  4 * ((4 + INR eps) / 4) * Rpower 3 ((INR n - 4) / 3) *
               Rpower 3 (- (INR eps / 3))) with
        (  4 * (((4 + INR eps) / 4) * Rpower 3 ((INR n - 4) / 3) *
  Rpower 3 (- (INR eps / 3)))) by ring.
    apply Rmult_le_compat_l; [fourier|].
    clear H2.
    replace ((4 + INR eps) / 4 * Rpower 3 ((INR n - 4) / 3) *
             Rpower 3 (- (INR eps / 3))) with
        ((4 + INR eps) / 4 * Rpower 3 (- (INR eps / 3)) * Rpower 3 ((INR n - 4) / 3)) by ring.
    assert ((4 + INR eps) / 4 * Rpower 3 (- (INR eps / 3)) <= 1).
    {
      apply Rmult_le_compat_r with (r:= / Rpower 3 (INR eps / 3)) in H3.
      replace (Rpower 3 (INR eps / 3) * / Rpower 3 (INR eps / 3)) with
          1  in H3.
      {
        rewrite Rpower_Ropp; auto.
      }
      {
        symmetry.
        apply Rinv_r.
        pose proof (n_q eps).
        clear -H2.
        intros Hnot.
        rewrite Hnot in H2.
        pose proof (pos_INR eps).
        inversion H2.
        inversion H.
        fourier.
        subst.
        fourier.
        inversion H.
        fourier.
        rewrite H0 in Hnot.
        replace (0 / 3) with 0 in Hnot by field.
        rewrite Rpower_O in Hnot; fourier.
      }
      {
        pose proof (n_q eps).
        clear - H2.
        pose proof (pos_INR eps).
        inversion H.
        inversion H2.
        constructor.
        apply Rinv_0_lt_compat; auto.
        fourier.
        rewrite <- H1.
        constructor.
        apply Rinv_0_lt_compat; auto.
        rewrite <- H0.
        replace (0 / 3) with 0  by field.
        rewrite Rpower_O; fourier.
      }
    }
    apply Rmult_le_compat_r with (r:= Rpower 3 ((INR n -4 )/3)) in H2.
    fourier.
    pose proof (n_q (n - 4)).
    clear - H4 H0.
    assert ( n = 3 \/ n = 4 \/ 4 <= n)%nat.
    omega.
    destruct H; subst.
    {
      simpl.
      replace ((1 + 1 + 1 - 4) / 3) with (-(1/3)) by field.
      rewrite Rpower_Ropp.
      left.
      apply Rinv_0_lt_compat; try fourier.
      apply pos_pow; try fourier.
    }
    destruct H; subst.
    {
      simpl.
      replace ((1 + 1 + 1 + 1 - 4) / 3) with (0) by field.
      rewrite Rpower_O; fourier.
    }
    pose proof (pos_INR (n-4)).
    inversion H1.
    left.
    apply pos_pow; try fourier.
    unfold Rdiv.
    apply Rmult_lt_0_compat; try fourier; auto.
    rewrite minus_INR in H2; try fourier.
    replace (INR 4) with 4 in H2 by (simpl; ring); 
    auto.
    auto.
    assert (INR n = 4).
    {
      rewrite minus_INR in H2; auto.
      replace (INR 4) with 4 in H2 by (simpl; ring).
      clear -H2.
      generalize dependent (INR n).
      intros.
      unfold Rminus in H2.
      symmetry in H2.
      apply Rplus_opp_r_uniq in H2.
      apply Ropp_eq_compat in H2.
      do 2 rewrite Ropp_involutive in H2.
      symmetry; auto.
    }
    rewrite H3.
    replace ((4 - 4) / 3) with 0 by field.
    rewrite Rpower_O; fourier.
  Qed.
    
    
(*** Paper proof
  if d >= 3
     MIS(G)| ≤ (d + 1) · 3^(n−d−1)/3 ≤ 4 · 3^(n−4)/3 ≤ g(n) 
  if d = 2
     | MIS(G)| ≤ 3 · g(n − 3) = g(n)
  if d = 1 
        MIS(G) ≤ 2 · g(n − 2) ≤ g(n)
   ***)
           
  Lemma I_three_eq : forall (n: nat), 
      (3  <= n)%nat -> 
       3 * I (n - 3) = I n.
  Proof.
    intros.
    destruct n.
    inversion H.
    inversion H.
    {
      subst.
      unfold I; simpl.
      replace ((1 + 1 + 1) / 3) with (1) by field.
      rewrite Rpower_1.
      replace (0 /3) with 0 by field.
      rewrite Rpower_O.      
      ring.
      fourier.
      fourier.
    }
    subst.
    assert (H0 : (S n = 1 \/ S n = 2 \/ exists m, S n = ( m + 3) )%nat).
    {
      do 2 (destruct n;
            auto); do 2 right;
        exists n; omega.
    }
    destruct H0; subst.
    {
      exfalso.
      omega.
    }
    destruct H0.
    {
      exfalso.
      omega.
    }
    destruct H0.
    rewrite -> H0 in *.
    replace (x+ 3-3)%nat with x by (omega).
    rewrite <- I_unfold; ring.
  Qed.

  
  Lemma I_pos :
    forall n, (0 <= n)%nat ->
              0 <= I n .
  Proof.
    clear.
    intros.
    induction n using strong_induction.
    {
      unfold I; simpl; auto.
      replace (0/3) with 0 by field.
      rewrite Rpower_O; fourier.
    }
    rename H0 into H1.
    assert (H0 : (S n = 1 \/ S n = 2 \/ exists m, S n = ( m + 3) )%nat).
    {
      do 2 (destruct n;
            auto); do 2 right;
        exists n; omega.
    }
    destruct H0.
    {
      inversion H0.
      subst.
      unfold I; simpl.
      replace ((1-4)/3) with (-(1)) by field.
      rewrite Rpower_Ropp.
      rewrite Rpower_1;
        fourier.
    }
    destruct H0.
    {
      inversion H0.
      subst.
      unfold I; simpl.
      replace (0/3) with 0 by field. 
      replace (2-2) with (0) by ring. 
      replace (0/3) with (0) by field.
      replace ((1 + 1 - 2) / 3) with 0 by field.
      rewrite Rpower_O; fourier.
    }
    destruct H0.
    inversion H.
    subst.
    assert (x <= n)%nat by omega.
    apply H1 in H2; auto.
    rewrite H0.
    rewrite <- I_unfold.
    apply Rmult_le_pos; try fourier.
    omega.
  Qed.


Lemma I_lower_bound_1 :
  forall n,
    (3 <= n)%nat -> 
    2 * I (n - 2) <= I n.
Proof.
  clear.
  intros.
  induction n using strong_induction.
  {
    omega.
  }
  inversion H.
  subst.
  simpl.
  unfold I.
  simpl.
  {
    replace ((1-4)/3) with (-(1)) by field.
    rewrite Rpower_Ropp.
    replace ((1 + 1 + 1)/3) with 1 by field.
    rewrite Rpower_1;
      fourier.
  }
  subst.
  clear H.
  assert (H1 : (S n = 1 \/ S n = 2 \/ exists m, S n = ( m + 3) )%nat).
  {
    do 2 (destruct n;
          auto); do 2 right;
      exists n; omega.
  }
  destruct H1; subst.
  {
    exfalso.
    omega.
  }
  destruct H.
  {
    exfalso.
    omega.
  }
  destruct H.
  rewrite H.
  assert (x <= n)%nat by omega.
  assert (3 <= x \/ x = 0 \/ x = 1 \/ x = 2 \/ x = 3)%nat.
  omega.
  destruct H3.
  {
    apply H0 in H1; auto.
    replace (x + 3 - 2)%nat with (x - 2 + 3)%nat by 
        (clear - H3;
         omega).
    rewrite <- I_unfold;
      auto.
    rewrite <- I_unfold.
    rewrite <- Rmult_assoc.
    apply Rmult_le_compat; try fourier; auto.
    assert (0 <= x - 2)%nat by
        omega.
    {
      apply Rmult_le_pos; try fourier.
      apply I_pos; auto.
    }
  }
  destruct H3; subst.
  {
    simpl.
    unfold I.
    simpl.
    replace ((1-4)/3) with (-(1)) by field.
    rewrite Rpower_Ropp.
    replace ((1 + 1 + 1)/3) with 1 by field.
    rewrite Rpower_1;
      fourier.
  }
  {
    destruct H3; subst.
    {
      unfold I; simpl.
      replace (1 + 1 + 1 + 1 - 4) with 0 by field.
      replace ((1 + 1 - 2) / 3) with 0 by field.
      replace (0 / 3) with 0 by field.
      rewrite Rpower_O; fourier.
    }
    destruct H3; subst; unfold I; simpl; try fourier.
    {
      apply Rmult_le_compat_l; try fourier.
      apply Rle_Rpower; fourier.
    }
    {
      replace ((1+ 1+1 + 1 + 1 + 1)/3) with 2 by field.
      replace ((1 + 1 + 1 + 1 - 4)/3) with
          0 by field.
      rewrite Rpower_O; try fourier.
      replace 2 with (INR 2) by (simpl; ring).
      rewrite Rpower_pow; try fourier.
      simpl.
      fourier.
    }
  }
Qed.

Lemma I_lower_bound_2 :
  forall n,
    (3 <= n)%nat -> 
    I (n - 1) + I (n - 4) <= I n.
Proof.
  clear.
  intros.
  intros.
  induction n using strong_induction.
  {
    omega.
  }
  inversion H.
  subst.
  simpl.
  unfold I.
  simpl.
  {
    replace (0 /3) with 0 by field.
    rewrite Rpower_O; try fourier.
    replace ((1 + 1 + 1)/3) with 1 by field.
    replace ((1+1-2)/3) with 0 by field.
    rewrite Rpower_O.
    rewrite Rpower_1.
    all: fourier.
  }
  subst.
  clear H.
  assert (H1 : (S n = 1 \/ S n = 2 \/ exists m, S n = ( m + 3) )%nat).
  {
    do 2 (destruct n;
          auto); do 2 right;
      exists n; omega.
  }
  destruct H1; subst.
  {
    exfalso.
    omega.
  }
  destruct H.
  {
    exfalso.
    omega.
  }
  destruct H.
  rewrite H.
  assert (x <= n)%nat by omega.
  assert (4 <= x \/ x = 0 \/ x = 1 \/ x = 2 \/ x = 3 \/ x = 4)%nat.
  omega.
  destruct H3.
  {
    apply H0 in H1; auto.
    replace (x + 3 - 1)%nat with (x - 1 + 3)%nat by 
        (clear - H3;
         omega).
    rewrite <- I_unfold;
      auto.
    rewrite <- I_unfold.
    replace (x + 3 - 4)%nat with (x - 4 + 3)%nat by 
        (clear - H3;
         omega).
    rewrite <- I_unfold.
    ring_simplify.
    fourier.
    omega.
  }
  destruct H3; subst.
  {
    simpl.
    unfold I.
    simpl.
    replace ((0/3)) with (0) by field.
    rewrite Rpower_O; try fourier.
    replace ((1 + 1 + 1)/3) with 1 by field.
    replace ((1+1-2)/3) with 0 by field.
    rewrite Rpower_O.
    rewrite Rpower_1.
    all: fourier.
  }
  {
    destruct H3; subst.
    {
      unfold I; simpl.
      replace (1 + 1 + 1 + 1 - 4) with 0 by field.
      replace (0 / 3) with 0 by field.
      replace ((1 + 1 + 1)/3) with 1 by field.
      rewrite Rpower_1;
        try fourier.
      rewrite Rpower_O; fourier.
    }
    destruct H3; subst; unfold I; simpl; try fourier.
    {
      replace (1 + 1 + 1 + 1 - 4) with 0 by field.
      replace ((1 + 1 + 1)/3) with
          1 by field.
      replace ((1 - 4)/3) with (-(1)) by field.
      replace (0 / 3) with 0 by field.        
      rewrite Rpower_O; try fourier.
      ring_simplify.
      rewrite Rpower_Ropp.
      rewrite Rpower_1.
      replace (((1 + 1 + 1 + 1 + 1 - 2) / 3)) with 1 by field.  
      rewrite Rpower_1;
      fourier.
      fourier.
    }
    destruct H3; subst;
      simpl.
    {
      replace ((1+ 1+1 + 1 + 1 + 1)/3) with 2 by field.
      replace ((1+1-2)/3) with 0 by field.
      replace ((1 + 1+ 1 + 1 + 1 -2)/3) with 1 by field.
      rewrite Rpower_O.
      rewrite Rpower_1.
      replace 2 with (INR 2) by (simpl; ring).
      rewrite Rpower_pow; try fourier.
      simpl.
      all: 
      fourier.
    }
    {
      replace ((1+ 1+1 + 1 + 1 + 1)/3) with 2 by field.
      replace ((1+ 1+1 + 1 + 1 + 1 + 1-4)/3) with (1) by field.
      replace ((1 + 1 + 1)/3) with
          1 by field.
      rewrite Rpower_1; try fourier.
      ring_simplify.
      replace 2 with (INR 2) by (simpl; ring).
      rewrite Rpower_pow; try fourier.
      simpl.
      fourier.
    }
  }
Qed.

(** This next section is contributed by DWJ  **)
(** We are trying to prove that I is monotonic **)
Lemma DWJ_helper1:forall n:nat, ((n mod 3 = 0)\/ (n mod 3) = 1 \/ (n mod 3) =2)%nat.
Proof.
  intros.
  assert ((n mod 3) < 3)%nat.
  apply Nat.mod_small_iff.
  omega.
  apply Nat.mod_mod.
  omega.
  assert (forall n:nat, (n =0)\/(n = 1)\/(n=2)\/(n>2))%nat.
  intro.
  omega.
  assert (((n mod 3) =0)\/((n mod 3) = 1)\/((n mod 3) =2)\/((n mod 3) >2))%nat.
  apply H0.
  destruct H1.
  left;rewrite H1; reflexivity.
  destruct H1.
  right;left;rewrite H1;reflexivity.
  destruct H1.
  right;right;rewrite H1;reflexivity.
  omega.
Qed.

Lemma DWJ_helper2: (INR 0) /3 = 0.
Proof.
simpl.
field.
Qed.

Lemma DWJ_helper3: forall n:nat, 0<= (INR n) /3.
Proof.
intros.
assert (0<=INR n).
apply pos_INR.
unfold Rdiv.
apply Rmult_le_pos.
exact H.
fourier.
Qed.

Lemma DWJ_helper4: 0 < Rpower 3 (1 / 3).
Proof.
apply Rlt_trans with (r2:=1 + (1/3)).
fourier.
apply three_x_1.
fourier.
Qed.

Lemma DWJ_helper5: forall x:R, 0<x -> 0< Rpower 3 (x/3).
Proof.
intros.
apply Rlt_trans with (r2:=1 + (x/3)).
fourier.
apply three_x_1.
fourier.
Qed.


(*** The hardest technical lemma --- forall n, I(n) < I(n+1)  ***)
Lemma Monotonic_helper: forall n:nat, I n < I (S n).
Proof.
intros.
unfold I.

assert (  n mod 3 = 0%nat \/ n mod 3 = 1%nat \/ n mod 3 = 2%nat).
apply DWJ_helper1.

destruct H.
{
  rewrite H.
  assert ((S n mod 3) = 1)%nat.
  replace (S n) with (n+1)%nat.
SearchAbout Nat.modulo.
rewrite Nat.add_mod.
rewrite H.
simpl.
reflexivity.
omega.
omega.
rewrite H0.
simpl.
induction n.
{
  rewrite DWJ_helper2.
  replace (1-4) with (-3).
  replace (Rpower 3 0) with 1.
  replace (-3/3) with (-1).
  replace (Rpower 3 (-1)) with (/Rpower 3 1).
  replace (Rpower 3 1) with 3.
  fourier.
  symmetry.
  apply Rpower_1.
  fourier.
  symmetry.
  apply Rpower_Ropp.
  field.
  symmetry.
  apply Rpower_O.
  fourier.
  field.
  }
  {
    replace (INR (S n)) with ((INR n) + 1).
    replace (INR n + 1 + 1 -4) with (INR n -2).
    replace ((INR n +1)/3) with ((INR n)/3 + 1/3).
    replace ((INR n -2)/3) with (((INR n)/3) + (-2/3)).
    replace (Rpower 3 (INR n / 3 + 1 / 3)) with  ((Rpower 3 ((INR n)/3))* (Rpower 3 (1/3))). 
    assert ((Rpower 3 (((INR n) / 3) + (-2 / 3))) = ((Rpower 3 ((INR n)/3) ) * (Rpower 3 (-2/3)))).
    apply Rpower_plus with (x:=(INR n)/3) (y:= (-2/3)) (z:=3).
    rewrite H1.
    replace (4 * (Rpower 3 (INR n / 3) * Rpower 3 (-2 / 3))) with (Rpower 3 (INR n / 3)*(4*Rpower 3 (-2 / 3))).
    apply Rfourier_lt.
    assert ((Rpower 3 (1/3)) = (3*(Rpower 3 (-2/3)))).
    replace (3) with (Rpower 3 1) at 3.
    replace ((Rpower 3 1) * (Rpower 3 (-2/3))) with (Rpower 3 (1 + (-2/3))).
    replace (1+(-2/3)) with (1/3).
    reflexivity.
    field.
    apply Rpower_plus.
    apply Rpower_1.
    fourier.
    rewrite H2.
    rewrite Rmult_comm.
    assert (4 * Rpower 3 (-2 / 3) = (Rpower 3 (-2/3))*4).
    rewrite Rmult_comm.
    reflexivity.
    rewrite H3.
    apply Rfourier_lt.
    fourier.
    replace (-2/3) with (-(2/3)).
    rewrite Rpower_Ropp.
    replace (/Rpower 3 (2/3)) with (1*/(Rpower 3 (2/3))).
    apply Rlt_mult_inv_pos.
    fourier.
    assert (1+(2/3) < (Rpower 3 (2/3))).
    apply three_x_1.
    fourier.
    assert (0<1+(2/3)).
    fourier.
    apply Rlt_trans with (r2:=(1+(2/3))).
    exact H5.
    exact H4.
    rewrite Rmult_comm.
    apply Rmult_1_r.
    field.
    apply Rlt_le_trans with (r2:=1+(INR n /3)).
    apply Rlt_le_trans with (r2:=1).
    fourier.
    replace (1) with (1+0) at 1.
    apply Rplus_le_compat_l.
    apply DWJ_helper3.
    field.
    destruct n.
    {
      simpl.
      replace (0/3) with (0).
      replace (Rpower 3 0) with 1.
      fourier.
      symmetry.
      apply Rpower_O.
      fourier.
      field.
    }
    {
      
    unfold Rle.
    left.
    apply three_x_1.
    replace (INR (S n) ) with ((INR n)+1).
    replace (((INR n)+1)/3) with ((INR n)/3 + (1/3)).
    apply Rplus_le_lt_0_compat.
    apply DWJ_helper3.
    fourier.
    symmetry.
    apply Rdiv_plus_distr.
    symmetry.
    apply S_INR.
    }
    field.
    symmetry.
    apply Rpower_plus.
    field.
    field.
    field.
    symmetry.
    apply S_INR.
  }
  }
  (*** First case (n mod 3 = 0 is done! ***)
  destruct H.
  assert ((S n mod 3) = 2)%nat.
  replace (S n) with (n+1)%nat.
  rewrite Nat.add_mod.
  rewrite H.
  simpl.
  reflexivity.
  omega.
  omega.
  rewrite H.
  rewrite H0.
  simpl.
  {
    induction n.
    {
      (* Base *)
      replace (INR 0) with (0) by (simpl;reflexivity).
      replace (1 - 2) with (-1) by field.
      replace ((0-4)/3) with (-1 + (-1/3)) by field.
      replace (Rpower 3 ((-1 +  (-1 / 3)))) with ((Rpower 3 (-1))*(Rpower 3 (-1/3))).
      replace (4 * (Rpower 3 (-1) * Rpower 3 (-1 / 3))) with ((Rpower 3 (-1 / 3)) * (4 * (Rpower 3 (-1)))) by field. 
      replace (2 * Rpower 3 (-1 / 3)) with (Rpower 3 (-1 / 3) * 2) by field.
      apply Rfourier_lt.
      replace (-1) with (-(1)) by auto.
      rewrite Rpower_Ropp.
      rewrite Rpower_1.
      fourier.
      fourier.
      replace (-1/3) with (-(1/3)) by field.
      rewrite Rpower_Ropp.
      assert ((Rpower 3 (1/3)) <= Rpower 3 1).
      apply Rle_Rpower.
      fourier.
      fourier.
      apply Rlt_le_trans with (r2:=1/3); auto.
      fourier.
      replace (1/3) with (/3) by field.
      apply Rinv_le_contravar.
      assert (1<=Rpower 3 (/3)).
      rewrite <-Rpower_O with (x:=3) at 1.
      apply Rle_Rpower.
      fourier.
      fourier.
      fourier.
      fourier.
      assert (3=Rpower 3 1).
      symmetry.
      apply Rpower_1.
      fourier.
      rewrite H2 at 3.
      replace (/3) with (1/3) by field.
      exact H1.
      symmetry.
      apply Rpower_plus.
      }
      replace (INR (S n)) with ((INR n)+1) by (rewrite S_INR; field). 
      replace ((INR n) + 1-4) with ((INR n) + -3) by field.
      replace ((INR n) + 1 + 1 -2) with (INR n) by field.
      replace (2 * Rpower 3 (INR n / 3)) with (Rpower 3 (INR n / 3) * 2) by field.
      replace ((INR n + -3) / 3) with ((INR n)/3 + (-3/3)) by field.
      replace (Rpower 3 ((INR n) / 3 + (-3 / 3))) with ((Rpower 3 ((INR n)/3))*(Rpower 3 (-3/3))).
      replace (4 * ((Rpower 3 ((INR n) / 3)) * Rpower 3 (-3 / 3))) with ((Rpower 3 ((INR n) / 3))*(4*(Rpower 3 (-3/3)))).
      apply Rfourier_lt.
      replace (-3/3) with (-1) by field.
      replace (-1) with (-(1)) by field.
      rewrite Rpower_Ropp.
      rewrite Rpower_1.
      fourier.
      fourier.
      assert (1<=Rpower 3 (INR n /3)).
      rewrite <-Rpower_O with (x:=3) at 1.
      apply Rle_Rpower.
      fourier.
      {
        clear.
        induction n.
        simpl.
        fourier.
        rewrite S_INR.
        rewrite Rdiv_plus_distr.
        fourier.
      }
      fourier.
      fourier.
      field.
      symmetry.
      apply Rpower_plus.
    }
  {
      rewrite H.
  assert ((S n mod 3) = 0)%nat.
  replace (S n) with (n+1)%nat.
  rewrite Nat.add_mod.  
  rewrite H.
  simpl.
  reflexivity.
  omega.
  omega.
  rewrite H0.
  simpl.
  induction n.  
  {
    simpl.
    replace (0-2) with (1+-3) by field.
    replace ((1+-3)/3) with (1/3+(-1)) by field.
    replace (Rpower 3 ((1/3)+(-1))) with ((Rpower 3 (1/3)) * (Rpower 3 (-1))).  
    replace (2 * (Rpower 3 (1 / 3) * Rpower 3 (-1)) ) with ((Rpower 3 (1/3)) * (2* (Rpower 3 (-1)))).
    assert ( Rpower 3 (1 / 3) = Rpower 3 (1 / 3) * 1).
    field.
    rewrite H1 at 2.
    apply Rfourier_lt.
    replace (-1) with (-(1)) by auto.
    rewrite Rpower_Ropp.
    rewrite Rpower_1.
    fourier.
    fourier.
    apply DWJ_helper4.
    field.
    symmetry.
    apply Rpower_plus.
   }
    { 
      replace (INR (S n)) with ((INR n) + 1).
      replace (INR n +1 -2) with (((INR n) + 2) + (- 3)) by field.
      replace ((INR n) + 1 + 1) with ((INR n) + 2) by field.
      replace (Rpower 3 ((INR n + 2) / 3)) with (Rpower 3 ((INR n + 2) / 3) * 1) by field.
      replace (Rpower 3 ((INR n + 2 + -3) / 3)) with ((Rpower 3 ((INR n +2)/3))*(Rpower 3 (-3/3))).
      replace  (2* (Rpower 3 ((INR n + 2) / 3) * Rpower 3 (-3 / 3))) with 
      (Rpower 3 ((INR n + 2) / 3) * (2* Rpower 3 (-3 / 3))) by field.
      apply Rfourier_lt.
      replace (-3/3) with (-(1)) by field.
      rewrite Rpower_Ropp.
      rewrite Rpower_1.
      fourier.
      fourier.
      apply DWJ_helper5.
      assert (0<=INR n).
      apply pos_INR.
      fourier.
      symmetry.
      replace (((INR n)+2 + -3)/3) with (((INR n) +2)/3 + (-3)/3) by field.
      apply Rpower_plus.
      rewrite S_INR.
      reflexivity.
    }
   }
Qed.

      
 
 (*** Here we prove that the function I is strictly increasing for all values of      n.   ****)
 
Theorem I_increasing:  forall m :nat, forall n:nat, ((n<m)%nat -> I n < I m).
Proof.
induction m.
{
  induction n.
  { 
  intro.
  inversion H.
  }
  {
    intros.
    omega.
  }
  }
  {
    assert (forall n m:nat, (n<m)\/ (n=m) \/ (m<n))%nat.
    intros.
    omega.
    intros.
    assert ((n < m)%nat \/ n = m \/ (m < n)%nat).
    apply H.
    destruct H1.
    {
      apply Rlt_trans with (r2:= I m).
      apply IHm.
      exact H1.
      apply Monotonic_helper.
    }
    destruct H1.
    {
      rewrite H1.
      apply Monotonic_helper.
    }
    {
      omega.
    }
  }
Qed.
(*** The function I is monotonically increasing, i.e., n<=m -> I(n) <= I(m) **)
Theorem I_monotonic:  forall m :nat, forall n:nat, ((n<=m)%nat -> I n <= I m).
Proof.
intros.
destruct H.
{
  fourier.
}
{
  assert (n<S m)%nat.
  omega.
  left.
  apply I_increasing.
  exact H0.
}
Qed.


