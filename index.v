Set Implicit Arguments.

Require Import Arith List ProofIrrelevance Omega.

Require Import eqtype fintype.

Module Index. Section index.
  Variable N : nat.
                
  Inductive ty : Type := mk : forall (i : nat) (pf : i < N), ty.
End index. End Index.

Definition Ix (N : nat) := Index.ty N.

Definition Ix0 (N : nat) (H : 0 < N) : Ix N := @Index.mk N 0 H.

Definition eq_Ix (N : nat) (ix iy : Ix N) : bool :=
  match ix, iy with
    | Index.mk x _, Index.mk y _ =>
      if eq_nat_dec x y then true else false
  end.

Lemma eq_Ix_eq N (ix iy : Ix N) : reflect (ix = iy) (eq_Ix ix iy).
Proof.
  unfold eq_Ix; destruct ix; destruct iy.
  destruct (eq_nat_dec i i0); constructor. subst i0.
  assert (pf = pf0) as -> by apply proof_irrelevance. auto.
  intros Contra; inversion Contra; apply n; auto.
Defined.

Definition eqType_Ix_mixin (N : nat) :=
  @eqTypeMixin _ (@eq_Ix N) (@eq_Ix_eq N).

Definition eqType_Ix (N : nat) : eqType :=
  Eval hnf in EqType _ (eqType_Ix_mixin N).

Canonical Structure eqType_Ix.

Definition lift (N : nat) (ix : Ix N) : Ix (S N) :=
  match ix with
    | Index.mk x pf => @Index.mk (S N) x (lt_trans _ _ _ (@lt_n_Sn _) (lt_n_S _ _ pf))
  end.

Fixpoint Ix_enum_aux (N : nat) (H : 0 < N) {struct N} : list (Ix N).
  refine ((match N return N = _ -> list (Ix N) with
            | O => fun pf => _
            | S N' => fun pf => 
              (match N' return N' = _ -> list (Ix (S N')) with
                | O => fun pf' => Ix0 _ :: nil
                | S N'' => fun pf' => _
               end) eq_refl
           end) eq_refl).
  { rewrite pf in H; destruct (lt_irrefl _ H). }
  { apply le_n. }
  assert (Hlt : S N'' < S (S N'')) by apply le_n.
  refine (Index.mk Hlt :: _).
  assert (H0 : 0 < N') by (rewrite <-pf'; apply lt_0_Sn).
  refine (map (@lift (S N'')) _).
  rewrite pf'; refine (Ix_enum_aux _ H0).
Defined.

Lemma zero_lt_succ n : 0 < S n. Proof. omega. Qed.

Definition Ix_enum (N : nat) : list (Ix N) :=
  match N with
    | O => nil
    | S n' => Ix_enum_aux (zero_lt_succ n')
  end.
