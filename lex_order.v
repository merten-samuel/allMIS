Require Import List.
Require Import Arith.
Require Import Omega.

Theorem list_in_dec : forall (x : nat) (X : list nat), {In x X} + { ~ In x X}.
Proof.
  apply in_dec.
  apply eq_nat_dec.
Defined.

Definition list_eq X Y :=
  forall x : nat, In x X <-> In x Y.

Theorem incl_list_eq : forall X Y, list_eq X Y <-> incl X Y /\ incl Y X.
Proof.
  intros.
  split;
  unfold list_eq.
  intros.
  unfold incl.
  split;
  intros;
  specialize (H a);
  intuition.
  intros.
  destruct H.
  unfold incl in *.
  split;
  intros;
  specialize (H x);
  specialize (H0 x);
  intuition.
Qed.

Theorem incl_dec : forall X Y : list nat, {incl X Y} + {~ incl X Y}.
Proof.
  intros.
  induction X.
  left.
  unfold incl.
  intros.
  inversion H.
  destruct IHX.
  assert ({In a Y} + {~In a Y}).
  apply in_dec.
  apply eq_nat_dec.
  destruct H;
  [left | right].
  unfold incl.
  intros.
  simpl In in *.
  intuition.
  replace a0;
  intuition.
  unfold not.
  intros.
  apply n.
  unfold incl in H.
  specialize (H a).
  apply H;
  intuition.
  right.
  unfold not;
  intros.
  apply n.
  unfold incl in *.
  intros.
  specialize (H a0).
  apply H.
  intuition.
Defined.

Theorem list_eq_dec : forall X Y, {list_eq X Y} + {~ list_eq X Y}.
Proof.
  intros.
  assert ( {incl X Y} + {~ incl X Y}).
  apply incl_dec.
  assert ({incl Y X} + {~ incl Y X} ).
  apply incl_dec.
  destruct H;
  destruct H0;
  [left | right | right | right];
  unfold not; 
  intros.
  apply incl_list_eq.
  intuition.
  apply n.
  apply incl_list_eq in H.
  intuition.
  apply n.
  apply incl_list_eq in H.
  intuition.
  apply n.
  apply incl_list_eq in H.
  intuition.
Defined. 

Theorem list_eq_ref :
  forall L, list_eq L L.
Proof. 
  intros.
  unfold list_eq.
  intuition.
Qed.

Theorem list_eq_symmetric :
  forall X Y, list_eq X Y -> list_eq Y X.
Proof.
  intros.
  unfold list_eq in *.
  intuition;
  apply H;
  intuition.
Qed.

Theorem list_eq_trans :
  forall X Y Z, list_eq X Y -> list_eq Y Z -> list_eq X Z.
Proof.
  intros.
  unfold list_eq in *.
  intuition.
  apply H0.
  apply H.
  intuition.
  apply H.
  apply H0.
  intuition.
Qed.

Fixpoint LeastElem (X : list nat) : option nat := 
  match X with
  | nil => None
  | cons x X' =>
      match LeastElem X' with
      | None => Some x
      | Some y =>  if (lt_dec x y) then Some x else Some y
      end
  end.

Theorem LeastElem_spec1 : forall X : list nat, X = nil <-> LeastElem X = None.
Proof.
  intros.
  split;
  intros.
  replace X.
  reflexivity.
  destruct X.
  reflexivity.
  simpl LeastElem in H.
  destruct LeastElem.
  destruct lt_dec in H;
  inversion H.
  inversion H.
Qed.

Theorem LeastElem_spec2 : forall X : list nat, X <> nil <-> exists x : nat,  LeastElem X = Some x.
Proof.
  split;
  intros.
  case_eq X;
  intuition.
  simpl LeastElem.
  case LeastElem.
  intros.
  destruct lt_dec;
  [exists n | exists n0];
  intuition.
  exists n.
  intuition.
  case_eq X.
  intros.
  replace X in H.
  destruct H.
  simpl LeastElem in H.
  inversion H.
  unfold not.
  intros.
  inversion H1.
Qed. 

Theorem LeastElemDec : forall (x : nat) (X : list nat), {LeastElem X = Some x} + {LeastElem X <> Some x}.
Proof.
  intros.
  destruct LeastElem.
  assert ({n = x} + {n <> x}).
  apply eq_nat_dec.
  destruct H as [H | H]; [left | right].
    replace n. intuition.
    unfold not. intros negH.
    inversion negH. intuition.
  right. unfold not; intros negH ; inversion negH.
Qed.

Theorem LeastElem_spec3 : forall (x : nat) (X : list nat), LeastElem X = Some x -> In x X.
Proof.
  intros.
  induction X.
  assert (LeastElem nil = None).
  apply LeastElem_spec1.
  intuition.
  replace (LeastElem nil) in H.
  inversion H.
  simpl LeastElem in H.
  destruct (LeastElem X).
  destruct lt_dec in H;
  inversion H;
  replace x;
  intuition.
  replace n;
  intuition.  
  inversion H.
  intuition.
Qed.

Theorem LeastElem_decons1 : forall (x y : nat) (X : list nat), LeastElem X = Some y -> (x <= y <-> LeastElem (cons x X) = Some x).
Proof.
  split;
  intros.
  simpl LeastElem.
  replace (LeastElem X).
  destruct lt_dec.
  intuition.
  assert (x = y).
  omega.
  intuition.
  simpl LeastElem in H0.
  replace (LeastElem X) in H0.
  destruct lt_dec in H0.
  omega.
  inversion H0.
  omega.
Qed.

Theorem LeastElem_decons2 : forall (x y : nat) (X : list nat), LeastElem X = Some y -> (y <= x <-> LeastElem (cons x X) = Some y).
Proof.
  split;
  intros.
  simpl LeastElem.
  replace (LeastElem X).
  destruct lt_dec.
  assert (x = y).
  omega.
  intuition.
  intuition.
  simpl LeastElem in H0.
  replace (LeastElem X) in H0.
  destruct lt_dec in H0.
  inversion H0.
  omega.
  omega.
Qed.

Theorem LeastElem_spec4 :
  forall (X : list nat),  LeastElem X = None \/ (exists x : nat, LeastElem X = Some x /\ (forall y : nat, In y X -> x <= y)).
Proof.  
  intros.
  induction X.
  left. reflexivity.
  right.
  destruct IHX.
  exists a.
  apply LeastElem_spec1 in H.
  replace X. simpl. intuition.
  destruct H.
  destruct H as [H0 H1].
  assert (H : {x <= a} + {a < x}).
  apply le_lt_dec.
  destruct H as [H | H].
  exists x.
  simpl LeastElem.
  replace (LeastElem X).
  destruct lt_dec.
  split; intros ; omega.
  split ; intuition.
  simpl In in H2.
  destruct H2 as [H2 | H2].
  omega.
  apply H1; intuition.
  exists a.
  simpl LeastElem.
  replace (LeastElem X).
  destruct lt_dec.
  split; intros.
  intuition.
  simpl In in H2.
  destruct H2 as [H2 | H2].
  omega.
  apply H1 in H2. omega.
  intuition.
Qed.

Fixpoint Subtract_list (X Y : list nat) :=
  match X with
  | nil => nil
  | cons x X' =>
     if list_in_dec x Y
       then Subtract_list X' Y
       else cons x (Subtract_list X' Y)
  end.

Theorem Subtract_list_r_nil : forall X : list nat, Subtract_list X nil = X.
Proof.
  intros.
  induction X.
  simpl. reflexivity.
  simpl.
  rewrite -> IHX.
  reflexivity.
Qed.

Theorem Subtract_list_l_nil : forall X : list nat, Subtract_list nil X = nil.
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Theorem Subtract_list_spec : forall (x : nat) (X Y : list nat),  In x (Subtract_list X Y) <-> (In x X /\ ~ In x Y).
  split; 
  intros.
  induction X.
  simpl Subtract_list in H.
  inversion H.
  simpl Subtract_list in H.
  destruct list_in_dec.
  apply IHX in H.
  simpl In. intuition.
  simpl In in H.
  destruct H.
  replace x.
  intuition.
  apply IHX in H.
  simpl In. intuition.
  destruct H as [H H0].
  induction X.
  inversion H.
  simpl In in H.
  destruct H as [H | H];
  simpl Subtract_list; 
  destruct list_in_dec.
  replace a in i. intuition.
  replace x. intuition.
  apply IHX. intuition.
  apply IHX in H.
  simpl In.
  intuition.
Qed.
 (*Finds the smallest element of X, but not Y*)
Definition delta_min ( X Y : list nat) : option nat := 
  LeastElem (Subtract_list X Y).    

  (*Let's prove it!*)
Theorem delta_min_dec : forall X Y : list nat,
  delta_min X Y = None \/
  (exists x : nat,
    delta_min  X Y = Some x /\
                     In x X /\
                     ~ In x Y /\
                     forall y : nat, In y X -> ~ In y Y -> x <= y).
Proof.
  intros.
  unfold delta_min.
  assert ( forall (X : list nat),  LeastElem X = None \/ (exists x : nat, LeastElem X = Some x /\ (forall y : nat, In y X -> x <= y))).
  apply LeastElem_spec4.
  specialize (H (Subtract_list X Y)).
  destruct H.
  intuition.
  right.
  destruct H.
  exists x.
  destruct H.
  split.
  exact H.
  assert (In x X /\ ~ In x Y).
  apply Subtract_list_spec.
  apply LeastElem_spec3.
  exact H.
  split; intuition.
  assert (In y (Subtract_list X Y)).
  apply Subtract_list_spec.
  intuition.
  apply H0.
  intuition.
Qed.

Theorem delta_min_disj : forall X Y : list nat, delta_min X Y = None \/ delta_min X Y <> delta_min Y X.
Proof.
  intros.
  assert (delta_min X Y = None \/ (exists x : nat,
                                    delta_min  X Y = Some x /\
                                    In x X /\
                                    ~ In x Y /\
                                    forall y : nat, In y X -> ~ In y Y -> x <= y)).
  apply delta_min_dec.
  assert (delta_min Y X = None \/ (exists y : nat,
                                    delta_min  Y X = Some y /\
                                    In y Y /\
                                    ~ In y X /\
                                    forall x : nat, In x Y -> ~ In x X -> y <= x)).
  apply delta_min_dec.
  destruct H. intuition.
  destruct H0.
  destruct H. destruct H.  right. replace (delta_min X Y). replace (delta_min Y X). intuition.  inversion H2.
  right.
  unfold not. intros.
  destruct H. destruct H0. intuition.
  rewrite -> H2 in H1. rewrite -> H in H1.
  inversion H1.
  rewrite <- H9 in H3.
  intuition.
Qed.

Theorem delta_min_l_nil : forall  X, delta_min X nil = LeastElem X.
Proof.
  intros.
  unfold delta_min.
  rewrite -> Subtract_list_r_nil.
  reflexivity.
Qed.

Theorem delta_min_r_nil : forall X, delta_min nil X = None.
Proof.
  intros.
  unfold delta_min.
  rewrite -> Subtract_list_l_nil.
  simpl.
  reflexivity.
Qed.


Theorem delta_min_subs : forall X Y : list nat, delta_min X Y = None <-> forall x : nat, In x X -> In x Y.
Proof.
  split; intros.
  unfold delta_min in H.
  induction X.
  inversion H0.
  simpl LeastElem in H.
  destruct list_in_dec in H.
    simpl In in H0. destruct H0.
    replace a in i. intuition.
    apply IHX. intuition.
    exact H0.
  assert (exists n : nat,  LeastElem (a :: Subtract_list X Y) = Some n).
    apply LeastElem_spec2.
    unfold not. intros. inversion H1.
  destruct H1.
  rewrite H1 in H. inversion H.
  induction X.
  simpl.
  simpl.
  rewrite -> delta_min_r_nil.
  intuition.
  unfold delta_min.
  simpl.
  destruct list_in_dec.
  apply IHX.
  intros. apply H. simpl. right. exact H0.
  assert (In a (a::X)).
  intuition.
  specialize H.
  apply H in H0.
  intuition.
Qed.

Inductive list_order :=
| lt_list : list_order
| eq_list : list_order
| gt_list : list_order.

Fixpoint dec_order (X Y : list nat) : list_order :=
  match delta_min X Y with
  | None =>
      match delta_min Y X with
      | None => eq_list 
      | Some y => gt_list
      end
  | Some x =>
      match delta_min Y X with
      | None => lt_list 
      | Some y => 
          if lt_dec x y
          then lt_list 
          else gt_list
      end
  end.

(*Connexity of the above program *)
Theorem dec_order_dec : forall X Y : list nat, {dec_order X Y = lt_list} + {dec_order X Y = eq_list} + {dec_order X Y = gt_list}.
Proof.
  intros.
  destruct dec_order; intuition.
Qed.

Theorem dec_order_nil_l_neg : forall X Y : list nat, dec_order nil X <> lt_list.
Proof.
  intros.
  simpl.
  destruct delta_min;
  intuition; inversion H.
Qed.

Theorem dec_order_nil_r_neg : forall X Y : list nat, dec_order X nil <> gt_list.
Proof.
  intros.
  destruct X.
  simpl; unfold not; intros; inversion H.
  unfold dec_order.
  rewrite -> delta_min_r_nil.
  destruct delta_min;
  unfold not;
  simpl; intros; inversion H.
Qed.

Example dec_order_nil : forall X Y : list nat, dec_order nil nil = eq_list.
Proof.
  intros.
  simpl.
  reflexivity.
Qed.
  (*Show that dec_order's eq is equivalent to the membership def in list_eq *)
Theorem dec_order_eq_spec : forall X Y : list nat, dec_order X Y = eq_list <-> list_eq X Y.
Proof.
  intros.
  unfold list_eq.
  split; intros.
  assert (delta_min X Y = None).
    unfold dec_order in H.
    destruct X; destruct Y;
    destruct delta_min;
      try (destruct lt_dec; inversion H); try intuition.
      destruct delta_min. destruct lt_dec. inversion H.
      inversion H. inversion H.
      destruct delta_min. destruct lt_dec.
      inversion H. inversion H. inversion H.
      destruct delta_min. destruct lt_dec.
      inversion H. inversion H. inversion H.
  assert (delta_min Y X = None).
    unfold dec_order in H.
    destruct X; destruct Y;
    destruct delta_min;
      try (destruct lt_dec; inversion H); try intuition.
      destruct delta_min. destruct lt_dec. inversion H.
      inversion H. inversion H.
      destruct delta_min.
        inversion H. reflexivity.
        destruct delta_min. destruct lt_dec.
        inversion H. inversion H. inversion H.
        destruct delta_min. inversion H. reflexivity.
  split; apply delta_min_subs; intuition.
  assert (delta_min X Y = None).
    apply delta_min_subs.
    apply H.
  assert (delta_min Y X = None).
    apply delta_min_subs.
    apply H.
  destruct X.
  simpl. rewrite -> H1. reflexivity.
  simpl. rewrite -> H0. rewrite -> H1. reflexivity.
Qed.

(*Show that lt is the dual of gt *)
Theorem dec_order_dual_spec : forall X Y : list nat, dec_order X Y = lt_list <-> dec_order Y X = gt_list.
Proof.
  split;
  intros.
  unfold dec_order in *.
  destruct Y; destruct X; simpl in *.
    inversion H.
    destruct delta_min.
      intuition.
      inversion H.
    destruct delta_min.
      intuition.
      inversion H.
    destruct delta_min;
    destruct delta_min.
    destruct lt_dec; destruct lt_dec;
    try omega; try reflexivity; try inversion H.
    reflexivity. inversion H. inversion H.
  unfold dec_order in *.
  destruct Y; destruct X; simpl in *.
    inversion H.
    destruct delta_min.
      intuition.
      inversion H.
    destruct delta_min.
      intuition.
      inversion H.
    remember (delta_min (n0 :: X) (n :: Y)) as i.
    remember (delta_min (n :: Y) (n0 :: X)) as j.
    assert (i <> j).
    unfold not; intros.
      assert (~ (j = None /\ i = None)).
        unfold not; intros.
        destruct H1.
        rewrite -> H1 in H.
        rewrite -> H2 in H.
        inversion H.
      assert (delta_min (n0 :: X) (n :: Y) = None \/ delta_min (n0 :: X) (n :: Y) <> delta_min (n :: Y) (n0 :: X)).
      apply delta_min_disj.
      destruct H2. rewrite -> H2 in Heqi. rewrite -> Heqi in H0.
      apply H1. split. intuition. intuition.
      rewrite <- Heqi in H2. rewrite <- Heqj in H2.
      intuition.
    destruct delta_min; destruct delta_min;
      replace i in H0; replace j in H0;
      rewrite -> Heqj in H; rewrite -> Heqi in H; replace i; replace j.
    destruct lt_dec; destruct lt_dec.
      reflexivity.
      inversion H.
      reflexivity.
      assert (n1 = n2). omega. assert (Some n1 = Some n2). intuition. intuition.
      reflexivity.
      inversion H.
      intuition.
Qed.

Theorem delta_min_in : forall (x : nat) (X Y : list nat), delta_min X Y = Some x -> In x X.
Proof.
  intros x X Y H0.
  assert (delta_min X Y = None \/
           (exists x : nat,
           delta_min X Y = Some x /\
           In x X /\ ~ In x Y /\ (forall y : nat, In y X -> ~ In y Y -> x <= y))) as H1.
  apply delta_min_dec.
  destruct H1 as [H1 | [n [H1 [H2 [H3 H4]]]]].
  rewrite -> H1 in H0. inversion H0.
  rewrite -> H0 in H1.
    assert (x = n) as H5. inversion H1. reflexivity.
    rewrite -> H5. apply H2.
Qed.

Theorem delta_min_neg_in : forall x X Y, delta_min X Y = Some x -> ~ In x Y.
Proof.
  intros x X Y H0.
  assert (delta_min X Y = None \/
           (exists x : nat,
           delta_min X Y = Some x /\
           In x X /\ ~ In x Y /\ (forall y : nat, In y X -> ~ In y Y -> x <= y))) as H1.
  apply delta_min_dec.
  destruct H1 as [H1 | [n [H1 [H2 [H3 H4]]]]].
  rewrite -> H1 in H0. inversion H0.
  rewrite -> H0 in H1.
    assert (x = n) as H5. inversion H1. reflexivity.
    rewrite -> H5. apply H3.
Qed.
