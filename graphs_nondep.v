Require Import List.
Require Import Arith.
Require Import Omega.
Require Import lex_order.
Section IS.
Variable V : nat. (* The number of vertices *)
Variable E : list (nat*nat).

Variable NoSelfEdges : forall x : nat, ~ In (x,x) E.
Variable Edges_lt_V : forall x y, In (x, y) E -> x < V.
Variable EdgesBidirectional : 
  forall x y : nat, In (x,y) E -> In (y,x) E.

Definition ValidSet (X : list nat) :=
  forall x : nat, In x X -> x < V.

Definition Independent (X : list nat) :=
  forall x y, In x X -> In y X -> ~ In (x,y) E.

Inductive IndSet (X : list nat) : Prop :=
| defIndSet : ValidSet X -> Independent X -> IndSet X.

Inductive MaximalIndSet (X : list nat) : Prop :=
| defMaximalIndSet :
    IndSet X ->
    (forall x, ~ In x X -> ~ IndSet (x::X)) ->
      MaximalIndSet X.

Theorem validSetRecr : 
  forall (x : nat) (X : list nat), ValidSet (x::X) -> ValidSet X.
Proof.
  intros. intros y H0.
  apply H. right. auto.
Qed.

Theorem ValidSet_dec :
  forall X : list nat, {ValidSet X}+{~ValidSet X}.
Proof.
  intros. induction X.
  left. intros x H. inversion H.
  destruct IHX. assert ( {V <= a} + {a < V}).
  apply le_lt_dec. destruct H. 
  right. intros H0. 
  assert (In a (a::X)). left. auto.
  apply H0 in H. omega. left.
  intros b H. destruct H. omega.
  apply v in H. auto. right.
  intros H. apply validSetRecr in H.
  auto.
Defined.

Theorem edgeEqDec : forall X Y : (nat*nat), {X=Y} + {X<>Y}.
Proof.
  intros.
  destruct X.
  destruct Y.
  assert ({n=n1}+{n<>n1}).
  apply eq_nat_dec.
  assert ({n0= n2}+{n0<>n2}).
  apply eq_nat_dec.
  destruct H.
  destruct H0.
  left. intuition.
  right.
  intuition. inversion H.
  intuition.
  right.
  unfold not. intros.
  inversion H.
  intuition.
Defined.
 

Theorem inEdgeDec : forall X : (nat*nat), {In X E}+{~In X E}.
Proof.
  intros.
  clear NoSelfEdges Edges_lt_V EdgesBidirectional.
  induction E.
  right. unfold not. intros. inversion H.
  destruct IHl.
  left. intuition.
  assert ({X =a}+{~X=a}).
  apply edgeEqDec.
  destruct H.
  left. intuition.
  simpl.
  left. intuition.
  right. simpl.
  unfold not. intros.
  intuition.
Defined.  

Fixpoint vertexConnected (v : nat) (S : list nat) : bool :=
  match S with
  | nil => false
  | cons s S' => if inEdgeDec (v,s) then true else vertexConnected v S'
  end.

Theorem vertexConnected_spec :
forall (v : nat) (S: list nat),
    vertexConnected v S = true <-> exists (v' : nat), In v' S /\ In (v,v') E. 
Proof.
  split; intros;
  induction S.
  simpl in H.
  inversion H.
  simpl vertexConnected in H.
  destruct inEdgeDec in H.
  exists a.
  split; intuition.
  apply IHS in H.
  destruct H.
  exists x. split; intuition.
  destruct H.
  destruct H.
  inversion H.
  simpl.
  destruct inEdgeDec.
  intuition.
  destruct H.
  destruct H.
  apply IHS.
  exists x.
  simpl in H.
  destruct H.
  replace x in H0.
  intuition.
  intuition.
Qed.

Theorem vertexConnected_spec_neg :
forall (v : nat) (S: list nat),
  vertexConnected v S = false <-> ~ exists (v' : nat), In v' S /\ In (v,v') E.
Proof.
  split.
  unfold not.
  intros.
  apply vertexConnected_spec in H0.
  replace (vertexConnected v S) with false in H0.
  intuition.
  intros.
  unfold not in H.
  assert ({vertexConnected v S = true} + {vertexConnected v S = false}).
  destruct vertexConnected; intuition.
  destruct H0.
  apply vertexConnected_spec in e.
  intuition.
  intuition.
Qed.  

Fixpoint independent (X :  list nat) :=
  match X with
  | nil => true
  | x::X' => if vertexConnected x X then false else independent X'
  end.

Theorem independent_spec :
forall X : list nat,
  independent X = true <-> Independent X. 
Proof.
  unfold Independent. split. 
  intros. induction X. inversion H0.
  simpl In in H0. simpl In in H1.
  destruct H0; destruct H1;
  repeat subst. inversion H.
  destruct inEdgeDec in H1.
  inversion H1. assumption.  
  inversion H. destruct inEdgeDec in H2.
  inversion H2. remember (vertexConnected x X).
  destruct b. inversion H2.
  symmetry in Heqb. apply vertexConnected_spec_neg in Heqb.
  intros H3. apply Heqb. exists y; split; assumption.
  inversion H. destruct inEdgeDec in H2.
  inversion H2. remember (vertexConnected y X).
  destruct b. inversion H2.
  symmetry in Heqb. apply vertexConnected_spec_neg in Heqb.
  intros H3. apply Heqb. exists x; split; try assumption.
  apply EdgesBidirectional. auto. apply IHX; try auto.
  inversion H. destruct inEdgeDec. inversion H3.
  destruct vertexConnected. inversion H3.
  reflexivity. intros. induction X. auto.
  simpl independent. destruct inEdgeDec.
  apply False_rec. specialize (H a a).
  apply H; try (left; auto). assumption.
  remember (vertexConnected a X).
  destruct b. symmetry in Heqb.
  apply vertexConnected_spec in Heqb.
  destruct Heqb as [v' [H0 H1]].
  apply False_rec. apply H with (x :=  a) (y := v');
  auto. left. auto. right. auto.
  apply IHX. intros. symmetry in Heqb.
  apply H; right; auto.
Qed.

Theorem Independent_dec : forall X, {Independent X} + {~ Independent X}.
Proof.
  intros X. remember (independent X).
  destruct b; [left | right]. apply independent_spec.
  auto. intros H. apply independent_spec in H.
  rewrite <- Heqb in H. inversion H.
Defined.

Theorem IndSetDec : forall X : list nat, {IndSet X} + {~IndSet X}.
  intros. destruct (ValidSet_dec X);
  [destruct (Independent_dec X) | right].
  left; constructor; auto.
  right. intros H. inversion H. auto.
  intros H. inversion H. auto.
Defined.

Theorem MaximalBound :
forall (x : nat) (X : list nat),
  x >= V -> ~ MaximalIndSet (x::X).
Proof.
  unfold not. intros.
  inversion H0. subst.
  inversion H1. subst.
  assert (In x (x::X)).
  left. auto. apply H3 in H5.
  omega.
Qed.

Fixpoint StepMaximalIndSet (X : list nat) (n : nat) :=
  match n with
  | O => if (IndSetDec (n::X)) then (n::X) else X
  | S m => if IndSetDec (n::(StepMaximalIndSet X m))
             then (n::(StepMaximalIndSet X m))
             else StepMaximalIndSet X m
  end.

Definition MkMaximalIndSet (S : list nat) : list nat :=
  StepMaximalIndSet S (pred V). 

Theorem StepMaximalIndSet_spec : forall (n : nat) (X : list nat), IndSet X -> IndSet (StepMaximalIndSet X n).
Proof.
  intros.
  induction n.
  unfold StepMaximalIndSet.
  case IndSetDec; intuition.
  simpl.
  case IndSetDec;
  intuition.
Qed.

Theorem ConnectedApp :
  forall (X X' : list nat) (n : nat), vertexConnected n X = true -> vertexConnected n (X'++ X) = true.
Proof.
  intros.
  apply vertexConnected_spec in H.
  apply vertexConnected_spec.
  destruct H.
  destruct H.
  exists x.
  intuition.
Qed.

Theorem TrivialIndSet : V = 0 -> forall X, MaximalIndSet X -> X = nil.
Proof.
  intros. inversion H0. inversion H1.
  destruct X. auto.
  assert (In n (n::X)) as H5.
  left. auto. apply H3 in H5.
  omega.
Qed.

Theorem nilIndSet : IndSet nil.
Proof.
  constructor. unfold ValidSet. intros x H0.
  inversion H0. unfold Independent. intros.
  inversion H.
Qed.

Theorem IndCons : forall (x : nat) (X : list nat), Independent (x::X) -> Independent X.
Proof.
  intros. unfold Independent in *.
  intros. apply H; right; auto.
Qed.

Theorem IndSetCons :
  forall (x : nat) (X : list nat), IndSet (x::X) -> IndSet X.
Proof.
  intros. inversion H.
  constructor. intros y H2.
  apply H0. right. auto.
  apply IndCons in H1. auto.
Qed.

Theorem IndSetApp :
  forall (x : nat) (X X': list nat),
    IndSet X ->
    ~ IndSet (x::X) -> ~ IndSet (x::(X' ++ X)).
Proof.
  intros. intros H1. apply H0.
  constructor. intros y H2. inversion H1.
  apply H3. destruct H2 as [H2 | H2].
  left. auto. right. apply in_or_app.
  auto. unfold Independent.
  intros y z H2 H3. inversion H1.
  apply H5. destruct H2. left. auto.
  right. apply in_or_app. right. auto.
  destruct H3. left. auto.
  right. apply in_or_app. right. auto.
Qed.
  
Theorem MkMaximalIndSet_spec1 : forall X, IndSet X -> IndSet(MkMaximalIndSet X).
Proof.
  intros. induction X. simpl.
  unfold MkMaximalIndSet. destruct V.
  simpl. case IndSetDec;
  intuition. apply StepMaximalIndSet_spec.
  assumption. unfold MkMaximalIndSet in *.
  destruct V. simpl.
  case IndSetDec;
  intuition.
  apply StepMaximalIndSet_spec.
  intuition.
Qed.

Theorem StepMaximalIndSet_decons :
  forall (n : nat)(X : list nat),
    IndSet X -> exists (X' : list nat), StepMaximalIndSet X n = X' ++ X.
Proof.
  intros.
  induction n.
  unfold StepMaximalIndSet.
  destruct IndSetDec.
  exists (cons 0 nil).
  intuition.
  exists nil.
  intuition.
  simpl StepMaximalIndSet.
  destruct IHn.
  destruct IndSetDec.
  replace (StepMaximalIndSet X n).
  exists (S n :: x).
  intuition.
  replace (StepMaximalIndSet X n).
  exists x.
  intuition.
Qed.

Theorem MkMIS_to_StepMIS :
  forall X, exists n, MkMaximalIndSet X = StepMaximalIndSet X n.
Proof.
  intros. 
  remember V.
  induction n;
  unfold MkMaximalIndSet;
  replace V;
  [exists 0 | exists n];
  induction X;
  intuition.
Qed.

Theorem MkMaximalIndSet_deapp :
  forall X, IndSet X -> exists X', MkMaximalIndSet X = X'++X.
Proof.
  intros.
  assert (exists n : nat, MkMaximalIndSet X = StepMaximalIndSet X n).
  apply MkMIS_to_StepMIS.
  destruct H0.
  replace (MkMaximalIndSet X).
  apply (StepMaximalIndSet_decons).
  intuition.
Qed.

Theorem IndSet_destr :
  forall (X : list nat) (m : nat), IndSet X -> m < V -> ~ IndSet (m::X) -> vertexConnected m X = true.
Proof.
  intros.
  induction X.
  assert (IndSet (m::nil)).
  constructor.
  unfold ValidSet.
  simpl In.
  intros. destruct H2;
  intuition. unfold Independent.
  intros.
  destruct H2, H3; auto.
  repeat subst. apply NoSelfEdges.
  auto.
  simpl vertexConnected.
  destruct inEdgeDec. auto.
  apply IHX. apply IndSetCons in H.
  auto. intros H2. apply H1.
  constructor. inversion H2.
  intros y H5. destruct H5 as [H5 | [H5| H5]];
  subst. apply H2. left. auto. apply H. left. auto.
  apply H3. right. auto. intros y z H3 H4.
  destruct H3 as [H3 | H3];
  destruct H4 as [H4 | H4]; repeat subst.
  apply NoSelfEdges. destruct H4 as [H4 | H4].
  subst. auto. apply H2. left. auto.
  right. auto. destruct H3 as [H3 | H3].
  subst. intros n'. apply n.
  apply EdgesBidirectional. auto.
  apply H2. right. auto. left. auto.
  apply H; auto.
Qed.

(*show that for everything less than n, this has to either contain that value or there's an edge between the constructed set. *)
Theorem IndSetConstraint :
  forall (X : list nat) (m : nat),
    IndSet X ->
    m < V ->
    ~ In m (StepMaximalIndSet X m) ->
      vertexConnected m (StepMaximalIndSet X m) = true.
Proof.
  intros.
  induction m.
  simpl StepMaximalIndSet in *.
  destruct IndSetDec.
  assert False.
  apply H1.
  intuition.
  intuition.
  apply IndSet_destr;
  intuition.
  simpl StepMaximalIndSet in *.
  destruct IndSetDec.
  assert False.
  apply H1.
  intuition.
  intuition.
  apply IndSet_destr.
  apply StepMaximalIndSet_spec.
  intuition.
  intuition.
  exact n.
Qed.

Theorem StepMaximalIndSet_decomp : 
  forall (X : list nat) (n m: nat),
    m <= n -> exists (X' : list nat), (StepMaximalIndSet X n) = X'++(StepMaximalIndSet X m) /\
                                      forall y : nat, In y X' -> y > m.
Proof.
  intros.
  induction n.
  assert (m = 0).
  omega.
  replace m.
  exists nil.
  intuition. inversion H1.
  assert (m <= n \/ m = S n).
  omega.
  destruct H0.
  assert (m <= n) as i.
  intuition.
  apply IHn in H0.
  destruct H0.
  destruct H0.
  simpl StepMaximalIndSet.
  destruct IndSetDec.
  exists (S n :: x).
  replace (StepMaximalIndSet X n).
  intuition.
  simpl In in H3.
  destruct H3.
  omega.
  intuition.
  exists x.
  intuition.
  replace m.
  exists nil.
  intuition. inversion H1.
Qed.

Theorem IndSetConstraint_gen :
  forall (X : list nat ) (n m : nat),
    IndSet X ->
    n < V ->
    m <= n ->
    ~ In m (StepMaximalIndSet X n) ->
      vertexConnected m (StepMaximalIndSet X n) = true.
Proof.
  intros.
  assert (exists (X' : list nat),
            (StepMaximalIndSet X n) = X'++(StepMaximalIndSet X m) /\
            forall y : nat, In y X' -> y > m).
  apply StepMaximalIndSet_decomp; intuition.
  destruct H3.
  destruct H3.
  replace (StepMaximalIndSet X n) in *.
  apply ConnectedApp.
  assert (~ In m (StepMaximalIndSet X m)).
  unfold not.
  intros.
  apply H2.
  apply in_or_app.
  intuition.
  induction m.
  simpl StepMaximalIndSet in *.
  destruct IndSetDec.
  intuition.
  apply IndSet_destr;
  intuition.
  simpl StepMaximalIndSet in *.
  destruct IndSetDec.
  intuition.
  apply IndSet_destr; intuition.
  apply StepMaximalIndSet_spec.
  intuition.
Qed.

Theorem MkMaximalIndSet_red : forall (X : list nat) (n : nat), V = S n -> MkMaximalIndSet X = StepMaximalIndSet X n.
Proof.
  intros.
  unfold MkMaximalIndSet;
  intros.
  replace V;
  induction X; intuition.
Qed.

 (*Find a limit on expanding the S' in the proof below *)
Theorem MkMaximalIndSet_spec2 : forall X, IndSet X -> MaximalIndSet (MkMaximalIndSet X).
Proof.
  intros. constructor.
  apply MkMaximalIndSet_spec1. auto.
  intros. assert (x < V \/ x >= V).
  omega.
  destruct H1.
  assert ( {m : nat | S m = V} + {0 = V}).
  apply O_or_S.
  destruct H2.
  destruct s. 
  assert ( MkMaximalIndSet X = StepMaximalIndSet X x0).
  apply MkMaximalIndSet_red. auto. rewrite -> H2 in H0.
  assert (vertexConnected x (StepMaximalIndSet X x0) = true).
  apply IndSetConstraint_gen;
  auto; omega.
  apply vertexConnected_spec in H3.
  intros H4. destruct H3 as [v' [H3 H3']].
  apply H4 in H3'; auto. left. auto.
  rewrite -> H2. right. auto.
  unfold MkMaximalIndSet in H0.
  rewrite <- e in H0. simpl in H0.
  destruct IndSetDec. inversion i.
  unfold ValidSet in H2. assert (In 0 (0::X)) as H4.
  left. auto. apply H2 in H4. omega. 
  omega. intros H2. inversion H2.
  assert (In x (x::(MkMaximalIndSet X))).
  left. auto. apply H3 in H5. omega.
Qed.

Theorem MIS_nil_iff_0 : MaximalIndSet nil <-> V = 0.
Proof.
  split.
  (* -> *)
  intros H0.
  assert ( {V <= 0} + {0 < V} ) as H1. apply le_lt_dec.
  destruct H1 as [H1 | H1].
    (* V <= 0 *)
    omega.
    (* 0 < v *)
    inversion H0.
    apply False_rec.
    specialize (H2 0).
    apply H2. intros H3. inversion H3.
    constructor. intros x H3. inversion H3.
    omega. inversion H4.
    intros x y H3 H4. destruct H3;
    destruct H4; repeat subst.
    apply NoSelfEdges. inversion H4.
    inversion H3. inversion H3.
  intros. constructor. apply nilIndSet.
  intros x H0 H1. inversion H1.
  specialize (H2 x). assert (In x (x::nil)) as H4.
  left. auto. apply H2 in H4. omega.
Qed.

Theorem IndSet_cons : forall (l : list nat) (x : nat), ~IndSet l -> ~ IndSet (x::l).
Proof.
  intros l x H0 H1.
  apply H0. apply IndSetCons in H1.
  auto.
Qed. 

Theorem IndSet_lift_spec : forall (l : list nat) (x : nat),
  MaximalIndSet l -> x < V -> IndSet (x::l) -> In x l.
Proof.
  intros. destruct H as [[H2 H3] H4].
  assert ( {In x l}+{~In x l} ) as H5 by (apply in_dec; apply (eq_nat_dec)).
  destruct H5 as [H5 | H5]. assumption.
  apply False_rec. apply H4 in H5. contradiction.
Qed.


Theorem IndSet_order : forall X Y : list nat, IndSet (X++Y) -> IndSet (Y ++ X).
Proof.
  intros X Y H0. inversion H0. constructor.
  unfold ValidSet. intros x H2. apply H0.
  apply in_or_app. apply in_app_or in H2.
  destruct H2 as [H2 | H2]; [right | left]; auto.
  intros x y H2 H3. apply H1;
  apply in_or_app; apply in_app_or in H2;
  apply in_app_or in H3; destruct H2 as [H2 | H2];
  destruct H3 as [H3 | H3]; auto.
Qed.
    
Theorem VertexConnected_order :
  forall (x : nat) (X Y : list nat),
    vertexConnected x (X++Y) = vertexConnected x (Y++X).
  intros x X Y.
    assert ({vertexConnected x (X++Y) = true} + {vertexConnected x (X++Y) = false}).
      destruct (vertexConnected x (X++Y)); intuition.  
    assert ({vertexConnected x (Y++X) = true} + {vertexConnected x (Y++X) = false}).
      destruct (vertexConnected x (Y++X)); intuition.
    destruct H; destruct H0.
      rewrite -> e. intuition.
      apply vertexConnected_spec in e.
        apply vertexConnected_spec_neg in e0.
        assert False as F. apply e0. destruct e as [e [H0 H1]].
        exists e. split.
          apply in_app_or in H0. apply in_or_app. intuition.
          apply H1.
        inversion F.
      apply vertexConnected_spec in e0.
        apply vertexConnected_spec_neg in e.
        assert False as F. apply e. destruct e0 as [e0 [H0 H1]].
        exists e0. split.
          apply in_app_or in H0. apply in_or_app. intuition.
          apply H1.
        inversion F.
      rewrite -> e. intuition.
Qed.
    
Theorem MaximalIndSet_order : forall ( X Y : list nat), MaximalIndSet (X ++ Y) -> MaximalIndSet (Y ++ X).
Proof. 
  intros X Y H0. inversion H0. constructor. apply IndSet_order. auto.
  intros x H2 H3. assert (~ In x (X++Y)) as H4.
  intros H4. apply H2. apply in_app_or in H4.
  apply in_or_app. destruct H4 as [H4 | H4]; auto.
  apply H1 in H4. apply H4.
  constructor. intros. intros y H5.
  destruct H5 as [H5 | H5]. apply H3.
  left. auto. apply H0. auto.
  intros y z H5 H6. apply H3.
  destruct H5 as [H5 | H5].
  left. auto. right. apply in_app_or in H5.
  destruct H5 as [H5 | H5];
  apply in_or_app; auto.
  destruct H6 as [H6 | H6].
  left. auto. right. apply in_app_or in H6.
  destruct H6 as [H6 | H6];
  apply in_or_app; auto.
Qed.

Theorem neg_incl_witness : forall X Y : list nat, ~ incl Y X -> exists n : nat, In n Y /\ ~ In n X.
Proof.
  intros. induction Y.
    assert (incl nil X). unfold incl. intros a H0. inversion H0. apply H in H0. destruct H0.
    unfold incl in H.
    assert ({In a X} + {~In a X}).
      apply in_dec. apply eq_nat_dec.
    destruct H0 as [H0 | H0].
    assert (~ incl Y X).
      intros H1.
      unfold incl in H1.
      assert (forall a0 : nat, In a0 (a :: Y) -> In a0 X).
        intros a0 H2. specialize (H1 a0). simpl In in H2. destruct H2 as [H2 | H2].
          rewrite <- H2. apply H0.
          apply H1 in H2. apply H2.
      apply H in H2.
      apply H2.
    apply IHY in H1.
    destruct H1 as [n0 [H1 H2]].
    exists n0.
    split.
      simpl. right. apply H1.
      apply H2.
    exists a. split.
      simpl. left. reflexivity.
      apply H0.
Qed. 


Theorem MaximalIndSet_subs : forall X Y : list nat, incl X Y -> MaximalIndSet X -> MaximalIndSet Y -> list_eq X Y.
Proof.
  intros X Y H0 H1 H2.
  unfold incl in H0. unfold list_eq. intros x. split; intros H3.
  (* -> *)
  apply H0 in H3. apply H3.
  (* <- *)
  assert ({In x X} + {~ In x X}) as H4. apply in_dec. apply eq_nat_dec.
  destruct H4 as [H4| H4]. apply H4.
  (*We're now in a contradictory state *)
  assert (False).
  assert (~IndSet (x::X)) as H5. destruct H1 as [H1 H5]. apply H5. apply H4.
  apply H5. constructor. intros y H6.
  destruct H6 as [H6 | H6]. apply H2.
  subst. auto. apply H1. auto.
  intros y z H6 H7. apply H2.
  destruct H6 as [H6 | H6].
  subst. auto. auto. destruct H7 as [H7 | H7].
  subst. auto. apply H0. auto. inversion H.
Qed.


Theorem StepMaximalIndSet_in : forall n x X, In x (StepMaximalIndSet X n) -> In x X \/ x <= n.
Proof.
  intros n. induction n; intros x X H0.
  (* n = 0 *)
  simpl in H0. destruct IndSetDec in H0.
    (* IndSet *)
      simpl In in H0. intuition. left. intuition.
    (* ~ INdSet *)
      simpl in H0. destruct IndSetDec. simpl In in H0. intuition. apply IHn in H. intuition omega.  
  (* n = S n' *)
  apply IHn in H0. intuition omega.
Qed.  

Lemma MkMaximalIndSet_spec3_help : forall X Y : list nat,
  IndSet X -> MaximalIndSet Y -> incl X Y -> 
    forall x : nat, delta_min (MkMaximalIndSet X) Y = Some x ->
    forall y : nat, delta_min Y (MkMaximalIndSet X) = Some y ->
      x < y.
Proof.
  intros X Y H0 H1 H2 x H3 y H4.
  assert (exists n : nat, n = V) as H5. exists V. reflexivity.
  destruct H5 as [n H5].
  destruct n.
  (*V = 0*)
    assert (MkMaximalIndSet X = nil).
      assert (MaximalIndSet (MkMaximalIndSet X)). apply MkMaximalIndSet_spec2. apply H0.
      destruct (MkMaximalIndSet X).
        reflexivity. inversion H.
        inversion H. assert (In n (n::l)).
        left. auto. apply H6 in H10. omega.
        rewrite -> H in H3. rewrite -> delta_min_r_nil in H3. inversion H3.
  (* V = S n *)
    assert (MaximalIndSet (MkMaximalIndSet X)) as H6. apply MkMaximalIndSet_spec2.
    apply H0.
    assert (MkMaximalIndSet X = StepMaximalIndSet X n) as H7.
    apply MkMaximalIndSet_red. rewrite -> H5. reflexivity.
    assert ( y < V ) as H8.
      destruct H1 as [[H0' H1'] H2']. apply H0'. apply (delta_min_in y Y (MkMaximalIndSet X) H4).
    assert ( ~ In y (MkMaximalIndSet X)) as H9.
      apply ((delta_min_neg_in y Y (MkMaximalIndSet X) )H4).        
    assert (y <= n) as H10. omega.
    assert (exists X' : list nat, StepMaximalIndSet X n = X' ++ (StepMaximalIndSet X y) /\
                                  forall z : nat, In z X' -> z > y) as H11.
      apply StepMaximalIndSet_decomp. apply H10.
      destruct H11 as [X' [H11 H12]].
    assert (vertexConnected y (StepMaximalIndSet X y) = true) as H13. apply IndSetConstraint_gen.
      apply H0. apply H8. omega. rewrite -> H7 in H9. rewrite -> H11 in H9. intros H13. apply H9. apply in_or_app. right. apply H13.
    apply vertexConnected_spec in H13. destruct H13 as [z [H13 H14]].
    assert (In z (StepMaximalIndSet X n)) as H15. rewrite -> H11. apply in_or_app. right. apply H13.
    assert (z < y) as H16. assert (z <= y) as H0'.
      apply StepMaximalIndSet_in in H13. destruct H13 as [H13 | H13].
        (* Left *)
          assert (In z Y) as H1'. apply H2. apply H13.
          inversion H1. inversion H. apply False_rec.
          apply (H18 y z). apply (delta_min_in _ _ _ H4).
          apply H1'. apply H14. auto. 
        (* Right *)
      assert (z <> y) as H16. intros H1'. rewrite H1' in H14. apply NoSelfEdges in H14. apply H14. omega. SearchAbout delta_min.
      assert (delta_min (MkMaximalIndSet X) Y = None \/
             (exists p : nat,
               delta_min (MkMaximalIndSet X) Y = Some p /\
               In p (MkMaximalIndSet X) /\
               ~ In p Y /\
               (forall q : nat, In q (MkMaximalIndSet X) -> ~ In q Y -> p <= q))) as H17.
     apply delta_min_dec.
     destruct H17 as [H17 | H17]. rewrite -> H3 in H17. inversion H17.
     destruct H17 as [p [H0' [H1' [H2' H3']]]].
     assert (p = x) as H17. rewrite H3 in H0'. inversion H0'. reflexivity.
     assert (x <= z) as H18.
       rewrite <- H17. apply H3'. rewrite -> H7. apply H15.
       inversion H1. inversion H.
       specialize (H20 y z). intros H21. apply H20.
         apply (delta_min_in _ _ _ H4). auto. auto. omega.
Qed.    

Theorem MkMaximalIndSet_spec3 : forall X Y : list nat,
  IndSet X -> MaximalIndSet Y -> incl X Y ->
    dec_order (MkMaximalIndSet X) Y = lt_list \/ dec_order (MkMaximalIndSet X) Y = eq_list.
Proof.
  intros X Y H0 H1 H2.
  assert ( {dec_order (MkMaximalIndSet X) Y = lt_list} +
           {dec_order (MkMaximalIndSet X) Y = eq_list} +
           {dec_order (MkMaximalIndSet X) Y = gt_list}) as H5.
  apply dec_order_dec.
  destruct H5 as [[H5 | H5] | H5].
  (* Let's eliminate the trivial cases *)
    intuition. intuition. (*add in an ability to reorder/rename nodes? *)
  (* Now we're in the contradictory cases -> @H5 *)
  (* Let's set up some basic facts about the lists here *)
  assert (dec_order Y (MkMaximalIndSet X) = lt_list) as H6.
    apply dec_order_dual_spec. apply H5.
  assert (MaximalIndSet (MkMaximalIndSet X)) as H12.
    apply MkMaximalIndSet_spec2. apply H0.
  (* Let's introduce some facts about dec_order *)
  assert ( delta_min (MkMaximalIndSet X) Y = None \/ (exists x : nat,
    delta_min (MkMaximalIndSet X) Y = Some x /\
    In x (MkMaximalIndSet X) /\ ~ In x Y /\ (forall y : nat, In y (MkMaximalIndSet X) -> ~ In y Y -> x <= y))) as H7.
    apply delta_min_dec.
  assert ( delta_min Y (MkMaximalIndSet X) = None \/ (exists x : nat,
    delta_min Y (MkMaximalIndSet X) = Some x /\
    In x Y /\ ~ In x (MkMaximalIndSet X) /\ (forall y : nat, In y Y -> ~ In y (MkMaximalIndSet X) -> x <= y))) as H8.
    apply delta_min_dec.
  destruct H7 as [H7 | H7]; destruct H8 as [H8 | H8].
  (* delta_mins : None None *)
    right. unfold dec_order. destruct (MkMaximalIndSet X);
    rewrite -> H7; rewrite -> H8; reflexivity.
  (* delta_mins : None Some *)
    destruct H8 as [x [H8 [H9 [H10 H11]]]].
    assert (forall a : nat, In a (MkMaximalIndSet X) -> In a Y) as H13.
      apply delta_min_subs. apply H7.
    assert (~ IndSet(x::(MkMaximalIndSet X))) as H14.
       destruct H12 as [H12 H14].
      apply H14. apply H10.
    assert ({ValidSet (x::(MkMaximalIndSet X))} + {~ ValidSet (x::(MkMaximalIndSet X))}) as H15.
      apply ValidSet_dec. 
    assert ( {independent (x :: MkMaximalIndSet X) = true} + {independent (x :: MkMaximalIndSet X) = false} ) as H16.
      intuition.
    destruct H15 as [H15 | H15]; destruct H16 as [H16 | H16]; assert False.
      apply H14. constructor. intuition. apply independent_spec. auto. inversion H.
      apply H14. constructor. apply H15. unfold Independent. intros a b  H0' H1'.
        destruct H1 as [H1 H17].
        destruct H1 as [H1 H18]. assert (forall x y : nat, In x Y -> In y Y -> ~ In (x, y) E) as H2'.
        apply H18. specialize (H2' a b). apply H2'.
          simpl in H0'. destruct H0' as [H0' | H0']. rewrite -> H0' in H9. apply H9. apply H13. apply H0'.
          simpl in H1'. destruct H1' as [H1' | H1']. rewrite -> H1' in H9. apply H9. apply H13. apply H1'.
        inversion H.
      apply H15. unfold ValidSet. intros a H0'. simpl In in H0'. destruct H0' as [H0' | H0'].
        destruct H1 as [H1 H1']. destruct H1 as [H1 H2'].
        unfold ValidSet in H1. apply H1. rewrite -> H0' in H9. apply H9. 
        destruct H12 as [H12 H1']. destruct H12 as [H12 H2']. apply H12. apply H0'. inversion H.
      apply H15. unfold ValidSet. intros a H0'. simpl In in H0'. destruct H0' as [H0' | H0'].
         destruct H1 as [H1 H1']. destruct H1 as [H1 H2'].
        unfold ValidSet in H1. apply H1. rewrite -> H0' in H9. apply H9. 
        destruct H12 as [H12 H1'].
        unfold ValidSet in H12. destruct H12 as [H12 H2']. apply H12. apply H0'. inversion H.
  (* delta_mins : Some None *)
    destruct H7 as [x [H7 [H9 [H10 H11]]]]. left.
    unfold dec_order. destruct (MkMaximalIndSet X);
    rewrite -> H7; rewrite -> H8; reflexivity.
  (* Some Some *)
    destruct H7 as [x [H7 [H9 [H10 H11]]]].
    destruct H8 as [y [H8 [H13 [H14 H15]]]].    
    assert (y < x) as H0'.
      unfold dec_order in H6; destruct Y; rewrite -> H7 in H6; rewrite -> H8 in H6;
      destruct lt_dec; try (apply l); try inversion H6.
    assert (x < y) as H1'.
    apply (MkMaximalIndSet_spec3_help X Y).
      apply H0. apply H1. apply H2. 
      destruct H12 as [H0'' H1'']. apply H7. apply H8.
    omega.
Qed.


Theorem independent_dec : forall X : list nat, {independent X = true} + {independent X = false}.
Proof. intuition. Qed.

Theorem IndSet_dec : forall (X : list nat), {IndSet X} + {~ IndSet X}.
Proof.
  intros X.
    assert ({ValidSet X} + {~ValidSet X}) as H0. apply ValidSet_dec.
    assert ({Independent X} + {~Independent X }) as H1. apply Independent_dec.
    destruct H0 as [H0 | H0]; destruct H1 as [H1 | H1]; [left | right | right | right]; intuition.
    constructor; auto. inversion H. auto. inversion H. auto. inversion H. auto.
Qed.

Theorem Independent_spec_neg :
  forall F : list nat,
    independent F = false <-> (exists x y, In x F /\ In y F /\ In (x, y) E).
Proof.
  split; intros; induction F. inversion H.
  {
    simpl in H. destruct inEdgeDec.
    apply NoSelfEdges in i. inversion i. remember (vertexConnected a F) as b.
    destruct b. symmetry in Heqb. apply vertexConnected_spec in Heqb.
    destruct Heqb as [v' [H0 H1]]. exists a. exists v'. repeat split.
    left. reflexivity. right. assumption. assumption. apply IHF in H.
    destruct H as [v [v' [H0 [H1 H2]]]]. exists v. exists v'. repeat split;
    try right; assumption. 
  }
  destruct H as [x [y [H0 H1]]]. inversion H0.
  {
    destruct H as [x [y [H0 [H1 H2]]]].
    destruct H0 as [H0 | H0]; destruct H1 as [H1 | H1]; repeat subst.
    apply NoSelfEdges in H2. inversion H2. simpl.
    destruct inEdgeDec. reflexivity. remember (vertexConnected x F) as b.
    destruct b. reflexivity. symmetry in Heqb.
    apply vertexConnected_spec_neg in Heqb. apply False_rec.
    apply Heqb. exists y. split; assumption. simpl.
    destruct inEdgeDec. reflexivity. remember (vertexConnected y F) as b.
    destruct b. reflexivity. symmetry in Heqb.
    apply vertexConnected_spec_neg in Heqb. apply False_rec.
    apply Heqb. apply EdgesBidirectional in H2. exists x. split; assumption.
    simpl. destruct inEdgeDec. reflexivity. destruct vertexConnected.
    reflexivity. apply IHF. exists x. exists y.
    repeat split; try assumption.
  }
Qed.

Theorem eq_preserves_MIS : forall X Y: list nat, list_eq X Y -> MaximalIndSet X -> MaximalIndSet Y.
Proof.
  intros X Y H0 H1.
  unfold list_eq in H0. inversion H1. constructor. constructor.
  intros z H3. apply H1. apply H0. auto. intros a b H3 H4.  apply H1.
  apply H0. auto. apply H0. auto. intros x H3 H4.
  apply (H2 x). intros H5. apply H3. apply H0. auto.
  constructor. intros y H5. apply H4.  inversion H5.
  left. auto. right. apply H0. auto. intros y z H5 H6.
  apply H4. inversion H5. left. auto. right. apply H0.
  auto. inversion H6. left. auto. right. apply H0. auto.
Qed.

Theorem MIS_MKMIS : forall X : list nat, IndSet X -> (list_eq X (MkMaximalIndSet X) -> MaximalIndSet X).
Proof.
  intros X H0 H2.
  eapply eq_preserves_MIS.
    { apply list_eq_symmetric in H2. apply H2. }
    { apply MkMaximalIndSet_spec2. apply H0. }
Qed.

End IS.
