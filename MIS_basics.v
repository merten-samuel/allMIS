Require Import List.
Require Import Arith.
Require Import Omega.
Require Import ProofIrrelevance.
Require Import graph_basics.
Require Import lex_order.
Require Import graphs_nondep.


Ltac graphax_tac :=
  try solve [intros ? Hcontra; apply flatten_Edges_irref in Hcontra; auto
            |intros ? ? A; apply flatten_EdgesGraph_spec2 in A; destruct A; auto
            |intros ?? A; apply flatten_Edges_symm in A; auto].

Definition MkMaximalIndSet_lGraph (G : lGraph) : list nat -> list nat :=
  MkMaximalIndSet (lV G) (flatten_EdgesGraph G)
                  (fun x y =>
                     match flatten_Edges_symm G x y with
                     | conj H H2 => H
                   end).
Definition ValidSet_lGraph (G : lGraph) : list nat -> Prop :=
  ValidSet (lV G).

Definition Independent_lGraph (G : lGraph) : list nat -> Prop :=
  Independent (flatten_EdgesGraph G).

Definition independent_lGraph (G : lGraph) : list nat -> bool :=
  independent (flatten_EdgesGraph G).

Definition Ind_Set_lGraph (G : lGraph) : list nat -> Prop :=
  IndSet (lV G) (flatten_EdgesGraph G).

Definition MaximalIndSet_lGraph (G : lGraph) : list nat -> Prop := 
  MaximalIndSet (lV G) (flatten_EdgesGraph G).

Definition MaximalIndSet_cp_lGraph (G : lGraph) : list nat -> Prop := 
  MaximalIndSet_contrapos (lV G) (flatten_EdgesGraph G).

Theorem MaximalIndSet_eq_lGraph :
  forall G l, MaximalIndSet_lGraph G l <-> MaximalIndSet_cp_lGraph G l.
Proof.
  unfold MaximalIndSet_lGraph.
  unfold MaximalIndSet_cp_lGraph.
  intros. apply MaximalIndSet_eq.
Qed.

Definition VertexConnected_lGraph G x l:=
  vertexConnected (flatten_EdgesGraph G) x l.

Theorem mkMaximalIndSet_lGraph_spec :
  forall G l,
    Ind_Set_lGraph G l -> MaximalIndSet_lGraph G (MkMaximalIndSet_lGraph G l).
Proof.
  intros. apply MkMaximalIndSet_spec2.
  intros x Hcontra.   
  apply flatten_Edges_irref in Hcontra. apply Hcontra; auto.
  intros x y H2.
  apply flatten_EdgesGraph_spec2 in H2. destruct H2; auto.
  auto.
Qed.

Theorem LiftGraph_FlatEdge_spec :
  forall e1 e2 x G, In (e1, e2) (flatten_EdgesGraph (LiftGraph x G)) <->
    In (e1, e2) (flatten_EdgesGraph G) /\ e1 < x /\ e2 < x.
Proof.
  split; intros.
  {
    apply flatten_EdgesGraph_spec1 in H.
    destruct H as [H0 [H1 H2]]. split; try split; try assumption.
    apply flatten_EdgesGraph_spec1. simpl in H2.
    apply reduceLEdges_preservation in H2.
    destruct H2 as [H2 [H3 H4]]. exists H2. exists H3. assumption.
  }
  destruct H as [H0 [H1 H2]].
  apply flatten_EdgesGraph_spec1. simpl.
  exists H1. exists H2. apply flatten_EdgesGraph_spec1 in H0.
  destruct H0 as [H3 [H4 H0]].
  apply reduceLEdges_spec with
    (H00 := H3)
    (H01 := H4).
  assumption.
Qed.

Theorem lt_LiftGraph_PreservesIndSet :
  forall x l G, Ind_Set_lGraph  (LiftGraph x G) l -> Ind_Set_lGraph (LiftGraph (S x) G) l.
Proof.
  intros. induction l. apply nilIndSet.
    unfold Ind_Set_lGraph. simpl. constructor. inversion H.
    simpl in H0. intros y H2. apply H0 in H2. omega.
    destruct H as [H0 H1]. intros y z H2 H3 H4. 
    apply LiftGraph_FlatEdge_spec in H4.
    specialize (H1 y z). apply H1; auto.
    destruct H4 as [H4 _]. apply LiftGraph_FlatEdge_spec.
    split; auto.
Qed.

Theorem gt_LiftGraph_PreservesIndSet :
  forall x l G, Ind_Set_lGraph (LiftGraph (S x) G) l -> 
    ValidSet_lGraph (LiftGraph x G) l -> Ind_Set_lGraph (LiftGraph x G) l.
Proof.
  intros. induction l. apply nilIndSet. constructor. assumption.
  intros y z H3 H4 H5. apply LiftGraph_FlatEdge_spec in H5.
  inversion H. specialize (H2 y z). apply H2; auto.
  apply LiftGraph_FlatEdge_spec. split; auto.
  destruct H5 as [H5 _]. auto.
Qed.
    
Fixpoint rmvNeighbors (v : nat) (G : lGraph) (l : list nat) : list nat :=
  match l with
  | nil => nil
  | cons v' l' =>
      if inEdgeDec (flatten_EdgesGraph G) (v,v')
        then rmvNeighbors v G l'
        else v' :: (rmvNeighbors v G l')
  end.  
 
Theorem rmvNeighbors_preservation :
  forall v v' G l , In v' (rmvNeighbors v G l) -> In v' l.
Proof.
  intros. induction l. inversion H.
  simpl. simpl in H. destruct inEdgeDec.
  right.  apply IHl. exact H. destruct H as [H | H].
  subst. left. reflexivity. right. apply IHl. exact H.
Qed. 

Theorem rmvNeigbors_preserves_valid : 
  forall v G l, ValidSet_lGraph G l -> ValidSet_lGraph G (rmvNeighbors v G l).
Proof.
  intros. induction l. simpl. assumption.
  simpl. destruct inEdgeDec. apply IHl. 
  apply validSetRecr in H. assumption.
  unfold ValidSet_lGraph. unfold ValidSet.
  intros. destruct H0 as [H0 | H0]. subst.
  apply H. left. reflexivity. apply IHl.
  unfold ValidSet_lGraph. unfold ValidSet. intros.
  unfold ValidSet_lGraph in H. unfold ValidSet in H.
  apply H. right. assumption. assumption.
Qed.


Theorem rmv_neighbors_spec : 
  forall v v' G l, 
    In v' (rmvNeighbors v G l) <->
    (In v' l) /\ ~ In (v, v') (flatten_EdgesGraph G).
Proof.
  intros. split; intros; induction l.
  {
    inversion H.
  }
  {
    simpl in H. destruct inEdgeDec. apply IHl in H. simpl.
    split; try right; apply H. 
    destruct H as [H | H].
    subst. split. simpl. left. reflexivity. apply n.
    apply IHl in H. split. simpl. right. apply H. apply H.
  }
  {
    inversion H. inversion H0.
  }
  destruct H as [H0 H1].
  destruct H0 as [H0 | H0].
  {
    subst. simpl.
    destruct inEdgeDec. contradiction.
    simpl. left. reflexivity.
  }
  {
    simpl. destruct inEdgeDec; try right; apply IHl; split; assumption.
  }
Qed.

Theorem rmv_neighbors_spec_neg :
  forall v v' G l,
    In v' l -> 
    ~ In v' (rmvNeighbors v G l) ->
      In (v, v') (flatten_EdgesGraph G).
Proof.
  intros. induction l.
  inversion H. destruct H as [H | H].
  {
    subst. simpl in H0.
    destruct inEdgeDec; try assumption.
    apply False_rec. apply H0. left.
    reflexivity.
  }
  {
    simpl in H0. destruct inEdgeDec;
    apply IHl; try assumption.
    intros H1. apply H0.
    right. assumption.
  }
Qed.

Theorem rmv_neighbors_preserves_IndSet :
  forall v G l, Ind_Set_lGraph G l -> Ind_Set_lGraph G (rmvNeighbors  v G l).
Proof.
  intros. split. apply rmvNeigbors_preserves_valid.
  destruct H as [H0 H1]. simpl in H0. assumption.
  induction l. simpl. inversion H. auto.
  simpl. destruct inEdgeDec.
  apply IHl. apply IndSetCons in H. apply H.
  inversion H. intros y z H2 H3 H4.
  specialize (H1 y z). apply H1.
  inversion H2. left. auto. right.
  apply rmv_neighbors_spec in H5.
  destruct H5 as [H5 _]. auto.
  inversion H3. left. auto.
  right. apply rmv_neighbors_spec in H5.
  destruct H5 as [H5 _]. auto. auto.
Qed.

Theorem rmv_neighbors_preserves_IndSet_ext :
  forall v G l, Ind_Set_lGraph G l -> v < (lV G) -> 
    Ind_Set_lGraph G (v :: (rmvNeighbors v G l)).
Proof.
  intros. induction l; split.
  {
    simpl. intros V' H1. destruct H1 as [H1 | H1];
    [subst | inversion H1]. assumption.
  }
  {
    simpl. intros x y H1 H2 i. apply flatten_Edges_irref in i.
    inversion H1; inversion H2; auto. apply i. subst. auto.
  }
  {
    intros v' H1. destruct H1 as [H1 | H1]. subst. apply H0.
    apply H. apply rmvNeighbors_preservation in H1. apply H1.
  }
  {
    unfold Independent. intros. destruct H1 as [H1 | H1];
    destruct H2 as [H2 | H2]; repeat subst; intros H3.
    apply flatten_Edges_irref in H3. apply H3. reflexivity.
    apply rmv_neighbors_spec in H2. destruct H2 as [H2 H4].
    contradiction.
    apply rmv_neighbors_spec in H1. apply flatten_Edges_symm in H3.
    destruct H1 as [H1 H2]. contradiction.
    destruct H as [H4 H5].
    specialize (H5 x y). apply H5.
    apply rmvNeighbors_preservation in H1. auto.
    apply rmvNeighbors_preservation in H2. auto.
    assumption.
  }
Qed.

Definition LFMIS (G : lGraph) (inp : list nat) : (list nat) -> Prop :=
  fun (x : list nat) => list_eq (MkMaximalIndSet_lGraph G inp) x.

Theorem LFMIS_dec : forall G l l', {LFMIS G l l'} + {~ LFMIS G l l'}.
Proof.
  intros. apply list_eq_dec.
Defined.

Definition isMIS G l := LFMIS_dec G l l. 

Theorem remove_incl :
  forall (A : Type) (L : list A) (H0 : forall x y, {x = y} + {x <> y}) (z : A),
    incl (remove H0 z L) L.
Proof.
  intros. induction L. simpl. intros z' H1. inversion H1.
  simpl. intros z' H1. destruct (H0 z a). subst. right.
  apply IHL. apply H1. destruct H1 as [H1 | H1]. subst.
  left. reflexivity. right. apply IHL. assumption.
Qed.

Theorem remove_spec :
  forall (A : Type) (L : list A) (H0 : forall x y, {x = y} + { x <> y}) (x y : A),
    In x (remove H0 y L) <-> In x L /\ x <> y.
Proof.
  intros until L. induction L. split; intros. simpl in H. inversion H.
  destruct H as [H H1]. inversion H.
  intros. split; intros.
  {
    split. simpl in H. case_eq (H0 x y); intros; subst;
    case_eq (H0 y a); intros; subst. left. reflexivity.
    rewrite -> H2 in H. destruct H as [H | H]. symmetry in H.
    contradiction. apply IHL in H. apply False_rec. destruct H as [H H'].
    apply H'. reflexivity. rewrite -> H2 in H. apply IHL in H.
    destruct H as [H H']. right. assumption. rewrite -> H2 in H.
    destruct H as [H | H]. left. assumption. right. apply IHL in H.
    destruct H as [H H']. assumption.
    simpl in H. case_eq (H0 y a); intros; rewrite -> H1 in H. apply IHL in H.
    destruct H as [H H']. assumption.  destruct H as [H | H]. subst. intros H2.
    symmetry in H2. contradiction. apply IHL in H. destruct H as [H H']. assumption.
  }
  {
    simpl. case_eq (H0 y a); intros. subst. apply IHL. destruct H as [[H | H''] H'].
    symmetry in H. contradiction. split; assumption. destruct H as [[H | H] H'].
    subst. left. reflexivity. right. apply IHL. split; assumption.
  }
  Qed.

Theorem remove_inv : forall (l : list nat) (z : nat),
    In z l -> list_eq l (z :: (remove eq_nat_dec z l)).
Proof.
  intros l. induction l.
  {
    intros. inversion H.
  }
  {
    intros. case (eq_nat_dec z a); intros H0;
    apply incl_list_eq; split; intros x H1; case (eq_nat_dec x z); intros H2;
    repeat subst.
    left. reflexivity. right. apply remove_spec; split; assumption.
    apply H. destruct H1. symmetry in H0. contradiction.
    apply remove_incl in H0. assumption. left. reflexivity.
    right. apply remove_spec; split; assumption. assumption.
    destruct H1 as [H1 | H1]. symmetry in H1. contradiction.
    apply remove_spec in H1. destruct H1 as [H1 H3]. assumption.
  }
Qed.

Theorem list_eq_cons : forall l l' x, list_eq l l' -> list_eq (x::l) (x::l').
Proof.
  intros. apply incl_list_eq. apply incl_list_eq in H.
  destruct H as [H0 H1]. split; intros; intros y H2;
  destruct H2 as [H2 | H2]; subst; try (left; reflexivity);
  right; [apply H0 | apply H1]; assumption.
Qed.

Definition rmv x l := remove eq_nat_dec x l.

Theorem incl_Ind_Set_lGraph :
  forall G l l', Ind_Set_lGraph G l -> incl l' l -> Ind_Set_lGraph G l'.
Proof.
  intros. split. intros x H1. apply H0 in H1. destruct H as [H H2].
  apply H in H1. assumption. unfold Independent. intros. intros H3.
  destruct H as [H H4]. apply (H4 x y);
  try (apply H0; assumption). auto.
Qed.


Lemma l1_spec_mkCandidateSets : forall x l G,
  MaximalIndSet_lGraph (LiftGraph x G) l ->
  Independent_lGraph (LiftGraph (S x) G) (x::l) ->
    MaximalIndSet_lGraph (LiftGraph (S x) G) (x::l).
Proof.
  intros. unfold MaximalIndSet_lGraph. simpl.
  split. split.
  {
    simpl. unfold ValidSet. intros. destruct H1 as [H1 | H1].
    subst. omega. destruct H as [[H2 H3] H4]. apply H2 in H1.
    simpl in H1. omega.
  }
  {
    auto.
  }
  {
    intros. inversion H. destruct (eq_nat_dec x0 x).
    left. auto. right. apply H3. constructor.
    simpl. intros y H5. assert (In y (x0::x::l)).
    destruct H5 as [H5 | H5]. left. auto. right.
    right. auto. apply H1 in H4. destruct H5 as [H5 | H5].
    omega. apply H2. auto. inversion H1. 
    intros a b h1 h2 h3. specialize (H5 a b).
    apply H5. destruct h1 as [h1 | h1]; [left | right;right]; auto.
    destruct h2 as [h2 | h2]; [left | right;right]; auto.
    apply LiftGraph_FlatEdge_spec.
    apply LiftGraph_FlatEdge_spec in h3.
    destruct h3 as [h3 [h3' h3'']].
    repeat split; auto; omega.
  }
Qed.
    

Theorem l2_spec_mkCandidateSets : forall x l G,
  MaximalIndSet_lGraph (LiftGraph x G) l ->
  ~ Independent_lGraph (LiftGraph (S x) G) (x::l) ->
    MaximalIndSet_lGraph (LiftGraph (S x) G) l.
Proof.
  intros. constructor; intros.
  {
    simpl. inversion H. constructor. 
    intros y H3. apply H in H3. simpl in H3. omega.
    intros a b H3 H4 H5. inversion H1.
    specialize (H7 a b). apply H7; auto.
    apply LiftGraph_FlatEdge_spec in H5.
    destruct H5 as [H5 [H5' H5'']].
    apply LiftGraph_FlatEdge_spec.
    repeat split; auto.
  }
  {
    simpl in *. assert (x0 < x) as H2.
    destruct (eq_nat_dec x0 x). subst.
    inversion H1. contradiction.
    assert (In x0 (x0::l)). left. auto.
    apply H1 in H2. omega.
    apply H. simpl. constructor.
    intros y H3. destruct H3 as [H3 | H3].
    omega. apply H. auto. inversion H1.
    intros a b h h0 h1. apply (H4 a b h h0).
    apply LiftGraph_FlatEdge_spec.
    apply LiftGraph_FlatEdge_spec in h1.
    destruct h1 as [h1 [h1' h1'']].
    repeat split; auto.
  }
Qed.
 

Theorem IndSet_FE_step :
  forall x G l,
  IndSet x (flatten_EdgesGraph (LiftGraph x G)) l -> 
    IndSet (S x) (flatten_EdgesGraph (LiftGraph (S x) G)) l.
Proof.
  intros. constructor. inversion H.
  intros y H2. apply H0 in H2. omega.
  intros a b H0 H1 H2. inversion H. apply (H4 a b);
  subst; auto. apply LiftGraph_FlatEdge_spec.
  apply LiftGraph_FlatEdge_spec in H2.
  destruct H2 as [h1 [h1' h1'']].
  repeat split; auto.
Qed.
  

Theorem l3_spec_mkCandidateSets :
  forall l G x, MaximalIndSet_lGraph (LiftGraph (S x) G) l -> 
                ~ In x l ->
                  MaximalIndSet_lGraph (LiftGraph x G) l.
Proof. 
  intros. destruct H as [[H1 H2] H3]. repeat split.
  {
    simpl. intros y H4. specialize (H1 y).
    assert ( (y = x) \/ (y < x) ) as H5 by
      (apply H1 in H4; simpl in H4; omega).
    destruct H5 as [H5 | H5].
    subst. contradiction. assumption.
  }
  {
    unfold Independent. intros.
    specialize (H2 x0 y); try assumption.
    intros H5. apply H2. apply LiftGraph_FlatEdge_spec in H5.
    auto. auto. apply LiftGraph_FlatEdge_spec.
    apply LiftGraph_FlatEdge_spec in H5. destruct H5 as [H5 [H6 H7]].
    repeat split; auto.
  }
  {
    intros. simpl in *. apply (H3 x0); try assumption.
    simpl. apply IndSet_FE_step. auto. 
  }
Qed.

Theorem l4_spec_mkCandidateSets :
  forall G l x, Ind_Set_lGraph (LiftGraph (S x) G) l ->
                Ind_Set_lGraph (LiftGraph x G) (remove eq_nat_dec x l).
Proof.
  intros. apply gt_LiftGraph_PreservesIndSet.
  apply incl_Ind_Set_lGraph with (l := l). assumption.
  apply remove_incl. destruct H as [H0 H1].
  intros y H2. simpl. simpl in H0. specialize (H0 y).
  assert ( y < x \/ y = x) as H3. assert (In y l).
  assert (incl (remove eq_nat_dec x l) l) by apply remove_incl.
  apply H in H2. assumption. apply H0 in H. omega.
  destruct H3 as [H3 | H3]. assumption. subst.
  apply remove_In in H2. inversion H2.
Qed.


Theorem l6_spec_mkCandidateSets : forall x,
  lE (LiftGraph x nil_lGraph) = nil.
Proof.
  intros. simpl. reflexivity.
Qed.

Theorem l7_spec_mkCandidateSets : forall x,
  flatten_EdgesGraph (LiftGraph x nil_lGraph) = nil.
Proof.
  intros. unfold flatten_EdgesGraph.
  rewrite -> l6_spec_mkCandidateSets. simpl.
  reflexivity.
Qed.
  
Theorem l8_spec_mkCandidateSets : forall l x, 
  MaximalIndSet_lGraph (LiftGraph x nil_lGraph) l ->
  (forall y, y < x <-> In y l).
Proof.
  split.
  {
    intros. apply H. simpl.
    constructor.
    {
      intros a H1. destruct H1 as [H1 | H1].
      subst. auto. apply H. auto.
    }
    {
      rewrite -> l7_spec_mkCandidateSets.
      intros a b H1 H2 H3. inversion H3.
    }
  }
  {
    intros.
    apply H in H0. auto.
  }
Qed.

Theorem l9_spec_mkCandidateSets : forall l G x, 
  Ind_Set_lGraph (LiftGraph (S x) G) l ->
    Ind_Set_lGraph (LiftGraph x G) (rmv x l).
Proof.
  intros. split. intros y H0. simpl. 
  apply remove_spec with (H0 := eq_nat_dec) in H0.
  destruct H0 as [H0 H1]. destruct H as [H H'].
  apply H in H0. simpl in H0. omega.
  unfold Independent. intros. intros H2.
  destruct H as [H H'].
  apply (H' x0 y).
  apply remove_spec with (H0 := eq_nat_dec) in H0.
  destruct H0 as [H0 _]. auto.
  apply remove_spec with (H0 := eq_nat_dec) in H1.
  destruct H1 as [H1 _]. auto.
  auto.
  apply LiftGraph_FlatEdge_spec.
  apply LiftGraph_FlatEdge_spec in H2. 
  destruct H2 as [H2 [ H3 H4]]. repeat split; try omega.
  assumption.
Qed.


Theorem MkMaximalIndSet_fix :
  forall G l, MaximalIndSet_lGraph G l ->
              list_eq (MkMaximalIndSet_lGraph G l) l.
Proof.
  intros.  assert (MaximalIndSet_lGraph G (MkMaximalIndSet_lGraph G l)) as H0.
  apply MkMaximalIndSet_spec2; graphax_tac.
  destruct H as [H0 H0']. assumption.
  apply incl_list_eq. split; intros x H1.
  {
    assert ({In x l} + {~ In x l}) as H2 by apply (in_dec eq_nat_dec).
    destruct H2 as [H2 | H2]. assumption.
    destruct H as [[H H'] H'']. apply H''.
    constructor. intros a H3.
    destruct H3 as [H3 | H3]. subst. destruct H0 as [[H0 H0''] H0'].
    apply H0 in H1. assumption. apply H in H3. assumption.
    unfold Independent. intros. destruct H3 as [H3 | H3];
    destruct H4 as [H4 | H4]; repeat subst.
    {
      intros H3. apply flatten_Edges_irref in H3.
      apply H3. reflexivity.
    }
    {
      assert (In y (MkMaximalIndSet_lGraph G l)) as H3.
      assert (exists l', MkMaximalIndSet_lGraph G l = l'++l).
      apply MkMaximalIndSet_deapp; graphax_tac. split; assumption.
      destruct H3 as [l' H3]. rewrite -> H3.
      apply in_or_app. right. assumption.
      destruct H0 as [[H0 H0'] H0''].
      apply (H0' x0 y).
      assumption. assumption.
    }
    {
      assert (In x0 (MkMaximalIndSet_lGraph G l)) as H4.
      assert (exists l', MkMaximalIndSet_lGraph G l = l'++l).
      apply MkMaximalIndSet_deapp; graphax_tac. split; assumption.
      destruct H4 as [l' H4]. rewrite -> H4.
      apply in_or_app. right. assumption.
      destruct H0 as [[H0 H0'] H0''].
      apply (H0' x0 y).
      assumption. assumption.
    }
    {
      apply (H' x0 y); assumption.
    }
  }
  {
    assert (exists l', (MkMaximalIndSet_lGraph G l) = l'++l).
    apply MkMaximalIndSet_deapp; graphax_tac.
    destruct H as [H H']. assumption.
    destruct H2 as [l' H2]. rewrite -> H2. apply in_or_app. right.
    assumption.
  }
Qed.

Theorem LFMIS_cond_ref :
  forall G l, MaximalIndSet_lGraph G l -> LFMIS G l l.
Proof.
  intros. apply MkMaximalIndSet_fix. assumption.
Qed. 
 
Theorem l10_spec_mkCandidateSets_cp : forall l G x,
  MaximalIndSet_cp_lGraph (LiftGraph (S x) G) l ->
  In x l ->
  list_eq
    l
    (x::rmvNeighbors x (LiftGraph (S x) G) 
          (MkMaximalIndSet_lGraph (LiftGraph x G) (rmv x l))).
Proof.
  intros. apply incl_list_eq. split; intros.
  {
    intros y H1.
    assert (~ In (x,y) (flatten_EdgesGraph ( LiftGraph (S x) G))) as H2.
    destruct H as [[H H'] H'']. 
    apply (H' x y); assumption.
    assert ({x = y} + {x <> y} ) as H3 by apply eq_nat_dec.
    destruct H3 as [H3 | H3]. subst. left. reflexivity.
    right. apply rmv_neighbors_spec. split; try assumption.
    assert (
      exists l', MkMaximalIndSet_lGraph (LiftGraph x G) (rmv x l)
                   = l'++(rmv x l)) as H4.
    apply MkMaximalIndSet_deapp; graphax_tac.
    simpl (lV (LiftGraph x G)).
    split. assert (forall z, In z (rmv x l) -> z <> x) as H4.
    intros. apply remove_spec with (H0 := eq_nat_dec) in H4.
    destruct H4 as [H4 H4']. assumption.
    destruct H as [[H H'] H'']. intros z H5.
    apply remove_spec with (H0 := eq_nat_dec) in H5.
    destruct H5 as [H5 H5']. apply H in H5. simpl in H5.
    omega. unfold Independent. intros.
    apply remove_spec with (H0 := eq_nat_dec) in H4.
    apply remove_spec with (H0 := eq_nat_dec) in H5.
    destruct H4 as [H4 H4']. destruct H5 as [H5 H5'].
    destruct H as [[H H'] H''].
    intros H6. apply (H' x0 y0); auto. apply LiftGraph_FlatEdge_spec.
    apply LiftGraph_FlatEdge_spec in H6. destruct H6 as [H6 [H6' H6'']].
    split; try assumption; omega.
    destruct H4 as  [l' H4]. rewrite -> H4. apply in_app_iff.
    right. apply remove_spec. split. assumption.
    intros H5. symmetry in H5. contradiction.
  }
  {
    intros y H1. destruct H1 as [H1 | H1].
    subst. assumption. destruct H as [[H H'] H''].
    assert ({In y l} + {~In y l}) as H2 by apply (in_dec eq_nat_dec).
    destruct H2 as [H2 | H2]. assumption. apply False_rec.
    apply (H'' y). assumption. simpl. 
    apply rmv_neighbors_spec in H1. destruct H1 as [H1 H3].
    assert (MaximalIndSet_lGraph (LiftGraph x G)
             (MkMaximalIndSet_lGraph
               (LiftGraph x G) (rmv x l))) as H4.
    apply MkMaximalIndSet_spec2; graphax_tac. simpl.
    apply l9_spec_mkCandidateSets. split; assumption.
    split. destruct H4 as [[H4 H5] H6]. simpl in H4.
    {
      intros z H7. destruct H7 as [H7 | H7]. subst.
      apply H4 in H1. omega. apply H. assumption.
    }
    {
      unfold Independent; intros. intros H7.
      destruct H5 as [H5 | H5];
      destruct H6 as [H6 | H6]; repeat subst.
      {
        apply flatten_Edges_irref in H7. apply H7. reflexivity.
      }
      {
        assert ({y0 =x} + {y0 <> x}) as H5 by apply eq_nat_dec.
        destruct H5 as [H5 | H5]. subst. 
        apply flatten_Edges_symm in H7. contradiction.
        assert (In y0 (MkMaximalIndSet_lGraph (LiftGraph x G) (rmv x l))) as H8.
        assert (exists l',
                 (MkMaximalIndSet_lGraph (LiftGraph x G) (rmv x l)) = 
                 l'++(rmv x l) ).
        apply MkMaximalIndSet_deapp; graphax_tac.
        simpl. apply l9_spec_mkCandidateSets.
        split; assumption. destruct H8 as [l' H8]. rewrite -> H8.
        apply in_or_app. right. apply remove_spec. split; assumption.
        destruct H4 as [[H4 H4'] H4''].
        apply (H4' x0 y0); auto. apply LiftGraph_FlatEdge_spec.
        apply LiftGraph_FlatEdge_spec in H7.
        destruct H7 as [H7 [H7' H7'']]. repeat split; try assumption; try omega.
        simpl in H4. apply H4. assumption.
      }
      {
        assert ({x0 =x} + {x0 <> x}) as H6 by apply eq_nat_dec.
        destruct H6 as [H6 | H6]. subst. contradiction.
        assert (In x0 (MkMaximalIndSet_lGraph (LiftGraph x G) (rmv x l))) as H8.
        assert (exists l',
                 (MkMaximalIndSet_lGraph (LiftGraph x G) (rmv x l)) = 
                 l'++(rmv x l) ).
        apply MkMaximalIndSet_deapp; graphax_tac.
        simpl. apply l9_spec_mkCandidateSets.
        split; assumption. destruct H8 as [l' H8]. rewrite -> H8.
        apply in_or_app. right. apply remove_spec. split; assumption.
        destruct H4 as [[H4 H4'] H4''].
        apply (H4' y0 x0); auto.
        apply LiftGraph_FlatEdge_spec.
        apply LiftGraph_FlatEdge_spec in H7.
        destruct H7 as [H7 [H7' H7'']]. repeat split; try assumption; try omega.
        simpl in H4. apply flatten_Edges_symm. apply H7. apply H4. assumption.
      }
      {
        apply (H' x0 y0);
        try assumption.
      }
    }
  }
Qed.

Theorem l10_spec_mkCandidateSets : forall l G x,
  MaximalIndSet_lGraph (LiftGraph (S x) G) l ->
  In x l ->
  list_eq
    l
    (x::rmvNeighbors x (LiftGraph (S x) G) 
          (MkMaximalIndSet_lGraph (LiftGraph x G) (rmv x l))).
Proof.
  intros. apply MaximalIndSet_eq_lGraph in H.
  apply l10_spec_mkCandidateSets_cp; auto.
Qed.

Theorem rmv_pres_list_eq :
  forall x l l', list_eq l l' -> list_eq (rmv x l) (rmv x l').
Proof.
  intros. apply incl_list_eq in H. apply incl_list_eq.
  destruct H as [H H']. split; intros y H0;
  apply remove_spec; apply remove_spec with (H0 := eq_nat_dec) in H0;
  destruct H0 as [H0 H1]; split; try assumption;
  [apply H | apply H'];  assumption.
Qed.


Theorem l11_spec_mkCandidateSets :
  forall (l : list nat) l',
    incl l' l -> 
    ~ incl l l' -> exists x : nat, In x l /\ ~ In x l'.
Proof.
  intros l. induction l; intros.
  destruct l'. contradiction. apply False_rec.
  apply H0. intros. intros y H1. inversion H1.
  assert ({In a l'} + {~ In a l'}) as H1 by apply (in_dec eq_nat_dec).
  assert ({In a l} + {~ In a l}) as H2 by apply (in_dec eq_nat_dec).
  destruct H1 as [H1 | H1]; destruct H2 as [H2 | H2].
  {
    assert (incl l' l) as H3. intros y H3. apply H in H3.
    destruct H3 as [H3 | H3]. subst. assumption. assumption.
    assert (~ incl l l') as H4. intros H4. apply H0.
    intros y H5. destruct H5 as [H5 | H5]. subst.
    assumption. apply H4 in H5. assumption. 
    apply IHl in H3. destruct H3 as [y [H5 H6]].
    exists y. split. right. assumption. assumption.
    assumption.
  }
  {
    assert (incl (rmv a l') l) as H3. intros y H3.
    apply remove_spec with (H0 := eq_nat_dec) in H3.
    destruct H3 as [H3 H4]. apply H in H3.
    destruct H3 as [H3 | H3]. apply False_rec.
    apply H4. subst. reflexivity. assumption.
    apply IHl in H3. destruct H3 as [y [H3 H4]].
    exists y. split. right. assumption. intros H4'.
    apply H4. apply remove_spec. split. assumption.
    intros H5. subst. contradiction. intros H4.
    apply H0. intros y H5. destruct H5 as [H5 | H5].
    subst. assumption. apply H4 in H5.
     apply remove_spec with (H0 := eq_nat_dec) in H5.
     destruct H5. assumption.
  }
  {
    exists a. split. left. reflexivity. assumption.
  }
  {
    exists a. split. left. reflexivity. assumption.
  }
Qed.

Theorem rmv_cons : 
  forall l x, rmv x (x::l) = rmv x l.
Proof.
  intros. simpl. destruct eq_nat_dec. reflexivity.
  apply False_rec. apply n. reflexivity.
Qed.

Theorem cons_invalid :
  forall x y l G,
    Ind_Set_lGraph G (x :: l) ->
    Ind_Set_lGraph G (y :: l) ->
    ~ (Ind_Set_lGraph G (x :: y :: l)) -> 
    In (x,y) (flatten_EdgesGraph G).
Proof.
  intros. apply IndSet_destr in H1.
  apply vertexConnected_spec in H1. 
  destruct H1 as [y' [H1 H2]]. 
  destruct H1. subst. auto.
  apply False_rec. inversion H.
  apply (H4 x y'); auto.
  left. auto. right. auto.
  graphax_tac.
  graphax_tac.
  apply H0. inversion H.
  apply H2. left. auto.
Qed.

Theorem list_eq_preserves_IndSet :
  forall l l' G,
    Ind_Set_lGraph G l ->
    list_eq l l' ->
    Ind_Set_lGraph G l'.
Proof.
  intros. destruct l'. apply nilIndSet.
  split. intros y H1. apply H0 in H1.
  apply H in H1. assumption.
  unfold Independent. intros.
  destruct H as [H H'].
  apply (H' x y).
  apply H0. auto. apply H0. auto.
Qed.

Theorem TBD1' : forall V E l1 l2 x,
  list_eq l1 l2 -> IndSet V E (x::l1) -> IndSet V E (x::l2).
Proof.
  intros. split. intros a H1. apply H0. destruct H1 as [H1 | H1].
  left. assumption. right. apply H. assumption. 
  unfold Independent. intros. destruct H0 as [H0  H0'].
  apply  (H0' x0 y).
  destruct H1 as [H1 | H1]. left. subst.
  reflexivity. right. apply H. assumption.
  destruct H2 as [H2 | H2]. left. subst. reflexivity.
  right. apply H. assumption.
Qed.

Theorem TBD1'' : forall V E l1 l2 ,
  list_eq l1 l2 -> IndSet V E l1 -> IndSet V E l2.
Proof.
  intros. split. intros a H1. apply H0. apply H. assumption. 
  unfold Independent. intros. destruct H0 as [H0  H0'].
  apply (H0' x y).
  apply H. assumption.
  apply H. assumption.
Qed.

Theorem TBD2 : forall x l1 l2, list_eq l1 l2 -> list_eq (rmv x l1) (rmv x l2).
Proof.
  intros. split; intros; apply remove_spec;
  apply remove_spec with (H0 :=  eq_nat_dec) in H0;
  destruct H0 as [H0 H1]; split; try apply H; assumption.
Qed.

Theorem TBD3 : forall x G l1 l2,
  list_eq l1 l2 -> list_eq (rmvNeighbors x G l1) (rmvNeighbors x G l2).
Proof.
  intros. split; intros; apply rmv_neighbors_spec;
  apply rmv_neighbors_spec in H0; destruct H0 as [H0 H1];
  split; try apply H in H0; assumption.
Qed.

Theorem TBE : forall x l, ~ In x l -> rmv x l = l.
Proof.
  intros. induction l. simpl. reflexivity.
  unfold rmv. simpl. destruct eq_nat_dec.
  subst. apply False_rec. apply H. left.
  reflexivity. unfold rmv in IHl.
  rewrite -> IHl. reflexivity.
  intros H0. apply H. right.
  assumption.
Qed.


Inductive list_eq_in : list nat -> list (list nat) -> Prop :=
| list_eq_in_head :
    forall l1 l2 L, list_eq l1 l2 -> list_eq_in l2 (l1::L)
| list_eq_in_tail :
    forall l1 l2 L, list_eq_in l1 L -> list_eq_in l1 (l2::L).

Theorem list_eq_in_spec :
  forall l1 l2 L, list_eq l1 l2 -> In l2 L -> list_eq_in l1 L.
Proof.
  intros. induction L.
  inversion H0. destruct H0 as [H0 | H0].
  left. subst. apply list_eq_symmetric.
  auto. right. apply IHL. auto.
Qed.

Theorem list_eq_in_witness :
  forall l1 L, list_eq_in l1 L -> exists l2, list_eq l2 l1 /\ In l2 L.
Proof.
  intros. induction L.
  inversion H. inversion H. subst.
  exists a. split; [|left]; auto.
  subst. apply IHL in H2.
  destruct H2 as [l2 [H2 H2']].
  exists l2. split; [|right]; auto.
Qed.

Inductive NoDuplicates' : list (list nat) -> Prop :=
| NoDup_nil : NoDuplicates' nil
| NoDup_cons : forall l L, ~ list_eq_in l L -> NoDuplicates' L -> NoDuplicates' (l::L).