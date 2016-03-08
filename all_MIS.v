Require Import List.
Require Import Arith.
Require Import Omega.
Require Import ProofIrrelevance.
Require Import graph_basics.
Require Import lex_order.
Require Import graphs_nondep.
Require Import MIS_basics.

Fixpoint mkCandidateSets (G : lGraph) (l : list (list nat)) : list (list nat) :=
  match lV G with
  | O => nil::nil
  | S V' =>
    match l with
    | nil => nil
    | cons cand l' =>
        if independent_lGraph G (V' :: cand) then (V' :: cand) :: mkCandidateSets G l'
        else if LFMIS_dec G (V' :: rmvNeighbors V' G cand)
                            (V' :: rmvNeighbors V' G cand) (*is this dude a MIS *)
             then if LFMIS_dec (LiftGraph V' G) (rmvNeighbors V' G cand) cand
                  then (V' :: rmvNeighbors V' G cand) :: cand :: mkCandidateSets G l'
                  else cand :: mkCandidateSets G l'
             else cand :: mkCandidateSets G l'
    end
  end.

Inductive mkCS : nat -> lGraph -> list (list nat) -> list (list nat) -> Prop :=
| mkCS_nilnil :
    forall G l,
      O = lV G -> 
      mkCS O G l (nil::nil)
| mkCS_Sxnil :
    forall G x,
      S x = lV G -> 
      mkCS (S x) G nil nil
| mkCS_indep :
    forall G x cand Lin Lout,
      S x = lV G -> 
      mkCS (S x) G Lin Lout ->
      independent_lGraph G (x :: cand) = true ->
      mkCS (S x) G (cand :: Lin) ((x :: cand) :: Lout)
| mkCS_nindep1 :
    forall G x cand Lin Lout,
      S x = lV G ->       
      mkCS (S x) G Lin Lout ->
      independent_lGraph G (x :: cand) = false ->
      LFMIS G (x :: rmvNeighbors x G cand) (x :: rmvNeighbors x G cand) ->
      LFMIS (LiftGraph x G) (rmvNeighbors x G cand) cand ->
      mkCS (S x) G (cand :: Lin) ((x :: rmvNeighbors x G cand) :: cand :: Lout)
| mkCS_nindep2 :
    forall G x cand Lin Lout,
      S x = lV G -> 
      mkCS (S x) G Lin Lout ->
      independent_lGraph G (x :: cand) = false ->
      LFMIS G (x :: rmvNeighbors x G cand) (x :: rmvNeighbors x G cand) ->
      ~LFMIS (LiftGraph x G) (rmvNeighbors x G cand) cand ->
      mkCS (S x) G (cand :: Lin) (cand :: Lout)
| mkCS_nindep3 :
    forall G x cand Lin Lout,
      S x = lV G ->       
      mkCS (S x) G Lin Lout ->
      independent_lGraph G (x :: cand) = false ->
      ~LFMIS G (x :: rmvNeighbors x G cand) (x :: rmvNeighbors x G cand) ->
      mkCS (S x) G (cand :: Lin) (cand :: Lout).

Lemma mkCandidateSets_mkCS G Lin Lout :
  mkCandidateSets G Lin = Lout ->
  mkCS (lV G) G Lin Lout.
Proof.
  revert G Lout.
  induction Lin.
  { intros G Lout. simpl.
    destruct (lV G) eqn:H; intros H2. subst. constructor; auto.
    subst. econstructor; eauto.
  }
  intros G l. simpl. destruct (lV G) eqn:H2.
  { intros H3. rewrite <-H3. apply mkCS_nilnil. auto.
  }
  destruct (if if inEdgeDec (flatten_EdgesGraph G) (n, n)
               then true
               else vertexConnected (flatten_EdgesGraph G) n a
            then false
            else independent_lGraph G a) eqn:H.
  { intros H3. rewrite <-H3. constructor; auto. rewrite <-H2. apply IHLin; auto.
  }
  destruct (LFMIS_dec G (n :: rmvNeighbors n G a) (n :: rmvNeighbors n G a)) eqn:H3.
  { destruct (LFMIS_dec (LiftGraph n G) (rmvNeighbors n G a) a) eqn:H4.
    { intros H5. rewrite <-H5. constructor; auto. rewrite <-H2.
      apply IHLin; auto.
    }
    intros H5. rewrite <-H5. constructor; auto. rewrite <-H2. auto.
  }
  intros H4. rewrite <-H4. apply mkCS_nindep3; auto. rewrite <-H2. auto.
Qed.

Lemma mkCS_mkCandidateSets G Lin Lout :
  mkCS (lV G) G Lin Lout -> 
  mkCandidateSets G Lin = Lout.
Proof.
  induction 1; simpl.
  { destruct l. simpl. rewrite <-H. auto.
    simpl. rewrite <-H. auto.
  }
  rewrite <-H. auto.
  rewrite <-H. simpl in H1. rewrite H1. f_equal. auto.
  rewrite <-H. simpl in H1. rewrite H1.
  destruct (LFMIS_dec G (x :: rmvNeighbors x G cand) (x :: rmvNeighbors x G cand)).
  destruct (LFMIS_dec (LiftGraph x G) (rmvNeighbors x G cand) cand).
  f_equal; auto.
  f_equal; auto.
  contradiction.
  contradiction.
  rewrite <-H. simpl in H1. rewrite H1.
  destruct (LFMIS_dec G (x :: rmvNeighbors x G cand) (x :: rmvNeighbors x G cand)).
  destruct (LFMIS_dec (LiftGraph x G) (rmvNeighbors x G cand) cand).
  contradiction.
  f_equal; auto.
  f_equal; auto.
  rewrite <-H.
  simpl in H1. rewrite H1.
  destruct (LFMIS_dec G (x :: rmvNeighbors x G cand) (x :: rmvNeighbors x G cand)).
  contradiction.
  f_equal; auto.
Qed.

Lemma mkCandidateSetsP G Lin Lout :
  mkCS (lV G) G Lin Lout <->
  mkCandidateSets G Lin = Lout.
Proof.
  split.
  apply mkCS_mkCandidateSets.
  apply mkCandidateSets_mkCS.
Qed.  

Fixpoint mkSetsPrintMIS (V : nat) (G : lGraph) : list (list nat) :=
  match V with
  | O => (nil) :: nil
  | S V' =>
      mkCandidateSets G (mkSetsPrintMIS V' (LiftGraph V' G))
  end.

Definition PrintMIS G :=
  mkSetsPrintMIS (lV G) G.

Theorem min_mkCandidateSets : forall G l, mkCandidateSets (LiftGraph 0 G) l = (nil)::nil.
Proof.
  intros. unfold mkCandidateSets. induction l; simpl; reflexivity.
Qed.

Lemma MIS_MKMIS' :
  forall x G,
    let V := lV G in
    let E := flatten_EdgesGraph G in
    IndSet V E x ->
    list_eq x (MkMaximalIndSet V E
                               (fun x y =>
                                  match flatten_Edges_symm G x y with
                                    | conj A B => A
                                  end) x) -> 
    MaximalIndSet V E x.
Proof. intros; eapply MIS_MKMIS; eauto; graphax_tac.
Qed.


Theorem l5_spec_mkCandidateSets : forall G l x,
  In l (PrintMIS (LiftGraph x G)) ->
  Independent_lGraph (LiftGraph (S x) G) (x :: l) ->
    In (x::l) (PrintMIS (LiftGraph (S x) G)).
Proof.
  intros. unfold PrintMIS. simpl. rewrite -> LiftGraph_red.
  unfold PrintMIS in H. simpl in H.
  induction ((mkSetsPrintMIS x (LiftGraph x G))). inversion H.
  destruct H as [H | H]. subst. unfold mkCandidateSets.
  simpl (lV (LiftGraph (S x) G)). cbv beta iota. fold mkCandidateSets.
  apply independent_spec in H0. unfold independent_lGraph.
  rewrite -> H0. left. reflexivity. graphax_tac. apply IHl0 in H.
  unfold mkCandidateSets. simpl (lV (LiftGraph (S x) G)).
  cbv beta iota. fold mkCandidateSets.
  destruct (independent_lGraph (LiftGraph (S x) G) (x :: a)).
  right. assumption. try repeat destruct LFMIS_dec; repeat right;
  assumption. omega.
Qed.

Theorem l12_spec_mkCandidateSets :
  forall G l,
    Ind_Set_lGraph G l ->
    ~LFMIS G l l ->
      exists y, In y (MkMaximalIndSet_lGraph G l) /\ ~ In y l .
Proof.
  intros. assert (exists l', MkMaximalIndSet_lGraph G l = l'++l) as H1.
  apply MkMaximalIndSet_deapp; graphax_tac.
  assumption. destruct H1 as [l' H1].
  rewrite -> H1. assert (incl l (l'++l)) as H2. apply incl_appr.
  apply incl_refl. apply l11_spec_mkCandidateSets in H2.
  assumption. intros H3. apply H0. unfold LFMIS. rewrite -> H1.
  apply incl_list_eq. split; assumption.
Qed.


Theorem l13_spec_mkCandidateSets :
  forall L l x G,
    In l L ->
    LFMIS (LiftGraph (S x) G)
        (x :: rmvNeighbors x (LiftGraph (S x) G) l)
        (x :: rmvNeighbors x (LiftGraph (S x) G) l) ->
    LFMIS (LiftGraph x G)
        (rmvNeighbors x (LiftGraph (S x) G) l) l ->
    ~ Independent_lGraph (LiftGraph (S x) G) (x::l) -> 
      In (x:: rmvNeighbors x (LiftGraph (S x) G) l)
        (mkCandidateSets (LiftGraph (S x) G) L).
Proof.
  intros L. induction L; intros. inversion H.
  destruct H as [H | H]. subst. unfold mkCandidateSets.
  simpl (lV (LiftGraph (S x) G)). cbv iota beta. fold mkCandidateSets.
  remember (independent_lGraph (LiftGraph (S x) G) (x :: l)).
  destruct b. symmetry in Heqb. 
  unfold independent_lGraph in Heqb.
  apply independent_spec in Heqb; graphax_tac.
  contradiction.
  destruct LFMIS_dec; try destruct LFMIS_dec;
  try rewrite -> LiftGraph_red in n; try contradiction.
  left. reflexivity. omega. apply (IHL l x G) in H; try assumption.
  unfold mkCandidateSets.
  simpl (lV (LiftGraph (S x) G)). cbv iota beta. fold mkCandidateSets.
  unfold independent_lGraph.
  destruct (independent).
  right. assumption. repeat destruct LFMIS_dec. right. right. assumption.
  right. assumption. right. assumption.
Qed.

Lemma MkMaximalIndSet_spec2' : forall G x,
   let V := lV G in
   let E := flatten_EdgesGraph G in
   IndSet V E x ->
   MaximalIndSet V E
                 (MkMaximalIndSet V E
                                  (fun x y =>
                                     match flatten_Edges_symm G x y with
                                       | conj A B => A
                                     end) x).
Proof.
  intros.
  eapply MkMaximalIndSet_spec2; eauto; graphax_tac.
Qed.  

Theorem MkMaximalIndSet_contents :
  forall l x y G,
    In x l ->
    MaximalIndSet_lGraph (LiftGraph (S x) G) l -> 
    In y (MkMaximalIndSet_lGraph (LiftGraph x G) (rmv x l)) ->
    In y l \/ In (x, y) (flatten_EdgesGraph (LiftGraph (S x) G)).
Proof.
  intros.
  assert ({In y l} + {~In y l}) as H2 by apply (in_dec eq_nat_dec).
  destruct H2 as [H2 | H2]. left. assumption. 
  right. destruct H0 as [H0 H0'].
  apply H0' in H2. simpl in H2.
  case_eq (independent_lGraph (LiftGraph (S x) G) (y::l)).
  {
    intros H3. apply False_rec. apply H2. split.
    intros z H4. destruct H4 as [H4 | H4]. subst.
    apply l9_spec_mkCandidateSets in H0; graphax_tac.
    eapply MkMaximalIndSet_spec2' in H0.
    simpl in H0. destruct H0 as [[H0 _] _].
    apply H0 in H1. omega. apply H0. assumption.
    apply independent_spec; graphax_tac.
    assumption.
  }
  intros H3. apply cons_invalid with (l := rmv x l).
  apply list_eq_preserves_IndSet with (l := l).
  simpl in H0. assumption. apply remove_inv.
  assumption. apply l9_spec_mkCandidateSets in H0.
  assert (exists l',
            MkMaximalIndSet_lGraph (LiftGraph x G) (rmv x l)
            = l'++(rmv x l))
    as H4. apply MkMaximalIndSet_deapp; graphax_tac.
  simpl. assumption.
  apply MkMaximalIndSet_spec2' in H0.
  split.  simpl. intros a H5. destruct H5 as [H5 | H5].
  subst. destruct H0 as [[h0 _] _]. apply h0 in H1.
  simpl in H1. omega. destruct H4 as [l' H4].
  simpl in H0. unfold MkMaximalIndSet_lGraph in H4.
  simpl in H4. rewrite -> H4 in H0. destruct H0 as [[h0 _] _].
  specialize (h0 a). assert (a <x). apply h0. apply in_or_app.
  right. assumption. omega. destruct H4 as [l' H4].
  unfold Independent. intros.
  assert (forall a, In a (y :: rmv x l) -> In a (l' ++ rmv x l)).
  {
    intros. destruct H7 as [H7 | H7]. subst.
    rewrite <- H4. assumption. apply in_or_app.
    right. assumption.
  }
  apply H7 in H5. apply H7 in H6. destruct H0 as [[h4 h0] _].
  simpl in h0.
  intros h1. apply (h0 x0 y0).
  apply LiftGraph_FlatEdge_spec in h1. destruct h1 as [h1 _].
  unfold MkMaximalIndSet_lGraph in H4. simpl in H4.
  rewrite -> H4. auto. unfold MkMaximalIndSet_lGraph in H4. 
  simpl in H4. rewrite -> H4. auto. auto. simpl in h4.
  apply LiftGraph_FlatEdge_spec. split.
  apply LiftGraph_FlatEdge_spec in h1. destruct h1 as [h1 _].
  auto. unfold MkMaximalIndSet_lGraph in H4. split; apply h4.
  rewrite <- H4 in H5. auto. rewrite <-  H4 in H6. auto.
  simpl in H0. intros H4. inversion H4. 
  apply H2. assert (list_eq l (x::rmv x l)). apply remove_inv.
  auto. apply list_eq_preserves_IndSet with (l' := y::l) in H4.
  auto. split; intros. inversion H8. right. apply H7. left. auto.
  inversion H9. left. auto. right. apply H7. right.  auto.
  inversion H8. right. left. auto. apply H7 in H9.
  inversion H9. left. auto. do 2 right. auto.
Qed.

Theorem TBD'''' : forall n V E l1 l2 (Hsym : forall x y : nat, In (x, y) E -> In (y, x) E),
  list_eq l1 l2 ->
  incl (StepMaximalIndSet V E Hsym l1 n)
          (StepMaximalIndSet V E Hsym l2 n).
Proof.
  intros n. induction n.
  {
    intros. intros x H0. intros.
    unfold StepMaximalIndSet in *.
    destruct IndSetDec; destruct IndSetDec.
    apply list_eq_cons with (x:=0) in H.
    apply H. assumption.
    apply TBD1' with (l2 := l2) in i.
    contradiction. assumption.
    apply TBD1' with (l2 := l1) in i.
    contradiction.
    apply list_eq_symmetric.
    assumption. apply H. assumption.
  }
  {
    intros.
    assert (list_eq (StepMaximalIndSet V E Hsym l1 n)
                    (StepMaximalIndSet V E Hsym l2 n)) as H0.
    apply incl_list_eq. split; apply IHn.
    assumption. apply list_eq_symmetric. assumption.
    intros x H1. simpl. simpl in H1.
    destruct IndSetDec; destruct IndSetDec.
    apply list_eq_cons with (x := S n) in H0.
    apply H0. assumption.
    apply TBD1' with (l2 := (StepMaximalIndSet V E Hsym l2 n)) in i.
    contradiction. assumption.
    apply TBD1' with (l2 := (StepMaximalIndSet V E Hsym l1 n)) in i.
    contradiction. apply list_eq_symmetric in H0. assumption.
    apply H0. assumption.
  }
Qed.

Theorem TBD1''' : forall V l1 l2 E (Hsym : forall x y : nat, In (x, y) E -> In (y, x) E),
  list_eq l1 l2 ->
    incl (MkMaximalIndSet V E Hsym l1) (MkMaximalIndSet V E Hsym l2).
Proof.
  intros. unfold MkMaximalIndSet. apply TBD''''.
  assumption. 
Qed.
  
Theorem TBD1 : forall G l1 l2,
  list_eq l1 l2 ->
    list_eq (MkMaximalIndSet_lGraph G l1) (MkMaximalIndSet_lGraph G l2).
Proof.
  intros. unfold MkMaximalIndSet_lGraph.
  apply incl_list_eq; split; apply TBD1''';
  [| apply list_eq_symmetric in H]; assumption.
Qed.

Theorem MkMIS_preserves_eq :
  forall V E l1 l2 (Hsym: forall x y : nat, In (x, y) E -> In (y, x) E),
    list_eq l1 l2 ->
      list_eq (MkMaximalIndSet V E Hsym l1) (MkMaximalIndSet V E Hsym l2).
Proof.
  intros. assert (list_eq l2 l1).
  apply list_eq_symmetric. auto.
  apply incl_list_eq. split;
  apply TBD1'''; auto.
Qed.


Theorem mkCS_implies_PrintMIS :
  forall (P : list (list nat) -> Prop) G Lin Lout, 
     mkCS (lV G) G Lin Lout ->
     P Lout -> P (mkCandidateSets G Lin).
Proof.
  intros. apply mkCandidateSetsP in H. subst.
  auto.
Qed.

Theorem form1 :
  forall x G Lout Lin l,
    lV G = S x -> 
    ~ In x l ->
    In l Lout ->
    mkCS (lV G) G Lin Lout ->
      In l Lin.
Proof.
  intros. induction H2. 
  {
    omega.
  }
  {
    auto.
  }
  {
    destruct H1. apply False_rec.
    apply H0. rewrite <- H1. left.
    omega. right. apply IHmkCS; auto.    
  }
  {
    destruct H1 as [H1 | [H1 | H1]].
    {
      apply False_rec. apply H0. rewrite <- H1.
      left. omega.
    }
    {
      left. auto.
    }
    {
      right. apply IHmkCS; auto.
    }
  }
  {
    destruct H1 as [H1 | H1].
    {
      left. auto.
    }
    {
      right. apply IHmkCS; auto.
    }
  }
  {
    destruct H1 as [H1 | H1].
    {
      left. auto.
    }
    {
      right. auto.
    }
  }
Qed.

Theorem form2 :
  forall x G Lout Lin l,
    lV G = S x -> 
    In x l ->
    In l Lout ->
    (forall l', In l' Lin -> MaximalIndSet_lGraph (LiftGraph x G) l') ->
    MaximalIndSet_lGraph (LiftGraph x G) (rmv x l) -> 
    mkCS (lV G) G Lin Lout ->
    (forall l', In l' Lout -> MaximalIndSet_lGraph G l') ->
      In (rmv x l) Lin.
Proof.
  intros. induction H4.
  {
    omega.
  }
  {
    inversion H1.
  }
  {
    destruct H1 as [H1 | H1].
    {
      subst. 
      {
        left. simpl. destruct eq_nat_dec.
        symmetry. apply TBE. intros H8.
        apply H2 in H8. simpl in H8. omega.
        left. auto. omega.
      }
    }
    right. apply IHmkCS; auto.
    intros. apply H2. right. auto.
    intros. apply H5. right. auto.
  }
  {
    destruct H1 as [H1 | [H1 | H1]].
    {
      subst. simpl in H3.
      destruct eq_nat_dec in H3.
      {
        assert (list_eq cand (rmv x (rmvNeighbors x0 G cand))).
        rewrite -> TBE. split; intros.
        destruct (in_dec eq_nat_dec x1 (rmvNeighbors x0 G cand)).
        auto.
        apply eq_preserves_MIS with (Y:= (rmvNeighbors x0 G cand)) in H3.
        apply H3 in n. apply False_rec. apply n.
        constructor.
        simpl. intros y h. destruct h as [h | h].
        apply H2 in H1. simpl in H1. omega.
        left. auto. apply rmv_neighbors_spec in h.
        destruct h as [h _].
        apply H2 in h. simpl in h. auto.
        left. auto. intros a b h1 h2.
        apply (H2 cand). left. auto.
        destruct h1 as [h1 | h1].
        subst. auto. apply rmv_neighbors_spec in h1.
        destruct h1 as [h1 _]. auto.
        destruct h2 as [h2 |h2]. subst. auto.
        apply rmv_neighbors_spec in h2.
        destruct h2 as [h2 _].
        auto. rewrite -> TBE.
        apply list_eq_ref. intros h.
        apply rmv_neighbors_spec in h.
        destruct h as [h _].
        apply H2 in h. simpl in h.
        omega. left. auto. apply rmv_neighbors_spec in H1.
        destruct H1 as [H1 _]. auto.
        intros h. apply rmv_neighbors_spec in h.
        destruct h as [h _]. apply H2 in h.
        simpl in h. omega. left. auto.
        apply False_rec. apply list_eq_cons with (x := x) in H1.
        apply eq_preserves_MIS with
          (X := (x0 :: rmvNeighbors x0 G cand)) (Y := x::cand) in H5.
        inversion H5. inversion H10. 
        apply independent_spec in H13; graphax_tac.
        unfold independent_lGraph in H7. 
        subst. rewrite -> H7 in H13. inversion H13.
        subst. apply list_eq_symmetric.
        apply list_eq_trans
          with (Y := (x0 :: rmv x0 (rmvNeighbors x0 G cand))).
        auto. apply list_eq_cons.
        rewrite -> TBE. apply list_eq_ref.
        assert (In cand (cand::Lin)).
        left. auto. apply H2 in H10.
        intros H11. apply rmv_neighbors_spec in H11.
        destruct H11 as [H11 _]. apply H10 in H11.
        simpl in H11. omega.
        left. auto.
      }
      {
        omega.
      }
    }
    {
      apply False_rec. subst.
      apply H2 in H0. simpl in H0.
      omega. left. auto.
    }
    {
      right. apply IHmkCS; auto.
      intros. apply H2. right. auto.
      intros. apply H5. right. right. auto.
    }
  }
  {
    destruct H1 as [H1 | H1].
    subst. apply H2 in H0.
    simpl in H0. omega.
    left. auto. right.
    apply IHmkCS; auto.
    intros. apply H2. right. auto.
    intros. apply H5. right. auto.
  }
  {
    destruct H1 as [H1 | H1].
    subst. apply H2 in H0.
    simpl in H0. omega.
    left. auto. right.
    apply IHmkCS; auto.
    intros. apply H2. right. auto.
    intros. apply H5. right. auto.
  }
Qed.


Theorem form3 :
  forall x G Lout Lin l,
    lV G = S x -> 
    In x l ->
    In l Lout ->
    (forall l', In l' Lin -> MaximalIndSet_lGraph (LiftGraph x G) l') ->
    ~ MaximalIndSet_lGraph (LiftGraph x G) (rmv x l) -> 
    mkCS (lV G) G Lin Lout ->
      exists l', LFMIS (LiftGraph x G) (rmv x l) l' /\ In l' Lin.
Proof.
  intros. induction H4.
  {
    omega.
  }
  {
    inversion H1.
  }
  {
    destruct H1 as [H1 | H1].
    subst. 
    apply False_rec. apply H3.
    unfold MaximalIndSet_lGraph. simpl lV.
    apply eq_preserves_MIS with (X := cand).
    simpl. destruct eq_nat_dec.
    rewrite -> TBE. apply list_eq_ref.
    intros H7. apply H2 in H7.
    simpl in H7. omega. left. auto.
    omega. apply H2. left. auto.
    apply IHmkCS in H1.
    destruct H1 as [l' [H1 H1']].
    exists l'. split; auto. right. auto.
    auto. intros. apply H2. right. auto.
    auto.    
  }
  {
    destruct H1 as [H1 | [H1 | H1]].
    {
      subst. exists cand.
      split. unfold LFMIS in H8 |-*.
      apply list_eq_trans
        with (Y := (MkMaximalIndSet_lGraph
                     (LiftGraph x0 G)
                     (rmvNeighbors x0 G cand))).
      simpl. destruct eq_nat_dec.
      rewrite -> TBE. subst.
      apply list_eq_ref.
      intros H9.
      apply rmvNeighbors_preservation in H9.
      apply H2 in H9. simpl in H9.
      omega. left. auto.
      omega. auto. left. auto.
    }
    {
      subst. apply H2 in H0.  simpl in H0.
      omega. left. auto.
    }
    {
      apply IHmkCS in H.
      destruct H as [l' [H H']].
      exists l'. split. auto.
      right. auto. auto.
      intros. apply H2. right.
      auto. auto.
    }
  }
  {
    destruct H1 as [H1 | H1].
    apply H2 in H0. simpl in H0.
    omega. left. auto.
    apply IHmkCS in H.
    destruct H as [l' [H H']].
    exists l'. split. auto.
    right. auto. auto. intros.
    apply H2. right. auto. auto.
  }
  {
    destruct H1 as [H1 | H1].
    apply H2 in H0. simpl in H0.
    omega. left. auto.
    apply IHmkCS in H.
    destruct H as [l' [H H']].
    exists l'. split. auto.
    right. auto. auto. intros.
    apply H2. right. auto. auto.
  }
Qed. 
