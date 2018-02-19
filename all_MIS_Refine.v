Require Import graph_basics.
Require Import MIS_basics.
Require Import all_MIS.
Require Import wf_combinators.
Require Import Wellfounded.
Require Import Relations.
Require Import List. 
Require Import Omega.
Require Import index.
(* Require Import Fin. *)
Definition iN (N : nat) :=  Ix N.
Require Import Coq.extraction.ExtrHaskellString.
Extraction Language Haskell.
Extract Inductive sumbool => "Prelude.Bool" ["Prelude.True" "Prelude.False"].

Section RefineMIS.
  (** Let's set up the environment we need to apply queueMIS **)

  Variable G : lGraph.
  Notation "|V|" := (lV G).

  (* The list we iterate over is composed of ordered pairs of (N,S)
      where S is a maximal independent set of a graph of size N *)
  (* Left part of pair is Index type to allow for the relation over 
     A to be total *)
  Notation A := (iN (S |V|) *(list nat))%type.

  (* The output should store MISs of the input graph (as a list of list of nats) *)
  Notation B := (list (list nat)).
  
  (* At each step of the function the head of the list is removed
      and replaced with a new list of MISs s.t. N is larger by one,
      but no larger than the vertices of G. *)

  (* Coercion nat_of_fin' (N:nat) (x:iN N) : nat := proj1_sig (Fin.to_nat x). *)
  Definition iXToNat (x : iN (S |V|)) : nat.
  Proof.
    destruct x.
    exact i.
  Defined.
  
  Inductive R_Ix : iN (S |V|) -> iN (S |V|) -> Prop :=
  | mkR_Ix : forall a1 a2, iXToNat a2 < iXToNat a1 -> R_Ix a1 a2.

  Definition R : A -> A -> Prop :=
    LeftProdRel (iN (S |V|)) (list nat) R_Ix.


  (* ltof (iN (|V|)) iXToNat n m). *)

  Ltac solve_by_inverts n :=
    match goal with
    | H : _ /\ _ |- _ => destruct H
    | |- _ /\ _ => split
    | H : ?T |- _ => 
      match type of T with Prop =>
                           solve [ 
                               inversion H; try reflexivity; eauto;
                               match n with S (S (?n')) => subst; solve_by_inverts (n') end ]
      end end;
    intros; eauto; solve_by_inverts (n-1).

  Ltac si :=
    try solve_by_inverts 3; eauto.


  Set Implicit Arguments.

  Definition Eqa (a1 a2 : (iN (S|V|) * list nat)) : Prop := fst a1 = fst a2.

  Lemma R_wf : well_founded R.
  Proof.
    unfold R.
    constructor. destruct a, i.
    generalize dependent l.
    induction i using (well_founded_induction (Nat.gt_wf (S |V|))).
    intros. destruct y. constructor. intros. destruct y. destruct i0.
    eapply H. Focus 2. apply H1. constructor. Focus 2. omega.
    inversion H0; subst. inversion H2; subst. simpl in H3, H1.
    omega.
  Qed.

  Lemma R_trans : forall a1 a2 a3, R a1 a2 -> R a2 a3 -> R a1 a3.
  Proof.
    unfold R.
    unfold ltof.
    intros.
    inversion H.
    subst.
    inversion H0.
    subst.
    constructor.
    destruct a1, a2, a3.
    inversion H1. inversion H2; subst; simpl in *.
    constructor. omega.
  Qed.

  Lemma Eqa_eq : equivalence _ Eqa.
  Proof.
    constructor; 
      [constructor; reflexivity |  | ];
      intros; try omega.
    {
      unfold transitive.
      intros.
      inversion H.
      -
        inversion H0.
        *
          unfold Eqa.
          rewrite H2,H3.
          auto.
    }
    unfold symmetric.
    intros.
    inversion H.
    unfold Eqa.
    rewrite H1.
    reflexivity.
  Qed.

  Lemma R_irref : (forall a1 a2 : A, R a1 a2 -> ~ Eqa a1 a2).
  Proof.
    unfold R,Eqa.
    unfold ltof.
    intros.
    destruct a1,a2.
    simpl in *.
    inversion H.
    subst.
    simpl in H0.
    destruct i, i0.
    intros Hnot.
    rewrite Hnot in H0.
    inversion H0; subst. omega.
  Qed.

  Require Import ProofIrrelevance.

  Lemma R_total : (forall a1 a2 : A, {R a1 a2} + {Eqa a1 a2} + {R a2 a1}).
  Proof.
    intros.
    unfold R.
    unfold ltof.
    unfold Eqa.
    destruct a1,a2.
    destruct i,i0.
    destruct (lt_eq_lt_dec i i0).
    destruct s.
    +
      right.
      constructor.
      simpl.
      constructor; auto.
    +
      left.
      right.
      simpl.
      subst.
      f_equal.
      apply proof_irrelevance.
    +
      do 2 left.
      constructor.
      constructor.
      simpl.
      omega.
  Defined.

  Definition Accum (a : A) (acc : B) : B :=
    if Nat.eqb (iXToNat (fst a)) |V| then (snd a)::acc else acc.
  

  (** This should be performing this step of the
      MIS algorithm: 
~~~~~~~~~~~~~~~~
        if independent_lGraph G (V' :: cand) then (V' :: cand) :: mkCandidateSets G l'
        else if isMIS G (V' :: rmvNeighbors V' G cand)
             then if LFMIS_dec (LiftGraph V' G) (rmvNeighbors V' G cand) cand
                  then (V' :: rmvNeighbors V' G cand) :: cand :: mkCandidateSets G l'
                  else cand :: mkCandidateSets G l'
             else cand :: mkCandidateSets G l'
~~~~~~~~~~~~~~~~
   **)


  (* Explaining notation in this function:
        cand - a MIS of the subgraph (G_graphSize)
               ^--- This means that \forall x \in cand, x < graphSize

        G_s - The next subgraph we need to build an MIS for.
               ^--- This means that newest vertex in G_s is graphSize.
   *)

  (* function over nats that will be refined to use index type
   was having trouble with dependent case analysis when using 
   Index type. *)

Definition packNat (n : nat) (pf : n < S|V|) : iN (S|V|) := @Index.mk _ n pf.

Definition stepCandSet (a : A) : list A.
  refine (
    let (graphSize, cand) := a in
    match graphSize with @Index.mk _ natSize ntPf =>
    let G_graphSize := LiftGraph natSize G in    
    let G_s := (LiftGraph (S natSize) G) in
    match (Nat.eq_dec natSize |V|)  with
    | left _ => nil (* if natSize == |V|) *) (* Is this an MIS of the whole graph G? Then drop it*)
    | right _ =>
      if independent_lGraph G_s (natSize::cand)
        then (@packNat (S natSize) _, (cons natSize cand))::nil
      else if isMIS G_s (natSize :: (rmvNeighbors natSize G_s cand))
        then if LFMIS_dec G_graphSize (rmvNeighbors natSize G_s cand) cand
          then  (@packNat (S natSize) _, (natSize :: (rmvNeighbors natSize G_s cand)))::
                (@packNat (S natSize) _, cand)::
                nil
          else (@packNat (S natSize) _, cand)::nil
           else (@packNat (S natSize) _, cand)::nil
    end
    end).
Proof.
  omega. omega. omega. omega. omega.
Defined.


Definition stepCandSet' (a : A) : list A.
  refine (
    let (graphSize, cand) := a in
    match graphSize with @Index.mk _ natSize ntPf =>
    let G_graphSize := LiftGraph natSize G in    
    let G_s := (LiftGraph (S natSize) G) in
    (match (Nat.eqb natSize |V|)  as b return (Nat.eqb natSize |V| = b -> list A) with
      (* if (Nat.eqb graphSizeN |V|) *) (* Is this an MIS of the whole graph G? Then drop it*)
      |true => fun _ => nil 
                 (* then nil *)
      |false => 
      if independent_lGraph G_s (natSize::cand)
        then fun eq_pf => (@packNat (S natSize) _, (cons natSize cand))::nil
      else if isMIS G_s (natSize :: (rmvNeighbors natSize G_s cand))
        then if LFMIS_dec G_graphSize (rmvNeighbors natSize G_s cand) cand
          then fun eq_pf =>  (@packNat (S natSize) _, (natSize :: (rmvNeighbors natSize G_s cand)))::
                (@packNat (S natSize) _, cand)::
                nil
          else fun eq_pf => (@packNat (S natSize) _, cand)::nil
           else fun eq_pf => (@packNat (S natSize) _, cand)::nil
    end) (eq_refl (Nat.eqb natSize |V|))
    end).
Proof.
  apply beq_nat_false in eq_pf. omega.
  apply beq_nat_false in eq_pf. omega.
  apply beq_nat_false in eq_pf. omega.
  apply beq_nat_false in eq_pf. omega.
  apply beq_nat_false in eq_pf. omega.
Defined.


Lemma stepCandSet_desc : forall a a' : A, In a' (stepCandSet a) -> R a' a.
Proof.
  intros.
  destruct a, a'. destruct i.
  constructor; simpl. constructor. destruct i0.
  simpl.
  unfold stepCandSet in H.
  destruct (Nat.eq_dec i |V|). inversion H.
  destruct independent_lGraph. inversion H.
  inversion H0. clear H H0. omega.
  inversion H0. destruct isMIS.
  destruct LFMIS_dec. inversion H.
  inversion H0. omega. inversion H0.
  inversion H1. omega. inversion H1.
  inversion H. inversion H0. omega.
  inversion H0. inversion H.
  inversion H0. omega. inversion H0.
Qed.

  Definition queueMIS :=
    IterQueueWithAccum A B R Eqa R_wf R_trans Eqa_eq R_total R_irref
                       Accum stepCandSet stepCandSet_desc. 

  Definition Ox : iN (S|V|).
    unfold iN. unfold Ix. eapply (@Index.mk _ 0 _).
    Unshelve. omega.
  Defined.

  Definition queueStep := QueueStepR _ _ Accum stepCandSet.

  (* This form is nice for working with composition,
      but the form of the transitivity means that
      you can build a chain of arbitrary length
      deriving this relation. 
  *)
  Inductive queueStep_n :
    nat -> list A * B -> list A * B -> Prop :=
  | QMS_refl : forall l, queueStep_n 0 l l
  | QMS_step : forall l1 l2, queueStep l1 l2 -> queueStep_n 1 l1 l2
  | QMS_trans : forall n m l1 l2 l3,
                  queueStep_n n l1 l2 ->
                  queueStep_n m l2 l3 -> queueStep_n (n + m) l1 l3.

  (*
      To work around this, we prove the following two lemmas
      regarding the base cases that can appear in induction
      on queueStep_n. These 'shortcut' any of the problematic
      chains mentioned above
  *)
  Lemma queueStep_n_0 :
    forall l1 l2 n, queueStep_n n l1 l2 -> n = 0 -> l1 = l2.
  Proof.
    intros l1 l2 n H. induction H.
    + intros. auto.
    + intros. inversion H0.
    + intros. apply plus_is_O in H1.
      inversion H1. 
      rewrite IHqueueStep_n1; auto.
  Qed.

  Lemma queueStep_n_1 :
    forall l1 l2 n, queueStep_n n l1 l2 -> n = 1 -> queueStep l1 l2.
  Proof.
    intros l1 l2 n H. induction H.
    + intros. inversion H.
    + intros. auto.
    + intros. apply Nat.eq_add_1 in H1. 
      do 2 destruct H1; subst.
      apply queueStep_n_0 in H0; auto.
      simpl; subst. apply IHqueueStep_n1. auto.
      apply queueStep_n_0 in H; auto.
      simpl; subst. apply IHqueueStep_n2. auto.
  Qed.

  (* This guy helps clean up some obnoxious cases *)
  Lemma queueStep_n_inv :
    forall p1 p2 n m, queueStep_n (n + m) p1 p2 ->
      exists p_int, queueStep_n n p1 p_int /\ queueStep_n m p_int p2.
  Proof.
    intros p1 p2. induction n; induction m.
  Admitted.
  
  Lemma queueStep_n_length_app :
    forall a1 a1' b1 b1',
      queueStep_n (length a1) (a1, b1) (a1', b1') ->
      forall a2 b2 p,
        queueStep_n (length a1) (a1 ++ a2, b2) p ->
        fst p = a2 ++ a1'.
  Proof.

  Admitted.

  Lemma queueStep_n_exists :
    forall a, exists a', queueStep_n (length (fst a)) a a'.
  Proof.

  Admitted.


  Lemma stepEq :
    forall p1 p2, queueStep p1 p2 -> queueMIS p1 = queueMIS p2.
  Proof.

  Admitted.

  Lemma stepNEq :
    forall n p1 p2, queueStep_n n p1 p2 -> queueMIS p1 = queueMIS p2.
  Proof.

  Admitted.

  Definition AasB : list A -> B :=
    fun l => map snd l.

  Inductive matchQandCand : nat -> list A -> B -> Prop :=
  | matchQCand_intro :
      forall lA lB v,
        AasB lA = lB ->
        (forall a, In a lA -> iXToNat (fst a) = v) ->
        matchQandCand v lA lB.

  Lemma list_sep : forall (T : Type) (l : list T) n m,
    length l = n + m ->
    exists l1 l2, length l1 = n /\ length l2 = m /\ l1++l2 = l.
  Proof.

  Admitted.

  Lemma mkCandidateSets_app :
    forall l1 l2 G,
      lV G <> 0 -> mkCandidateSets G (l1 ++ l2) =
                   (mkCandidateSets G l1) ++ (mkCandidateSets G l2).
  Proof.
    induction l1.
    + intros. rewrite app_nil_l. simpl. destruct (lV G0). omega. auto. 
    + intros. simpl.
      assert (
        forall (l2 : B),
          mkCandidateSets G0 (l1 ++ l2) =
          mkCandidateSets G0 l1 ++ mkCandidateSets G0 l2).
      { intros. apply IHl1. auto. }
      destruct (lV G0). omega.
      destruct graphs_nondep.inEdgeDec.
      destruct isMIS.
      destruct LFMIS_dec. rewrite H0. auto.
      rewrite H0. auto.
      rewrite H0. auto.
      destruct graphs_nondep.vertexConnected.
      destruct isMIS.
      destruct LFMIS_dec. rewrite H0. auto.
      rewrite H0. auto.
      rewrite H0. auto.
      destruct independent_lGraph.
      rewrite H0. auto.
      destruct isMIS. destruct LFMIS_dec.
      rewrite H0. auto.
      rewrite H0. auto.
      rewrite H0. auto.
Qed. 

  Lemma stepQ_as_mkCandSets :
    forall n (p1 p2 : list A * B),
      queueStep_n n p1 p2 -> 
    forall v (p1 p2 : list A * B) (lG : B),
      length lG = n ->
      queueStep_n n p1 p2 ->
      matchQandCand v (fst p1) lG ->
      v < |V| ->  v <> 0 ->
      AasB (fst p2) = mkCandidateSets (LiftGraph (S v) G) lG.
  Proof.
    intros n p1 p2 H.
    induction H. intros.
    + apply length_zero_iff_nil in H. subst.
      apply queueStep_n_0 in H0. subst.
      inversion H1; subst. rewrite H. auto.
      auto.
    + intros. apply queueStep_n_1 in H1; auto.
      inversion H2; subst.
      inversion H1. subst. simpl fst.
      assert (l = nil).
      {
        simpl in H0. inversion H0.
        apply length_zero_iff_nil.
        unfold AasB in H7.
        rewrite map_length in H7. auto.
      }
      subst. rewrite app_nil_l in *.
      destruct a. destruct i. simpl fst in *.
      assert (In (Index.mk pf, l) ((Index.mk pf, l) :: nil)). left; auto.
      apply H6 in H5. simpl in H5. subst. simpl.
      destruct (Nat.eq_dec). omega.
      destruct graphs_nondep.inEdgeDec.
      destruct isMIS. rewrite LiftGraph_red.
      destruct LFMIS_dec. simpl. auto.
      simpl. auto. omega. simpl. auto.
      destruct graphs_nondep.vertexConnected.
      destruct isMIS. rewrite LiftGraph_red.
      destruct LFMIS_dec. simpl. auto.
      simpl. auto. omega. simpl. auto.
      destruct independent_lGraph. simpl. auto.
      destruct isMIS. rewrite LiftGraph_red.
      destruct LFMIS_dec. simpl. auto.
      simpl. auto. omega. simpl. auto.
    + intros. inversion H3; subst.
      assert (exists l1 l2,
                length l1 = n /\ length l2 = m /\ l1++l2 = (fst p1)).
      { unfold AasB in H1. rewrite map_length in H1.
        apply list_sep in H1. auto. }
      destruct H6 as [nl [ml [H6 [H8 ] ] ] ].
      rewrite <- H9.
      replace (mkCandidateSets (LiftGraph (S v) G) (AasB (nl ++ ml))) with
        ( mkCandidateSets (LiftGraph (S v) G) (AasB nl) ++
          mkCandidateSets (LiftGraph (S v) G) (AasB ml)).
      apply queueStep_n_inv in H2.
      inversion H2. destruct H10.
      destruct p1; simpl in *.
      destruct (queueStep_n_exists (nl, l0)); simpl in H12.
      destruct x0.
      specialize (queueStep_n_length_app H12). intros.
      rewrite <- H9, <- H6 in H10. apply H13 in H10.
      destruct (queueStep_n_exists (ml, l0)); simpl in H14.
      destruct x0. specialize (queueStep_n_length_app H14). intros.
      destruct x. simpl in *.
      rewrite H10, <- H8 in H11.
      apply H15 in H11. rewrite H11.
      replace (AasB (l4 ++ l6)) with (AasB l4 ++ AasB l6).
      f_equal.
      - replace l4 with (fst (l4, l5)).
        eapply IHqueueStep_n1; try auto.
        * unfold AasB. rewrite map_length. auto.
        * rewrite <- H6. apply H12.
        * constructor. auto. intros.
          rewrite <- H9 in H7. apply H7.
          apply in_or_app. left. auto.
        * auto.
      - replace l6 with (fst (l6, l7)).
        eapply IHqueueStep_n2.
        * unfold AasB. rewrite map_length. auto.
        * rewrite <- H8. apply H14.
        * constructor. auto. intros.
          rewrite <- H9 in H7. apply H7.
          apply in_or_app. right. auto.
        * omega.
        * omega.
        * auto.
      - unfold AasB. rewrite map_app. auto.
      - unfold AasB. rewrite map_app.
        rewrite mkCandidateSets_app. auto.
        simpl. auto.
Qed.

  Lemma queueMIS_EQ_PrintMIS : snd (queueMIS ((Ox, nil)::nil, nil)) = PrintMIS G.
  Proof.
    (* it's gonna be a wild ride in here *)
  Admitted.

End RefineMIS.
Recursive Extraction queueMIS.

(*
PMap_Extraction queueMIS.
  PMap_Extraction

  Lemma queueMIS_EQ_PrintMIS : snd (queueMIS ((0, nil)::nil, nil)) = PrintMIS G.
  Proof.
    (* it's gonna be a wild ride in here *)
  Admitted.

 Definition stackMIS :=
    IterStackWithAccum A B R R_wf Accum stepCandSet stepCandSet_desc.
 *)


