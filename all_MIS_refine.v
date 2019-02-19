Require Import graph_basics.
Require Import MIS_basics.
Require Import all_MIS.
Require Import wf_combinators.
Require Import Wellfounded.
Require Import Relations.
Require Import List. 
Require Import Omega.
Require Import index.
Require Import Program.Equality.
Require Import Permutation.
Require Import all_MIS_sound.
Require Import all_MIS_complete.
Require Import all_MIS_unique.
Require Import SetoidList.



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
  Notation A := (Ix (S |V|) *(list nat))%type.

  (* The output should store MISs of the input graph (as a list of list of nats) *)
  Notation B := (list (list nat)).
  
  (* At each step of the function the head of the list is removed
      and replaced with a new list of MISs s.t. N is larger by one,
      but no larger than the vertices of G. *)

  (* Coercion nat_of_fin' (N:nat) (x:Ix N) : nat := proj1_sig (Fin.to_nat x). *)
  Definition iXToNat (x : Ix (S |V|)) : nat.
  Proof.
    destruct x.
    exact i.
  Defined.
  
  Inductive R_Ix : Ix (S |V|) -> Ix (S |V|) -> Prop :=
  | mkR_Ix : forall a1 a2, iXToNat a2 < iXToNat a1 -> R_Ix a1 a2.

  Definition R : A -> A -> Prop :=
    LeftProdRel (Ix (S |V|)) (list nat) R_Ix.


  (* ltof (Ix (|V|)) iXToNat n m). *)

  Ltac destr :=
    match goal with
    | H : context[exists _, _]  |- _ => destruct H
    |H : context[_ /\ _]  |- _=> destruct H
    | |- _ /\ _ => split
    end.

  Ltac solve_by_inverts n :=
    match goal with
    | H : ?T |- _ => 
      match type of T with
        Prop =>
        solve [ 
            inversion H; try reflexivity; eauto;
        match n with S (S (?n')) => subst; solve_by_inverts (n') end ]
      end end;
    intros; eauto; solve_by_inverts (n-1).

  Ltac si :=
    try repeat destr;
    try solve_by_inverts 3; eauto.

  Set Implicit Arguments.

  Definition Eqa (a1 a2 : (Ix (S|V|) * list nat)) : Prop := fst a1 = fst a2.

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

Definition packNat (n : nat) (pf : n < S|V|) : Ix (S|V|) := @Index.mk _ n pf.

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

  Definition stackMIS :=
    IterStackWithAccum A B R R_wf Accum stepCandSet stepCandSet_desc.


  Definition Ox : Ix (S|V|).
    unfold Ix. unfold Ix. eapply (@Index.mk _ 0 _).
    Unshelve. omega.
  Defined.

  (* Just a step relation for execution of the program *)
  Definition queueStep := QueueStepR _ _ Accum stepCandSet.

  (* An indexed version of the same *)
  Inductive queueStep_n :
    nat -> list A * B -> list A * B -> Prop :=
  | QMS_refl : forall l, queueStep_n 0 l l
  | QMS_step : forall l1 l2, queueStep l1 l2 -> queueStep_n 1 l1 l2
  | QMS_trans : forall n m l1 l2 l3,
                  queueStep_n n l1 l2 ->
                  queueStep_n m l2 l3 -> queueStep_n (n + m) l1 l3.

  (* A big step version... *)
  Definition queueBigStep : list A * B -> list A * B -> Prop := clos_refl_trans _ queueStep.

  (* Two alternate versions of the indexed step relation.
     These require one of the transitive componenents to take a single step *)
  Inductive queueStep_n_simpl :
    nat -> list A * B -> list A * B -> Prop :=
  | QMSs_refl : forall l, queueStep_n_simpl 0 l l
  | QMSs_trans : forall n l1 l2 l3,
                  queueStep_n_simpl n l1 l2 ->
                  queueStep l2 l3 -> queueStep_n_simpl (S n) l1 l3.

  Inductive queueStep_n_simpl' :
    nat -> list A * B -> list A * B -> Prop :=
  | QMSs_refl' : forall l, queueStep_n_simpl' 0 l l
  | QMSs_trans' : forall n l1 l2 l3,
                  queueStep l1 l2 ->
                  queueStep_n_simpl' n l2 l3 -> queueStep_n_simpl' (S n) l1 l3.

(** queueStep rewrite rules *)
  Lemma queueStep_n_0 :
    forall l1 l2 n, queueStep_n n l1 l2 -> n = 0 -> l1 = l2.
  Proof.
    intros.
    induction H; si.
    apply plus_is_O in H0; si.
    firstorder. subst. auto.
  Qed.

  Lemma queueStep_n_1 :
    forall l1 l2 n, queueStep_n n l1 l2 -> n = 1 -> queueStep l1 l2.
  Proof.
    intros l1 l2 n H;
      induction H; intros; si.
     apply Nat.eq_add_1 in H1.
     do 2 destruct H1.
     apply queueStep_n_0 in H0; auto.
     simpl; subst. apply IHqueueStep_n1. auto.
     apply queueStep_n_0 in H; auto.
     simpl; subst. apply IHqueueStep_n2. auto.
  Qed.

  Lemma queueStep_n_swap_aux : 
    forall n l1 l2,
      queueStep_n_simpl n l1 l2 ->
      queueStep_n n l1 l2.
  Proof.
    intros.
    induction H; subst.
    constructor.
    replace (S n) with (n + 1).
    apply QMS_trans with (l2 := l2).
    auto. constructor. auto. omega.
  Qed.

  Lemma queueStep_n_swap :
    forall n l1 l2,
      queueStep_n_simpl n l1 l2 <->
      queueStep_n n l1 l2.
  Proof.
    split.
    + apply queueStep_n_swap_aux.
    + intros. induction H.
      - constructor.
      - econstructor. apply QMSs_refl. auto.
      - dependent induction m.
        intros. simpl.
        apply queueStep_n_0 in H0. subst.
        replace (n+0) with n; try omega. auto.
        auto. simpl.
        replace (n+ S m) with (S (n + m)); try omega.
        inversion IHqueueStep_n2; subst.
        econstructor. eapply IHm; eauto.
        apply queueStep_n_swap_aux. apply H2. auto.
  Qed.

  Lemma queueStep_n_inv :
    forall n m p1 p2, queueStep_n (n + m) p1 p2 ->
      exists p_int, queueStep_n n p1 p_int /\ queueStep_n m p_int p2.
  Proof.
    intros. rewrite <- queueStep_n_swap in H.  
    dependent induction H.
    + symmetry in x.
      apply plus_is_O in x. destruct x. subst.
      exists l; split; constructor.
   + case_eq m; intros. subst. 
      replace (n + 0) with n in x; try omega.
      exists l3. subst. split.
      rewrite <- queueStep_n_swap. econstructor; eauto.
      constructor. subst.
      replace (n + S n1) with (S (n + n1)) in x.
      inversion x. subst.
      specialize (IHqueueStep_n_simpl n n1 (eq_refl _)).
      destruct IHqueueStep_n_simpl. inversion H1.
      exists x0. split; auto.
      rewrite <- queueStep_n_swap.
      econstructor.
      rewrite queueStep_n_swap. eauto.
      auto. omega.
  Qed.

  Lemma queueStep_n_lt_l :
    forall n m p1 p2,
      m < n -> queueStep_n n p1 p2 ->  
      exists p3, queueStep_n m p1 p3.
  Proof.
    intros n.
    induction n.
    intros. omega.
    intros. inversion H; subst.
    rewrite <- queueStep_n_swap in H0.
    inversion H0; subst. exists l2.
    apply queueStep_n_swap.
    auto.
    assert (m < n). omega.
    rewrite <- queueStep_n_swap in H0.
    inversion H0; subst.
    apply queueStep_n_swap_aux  in H4. 
    apply (IHn m) in H4. auto. auto.
  Qed.

  Lemma queueStep_n_uniq :
    forall n p1 p2 p3,
      queueStep_n n p1 p2 ->
      queueStep_n n p1 p3 ->
      p2 = p3.
  Proof.
    induction n.
    intros. apply queueStep_n_0 in H; auto. 
    apply queueStep_n_0 in H0; auto. subst. auto.
    intros. rewrite <- queueStep_n_swap in H, H0.
    inversion H; subst. inversion H0; subst.
    assert (l0 = l2).
    eapply IHn; apply queueStep_n_swap; eauto.
    subst.
    inversion H3; subst. inversion H5; subst.
    inversion H1; subst. auto.
  Qed.

  Hint Constructors queueStep_n.
  Hint Resolve queueStep_n_0.

  Lemma queueStep_n_simpl_length_app' a1 a1' b1 b1' x :
    queueStep_n_simpl' (length a1) (a1 ++ x, b1) (a1', b1') -> 
    forall a2,
      queueStep_n_simpl' (length a1) (a1 ++ a2 ++ x, b1) (a2 ++ a1', b1').
  Proof.
    revert a1' b1 b1' x.
    remember (length a1) as n.
    revert a1 Heqn.
    induction n.
    { intros.
      inversion H; subst.
      assert (H2: a1 = nil).
      { destruct a1; auto; inversion Heqn. }
      rewrite H2; simpl. constructor. }
    intros.
    inversion H; subst.
    inversion H1; subst. clear H1.
    inversion H0; subst. clear H0.
    destruct a1; subst; try solve[inversion Heqn].
    inversion Heqn; subst.
    inversion H3; subst. clear H3.
    eapply QMSs_trans'.
    { simpl; econstructor; eauto. }
    rewrite <-app_assoc.
    clear H.
    revert H2.
    generalize (stepCandSet a) as z.
    generalize (Accum a b) as w.
    intros.
    rewrite <-app_assoc in H2.
    apply IHn with (a2:=a1) (a3:=a2) in H2; auto.
    rewrite <-!app_assoc; auto.
  Qed.
  
  Lemma queueStep_n_simpl_length_app a1 a1' b1 b1' :
    queueStep_n_simpl' (length a1) (a1, b1) (a1', b1') -> 
    forall a2,
      queueStep_n_simpl' (length a1) (a1 ++ a2, b1) (a2 ++ a1', b1').
  Proof.
    intros H.
    generalize (@queueStep_n_simpl_length_app' a1 a1' b1 b1' nil) as H2; intro.
    rewrite app_nil_r in H2.
    specialize (H2 H).
    intros a2.
    specialize (H2 a2).
    rewrite app_assoc in H2.
    rewrite app_nil_r in H2.
    auto.
  Qed.    

  Lemma queueStep_n_simpl'_trans n m l1 l2 l3 :
    queueStep_n_simpl' n l1 l2 ->
    queueStep_n_simpl' m l2 l3 -> 
    queueStep_n_simpl' (n + m) l1 l3.
  Proof.
    revert m l1 l2 l3.
    induction n.
    { intros.
      inversion H; subst.
      apply H0. }
    intros.
    simpl.
    inversion H; subst.
    apply QMSs_trans' with (l2:=l4); auto.
    eapply IHn; eauto.
  Qed.    

  Lemma queueStep_n_simpl'_swap_forward n l l' :
    queueStep_n n l l' -> queueStep_n_simpl' n l l'.
  Proof.
    induction 1; try solve[constructor].
    { apply QMSs_trans' with (l2:=l2); auto. constructor. }
    apply (queueStep_n_simpl'_trans IHqueueStep_n1 IHqueueStep_n2).
  Qed.    

  Lemma queueStep_n_simpl'_swap_backward n l l' :
    queueStep_n_simpl' n l l' -> queueStep_n n l l'.
  Proof.
    induction 1; try solve[constructor].
    assert (H3: S n = 1 + n) by omega. rewrite H3.
    eapply QMS_trans; eauto.
  Qed.    
  
  Lemma queueStep_n_simpl'_swap n l l' :
    queueStep_n n l l' <-> queueStep_n_simpl' n l l'.
  Proof.
    split.
    apply queueStep_n_simpl'_swap_forward.
    apply queueStep_n_simpl'_swap_backward.
  Qed.    

  Lemma queueStep_n_length_app :
    forall a1 a1' b1 b1',
      queueStep_n (length a1) (a1, b1) (a1', b1') ->
      forall a2,
        queueStep_n (length a1) (a1 ++ a2, b1) (a2 ++ a1', b1').
  Proof.
    intros a1 a1' b1 b1'.
    rewrite queueStep_n_simpl'_swap; intros H a2.
    rewrite queueStep_n_simpl'_swap.
    apply queueStep_n_simpl_length_app; auto.
  Qed.    

  Lemma queueStep_n_ind_b :
    forall n a1 a2 a2' b1 b1' b2 b2',
      queueStep_n n (a1, b1) (a2, b2) ->
      queueStep_n n (a1, b1') (a2', b2') -> 
        a2 = a2'.
  Proof.
    induction n. intros.
    apply queueStep_n_0 in H.
    apply queueStep_n_0 in H0.
    inversion H. inversion H0.
    subst. auto. auto. auto.
    intros. replace (S n) with (n+1) in *; try omega.
    apply queueStep_n_inv in H.
    apply queueStep_n_inv in H0.
    inversion H. inversion H0.
    destruct H1, H2. destruct x, x0.
    specialize (IHn _ _ _ _ _ _ _ H1 H2). subst.
    apply queueStep_n_1 in H3. apply queueStep_n_1 in H4.
    inversion H3; inversion H4; subst.
    inversion H5; subst. inversion H9; subst.
    inversion H10. subst. inversion H6. subst.
    auto. auto. auto.
  Qed. 
  
  Hint Resolve queueStep_n_ind_b.

 Lemma queueStep_n_length_app' :
    forall a1 a1' b1 b1',
      queueStep_n (length a1) (a1, b1) (a1', b1') ->
      forall a2 b2 p,
        queueStep_n (length a1) (a1 ++ a2, b2) p ->
        fst p = a2 ++ a1'.
  Proof.
    intros.
    destruct p.
    specialize (@queueStep_n_length_app a1 a1' b1 b1' H a2).
    intros.
    inversion H; intros;
    subst; eauto.
  Qed.


  Lemma queueBigStep_n : forall n s1 s2,
    queueStep_n n s1 s2 ->
    queueBigStep s1 s2.
  Proof.
    intros.
    apply queueStep_n_simpl'_swap_forward in H.
    induction H. apply rt_refl.
    eapply rt_trans.
    constructor. eauto. eauto.
  Qed.

  Lemma length_ind :
    forall (T : Type) (P : list T -> Prop),
      (P nil) ->
      (forall n,
        (forall (l : list T), (length l = n) -> P l) ->
        (forall (l' : list T), (length l' = S n) -> P l')) ->
      forall l, P l.
  Proof.
    intros. remember (length l) as x. generalize dependent l.
    dependent induction x. intros. symmetry in Heqx.
    apply length_zero_iff_nil in Heqx. subst. auto.
    intros. destruct l. inversion Heqx. 
    simpl in Heqx. inversion Heqx. 
    apply (H0 x). intros. apply IHx. auto. auto.
  Qed.

  Notation prog_state := (list A*B)%type.
  Definition container (s : prog_state) := fst s.
  Definition output (s : prog_state) := snd s.

  Lemma queueStep_n_exists :
    forall a, exists a', queueStep_n (length (container a)) a a'.
  Proof.
    destruct a. revert l0.
    induction l using length_ind.
    intros. exists (nil, l0). simpl.
    constructor.
    case_eq l; intros. rewrite H1 in H0. simpl in H0. omega.
    rewrite H1 in H0. inversion H0.
    specialize (H l0 H3 (Accum p l1)).
    destruct H. simpl in H.
    destruct x.
    exists (stepCandSet p ++ l2, l3). simpl. 
    rewrite queueStep_n_simpl'_swap.
    apply QMSs_trans' with (l2 := (l0 ++ stepCandSet p, Accum p l1)).
    econstructor. reflexivity. reflexivity.
    rewrite <- queueStep_n_simpl'_swap.
    apply queueStep_n_length_app. auto.
  Qed.

  Lemma stepEq :
    forall p1 p2, queueStep p1 p2 -> queueMIS p1 = queueMIS p2.
  Proof.
    intros.
    inversion H.
    subst.
    unfold queueMIS.
    unfold IterQueueWithAccum.
    rewrite Fix_eq; auto.
    intros.
    destruct (mkSmallerQueue A B R Accum stepCandSet stepCandSet_desc x);
    auto.
    destruct s.
    simpl in *.
    auto.
  Qed.

  Lemma stepNEq :
    forall n p1 p2, queueStep_n n p1 p2 -> queueMIS p1 = queueMIS p2.
  Proof.
    intros.
    induction H.
    auto.
    inversion H. subst.
    unfold queueMIS.  
    unfold IterQueueWithAccum.
    rewrite Fix_eq; auto.
    intros.
    destruct (mkSmallerQueue A B R Accum stepCandSet stepCandSet_desc x);
    auto.
    destruct s.
    auto.
    rewrite IHqueueStep_n1 . auto.
  Qed.

  Lemma stepBigEq :
    forall p1 p2, queueBigStep p1 p2 -> queueMIS p1 = queueMIS p2.
  Proof.
    intros. induction H; try auto.
    inversion H. subst.
    unfold queueMIS.  
    unfold IterQueueWithAccum.
    rewrite Fix_eq; auto.
    intros.
    destruct (mkSmallerQueue A B R Accum stepCandSet stepCandSet_desc x);
    auto.
    destruct s.
    auto.
    rewrite IHclos_refl_trans1. auto.
  Qed.

  Definition AasB : list A -> B :=
    fun l => map snd l.

  (* This match relation should hold between
      every iteration of our queueMIS and 
      mkCandidate steps, excluding the final set of
      steps when things are moved into the accumulator
    ~~~~~~~~~~~~~~~~~~~~~~~~~~
      It holds when:
         1.) Removing the indexing from the elements of the
            container (AasB) yields the same list 
         2.) All elements in the container have the same index
         3.) The output of a state is empty
    ~~~~~~~~~~~~~~~~~~~~~~~~~~
  *)

  Inductive matchQandCand : nat -> prog_state -> B -> Prop :=
  | matchQandCand_intro :
      forall s b v,
        AasB (container s) = b -> (* 1 *)
        (forall a, In a (container s) -> iXToNat (fst a) = v) -> (* 2 *)
        (output s = nil) -> (* 3 *)
        matchQandCand v s b.

  Lemma nat_1 : forall n m,
      S n = S m ->
      n = m.
  Proof.
    intros.
    omega.
  Qed.

  Lemma list_sep : forall (T : Type) (l : list T) n m,
    length l = n + m ->
    exists l1 l2, length l1 = n /\ length l2 = m /\ l1++l2 = l.
  Proof.
    induction l.
    assert (@length T nil  = 0).
    apply length_zero_iff_nil.
    auto.
    intros.
    rewrite H0 in H.
    apply plus_is_O in H.
    intuition.
    exists nil,nil.
    intuition.
    intros.
    destruct n; simpl in *.
    exists nil.
    specialize (IHl 0 (m -1)).
    simpl in IHl.
    assert (length l = m - 1) by omega.
    apply IHl in H0.
    do 2 destruct H0.
    intuition.
    subst.
    apply length_zero_iff_nil in H1.
    subst.    
    simpl.
    exists (a :: x0).
    eauto.
    specialize (IHl n m).
    apply nat_1 in H.
    apply IHl in H.
    do 2 destruct H.
    intuition.
    destruct m.
    subst.
    apply length_zero_iff_nil in H.
    subst.
    assert (length (x ++ nil) = length x + 0).
    {
      clear IHl.
      induction x; auto.
      simpl.
      rewrite IHx.
      auto.
    }
    apply IHl in H.
    do 2 destruct H.
    intuition; subst.
    apply length_zero_iff_nil in H.
    subst.
    exists (a :: x).
    exists nil.
    intuition; eauto.
    subst.
    exists (a :: x), x0.
    eauto.
  Qed.

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

  Lemma queueStep_n_ltV_output :
    forall p1 p2,
      queueStep_n (length (container p1)) p1 p2 ->
      (forall a, In a (container p1) -> (iXToNat (fst a)) < |V|) ->       
      output p1 = output p2.
  Proof.
    destruct p1. generalize dependent l0.
    induction l using length_ind.
    - intros. simpl in *. subst. simpl in *.
      apply queueStep_n_0 in H. subst. simpl. split; auto. auto.
    - intros. subst. case_eq l; intros; subst;
      inversion H0; subst. simpl fst in *.
      simpl snd in *. simpl in *.
      replace (S (length l1)) with (1 + length l1) in H1 by omega.
      apply queueStep_n_inv in H1.
      destruct H1 as [p_int [H3 H4]].
      apply queueStep_n_1 in H3.
      inversion H3; subst. inversion H1; subst.
      specialize (queueStep_n_exists (l, Accum a b)).
      intros. destruct H5, x. simpl in H5.
      specialize (H l eq_refl (Accum a b) (l0, l1) H5).
      assert (Accum a b = snd (l0, l1)). apply H.
      intros. apply H2. right. auto.
      assert (queueStep_n (length l) (l ++ stepCandSet a, Accum a b) (stepCandSet a ++ l0, l1)).
      specialize (queueStep_n_length_app H5).
      intros. apply H7.
      assert ((stepCandSet a ++ l0, l1) = p2).
      eapply queueStep_n_uniq; eauto. subst. simpl in *.
      rewrite <- H6. unfold Accum.
      assert (iXToNat (fst a) =? |V| = false).
      assert (iXToNat (fst a) < |V|).
      apply H2. left. auto.
      apply Nat.eqb_neq. omega. rewrite H8. auto. auto.
  Qed.

  Lemma stepQ_as_mkCandSets :
    forall n (p1 p2 : prog_state),
      queueStep_n n p1 p2 ->      
      forall v (lG : B),
      length lG = n ->
      matchQandCand v p1 lG ->
      v < |V| ->  v <> 0 ->
      matchQandCand (S v) p2 (mkCandidateSets (LiftGraph (S v) G) lG).
  Proof.
    intros n p1 p2 H. remember H as H'.
    clear HeqH'. generalize p1 p2 H'.
    clear H'.
    dependent induction H.
    + intros. apply length_zero_iff_nil in H. subst.
      apply queueStep_n_0 in H'. subst.
      inversion H0; subst.
      constructor. rewrite H. auto.
      intros. unfold AasB in H.
      apply  map_eq_nil in H. rewrite H in H5.
      inversion H5. auto. auto.
    + intros. apply queueStep_n_1 in H'.
      inversion H'; subst.
      inversion H1; subst.
      simpl in H0. inversion H0.
      assert (l= nil).
      {
        unfold AasB in H7. rewrite map_length in H7.
        apply length_zero_iff_nil. auto.
      }
      subst. rewrite app_nil_l in *.
      destruct a. destruct i. simpl fst in *.
      assert (In (Index.mk pf, l) ((Index.mk pf, l) :: nil)). left; auto.
      apply H5 in H4. simpl in H4. simpl in H6. subst. simpl.
      destruct (Nat.eq_dec). omega.
      destruct graphs_nondep.inEdgeDec.
      destruct isMIS. rewrite LiftGraph_red.
      destruct LFMIS_dec.
      constructor; simpl; intros; auto. destruct H4. subst. simpl.
      auto. destruct H4. subst. simpl. auto. inversion H4.
      unfold Accum. simpl. replace (v =? |V|) with false.
      auto. symmetry. apply Nat.eqb_neq. auto.    
      constructor. simpl. auto.
      intros. inversion H4. subst; simpl. auto.
      inversion H6. simpl. unfold Accum. simpl.
      replace (v =? |V|) with false.
      auto. symmetry. apply Nat.eqb_neq. auto.
      auto. constructor. simpl. auto.
      intros. inversion H4. subst; simpl. auto.
      inversion H6. simpl. simpl. unfold Accum. simpl.
      replace (v =? |V|) with false.
      auto. symmetry. apply Nat.eqb_neq. auto.
      destruct graphs_nondep.vertexConnected.
      destruct isMIS. rewrite LiftGraph_red.
      destruct LFMIS_dec. constructor. simpl. auto.
      intros. inversion H4. subst; simpl. auto.
      inversion H6; subst. simpl. auto. inversion H8.
      simpl. unfold Accum. simpl.
      replace (v =? |V|) with false.
      auto. symmetry. apply Nat.eqb_neq. auto.
      constructor. simpl. auto.
      intros. inversion H4. subst; simpl. auto.
      inversion H6. simpl. unfold Accum. simpl.
      replace (v =? |V|) with false.
      auto. symmetry. apply Nat.eqb_neq. auto.
      auto.
      constructor. simpl. auto.
      intros. inversion H4. subst; simpl. auto.
      inversion H6. simpl. unfold Accum. simpl.
      replace (v =? |V|) with false.
      auto. symmetry. apply Nat.eqb_neq. auto.
      destruct independent_lGraph.
      constructor. simpl. auto.
      intros. inversion H4. subst; simpl. auto.
      inversion H6. simpl. unfold Accum. simpl.
      replace (v =? |V|) with false.
      auto. symmetry. apply Nat.eqb_neq. auto.
      destruct isMIS. rewrite LiftGraph_red.
      destruct LFMIS_dec.
      constructor. simpl. auto.
      intros. inversion H4. subst; simpl. auto.
      inversion H6. subst. simpl. auto. inversion H8.
      simpl. unfold Accum. simpl.
      replace (v =? |V|) with false.
      auto. symmetry. apply Nat.eqb_neq. auto.
      constructor. simpl. auto.
      intros. inversion H4. subst; simpl. auto.
      inversion H6. subst. simpl.
      unfold Accum. simpl.
      replace (v =? |V|) with false.
      auto. symmetry. apply Nat.eqb_neq. auto.
      auto.
      constructor. simpl. auto.
      intros. inversion H4. subst; simpl. auto.
      inversion H6. subst. simpl.
      unfold Accum. simpl.
      replace (v =? |V|) with false.
      auto. symmetry. apply Nat.eqb_neq. auto.
      auto.
    + intros. inversion H2; subst.
      assert (snd p2 = nil) as match_ob.
      { rewrite <- H7. symmetry.
        apply queueStep_n_ltV_output.
        auto. unfold AasB in H1. rewrite map_length in H1.
        rewrite H1. auto. intros.
        apply H6 in H5. subst. auto.
      }
        assert (exists ln lm,
                length ln = n /\ length lm = m /\ ln++lm = (fst p1)).
      { unfold AasB in H1. rewrite map_length in H1.
        apply list_sep in H1. auto. }
      destruct H5 as [nl [ml [H8 [H9 ] ] ] ].
      unfold container.
      rewrite <- H5.
      replace (mkCandidateSets (LiftGraph (S v) G) (AasB (nl ++ ml))) with
        ( mkCandidateSets (LiftGraph (S v) G) (AasB nl) ++
          mkCandidateSets (LiftGraph (S v) G) (AasB ml)).
      apply queueStep_n_inv in H'.
      inversion H'. destruct H10.
      destruct p1; simpl in *.
      destruct (queueStep_n_exists (nl, l0)); simpl in H12.
      destruct x0.
      specialize (queueStep_n_length_app' H12). intros.
      rewrite <- H8 in H10. rewrite <- H5 in H10. apply H13 in H10.
      destruct (queueStep_n_exists (ml, l0)); simpl in H14.
      destruct x0. specialize (queueStep_n_length_app' H14). intros.
      destruct x. simpl in *.
      rewrite H10, <- H9 in H11.
      apply H15 in H11.
      assert (length (AasB ml) = m).
      { rewrite <- H9. unfold AasB. apply map_length. }
      assert (length (AasB nl) = n).
      { rewrite <- H8. unfold AasB. apply map_length. }
      rewrite H9 in H14. rewrite H8 in H12.
      specialize (IHqueueStep_n1 (nl, l0) (l4, l5) H12  v (AasB nl) H17).
      specialize (IHqueueStep_n2 (ml, l0) (l6, l7) H14 v (AasB ml) H16).
      assert (matchQandCand (S v) (l4, l5)
        (mkCandidateSets (LiftGraph (S v) G) (AasB nl))).
      {
        apply IHqueueStep_n1. 
        constructor. simpl. auto. simpl.
        intros. apply H6. rewrite <- H5.
        apply in_or_app. left. auto.
        auto. omega. omega.
      }
      assert (matchQandCand (S v) (l6, l7)
              (mkCandidateSets (LiftGraph (S v) G) (AasB ml))).
      {
        apply IHqueueStep_n2. 
        constructor. simpl. auto. simpl.
        intros. apply H6. rewrite <- H5.
        apply in_or_app. right. auto.
        auto. omega. omega.
      }
      inversion H18; subst. inversion H19; subst.
      simpl in H5, H20. constructor.
      unfold container. rewrite H11.
      unfold AasB. rewrite map_app. fold AasB.
      unfold AasB in H5, H20. rewrite H5, H20.
      auto. intros. unfold container in H9.
      rewrite H11 in H9.
      apply in_app_or in H9. destruct H9.
      apply H21. auto. apply H7. auto.
      auto. 
      unfold AasB. rewrite map_app.
      rewrite mkCandidateSets_app. auto.
      simpl. omega.
  Qed.


  Lemma stepQ_as_mkCandSets_terminal :
    forall n (p1 p2 : prog_state),
      queueStep_n n p1 p2 -> 
      length (container p1) = n ->
      (forall a, In a (fst p1) -> iXToNat (fst a) = |V|) ->
      fst p2 = nil /\ Permutation (snd p2) (AasB (fst p1) ++ (snd p1)).
  Proof.
    destruct p1. generalize dependent l0.
    generalize n. clear n.
    induction l using length_ind.
    - intros. simpl in *. subst. simpl in *.
      apply queueStep_n_0 in H. subst. simpl. split; auto. auto.
    - intros. subst. case_eq l; intros; subst;
      inversion H0; subst. simpl fst in *.
      simpl snd in *. simpl in H1.
      replace (S(length l1)) with (1 + length l1) in H1.
      apply queueStep_n_inv in H1.
      destruct H1 as [p_int [H2 H4]].
      apply queueStep_n_1 in H2.
      inversion H2; subst. inversion H1; subst.
      assert (stepCandSet a = nil).
      {
        unfold stepCandSet.
        assert (iXToNat (fst a) = |V|). apply H3. left. auto.
        destruct a. destruct i.
        case (Nat.eq_dec i |V|); intros. auto. simpl in H5. omega.
      }
      rewrite H5, app_nil_r in H4.
      specialize (H l eq_refl (length l) (Accum a b) p2 H4 eq_refl).
      assert ((forall a : A, In a l -> iXToNat (fst a) = |V|)).
      {
        intros. apply H3. right. auto.
      }
      apply H in H6. destruct H6.
      split. auto. eapply Permutation_trans. apply H7.
      unfold Accum. assert (iXToNat (fst a) = |V|). apply H3. left. auto.
      apply Nat.eqb_eq in H8. rewrite H8.
      unfold AasB. simpl. apply Permutation_sym.
      apply Permutation_cons_app. apply Permutation_refl.
      auto.
  Qed.

  Lemma output_backwards_nil :
   forall (s1 s2 : prog_state),
      queueStep s1 s2 -> 
      output s2 = nil -> 
      output s1 = nil.
  Proof.
    intros. inversion H.
    subst. rewrite <- H0.
    simpl. unfold Accum in *.
    destruct (iXToNat (fst a) =? |V| );
    simpl in H0. inversion H0. auto.
  Qed.
 
  Lemma output_big_backwards_nil :
    forall (s1 s2 : prog_state),
      queueBigStep s1 s2 -> 
      output s2 = nil -> 
      output s1 = nil.
  Proof.
    intros s1 s2 H.
    dependent induction H.
    - apply output_backwards_nil. auto.
    - auto.
    - intros. apply IHclos_refl_trans2 in H1.
      apply IHclos_refl_trans1. auto.
  Qed.
End RefineMIS.

Section noDepRefine.

  Lemma map_struct_inv  :
    forall A A' B (f : A -> B) (f' : A' -> B) a l lb,
      map f (a::l) = map f' lb -> exists a' l', lb = a'::l'.
  Proof.
    intros. case_eq lb. intros; subst. inversion H. intros.
    rewrite H0 in H. do 2 eexists. eauto.
  Qed.

  Record queueMIS_state : Type :=
    mkState {
      Gam : lGraph;
      state : list (Ix (S (lV Gam)) * list nat) * list (list nat)
    }.

  Definition startState G : list (Ix (S (lV G)) * list nat) * list (list nat) :=
    ((Ox G, nil)::nil, nil).

  Definition queueMIS_startState G := mkState G (startState G).
  
  Definition stateContainer (s : queueMIS_state) := fst (state s).
  Definition outputContainer (s : queueMIS_state) := snd (state s).

  Definition indicesOfState (s : queueMIS_state) :=
    map (fun e => (iXToNat (Gam s)) (fst e)) (stateContainer s).

  Inductive matchQueue : queueMIS_state -> queueMIS_state -> Prop :=
  | mkQmatch : forall s1 s2,
      AasB (Gam s1) (stateContainer s1) = AasB (Gam s2) (stateContainer s2) ->
      indicesOfState s1 = indicesOfState s2 ->
      outputContainer s1 = outputContainer s2 ->
      matchQueue s1 s2.

  Lemma stepCandSet_lift_snd' : forall n G a1 a2,
    let G' := LiftGraph n G in 
    n < (lV G) ->
    (iXToNat _ (fst a1) = iXToNat _ (fst a2)) -> 
    snd a1 = snd a2 ->
    (forall b, Accum G' a1 b = b) ->
    map snd (stepCandSet G' a1) = map snd (stepCandSet G a2).
  Proof.
    intros.
    unfold stepCandSet; simpl.
    destruct a1, a2; simpl.
    destruct i, i0; simpl in *.
    assert (i <> n). subst.
    specialize (H2 nil). unfold Accum in H2.
    simpl in H2. intros H3. subst. rewrite Nat.eqb_refl in H2.
    inversion H2.
    case_eq (Nat.eq_dec i n). intros; subst. omega.
    intros. case_eq (Nat.eq_dec i0 (lV G)). intros; subst. omega.
    intros. subst. rename i0 into i.
    assert (LiftGraph (S i) G' = LiftGraph (S i) G). unfold G'.
    {
      assert ((S i < n) \/  S i = n). omega.
      destruct H0. apply LiftGraph_red. omega.
      subst. replace (S i) with (lV ((LiftGraph (S i) G))).
      rewrite fix_LiftGraph. simpl. auto. auto.
    }
    rewrite H0.
    assert ((LiftGraph i G') = LiftGraph i G).
    {
      unfold G'. apply LiftGraph_red. omega.
    }
    rewrite H1.
    destruct graphs_nondep.inEdgeDec; simpl; auto.
    destruct isMIS; simpl; auto.
    destruct LFMIS_dec; simpl; auto.
    destruct graphs_nondep.vertexConnected; simpl; auto.
    destruct isMIS; simpl; auto.
    destruct LFMIS_dec; simpl; auto.
    destruct independent_lGraph; simpl; auto.
    destruct isMIS; simpl; auto.
    destruct LFMIS_dec; simpl; auto.
  Qed.

  Lemma stepCandSet_lift_snd : forall n G a1 a2,
    let G' := LiftGraph n G in
    n < (lV G) ->
    (iXToNat _ (fst a1) = iXToNat _ (fst a2)) -> 
    (iXToNat _ (fst a1) < n) ->
    snd a1 = snd a2 ->
    map snd (stepCandSet G' a1) = map snd (stepCandSet G a2).
  Proof.
    intros.
    unfold stepCandSet; simpl.
    destruct a1, a2; simpl.
    destruct i, i0; simpl in *.
    case_eq (Nat.eq_dec i n). intros; subst. omega.
    intros. case_eq (Nat.eq_dec i0 (lV G)). intros; subst. omega.
    intros. subst. rename i0 into i.
    assert (LiftGraph (S i) G' = LiftGraph (S i) G). unfold G'.
    {
      assert ((S i < n) \/  S i = n). omega.
      destruct H0. apply LiftGraph_red. omega.
      subst. replace (S i) with (lV ((LiftGraph (S i) G))).
      rewrite fix_LiftGraph. simpl. auto. auto.
    }
    rewrite H0.
    assert ((LiftGraph i G') = LiftGraph i G).
    {
      unfold G'. apply LiftGraph_red. omega.
    }
    rewrite H2.
    destruct graphs_nondep.inEdgeDec; simpl; auto.
    destruct isMIS; simpl; auto.
    destruct LFMIS_dec; simpl; auto.
    destruct graphs_nondep.vertexConnected; simpl; auto.
    destruct isMIS; simpl; auto.
    destruct LFMIS_dec; simpl; auto.
    destruct independent_lGraph; simpl; auto.
    destruct isMIS; simpl; auto.
    destruct LFMIS_dec; simpl; auto.
  Qed.

  Lemma stepCandSet_lift_fst : forall n G a1 a2,
    let G' := LiftGraph n G in
    n < (lV G) ->
    (iXToNat _ (fst a1) = iXToNat _ (fst a2)) -> 
    (iXToNat _ (fst a1) < n) ->
    snd a1 = snd a2 ->
      map (fun e => (iXToNat _) (fst e)) (stepCandSet G' a1) =
      map (fun e => (iXToNat _) (fst e)) (stepCandSet G a2).
  Proof.
    intros.
    unfold stepCandSet; simpl.
    destruct a1, a2; simpl.
    destruct i, i0; simpl in *.
    case_eq (Nat.eq_dec i n). intros; subst. omega.
    intros. case_eq (Nat.eq_dec i0 (lV G)). intros; subst. omega.
    intros. subst. rename i0 into i.
    assert (LiftGraph (S i) G' = LiftGraph (S i) G). unfold G'.
    {
      assert ((S i < n) \/  S i = n). omega.
      destruct H0. apply LiftGraph_red. omega.
      subst. replace (S i) with (lV ((LiftGraph (S i) G))).
      rewrite fix_LiftGraph. simpl. auto. auto.
    }
    rewrite H0.
    assert ((LiftGraph i G') = LiftGraph i G).
    {
      unfold G'. apply LiftGraph_red. omega.
    }
    rewrite H2.
    destruct graphs_nondep.inEdgeDec; simpl; auto.
    destruct isMIS; simpl; auto.
    destruct LFMIS_dec; simpl; auto.
    destruct graphs_nondep.vertexConnected; simpl; auto.
    destruct isMIS; simpl; auto.
    destruct LFMIS_dec; simpl; auto.
    destruct independent_lGraph; simpl; auto.
    destruct isMIS; simpl; auto.
    destruct LFMIS_dec; simpl; auto.
  Qed.

  Lemma stepCandSet_lift_fst' : forall n G a1 a2,
    let G' := LiftGraph n G in 
    n < (lV G) ->
    (iXToNat _ (fst a1) = iXToNat _ (fst a2)) -> 
    snd a1 = snd a2 ->
    (forall b, Accum G' a1 b = b) ->
      map (fun e => (iXToNat _) (fst e)) (stepCandSet G' a1) =
      map (fun e => (iXToNat _) (fst e)) (stepCandSet G a2).
  Proof.
    intros.
    unfold stepCandSet; simpl.
    destruct a1, a2; simpl.
    destruct i, i0; simpl in *.
    assert (i <> n). subst.
    specialize (H2 nil). unfold Accum in H2.
    simpl in H2. intros H3. subst. rewrite Nat.eqb_refl in H2.
    inversion H2.
    case_eq (Nat.eq_dec i n). intros; subst. omega.
    intros. case_eq (Nat.eq_dec i0 (lV G)). intros; subst. omega.
    intros. subst. rename i0 into i.
    assert (LiftGraph (S i) G' = LiftGraph (S i) G). unfold G'.
    {
      assert ((S i < n) \/  S i = n). omega.
      destruct H0. apply LiftGraph_red. omega.
      subst. replace (S i) with (lV ((LiftGraph (S i) G))).
      rewrite fix_LiftGraph. simpl. auto. auto.
    }
    rewrite H0.
    assert ((LiftGraph i G') = LiftGraph i G).
    {
      unfold G'. apply LiftGraph_red. omega.
    }
    rewrite H1.
    destruct graphs_nondep.inEdgeDec; simpl; auto.
    destruct isMIS; simpl; auto.
    destruct LFMIS_dec; simpl; auto.
    destruct graphs_nondep.vertexConnected; simpl; auto.
    destruct isMIS; simpl; auto.
    destruct LFMIS_dec; simpl; auto.
    destruct independent_lGraph; simpl; auto.
    destruct isMIS; simpl; auto.
    destruct LFMIS_dec; simpl; auto.
  Qed.

  Lemma matchQueueStep' : forall n G st1 st1' st2,
    let G' := LiftGraph n G  in
    let S1 := mkState G' st1 in
    let S2 := mkState G st2  in
    let S1':= mkState G' st1' in
    n < (lV G) -> 
    matchQueue S1 S2  -> 
    queueStep G' st1 st1' -> 
    outputContainer S1' = nil ->
    (forall e, In e (indicesOfState S1') -> e <= n) ->
    exists st2',
      matchQueue S1' (mkState G st2') /\ queueStep G st2 st2'.
  Proof.
    intros. rename H3 into H_.
    inversion H1. subst.
    assert (exists a' l', a'::l' = stateContainer S2).
    { inversion H0; subst.
      unfold stateContainer, AasB in H3. simpl (fst (state S1)) in H3.
      unfold stateContainer; simpl. simpl (fst (state S2)) in H3.
      generalize (@map_struct_inv _ _ _ snd snd a l (fst st2) H3). intros.
      destruct H6 as [a' [l' H6]]. rewrite H6. eexists; eauto.
    }
    destruct H3 as [a' [l' H3]].
    exists (l' ++ stepCandSet G a', Accum G a' b).
    split.
    constructor. 
    + unfold stateContainer, AasB. simpl.
      do 2 rewrite map_app.
      inversion H0. subst.
      unfold stateContainer, AasB in H4.
      simpl in H4. unfold stateContainer in H3.
      simpl in H3. rewrite <- H3 in H4. simpl in H4.
      inversion H4.
      f_equal. auto.
      apply stepCandSet_lift_snd'. auto. unfold indicesOfState in H5.
      unfold stateContainer in H5; simpl in H5.
      rewrite <- H3 in H5; simpl in H5.
      inversion H5. auto. auto.
      intros.
      unfold outputContainer in H2. simpl in H2.
      unfold Accum in H2. unfold Accum.
      unfold G' in H2.
      case_eq (Nat.eqb (iXToNat (LiftGraph n G) (@fst (Ix (S (lV (LiftGraph n G)))) (list nat) a))
      (lV (LiftGraph n G))). intros z. rewrite z in H2. inversion H2.
      auto.
    + unfold indicesOfState, stateContainer; simpl. 
      do 2 rewrite map_app. f_equal.
      inversion H0; subst.
      unfold indicesOfState, stateContainer in H5.
      simpl in H5. unfold stateContainer in H3. simpl in H3.
      rewrite <- H3 in H5. simpl in H5.
      inversion H5. auto.
      apply stepCandSet_lift_fst'; auto.
      inversion H0; subst.
      unfold indicesOfState in H5.
      unfold stateContainer in H5; simpl in H5.
      unfold stateContainer in H3.
      simpl in H3.
      rewrite <- H3 in H5; simpl in H5.
      inversion H5. auto. 
      inversion H0.
      unfold stateContainer in H4. simpl in H4.
      unfold stateContainer in H3. simpl in H3.
      rewrite <- H3 in H4. simpl in H4. inversion H4.
      auto.
      intros.
      unfold outputContainer in H2. simpl in H2.
      unfold Accum in H2. unfold Accum.
      unfold G' in H2.
      case_eq (Nat.eqb (iXToNat (LiftGraph n G) (@fst (Ix (S (lV (LiftGraph n G)))) (list nat) a))
      (lV (LiftGraph n G))). intros z. rewrite z in H2. inversion H2.
      auto.
    + unfold outputContainer. simpl.
      inversion H0; subst.
      unfold indicesOfState in H5.
      rewrite <- H3 in H5. unfold stateContainer in H5; simpl in H5.
      inversion H5. unfold Accum. rewrite <- H8.
      unfold outputContainer in H2. simpl in H2. unfold Accum in H2.
      rewrite H2.
      case_eq (Nat.eqb (iXToNat G' (@fst (Ix (S n)) (list nat) a)) (lV G)); intros.
      apply Nat.eqb_eq in H7.
      destruct a. simpl in H7. destruct i. simpl in H7.
      generalize pf. intros pf'. rewrite H7 in pf'.
      simpl in pf'. omega. 
      generalize (output_backwards_nil H1).
      intros. unfold output in H10. simpl in H10.
      unfold Accum in H10. apply H10 in H2. auto.
    + unfold stateContainer in H3.  simpl in H3. econstructor; [|eauto].
      destruct st2. simpl in H3. rewrite H3. f_equal.
      inversion H0. unfold outputContainer in H6. simpl in H6.
      auto.
  Qed.

  Lemma matchQueueBigStep' : forall n G st1 st1' st2,
    let G' := LiftGraph n G  in
    let S1 := mkState G' st1 in
    let S2 := mkState G st2  in
    let S1':= mkState G' st1' in
    queueBigStep G' st1 st1' -> 
    n < (lV G) -> 
    matchQueue S1 S2  -> 
    outputContainer S1' = nil ->
    (forall e, In e (indicesOfState S1') -> e <= n) ->
    exists st2', matchQueue S1' (mkState G st2') /\ queueBigStep G st2 st2'.
  Proof.
    intros. dependent induction H.
    + generalize (@matchQueueStep' n G st1 st1' st2 H0); intros. 
      assert (exists st2' : list (Ix (S (lV G)) * list nat) * list (list nat),
        matchQueue {| Gam := LiftGraph n G; state := st1' |} {| Gam := G; state := st2' |} /\
        queueStep G st2 st2').
      { apply H4; try auto. }
      clear H4.
      destruct H5 as [st2' [H5 H6]].
      exists st2'. split. auto.
      constructor. auto.
    + exists st2. split; auto.
      apply rt_refl.
    + specialize (IHclos_refl_trans1 st2 y st1).
      destruct IHclos_refl_trans1 as [st2' HInt1]; try auto.
      {
        clear IHclos_refl_trans2.
        unfold outputContainer in H3.
        simpl in H3.
        unfold outputContainer. simpl.
        generalize (@output_big_backwards_nil (LiftGraph n G) y st1' H0).
        unfold output. simpl. intros. auto.
      }
      {
        clear IHclos_refl_trans2.
        intros. unfold indicesOfState, stateContainer in H4, H5.
        simpl in H4, H5.
        apply in_map_iff in H5.
        destruct H5 as [x [H5 H6]].
        unfold iXToNat in H5. destruct x.
        destruct i. simpl in H5. subst. omega.
      }
      specialize (IHclos_refl_trans2 st2' st1' y).
      destruct IHclos_refl_trans2 as [st2'' HInt2]; try auto.
      destruct HInt1. auto.
      exists st2''.
      split. destruct HInt2. apply H5.
      eapply rt_trans; destruct HInt1, HInt2; eauto.
  Qed.

  Program Definition one_lGraph : lGraph :=
    mkListGraph 1 nil _ _.
  Next Obligation. split; auto. Qed.

  Lemma Ix_one : forall (n1 n2 : Ix 1), n1 = n2.
  Proof.
    intros.
    case_eq n1. case_eq n2.
    intros. assert (i = i0). omega.
    subst.
    f_equal. apply proof_irrelevance.
  Qed. 

  Lemma reduceEdges_symm_one_empty :
    forall n (l : list ((Ix n)*(Ix n))),
    (forall x, ~ In (x, x) l) ->
      reduceLEdges l 1 = nil.
  Proof.
    intros. induction l. simpl. auto.
    simpl. rewrite IHl.
    destruct a. destruct i, i0.
    unfold oLift_pairIx. simpl.
    case_eq (lt_dec i 1); intros;
    case_eq (lt_dec i0 1); intros; auto.
    assert (i = 0) by omega.
    assert (i0 = 0) by omega. subst.
    apply False_rec. apply (H (Index.mk pf)).
    left. f_equal. f_equal. apply proof_irrelevance.
    intros x H'. eapply H. right. eauto.
  Qed.

  Lemma one_lGraph_uniq :
    forall G, LiftGraph 1 G = one_lGraph.
  Proof.
    intros.
    apply fix_LiftGraph_lemma. auto.
    simpl. destruct G. simpl.
    erewrite <- reduceEdges_symm_one_empty.
    reflexivity. apply lIrref.
  Qed.

  Lemma print_mis_one_lGraph :
    AllMIS one_lGraph = (0::nil)::nil.
  Proof. auto. Qed.

  Lemma queueMIS_EQ_AllMIS :
    forall n G, (lV G = n) -> lV G <> 0 -> 
      exists s', queueBigStep G (startState G) s' /\ matchQandCand G (lV G)  s' (AllMIS G).
  Proof.
    intros n.
    induction n.
    + intros. apply False_rec. apply H0. auto.
    + intros. simpl in H, H0. case_eq n.
      generalize (matchQueueBigStep').
      - intros; subst. simpl in *. clear H1. clear IHn.
        assert (G = one_lGraph).
        assert (G = LiftGraph 1 G).
        rewrite <- H. rewrite fix_LiftGraph. auto.
        rewrite H1. apply one_lGraph_uniq.
        subst.
        clear H H0. rewrite print_mis_one_lGraph.
        eexists. split. constructor.
        unfold startState, one_lGraph. econstructor; eauto.
        constructor. simpl. auto.
        intros. simpl in H.
        destruct H. rewrite <- H. simpl. auto.
        inversion H.
        simpl. compute. auto.
      - intros.
        specialize (IHn (LiftGraph n G)).
        assert (lV (LiftGraph n G) = n) by auto.
        assert (lV (LiftGraph n G) <> 0) by omega.
        specialize (IHn H2 H3).
        destruct IHn as [s' H4].
        destruct H4 as [H4 H5].
        clear H2 H3.
        assert (n < lV G) by omega.
        generalize (@matchQueueBigStep' n G
                      (startState (LiftGraph n G)) s' (startState G) H4 H2); intros.
        destruct H3 as [s'' [H3 H6]].
        { 
          constructor; simpl; auto.
        }
        {
          inversion H5. subst. apply H7.
        }
        intros. unfold indicesOfState, stateContainer in H3.
        simpl in H3. apply in_map_iff in H3.
        destruct H3 as [x [H3 H3']].
        destruct x. destruct i. simpl in H3. omega. 
        generalize (queueStep_n_exists G s''); intros.
        destruct H7 as [s''' H7].
        generalize (@stepQ_as_mkCandSets G (length (fst s''))
                      s'' s''' H7 (lV (LiftGraph n G))
                    (AllMIS (LiftGraph n G))); intros.
        assert  (matchQandCand G (S (lV (LiftGraph n G))) s'''
                  (mkCandidateSets (LiftGraph (S (lV (LiftGraph n G))) G)
                  (AllMIS (LiftGraph n G)))).
        apply H8.
        { inversion H5; subst. rewrite <- H9.
          unfold container, AasB; simpl. rewrite map_length.
          inversion H3. unfold AasB, stateContainer in H1. simpl in H1.
          do 2 rewrite <- (map_length snd). rewrite H1; auto.
        }
        { constructor.
          * inversion H3; subst.
            unfold stateContainer in H9; simpl in H9.
            unfold container. rewrite <- H9.
            inversion H5; subst. rewrite <- H1.
            unfold container; subst. auto.
          * inversion H3. subst.
            unfold indicesOfState, stateContainer in H10.
            simpl in H10.
            unfold container; simpl. intros.
            generalize (in_map
                          (fun e : Ix (S (lV G)) * list nat =>
                            iXToNat G (fst e)) (fst s'') a H1).
            intros.
            rewrite <- H10 in H12.
            inversion H5; subst.
            unfold container in H14.
            simpl in H14.
            apply in_map_iff in H12.
            destruct H12 as [x [H12 H12']].
            rewrite <- H12. apply H14. auto.
         * inversion H3; subst.
            unfold outputContainer in H11. simpl in H11.
            unfold output. rewrite <- H11.
            clear H8. inversion H5; subst.
            unfold output in H11. auto.
        }
        { rewrite H. simpl. omega. }
        { simpl; omega. }
        clear H8.
        exists s'''.
        split.
        * eapply rt_trans. apply H6.
          apply queueBigStep_n in H7. auto.
        * replace (lV G) with (S (lV (LiftGraph n G))).
          replace (AllMIS G) with
            (mkCandidateSets (LiftGraph (S (lV (LiftGraph n G))) G)
              (AllMIS (LiftGraph n G))).
          auto. simpl.
          unfold AllMIS, mkSetsAllMIS.
          replace (lV G) with (S (lV (LiftGraph n G))). simpl.
          replace (LiftGraph (S n) G) with G; auto.
          rewrite <- H. rewrite fix_LiftGraph. auto.
  Qed.

  Lemma queueMIS_step_perm_AllMIS :
    forall n G, (lV G = n) -> lV G <> 0 -> 
      exists s', queueBigStep G (startState G) s' /\  (fst s' = nil) /\ Permutation (snd s') (AllMIS G).
  Proof.
    intros. generalize (@queueMIS_EQ_AllMIS n G H H0); intros.
    destruct H1 as [s_int [H1 H2]].
    generalize (queueStep_n_exists G s_int); intros.
    destruct H3 as [s' H3].
    assert (length (container G s_int) = length (container G s_int)) by auto.
    generalize (@stepQ_as_mkCandSets_terminal G (length (container G s_int))
                  s_int s' H3 H4); intros.
    assert (fst s' = nil /\ Permutation (snd s') (AasB G (fst s_int) ++ snd s_int)).
    apply H5.
    - inversion H2.
      intros; subst. apply H7. unfold container; auto.
    - exists s'. split. eapply rt_trans.
      apply H1. apply queueBigStep_n in H3. auto. destruct H6. 
      split. auto.
      inversion H2. unfold output in H10. rewrite H10 in H7.
      eapply Permutation_trans. eauto. unfold container in H8.
      rewrite H8. rewrite app_nil_r. apply Permutation_refl.
  Qed.

  Lemma queueMIS_perm_AllMIS : 
    forall G,
      (lV G <> 0) -> fst (queueMIS G (startState G)) = nil /\
                     Permutation (snd (queueMIS G (startState G))) (AllMIS G).
  Proof.
    intros. assert (lV G = lV G) by auto.
    generalize (@queueMIS_step_perm_AllMIS (lV G) G H0 H); intros.
    destruct H1 as [s' [H1 [H2 H3]]].
    assert (queueMIS G (startState G) = queueMIS G s').
    apply stepBigEq. auto.
    rewrite H4. clear H4.
    assert (queueMIS G s' = s').
    destruct s'. simpl in H2. rewrite H2.
    apply QP_nil. rewrite H4.
    split; auto.
  Qed.

  Lemma stackMIS_perm_AllMIS :
    forall G,
      (lV G <> 0) -> Permutation (snd (stackMIS G (startState G))) (AllMIS G).
  Proof.
    intros.
    apply queueMIS_perm_AllMIS in H.
    destruct H as [H H0].
    eapply Permutation_trans; [|eauto].
    unfold startState.
    generalize (Simulation). intros.
    unfold QueueProg, StackProg in H1.
    unfold stackMIS, queueMIS.
    eapply H1.
    * constructor.
      - unfold reflexive. apply Permutation_refl.
      - unfold transitive. apply Permutation_trans.
      - unfold symmetric. apply Permutation_sym.
    * intros. unfold Accum.
      case_eq (Nat.eqb (iXToNat G (@fst (Ix (S (lV G))) (list nat) a1)) (lV G));
      case_eq (Nat.eqb (iXToNat G (@fst (Ix (S (lV G))) (list nat) a2)) (lV G));
      intros; auto. constructor.
    * intros. unfold Accum.
      case_eq (Nat.eqb (iXToNat G (@fst (Ix (S (lV G))) (list nat) a)) (lV G)); intros.
      apply perm_skip; auto. auto.
  Qed.


  Section stackMIS_props.

  Lemma stackMIS_complete : 
    forall G l, (lV G <> 0) -> MaximalIndSet_lGraph G l ->
      exists l', lex_order.list_eq l' l /\ In l' (snd (stackMIS G (startState G))).
  Proof.
    intros.
    generalize (stackMIS_perm_AllMIS _ H).
    generalize (AllMIS_complete _ _ H0).
    intros. destruct H1 as [l' [H1 H3]]. exists l'.
    split; auto.
    eapply Permutation_in;[|eauto].
    apply Permutation_sym. auto.
  Qed.

  Lemma stackMIS_sound : 
    forall G l, (lV G <> 0) -> In l (snd (stackMIS G (startState G))) -> MaximalIndSet_lGraph G l.
  Proof.
    intros.
    generalize (stackMIS_perm_AllMIS _ H).
    generalize (AllMIS_correct G l). intros.
    apply H1.
    eapply Permutation_in;[|eauto].
    auto.
  Qed.

  Lemma Perm_preserves_list_eq_in : 
    forall l1 l2, Permutation l1 l2 -> (forall x, list_eq_in x l1 -> list_eq_in x l2 ).
  Proof.
    intros l1 l2 H.
    induction H.
    + auto.
    + intros. inversion H0; subst. left. auto.
      right. auto.
    + intros. inversion H; subst. right; left; auto.
      inversion H2; subst. left; auto.
      do 2 right; auto.
    + firstorder.
  Qed. 

  Lemma Perm_preserves_NoDuplicates' :
    forall l1 l2, Permutation l1 l2 -> NoDuplicates' l1 -> NoDuplicates' l2.
  Proof.
    intros l1 l2 H.
    induction H. intros.
    + auto.
    + intros. inversion H0; subst.
      constructor. intros H5. apply H3.
      eapply Perm_preserves_list_eq_in.
      apply Permutation_sym. eauto. auto. auto.
    + intros. inversion H; subst. clear H.
      inversion H3; subst. clear H3.
      constructor.
      - intros H5. inversion H5; subst.
        apply H2. constructor. 
        apply lex_order.list_eq_symmetric. auto.
        congruence.
      - constructor. intros H5.
        apply H2. apply list_eq_in_tail. auto. auto.
    + firstorder.
  Qed.
  
  Lemma NoDuplicates'_iff_NoDupA_equivlist :
    forall l, NoDuplicates' l <-> NoDupA (equivlistA eq) l.
  Proof.
    intros l. induction l.
    split; intros; constructor.
    split; intros; constructor; inversion H; subst.
    intros HContra. apply InA_alt in HContra.
    destruct HContra. destruct H0. apply H2.
    eapply list_eq_in_spec; eauto.
    unfold lex_order.list_eq. split;
    intros. 
    assert (InA eq x0 a). apply InA_alt.
    eexists; eauto. rewrite H0 in H5.
    apply InA_alt in H5. do 2 destruct H5.
    subst. auto. 
    assert (InA eq x0 x). apply InA_alt.
    eexists; eauto. rewrite <- H0 in H5.
    apply InA_alt in H5. do 2 destruct H5.
    subst. auto. apply IHl; auto.
    intros Hcontra. apply H2.
    apply list_eq_in_witness in Hcontra.
    destruct Hcontra. destruct H0.
    apply InA_alt. eexists; split; eauto.
    unfold equivlistA. split; intros;
    apply InA_alt in H4; do 2 destruct H4; subst.
    apply H0 in H5. apply InA_alt.
    eexists; split; eauto.
    apply H0 in H5.
    apply InA_alt.
    eexists; split; eauto.
    apply IHl. auto.
  Qed.

  Lemma stackMIS_unique : 
    forall G, (lV G <> 0) -> NoDuplicates' (snd (stackMIS G (startState G))).
  Proof.
    intros.
    generalize (stackMIS_perm_AllMIS _ H).
    generalize (AllMIS_unique G). intros.
    eapply Perm_preserves_NoDuplicates'.
    apply Permutation_sym. eauto. auto.
  Qed.

  End stackMIS_props.
End noDepRefine.