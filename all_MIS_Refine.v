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

  Ltac destr :=
    match goal with
    | H : context[exists _, _]  |- _ => destruct H
    |H : _ /\ _  |- _=> destruct H
    |H : _ /\ _ /\ _  |- _=> destruct H
    |H : _ /\ _ /\ _ /\ _  |- _=> destruct H
    |H : _ /\ _ /\ _ /\ _ /\ _ |- _=> destruct H
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

  Hint Constructors queueStep_n.
  Hint Constructors queueStep_n_simpl.
  Hint Constructors queueStep_n_simpl'.
  (*
      To work around this, we prove the following two lemmas
      regarding the base cases that can appear in induction
      on queueStep_n. These 'shortcut' any of the problematic
      chains mentioned above
  *)

Ltac guess v H :=
  repeat match type of H with
           | forall x : ?T, _ =>
             match type of T with
               | Prop =>
                 (let H' := fresh "H'" in
                   assert (H' : T); [
                     solve [ eauto 6 ]
                     | specialize (H H'); clear H' ])
                 || fail 1
               | _ =>
                 specialize (H v)
                 || let x := fresh "x" in
                   evar (x : T);
                   let x' := eval unfold x in x in
                     clear x; specialize (H x')
             end
         end.

(** Version of [guess] that leaves the original [H] intact *)

  Lemma queueStep_n_0 :
    forall l1 l2 n, queueStep_n n l1 l2 -> n = 0 -> l1 = l2.
  Proof.
    intros.
    induction H; si.
    apply plus_is_O in H0; si.
    guess H2 IHqueueStep_n2.
    guess H1 IHqueueStep_n1.
    si.
  Qed.
  Hint Resolve queueStep_n_0.

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
(*
  Lemma queueStep_n_lt_r :
    forall n m p1 p2 p3,
      queueStep_n (n+m) p1 p2 ->
      queueStep_n n p1 p3 ->
      queueStep_n m p3 p2.
  Proof.
    intros.
    rewrite <- queueStep_n_swap.
    dependent induction m.
    intros. replace (n+0) with n in H; try omega.
    apply (queueStep_n_uniq H0) in H. subst. constructor.
    replace (n + S m) with (S (n + m)) in H; try omega.
    inversion H; subst. assert (m = 0). omega.
    assert (n = 0). omega. subst. constructor.
    simpl in H. apply queueStep_n_0 in H0. subst. auto.
    auto.
    apply queueStep_n_0 in H.

 H0.
    
    
    apply queueStep_n_swap
    econstructor.
    apply (queueStep_n_uniq H) in H0. subst.
    constructor. intros.
    replace (n + S m) with (S (n + m)) in H; try omega.
    apply queueStep_n_swap in H. inversion H.
    assert (n = 0). omega. assert (m=0). omega.
    subst. econstructor. simpl in H.
    apply queueStep_n_swap in H. 
    apply queueStep_n_1 in H.
    apply queueStep_n_0 in H0. subst. auto.
    auto. auto. subst. 
 simpl in H. apply queueStep_n_0. in H0.
    subst. simpl in *. auto. auto.
    intros. eapply IHn. 
      exists p3, queueStep_n m p1 p3.
*)

  (* This guy helps clean up some obnoxious cases *)
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
    { apply QMSs_trans' with (l2:=l2); auto.  }
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

  (* This match relation should hold between
      every iteration of our queueMIS and 
      mkCandidate steps, excluding the final set of
      steps when things are moved into the accumulator
    ~~~~~~~~~~~~~~~~~~~~~~~~~~
      It holds when:
         
    ~~~~~~~~~~~~~~~~~~~~~~~~~~
 *)
  Inductive matchQandCand : nat -> list A * B -> B -> Prop :=
  | matchQCand_intro :
      forall p b v,
        AasB (fst p) = b ->
        (forall a, In a (fst p) -> iXToNat (fst a) = v) ->
        (snd p = nil) ->
        matchQandCand v p b.

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

  Lemma queueStep_n_ltV :
    forall p1 p2,
      queueStep_n (length (fst p1)) p1 p2 ->
      (forall a, In a (fst p1) -> (iXToNat (fst a)) < |V|) ->       
      snd p1 = snd p2.
  Proof.
    intros p1. destruct p1.
    generalize dependent l0.
    simpl. induction l.
    intros. simpl in *.
    apply queueStep_n_0 in H; auto.
    inversion H; subst. auto.
    intros. simpl in H.
    rewrite <- queueStep_n_swap in H.
    assert (iXToNat (fst a) < |V|). apply H0.
    left. auto.
    assert (iXToNat (fst a) =? |V| = false).
    apply Nat.eqb_neq. omega. 
    inversion H; subst. inversion H4; subst.
    simpl. unfold Accum. inversion H5. subst.    
  Admitted.

  Lemma stepQ_as_mkCandSets :
    forall n (p1 p2 : list A * B),
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
        apply queueStep_n_ltV.
        auto. unfold AasB in H1. rewrite map_length in H1.
        rewrite H1. auto. intros.
        apply H6 in H5. subst. auto.
      }
        assert (exists ln lm,
                length ln = n /\ length lm = m /\ ln++lm = (fst p1)).
      { unfold AasB in H1. rewrite map_length in H1.
        apply list_sep in H1. auto. }
      destruct H5 as [nl [ml [H8 [H9 ] ] ] ].
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
      rewrite H11.
      unfold AasB. rewrite map_app. fold AasB.
      unfold AasB in H5, H20. rewrite H5, H20.
      auto. intros. rewrite H11 in H9.
      apply in_app_or in H9. destruct H9.
      apply H21. auto. apply H7. auto.
      auto. 
      unfold AasB. rewrite map_app.
      rewrite mkCandidateSets_app. auto.
      simpl. omega.
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

    Require Import Permutation.
    Check Permutation.
  Lemma stepQ_as_mkCandSets_terminal :
    forall n (p1 p2 : list A * B),
      queueStep_n n p1 p2 -> 
      length (fst p1) = n ->
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
      simpl snd in *.
      replace (length (p::l1)) with (1 + length l1) in H1.
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

  Lemma queueMIS_EQ_PrintMIS : snd (queueMIS ((Ox, nil)::nil, nil)) = PrintMIS G.
  Proof.
    (* it's gonna be a wild ride in here *)
  Admitted.

  Definition stackMIS :=
    IterStackWithAccum A B R R_wf Accum stepCandSet stepCandSet_desc.

End RefineMIS.





