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
<<<<<<< HEAD


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

(*
Definition stepCandSet' (mis : nat * list nat) : list (nat * list nat) :=
=======
  Definition stepCandSet' (mis : nat * list nat) :
   list (nat * list nat) :=
>>>>>>> d68d13bb73cbf2e3598da3265a3410d516ab0a65
    let (graphSize, cand) := mis in
    let G_graphSize := LiftGraph graphSize G in    
    let G_s := (LiftGraph (S graphSize) G) in
    match (Nat.eqb graphSize |V|) with
    (* if (Nat.eqb graphSizeN |V|) *) (* Is this an MIS of the whole graph G? Then drop it*)
    |true => nil 
    (* then nil *)
    |false => 
     if independent_lGraph G_s (graphSize::cand)
     then (S graphSize, (cons graphSize cand))::nil
     else if isMIS G_s (graphSize :: (rmvNeighbors graphSize G_s cand))
          then if LFMIS_dec G_graphSize (rmvNeighbors graphSize G_s cand) cand
               then  ((S graphSize),
               (graphSize :: (rmvNeighbors graphSize G_s cand)))::
                                         ((S graphSize), cand)::nil
               else ((S graphSize), cand)::nil
          else ((S graphSize), cand)::nil
    end.

  Lemma stepCand_spec_range :
    forall n l,
<<<<<<< HEAD
    n < S |V| -> (forall m l',
    In (m, l') (stepCandSet' (n,l)) -> 
    m < S |V|).
Proof.
  intros. simpl in H0.
  case_eq (Nat.eqb n |V|); intros; rewrite H1 in H0; simpl.
  inversion H0.
  destruct graphs_nondep.inEdgeDec.
  destruct isMIS. destruct LFMIS_dec.
  apply beq_nat_false in H1.
  inversion H0. inversion H2. omega.
  inversion H2. inversion H3. omega. inversion H3.
  apply beq_nat_false in H1. inversion H0.
  inversion H2; omega. inversion H2.
  apply beq_nat_false in H1. inversion H0. inversion H2.
  omega. inversion H2. apply beq_nat_false in H1.
  destruct (graphs_nondep.vertexConnected).
  destruct isMIS. destruct LFMIS_dec.
  inversion H0. inversion H2.
  omega. inversion H2. inversion H3. omega.
  inversion H3. inversion H0. inversion H2.
  omega. inversion H2. inversion H0. inversion H2.
  omega. inversion H2. destruct independent_lGraph.
  inversion H0. inversion H2. omega. inversion H2.
  destruct isMIS. destruct LFMIS_dec.
  inversion H0. inversion H2. omega. inversion H2.
  inversion H3. omega. inversion H3. inversion H0.
  inversion H2. omega. inversion H2. inversion H0.
  inversion H2. omega. inversion H2.
Qed.

Lemma stepCand_spec_range' :
    forall p,
    (fst p) < S |V| -> (forall m l',
    In (m, l') (stepCandSet' p) -> 
    m < S |V|).
Proof. intros p. destruct p. apply stepCand_spec_range. Qed.

Lemma stepCand_spec_desc :
  forall n l m l',
    In (m, l') (stepCandSet' (n, l)) -> m = S n.
Proof.
  intros n l m l' H0. simpl in H0.
  case_eq (Nat.eqb n |V|); intros H1; rewrite H1 in H0; simpl.
  inversion H0.
  destruct graphs_nondep.inEdgeDec.
  destruct isMIS. destruct LFMIS_dec.
  apply beq_nat_false in H1.
  inversion H0. inversion H. omega.
  inversion H. inversion H2. omega. inversion H2.
  apply beq_nat_false in H1. inversion H0.
  inversion H; omega. inversion H.
  apply beq_nat_false in H1. inversion H0. inversion H.
  omega. inversion H. apply beq_nat_false in H1.
  destruct (graphs_nondep.vertexConnected).
  destruct isMIS. destruct LFMIS_dec.
  inversion H0. inversion H.
  omega. inversion H. inversion H2. omega.
  inversion H2. inversion H0. inversion H.
  omega. inversion H. inversion H0. inversion H.
  omega. inversion H. destruct independent_lGraph.
  inversion H0. inversion H. omega. inversion H.
  destruct isMIS. destruct LFMIS_dec.
  inversion H0. inversion H. omega. inversion H.
  inversion H2. omega. inversion H2. inversion H0.
  inversion H. omega. inversion H. inversion H0.
  inversion H. omega. inversion H.
Qed.
    

Lemma P_tl :
  forall (A : Type)
         (a : A) (l1 l2 : list A)
         (P : A -> Prop),
  a::l1 = l2 -> (forall a', In a' l2 -> P a') ->
  (forall a', In a' l1 -> P a').
Proof. intros. apply H0. subst. right; auto. Defined.

SearchAbout In cons.

Lemma P_hd :
  forall (A : Type)
         (a : A) (l1 l2 : list A),
  a::l1 = l2 -> In a l2.
Proof. intros. subst. left. auto. Defined.

Fixpoint pMap
  (T1 T2 : Type) (P : T1 -> Prop) (f : forall t, P t -> T2)
  (l : list T1) (pf : forall t, In t l -> P t) : list T2 :=
match l as k return (k = l -> list T2)with
| nil => fun _ => nil
| a::l' => fun eq_pf => (f a (pf a (@P_hd _ a l' l eq_pf)))::
                        (@pMap T1 T2 P f l' (@P_tl _ a l' l _ eq_pf pf))
end (eq_refl l).
Print A.
Lemma stripiN : forall (x : iN (S|V|)), iXToNat x < S|V|.
Proof. intros. destruct x; auto. Qed.

Lemma stripiNList : forall (l : list (iN (S|V|))) a, In a l -> iXToNat a < S|V|.
Proof. intros. destruct a. simpl. auto. Qed.

Definition liftiN : forall n, n < S|V| -> iN (S|V|).
Proof. intros. apply (Index.mk H). Qed.

(* 
(A ->
 forall (nX : iN (S |V|)) (l : list nat) (t : nat * list nat),
 In t (stepCandSet' (iXToNat nX, l)) -> (fun t0 : nat * list nat => fst t0 < S |V|) t).
*)
Check (fun (a : A) => stepCand_spec_range).
Program Definition stepCandSet : A -> list A :=
  fun p =>
    let (nX, l) := p in
      (@pMap (nat * list nat) ((iN (S|V|)) * list nat)
              (fun t => (fst t < S|V|))
              (fun p pf => (@liftiN (fst p) pf, snd p))
              (stepCandSet' ((iXToNat nX), l))
              _).
Next Obligation.
  eapply (@stepCand_spec_range' (iXToNat nX) l).
  case_eq nX; intros; subst. simpl. auto.
  eapply H.
Defined.

Lemma unwrapStepCandSet :
  forall ix1 ix2 l1 l2,
    In (ix2, l2) (stepCandSet (ix1, l1)) ->
=======
      n < S |V| -> (forall m l',
                       In (m, l') (stepCandSet' (n,l)) -> 
                       m < S |V|).
  Proof.
    intros. simpl in H0.
    case_eq (Nat.eqb n |V|); intros; rewrite H1 in H0; simpl.
    inversion H0.
    destruct graphs_nondep.inEdgeDec.
    destruct isMIS. destruct LFMIS_dec.
    apply beq_nat_false in H1.
    inversion H0. inversion H2. omega.
    inversion H2. inversion H3. omega. inversion H3.
    apply beq_nat_false in H1. inversion H0.
    inversion H2; omega. inversion H2.
    apply beq_nat_false in H1. inversion H0. inversion H2.
    omega. inversion H2. apply beq_nat_false in H1.
    destruct (graphs_nondep.vertexConnected).
    destruct isMIS. destruct LFMIS_dec.
    inversion H0. inversion H2.
    omega. inversion H2. inversion H3. omega.
    inversion H3. inversion H0. inversion H2.
    omega. inversion H2. inversion H0. inversion H2.
    omega. inversion H2. destruct independent_lGraph.
    inversion H0. inversion H2. omega. inversion H2.
    destruct isMIS. destruct LFMIS_dec.
    inversion H0. inversion H2. omega. inversion H2.
    inversion H3. omega. inversion H3. inversion H0.
    inversion H2. omega. inversion H2. inversion H0.
    inversion H2. omega. inversion H2.
  Qed.

  Lemma stepCand_spec_desc :
    forall n l m l',
      In (m, l') (stepCandSet' (n, l)) -> m = S n.
  Proof.
    intros n l m l' H0. simpl in H0.
    case_eq (Nat.eqb n |V|); intros H1; rewrite H1 in H0; simpl.
    inversion H0.
    destruct graphs_nondep.inEdgeDec.
    destruct isMIS. destruct LFMIS_dec.
    apply beq_nat_false in H1.
    inversion H0. inversion H. omega.
    inversion H. inversion H2. omega. inversion H2.
    apply beq_nat_false in H1. inversion H0.
    inversion H; omega. inversion H.
    apply beq_nat_false in H1. inversion H0. inversion H.
    omega. inversion H. apply beq_nat_false in H1.
    destruct (graphs_nondep.vertexConnected).
    destruct isMIS. destruct LFMIS_dec.
    inversion H0. inversion H.
    omega. inversion H. inversion H2. omega.
    inversion H2. inversion H0. inversion H.
    omega. inversion H. inversion H0. inversion H.
    omega. inversion H. destruct independent_lGraph.
    inversion H0. inversion H. omega. inversion H.
    destruct isMIS. destruct LFMIS_dec.
    inversion H0. inversion H. omega. inversion H.
    inversion H2. omega. inversion H2. inversion H0.
    inversion H. omega. inversion H. inversion H0.
    inversion H. omega. inversion H.
  Qed.

  Definition pMap_o_1 := 
    fun (T1 : Type) (P : T1 -> Prop) (l : list T1)
        (pf : forall t : T1, In t l -> P t) (a : T1) 
        (l' : list T1) (Heq_l : a :: l' = l) =>
      eq_ind (a :: l')
             (fun l0 : list T1 => (forall t : T1, In t l0 -> P t) -> In a l0)
             (fun _ : forall t : T1, In t (a :: l') -> P t => or_introl eq_refl) l
             Heq_l pf.

  
  Program Fixpoint pMap
          (T1 T2 : Type) (P : T1 -> Prop) (f : forall t, P t -> T2)
          (l : list T1) (pf : forall t, In t l -> P t) : list T2 :=
    match l with
    | nil => nil
    | a::l' =>  (f a _)::(@pMap T1 T2 P f l' _)
    end.
  Next Obligation.
    apply pf.
    left.
    reflexivity.
  Defined.
  Next Obligation.
    apply pf. right. exact H.
  Defined.  

  Lemma pMap_spec : forall (T1 T2 : Type) P f l pf,
      @pMap T1 T2 P f l pf = nil ->
      l = nil.
    intros.
    induction l; auto.
    simpl.
    simpl in H.
    inversion H.
  Qed.

  Definition pMap_make : forall T1 l P a,
      (forall t : T1, In t (a :: l) -> P t) ->
      (forall t : T1, In t l -> P t).
  Proof.
    intros.
    apply X.
    right.
    exact H.
  Defined.

  Definition pMap_extract : forall T1 a l P,
      (forall t : T1, In t (a::l) -> P t)
      -> P a.
  Proof.
    intros.
    apply X.
    left.
    reflexivity.
  Defined.

  Lemma pMap_cons : forall (T1 T2 : Type) (P : T1 -> Prop) f a l 
                           (pf : forall t : T1, In t (a::l) -> P t),
      @pMap T1 T2 P f (a::l) pf = 
      f a (pMap_extract P pf) :: (@pMap T1 T2 P f l (pMap_make P pf)).
  Proof.
    intros.
    induction l.
    auto.
    auto.
  Qed.

  Definition step (l : list (nat * list nat))
             (p : forall t, In t l -> fst t < S|V|) 
    : list A :=
    @pMap (nat * list nat) A (fun t => fst t < S|V|)
          (fun t pf => (Index.mk pf,snd t) ) l
          p.

  Program Definition stepCandSet (a : A) : list A :=
    step (stepCandSet' (iXToNat (fst a), snd a)) _.
  Next Obligation.
    fold stepCandSet' in H.
    destruct i.
    simpl in *.
    apply (@stepCand_spec_range i l0) 
      with (l' := l).
    auto.
    apply H.
  Defined.

  Lemma unwrapStepCandSet' :
    forall ix1 ix2 l1 l2 pf,
      In (ix2, l2) (step (stepCandSet' (iXToNat ix1, l1)) pf) ->
>>>>>>> d68d13bb73cbf2e3598da3265a3410d516ab0a65
      In (iXToNat ix2, l2) (stepCandSet' (iXToNat ix1, l1)).
  Proof.
    intros.
    generalize dependent ((stepCandSet' (iXToNat ix1, l1))).
    intros l.
    intros pf.
    induction l.
    intros.
    simpl in H.
    inversion H.
    intros.
    unfold step in H.
    rewrite pMap_cons in H.
    simpl in H.
    destruct H.
    destruct a.
    simpl.
    inversion H;
      subst; auto.
    unfold pMap_make in H.
    destruct ix2.
    simpl. simpl in H.
    si.
  Qed.
  
  Lemma unwrapStepCandSet :
    forall ix1 l1 ix2 l2,
      In (ix2, l2) (stepCandSet (ix1,l1)) ->
      exists pf,
        In (ix2, l2) (step (stepCandSet' (iXToNat ix1, l1)) pf).
  Proof.
    intros.
    unfold stepCandSet in H.
    eauto.
  Qed.


  Lemma stepCandSet_desc : forall a a' : A, In a' (stepCandSet a) -> R a' a.
  Proof.
    intros. unfold stepCandSet in H.
    destruct a, a'. constructor.
    specialize (@stepCand_spec_range (iXToNat i) l). intros.
    specialize (@stepCand_spec_desc (iXToNat i) l). intros.
    case_eq i. intros; subst.
    specialize (H0 pf).
    case_eq i0; intros; subst.
    specialize (H0 i l0).
    specialize (H1 i l0). simpl (S (iXToNat (Index.mk pf))) in H1.
    simpl.
    constructor.
    assert (In (i, l0) (stepCandSet' (iXToNat (Index.mk pf), l))).
    simpl(iXToNat (Index.mk pf)).
    replace i with (iXToNat (Index.mk pf0)); auto.
    replace i1 with (iXToNat (Index.mk pf)); auto.
    eapply unwrapStepCandSet'.
    apply H.
    apply H1 in H2. subst. simpl. omega.
<<<<<<< HEAD
Qed.
*)

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
=======
  Qed.
>>>>>>> d68d13bb73cbf2e3598da3265a3410d516ab0a65

  Definition queueMIS :=
    IterQueueWithAccum A B R Eqa R_wf R_trans Eqa_eq R_total R_irref
                       Accum stepCandSet stepCandSet_desc. 

  Definition Ox : iN (S|V|).
    unfold iN. unfold Ix. eapply (@Index.mk _ 0 _).
    Unshelve. omega.
  Defined.

  Definition queueStep := QueueStepR _ _ Accum stepCandSet.

  Inductive queueStep_n :
    nat -> list A * B -> list A * B -> Prop :=
  | QMS_refl : forall l1 l2, queueStep_n 0 l1 l2
  | QMS_step : forall l1 l2, queueStep l1 l2 -> queueStep_n 1 l1 l2
  | QMS_trans : forall n m l1 l2 l3,
                  queueStep_n n l1 l2 ->
                  queueStep_n m l2 l3 -> queueStep_n (n + m) l1 l3.

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
    + admit.
    + admit.
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
        * admit.
        * rewrite <- H6. apply H12.
        * simpl. admit.
        * auto.
      - admit.
      - admit.
      - admit.
Admitted.

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


