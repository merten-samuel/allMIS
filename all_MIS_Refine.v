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
Definition stepCandSet' (mis : nat * list nat) : list (nat * list nat) :=
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
          then  ((S graphSize), (graphSize :: (rmvNeighbors graphSize G_s cand)))::
                ((S graphSize), cand)::
                nil
          else ((S graphSize), cand)::nil
           else ((S graphSize), cand)::nil
    end.

Lemma stepCand_spec_range :
    forall n l,
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
    

Program Fixpoint pMap
  (T1 T2 : Type) (P : T1 -> Prop) (f : forall t, P t -> T2)
  (l : list T1) (pf : forall t, In t l -> P t) : list T2 :=
match l with
| nil => nil
| a::l' =>  (f a (pf a _))::(@pMap T1 T2 P f l' _)
end.
Next Obligation.
  left; auto.
Defined.
Next Obligation.
  apply pf. right. auto.
Defined.

Program Definition stepCandSet : A -> list A :=
  fun p =>
    let (nX, l) := p in
      (@pMap (nat * list nat) ((iN (S|V|)) * list nat)
              (fun t => (fst t < S|V|)) _
             (stepCandSet' ((iXToNat nX), l))
             _).
Next Obligation.
  constructor. unfold iN. simpl in H. exact (Index.mk H).
  exact l0.
Defined.
Next Obligation.
  eapply (@stepCand_spec_range (iXToNat nX) l).
  case_eq nX; intros; subst. simpl. auto.
  eapply H.
Defined.

Lemma unwrapStepCandSet :
  forall ix1 ix2 l1 l2,
    In (ix2, l2) (stepCandSet (ix1, l1)) ->
      In (iXToNat ix2, l2) (stepCandSet' (iXToNat ix1, l1)).
Proof.

Admitted.
          
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
    apply unwrapStepCandSet. apply H.
    apply H1 in H2. subst. simpl. omega.
Qed.

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
  | QMS_step : forall l1 l2, queueStep l1 l2 -> queueStep_n 1 l1 l2
  | QMS_trans : forall n l1 l2 l3,
                  queueStep_n n l1 l2 ->
                  queueStep l2 l3 -> queueStep_n (S n) l1 l3.

  Lemma stepEq :
    forall p1 p2, queueStep p1 p2 -> queueMIS p1 = queueMIS p2.
  Proof.

  Admitted.

  Lemma stepNEq :
    forall n p1 p2, queueStep_n n p1 p2 -> queueMIS p1 = queueMIS p2.
  Proof.

  Admitted.


  Lemma queueMIS_EQ_PrintMIS : snd (queueMIS ((Ox, nil)::nil, nil)) = PrintMIS G.
  Proof.
    (* it's gonna be a wild ride in here *)
  Admitted.

End RefineMIS.

(*
Extraction queueMIS.
  Extraction

  Lemma queueMIS_EQ_PrintMIS : snd (queueMIS ((0, nil)::nil, nil)) = PrintMIS G.
  Proof.
    (* it's gonna be a wild ride in here *)
  Admitted.

 Definition stackMIS :=
    IterStackWithAccum A B R R_wf Accum stepCandSet stepCandSet_desc.
*)


