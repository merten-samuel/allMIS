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

  Definition R : A -> A -> Prop :=
    LeftProdRel (iN (S |V|)) (list nat)
                (fun n m => iXToNat n < iXToNat m <= |V|).
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
  apply LeftProdRel_wf.
  apply well_founded_lt_compat with (f := iXToNat).
  intros.
  inversion H.
  auto.
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
    omega.
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
    omega.
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
      left.
      left.
      constructor; auto.
      simpl.
      omega.
    +
      left.
      right.
      simpl.
      subst.
      f_equal.
      apply proof_irrelevance.
    +
      right.
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

Check mkCandidateSets. About LiftGraph.

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
        then (graphSize, (cons graphSize cand))::nil
      else if isMIS G_s (graphSize :: (rmvNeighbors graphSize G_s cand))
        then if LFMIS_dec G_graphSize (rmvNeighbors graphSize G_s cand) cand
          then  ((S graphSize), (graphSize :: (rmvNeighbors graphSize G_s cand)))::
                ((S graphSize), cand)::
                nil
          else ((S graphSize), cand)::nil
           else ((S graphSize), cand)::nil
    end.

Lemma stepCand_spec : forall n l,
    n < S |V| -> (forall l' m,
    In (m, l') (stepCandSet' l) -> 
    m < S |V|).
Proof.
  Admitted.

Definition stepCandSet (mis : A) : list A.
  destruct mis.
  destruct i.
  
  (* destruct (lex_order.list_in_dec (S i) ). *)
  (* apply stepCand_spec1 in pf.   *)
          
Lemma stepCandSet_desc : forall a a' : A, In a' (stepCandSet a) -> R a' a.
  Proof.
  Admitted.


  Definition queueMIS :=
    IterQueueWithAccum A B R Eqa R_wf R_trans Eqa_eq R_total R_irref
      Accum stepCandSet stepCandSet_desc. 

End RefineMIS.

Extraction queueMIS.
  Extraction

  Lemma queueMIS_EQ_PrintMIS : snd (queueMIS ((0, nil)::nil, nil)) = PrintMIS G.
  Proof.
    (* it's gonna be a wild ride in here *)
  Admitted.

 Definition stackMIS :=
    IterStackWithAccum A B R R_wf Accum stepCandSet stepCandSet_desc.

End RefineMIS.



