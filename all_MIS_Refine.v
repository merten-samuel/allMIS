Require Import graph_basics.
Require Import MIS_basics.
Require Import all_MIS.
Require Import wf_combinators.
Require Import Wellfounded.
Require Import Relations.
Require Import List. 

Section RefineMIS.
  (** Let's set up the environment we need to apply queueMIS **)

  Variable G : lGraph.
  Notation "|V|" := (lV G).

  (* The list we iterate over is composed of ordered pairs of (N,S)
      where S is a maximal independent set of a graph of size N *)

  Notation A := (nat*(list nat))%type.

  (* The output should store MISs of the input graph (as a list of list of nats) *)
  Notation B := (list (list nat)).
  
  (* At each step of the function the head of the list is removed
      and replaced with a new list of MISs s.t. N is larger by one,
      but no larger than the vertices of G. *)
  Definition R : A -> A -> Prop :=
    LeftProdRel nat (list nat) (fun n m => m < n <= |V|).

  (* Elements are equivalent with respect to R if their
      fist projections are identical *)
  Definition Eqa (a1 a2 : A) : Prop := fst a1 = fst a2.

  Lemma R_wf : well_founded R.
  Proof.
    apply LeftProdRel_wf.
    apply PeanoNat.Nat.gt_wf.
  Qed.
  
  Lemma R_trans : forall a1 a2 a3, R a1 a2 -> R a2 a3 -> R a1 a3.
  Proof.
   
  Admitted.

  Lemma Eqa_eq : equivalence _ Eqa.
  Proof.

  Admitted.

  Lemma R_total : (forall a1 a2 : A, {R a1 a2} + {Eqa a1 a2} + {R a2 a1}).
  Proof.

  Admitted.

  Lemma R_irref : (forall a1 a2 : A, R a1 a2 -> ~ Eqa a1 a2).
  Proof.

  Admitted.
  Definition Accum (a : A) (acc : B) : B :=
    if Nat.eqb (fst a) |V| then (snd a)::acc else acc.
    

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
  Definition stepCandSet (mis : A) : list A :=
    let (graphSize, cand) := mis in
    let G_graphSize := LiftGraph graphSize G in    
    let G_s := (LiftGraph (S graphSize) G) in
      if (Nat.eqb graphSize |V|) (* Is this an MIS of the whole graph G? Then drop it*)
        then nil
      else if independent_lGraph G_s (graphSize::cand)
        then (S graphSize, (cons graphSize cand))::nil
      else if isMIS G_s (graphSize :: (rmvNeighbors graphSize G_s cand))
        then if LFMIS_dec G_graphSize (rmvNeighbors graphSize G_s cand) cand
          then  (S graphSize, (graphSize :: (rmvNeighbors graphSize G_s cand)))::
                (S graphSize, cand)::
                nil
          else (S graphSize, cand)::nil
      else (S graphSize, cand)::nil.

  Lemma stepCandSet_desc : forall a a' : A, In a' (stepCandSet a) -> R a' a.
  Proof.

  Admitted.

  Definition queueMIS :=
    IterQueueWithAccum A B R Eqa R_wf R_trans Eqa_eq R_total R_irref
      Accum stepCandSet stepCandSet_desc. 

  Lemma queueMIS_EQ_PrintMIS : snd (queueMIS ((0, nil)::nil, nil)) = PrintMIS G.
  Proof.
    (* it's gonna be a wild ride in here *)
  Admitted.

 Definition stackMIS :=
    IterStackWithAccum A B R R_wf Accum stepCandSet stepCandSet_desc.

End RefineMIS.
