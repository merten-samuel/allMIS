Require Import List.
Require Import Arith.
Require Import Omega.

Require Import index.
Require Import ProofIrrelevance.
Require Import Coq.Program.Equality.

(* 
The definition of a ListGraph, whose edges are contained in a list
*) 
Record lGraph :=
  mkListGraph {
    lV : nat;
    lE : list ((Ix lV) * (Ix lV));
    lIrref : forall x, ~ In (x,x) lE;
    lSymm : forall x y, In (x,y) lE <-> In (y,x) lE
  }.


(*
~~~~~~~~~~~~~~~~~~~~~~~~~
The construction of an empty lGraph
~~~~~~~~~~~~~~~~~~~~~~~~~
*)
Theorem nil_lGraph_Irref : forall (x : Ix 0), ~ In (x, x) nil.
Proof.
  intros x H0. inversion H0.
Qed.

Theorem nil_lGraph_Symm : forall (x y: Ix 0), In (x,y) nil <-> In (y,x) nil.
Proof.
  split; intros; inversion H.
Qed.   

Definition nil_lGraph : lGraph :=
  mkListGraph 0 nil nil_lGraph_Irref nil_lGraph_Symm.

(* Decidability thm for pairs of indexed nats *)
Theorem ixPair_dec : forall (I : nat) (x y : (Ix I)*(Ix I)), {x = y} + {x <> y}.
Proof.
  intros.
  destruct x as [x1 x2].
  destruct y as [y1 y2].
  destruct (eq_Ix_eq x1 y1); destruct (eq_Ix_eq x2 y2); subst;
  [left; reflexivity |  |  | ]; right; intros H0; inversion H0; contradiction.
Qed.


(* Decidability thm for lists of pairs of indexed nats *)
Theorem ixList_dec : forall (I : nat) (x y : (Ix I)) (L : list ((Ix I)*(Ix I))),
  {In (x,y) L} + {~In (x,y) L}.
Proof.
  intros. apply in_dec. apply ixPair_dec.
Qed.

(*
~~~~~~~~~~~~~~~~~~~~~~~~~
Construction of a function for transforming an lGraph to a bGraph
~~~~~~~~~~~~~~~~~~~~~~~~~
*)
(* A function for transforming lists of Ix pairs to a boolean function *)
Definition list_to_func (x : nat) : list ((Ix x)*(Ix x)) -> ((Ix x) -> (Ix x) -> bool) :=
  fun (L : list ((Ix x)*(Ix x))) => fun (a b : Ix x) => if ixList_dec x a b L then true else false.

(* Preservation of the above function *)
Theorem list_to_func_preservation : forall x l a b,
  In (a,b) l <-> (list_to_func x l) a b = true.
Proof.
intros; split; intros; unfold list_to_func in *; destruct ixList_dec;
[reflexivity | contradiction | assumption | inversion H ].
Qed.

(* Irreflexivity holds unfer the function's application *)
Theorem list_to_func_irref : forall x l a, ~ In (a,a) l <-> (list_to_func x l) a a = false.
intros; split;intros; unfold list_to_func in *; destruct ixList_dec;
[contradiction | reflexivity | inversion H| assumption].
Qed.

(* Symmetry holds under the function's application *)
Theorem list_to_func_symm : forall x l a b,
  (In (a,b) l <-> In (b,a) l) <-> (list_to_func x l) a b = (list_to_func x l)b a.
Proof.
  intros; split; intros; unfold list_to_func in *; do 2 destruct ixList_dec;
  try reflexivity; try apply H in i; try contradiction;
  split; intros; try assumption; try inversion H; try contradiction.
Qed.

(* 
~~~~~~~~~~~~~~~~~~~~~~~~~
Construction of induction via induced subgraphs of an lGraph.
~~~~~~~~~~~~~~~~~~~~~~~~~
*)


(* a function for lifting Ix elements to a new index
     - returns none if the element cannot be indexed (element > new index) 
*)
Definition oLift_Ix {x : nat} (a : Ix x) (y : nat) : option (Ix y) :=
  match a with @Index.mk _ a' _ =>
    match lt_dec a' y with
    | left H => Some (@Index.mk y a' H)  
    | right H => None
    end
  end.    

(* 
  A minimal case for the lift function
*)
Theorem oLift_Ix_min : forall {x : nat} (a : Ix x), oLift_Ix a 0 = None.
Proof.
  intros.
  unfold oLift_Ix. destruct a.
  destruct lt_dec. inversion l.
  reflexivity.
Qed.

(* 
  A specification for oLift:
    When exactly does oLift produce some rather than none
*)
Theorem oLift_Ix_spec :
  forall (x y a : nat) (H0 : a < x) (H1  : a < y ),
    oLift_Ix (@Index.mk x a H0) y = Some (@Index.mk y a H1).
Proof.
  intros. unfold oLift_Ix. destruct lt_dec. assert (H1 = l) as -> by apply proof_irrelevance.
  subst. reflexivity. contradiction.
Qed.

(* 
  A preservation for oLift:
    What can be said about the object produced by olift?
*)
Theorem oLift_Ix_preservation :
  forall (x a : nat) (H0 : a < x) (y b : nat) (H1 : b < y),
    oLift_Ix (@Index.mk x a H0) y = Some (@Index.mk y b H1) -> a=b.
Proof.
  intros.
  unfold oLift_Ix in H. destruct lt_dec in H; inversion H. reflexivity.
Qed.

(*
  Lifting an element to its current index is a fixpoint 
*) 
Theorem fix_oLift_Ix : forall (x : nat) (a : Ix x), oLift_Ix a x = Some a.
Proof.
  intros. unfold oLift_Ix. destruct a. destruct lt_dec. assert (pf = l) as -> by apply proof_irrelevance.
  reflexivity. contradiction.
Qed.

Theorem rec_oLift_Ix : forall (x : nat) (a : Ix x), exists a' : (Ix (S x)), oLift_Ix a (S x) = Some a'.
Proof.
  intros. destruct a. assert (i < S x) as pf'. omega. exists (Index.mk pf'). simpl. destruct lt_dec.
  f_equal. apply f_equal. apply proof_irrelevance. contradiction.
Qed.

(*
  oLift provided over pairs of indexed numbers
*)
Definition oLift_pairIx {x : nat} (a : (Ix x)*(Ix x)) (y : nat) : option ((Ix y)*(Ix y)) :=
  match a with (a1, a2) =>
    match (oLift_Ix a1 y), (oLift_Ix a2 y) with
    | Some a1', Some a2' => Some (a1',a2')
    | _, _ => None
    end
  end.

(*
 A minimal construction for oLift_pairs
*)
Theorem oLift_pairIx_min : forall {x : nat} (a : (Ix x)*(Ix x)), oLift_pairIx a 0 = None.
Proof.
  intros. destruct a as [a1 a2].
  unfold oLift_pairIx.
  rewrite -> oLift_Ix_min. reflexivity.
Qed.

(*
  Specification thm for oLift_pair
*)
Theorem oLift_pair_spec :
  forall (x y a1 a2: nat) (H00 : a1 < x) (H01 : a2 < x) (H10 : a1 < y) (H11 : a2 < y),
    (@oLift_pairIx x (@Index.mk x a1 H00 ,@Index.mk x a2 H01) y) = Some ((@Index.mk y a1 H10), (@Index.mk y a2 H11)).
Proof.
  intros. unfold oLift_pairIx. do 2 try(unfold oLift_Ix; destruct lt_dec); try contradiction.
  { assert(l = H10) as -> by apply proof_irrelevance.
    assert(l0 = H11) as -> by apply proof_irrelevance. reflexivity.
  }
Qed.

(*
  Preservation thm for oLift_pair
*)
Theorem oLift_pairIx_preservation :
  forall (x a1 a2 : nat) (H00 : a1 < x) (H01 : a2 < x)
         (y b1 b2 : nat) (H10 : b1 < y) (H11 : b2 < y),
    oLift_pairIx ((@Index.mk x a1 H00), (@Index.mk x a2 H01)) y = Some ((@Index.mk y b1 H10), (@Index.mk y b2 H11))
      -> a1=b1 /\ a2 = b2.
Proof.
  intros. unfold oLift_pairIx in H. do 2 unfold oLift_Ix in H.
  do 2 try (destruct lt_dec); inversion H. subst. split; reflexivity.
Qed.

(*
  Fixpoint for oLift_pair
*)
Theorem fix_oLift_pairIx : forall (x : nat) (a b : Ix x), oLift_pairIx (a,b) x = Some (a, b).
Proof.
  intros. unfold oLift_pairIx. do 2 rewrite -> fix_oLift_Ix. reflexivity.
Qed.

Theorem rec_oLift_pairIX : forall (x : nat) (a b : Ix x), exists a' b', oLift_pairIx (a,b) (S x) = Some (a', b').
Proof.
  intros. unfold oLift_pairIx.
  assert (exists a', oLift_Ix a (S x) = Some a'). apply rec_oLift_Ix.
  assert (exists b', oLift_Ix b (S x) = Some b'). apply rec_oLift_Ix.
  destruct H. destruct H0. exists x0. exists x1.
  destruct (@oLift_Ix x). destruct (@oLift_Ix x). f_equal. inversion H.
  inversion H0. subst. reflexivity. inversion H0. inversion H.
Qed.

(*
  A function for raising/lowering the index of 
  a list of pairs of indexed by nats (like our edge lists in an lGraph) 
*)
Fixpoint reduceLEdges {x : nat} (L : list ((Ix x)*(Ix x))) (y : nat) : list ((Ix y)*(Ix y)) :=
  match L with
  | nil => nil
  | l::L' =>
    match oLift_pairIx l y with
    | Some l' => l' :: reduceLEdges L' y
    | None => reduceLEdges L' y
    end
  end.

(* 
  A minimal instance of LEdges
*)
Theorem reduceLEdges_min :
  forall {x : nat} (L : list ((Ix x)*(Ix x))), reduceLEdges L 0 = nil.
Proof.
  intros. induction L. simpl. reflexivity.
  simpl. rewrite -> oLift_pairIx_min. apply IHL.
Qed.

(* 
Specification thm for reduceLEdges
*)
Theorem reduceLEdges_spec :
  forall x y a1 a2 L
         (H00 : a1 < x) (H01 : a2 < x)
         (H10 : a1 < y)(H11 : a2 < y),
    In ((@Index.mk x a1 H00),(@Index.mk x a2 H01)) L
      -> In ((@Index.mk y a1 H10), (@Index.mk y a2 H11)) (@reduceLEdges x L y).
Proof.
  intros. induction L. inversion H.
  simpl In in H. destruct H as [H | H].
  { subst. unfold reduceLEdges. rewrite -> (oLift_pair_spec x y a1 a2 _ _ H10 H11).
    simpl. left. reflexivity. 
  }
  { apply IHL in H. unfold reduceLEdges. destruct (@oLift_pairIx x); fold (@reduceLEdges x);
    simpl In; [right | ]; assumption.
  }
Qed.

(*
Preservation thm for reduceLEdges
*)
Theorem reduceLEdges_preservation :
  forall x y L b1 b2 (H11 : b1 < y) (H12 : b2 < y),
    In ((@Index.mk y b1 H11),(@Index.mk y b2 H12)) (@reduceLEdges x L y) ->
     exists (H21 : b1 < x) (H22 : b2 < x), In ((@Index.mk x b1 H21),(@Index.mk x b2 H22)) L.
Proof.
  intros. induction L. inversion H.
  unfold reduceLEdges in H. destruct a as (a1, a2).
  remember a1. remember a2.
  remember (@oLift_pairIx x (i, i0) y) in H.
  destruct o; fold (@reduceLEdges x) in H; simpl In in H.
  { destruct H as [H | H].
    { rewrite -> H  in Heqo. symmetry in Heqo. destruct i. destruct i0.
      apply oLift_pairIx_preservation in Heqo. destruct Heqo as [Heq0 Heq1]. subst.
      exists pf. exists pf0. simpl. left. reflexivity.
    }
    { apply IHL in H. destruct H as [h0 [h1 H]]. exists h0. exists h1. simpl. right. apply H.
    }
  }
  { apply IHL in H. destruct H as [h0 [h1 H]]. exists h0. exists h1. simpl. right. apply H. }
Qed.

(* 
  Irreflexivity is preserved by reduceLEdges
*)
Theorem reduceLEdges_irref :
  forall (x : nat) (L : list ((Ix x)*(Ix x))),
    (forall a, ~ In (a,a) L) ->
      forall y, (forall a, ~ In (a,a) (reduceLEdges L y)).
Proof.
  intros. intros H0.
  remember a. destruct i. apply reduceLEdges_preservation in H0. destruct H0 as [h0 [h1 h2]].
  assert (eq_Ix (Index.mk h0) (Index.mk h1) = true). simpl.
  destruct eq_nat_dec; [ | apply False_rec; apply n]; reflexivity.
  destruct (eq_Ix_eq(Index.mk h0) (Index.mk h1)).
    { rewrite -> e in h2. apply H in h2. inversion h2. }
    {inversion H0. }
Qed.

(* 
  Symmetry is preserved by reduceLEdges
*)
    
Theorem reduceLEdges_symm : 
  forall (x : nat) (L : list ((Ix x)*(Ix x))),
    (forall a b, (In (a, b) L <-> In (b,a) L)) ->
      forall y, (forall a b, (In (a, b) (reduceLEdges L y) <-> (In (b,a) (reduceLEdges L y)))).
Proof.
  split; intros; remember a; remember b; destruct i; destruct i0; apply reduceLEdges_preservation in H0;
  destruct H0 as [h0 [h1 h2]]; apply H in h2.
  {
    apply (reduceLEdges_spec x y i0 i L h1 h0 pf0 pf). assumption.
  }
  {
   apply (reduceLEdges_spec x y i i0 L h1 h0 pf pf0). assumption. 
  }
Qed.

(*
  Reducing a list of edges by its current index is a fixpoint
*)
Theorem fix_reduceLEdges: forall  (x : nat) (L : list ((Ix x)*(Ix x))),
  reduceLEdges L x = L.
Proof.
  intros. induction L.
  {
    reflexivity. 
  }
  {
    simpl. destruct a as [a1 a2]. rewrite -> fix_oLift_pairIx.
    rewrite -> IHL. reflexivity.
  }
Qed.


(*
  Toss everything together to make a function that raises and lowers
  the number of vertices in a graph, allowing for induced subgraphs
*) 
Definition LiftGraph (V' : nat) : lGraph -> lGraph :=
  fun G : lGraph =>
    mkListGraph
      V'
      (@reduceLEdges (lV G) (lE G) V')
      (reduceLEdges_irref (lV G) (lE G) (lIrref G) V')
      (reduceLEdges_symm (lV G) (lE G) (lSymm G) V').

(*
  A lemma to help prove our fixpoint thm scheme later
*)
Theorem fix_LiftGraph_lemma : forall (G1 G2 : lGraph) (H0 : lV G1 = lV G2) (H1 : lE G1 ~= lE G2),
  G1 = G2.
Proof.
  intros. destruct G1. destruct G2. simpl in *. subst. apply JMeq_eq in H1.  subst. 
  f_equal; apply proof_irrelevance.
Qed.

(*
  A minimal result of LiftGraph
*)
Theorem least_LiftGraph : forall (G : lGraph), LiftGraph 0 G = nil_lGraph.
Proof.
  intros. apply fix_LiftGraph_lemma. 
  simpl. reflexivity.
  simpl. rewrite -> reduceLEdges_min.
  reflexivity.
Qed.

(*
  Lifting a graph to its current number of vertices is a fixpoint
*)
Theorem fix_LiftGraph : forall (G : lGraph),
  LiftGraph (lV G) G = G.
Proof.
  intros. apply fix_LiftGraph_lemma;  simpl. reflexivity.
  assert ( reduceLEdges (lE G) (lV G) = lE G).
  apply fix_reduceLEdges. rewrite -> H.
  apply JMeq_refl.
Qed.

(*
  Under certain conditions, we need only consider the
  outermost application of LiftGraph
*)
Theorem LiftGraph_red :
  forall x y G, x < y -> LiftGraph x (LiftGraph y G) = LiftGraph x G.
Proof.
  intros. apply fix_LiftGraph_lemma. simpl. reflexivity. simpl.
  assert ( reduceLEdges (reduceLEdges (lE G) y) x = reduceLEdges (lE G) x).
  induction (lE G). simpl. reflexivity.
  destruct a as (a1, a2). destruct a1 as [a1  H1]. destruct a2 as [a2 H2].
  simpl. repeat (destruct lt_dec; simpl); rewrite -> IHl; try reflexivity; try omega.
  rewrite -> H0. apply JMeq_refl.
Qed.

(* A lemma for our induction scheme below *)
Theorem InducedGraph_lemma :
  forall (P : lGraph -> Prop),
    P nil_lGraph -> (forall G x, P (LiftGraph x G) -> P (LiftGraph (S x) G)) ->
     (forall G x, P (LiftGraph x G)).
Proof.
  intros. induction x. rewrite -> least_LiftGraph. assumption.
  apply H0. assumption.
Qed.

(*
  An induction scheme via induced subgraphs
  - IF some property holds for the empty graph
  AND
  - The property holding for the induced graph with x vertices implies it holds
    for the graph with S x vertices, then it holds for every graph.
*)
Theorem InducedGraph_ind :
  forall (P : lGraph -> Prop),
    P nil_lGraph ->
    (forall G x, P (LiftGraph x G) -> P (LiftGraph (S x) G))
      -> forall G, P G.
Proof.
  intros. rewrite <- fix_LiftGraph. apply InducedGraph_lemma; assumption.
Qed.

(*
~~~~~~~~~~~~~~~~~~~~~~~~~
Describe some functions to provide later compatibility for graphs without dependent types
~~~~~~~~~~~~~~~~~~~~~~~~~
*)

(*
  Removes the indexing from an indexed edge list
*)
Fixpoint flatten_EdgeList {x : nat} (L : list ((Ix x)*(Ix x))): list (nat*nat) := 
  match L with
  | nil => nil
  | l::L' =>
    match l with (l1, l2) =>
      match l1, l2 with
        @Index.mk _ l1' _, @Index.mk _ l2' _ => (l1', l2')::flatten_EdgeList L'
      end
    end
  end.

(* Applies the above function to an lGraph *)
Definition flatten_EdgesGraph (G : lGraph) : list (nat*nat) :=
  flatten_EdgeList (lE G).

(* Specification thm for the above *)
Theorem flatten_EdgesGraph_spec1 :
  forall G x y,
    In (x,y) (flatten_EdgesGraph G) <->
    (exists (H0 : x < (lV G)) (H1 : y < (lV G)), In ((Index.mk H0), (Index.mk H1)) (lE G)).
Proof.
  split; intros.
  { unfold flatten_EdgesGraph in H. unfold flatten_EdgeList in H. induction (lE G). inversion H.
    destruct a. destruct i. destruct i0. fold (@flatten_EdgeList (lV G)) in *. simpl In in H. destruct H as [H | H].
    { inversion H. subst. exists pf. exists pf0. simpl. left. reflexivity. }
    {
      apply IHl in H. destruct H as [h0 [h1 H]]. exists h0. exists h1. simpl In. right. assumption.
    }
  }
  {
     destruct H as [h0 [h1 H]]. unfold flatten_EdgesGraph; unfold flatten_EdgeList; induction (lE G).
     inversion H. destruct a. destruct i. destruct i0. fold (@flatten_EdgeList (lV G)) in *.
     simpl In in H. destruct H as [H | H].
     { inversion H. simpl In. left. reflexivity. }
     { apply IHl in H. simpl In. right. assumption. }
   }
Qed.

(*
  The elements extracted from an application of flatten_Edges
  are lt the  # of vertices of the graph
*)
Theorem flatten_EdgesGraph_spec2 : 
  forall G x y, In (x,y) (flatten_EdgesGraph G) -> (x < (lV G)) /\ (y < (lV G)).
Proof.
  intros. apply flatten_EdgesGraph_spec1 in H. destruct H as [h0 [h1 H]]. split; assumption.
Qed.

(*
  Flatten edges preserves irreflexivity
*)
Theorem flatten_Edges_irref : forall G x y, In (x,y) (flatten_EdgesGraph G) -> x <> y.
Proof.
  intros. apply flatten_EdgesGraph_spec1 in H. destruct H as [h0 [h1 H]].
  assert (Index.mk h0 <> Index.mk h1) as H0.
    { intros H1. rewrite -> H1 in H. apply lIrref in H. assumption. }
  intros H1. apply H0. clear H0. subst x.  assert (h0 = h1) as -> by apply proof_irrelevance.
  reflexivity.
Qed.

(*
  Flatten edges preserves symmetry
*)
Theorem flatten_Edges_symm : forall G x y, In (x,y) (flatten_EdgesGraph G) <-> In (y,x) (flatten_EdgesGraph G).
Proof.
  split; intros; apply flatten_EdgesGraph_spec1 in H; destruct H as [H0 [H1 H2]];
  apply (lSymm G) in H2; apply flatten_EdgesGraph_spec1; exists H1; exists H0; assumption.
Qed. 
