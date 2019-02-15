Require Import GenGraph.
Require Import explicit_graph.
Require Import graph_basics.
Require Import graphs_nondep.
Require Import SetoidList.
Require Import Omega.
Require Import all_MIS.
Require Import all_MIS_complete.
Require Import all_MIS_unique.
Import MIS_basics.

Inductive MIS_set_lGraph (G : lGraph) (l : list (list nat)) : Prop :=
| mkMIS_setL :
    (forall x :
    list nat, In x l -> MaximalIndSet (lV G) (flatten_EdgesGraph G) x) ->
    NoDupA (equivlistA eq) l ->
    (forall x : list nat ,
        MaximalIndSet (lV G) (flatten_EdgesGraph G) x ->
        InA (equivlistA eq) x l) ->
    MIS_set_lGraph G l.



  Fixpoint enumerate (x : nat) :=
    match x with
    | O => 0::nil
    | S x' => x::(enumerate x')
    end.

  Fixpoint enumerate_acc (count : nat) (x : nat) :=
    match x with
    | O => count::nil
    | S x' => count::(enumerate_acc (S count) x')
    end.

  Lemma enumerate_complete :
    forall x y, y <= x -> In y (enumerate x).
  Proof.
    induction x. intros. simpl. left.
    omega. intros. inversion H. left. auto.
    right. apply IHx. auto.
  Qed.

  Lemma enumerate_bounded : 
    forall x y, x < y -> ~ In y (enumerate x).
  Proof.
    induction x. intros. intros Hcontra. inversion Hcontra.
    omega. inversion H0.
    intros. simpl. intros Hcontra.
    destruct Hcontra. omega. eapply IHx; [|eauto]. omega.
  Qed.

  Lemma enumerate_nodup : 
    forall x, NoDup (enumerate x).
  Proof.
    induction x. constructor. intros H.
    inversion H. constructor. simpl.
    constructor. apply enumerate_bounded. omega.
    auto.
  Qed.

  Program Definition GenGraph_of (G : lGraph) : @GenGraph nat :=
     mkGGraph _ (if Nat.eq_dec (lV G) 0 then nil else enumerate ((lV G)-1)) (nodup _ (flatten_EdgesGraph G)) _ _ _ _ _. 
  Next Obligation.
    destruct (eq_nat_dec n1 n);
    [destruct (eq_nat_dec n2 n0);
      [left; subst | right]
    | right];congruence.
  Qed.
  Next Obligation.
    rewrite nodup_In.
    intros HContra. eapply flatten_Edges_irref. eauto. auto.
  Qed.
  Next Obligation.
    rewrite nodup_In.
    apply flatten_Edges_symm.
    rewrite nodup_In in H. auto.
  Qed.
  Next Obligation.
    destruct Nat.eq_dec; auto.
    constructor.
    apply enumerate_nodup.
  Qed.
  Next Obligation.
    apply NoDup_nodup.
  Qed.
  Next Obligation.
    rewrite nodup_In in H.
    apply flatten_EdgesGraph_spec2 in H.
    destruct H.
    destruct Nat.eq_dec; auto.
    omega.
    apply enumerate_complete; auto.
    omega.
  Qed.
    
  (* have a function h that maps maximal independent sets in lGraphs to 
     maximal independent sets in GenGraphs 
     Proof that that function is injective
   *)        
  
  
  Lemma enumerate_inj : forall x y, enumerate x = enumerate y ->
                                    x = y.
  Proof.
    intros.
    destruct x.
    simpl in H.
    destruct y.
    simpl in H.
    auto.
    simpl in H.
    inversion H.
    simpl in H.
    destruct y.
    simpl in *.
    inversion H.
    simpl in *.
    inversion H.
    auto.
  Qed.

Lemma enumerate_sound' : forall x V,
    In x (enumerate V) -> x <= V.
Proof.
  induction V; intros.
  {
    simpl in H.
    destruct H; subst; intuition.
  }
  simpl in H.
  destruct H; subst; auto.
Qed.

Lemma enumerate_sound : forall x V,
    V <> 0 ->
    In x (enumerate (V -1)) -> x < V.
Proof.
  destruct V; intros.
  {
    contradiction.
  }
  {
    simpl in H0.
    assert (x < S V <-> x <= V).
    omega.
    apply H1.
    rewrite <- minus_n_O in H0.
    apply enumerate_sound'; auto.
  }
Qed.


(* If l is the set of all maximal independent sets a graph, G, of 
   type lGraph then l is the set of all maximal independent sets of 
   the projection of G to type : @GenGraph nat,  Which is a record 
   of graphs with and explicity list of vertices. 
 *)

Lemma All_MIS_preserved_lGraph_to_GenGraph :
  forall (G : lGraph) (l : list (list nat)),
    MIS_set_lGraph G l -> MIS_set_gGraph (GenGraph_of G) l.
Proof.
  intros.
  inversion H.
  constructor; auto.
  {
    intros.
    apply H0 in H3.
    assert (H10: InA (equivlistA eq) x l).
    {
      apply H2 in H3.
      auto.
    }
    constructor; auto.
    {
      constructor.
      {
        red.
        intros.
        simpl.
        destruct Nat.eq_dec; auto.
        {
          apply TrivialIndSet in H3; auto.
          subst.
          inversion H4.
        }
        inversion H3.
        inversion H5.
        red in H7.
        apply enumerate_complete.
        apply H7 in H4; auto.
        omega.
      }
      {
        red.
        intros.
        simpl.
        inversion H3.
        inversion H6.
        red in H9.
        rewrite nodup_In.
        apply H9; auto.
      }
    }
    {
      simpl.
      intros.
      pose proof H3.
      apply MaximalIndSet_eq in H3.
      inversion H3.
      apply H8 in H5.
      apply IndSet_destr in H5; auto.
      clear -H5.
      {
        apply vertexConnected_spec in H5; eauto.
        destruct H5; eauto.
        destruct H.
        exists x1.
        rewrite nodup_In.
        specialize  (flatten_EdgesGraph_spec2 _  _ _ H0).
        intuition.
        destruct (Nat.eq_dec); [omega | ].
        apply enumerate_complete; auto.
        omega.
      }
      {
        intros.
        intros Hnot.
        apply flatten_Edges_irref in Hnot; contradiction.
      }
      {
        apply flatten_Edges_symm.
      }
      {
        destruct Nat.eq_dec; [| 
        apply enumerate_sound; auto].
        {
          inversion H4.
        }
      }
    }
  }
  {
    intros.
    apply H2.
    apply MaximalIndSet_eq.
    constructor.
    {
      inversion H3.
      clear H5.
      inversion H4.
      red in H5.
      red in H6.
      constructor; auto;
      red; intros; auto.
      {
        apply H5 in H7.
        simpl in H7.
        destruct Nat.eq_dec; [contradiction | 
        apply enumerate_sound; auto].
      }
      {
        simpl in H6.
        apply (H6 _ _ H7) in H8.
        rewrite nodup_In in H8.
        auto.
      }
    }
    {
      intros.
      intros Hnot.
      inversion H3.
      inversion H5.
      red in H7.
      inversion Hnot.
      red in H10.
      specialize (H6 x0).
      apply H6 in H4; auto.
      {
        destruct H4.
        clear -Hnot H4.
        intuition.
        inversion Hnot.
        red in H3.
        red in H0.
        specialize (H3 x0 x1 (in_eq x0 _) (in_cons _ _ _ H1)).
        simpl in H2.
        rewrite nodup_In in H2.
        contradiction.
      }
      {
        red in H9.
        specialize (H9 x0 (in_eq _ _)).
        simpl.
        destruct Nat.eq_dec; [omega | 
        apply enumerate_complete; omega].
      }
    }
  }        
Qed.

Lemma Proper_list_eq :forall a,
    Proper (equivlistA eq ==> flip impl) (lex_order.list_eq a).
Proof.
  intros.
  red.
  red.
  intros.
  unfold flip.
  unfold impl.
  intros.
  red in H0.
  red in H.
  red.
  split; intros; auto.
  {
    apply H0 in H1.
    rewrite <- In_InAeq_iff in H1;
      rewrite <- In_InAeq_iff .
    apply H; auto.
  }
  {
    rewrite <- In_InAeq_iff in H1;
      rewrite <- In_InAeq_iff .
    apply H in H1; auto.
    rewrite In_InAeq_iff in H1;
      rewrite In_InAeq_iff .
    apply H0; auto.
  }
Qed.

Instance : (forall a,
    Proper (equivlistA eq ==> flip impl) (lex_order.list_eq a)).
apply Proper_list_eq.
Qed.

Instance : forall a,
 Proper (lex_order.list_eq ==> flip impl) (equivlistA eq a).
Proof.
  red.
  red.
  intros.
  unfold impl.
  unfold flip.
  intros.
  red in H0.
  red in H.
  red.
  split; intros; auto.
  {
    apply H0 in H1.
    rewrite In_InAeq_iff in H1;
      rewrite In_InAeq_iff .
    apply H; auto.
  }
  {
    rewrite In_InAeq_iff in H1;
      rewrite In_InAeq_iff .
    apply H in H1; auto.
    rewrite <- In_InAeq_iff in H1;
      rewrite <- In_InAeq_iff .
    apply H0; auto.
  }
Qed.

Lemma AllMIS_exists_helper : forall x0 x l,
  lex_order.list_eq x0 x -> 
  In x0 l -> 
  InA (equivlistA eq) x l.
Proof.
  intros.
  induction l.
  inversion H0.
  inversion H0; subst; auto.
  left.
  rewrite H.
  constructor; try split; intros; auto.
Qed.

Lemma PrintMIS_correct : forall G: lGraph,
  MIS_set_lGraph G (PrintMIS G).
Proof.
  intros.
  constructor.
  {
    intros.
    apply all_MIS_sound.PrintMIS_correct; auto.
  }
  {
    pose proof (all_MIS_unique.PrintMIS_unique G). 
    induction H.
    constructor.
    subst.
    constructor; auto.
    intros Hnot.
    apply H.
    clear - Hnot.
    induction L; auto.
    inversion Hnot.
    inversion Hnot.
    subst.
    constructor.
    rewrite H0.
    apply lex_order.list_eq_ref.
    subst.
    apply IHL in H0.
    right; auto.
  }
  {
    intros.
    pose proof (PrintMIS_complete G); auto.
    unfold MIS_basics.MaximalIndSet_lGraph in H0.
    apply H0 in H; auto.
    destruct H; intuition.
    eapply AllMIS_exists_helper; eauto.
  }
Qed.

Require Import Reals.
Require Import moon_lemma.

Lemma MIS_bound : forall G l,
    MIS_set_lGraph G l -> INR (length l) <= I (lV G).
Proof.
  intros.
  apply All_MIS_preserved_lGraph_to_GenGraph in H.
  pose proof (@MIS_Bounds nat Nat.eq_dec (GenGraph_of G) l H);
    auto.
  assert (length (gV nat (GenGraph_of G)) = lV G); auto.
  {
    unfold GenGraph_of.
    simpl.
    destruct Nat.eq_dec; subst; auto.
    clear -n.
    generalize dependent (lV G).
    intros.
    induction n; auto.
    contradiction.
    destruct n; simpl in *; auto.
    rewrite <- IHn; auto.
    rewrite Nat.sub_0_r; auto.
  }
  rewrite <- H1; auto.
Qed.

Theorem PrintMIS_correct_and_small : forall G: lGraph,
    MIS_set_lGraph G (PrintMIS G) /\
    INR (length (PrintMIS G)) <= I (lV G).
Proof.
  intros G; split.
  { apply PrintMIS_correct. }
  apply MIS_bound. apply PrintMIS_correct.
Qed.  
