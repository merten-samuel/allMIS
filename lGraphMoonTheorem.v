Require Import explicit_graph.
Require Import graph_basics.
Require Import graphs_nondep.
Require Import SetoidList.
Require Import Omega.
Require Import all_MIS.
Require Import all_MIS_complete.
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


Lemma AllMIS_exists_lGraph : forall
    (G : lGraph),
    MIS_set_lGraph G ((PrintMIS G)).
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
Theorem MIS_bounds_lGraph : forall G l
    (mkG_MIS :  (GenGraph nat) -> list (list nat)), (*FIXME: This assumption needs to be instantiated.*)    
    MIS_set_lGraph G l -> 
    INR (length l) <= I (lV G).
Proof.
  intros.
  apply All_MIS_preserved_lGraph_to_GenGraph in H.
  pose proof (@MIS_Bounds nat Nat.eq_dec mkG_MIS (GenGraph_of G) l H);
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
