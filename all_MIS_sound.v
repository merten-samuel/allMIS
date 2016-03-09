Require Import List.
Require Import Arith.
Require Import Omega.
Require Import ProofIrrelevance.
Require Import graph_basics.
Require Import lex_order.
Require Import graphs_nondep.
Require Import MIS_basics.
Require Import all_MIS.

Theorem mkCandidateSets_correct_ind :
  forall l x G,
    (forall y, In y l -> MaximalIndSet_lGraph (LiftGraph x G) y) ->
      (forall y, In y (mkCandidateSets (LiftGraph (S x) G) l) -> MaximalIndSet_lGraph (LiftGraph (S x) G) y).
Proof.
  intros l. induction l; intros.
  {
    inversion H0.
  }
  unfold mkCandidateSets in H0. simpl (lV (LiftGraph (S x) G)) in H0.
  fold mkCandidateSets in H0. cbv beta iota in H0.
  remember (independent_lGraph (LiftGraph (S x) G) (x :: a)) as b0.
  destruct b0.
  {
    destruct H0 as [H0 | H0]. subst.
    apply  l1_spec_mkCandidateSets. apply H. simpl. left. 
    reflexivity. symmetry in Heqb0. apply independent_spec.
    { intros x0 y H2.
      apply flatten_Edges_symm in H2; auto.
    }
    assumption.
    apply IHl. intros. apply H. right. assumption.
    assumption.
  }
  {
    destruct isMIS.
    {
      destruct LFMIS_dec.
      {
        destruct H0 as [H0 | [H0 | H0]].
        {
          subst. apply MIS_MKMIS'.
          simpl.
          apply (rmv_neighbors_preserves_IndSet_ext x (LiftGraph (S x) G) a). 
          apply lt_LiftGraph_PreservesIndSet. assert (In a (a::l)) as H0.
          left. reflexivity. apply H in H0. destruct H0 as [H0 H1].
          apply H0. simpl. omega. unfold LFMIS in l0. simpl in l0. simpl.
          apply list_eq_symmetric. assumption.
        }
        {
          subst. apply l2_spec_mkCandidateSets. apply H.
          left. reflexivity. symmetry in Heqb0. intros H0.
          apply independent_spec in H0.
          unfold independent_lGraph in Heqb0.
          rewrite -> H0 in Heqb0. inversion Heqb0.
          graphax_tac.
        }
        {
          apply IHl; [intros; apply H; right | ]; assumption.
        }
      }
      {
        destruct H0 as [H0 | H0].
        {
          subst. apply l2_spec_mkCandidateSets. apply H.
          left. reflexivity. symmetry in Heqb0. intros H0.
          apply independent_spec in H0.
          unfold independent_lGraph in Heqb0.
          rewrite -> H0 in Heqb0. inversion Heqb0.
          graphax_tac.
        }
        {
          apply IHl; [intros; apply H; right | ]; assumption.
        }
      }
    }
    {
      destruct H0 as [H0 | H0].
      {
        subst. apply l2_spec_mkCandidateSets. apply H.
        left. reflexivity. symmetry in Heqb0. intros H0.
        apply independent_spec in H0.
        unfold independent_lGraph in Heqb0.
        rewrite -> H0 in Heqb0. inversion Heqb0.
        graphax_tac.
      }
      {
        apply IHl; [intros; apply H; right | ]; assumption.   
      }
    }
  }
Qed.

Theorem PrintMIS_correct :
  forall G l, In l (PrintMIS G) -> MaximalIndSet_lGraph G l.
Proof.
  intros G. induction G using InducedGraph_ind; intros.
  {
    simpl in H. unfold MaximalIndSet_lGraph.
    simpl. destruct H as [H | H].  subst. apply MIS_nil_iff_0. graphax_tac.
    reflexivity. inversion H.
  }
  {
    unfold PrintMIS in H.
    apply mkCandidateSets_correct_ind with (l := PrintMIS (LiftGraph x G)).
    assumption. simpl in H. 
    simpl mkSetsPrintMIS in H. simpl in H.
    rewrite -> LiftGraph_red in H.
    assumption. omega.
  }
Qed.


Print Assumptions PrintMIS_correct.