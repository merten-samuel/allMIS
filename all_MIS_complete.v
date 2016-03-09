Require Import List.
Require Import Arith.
Require Import Omega.
Require Import ProofIrrelevance.
Require Import graph_basics.
Require Import lex_order.
Require Import graphs_nondep.
Require Import MIS_basics.
Require Import all_MIS.
Require Import all_MIS_sound.

Theorem PrintMIS_complete :
  forall G l, MaximalIndSet_lGraph G l -> exists l', list_eq l' l /\ In l' (PrintMIS G).
Proof.
    intros G.  induction G using InducedGraph_ind; intros.
  {
  (* Base Case *) 
    exists nil. simpl. apply TrivialIndSet in H. subst.
    split. apply list_eq_ref. left. reflexivity. reflexivity.
  }
  {
    rewrite -> MaximalIndSet_eq_lGraph in *.  
    assert ({In x l} + {~In x l}) as H0
      by (apply list_in_dec; apply eq_nat_dec).
    destruct H0 as [H0 | H0].
    (*Is x in the MIS? *)
    {
      (*If it is, one of two things happened:
          1.) removing x from l produces a LFMIS in (LG x G)
          2.) removing x from l fails to produce a LFMIS in (LG x G) 
       *)
       (* Case 1 *)
     case (isMIS (LiftGraph x G) (rmv x l)); intros H2.       
     {
       assert (list_eq l (x::rmv x l)). apply remove_inv. assumption.
       assert (MaximalIndSet_lGraph (LiftGraph x G) (rmv x l)) as H3.
       unfold LFMIS in H2.
       assert (MaximalIndSet_lGraph (LiftGraph x G)
         (MkMaximalIndSet_lGraph (LiftGraph x G) (rmv x l))) as H4.
       apply MkMaximalIndSet_spec2'. simpl.
       apply l4_spec_mkCandidateSets. destruct H as [H H'].
       assumption.
       apply eq_preserves_MIS with
         (X := (MkMaximalIndSet_lGraph (LiftGraph x G) (rmv x l))).
       assumption. assumption. 
       specialize (IHG (rmv x l)). remember (IHG H3). clear Heqe.
       destruct e as [l' [H4 H5]]. exists (x::l').
       split. apply (list_eq_trans _ (x :: rmv x l) _).
       apply list_eq_cons. assumption. apply list_eq_symmetric in H1.
       assumption. unfold PrintMIS. simpl.
       apply l5_spec_mkCandidateSets. assumption.
       destruct H as [[H H'] H'']. simpl in H'.
       unfold Independent. intros x0 y0 H6 H7.
       assert (list_eq l (x:: l')) as H8.
       apply (list_eq_trans _ (x :: rmv x l) _).
       assumption. apply list_eq_cons.
       apply list_eq_symmetric in H4. assumption.
       apply (H' x0 y0).
       apply incl_list_eq in H8.
       destruct H8 as [H8 H8']. apply H8'. assumption.
       apply incl_list_eq in H8.
       destruct H8 as [H8 H8']. apply H8'. assumption.
    }
    (* Case 2 - removing X from l did not produce a LFMIS *)
    {
      assert (list_eq
              l
              (x :: rmvNeighbors x (LiftGraph (S x) G)
                      (MkMaximalIndSet_lGraph (LiftGraph x G) (rmv x l)))) as H3.
      {
        apply MaximalIndSet_eq_lGraph in H.
        apply l10_spec_mkCandidateSets in H.
        assumption. assumption.
      }
      assert (MaximalIndSet_lGraph (LiftGraph x G)
               (MkMaximalIndSet_lGraph (LiftGraph x G) (rmv x l))) as H4.
      {
        apply MkMaximalIndSet_spec2'. simpl. apply l9_spec_mkCandidateSets.
        destruct H; assumption.
      }
      apply IHG in H4. destruct H4 as [l' [H4 H5]].
      assert (LFMIS (LiftGraph x G) l' l') as H7.
      {
        apply LFMIS_cond_ref.
        apply eq_preserves_MIS
          with (X := (MkMaximalIndSet_lGraph (LiftGraph x G) (rmv x l))).
        apply list_eq_symmetric. assumption. simpl.
        apply MkMaximalIndSet_spec2; graphax_tac.
        apply l9_spec_mkCandidateSets.
        destruct H as [H' H]. assumption.
      }
      assert (independent
               (flatten_EdgesGraph (LiftGraph (S x) G))
               (x::l')
              = 
              false) as H8.
      {
        apply l12_spec_mkCandidateSets in H2.
        destruct H2 as [y [H2 H8]]. apply Independent_spec_neg; graphax_tac.
        destruct H as [[H H'] H''].
        assert (~ In y l) as H9. intros H8'. apply H8.
        apply remove_spec. split. assumption.
        assert (MaximalIndSet_lGraph (LiftGraph x G)
                 (MkMaximalIndSet_lGraph (LiftGraph x G) (rmv x l))).
        {
          apply MkMaximalIndSet_spec2; graphax_tac. simpl.
          apply l9_spec_mkCandidateSets. split; assumption.
        }
        destruct H1 as [[H1 H1'] H1'']. specialize (H1 y).
        simpl in H1. apply H1 in H2. omega. apply H'' in H9.
        simpl in H9.
        assert (~independent (flatten_EdgesGraph
                             (LiftGraph (S x) G)) (y :: l) = true).
        {
          intros H10. apply H9.
          assert (MaximalIndSet_lGraph (LiftGraph x G)
          (MkMaximalIndSet_lGraph (LiftGraph x G) (rmv x l))).
          {
            apply MkMaximalIndSet_spec2; graphax_tac. simpl.
            apply l9_spec_mkCandidateSets. split; assumption.
          }
          split. intros z H11.
          destruct H11 as [H11 | H11]. subst. destruct H1 as [[H1 H1'] H1''].
          specialize (H1 z). simpl in H1. apply H1 in H2. omega.
          apply H in H11. simpl in H11. assumption.
          apply independent_spec in H10; graphax_tac.
          assumption.
        }
        assert (independent (flatten_EdgesGraph (LiftGraph (S x) G)) (y :: l)
                = false).
        destruct (independent (flatten_EdgesGraph (LiftGraph (S x) G)) (y :: l)).
        apply False_rec. apply H1. reflexivity. reflexivity.
        apply Independent_spec_neg in H6; graphax_tac.
        destruct H6 as [x0 [y0 [H6 [H6' H6'']]]].
        exists x0, y0. repeat split; try assumption.
        destruct H6 as [H6 | H6]. right. apply H4.
        subst. assumption.
        assert ({x0 = x} + {x0 <> x}) as H10 by apply eq_nat_dec.
        destruct H10. left. subst. reflexivity.
        right. apply H4. assert (In x0 (rmv x l)). apply remove_spec.
        split; assumption.
        assert (exists l'', MkMaximalIndSet_lGraph (LiftGraph x G) (rmv x l)=
                            l''++(rmv x l)).
        {
          apply MkMaximalIndSet_deapp; graphax_tac.
          simpl. apply l9_spec_mkCandidateSets.
          split; assumption.
        }
        destruct H11 as [l'' H11]. rewrite -> H11. apply in_or_app. right.
        assumption.
        destruct H6' as [H6' | H6']. right. apply H4.
        subst. assumption.
        assert ({y0 = x} + {y0 <> x}) as H10 by apply eq_nat_dec.
        destruct H10. left. subst. reflexivity.
        right. apply H4. assert (In y0 (rmv x l)). apply remove_spec.
        split; assumption.
        assert (exists l'', MkMaximalIndSet_lGraph (LiftGraph x G) (rmv x l)=
                            l''++(rmv x l)).
        {
          apply MkMaximalIndSet_deapp; graphax_tac.
          simpl. apply l9_spec_mkCandidateSets.
          split; assumption.
        }
        destruct H11 as [l'' H11]. rewrite -> H11. apply in_or_app. right.
        assumption. apply l9_spec_mkCandidateSets.
        destruct H as [H H']. assumption.
      }
      exists (x
        :: rmvNeighbors x (LiftGraph (S x) G) l').
      split. apply list_eq_symmetric.
      apply list_eq_trans with (Y:=
        (x :: rmvNeighbors x (LiftGraph (S x) G)
                (MkMaximalIndSet_lGraph (LiftGraph x G) (rmv x l)))) .
      assumption.
      {
        apply list_eq_cons. unfold list_eq. intros a; split; intros h;
        apply rmv_neighbors_spec in h; apply rmv_neighbors_spec; destruct h 
        as [h h']; split; try assumption; apply H4; assumption.
      }
      unfold PrintMIS. simpl (lV (LiftGraph (S x) G)).
      simpl. rewrite -> LiftGraph_red. unfold PrintMIS in H5.
      apply l13_spec_mkCandidateSets; try assumption.
      apply LFMIS_cond_ref. apply eq_preserves_MIS with (X := l).
      apply list_eq_trans with
        (Y := (x :: rmvNeighbors x (LiftGraph (S x) G)
                      (MkMaximalIndSet_lGraph (LiftGraph x G) (rmv x l)))).
      assumption. apply list_eq_cons. split; intros h.
      {
        apply rmv_neighbors_spec in h. destruct h as [h h'].
        apply rmv_neighbors_spec. split. apply H4.
        assumption. assumption.
      }
      {
        apply rmv_neighbors_spec in h. destruct h as [h h'].
        apply rmv_neighbors_spec. split. apply H4.
        assumption. assumption.
      }
      simpl. unfold MaximalIndSet_lGraph in H.
      simpl in H. apply MaximalIndSet_eq_lGraph in H. assumption.
      unfold LFMIS. apply list_eq_symmetric in H4.
      apply list_eq_trans with
        (MkMaximalIndSet_lGraph (LiftGraph x G) (rmv x l)).
      apply TBD1.
      assert (list_eq
               (rmv x l)
               (rmv x
                 (x :: (rmvNeighbors x (LiftGraph (S x) G) 
                         (MkMaximalIndSet_lGraph (LiftGraph x G) (rmv x l))))))
      as H9 by (apply TBD2; assumption).

      assert (list_eq
               (rmv x (x :: ((rmvNeighbors x (LiftGraph (S x) G) 
                         (MkMaximalIndSet_lGraph (LiftGraph x G) (rmv x l))))))
               (rmvNeighbors x (LiftGraph (S x) G) 
                         (MkMaximalIndSet_lGraph (LiftGraph x G) (rmv x l)))) as H10.
      {
        assert (rmv x 
                    (x :: rmvNeighbors x (LiftGraph (S x) G)
                            (MkMaximalIndSet_lGraph (LiftGraph x G) (rmv x l)))
                =
                rmvNeighbors x (LiftGraph (S x) G)
                            (MkMaximalIndSet_lGraph (LiftGraph x G) (rmv x l)))
        as H10.
        {
          simpl. destruct eq_nat_dec. apply TBE.
          intros H1. apply rmv_neighbors_spec in H1.
          destruct H1 as [H1 H1']. 
          assert (Ind_Set_lGraph (LiftGraph x G) (rmv x l)) as h2.
          apply l9_spec_mkCandidateSets.
          destruct H as [H H']. assumption.
          apply MkMaximalIndSet_spec2' in h2.
          destruct h2 as [[h2' _] _].
          apply h2' in H1. simpl in H1. omega.
          apply False_rec. apply n. reflexivity.
        }
        rewrite -> H10. apply list_eq_ref.
      }
      
      apply list_eq_trans with
        (Y := (rmv x (x :: rmvNeighbors x (LiftGraph (S x) G)
                             (MkMaximalIndSet_lGraph (LiftGraph x G) (rmv x l)))));
      try (apply list_eq_symmetric; assumption).
      apply list_eq_trans with
        (Y := (rmvNeighbors x (LiftGraph (S x) G)
           (MkMaximalIndSet_lGraph (LiftGraph x G) (rmv x l))));
      try (apply list_eq_symmetric; assumption).
      apply TBD3. apply list_eq_symmetric. assumption. assumption.
      intros H9. apply independent_spec in H9; graphax_tac.
      rewrite -> H9 in H8.
      inversion H8. omega.
    }
  }
  (*x isn't in the MIS *)
  {
    apply MaximalIndSet_eq_lGraph in H.
    assert (MaximalIndSet_lGraph (LiftGraph x G) l)
      by (apply l3_spec_mkCandidateSets in H; assumption).
    apply MaximalIndSet_eq_lGraph in H.
    apply IHG in H1.
    destruct H1 as [l' [H2 H3]].
    exists l'. split. assumption.
    assert (MaximalIndSet_lGraph (LiftGraph (S x) G) l').
    apply eq_preserves_MIS with (X := l). apply list_eq_symmetric.
    assumption. simpl. apply MaximalIndSet_eq_lGraph in H. assumption. 
    unfold PrintMIS. simpl.
    unfold PrintMIS in H3. simpl in H3.
    rewrite -> LiftGraph_red.
    induction ((mkSetsPrintMIS x (LiftGraph x G))).
    inversion H3. destruct H3.
    {
      subst.
      unfold mkCandidateSets.
      simpl (lV (LiftGraph (S x) G)). cbv iota beta.
      fold mkCandidateSets.
      remember (independent_lGraph (LiftGraph (S x) G) (x :: l')).
      destruct b. apply MaximalIndSet_eq_lGraph in H1.
      destruct H1 as [H1 H1']. specialize (H1' x).
      assert (~ In x l') as H3. intros H0'. apply H0.
      apply H2. assumption.
      apply H1' in H3.
      assert (~ independent_lGraph (LiftGraph (S x) G) (x::l') = true).
      intros H4. apply H3. split. simpl.
      intros a H5. destruct H5 as [H5 | H5].
      subst. omega. destruct H1 as [H1 H1''].
      apply H1 in H5. simpl in H5. assumption.
      unfold independent_lGraph in H4. 
      apply independent_spec in H4; graphax_tac.
      assumption. symmetry in Heqb.
      contradiction.
      destruct isMIS.
    {
      destruct LFMIS_dec. right. left. reflexivity.
      left. reflexivity.
    }
    {
      left. reflexivity.
    }
  }
  apply IHl0 in H3. unfold mkCandidateSets.
  simpl (lV (LiftGraph (S x) G)).
  fold mkCandidateSets. cbv iota beta.
  unfold isMIS.
  destruct independent_lGraph; try (repeat destruct LFMIS_dec);
  repeat right; assumption. omega.
  }
}
Qed.

Print Assumptions PrintMIS_complete.