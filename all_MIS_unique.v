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

Theorem PrintMIS_unique :
  forall G, NoDups' (PrintMIS G).
Proof.
  intros G. induction G using InducedGraph_ind.
  unfold PrintMIS. simpl. constructor. intros H.
  inversion H. constructor.
  (*generalize (PrintMIS_complete (LiftGraph x G)). intros. *)
  generalize I. intros.
  generalize (PrintMIS_correct (LiftGraph x G)). intros.
  generalize (PrintMIS_correct (LiftGraph (S x) G)). intros.
  generalize I. intros.
  (*generalize (PrintMIS_complete (LiftGraph (S x) G)). intros. *) (*sick chiasmus dawg *) 
  {
    unfold PrintMIS in *. simpl in *.
    rewrite -> LiftGraph_red in *; try omega. 
    revert H H0 H1 H2 IHG. generalize (mkSetsPrintMIS x (LiftGraph x G)).
    intros. induction l. constructor. inversion IHG. subst.
    unfold mkCandidateSets. simpl (lV (LiftGraph (S x) G)).
    cbv iota beta. fold mkCandidateSets.
    destruct (independent_lGraph (LiftGraph (S x) G) (x :: a)) eqn: H3. 
    { (*Begin (x::a) in children *)
      constructor. intros H4.
      apply list_eq_in_witness in H4.
      destruct H4 as [l1 [H9 H4']].
      assert (In (rmv x l1) l).
      apply form2 with
        (G := LiftGraph (S x) G)
        (Lout := mkCandidateSets (LiftGraph (S x) G) l); auto.
      {
        apply H9. left. auto.
      }
      {
        intros.
        subst. rewrite -> LiftGraph_red.
        apply H0. right. auto. omega.
      }
      {
        rewrite -> LiftGraph_red; [|omega].
        apply TBD2 with (x := x) in H9.
        simpl (rmv x (x:: a)) in H9.
        destruct eq_nat_dec in H9; try omega.
        apply eq_preserves_MIS with (X := a).
        apply list_eq_trans with (Y := rmv x a).
        rewrite -> TBE. apply list_eq_ref.
        intros H10. apply (H0 a) in H10.
        simpl in H10. omega. left. auto.
        apply list_eq_symmetric. auto.
        simpl. apply H0. left. auto.
      }
      {
        apply mkCandidateSetsP.
        symmetry. auto.
      }
      {
        intros. apply H1. unfold mkCandidateSets.
        simpl lV. fold mkCandidateSets.
        cbv iota beta. destruct independent_lGraph.
        right. auto. repeat (destruct LFMIS_dec);
        repeat right; auto.
      }
      {
        apply H5. apply list_eq_in_spec with (l2 := (rmv x l1)).
        unfold list_eq. intros y. split; intros h.
        apply remove_spec. split.
        apply H9. right. auto. apply H0 in h.
        simpl in h. omega. left. auto.
        apply remove_spec with (H0 := eq_nat_dec) in h.
        destruct h as [h h']. apply H9 in h.
        destruct h as [h | h]. omega. auto.
        auto.
      }
      {
        apply IHl.
        {
          intros. apply H0. right. auto.
        }
        {
          intros. apply H1. unfold mkCandidateSets.
          simpl lV. fold mkCandidateSets.
          cbv iota beta. destruct independent_lGraph.
          right. auto. repeat (destruct LFMIS_dec);
          repeat right; auto.
        }
        {
          auto.
        }
      }
    (*End (x::a) in children *)
    }
    destruct LFMIS_dec.
    destruct LFMIS_dec.
    { (* Begin (x::rmvNeighb x a) in Head *)
      constructor. intros H4.
      { 
        apply list_eq_in_witness in H4.
        destruct H4 as [l2 [H9 H4']].
        assert (exists l' : list nat,
          LFMIS (LiftGraph x (LiftGraph (S x) G)) (rmv x l2) l' /\ In l' l).
          apply (form3 x (LiftGraph (S x) G) 
                    (mkCandidateSets (LiftGraph (S x) G) l)
                    l l2).
          {
            simpl. auto.
          }
          {
            apply H9. left. auto.
          }
          {
            destruct H4'.
            { 
              subst. assert (In x l2). apply H9.
              left. auto. apply H0 in H4. simpl in H4.
              omega. left. auto.
            }
            {
              auto.
            }
          }
          {
            intros. rewrite -> LiftGraph_red. apply H0.
            right. auto. omega.
          }
          {
            rewrite -> LiftGraph_red; [|omega].
            rewrite -> LiftGraph_red in l1; [|omega].
            intros h. clear H H2 H4' H5 H6 IHl IHG.
            apply (TBD2 x) in H9.
            simpl in H9. destruct eq_nat_dec; [|omega].
            assert (rmv x (rmvNeighbors x (LiftGraph (S x) G) a)
                    =
                    (rmvNeighbors x (LiftGraph (S x) G) a)) as h0.
            apply TBE. intros h0.  apply rmv_neighbors_spec in h0.
            destruct h0 as [h0 _]. apply H0 in h0. simpl in h0.
            omega. left. auto. rewrite -> h0 in H9. clear h0.
            apply eq_preserves_MIS
              with (Y := (rmvNeighbors x (LiftGraph (S x) G) a))in h.
            simpl in h. assert (In a (a::l)). left. auto.
            apply H0 in H. unfold independent_lGraph in H3; graphax_tac.
            apply Independent_spec_neg in H3; graphax_tac.
            destruct H3 as [i [j [h0 [h1 h2]]]].
            destruct h0 as [h0 | h0]; destruct h1 as [h1 | h1].
            {
              repeat subst. apply flatten_Edges_irref in h2.
              omega.
            }
            {
              subst. assert (~ In j (rmvNeighbors i (LiftGraph (S i) G) a)).
              intros h0. apply rmv_neighbors_spec in h0.
              destruct h0 as [_ h0]. contradiction.
              inversion h. apply H4 in H2. 
              apply H2. constructor.
              intros k h0. apply H.
              destruct h0 as [h0 | h0]. subst. auto.
              apply rmv_neighbors_spec in h0.
              destruct h0 as [h0 _]. auto.
              intros x0 y0 h0 h3. apply H.
              destruct h0 as [h0 | h0]. subst. auto.
              apply rmv_neighbors_spec in h0.
              destruct h0 as [h0 _]. auto.
              destruct h3 as [h3 | h3]. subst. auto.
              apply rmv_neighbors_spec in h3.
              destruct h3 as [h3 _]. auto.
            }
            {
              repeat subst.
              assert (~ In i (rmvNeighbors j (LiftGraph (S j) G) a)).
              intros h1. apply rmv_neighbors_spec in h1.
              destruct h1 as [_ h1]. 
              apply flatten_Edges_symm in h2. contradiction.
              inversion h. apply H4 in H2. 
              apply H2. constructor.
              intros k h1. apply H.
              destruct h1 as [h1 | h1]. subst. auto.
              apply rmv_neighbors_spec in h1.
              destruct h1 as [h1 _]. auto.
              intros x0 y0 h1 h3. apply H.
              destruct h1 as [h1 | h1]. subst. auto.
              apply rmv_neighbors_spec in h1.
              destruct h1 as [h1 _]. auto.
              destruct h3 as [h3 | h3]. subst. auto.
              apply rmv_neighbors_spec in h3.
              destruct h3 as [h3 _]. auto.            
            }
            {
              inversion H. inversion H2.
              apply (H5 i j); auto.
              apply LiftGraph_FlatEdge_spec.
              split. apply LiftGraph_FlatEdge_spec in h2.
              destruct h2 as [h2 _]. auto.
              split; apply H4; auto.
            }
            auto.
          }
          {
            apply mkCandidateSetsP. reflexivity.
          }          
          {
            destruct H4' as [H4' | H4'].
            {
              subst. assert (In l2 (l2::l)).
              left. auto. apply H0 in H7.
              apply eq_preserves_MIS
                with (Y := (x :: rmvNeighbors x (LiftGraph (S x) G) l2))
                in H7.
              inversion H7. inversion H8.
              assert (x < x). apply H11.
              left. auto. omega. auto.
            }
            {
              apply H5. destruct H4 as [l' [h h0]].
              apply list_eq_in_spec with (l2 := l'); auto.
              rewrite -> LiftGraph_red in h; [|omega].
              rewrite -> LiftGraph_red in l1; [|omega].
              unfold LFMIS in *.
              assert (In l' (a::l)). right. auto.
              apply H0 in H4.
              assert (In a (a::l)). left. auto.
              apply H0 in H7. clear H0 H H2 IHG H5 H6.
              assert (list_eq
                       (rmv x l2)
                       (rmvNeighbors x (LiftGraph (S x) G) a)).
              {
                apply TBD2 with (x := x) in H9.
                simpl in H9. destruct eq_nat_dec; [|omega].
                assert (rmv x (rmvNeighbors x (LiftGraph (S x) G) a)
                        =
                       (rmvNeighbors x (LiftGraph (S x) G) a)).
                {
                  apply TBE. intros H8.
                  apply rmv_neighbors_spec in H8. destruct H8 as [H8 _].
                  apply H7 in H8. simpl in H8. omega.
                }
                rewrite -> H in H9. auto.
              }
              eapply (MkMIS_preserves_eq x (flatten_EdgesGraph (LiftGraph x G))) in H.
              unfold MkMaximalIndSet_lGraph in h. simpl in h.
              apply list_eq_symmetric in H.
              generalize ((list_eq_trans _ _ _) H h). intros.
              apply list_eq_trans
                with (Y := (MkMaximalIndSet x
                                            (flatten_EdgesGraph (LiftGraph x G))
                                            (fun x0 y =>
                                               match flatten_Edges_symm (LiftGraph x G) x0 y with
                                                 | conj A B => A
                                               end)
                             (rmvNeighbors x (LiftGraph (S x) G) a))); auto.
              apply list_eq_symmetric in l1.
              auto.
            }
          }
        }
        {
          constructor. intros H4.
          apply list_eq_in_witness in H4.
          destruct H4 as [l2 [H9 H4']].
          assert (In l2 l).
          apply form1 with
            (x := x)
            (G := LiftGraph (S x) G)
            (Lout := mkCandidateSets (LiftGraph (S x) G) l); auto.
          {
            intros h. apply H9 in h.
            apply H0 in h. simpl in h. omega.
            left. auto.
          }
          {
            apply mkCandidateSetsP. 
            reflexivity.
          }
          {
            apply H5. apply list_eq_in_spec with (l2 := l2).
            apply list_eq_symmetric. auto. auto.
          }
          {
            apply IHl. intros. apply H0.
            right. auto. intros. apply H1.
            unfold mkCandidateSets.
            simpl lV. fold mkCandidateSets.
            cbv iota beta. destruct independent_lGraph.
            right. auto. repeat (destruct LFMIS_dec);
            repeat right; auto. auto.
          }
        }
      }
    {
      constructor. intros H4.
      apply list_eq_in_witness in H4.
      destruct H4 as [l1 [H9 H4']].
      assert (In l1 l).
      apply form1 with
        (x := x)
        (G := LiftGraph (S x) G)
        (Lout := mkCandidateSets (LiftGraph (S x) G) l); auto.
      {
        intros h. apply H9 in h.
        apply H0 in h. simpl in h. omega.
        left. auto.
      }
      {
        apply mkCandidateSetsP. 
        reflexivity.
      }
      {
        apply H5. apply list_eq_in_spec with (l2 := l1).
        apply list_eq_symmetric. auto. auto.
      }
      {
        apply IHl. intros. apply H0.
        right. auto. intros. apply H1.
        unfold mkCandidateSets.
        simpl lV. fold mkCandidateSets.
        cbv iota beta. destruct independent_lGraph.
        right. auto. repeat (destruct LFMIS_dec);
        repeat right; auto. auto.
      }
    }
    {
      constructor. intros H4.
      apply list_eq_in_witness in H4.
      destruct H4 as [l1 [H9 H4']].
      assert (In l1 l).
      apply form1 with
        (x := x)
        (G := LiftGraph (S x) G)
        (Lout := mkCandidateSets (LiftGraph (S x) G) l); auto.
      {
        intros h. apply H9 in h.
        apply H0 in h. simpl in h. omega.
        left. auto.
      }
      {
        apply mkCandidateSetsP. 
        reflexivity.
      }
      {
        apply H5. apply list_eq_in_spec with (l2 := l1).
        apply list_eq_symmetric. auto. auto.
      }
      {
        apply IHl. intros. apply H0.
        right. auto. intros. apply H1.
        unfold mkCandidateSets.
        simpl lV. fold mkCandidateSets.
        cbv iota beta. destruct independent_lGraph.
        right. auto. repeat (destruct LFMIS_dec);
        repeat right; auto. auto.
      }
    }
  }
Qed.


Print Assumptions PrintMIS_unique.