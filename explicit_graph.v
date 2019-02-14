Require Import SetoidList Omega.
Require Import moon_lemma.
Require Import graph_basics.
Require Import all_MIS_unique.
Require Import GenGraph.
Require Import GenGraphAllMIS.
Close Scope R_scope.

Section GraphInequalities.
  Variable T : Type.
  Variable Tdec : forall t1 t2 : T, {t1 = t2} + {t1 <> t2}.

Lemma Prop4_vatter :
  forall G misG misG_x misG_Nx x Nx (H_mem : In x (gV _ G)),
    neighborhood_E T G x Nx ->    
    MIS_set_gGraph G misG ->
    MIS_set_gGraph (removeVerts T Tdec G (x::nil)) misG_x ->
    MIS_set_gGraph (removeVerts T Tdec G (x::Nx)) misG_Nx ->
      length(misG) <= length misG_x + length misG_Nx.
Proof.
  intros.
  remember
    (filter (sumbool_left_bool _ _ _ ((in_dec Tdec) x)) misG) as l2.
  remember
    ((filter (sumbool_right_bool _ _ _ ((in_dec Tdec) x)) misG)) as l1.
  assert ((NoDupA (equivlistA eq)) l1).
    { rewrite Heql1. apply filter_NoDupA. inversion H0. auto. }
  assert ((NoDupA (equivlistA eq)) l2).
    { rewrite Heql2. apply filter_NoDupA. inversion H0. auto. }
  replace (length misG) with
      ((length l1) + (length l2)).
  2:{ rewrite -> Heql1, Heql2. symmetry. rewrite plus_comm. apply splitList_length. intros.
      apply splitList_summbool_spec. }
  apply Nat.add_le_mono.
  apply
    (NoDupA_subset_length
      (list T)
      (list_eq_dec Tdec) (equivlistA eq) l1 misG_x
      (equivlist_equiv eq_equivalence) H3).
  intros.
  assert (forall l, In l l1 ->
             MaximalIndSet_E (removeVerts _ Tdec G (x::nil)) l).
  intros. apply Prop4_aux1. rewrite Heql1 in H6.
  apply filter_In in H6. destruct H6. inversion H0.
  apply H8. auto. auto. rewrite Heql1 in H6.
  apply filter_In in H6. destruct H6.
  intros Hcontra. unfold sumbool_right_bool in H7.
  destruct in_dec in H7. congruence. congruence. inversion H1.
  apply H9. apply InA_alt in H5.
  do 2 destruct H5. apply H6 in H10.
  eapply listeq_preserves_MIS_E. symmetry. eauto.
  auto.
  replace (length l2) with 
            (length (map (remove Tdec x) l2)).
  2:{ symmetry. rewrite map_length. auto. }
  apply
    (NoDupA_subset_length
      (list T)
      (list_eq_dec Tdec) (equivlistA eq) (map (remove Tdec x) l2) misG_Nx
      (equivlist_equiv eq_equivalence)). apply remove_NoDupA.
  auto. intros. rewrite Heql2 in H5.
  apply filter_In in H5. destruct H5. unfold sumbool_left_bool in H6.
  destruct in_dec in H6. auto. congruence.
  intros. inversion H2. apply H8.
  assert (In x (x::x0)). {left; auto. } 
  generalize (Prop4_aux2 _ Tdec G (x::x0) Nx x H9); intros.
  assert (MaximalIndSet_E G (x :: x0)).
  assert (InA (equivlistA eq) (x::x0) l2).
  eapply AllInA_remove_undo. intros.
  rewrite Heql2 in H11. apply filter_In in H11. 
  destruct H11. unfold sumbool_left_bool in H12.
  destruct in_dec. auto. congruence. eauto.
  inversion H0. apply InA_alt in H11.
  do 2 destruct H11. apply (listeq_preserves_MIS_E _ x1). symmetry.
  auto. apply H12. rewrite Heql2 in H15.
  apply filter_In in H15. destruct H15. auto.
  replace (remove Tdec x (x::x0)) with x0 in H10.
  apply H10. auto. auto. simpl. destruct Tdec.
  rewrite remove_id. auto. 
  apply InA_alt in H5. do 2 destruct H5. intros Hcontra.
  assert (InA eq x x0). apply InA_alt. exists x; split; auto.
  apply H5 in H13. apply in_map_iff in H12.
  do 2 destruct H12. rewrite <- H12 in H13.
  apply InA_alt in H13. do 2 destruct H13. subst.
  apply remove_In in H15. auto. congruence.
Qed.

Lemma MIS_Bounds_0_verts_aux1 : 
  forall G (l : list (list T)),
    MIS_set_gGraph G l -> 
    (length (gV _ G) = 0) ->
    MaximalIndSet_E G nil.
Proof.
  intros. constructor. constructor. intros x Hcontra.
  inversion Hcontra.
  simpl. intros x y Hcontra. inversion Hcontra.
  intros. destruct (gV T G). inversion H1. simpl in H0. omega.
Qed.

Lemma MIS_Bounds_0_verts_aux2 :
  forall G (l : list (list T)) l',
    MIS_set_gGraph G l -> 
    (length (gV _ G) = 0) ->
    In l' l -> l' = nil.
Proof.
  intros. destruct l'. auto. 
  inversion H. apply H2 in H1.
  inversion H1. assert (In t (t::l')). left. auto.
  apply H5 in H7. destruct (gV T G). inversion H7.
  simpl in H0. omega.
Qed.

Lemma MIS_Bounds_0_verts : 
  forall G (l : list (list T)),
    MIS_set_gGraph G l -> 
    (length (gV _ G) = 0) ->
    length l = 1.
Proof.
  intros. assert (gV T G = nil).
  destruct (gV T G). auto. simpl in H0.
  omega.
  assert (l = nil::nil).
  inversion H. destruct l.
  specialize (H4 nil).
  assert (MaximalIndSet_E G nil).
  eapply MIS_Bounds_0_verts_aux1. apply H.
  apply H0. apply H4 in H5. inversion H5.
  f_equal. eapply MIS_Bounds_0_verts_aux2; eauto.
  left. auto. destruct l0. auto. exfalso.
  inversion H3. apply H7; subst. left.
  assert (l = nil). eapply MIS_Bounds_0_verts_aux2; eauto.
  left. auto. assert (l0 = nil). 
  eapply MIS_Bounds_0_verts_aux2; eauto.
  right. left. auto. subst. reflexivity.
  subst. auto.
Qed.

Lemma MIS_Bounds_1_verts_aux1 : 
  forall G (l : list (list T)) t,
    MIS_set_gGraph G l -> 
    (gV _ G) = t::nil ->
    MaximalIndSet_E G (t::nil).
Proof.
  intros. constructor. constructor. intros x Hcontra.
  inversion Hcontra. subst. rewrite H0. left. auto.
  inversion H1. intros x y H1 H2.
  inversion H1. inversion H2. subst.
  apply (gE_irref _ G). inversion H4. inversion H3.
  intros. exfalso. apply H2. rewrite <- H0.
  auto.
Qed.

Lemma MIS_Bounds_1_verts_aux2 :
  forall G (l : list (list T)) t,
    MIS_set_gGraph G l -> 
    ((gV _ G) = t::nil) ->
    forall l', In l' l -> equivlistA eq l' (t::nil).
Proof.
  intros.
  assert (forall x, In x (l') -> x = t).
  inversion H. apply H2 in H1. inversion H1.
  inversion H5. intros. apply H7 in H9.
  rewrite H0 in H9. inversion H9. subst. auto.
  inversion H10. constructor; intros.
  constructor. apply H2. apply InA_alt in H3.
  do 2 destruct H3; subst; auto. inversion H3; subst.
  inversion H. apply H4 in H1.
  apply InA_alt. exists t; split; auto.
  inversion H1. destruct l'.
  assert (In t (gV T G)). rewrite H0. left. auto.
  apply H8 in H9. do 2 destruct H9. destruct H10.
  inversion H10. auto. left. apply H2. left. auto.
  inversion H5.
Qed.

Lemma all_in_no_dup
      x l
      (H: InA (equivlistA eq) x l)
      (All: forall l' : list T, In l' l -> equivlistA eq l' x)
      (NoDup: NoDupA (equivlistA eq) l): length l = 1.
  destruct l as [|a l].
  { inversion H. }
  simpl. cut (length l = 0).
  { intros ->; auto. }
  destruct l; auto.
  exfalso.
  assert (H2: In l (a :: l :: l0)).
  { right; left; auto. }
  generalize (All l H2).
  assert (H3: In a (a :: l :: l0)).
  { left; auto. }
  generalize (All a H3).
  intros <- Hx.
  inversion NoDup; subst. clear NoDup.
  apply H4. clear H4.
  left; rewrite Hx.
  constructor; auto.
Qed.  

(* For graphs G, if G has one vertex then G has one MIS (length l = 1). *)
Lemma MIS_bounds_1_verts :
  forall G (l : list (list T)) t,
    MIS_set_gGraph G l -> 
    ((gV _ G) = t::nil) -> length l = 1.
Proof.
  intros G l t H H2.
  generalize (MIS_Bounds_1_verts_aux2 _ _ _ H H2).
  inversion H; subst.
  assert (Hx: MaximalIndSet_E G (t::nil)).
  { apply MIS_Bounds_1_verts_aux1 with l; auto. }
  intros Hy; apply (all_in_no_dup (t::nil)); auto.
Qed.  


Definition isFstElemOfPair (x : T) (p : T*T) :=
  if Tdec x (fst p) then true else false.

Lemma isElemOFPair_spec :
  forall x p, isFstElemOfPair x p = true <-> (x = (fst p)).
Proof.
  intros. destruct p. simpl. unfold isFstElemOfPair.
  destruct Tdec; simpl in *; split; intros; subst; auto.
  congruence.
Qed.

Definition genNeighborhood_aux x l :=
  map snd (filter (fun p => isFstElemOfPair x p) l).

Lemma genNeighborhood_step x a l :
  genNeighborhood_aux x (a::l) =
  if Tdec x (fst a)
    then (snd a)::(genNeighborhood_aux x l)
    else genNeighborhood_aux x l.
Proof.
  unfold genNeighborhood_aux. simpl.
  destruct a. unfold isFstElemOfPair.
  destruct Tdec. auto. auto.
Qed.

Lemma genNeighborhood_aux_spec_inv :
  forall l x y, (In y (genNeighborhood_aux x l)) <-> In (x,y) l.
Proof.
  induction l. intros. simpl. split; intros; auto.
  intros. unfold genNeighborhood_aux. simpl. destruct a.
  unfold isFstElemOfPair; destruct Tdec; simpl in *; split; intros.
  destruct H. subst. left. auto. right. apply IHl in H. auto. destruct H.
  left. inversion H. auto.
  right. apply IHl. auto. right. apply IHl. auto.
  destruct H. inversion H. congruence. apply IHl. auto.
Qed.

Lemma genNeighborhood_aux_spec_nodup :
  forall l x, NoDup l -> NoDup (genNeighborhood_aux x l).
Proof.
  induction l. intros. unfold genNeighborhood_aux. simpl.
  constructor. intros. 
  rewrite genNeighborhood_step. destruct Tdec; destruct a;
  simpl in *. subst; inversion H; subst.
  constructor. rewrite genNeighborhood_aux_spec_inv. auto.
  all: (apply IHl; auto). inversion H; subst; auto.
Qed.


Definition genNeighborhood G x := 
  genNeighborhood_aux x (gE _ G).

Lemma genNeighborhood_spec1 : 
  forall G x,
    neighborhood_E _ G x (genNeighborhood G x).
Proof.
  intros. constructor; intros.
  apply (gE_symm _ G).
  apply genNeighborhood_aux_spec_inv. auto.
  apply (gE_symm _ G) in H.
  apply genNeighborhood_aux_spec_inv. auto.
Qed.

Lemma genNeighborhood_spec2 : 
  forall G x,
    NoDup (genNeighborhood G x).
Proof.
  intros. apply genNeighborhood_aux_spec_nodup.
  apply (gE_simplset _ G).
Qed.

Lemma neighborhood_E_NoDup_length_unique : 
  forall G (x : T) l1 l2, 
    NoDup l1 ->
    NoDup l2 ->
    neighborhood_E _ G x l1 ->
    neighborhood_E _ G x l2 ->
    length l1 = length l2.
Proof.
  intros. apply Nat.le_antisymm;
  apply NoDup_incl_length; auto;
  intros t H3. apply H2. apply H1. auto.
  apply H1. apply H2. auto.
Qed.

Lemma map_ind_cases : 
  forall (f : T -> nat) (l : list T),
    (exists x, In x l /\ f x = 0) \/
    (exists x, In x l /\ f x = 1) \/
    (exists x, In x l /\ f x >= 3) \/
    (forall x, 
      In x l ->
      f x = 2).
Proof.
  intros f l. induction l.
  repeat right. intros. inversion H.
  destruct IHl. do 2 destruct H.
  left. exists x. split. right. auto. auto.
  destruct H. right. left. do 2 destruct H.
  exists x. split. right. auto. auto.
  destruct H. right. right. left. do 2 destruct H.
  exists x. split. right. auto. auto.
  assert (f a = 0 \/ f a = 1 \/ f a = 2 \/ f a >= 3).
  omega. destruct H0. left. exists a. split. left. auto. auto.
  destruct H0. right. left. exists a. split. left. auto. auto.
  destruct H0. repeat right. intros. destruct H1. subst. auto.
  apply H. auto. do 2 right. left. exists a. split. left. auto.
  auto.
Qed.

Lemma MIS_bounds_ind_cases :
  forall G, 
    (exists x l,  In x (gV _ G) /\
                  (neighborhood_E T G x l) /\
                  NoDup l /\
                  length l = 0) \/
    (exists x l,  In x (gV _ G) /\
                  (neighborhood_E T G x l) /\
                  NoDup l /\
                  length l = 1) \/
    (exists x l,  In x (gV _ G) /\
                  (neighborhood_E T G x l) /\
                  NoDup l /\
                  length l >= 3) \/
    (forall x l, 
      In x (gV _ G) ->
      neighborhood_E T G x l ->
      NoDup l ->
      length l = 2).
Proof.
  intros.
  specialize (map_ind_cases 
                (fun x => length (genNeighborhood G x))
                (gV _ G)).
  intros.
  destruct H. left.
  do 2 destruct H. exists x, (genNeighborhood G x).
  split. auto. split. apply genNeighborhood_spec1.
  split. apply genNeighborhood_spec2. auto.
  destruct H. right. left.
  do 2 destruct H. exists x, (genNeighborhood G x).
  split. auto. split. apply genNeighborhood_spec1.
  split. apply genNeighborhood_spec2. auto.
  destruct H. do 2 right. left.
  do 2 destruct H. exists x, (genNeighborhood G x).
  split. auto. split. apply genNeighborhood_spec1.
  split. apply genNeighborhood_spec2. auto.
  repeat right. intros. erewrite neighborhood_E_NoDup_length_unique.
  apply H; eauto. auto. apply genNeighborhood_spec2. eauto.
  apply genNeighborhood_spec1.
Qed.

Lemma excise_0_degree_vert_aux :
  forall G x neigh l,
    (In x (gV _ G)) ->
    (neighborhood_E T G x neigh) ->
    (length neigh = 0) ->
    MaximalIndSet_E G l -> 
      In x l.
Proof.
  intros. assert (neigh = nil). destruct neigh.
  auto. simpl in H1. omega. subst.
  inversion H2. destruct (In_dec Tdec x l). auto.
  specialize (H4 _ H n). do 2 destruct H4.
  destruct H5.
  apply (gE_symm) in H6. apply H0 in H6. inversion H6.
Qed.

Lemma remove_idem : 
  forall x l, 
    remove Tdec x l = remove Tdec x (remove Tdec x l).
Proof.
  induction l. simpl; auto.
  simpl. destruct Tdec. apply IHl.
  simpl. destruct Tdec. congruence.
  rewrite <- IHl. auto.
Qed.

(* There is a strict equality here, but we only need one direction for
    the bounds we establish below *)
Lemma excise_0_degree_vert :
  forall G x l L L', 
    (In x (gV _ G)) ->
    (neighborhood_E T G x l) ->
    (length l = 0) ->
    MIS_set_gGraph G L -> 
    MIS_set_gGraph (removeVerts T Tdec G (x::nil)) L' ->
    length L <= length L'.
Proof.
  generalize Prop4_aux2, NoDupA_subset_length. intros.
  transitivity (length (map (fun l => remove Tdec x l) L)).
  apply Nat.eq_le_incl. symmetry.
  apply map_length.
  apply NoDupA_subset_length with (R := equivlistA eq).
  apply list_eq_dec. exact Tdec. 
  apply equivlist_equiv. apply eq_equivalence. 
  apply remove_NoDupA. inversion H4. auto.
  intros. eapply excise_0_degree_vert_aux; eauto.
  apply H4. auto. intros.
  assert (~ In x x0).
  { apply InA_alt in H6.
    do 2 destruct H6. apply in_map_iff in H7. 
    do 2 destruct H7. intros Hcontra.
    subst.
    assert (InA eq x x0). apply InA_alt.
    exists x. split; auto. apply H6 in H7.
    eapply remove_In.
    apply InA_alt in H7. do 2 destruct H7. subst. exact H9.
  }
  apply AllInA_remove_undo in H6.
  apply InA_alt in H6.
  do 2 destruct H6.
  inversion H5. apply H11.
  replace x0 with (remove Tdec x (x::x0)).
  apply Prop4_aux2. left. auto.
  eapply listeq_preserves_MIS_E. symmetry. eauto.
  apply H4. eauto. assert (l = nil).
  destruct l. auto. simpl in H3. omega.
  subst. auto. simpl. destruct Tdec; try congruence.
  apply remove_id. auto.
  intros. eapply excise_0_degree_vert_aux; eauto.
  apply H4. auto.
Qed.

Lemma MIS_exists : 
  forall G, 
    exists (l : list (list T)), MIS_set_gGraph G l.
Proof. 
  apply MIS_exists; auto.
Qed.

Definition BigSum_nat {X : Type} (l : list X) (f : X -> nat):=
  fold_right plus 0 (map f l).

Lemma BigSum_step  {X : Type} :
  forall (l : list X) x f,
  BigSum_nat (x::l) f = f x + BigSum_nat l f.
Proof.
  intros. unfold BigSum_nat.
  simpl. auto.
Qed.

Lemma BigSum_nat_map_rewrite {X Y : Type} :
  forall l f_count (fm1 fm2 : Y -> X),
    (forall x, In x l -> f_count (fm1 x) <= f_count (fm2 x)) ->
      BigSum_nat (map fm1 l) f_count <= 
      BigSum_nat (map fm2 l) f_count .
Proof.
  induction l. intros.
  simpl. auto.
  intros. simpl. unfold BigSum_nat. simpl.
  apply Nat.add_le_mono.
  apply H. left. auto.
  apply IHl. intros. apply H. right. auto.
Qed.

Definition list_excised_MIS_step G x : list (list T) :=
  AllMIS _ Tdec (removeVerts T Tdec G (x::(genNeighborhood G x))).

Definition list_excised_MIS G x :=
  map (fun k => list_excised_MIS_step G k) (x::genNeighborhood G x).

Lemma list_excised_MIS_gen_spec :
  forall G l k,
    (forall x, In x l -> In x (gV _ G)) ->
    (forall x neigh, In x l -> NoDup neigh -> neighborhood_E T G x neigh ->
      length (x::neigh) >= k) ->
    (forall L, In L (map (fun k => list_excised_MIS_step G k) l) ->
      exists G', (length (gV _ G') < length (gV _ G) /\
                 MIS_set_gGraph G' L) /\
                 length (gV _ G') + k<= length (gV _ G)).
Proof.
  intros.
  induction l. simpl in H1. inversion H1.
  simpl in H1.
  destruct H1. unfold list_excised_MIS_step in H1.
  exists (removeVerts T Tdec G (a :: genNeighborhood G a)).
  split. split. 
  simpl. 
  eapply le_lt_trans.
  apply removeList_length_le.
  apply remove_length_lt.
  apply H. left. auto. simpl.
  rewrite <- H1. apply AllMIS_spec.
  replace (gV T (removeVerts T Tdec G (a :: genNeighborhood G a)))
    with (removeList T Tdec(gV T G) (a :: genNeighborhood G a)) by auto.
  erewrite <- length_removeList_all_in with (l := gV T G).
  apply plus_le_compat_l.
  apply H0. left. auto. auto.
  apply genNeighborhood_spec2.
  apply genNeighborhood_spec1.
  apply gV_simplset.
  constructor. intros Hcontra.
  apply genNeighborhood_spec1 in Hcontra.
  apply gE_irref in Hcontra. auto.
  apply genNeighborhood_spec2.
  intros. destruct H2. subst. auto.
  apply H. left. auto. apply genNeighborhood_spec1 in H2.
  eapply gE_subset_l. eauto.
  apply IHl. intros. apply H. right. auto.
  intros. apply H0. right. auto. auto. auto.
  auto.
Qed.


Fixpoint find_b x l :=
match l with
| nil => false
| y :: l' => if Tdec x y then true else (find_b x l')
end.

Lemma find_b_spec :
  forall x l, find_b x l = true <-> In x l.
Proof.
  intros. induction l; simpl; split; intros.
  congruence. inversion H. destruct Tdec in H.
  left. auto. right. apply IHl. auto.
  destruct Tdec. auto. apply IHl. destruct H.
  congruence. auto.
Qed. 

Lemma In_map_remove_not_in :
  forall x l L,
    In l (map (fun l' => remove Tdec x l') L) ->
    ~ In x l.      
Proof.
  intros. induction L.
  simpl in H. inversion H.
  simpl in H. destruct H. subst.
  apply remove_In. apply IHL.
  auto.
Qed.

Lemma big_sum_NoDup_excise :
  forall (l : list T) x f ,
    NoDup l ->
    In x l ->
    BigSum_nat l f = BigSum_nat (remove Tdec x l) f + f x.
Proof.
  induction l. intros.
  inversion H0.
  intros. destruct H0. subst.
  rewrite BigSum_step. simpl.
  destruct Tdec. rewrite remove_id. omega.
  inversion H. auto. congruence.
  simpl.  destruct Tdec. subst. inversion H. congruence.
  do 2 rewrite BigSum_step. rewrite (IHl x). omega.
  inversion H. auto. auto.
Qed.

Lemma big_sum_func_equiv {X : Type} : 
  forall (l : list X) f1 f2,
    (forall x, In x l -> f1 x = f2 x) ->
    BigSum_nat l f1 = BigSum_nat l f2.
Proof.
  induction l. intros. simpl. auto.
  intros. do 2 rewrite BigSum_step.
  erewrite IHl. rewrite H. reflexivity. left. auto.
  intros. apply H. right. auto.
Qed.

Lemma big_sum_length_disjoint_split :
  forall l1 (l2 : list T),
    NoDup l2 ->
    (forall l,
      In l l1 ->
      (exists x, In x l2 /\ In x l /\ (forall x', x' <> x -> In x l2 -> ~ In x l))) ->
    length l1 = BigSum_nat l2 (fun x => length (filter (find_b x) l1)).
Proof.
  intros l1.
  induction l1; intros.
  simpl. induction l2. simpl. auto.
  rewrite BigSum_step. rewrite <- IHl2. omega.
  inversion H; auto.
  intros. inversion H1.
  simpl (length (a::l1)).
  rewrite (IHl1 l2). 
  assert (In a (a::l1)) by (left; auto).
  apply H0 in H1.
  do 2 destruct H1. destruct H2.
  rewrite (big_sum_NoDup_excise) with (x := x); auto.
  rewrite (big_sum_NoDup_excise l2 x); auto.
  assert (BigSum_nat (remove Tdec x l2)
                     (fun x0 : T => length
                        (filter (find_b x0) (a :: l1))) =
          BigSum_nat (remove Tdec x l2)
                     (fun x0 : T => length
                        (filter (find_b x0) (l1)))).
  {
    apply big_sum_func_equiv. intros.
    simpl. case_eq (find_b x0 a); intros.
    apply find_b_spec in H5.
    apply False_rec.
    apply (H3 x0); try auto.
    apply remove_mem in H4. destruct H4. auto.
    auto.
  }
  rewrite <- H4.
  replace (length (filter (find_b x) (a :: l1)))
    with (S (length (filter (find_b x) l1))).
  omega.
  simpl.
  case_eq (find_b x a); intros. simpl; omega.
  apply False_rec. apply find_b_spec in H2. congruence.
  auto.
  intros. apply H0. right. auto.
Qed.

Lemma big_sum_func_ge {X : Type} : 
  forall (l : list X) f1 f2,
    (forall x, In x l -> f1 x <= f2 x) ->
  BigSum_nat l f1 <= BigSum_nat l f2.
Proof.
  intros l. induction l.
  intros. auto.
  intros. do 2 rewrite BigSum_step.
  assert (BigSum_nat l f1 <= BigSum_nat l f2).
  apply IHl. intros. apply H. right. auto.
  assert (In a (a::l)). left. auto. apply H in H1. omega.
Qed. 

Lemma big_sum_inj_bound : 
  forall l1 (l2 : list T),
    (forall l, In l l1 -> exists x, In x l2 /\ In x l) ->
    (NoDup l2) ->
    length l1 <= BigSum_nat l2 (fun x => length (filter (find_b x) l1)).
Proof.
  intros l1.
  induction l1. intros. simpl.
  clear H. induction l2. simpl; auto.
  rewrite BigSum_step. omega.
  intros. 
  etransitivity. simpl. apply le_n_S.
  apply IHl1. intros. apply (H l). right. auto.
  clear IHl1. auto. 
  assert (In a (a::l1)) by (left; auto).
  apply H in H1. do 2 destruct H1.
  rewrite (big_sum_NoDup_excise) with (x := x); auto.
  rewrite (big_sum_NoDup_excise l2) with (x := x); auto.
  assert (length (filter (find_b x) l1) <
          length (filter (find_b x) (a :: l1))).
  simpl. case_eq (find_b x a); intros. 
  simpl. omega. apply find_b_spec in H2. congruence.
  assert ((BigSum_nat (remove Tdec x l2)
            (fun x0 : T => length (filter (find_b x0) l1)) <=
          (BigSum_nat (remove Tdec x l2)
            (fun x0 : T => length (filter (find_b x0) (a::l1)))))).
  apply big_sum_func_ge.
  intros. simpl. destruct find_b; simpl; omega. omega.
Qed.

Lemma map_step {X U : Type}:
  forall (x: X) l (f: X -> U),
    map f (x::l) = f x :: map f l.
Proof. intros. simpl. auto. Qed.

Lemma big_sum_map_index {X Y : Type} :
  forall (l : list X) (f_map : X -> Y) f_count,
    BigSum_nat l (fun x => f_count (f_map x)) =
    BigSum_nat (map f_map l) f_count.
Proof.
  intros.
  induction l. simpl. auto.
  simpl.
  do 2 rewrite BigSum_step. rewrite IHl. auto.
Qed.  

Lemma isElemMember : forall (l1 l2 : list T),
  (forall x, In x l2 -> ~ In x l1) \/ (exists x, In x l2 /\ In x l1).
Proof.
  induction l2. left. intros. inversion H.
  destruct (In_dec Tdec a l1). right. exists a. split. left. auto.
  auto. destruct IHl2. left. intros. destruct H0; subst. auto.
  auto. do 2 destruct H. right. exists x. split. right. auto. auto.
Qed.

Lemma neighMISWitness : 
  forall G (x : T) l neigh,
    MaximalIndSet_E G l ->
    In x (gV _ G) ->
    (neighborhood_E T G x neigh) ->
      exists x', In x' (x::neigh) /\ In x' l.
Proof.
  intros.
  destruct (isElemMember l (x::neigh)).
  apply False_rec.
  assert (In x (x::neigh)) by (left; auto).
  apply H2 in H3. inversion H. 
  specialize (H5 _ H0 H3).
  do 2 destruct H5. 
  destruct H6. apply H2 in H6. auto.
  right. apply H1. apply (gE_symm). auto.
  do 2 destruct H2.
  exists x0. repeat split; auto.
Qed.

Lemma WoodIneq_aux : 
  forall l G x,
    In x (gV _ G) ->
    MIS_set_gGraph G l ->
    length l <= BigSum_nat (list_excised_MIS G x) (@length (list T)).
Proof.
  intros.
  etransitivity.
  2:{ apply BigSum_nat_map_rewrite with
        (fm1 := fun v => (filter (fun l' => (find_b v l')) l)).
      intros. 
      replace (length (filter (fun l' : list T => find_b x0 l') l)) with
              (length (map (fun l' => remove Tdec x0 l')
                (filter (fun l' : list T => find_b x0 l') l))).
      2:{ apply map_length. }
      apply NoDupA_subset_length with (R := equivlistA eq).
      apply list_eq_dec. apply Tdec.
      apply equivlist_equiv. apply eq_equivalence.
      apply remove_NoDupA. apply filter_NoDupA. 
      inversion H0. auto.
      intros. apply filter_In in H2. destruct H2.
      apply find_b_spec. auto.
      intros.
      unfold list_excised_MIS_step.
      specialize (AllMIS_spec _ Tdec
        (removeVerts T Tdec G (x0 :: genNeighborhood G x0))).
      intros. apply H3.
      apply listeq_preserves_MIS_E with (l1 := remove Tdec x0 (x0::x1)).
      simpl. destruct Tdec; try congruence. rewrite remove_id. reflexivity.
      intros Hcontra. apply InA_alt in H2. destruct H2. destruct H2.
      assert (InA eq x0 x1). apply InA_alt. exists x0. split; auto.
      apply H2 in H5. 
      apply InA_alt in H5.
      destruct H5. destruct H5. repeat subst.
      apply In_map_remove_not_in in H4. congruence.
      apply Prop4_aux2. left. auto.
      apply AllInA_remove_undo in H2.
      apply filter_InA in H2. destruct H2.
      apply InA_alt in H2. do 2 destruct H2.
      eapply listeq_preserves_MIS_E. symmetry. apply H2.
      apply H0. auto. intros a b Hp.
      case_eq (find_b x0 a). intros.
      apply find_b_spec in H5. symmetry. 
      apply find_b_spec. assert (InA eq x0 a).
      apply InA_alt. exists x0. split; auto.
      apply Hp in H6. apply InA_alt in H6.
      do 2 destruct H6; subst. auto.
      intros Hcontra.
      case_eq (find_b x0 b). intros.
      apply find_b_spec in H5.
      assert (InA eq x0 b). apply InA_alt.
      exists x0. split; auto. apply Hp in H6.
      apply InA_alt in H6. do 2 destruct H6; subst.
      apply find_b_spec in H7. congruence.
      intros. auto.
      intros. apply filter_In in H4.
      destruct H4. apply find_b_spec in H5. auto.
      apply genNeighborhood_spec1.
  }
  {
    rewrite <- big_sum_map_index.
    etransitivity. apply big_sum_inj_bound.
    intros.
    generalize (@neighMISWitness G x l0 (genNeighborhood G x)).
    intros. destruct H2; try auto. apply H0. auto.
    apply genNeighborhood_spec1. destruct H2. exists x0. split.
    exact H2. exact H3. constructor.
    intros Hcontra. apply genNeighborhood_spec1 in Hcontra.
    apply gE_irref in Hcontra. auto.
    apply genNeighborhood_spec2.
    apply big_sum_func_ge. intros.
    clear H1 H0. induction l. simpl. auto.
    simpl. destruct find_b; simpl; omega.
  }
Qed.
Print Assumptions WoodIneq_aux.

Lemma MIS_Bounds_2_verts :
  forall G (l : list (list T)) t1 t2,
    MIS_set_gGraph G l -> 
    (gV _ G) = t1::t2::List.nil ->
    length l <= 2.
Proof.
  intros G l t1 t2 H H2.
  eapply Nat.le_trans.
  apply (WoodIneq_aux l G t1); auto.
  { rewrite H2; left; auto. }
  unfold list_excised_MIS.
  unfold list_excised_MIS_step.
  simpl.
  unfold BigSum_nat.
  simpl.
  assert (X: genNeighborhood G t1 = nil \/
             genNeighborhood G t1 = t2::nil).
  {  admit. }
  destruct X as [X|X].
  { rewrite X.
    simpl.
    rewrite <-plus_n_O.
    generalize (AllMIS_spec _ Tdec (removeVerts T Tdec G (t1::nil))); intro Y.
    apply (MIS_bounds_1_verts _ _ t2) in Y; eauto.
    { rewrite Y; omega. }
    simpl; rewrite H2; simpl.
    destruct (Tdec t1 t1); try congruence. clear e.
    destruct (Tdec t1 t2); auto.
    subst t1. generalize (gV_simplset _ G). rewrite H2. inversion 1.
    subst. exfalso; apply H4; left; auto. }
  rewrite X; simpl.
  assert (length (AllMIS T Tdec (removeVerts T Tdec G (t1 :: t2 :: nil))) = 1) as ->.
  { generalize (AllMIS_spec _ Tdec (removeVerts T Tdec G (t1 :: t2 :: nil))). intro Y.
    apply MIS_Bounds_0_verts in Y; auto.
    simpl; rewrite H2; simpl.
    destruct (Tdec t1 t1); try congruence. clear e.
    destruct (Tdec t1 t2); auto.
    simpl. destruct (Tdec t2 t2); try congruence. clear e. auto. }
  rewrite <-plus_n_O.
  assert (length (AllMIS T Tdec (removeVerts T Tdec G (t2 :: genNeighborhood G t2))) = 1) as ->.
  { generalize (AllMIS_spec _ Tdec (removeVerts T Tdec G (t2 :: t1 :: nil))). intro Y.
    apply MIS_Bounds_0_verts in Y; auto.
    { assert (genNeighborhood G t2 = t1 :: nil) as ->.
      { admit. }
      auto. }
    simpl; rewrite H2; simpl.
    destruct (Tdec t1 t1); try congruence. clear e.
    destruct (Tdec t2 t1); auto.
    { destruct (Tdec t2 t2); try congruence. auto. }
    simpl.
    destruct (Tdec t1 t1); try congruence. clear e.
    destruct (Tdec t2 t2); try congruence. auto. }
  omega.
Admitted. 

Require Import Reals.
Require Import Omega.
Require Import Fourier.
Open Scope R_scope.

Definition BigSum_R {X : Type} l (f : X -> R) :=
  fold_right Rplus 0 (map f l).

Lemma BigSum_R_step {X : Type} :
  forall (x : X) l f, 
    BigSum_R (x::l) f = f x + BigSum_R l f.
Proof. auto. Qed.

Lemma BigSum_nat_as_BigSumR :
  forall {X : Type} l (f : X -> nat),
    INR (BigSum_nat l f) = BigSum_R l (fun x => (INR (f x))).
Proof.
  intros. induction l. auto.
  rewrite BigSum_step. rewrite BigSum_R_step.
  rewrite <- IHl. apply plus_INR. 
Qed.
Check big_sum_func_ge.

Lemma big_sumR_func_ge {X : Type}:
  forall (l : list X) f1 f2,
    (forall x, List.In x l -> f1 x <= f2 x) ->
    BigSum_R l f1 <= BigSum_R l f2.
Proof.
  intros l. induction l.
  intros. compute. right. auto.
  intros. do 2 rewrite BigSum_R_step.
  assert (List.In a (a::l)) by (left; auto).
  apply Rplus_le_compat. apply H. left. auto.
  apply IHl. intros. apply H. right. auto.
Qed.

Lemma big_sumR_constant_length {X : Type} :
  forall (l : list X) x,
    BigSum_R l (fun _ => x) = (INR (length l)) * x.
Proof.
  intros. induction l.
  compute. ring. rewrite BigSum_R_step.
  simpl length. rewrite  IHl. rewrite S_INR.
  ring.
Qed.

Import ListNotations.

Lemma Bad_Bad: forall G (x:T), ((length (gV T (removeVerts T Tdec G [x]))) <= length (gV T G))%nat.
Proof.    
      unfold removeVerts.
      simpl.
      intros.
      induction (gV T G).
      simpl.
      omega.
      simpl.
      destruct (Tdec x a).
      { 
        assert ((length l) <= S (length l))%nat.
        omega.
        apply Nat.le_trans with (m:=length l).
        exact IHl.
        exact H.
      }
      {
        simpl.
        omega.  (* We love omega.   How did it just solve that! *)
      }
Qed.

Lemma MIS_Bounds :
  forall G (l : list (list T)),
    MIS_set_gGraph G l -> 
    INR (length l) <= I (length (gV _ G)).
Proof.
  intros G. induction G using GenGraph_StrongInd_aux.
  {
    intros. rewrite H. replace (I 0) with 1.
    simpl.
    inversion H0.
    assert (forall (x:T) (l1:list T), List.In l1 l -> ~List.In x l1).
    {
      intros.
      assert (MaximalIndSet_E G l1).
      apply H1.
      exact H4.
      assert ((gV T G) = []).
      apply length_zero_iff_nil.
      exact H.
      inversion H5.
      inversion H7.

      
      unfold valid_E in H9.
      rewrite H6 in H9.
      intro.
      assert (List.In x [] = False).
      simpl.
      reflexivity.
      assert (List.In x l1 -> List.In x []).
      apply H9.
      rewrite H12 in H13.
      apply H13.
      exact H11.
    }
    assert (forall l1:list T, List.In l1 l -> l1 = []).
    {
      intros.
      induction l1.
      reflexivity.
      assert (~List.In a (a :: l1)).
      apply H4.
      exact H5.
      simpl in H6.
      assert (a=a \/ List.In a l1).
      left; reflexivity.
      contradiction.
    }
    assert (length l <=1)%nat.
    {
      induction l.
      {
        simpl.
        omega.
      }
      {
        simpl.
        assert (a=[]).
        apply H5.
        simpl.
        left;reflexivity.
        inversion H2.
        assert (l = []).
        {
          induction l.
          reflexivity.
          assert (a0 = []).
          apply H5.
          simpl.
          right; left; reflexivity.
          rewrite H6 in H9.
          rewrite H11 in H9.
          assert (InA (equivlistA eq) [] ([] :: l)).
          constructor.
          constructor.
          intro; exact H12.
          intro; exact H12.
          contradiction.
        }
        rewrite H11.
        simpl.
        omega.
      }
      
    }
    replace 1 with (INR 1).
    apply le_INR.
    exact H6.
    simpl.
    reflexivity.
    unfold I.
    assert ((0 mod 3) = 0)%nat.
    simpl.
    reflexivity.
    rewrite H1.
    simpl.
    assert (0/3 = 0).
    field.
    rewrite H2.
    symmetry.
    apply Rpower_O.
    fourier.
    }
  
  destruct (Nat.le_gt_cases (length (gV T G)) 2).
  {
    inversion H1. clear H1. (* length = 2 *)
    {
      intros.
      remember (gV T G) as l_dest. 
      destruct l_dest. simpl in H3. omega.
      destruct l_dest. simpl in H3. omega. destruct l_dest. simpl in H3.
      eapply Rle_trans.
      apply le_INR. eapply MIS_Bounds_2_verts; eauto.
      unfold I. simpl. replace ((1+1-2) / 3) with 0 by field.
      rewrite Rpower_O. fourier. fourier. 
      simpl in H3. omega.
    }
    clear H1 H2. inversion H3. 
    { 
      intros. remember (gV T G) as l_dest.
      destruct l_dest. simpl in H3. simpl in H2. omega.
      destruct l_dest.
      eapply Rle_trans. 
      apply le_INR. erewrite MIS_bounds_1_verts; eauto.
      unfold I. simpl. replace ((1 - 4) / 3) with (-(1)).
      rewrite (Rpower_Ropp 3 1). rewrite Rpower_1. fourier.
      fourier. field. simpl in H2. omega.
    }
    {
      assert (length (gV T G) = 0)%nat by omega.
      intros. eapply Rle_trans. apply le_INR.
      assert (length (gV T G) = 0)%nat by omega.
      erewrite MIS_Bounds_0_verts; eauto. rewrite H4.
      unfold I. simpl. replace (0 / 3) with 0.
      rewrite Rpower_O. fourier. fourier. field.
    }
  }
  {
    generalize (MIS_bounds_ind_cases G); intros.
    destruct H2.
    { (* vert with degree 0 *)
      do 3 destruct H2. destruct H4.
      destruct H5.
      destruct (MIS_exists (removeVerts T Tdec G (x :: Datatypes.nil))).
      eapply Rle_trans. apply le_INR.
      eapply excise_0_degree_vert; eauto.
      eapply Rle_trans.
      apply H; eauto. apply lt_n_Sm_le.
      rewrite <- H0.
      replace (gV T (removeVerts _ Tdec G (x ::Datatypes.nil))) with
    (removeList _ Tdec (gV T G) (x::Datatypes.nil)) by auto.
    simpl. apply remove_length_in. auto.
    assert (forall x:T, (length (gV T (removeVerts T Tdec G [x]))) <= length (gV T G))%nat.
    { 
      unfold removeVerts.
      simpl.
      induction (gV T G).
      simpl.
      intro.
      reflexivity.
      intros.
      apply remove_length.
    }
(*** DWJ to here. *)
    apply I_monontonic2.  
    apply H8.
  }
    destruct H2.
    (** Start ***)
  { (* Vertices of degree 1. *)
    do 3 destruct H2. destruct H4. destruct H5.
    destruct x0. simpl in H6. omega.
    destruct x0. 
    Focus 2.
    { simpl in H6. omega. }
    Unfocus.
    destruct (MIS_exists (removeVerts T Tdec G (t :: Datatypes.nil))).
    destruct (MIS_exists (removeVerts T Tdec G (t :: genNeighborhood G t))).
    eapply Rle_trans. apply le_INR.
    apply Prop4_vatter with (G := G) (x := t) (Nx := genNeighborhood G t).
    eapply gE_subset_l. apply H4. left. auto. apply genNeighborhood_spec1.
    auto. exact H7. exact H8. rewrite plus_INR.
    apply Rle_trans with
        (r2 := ((I (length (gV T G) -2)) + (I (length (gV T G) -2)))).
      assert (List.In t [t]).
      simpl.
      left; reflexivity.
      assert (List.In (t, x) (gE T G)).
      apply H4.      
      exact H9.
      
  
      assert (List.In t (gV T G)).
      {
      apply gE_subset_l with (y:=x).
      exact H10.
      }
      assert (~List.In (x,x) (gE T G)).
      apply gE_irref.
      assert (x<>t).
      {
      intro.
      rewrite H13 in H12 at 1.
      contradiction.  
      }
    { assert (Hx: forall y0, MIS_set_gGraph (removeVerts T Tdec (removeVerts T Tdec G [t]) [x]) y0 ->
                             (length x0 <= length y0)%nat).
      { intros.
        apply excise_0_degree_vert with (G:=removeVerts T Tdec G [t]) (x:=x) (l:=[]).
        unfold removeVerts.
        simpl.
        apply remove_mem.
        split.
        exact H2.
        { 
      assert (List.In t [t] <-> List.In (t,x) (gE T G)).
      apply H4.
      assert (List.In t [t]).
      simpl.
      left; reflexivity.
      assert (List.In (t, x) (gE T G)).
      
      apply H10.
      exact H13. (* x<> t done!!! *)
      }
      (* assert (List.In t (gV T G)).
      apply gE_subset_l with (y:=x).
      exact H12.
      assert (~List.In (x,x) (gE T G)).
      apply gE_irref.
      intro.
      rewrite H15 in H14 at 1.
      contradiction.  
      }*)
      
      constructor.
      intros.
      
      simpl in H10.
      contradiction.
      assert (forall x2:T, ~List.In (x2, x) (gE T (removeVerts T Tdec G [t]))).
      { 
          unfold removeVerts.
          (* Arguments removePairs : simpl never. *)
          simpl.
          intros x3.
          intro.
          apply filter_In in H15.
          destruct H15.   (*** Thanks Alex B for the help. ***)
          assert (List.In x3 [t]).
          apply H4.
          exact H15.
          simpl in H17.
          destruct H17.
          rewrite <-H17 in H16.
          
          assert (isElemOfPair_b T Tdec t (t, x) = true).
          
          apply isElemOfPair_b_spec.
          simpl.
          left; reflexivity.
          rewrite H18 in H16.
          simpl in H16.
          inversion H16.
          contradiction.
        }
        assert (~
      List.In (x2, x) (gE T (removeVerts T Tdec G [t]))).
      apply H15.
        intro.
        contradiction.
        auto.
        exact H7.
        exact H14.
      }
        (* Here *)
    assert (List.In x (remove Tdec t (gV T G))).
      { simpl. 
      apply remove_mem.
      split.
      exact H2.
      exact H13.
      }
      
      assert ((length (remove Tdec x (remove Tdec t (gV T G)))) < length (remove Tdec t (gV T G)))%nat.
      { 
        apply remove_length_in.
        exact H14.
      }
      assert (length(remove Tdec t (gV T G)) < length (gV T G))%nat.
      { 
        apply remove_length_in.
        exact H11.
      }

                  
          
      
     
      
         
      
      
        

        
      destruct (MIS_exists (removeVerts T Tdec (removeVerts T Tdec G [t]) [x])) as [y0 Hy0].
      specialize (Hx _ Hy0).
      assert (INR(length x0) <= INR(length y0)).
      {
      apply le_INR.
      exact Hx.
      }
      apply Rle_trans with (r2:= INR(length y0) + INR (length x1)).
      fourier.
      
      apply Rplus_le_compat.
      { (* Two cases *)
      apply Rle_trans with
          (r2 := I (length (gV T (removeVerts T Tdec (removeVerts T Tdec G [t]) [x]) ))).
      apply H.
      unfold neighborhood_E in H4.
      
      unfold removeVerts.
      simpl.
      omega.
      (*assert (List.In t (gV T G)).
      assert (List.In t [t] <-> List.In (t,x) (gE T G)).
      apply H4.
      assert (List.In t [t]).
      simpl.
      left; reflexivity.
      assert (List.In (t, x) (gE T G)).
      apply H10.
      exact H11.*)
      (*apply gE_subset_l with (y:=x).
      exact H12.
      unfold removeVerts.
      simpl. *)
      
      
      exact Hy0.
      { (* case 2*) 
        assert (Hw:
        (length (gV T (removeVerts T Tdec (removeVerts T Tdec G [t])
           [x])) <= (length (gV T G) - 2))%nat).
        { 
          unfold removeVerts.
          simpl.
          omega.
        }
         
      apply I_monontonic2.
      exact Hw.
      }
      }
      
      assert (List.In x (genNeighborhood G t)). 
      {
        unfold genNeighborhood.
        unfold genNeighborhood_aux.
        assert (x = (snd (t,x))).
        auto.
        rewrite H18.
        apply in_map.
        apply filter_In.
        split.
        exact H10.
        unfold isFstElemOfPair.
        simpl.
        simpl.
        destruct Tdec.
        auto.
        contradiction.
      }
       
      assert (forall l1 l2, length((removeList T Tdec l2 l1)) <= length l2)%nat.     
      {
        induction l1.
        intros.
        simpl.
        omega.
        intros.
        simpl.
        assert (length (removeList T Tdec (remove Tdec a l2) l1) <= length (remove Tdec a l2))%nat.
        apply IHl1.
        assert (length (remove Tdec a l2)<= length l2)%nat.
        apply remove_length.
        omega.
      }
      
      assert (length(removeList T Tdec (remove Tdec t (gV T G))
      (genNeighborhood G t))+ length(genNeighborhood G t)=length (remove Tdec t (gV T G)))%nat.
      apply length_removeList_all_in.
      apply remove_NoDup.
      apply gV_simplset.
      apply genNeighborhood_spec2.
      assert (neighborhood_E T G t (genNeighborhood G t)).
      apply genNeighborhood_spec1.
      intros.
      unfold neighborhood_E in H20.
      apply H20 in H21.
      assert (x2 <> t).
      intro.
      rewrite H22 in H21.
      assert (~List.In (t,t) (gE T G)).
    
      apply gE_irref.
      contradiction.
      apply remove_mem.
      split.
      apply gE_subset_l with (y:=t).
      exact H21.
      exact H22.
      assert (length(remove Tdec t (gV T G)) < length(gV T G))%nat.
      apply remove_length_in.
      exact H11.
      assert (forall (x:T) (l: list T), List.In x l -> 1<=length l)%nat.
      {
        induction l0.
        {
          intros.
          simpl in H22.
          contradiction.
        }
        intros.
        simpl.
        omega.
      }
       
 
      assert (1<=length (genNeighborhood G t))%nat.
      apply H22 with (x:=x).
      auto.
      
      assert (length(gV T (removeVerts T Tdec G (t :: (genNeighborhood G t)))) <= length(gV T G) -2)%nat.
      simpl.
      omega.  
      
      assert (INR(length x1) <= I(length(gV T (removeVerts T Tdec G (t :: (genNeighborhood G t)))))).
      apply H.
      unfold removeVerts.
      simpl.
      omega.
      exact H8.
      assert (I(length
           (gV T
              (removeVerts T Tdec G
                 (t :: genNeighborhood G t)))) <= I(length (gV T G) - 2)).
      apply I_monontonic2.
      auto.
      apply Rle_trans with (r2:=I
        (length
           (gV T
              (removeVerts T Tdec G
                 (t :: genNeighborhood G t))))).
      auto.
      auto.
      
    }    

    
    replace (I (length (gV T G) - 2) + I (length (gV T G) - 2)) with (2*I (length (gV T G) - 2)) by field.
    apply I_lower_bound_1.
    omega.
  }
 
 destruct H2.
  {
    do 3 destruct H2. destruct H4. destruct H5.
    destruct (MIS_exists (removeVerts T Tdec G (x :: Datatypes.nil))).
    destruct (MIS_exists (removeVerts T Tdec G (x :: genNeighborhood G x))).
   assert (length(remove Tdec x (gV T G)) < length(gV T G))%nat.
      apply remove_length_in.
      exact H2.
    assert (length(removeList T Tdec (remove Tdec x (gV T G))
      (genNeighborhood G x))+ length(genNeighborhood G x)=length (remove Tdec x (gV T G)))%nat.
    {   
      apply length_removeList_all_in.
      apply remove_NoDup.
      apply gV_simplset.
      apply genNeighborhood_spec2.
      assert (neighborhood_E T G x (genNeighborhood G x)).
      apply genNeighborhood_spec1.
      intros.
      unfold neighborhood_E in H10.
      apply H10 in H11.
      assert (x3 <> x).
      intro.
      rewrite H12 in H11.
      assert (~List.In (x,x) (gE T G)).
    
      apply gE_irref.
      contradiction.
      apply remove_mem.
      split.
      apply gE_subset_l with (y:=x).
      exact H11.
      exact H12.
    }
   assert (length(remove Tdec x (gV T G)) < length(gV T G))%nat.
      apply remove_length_in.
      exact H2. 
    eapply Rle_trans. apply le_INR.
    apply Prop4_vatter with (G := G) (x := x) (Nx := genNeighborhood G x).
    auto. apply genNeighborhood_spec1. auto. eauto. eauto.
    rewrite plus_INR.
    apply Rle_trans with
      (r2 := I (length (gV T G) - 1) + I (length (gV T G) - 4)).
    assert (INR (length x1) <= I(length (gV T (removeVerts T Tdec G [x])))).
    apply H.
    unfold removeVerts.
    simpl.
    omega.
    exact H7.        

    assert (INR(length x2) <= I(length(gV T (removeVerts T Tdec G (x :: genNeighborhood G x))))).
    apply H.


    unfold removeVerts.
    simpl.
    omega.
    exact H8.
    assert (I(length
           (gV T
              (removeVerts T Tdec G
                 (x :: genNeighborhood G x))))<=I(length(gV T G) -4)).
    apply I_monontonic2.
    unfold removeVerts.
    simpl.
    assert (3<=length (genNeighborhood G x))%nat.
    {
      assert (neighborhood_E T G x (genNeighborhood G x)).
      apply genNeighborhood_spec1.
      assert (length (genNeighborhood G x) = length x0).
      apply neighborhood_E_NoDup_length_unique with (G:=G) (x:=x).
      apply genNeighborhood_spec2.
      exact H5.
      exact H14.
      exact H4.
      omega.
    }
    omega.
    assert (I (length (gV T (removeVerts T Tdec G [x]))) <= I(length(gV T G)-1)).
    apply I_monontonic2.
    unfold removeVerts.
    simpl.
    omega.
    fourier.
   
    apply I_lower_bound_2; auto.
  } (* Done with case d>=3 *)
  {
  {
    case_eq (gV T G); intros. rewrite H4 in H0. simpl in H0.
    omega. assert (List.In t (gV T G)). rewrite H4. left.
    auto.
    assert (exists k, (length (t::l0) = plus k 3)).
    {
      assert (length (genNeighborhood G t) = 2%nat).
      apply (H2 t). auto.
      apply genNeighborhood_spec1.
      apply genNeighborhood_spec2.
      remember (genNeighborhood G t) as l'.
      do 3 (destruct l'; simpl in H6; try omega).
      assert  (le (length[t;t0;t1]) (length (t::l0))).
      apply NoDup_incl_length.
      rewrite Heql'.
      constructor. intros Hcontra.
      apply genNeighborhood_spec1 in Hcontra.
      apply gE_irref in Hcontra. auto.
      apply genNeighborhood_spec2.
      intros t' H7. rewrite Heql' in H7.
      destruct H7. subst. left. auto.
      apply genNeighborhood_spec1 in H7.
      apply gE_subset_l in H7. rewrite <- H4.
      auto. simpl.
      do 2 (destruct l0; simpl in H7; try omega).
      simpl.
      exists (length l0). omega.
    }
    destruct H6.
    eapply Rle_trans. apply le_INR.
    apply WoodIneq_aux. apply H5. auto.
    rewrite H6. rewrite <- I_unfold.
    eapply Rle_trans.
    rewrite BigSum_nat_as_BigSumR.
    apply big_sumR_func_ge.
    2:{
      rewrite big_sumR_constant_length.
      replace (length (list_excised_MIS G t)) with 3%nat.
      rewrite Rmult_comm.
      replace (INR 3) with 3.
      apply Rmult_le_compat_r. fourier.
      apply Rle_refl. compute. ring.
      unfold list_excised_MIS.
      rewrite map_length. simpl. rewrite (H2 t).
      auto. auto. apply genNeighborhood_spec1.
      apply genNeighborhood_spec2.
    }
    intros. unfold list_excised_MIS in H7.
    apply list_excised_MIS_gen_spec with (k:=3%nat) in H7.
    do 3 destruct H7.
    eapply Rle_trans.
    apply H. 2:{ apply H9. }
    omega. apply I_monontonic2.
    etransitivity.
    eapply plus_le_reg_l.
    rewrite plus_comm.
    etransitivity. apply H8.
    rewrite H4. rewrite plus_comm.
    apply Nat.eq_le_incl. exact H6.
    omega. intros.
    destruct H8. subst. auto.
    apply genNeighborhood_spec1 in H8.
    eapply gE_subset_l. eauto.
    intros. simpl. rewrite (H2 x1).
    auto. destruct H8. subst. auto.
    apply genNeighborhood_spec1 in H8.
    eapply gE_subset_l. eauto. eauto.
    auto.
  }
}}
Qed.
End GraphInequalities.