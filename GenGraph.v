Require Import SetoidList Wellfounded Omega.
Section GenGraphs.

  Variable T : Type.

  Record GenGraph : Type :=
    mkGGraph { gV : list T;
               gE : list (T*T);
               gE_irref : forall x, ~ In (x, x) gE;
               gE_symm : forall x y, In (x, y) gE -> In (y ,x) gE;
               gV_simplset : NoDup gV;
               gE_simplset : NoDup gE;
               gE_subset_l : forall x y, In (x, y) gE -> In x gV;
            }.
  
  Lemma gE_subset_r G : forall x y, In (x, y) (gE G) -> In y (gV G).
  Proof.
    intros. apply gE_symm in H. eapply gE_subset_l. eauto.
  Qed.


  Lemma GenGraph_StrongInd_aux : 
      forall (P : (GenGraph -> Prop)),
        (forall G, (length (gV G) = 0) -> P G) ->
        (forall n, (forall G, length (gV G) <= n -> P G) -> 
                   (forall G, length (gV G) = S n -> P G)) ->
        forall G, P G.
    Proof.
      intros.
      apply well_founded_induction
        with (R:= fun g1 g2 => length (gV g1) < length (gV g2)).
      apply wf_inverse_image.
      apply PeanoNat.Nat.lt_wf_0.
      intros. 
      remember (gV x) as l.
      destruct l. apply H. rewrite <- Heql. auto.
      apply H0 with (n:= length l). intros. apply H1.
      simpl. omega. rewrite <- Heql. simpl. auto.
    Qed.
End GenGraphs.


  (* Given a list, this function maps the reversed indicies of the
      list to their corresponding elements.

    For example: 
      Input: [34::36::nil]
      Output : f := if 0 then 36
                    elif 1 then 34
                    else _.
  *)
  Program Definition FromRevIndexToInT {T : Type} (l : list T) 
    (pfX : {x : nat | x < length l}) : {t : T | In t l} :=
      match nth_error l (length l - (pfX + 1)) with
      | Some t => t
      | None => (False_rect _ _)
      end.
  Next Obligation.
    eapply nth_error_In. eauto.
  Qed.
  Next Obligation.
    symmetry in Heq_anonymous.
    apply nth_error_Some in Heq_anonymous; auto.    
    omega.
  Qed.

  Fixpoint find_at {T : Type}
    (Tdec : forall t1 t2 : T, {t1 = t2} + {t1 <> t2})
    (l : list T) (t : T) : option nat :=
  match l with
  | nil => None
  | cons x l' =>  if Tdec x t
                    then Some O
                    else
                      match find_at Tdec l' t with
                      | None => None
                      | Some n => Some (S n)
                      end
  end.

  Lemma find_at_None :
    forall T pf (l : list T) t,
      find_at pf l t = None <-> ~ In t l.
  Proof.
    induction l.
    intros. simpl; split; intros.
    intros Hcontra. auto. auto.
    intros. simpl. split; intros.
    intros Hcontra. destruct Hcontra.
    subst. destruct (pf t t) in H. congruence.
    apply n. auto. apply IHl in H0. auto.
    destruct (pf a t); try congruence.
    destruct (find_at pf l t); try congruence.
    destruct (pf a t). apply False_rec. apply H.
    left. auto.
    assert (~ In t l). intros Hcontra.
    apply H. right. auto. apply IHl in H0.
    rewrite H0. auto.
  Qed.

  Lemma find_at_Some : 
    forall T pf (l : list T) t,
      (exists x, find_at pf l t = Some x) <-> In t l.
  Proof.
    induction l.
    intros. split; intros.
    destruct H. simpl in H. congruence.
    inversion H.
    split; intros.
    destruct H. simpl in H.
    destruct (pf a t). left. auto.
    right. apply IHl.
    destruct (find_at pf l t). exists n0.
    auto. congruence.
    simpl. destruct (pf a t).
    subst. exists 0. auto. destruct H.
    congruence. apply IHl in H. destruct H.
    rewrite H. eauto.
  Qed.

  Lemma nth_error_nil : forall A n, @nth_error A nil n = None.
  Proof.
    intros. induction n. auto.
    simpl. auto.
  Qed.

  Lemma nth_error_Some_UB : 
    forall A n l x, @nth_error A l n = Some x -> 
      n < length l.
  Proof.
    induction n; intros.
    destruct l. inversion H. simpl. omega.
    destruct l. inversion H. simpl in H.
    apply IHn in H. simpl. omega.
  Qed.

  Lemma find_at_nth_error : 
    forall x T pf (l : list T) t,
      find_at pf l t = Some x -> nth_error l x = Some t.
  Proof.
    induction x. intros. simpl.
    destruct l. simpl in H. congruence.
    simpl in H. destruct (pf t0 t). rewrite e. auto.
    destruct (find_at pf l t). inversion H. congruence.
    intros. simpl. destruct l.
    simpl in H. congruence. simpl in H.
    destruct (pf t0 t). inversion H.
    apply IHx with (pf := pf). destruct (find_at pf l t).
    inversion H. auto. congruence.
  Qed.

  Lemma nth_error_find_error : 
    forall x T pf (l : list T) t,
      NoDup l -> nth_error l x = Some t -> find_at pf l t = Some x.
  Proof.
    induction x.
    intros. destruct l. simpl in H0.
    inversion H0. simpl in H0.
    inversion H0. subst. simpl. destruct (pf t t).
    auto. try congruence. 
    intros. destruct l. simpl in H0.
    congruence.
    simpl in H0.
    assert (t <> t0).
    intros Hcontra.
    specialize (nth_error_In _ _ H0). intros.
    inversion H; subst. congruence.
    simpl. destruct (pf t0 t).
    congruence. erewrite IHx. congruence.
    inversion H. auto. auto.
  Qed.


  Definition FromInTToRevIndex {T : Type}
    (pf : forall t1 t2 : T, {t1 = t2} + {t1 <> t2}) 
    (l : list T) (pfT : {t : T | In t l}) : {x : nat | x < length l}.
  Proof.
    destruct pfT.
    remember (find_at pf l x).
    destruct o.
    exists n. symmetry in Heqo.
    apply find_at_nth_error in Heqo.
    eapply nth_error_Some_UB. eauto.
    apply False_rec. symmetry in Heqo.
    apply find_at_None in Heqo. congruence.
  Defined.

Definition listAsSet {T : Type} (l : list T) :=
  NoDup l.

Definition independent_E {T : Type} (G : GenGraph T) (l : list T) : Prop :=
  forall x y, In x l -> In y l -> ~ In (x, y) (gE _ G).

Definition valid_E {T : Type} (G : GenGraph T) (l : list T) : Prop :=
  forall x, In x l -> In x (gV _ G).

Inductive IndSet_E {T : Type} (G : GenGraph T) (l : list T) : Prop :=
  mkIndSet_E : 
    valid_E G l ->
    independent_E G l ->
  IndSet_E G l.

Inductive MaximalIndSet_E {T : Type} (G : GenGraph T) (l : list T) : Prop :=
| mkMIS_E :
    IndSet_E G l ->
    (forall x, In x (gV _ G) -> ~ In x l ->
      (exists y, In y (gV _ G) /\
                 In y l /\
                 In (x, y) (gE _ G))) ->
    MaximalIndSet_E G l.

Lemma listeq_preserves_MIS_E :
  forall T (l1 l2 : list T) G,
    equivlistA eq l1 l2 ->
    (MaximalIndSet_E G l1) ->
    (MaximalIndSet_E G l2).
Proof.
  intros. 
  constructor.
  constructor. intros x H1. apply H0.
  assert (InA eq x l2). apply InA_alt.
  exists x; split; auto. apply H in H2.
  apply InA_alt in H2. do 2 destruct H2; subst; auto.
  intros x y H1 H2.
  inversion H0. apply H3.
  specialize (H x). assert (InA eq x l2).
  apply InA_alt. exists x; split; auto.
  apply H in H5. apply InA_alt in H5. do 2 destruct H5; subst.
  auto. 
  specialize (H y). assert (InA eq y l2).
  apply InA_alt. exists y; split; auto.
  apply H in H5. apply InA_alt in H5. do 2 destruct H5; subst.
  auto.
  intros. inversion H0.
  assert (~ In x l1).
  intros Hcontra. apply H2. assert (InA eq x l1).
  apply InA_alt. exists x. split; auto.
  apply H in H5. apply InA_alt in H5. do 2 destruct H5; subst.
  auto.
  specialize (H4 _ H1 H5).
  destruct H4. exists x0. repeat split.
  destruct H4. auto. destruct H4.
  destruct H6.
  assert (InA eq x0 l1). apply InA_alt.
  exists x0; split; auto. apply H in H8.
  apply InA_alt in H8. do 2 destruct H8; subst; auto.
  destruct H4. destruct H6. auto.
Qed.

Inductive ClosedNeighborhood
{T : Type} (G : GenGraph T) (v : T)  (l : list T) :=
| mkClosedNeighborhood :
  (forall x, In x l -> (In x (gV _ G))) ->  
  (In v l) -> 
  (forall x, In x l -> x <> v -> In (v, x) (gE _ G)) -> 
ClosedNeighborhood G v l.

Inductive OpenNeighborhood
{T : Type} (G : GenGraph T) (v : T)  (l : list T) :=
| mkOpenNeighborhood :
  In v (gV _ G) ->
  (forall x, In x l -> (In x (gV _ G))) ->  
  (forall x, In x l -> In (v, x) (gE _ G)) -> 
OpenNeighborhood G v l.

Fixpoint OpenNeighborhood_witness_aux
  {T : Type} (E : list (T * T)) (v : T)
  (Tdec : (forall t1 t2 : T, {t1 = t2} + {t1 <> t2})) : list T :=
match E with
| nil => nil
| p::E' =>
    match p with pair x y =>
    if (Tdec x v)
      then y::(OpenNeighborhood_witness_aux E' v Tdec)
      else (OpenNeighborhood_witness_aux E' v Tdec)
    end
end.

Definition OpenNeighborhood_witness T Tdec (G : GenGraph T) v :=
  OpenNeighborhood_witness_aux (gE _ G) v Tdec.

Lemma OpenNeighborhood_witness_aux_spec 
  {T : Type} (E : list (T * T)) (v : T)
  (Tdec : (forall t1 t2 : T, {t1 = t2} + {t1 <> t2})) :
    forall x, In x (OpenNeighborhood_witness_aux E v Tdec) ->
      In  (v, x) E.
Proof.
  induction E. intros.
  simpl in H. inversion H.
  simpl. intros. destruct a.
  destruct (Tdec t v); subst.
  destruct H; subst. left. auto.
  right. apply IHE. auto.
  right. apply IHE. auto.
Qed.

Lemma OpenNeighborhood_witness_spec :
  forall T Tdec G v, 
    In v (gV _ G) ->
    OpenNeighborhood G v (OpenNeighborhood_witness T Tdec G v).
Proof.
  intros. constructor. auto.
  intros.
  apply OpenNeighborhood_witness_aux_spec in H0.
  apply gE_subset_r in H0. auto.
  intros.  
  eapply OpenNeighborhood_witness_aux_spec.
  eauto.
Qed.


Section GraphSurgery.
  Variable T : Type.
  Variable Tdec : forall t1 t2 : T, {t1 = t2} + {t1 <> t2}.

  Fixpoint removeList (l r : list T) : list T :=
  match r with
  | nil => l
  | cons t r' => removeList (remove Tdec t l) r'
  end.

  Lemma remove_id : forall l r,
    ~ In r l ->
    remove Tdec r l = l.
  Proof.
    induction l; simpl; intros.
    auto.
    destruct Tdec. subst. apply False_rec.
    apply H. left. auto. f_equal.
    apply IHl. intros Hcontra. apply H.
    right. auto.
  Qed.

  Lemma remove_Subset : forall l r t,
    In t (remove Tdec r l) -> In t l.
  Proof.
    intros. induction l. simpl in H. auto.
    simpl in H. destruct Tdec; subst.
    right. apply IHl. auto.
    destruct H. left. auto.
    right. apply IHl. auto.
  Qed.

  Lemma remove_mem : forall l x t,
    In t (remove Tdec x l) <-> (In t l /\ ~ t = x).
  Proof.
    induction l.
    intros. split; intros. simpl in H. inversion H.
    destruct H. inversion H. intros; repeat split; intros.
    simpl in H. destruct Tdec in H. right. apply IHl in H.
    destruct H. auto. destruct H. left. auto. right.
    apply IHl in H. destruct H. auto.
    simpl in H. destruct Tdec in H. apply IHl in H.
    destruct H. auto. destruct H. subst. auto. apply IHl in H.
    destruct H. auto. simpl. destruct Tdec. apply IHl.
    destruct H. split. destruct H. congruence. auto.
    auto. destruct H. destruct H. left. auto. right.
    apply IHl. split. auto. auto.
  Qed.
  

  Lemma removeList_Subset : forall l r t, 
    In t (removeList l r) -> In t l.
  Proof.
    intros l r t. 
    generalize l t. clear l t.
    induction r. intros.
    simpl in H. auto.
    intros. simpl in H. 
    apply IHr in H.
    eapply remove_Subset. eauto.
  Qed.
  
  Lemma removeList_mem : forall l r t,
    In t (removeList l r) <-> 
      (In t l /\ forall x, In x r -> x <> t).
  Proof.
    intros l r. generalize dependent l.
    induction r. intros. simpl; repeat split; intros.
    auto. inversion H0. destruct H. auto.
    intros; repeat split; intros. simpl in H.
    apply IHr in H. destruct H. apply remove_Subset in H.
    auto. simpl in H. apply IHr in H.
    destruct H. intros Hcontra. subst.
    destruct H0. subst.
    eapply remove_In. eauto. apply (H1 _ H0). auto.
    simpl. apply IHr. split. apply remove_mem. destruct H. split.
    auto. intros Hcontra. eapply H0. left; eauto. auto.
    destruct H. intros. apply H0. right. auto.
  Qed.

  Lemma remove_NoDup : forall l r, NoDup l -> NoDup (remove Tdec r l).
  Proof.
    intros. induction l. simpl. auto.
    simpl. destruct Tdec; subst. apply IHl.
    inversion H. auto.
    constructor. inversion H; subst.
    intros Hcontra. apply H2. 
    apply remove_Subset in Hcontra. auto.
    apply IHl. inversion H; subst. auto.
  Qed.

  Lemma InA_remove_undo :
    forall l t,
      In t l ->
      (equivlistA eq l (t::(remove Tdec t l))).
  Proof.
    intros. constructor; intros.
    assert (In x (t::remove Tdec t l)).
    destruct (Tdec x t).
    left. auto. right.
    apply remove_mem. split. auto.
    apply InA_alt in H0. do 2 destruct H0. subst.
    auto. auto. apply InA_alt. exists x; split; auto.
    destruct (Tdec x t). subst. apply InA_alt.
    exists t; split; auto.
    apply InA_alt in H0.
    do 2 destruct H0; subst.
    inversion H1; subst; try congruence.
    apply remove_mem in H0. destruct H0.
    apply InA_alt. exists x0; split; auto.
  Qed.
  
  Lemma AllInA_remove_undo :
    forall L t,
      (forall l, In l L -> In t l) ->
      forall l', InA (equivlistA eq) l' (map (remove Tdec t) L) ->
        InA (equivlistA eq) (t::l') L.
  Proof.
    induction L. intros. inversion H0.
    intros. simpl in H0. inversion H0. subst.
    left. constructor. intros. inversion H1; subst.
    apply InA_alt. exists t; split; auto. apply H.
    left. auto. rewrite H2 in H4. apply InA_alt in H4.
    destruct H4. destruct H3. apply remove_Subset in H4. 
    apply InA_alt. exists x0. split; auto.
    intros. rewrite H2. destruct (Tdec x t).
    left. auto. right. apply InA_alt in H1. do 2 destruct H1.
    subst. apply InA_alt. exists x0. split; auto. apply remove_mem.
    split; auto. subst. right. apply IHL.
    intros. apply H. right. auto.
    auto.
  Qed.

  Lemma remove_NoDupA : 
    forall l x, 
      NoDupA (equivlistA eq) l -> 
      (forall l', In l' l -> In x l') ->
      NoDupA (equivlistA eq) (map (remove Tdec x) l).
  Proof.
    intros l x H. induction H; intros; subst. simpl. auto.
    simpl. constructor.
    intros Hcontra. apply H.
    assert (equivlistA eq x0 (x::remove Tdec x x0)).
    apply InA_remove_undo. apply H1. left. auto.
    rewrite H2. apply AllInA_remove_undo. intros. apply H1.
    right. auto. auto. apply IHNoDupA. intros. apply H1.
    right. auto.
  Qed.

  Lemma removeList_NoDup : forall l r, NoDup l -> NoDup (removeList l r).
  Proof.
    intros. generalize dependent l. induction r.
    intros. simpl. auto. simpl. intros.
    apply IHr. apply remove_NoDup. auto.
  Qed.

  Definition isElemOfPair_b (t : T) p :=
    if (Tdec t (fst p)) then true
    else if  (Tdec t (snd p)) then true
    else false.

  Lemma isElemOfPair_b_spec :
    forall t p, isElemOfPair_b t p = true <-> 
                (fst p = t \/ snd p = t).
  Proof.
    intros. destruct p.
    unfold isElemOfPair_b; simpl.
    destruct (Tdec t t0). split; auto.
    destruct (Tdec t t1); split; intros; auto;
    try congruence. inversion H; congruence.
  Qed.

  Fixpoint removePairs
    (l : list (T*T)) (r : list T) : list (T*T) :=
  match r with
  | nil => l 
  | cons t r' => removePairs
                  ((filter (fun x => (negb (isElemOfPair_b t x))) l)) r'
  end.

  Lemma removePairs_subset :
   forall t l r, In t (removePairs l r) -> In t l.
  Proof.
    intros t l r. generalize t l. clear t l.
    induction r; simpl; intros. auto.
    apply IHr in H. apply filter_In in H.
    destruct H. auto.
  Qed.

  Lemma filter_NoDup : 
    forall T (l : list T) f, NoDup l -> NoDup (filter f l).
  Proof.
    induction l. intros. simpl. auto.
    intros. simpl. destruct (f a).
    constructor. inversion H; subst. intros Hcontra.
    apply H2. apply filter_In in Hcontra. destruct Hcontra.
    auto. apply IHl. inversion H; subst; auto.
    apply IHl. inversion H; subst; auto.
  Qed.

  Lemma filter_NoDupA : 
    forall T (R : T -> T -> Prop)
           (l : list T) f, NoDupA R l -> NoDupA R (filter f l).
  Proof.
    induction l. intros. simpl. auto.
    intros. simpl. destruct (f a).
    constructor. intros Hcontra.
    apply InA_alt in Hcontra.
    destruct Hcontra. destruct H0.
    apply filter_In in H1.
    inversion H; subst. apply H4.
    apply InA_alt. exists x. split; auto.
    destruct H1; auto.
    inversion H; subst. eapply IHl in H3.
    eauto. inversion H; subst.
    eapply IHl. eauto.
  Qed.

  Lemma removePairs_NoDup :
    forall l r, NoDup l -> NoDup (removePairs l r).
  Proof.
    intros. generalize dependent l.
    induction r. intros. simpl. auto.
    intros. simpl. apply IHr. 
    apply filter_NoDup. auto.
  Qed.

  Lemma removePairs_mem : 
    forall t l r, In t (removePairs l r) <->
                  (In t l /\
                  (forall x, In x r -> ~ (fst t = x)) /\
                  (forall x, In x r -> ~ (snd t = x))).
  Proof.  
    intros t l r. generalize t l. clear t l.
    induction r. intros. split; simpl; intros.
    split; intros; auto. destruct H; auto.
    intros; split; intros; auto.
    repeat split. apply removePairs_subset in H. auto.
    intros. destruct H0.
    simpl in H.
    apply removePairs_subset in H. apply filter_In in H.
    destruct H. subst. unfold isElemOfPair_b in H1.
    destruct Tdec in H1. simpl in H1. congruence. auto.
    simpl in H. apply IHr in H. 
    destruct H. destruct H1. apply H1. auto.
    intros. destruct H0.
    simpl in H.
    apply removePairs_subset in H. apply filter_In in H.
    destruct H. subst. unfold isElemOfPair_b in H1.
    destruct Tdec in H1. simpl in H1. congruence.
    destruct Tdec in H1. simpl in H1. congruence. auto.
    simpl in H. apply IHr in H. 
    destruct H. destruct H1. apply H2. auto.
    simpl. apply IHr; split. apply filter_In.
    split. destruct H. auto.
    unfold isElemOfPair_b. destruct Tdec. destruct H. destruct H0.
    apply False_rec. apply (H0 a). left. auto. auto.
    destruct Tdec. destruct H. destruct H0. apply False_rec. apply (H1 a).
    left. auto. auto. auto.
    destruct H. destruct H0. split. intros. apply H0. right. auto.
    intros. apply H1. right. auto.
  Qed.


  Program Definition removeVerts (G : GenGraph T) (l : list T)
  : GenGraph T :=
  mkGGraph T (removeList (gV _ G) l)
           (removePairs (gE _ G) l) _ _ _ _ _.
  Next Obligation.
    intros Hcontra. apply removePairs_subset in Hcontra.
    apply (gE_irref _ G _ Hcontra).
  Qed.
  Next Obligation.
    apply removePairs_mem in H.
    destruct H.
    apply (gE_symm _ G) in H.
    apply removePairs_mem. split.
    auto. split; destruct H0;  simpl in *; auto.
  Qed.
  Next Obligation.
    apply removeList_NoDup. apply gV_simplset. 
  Qed.
  Next Obligation.
    apply removePairs_NoDup. apply gE_simplset.
  Qed.
  Next Obligation.
    apply removePairs_mem in H.
    apply removeList_mem. split. 
    destruct H. apply gE_subset_l in H. auto. 
    destruct H. destruct H0. intros. simpl in *.
    intros Hcontra. eapply H0; eauto.
  Qed.


Inductive MIS_set_gGraph {T : Type} (G : GenGraph T) (l : list (list T)) :=
| mkMIS_set : 
    (forall x, In x l -> MaximalIndSet_E G x) ->
    (NoDupA (equivlistA eq) l) ->
    (forall x, MaximalIndSet_E G x -> InA (equivlistA eq) x l) ->
      MIS_set_gGraph G l.
 
Lemma Prop4_aux1 : 
  forall G x l,
    MaximalIndSet_E G l ->
    (In x (gV _ G)) ->
    ~ (In x l) -> 
    MaximalIndSet_E (removeVerts G (x::nil)) l.
Proof.
  intros. constructor. constructor.
  inversion H. inversion H2. intros x0 H6.
  replace (gV T (removeVerts G (x :: nil))) with
    (removeList (gV _ G) (x::nil)) by auto.
  apply removeList_mem. split. apply H4. auto.
  intros. intros Hcontra. subst. inversion H7. subst. congruence.
  inversion H8.
  unfold independent_E.
  intros.
  replace (gE T (removeVerts G (x :: nil))) with
    (removePairs (gE _ G) (x::nil)) by auto.
  intros Hcontra. apply removePairs_subset in Hcontra.
  inversion H. inversion H4. apply (H7 x0 y); auto.
  replace (gV T (removeVerts G (x :: nil))) with
    (removeList (gV _ G) (x::nil)) by auto.
  replace (gE T (removeVerts G (x :: nil))) with
    (removePairs (gE _ G) (x::nil)) by auto.
  intros.
  assert (In x0 (gV T G)).
  apply removeList_Subset in H2. auto.
  inversion H. specialize (H6 _ H4 H3).
  destruct H6. exists x1. split.
  apply removeList_mem. split. destruct H6.
  auto. intros x' H7 H8. subst. apply H1.
  inversion H7. subst. destruct H6. destruct H8. auto.
  inversion H8. repeat split.
  destruct H6. destruct H7. auto.
  apply removePairs_mem. split. destruct H6.
  destruct H7. auto. split; simpl; intros.
  destruct H7; try congruence; subst.
  apply removeList_mem in H2.
  destruct H2. intros Hcontra; subst. eapply H7; eauto.
  left. auto. destruct H7; try congruence. subst. 
  intros Hcontra. subst. apply H1. destruct H6.  
  destruct H7. auto.
Qed.

Definition neighborhood_E (G : GenGraph T) (v : T) (l : list T) : Prop :=
  forall x, In x l <-> In (x, v) (gE _ G).

Lemma Prop4_aux2 :
  forall G l neigh x,
    In x l ->
    MaximalIndSet_E G l ->
    neighborhood_E G x neigh ->
    MaximalIndSet_E
      (removeVerts G (x::neigh))
      (remove Tdec x l).
  Proof.
    constructor. constructor.
    intros x0 H2. 
    replace (gV T (removeVerts G (x :: neigh))) with
      (removeList (gV _ G) (x::neigh)) by auto.
    apply removeList_mem. split. inversion H0.
    inversion H3. apply H3. eapply remove_Subset. eauto.
    intros. intros Hcontra. subst. destruct H3. subst.
    apply remove_mem in H2. destruct H2. congruence.
    inversion H0. eapply H4. apply remove_mem in H2.
    destruct H2. apply H2.  apply H. apply H1. auto.
    inversion H0. inversion H2.
    replace (gE T (removeVerts G (x :: neigh))) with
      (removePairs (gE _ G) (x::neigh)) by auto.
    unfold independent_E; intros.
    intros Hcontra.
    apply remove_Subset in H6. 
    apply remove_Subset in H7.
    apply removePairs_mem in Hcontra.
    eapply H2. apply H6. apply H7.
    destruct Hcontra. auto.
    replace (gE T (removeVerts G (x :: neigh))) with
      (removePairs (gE _ G) (x::neigh)) by auto.
    replace (gV T (removeVerts G (x :: neigh))) with
      (removeList (gV _ G) (x::neigh)) by auto.
    intros.
    inversion H0. assert (In x0 (gV T G)).
    apply removeList_mem in H2. destruct H2. auto.
    assert (~ In x0 l). auto.
    intros Hcontra. apply H3.
    apply remove_mem. split. auto. intros Hcontra'.
    apply removeList_mem in H2. subst.
    destruct H2. eapply H7. left. eauto. auto.
    specialize (H5 _ H6 H7).
    destruct H5. destruct H5. destruct H8.
    exists x1. assert (x1 <> x).
    assert (~ In (x0, x) (gE T G)).
    apply removeList_mem in H2.
    intros Hcontra. destruct H2.
    unfold neighborhood_E in H1. apply H1 in Hcontra.
    eapply H10. right. apply Hcontra. auto. intros Hcontra.
    subst. congruence. split. 
    apply removeList_mem. split. auto. intros. inversion H11.
    subst. auto. intros Hcontra.
    inversion H0; subst. inversion H4.
    specialize (H16 x1 x H8 H).
    apply H1 in H12. congruence. 
    split. apply remove_mem. split; auto.
    apply removePairs_mem. repeat split. auto.
    all: simpl; intros. intros Hcontra. subst.
    destruct H11. subst. apply removeList_mem in H2.
    destruct H2. eapply H11. left. auto. auto.
    apply removeList_mem in H2. destruct H2.
    eapply H12. right. apply H11. auto.
    destruct H11. subst. auto.
    intros Hcontra. subst. inversion H0.
    inversion H12.
    specialize (H15 x2 x H8 H). apply H15.
    apply H1 in H11. auto.
  Qed.

Lemma remove_length :
  forall l t,
    length (remove Tdec t l) <= length l.
Proof.
  induction l. intros. simpl. omega.
  intros. simpl. destruct Tdec. subst.
  etransitivity. apply IHl. omega.
  simpl. specialize (IHl t). omega.
Qed.

Lemma remove_length_in :
  forall l t,
    In t l ->
    length (remove Tdec t l) < length l.
Proof.
  induction l.
  intros. simpl. inversion H. 
  intros. 
  simpl. destruct Tdec; subst.
  specialize (remove_length l a). intros.
  omega. simpl.
  destruct H. congruence. apply IHl in H.
  omega.
Qed.

Lemma remove_length_le: forall l t,
  length (remove Tdec t l) <= length l.
Proof.
  induction l. simpl. auto.
  intros. simpl. destruct Tdec; specialize (IHl t);
  subst; simpl; omega.
Qed.

Lemma remove_length_lt : forall l t,
  In t l -> length (remove Tdec t l) < length l.
Proof.
  induction l. intros. inversion H.
  intros. destruct H. subst. simpl. destruct Tdec.
  subst. specialize (remove_length_le l t); intros.
  omega. congruence. simpl. destruct Tdec; simpl;
  specialize (IHl _ H); omega.
Qed.

Lemma removeList_length_le: forall l l',
  length (removeList l' l) <= length l'.
Proof.
  induction l; intros. simpl. omega.
  simpl. etransitivity. apply IHl. 
  apply remove_length_le.
Qed.

Lemma remove_commute : 
  forall l t1 t2,
    remove Tdec t1 (remove Tdec t2 l) = 
    remove Tdec t2 (remove Tdec t1 l).
Proof.
  induction l. simpl. auto.
  intros. simpl. do 2 destruct Tdec; subst.
  auto. try rewrite IHl. simpl.
  destruct Tdec; try congruence. 
  simpl. destruct Tdec; try congruence.
  simpl. do 2 destruct Tdec; try congruence.
Qed. 

Lemma removeList_remove_commute : 
  forall l' l t, 
    remove Tdec t (removeList l l') = removeList (remove Tdec t l) l'.
Proof.
  induction l'.
  intros. simpl.
  auto. intros. simpl. rewrite IHl'. rewrite remove_commute.
  auto.
Qed.

Lemma removeList_length_lt: forall l l',
  (exists x, In x l /\ In x l') ->
  length (removeList l' l) < length l'.
Proof.
  induction l; intros.
  do 2 destruct H. inversion H.
  do 3 destruct H.
  subst. simpl.
  eapply Nat.le_lt_trans.
  apply removeList_length_le.
  apply remove_length_lt. auto.
  simpl.
  eapply Nat.le_lt_trans.
  2:{ apply IHl. exists x; split; auto. }
  rewrite <- removeList_remove_commute.
  apply remove_length_le.
Qed.

Lemma length_remove_in :
  forall l t,
    NoDup l -> 
    In t l ->
      S (length (remove Tdec t l)) = length l.
Proof.
  induction l. 
  intros. inversion H0.
  intros. destruct H0.
  simpl. subst. destruct Tdec.
  rewrite remove_id. auto.
  inversion H. subst. auto.
  congruence.
  simpl. destruct Tdec.
  inversion H. subst. congruence.
  simpl. erewrite <- IHl.
  eauto. inversion H. subst. auto.
  auto.
Qed.

Lemma length_removeList_all_in :
forall l' l,
  NoDup l ->
  NoDup l' ->
  (forall x, In x l' -> In x l) ->
length (removeList l l') + length l' = length l.
Proof.
  induction l'. intros.
  auto. intros. simpl.
  rewrite <- removeList_remove_commute.
  rewrite <- plus_Snm_nSm.
  erewrite -> length_remove_in.
  apply IHl'. inversion H0. auto.
  inversion H0. auto.
  intros. apply H1. right. auto.
  apply removeList_NoDup. auto.
  apply removeList_mem. split.
  apply H1. left. auto. inversion H0.
  subst. intros. intros Hcontra. apply H4.
  subst. auto.
Qed.

Lemma NoDup_subset_length :
  forall (l1 l2 : list T),
    NoDup l1 ->
    (forall x, In x l1 -> In x l2) -> 
    length l1 <= length l2.
Proof.
  intros l1. induction l1. intros. simpl. omega.
  intros. simpl. apply le_lt_trans with (m := length (remove Tdec a l2)).
  apply IHl1. inversion H; subst. auto.
  intros. apply remove_mem. split. apply H0.
  right. auto. inversion H. subst. intros Hcontra.
  subst. auto. apply remove_length_in. apply H0.
  left. auto.
Qed.

Lemma NoDupA_subset_length : 
  forall R (l1 l2 : list T),
    (Equivalence R) -> 
    NoDupA R l1 -> 
    (forall x, InA R x l1 -> InA R x l2) ->
    length l1 <= length l2.
Proof.
  intros R l1. induction l1. intros. simpl. omega.
  intros. simpl.
  assert (InA R a l2). apply H1.
  left. apply H.
  apply InA_alt in H2.
  destruct H2. destruct H2.
  specialize (IHl1 (remove Tdec x l2) H).
  inversion H0; subst. apply IHl1 in H7.
  apply le_trans with (m := (S (length (remove Tdec x l2)))).
  omega. specialize (remove_length_in _ _ H3). intros.
  omega. intros.
  specialize (H1 x0). 
  assert (InA R x0 (a::l1)).
  right. auto. apply H1 in H5.
  apply InA_alt in H5.
  apply InA_alt. destruct H5. destruct H5.
  exists x1. split. auto. apply remove_mem. 
  split. auto.  intros Hcontra. subst.
  apply H6. apply InA_alt in H4. destruct H4.
  destruct H4. apply InA_alt. exists x1.
  split. etransitivity. exact H2. symmetry in H5.
  transitivity x0. auto. auto. auto.
Qed.

Lemma splitList_length : 
  forall f1 f2
    (H: forall (t : T), f1 t = negb (f2 t)) l,
  length l = length (filter f1 l) + length (filter f2 l).
Proof.
  intros. induction l.
  simpl. auto.
  simpl.
  replace (f1 a) with (negb (f2 a)).
  destruct (f2 a); simpl;
  rewrite IHl; omega.
  auto.
Qed.

Definition sumbool_left_bool
  P1 P2 (H : forall (t : T), {P1 t} + {P2 t}) t :=
    if H t then true else false.

Definition sumbool_right_bool
  P1 P2 (H : forall (t : T), {P1 t} + {P2 t}) t :=
    if H t then false else true.

Lemma splitList_summbool_spec P1 P2 H :
  forall t, (sumbool_left_bool P1 P2 H) t = 
            negb ((sumbool_right_bool P1 P2 H) t).
Proof.
  intros. unfold sumbool_left_bool, sumbool_right_bool.
  destruct (H t); auto.
Qed.

End GraphSurgery.

Lemma In_InAeq_iff : forall A (x : A) (l : list A),
    InA eq x l <-> In x l.
Proof.
  clear.
  intros.
  split; intros H.
  all: revgoals.
  apply In_InA; auto.
  typeclasses eauto.
  {
    induction H.
    subst.
    left; auto.
    right; auto.
  }
Qed.

