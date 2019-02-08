Require Import SetoidList Omega.
Require Import moon_lemma.
Require Import graph_basics.

Close Scope R_scope.

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
      apply well_founded_lt_compat with (f := fun x => length (gV x)).
      intros. auto.
      intros.
      remember (gV x) as l.
      destruct l. apply H. rewrite <- Heql. auto.
      apply H0 with (n:= length l). intros. apply H1.
      simpl. omega. rewrite <- Heql. simpl. auto.
    Qed.
End GenGraphs.

  Fixpoint enumerate (x : nat) :=
    match x with
    | O => 0::nil
    | S x' => x::(enumerate x')
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

  Program Definition GenGraph_of (G : lGraph) :=
     mkGGraph _ (enumerate (lV G)) (nodup _ (flatten_EdgesGraph G)) _ _ _ _. 
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
    apply enumerate_nodup.
  Qed.
  Next Obligation.
    apply NoDup_nodup.
  Qed.

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
  2:{ rewrite Heql1, Heql2. symmetry. rewrite plus_comm. apply splitList_length. intros.
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
  forall G (l : list (list T)) l' t,
    MIS_set_gGraph G l -> 
    ((gV _ G) = t::nil) ->
    In l' l -> equivlistA eq l' (t::nil).
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

(* For graphs G, if G has one vertex then G has one MIS (length l = 1). *)
Lemma MIS_bounds_1_verts :
  forall G (l : list (list T)) t,
    MIS_set_gGraph G l -> 
    ((gV _ G) = t::nil) -> length l = 1.
Proof.
  intros. inversion H.
(*
  destruct l.
  generalize MIS_Bounds_1_verts_aux1; intros.
  eapply H4 in H5; eauto. inversion H5.
  destruct l0. auto.
  inversion H3; subst.
  apply False_rec. apply H7.
  left. etransitivity.
  eapply MIS_Bounds_1_verts_aux2; eauto. left. auto.
  symmetry. eapply MIS_Bounds_1_verts_aux2; eauto. right.
  left. auto.
*)
Admitted.

(* For graphs G with two vertices, then for all MISs l' of G, 
   l' = [t1] \/ l' = [t2] \/ l' = [t1:t2]. *)
Lemma MIS_Bounds_2_verts_aux1 : 
  forall G (l : list (list T)) l' t1 t2,
    MIS_set_gGraph G l -> 
    (gV _ G) = t1::t2::nil ->
    In l' l -> 
    equivlistA eq l' (t1::nil) \/
    equivlistA eq l' (t2::nil) \/
    equivlistA eq l' (t1::t2::nil).
Proof.
  intros. 
  remember (gE _ G) as E.
  destruct E. right. right.
  inversion H. apply H2 in H1.
  inversion H1.
  constructor. intros.
Admitted.

Lemma equivlistA_length A (l1 l2: list (list A)):
  NoDupA (equivlistA eq) l1 ->
  NoDupA (equivlistA eq) l2 ->  
  equivlistA eq l1 l2 ->
  length l1 = length l2.
Admitted.

Lemma MIS_Bounds_2_verts :
  forall G (l : list (list T)) t1 t2,
    MIS_set_gGraph G l -> 
    (gV _ G) = t1::t2::nil ->
    length l <= 2.
Proof.
  intros G l t1 t2 H H2.
  destruct G; simpl in *.
  subst gV0.
  destruct gE0.
  { inversion H; subst.
    assert (Hx: equivlistA eq l ((t1 :: nil) :: (t2 :: nil) :: nil)).
    { admit. }
    apply equivlistA_length in Hx.
    rewrite Hx; auto.
    auto.
    constructor.
    inversion 1; subst.
    destruct (H5 t1).
    assert (Hy: InA eq t1 (t1 :: nil)).
    { constructor. auto. }
    generalize (H4 Hy). inversion 1; subst.
    inversion gV_simplset0; subst.
    apply H10; constructor; auto.
    inversion H9.
    inversion H5.
    constructor.
    inversion 1.
    constructor. }
  assert (Hx: gE0 = nil).
  { admit. (*provable*) }
  subst gE0.
  destruct p as [x1 y1].
  generalize (gE_subset_l0 x1 y1 (in_eq (x1,y1) _)).
  intros H2.
  assert (Hy: In y1 (t1 :: t2 :: nil)).
  { apply (gE_subset_l0 y1 x1).
    apply gE_symm0; left; auto. }
  assert (H3: (x1=t1 /\ y1=t2) \/ (x1=t2 /\ y1=t1)).
  { admit. (*by H2 Hy*) }
  destruct H3.
  { destruct H0; subst.
    admit. (*only MIS is (t1 :: t2 :: nil), by H*) }
  admit. (*by symmetric to previous case*)
Admitted. 

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


Require Import List.
Import ListNotations.

Definition d := [1;2;3].

Definition index := nat.
Definition value := nat.
Definition Pair_map := list (value * index).

Fixpoint vertex_index_list' (V : list nat) ( count: nat ) :=
  match V with
  | nil => nil
  | x::xs => count :: (vertex_index_list' xs (S count))
  end.

Definition vertex_index_list (V : list nat) : list nat :=
  vertex_index_list' V 0.

Lemma vertex_index_1 : forall c V C,
    In c (vertex_index_list' V C) -> c - C < (length V).
Proof.
  induction V; intros.
  inversion H.
  simpl in *.
  destruct H; subst.
  simpl.
  omega.
  apply IHV in H.
  omega.
Qed.

Fixpoint vertex_data_map (V : list nat) (count : nat)
         : Pair_map :=
  match V with
  | nil => nil
  | h :: t => (h,count):: (vertex_data_map t (S count))
  end.

Lemma vertex_map_fact1 : forall v V C,
    In v V -> exists c, In (v,c) (vertex_data_map V C).
Proof.
  induction V; intros.
  inversion H.
  destruct H; subst.
  exists C; left; auto.
  apply IHV with (C := S C) in H.
  destruct H.
  exists x.
  right.
  auto.
Qed.

Lemma vertex_map_fact2 : forall V v C c,
    In (v,c) (vertex_data_map V C) -> c -C < length V.
Proof.
  induction V; intros.
  inversion H.
  simpl in *.
  destruct H; subst.
  inversion H.
  subst.
  simpl.
  omega.
  apply IHV in H.
  omega.
Qed.
    
Lemma vertex_map_fact3 : forall v c V,
    In (v,c) (vertex_data_map V 0) -> c < (length V).
Proof.
  intros.
  destruct V.
  inversion H.
  apply vertex_map_fact2 in H; auto.
  omega.
Qed.

Import index.

Program Fixpoint lookup_Option (v : value) (m : Pair_map) (V : nat)
        (pf2 : forall c, In (v,c) m -> c < V)
: option (Ix V) :=
  match m with
  | nil => None
  | (x,y) :: h =>
    if Nat.eq_dec v x then Some (@Index.mk V y _)  else
      lookup_Option v h V _ 
  end.
Next Obligation.
  apply pf2.
  constructor; auto.
Defined.
Next Obligation.
  apply pf2.
  right.
  auto.
Defined.

Lemma ob2 : forall v x h y ,
    existsb (fun elt : nat * index => fst elt =? v) ((x, y) :: h) =
    true ->  v <> x -> 
    existsb (fun elt : nat * index => fst elt =? v) h = true.
Proof.
  intros.
  rename H into pf.
  rename H0 into H.
  apply existsb_exists.
  apply existsb_exists in pf.
  destruct pf.
  destruct H0.
  inversion H0.
  {
    destruct x0.
    simpl in *.
    exfalso.
    apply Nat.eqb_eq in H1.
    subst.
    inversion H2; subst; contradiction.
  }
  {  
    inversion H0.
    {
      exfalso.
      apply Nat.eqb_eq in H1.
      destruct x0; inversion H3; subst; clear H3.
      simpl in H; contradiction.
    }
    {
      exists x0; intuition.
    }
  }
Qed.


Program Definition l_ob1 :=
  fun (v : value) (m : Pair_map)
  (pf : existsb (fun elt : nat * index => fst elt =? v) m = true)
  (Heq_m : [] = m) =>
eq_ind []
  (fun m0 : Pair_map =>
   existsb (fun elt : nat * index => fst elt =? v) m0 = true -> False)
  (fun pf0 : existsb (fun elt : nat * index => fst elt =? v) [] = true
   =>
   let H : False :=
     eq_ind (existsb (fun elt : nat * index => fst elt =? v) [])
       (fun e : bool => if e then False else True) _ true pf0 in
   False_ind False H) m Heq_m pf.

Import eqtype.
Require Import ssreflect.

Definition list_eq_dec : forall (l l' : list (nat*nat)),
    {l = l'} + {~l = l'}.
Proof.
  intros.
  destruct (lists_eq l l') eqn:H.
  destruct (lists_eq_eq l l').
  left.
  exact e.
  right; exact n.
  right.
  destruct (lists_eq_eq l l').
  inversion H.
  exact n.
Defined.

Definition lookup_false_case v :=
        fun
        pf0 : existsb (fun elt : nat * index => snd elt =? v) [] = true
      =>
      let H :
        forall (A : Type) (f : A -> bool) (l : list A),
        existsb f l = true -> exists x : A, In x l /\ f x = true :=
        fun (A : Type) (f : A -> bool) (l : list A) =>
        match existsb_exists f l with
        | conj x _ => x
        end in
      let pf1 :
        exists x : nat * index, In x [] /\ (snd x =? v) = true :=
        H (nat * index)%type (fun elt : nat * index => snd elt =? v) []
          pf0 in
      False_rec index
        match pf1 with
        | ex_intro _ x H0 =>
            unkeyed
              match H0 with
              | conj H1 H2 =>
                  (fun (H3 : In x []) (_ : (snd x =? v) = true) =>
                   False_ind False H3) H1 H2
              end
        end
.


Definition f (E :list (nat * nat)) :
  match E with
  | [] => list (nat * nat)
  | _ :: _ => E = E -> list (nat * nat)
  end -> list (nat * nat) := 
  match
    E as l
    return
    (match l with
     | [] => list (nat * nat)
     | _ :: _ => l = l -> list (nat * nat)
     end -> list (nat * nat))
  with
  | [] => fun Nil : list (nat * nat) => Nil
  | p :: E0 =>
    fun H : p :: E0 = p :: E0 ->
            list (nat * nat) => H eq_refl
  end.

  (* f E (match E as E' return *)
  (*       (match E' *)
  (*        with nil => list (nat * nat) *)
  (*        | h::t => E'=E-> list (nat * nat) end) *)
  (* with *)

Definition convert_types (m : list (nat*nat)) (v : nat) :
match m as m' with
  | [] => m=m -> index
  | _ :: _ =>
      (* existsb (fun elt : nat * index => fst elt =? v) m = true -> index *)
    m = m -> index
  end -> index := 
match m as m' 
        return
        (match m' with
         | nil => m = m -> index
         | _ :: _ =>
           m' = m' -> index
        end -> index)
  with
  | nil => fun H => H eq_refl
  | h::t => (fun H :
                   (h::t) = (h::t) -> index => 
               H eq_refl)
end.

Definition lookup_helper x y l v H m Heq pf
  :
  existsb (fun elt : nat * index => fst elt =? v) l = true := 
  (eq_ind ((x, y) :: l)
                 (fun m0 : list (value * index) =>
                  existsb (fun elt : nat * index => fst elt =? v) m0 =
                  true ->
                  existsb (fun elt : nat * index => fst elt =? v) l =
                  true)
                 (fun
                    pf0 : existsb
                            (fun elt : nat * index => fst elt =? v)
                            ((x, y) :: l) = true => 
                  ob2 v x l y pf0 H) m Heq pf).

Definition lookup_helper2 v m
           (pf : existsb (fun elt : nat * index => fst elt =? v) m = true)               (Heq : [] = m)
           : existsb (fun elt : nat * index => fst elt =? v) [] = true
  := 
             ( (eq_ind_r 
                (fun m0 : list (value * index) =>
                 existsb (fun elt : nat * index => fst elt =? v) m0 =
                 true)) pf [] Heq ).

Fixpoint lookup (v : value) (m : Pair_map)
         (pf : existsb (fun elt => Nat.eqb (fst elt) v) m = true)
         {struct m}
  : index :=
(convert_types m v (match
    m as m'
    return (
      match m' with
        nil => m' = m -> index
      | h::t =>
        m' = m -> index
      end)
      
  with
  | [] =>  
    fun Heq : [] = m =>
      lookup_false_case v (lookup_helper2 v m pf Heq)
     
  | (x,y) :: l =>
    fun Heq => 
      ( (match Nat.eq_dec v x return index
         with 
       | left _ =>  y
       | right H =>  
      lookup v l (lookup_helper x y l v H m Heq pf) 
     end))
end)).

(* Fixpoint lookup (v : value) (m : Pair_map) *)
(*         (pf : existsb (fun elt => Nat.eqb (fst elt) v) m = true) *)
(*   : index := *)
(*     match *)
(*     m as l *)
(*     return *)
(*       (existsb (fun elt : nat * index => fst elt =? v) l = true -> index) *)
(*   with *)
(*   | [] => *)
(*     lookup_false_case v *)
(*   | p :: m0 => *)
(*       fun *)
(*         pf0 : existsb (fun elt : nat * index => fst elt =? v) (p :: m0) = *)
(*               true => *)
(*       (let *)
(*          (x, y) as p0 *)
(*           return *)
(*             (existsb (fun elt : nat * index => fst elt =? v) (p0 :: m0) = *)
(*              true -> index) := p in *)
(*        fun *)
(*          pf1 : existsb (fun elt : nat * index => fst elt =? v) *)
(*                  ((x, y) :: m0) = true => *)
(*        match Nat.eq_dec v x with *)
(*        | left _ => y *)
(*        | right H => lookup v m0 (ob2 v x m0 y pf1 H) *)
(*        end) pf0 *)
(*   end pf *)
(* . *)

Lemma li_ob1 : forall v x y m0 ,
    existsb (fun elt : nat * index => snd elt =? v) ((x, y) :: m0) =
    true -> 
    v <> y -> 
    existsb (fun elt : value * nat => snd elt =? v) m0 = true.
Proof.
  intros.
  rename H into pf1.
  rename H0 into H.
  apply existsb_exists.
  apply existsb_exists in pf1.
  destruct pf1.
  destruct H0.
  inversion H0.
  {
    destruct x0.
    simpl in *.
    exfalso.
    apply Nat.eqb_eq in H1.
    subst.
    inversion H2; subst; contradiction.
  }
  {  
    inversion H0.
    {
      exfalso.
      apply Nat.eqb_eq in H1.
      destruct x0; inversion H3; subst; clear H3.
      simpl in H; contradiction.
    }
    {
      exists x0; intuition.
    }
  }
Qed.


Definition lookup_index_helper x y l v H m Heq pf
  :
  existsb (fun elt : nat * index => snd elt =? v) l = true := 
  (eq_ind ((x, y) :: l)
                 (fun m0 : list (value * index) =>
                  existsb (fun elt : nat * index => snd elt =? v) m0 =
                  true ->
                  existsb (fun elt : nat * index => snd elt =? v) l =
                  true)
                 (fun
                    pf0 : existsb
                            (fun elt : nat * index => snd elt =? v)
                            ((x, y) :: l) = true => 
                     li_ob1 v x y l pf0 H) m Heq pf).

Definition lookup_index_helper2 v m
           (pf : existsb (fun elt : nat * index => snd elt =? v) m = true)               (Heq : [] = m)
           : existsb (fun elt : nat * index => snd elt =? v) [] = true
  := 
             ( (eq_ind_r 
                (fun m0 : list (value * index) =>
                 existsb (fun elt : nat * index => snd elt =? v) m0 =
                 true)) pf [] Heq ).

Lemma sdf : forall (A : eqType)  (v y : A), (v == y) = false -> v <> y.
Proof.
  clear.
  intros.
  destruct (eqP v y) => //.
Qed.

Fixpoint lookup_index (v : index) (m : Pair_map)
        (pf : existsb (fun elt => Nat.eqb (snd elt) v) m = true)
        (* (pf2 : forall c, In (v,c) m -> c < V) *)
: value := 
   (convert_types m v (match
    m as m'
    return (
      match m' with
        nil => m' = m -> index
      | h::t =>
        m' = m -> index
      end)
      
  with
  | [] =>  
    fun Heq : [] = m =>
      lookup_false_case v (lookup_index_helper2 v m pf Heq)
     
  | (x,y) :: l =>
    fun Heq => 
    (* (match Nat.eqb v y as res *)
      match Nat.eq_dec v y as res return index with
      | left _  => x
      | right H => 
         (lookup_index v l (lookup_index_helper x y l v
                                                         (H) m Heq pf))
      end 
end)).

Require Import Coq.Program.Equality. (* for simplify_dep_elim *)
Lemma sfsdf : forall v v0 m i pf pf',
      (forall
          (pf : existsb (fun elt : nat * index => fst elt =? v) m = true)
          (pf' : existsb
                   (fun elt : value * nat => snd elt =? lookup v m pf) m =
                 true), lookup_index (lookup v m pf) m pf' = v) ->

      v <> v0 ->
      lookup_index (lookup v m pf) ((v0, i) :: m) pf' = v.
    Proof.
      clear.
      intros.
      simpl lookup_index.
      destruct ( Nat.eq_dec (lookup v m pf) i) eqn:H4.
      (* if you lookup v and get i it has to be equal to v0 
         because of no dups... need to add *)
      admit.
      rewrite H; auto.
      Admitted.

(* nneds an addition assumption *)
Lemma help_ : forall v i v0 m n pf pf',
  (forall
          (pf : existsb (fun elt : value * nat => snd elt =? v) m = true)
          (pf' : existsb
                   (fun elt : nat * index =>
                    fst elt =? lookup_index v m pf) m = true),
      lookup (lookup_index v m pf) m pf' = v) ->
  
lookup (lookup_index v m (li_ob1 v v0 i m pf n)) ((v0, i) :: m) pf' =
  v.
Proof.
  clear.
  intros.
  simpl lookup.
  destruct (Nat.eq_dec (lookup_index v m (li_ob1 v v0 i m pf n)) v0) eqn:H4.
  admit.
  rewrite H; auto.
Admitted.

Lemma lookup_index_inverse :
  forall v m pf pf',
    lookup_index (lookup v m pf) m pf' = v.
Proof.
  clear.
  induction m.
  {
    intros.
    exfalso.
    apply (l_ob1 v [] pf eq_refl).
  }
  revert IHm.
  simpl lookup.
  destruct a.
  simplify_dep_elim.
  simpl lookup in pf'.
  simpl lookup_helper.
  destruct (Nat.eq_dec v v0) eqn:H1.
  {
    subst.
    simpl.
    destruct (Nat.eq_dec i i); auto.
    {
      contradiction.
    }
  }
    apply sfsdf; auto.
Qed.

Lemma lookup_inverse :
  forall v m pf pf',
    lookup (lookup_index v m pf) m pf' = v.
Proof.
  clear.
  induction m.
  {
    intros.
    exfalso.
    apply (l_ob1 v [] pf eq_refl).
  }
  revert IHm.
  simpl lookup_index.
  destruct a.
  simplify_dep_elim.
  simpl lookup_index in pf'.
  simpl lookup_index_helper.
  destruct (Nat.eq_dec v i) eqn:H1.
  {
    subst.
    simpl.
    destruct (Nat.eq_dec v0 v0); auto.
    {
      contradiction.
    }
  }
  apply help_; auto.
Qed.


(* Fixpoint lookup_index (v : index) (m : Pair_map) *)
(*         (pf : existsb (fun elt => Nat.eqb (snd elt) v) m = true) *)
(*         (* (pf2 : forall c, In (v,c) m -> c < V) *) *)
(* : value :=  *)
(*   match *)
(*     m as l *)
(*     return *)
(*       (existsb (fun elt : nat * index => snd elt =? v) l = true -> index) *)
(*   with *)
(*   | [] => *)
(*     lookup_false_case v *)
(*   | p :: m0 => *)
(*       fun *)
(*         pf0 : existsb (fun elt : nat * index => snd elt =? v) (p :: m0) = *)
(*               true => *)
(*       (let *)
(*          (x, y) as p0 *)
(*           return *)
(*             (existsb (fun elt : nat * index => snd elt =? v) (p0 :: m0) = *)
(*              true -> index) := p in *)
(*        fun *)
(*          pf1 : existsb (fun elt : nat * index => snd elt =? v) *)
(*                  ((x, y) :: m0) = true => *)
(*        match Nat.eq_dec v y with *)
(*        | left _ => x *)
(*        | right H => lookup_index v m0 (li_ob1 v x y m0 pf1 H) *)
(*        end) pf0 *)
(*   end pf. *)


(* Next Obligation. *)
(*   apply existsb_exists. *)
(*   apply existsb_exists in pf. *)
(*   destruct pf. *)
(*   destruct H0. *)
(*   inversion H0. *)
(*   { *)
(*     destruct x0. *)
(*     simpl in *. *)
(*     exfalso. *)
(*     apply Nat.eqb_eq in H1. *)
(*     subst. *)
(*     inversion H2; subst; contradiction. *)
(*   } *)
(*   {   *)
(*     inversion H0. *)
(*     { *)
(*       exfalso. *)
(*       apply Nat.eqb_eq in H1. *)
(*       destruct x0; inversion H3; subst; clear H3. *)
(*       simpl in H; contradiction. *)
(*     } *)
(*     { *)
(*       exists x0; intuition. *)
(*     } *)
(*   } *)
(* Defined. *)


Definition ret A (x : A) := Some x.
 
Definition bind A B(a : option A) (f : A -> option B) : option B :=
  match a with
    | Some x => f x
    | None => None
  end.

Notation "X <- c1 ;; c2" := (bind c1 (fun X => c2)) 
(at level 100, c1 at next level, right associativity) .

Fixpoint update_edges_Option
        (ind_map : Pair_map) (E : list (nat*nat))
        (V : nat)
        (pf2 : forall v c, In (v,c) ind_map -> c < V)
        : option (list (((Ix V)) * ( (Ix V)))) :=
  match E with
  | nil => Some nil
  | (x,y) :: t =>
    match (lookup_Option x ind_map V (fun
                                         c (H : In (x, c) ind_map) => 
                                        pf2 x c H)) with
    | Some x => 
      match (lookup_Option y ind_map V
                           (fun c (H : In (y, c) ind_map) => 
                                        pf2 y c H)
            ) with
      | Some y => 
        match update_edges_Option ind_map t V
                                  (
                                    fun v c (H : In (v, c) ind_map) => 
              pf2 v c H
    
                                  )
        with
        | Some l => 
          Some ((x,y)::l)
        | None => None
        end
      | None => None
      end
    | None => None
    end
  end.


Definition update_edges_1 :
      forall (ind_map : Pair_map) (E : list (nat * nat)),
       (forall e1 e2 : nat,
        In (e1, e2) E ->
        existsb (fun elt : nat * index => fst elt =? e1) ind_map = true /\
        existsb (fun elt : nat * index => fst elt =? e2) ind_map = true) ->
       forall (x y : nat) (t : list (nat * nat)),
       (x, y) :: t = E ->
       existsb (fun elt : nat * index => fst elt =? x) ind_map = true


  := 
fun (ind_map : Pair_map) (E : list (nat * nat))
  (pf : forall e1 e2 : nat,
        In (e1, e2) E ->
        existsb (fun elt : nat * index => fst elt =? e1) ind_map = true /\
        existsb (fun elt : nat * index => fst elt =? e2) ind_map = true)
  (x y : nat) (t : list (nat * nat)) (Heq_E : (x, y) :: t = E) =>
eq_ind ((x, y) :: t)
  (fun E0 : list (nat * nat) =>
   (forall e1 e2 : nat,
    In (e1, e2) E0 ->
    existsb (fun elt : nat * index => fst elt =? e1) ind_map = true /\
    existsb (fun elt : nat * index => fst elt =? e2) ind_map = true) ->
   existsb (fun elt : nat * index => fst elt =? x) ind_map = true)
  (fun
     pf0 : forall e1 e2 : nat,
           In (e1, e2) ((x, y) :: t) ->
           existsb (fun elt : nat * index => fst elt =? e1) ind_map =
           true /\
           existsb (fun elt : nat * index => fst elt =? e2) ind_map =
           true =>
   let H : In (x, y) ((x, y) :: t) := or_introl eq_refl in
   let H0 :
     existsb (fun elt : nat * index => fst elt =? x) ind_map = true /\
     existsb (fun elt : nat * index => fst elt =? y) ind_map = true :=
     pf0 x y H in
   and_ind
     (fun
        (H1 : existsb (fun elt : nat * index => fst elt =? x) ind_map =
              true)
        (_ : existsb (fun elt : nat * index => fst elt =? y) ind_map =
             true) => H1) H0) E Heq_E pf
.

Definition update_edges' (ind_map : Pair_map) (E : list (nat*nat))
        (pf : forall e1 e2,
            In (e1,e2) E -> 
            (existsb (fun elt => Nat.eqb (fst elt) e1) ind_map = true) /\
            (existsb (fun elt => Nat.eqb (fst elt) e2) ind_map = true)
        )
  : list (nat * nat).
  induction E.
  exact nil.
  destruct a.
  refine(_ :: _).
  refine (pair _ _).
  refine (lookup n ind_map _).
  specialize (pf n n0 (in_eq (n,n0) E)).
  destruct pf.
  exact H.
  refine (lookup n0 ind_map _).
  specialize (pf n n0 (in_eq (n,n0) E)).
  destruct pf.
  exact H0.
  apply IHE.
  intros.
  apply pf; right; auto.
Defined.
  
Definition ob :=
fun (ind_map : Pair_map) (E : list (nat * nat))
  (pf : forall e1 e2 : nat,
        In (e1, e2) E ->
        existsb (fun elt : nat * index => fst elt =? e1) ind_map = true /\
        existsb (fun elt : nat * index => fst elt =? e2) ind_map = true)
  (x y : nat) (t : list (nat * nat)) (Heq_E : (x, y) :: t = E) =>
eq_ind ((x, y) :: t)
  (fun E0 : list (nat * nat) =>
   (forall e1 e2 : nat,
    In (e1, e2) E0 ->
    existsb (fun elt : nat * index => fst elt =? e1) ind_map = true /\
    existsb (fun elt : nat * index => fst elt =? e2) ind_map = true) ->
   (x, y) :: t = E0)
  (fun
     _ : forall e1 e2 : nat,
         In (e1, e2) ((x, y) :: t) ->
         existsb (fun elt : nat * index => fst elt =? e1) ind_map = true /\
         existsb (fun elt : nat * index => fst elt =? e2) ind_map = true
   => eq_refl) E Heq_E pf.

Lemma update_edges_2 :
  forall ind_map l x y E
         (pf : forall e1 e2 : nat,                                                In (e1, e2) E ->
    existsb (fun elt : nat * index => fst elt =? e1) ind_map = true /\
    existsb (fun elt : nat * index => fst elt =? e2) ind_map = true),
    (x, y) :: l = E -> 
    existsb (fun elt : nat * index => fst elt =? y) ind_map = true.
Proof.
  intros.
  subst.
  specialize (pf x y (in_eq (x,y) l)).
  destruct pf.
  exact H0.
Qed.


Fixpoint update_edges (ind_map : Pair_map) (E : list (nat*nat))
        (pf : forall e1 e2,
            In (e1,e2) E -> 
            (existsb (fun elt => Nat.eqb (fst elt) e1) ind_map = true) /\
            (existsb (fun elt => Nat.eqb (fst elt) e2) ind_map = true)
        ) : list (nat*nat) := 
  f E (match E as E' return
        (match E'
         with nil => list (nat * nat)
         | h::t => E'=E-> list (nat * nat) end)
  with
  | nil => nil
  | (x,y) :: l => (fun Heq =>
                    ((lookup x ind_map
                      (update_edges_1 ind_map E pf x y l Heq )),
                     (lookup y ind_map
                    (update_edges_2 ind_map l x y E pf Heq)))
                              ::
                              update_edges ind_map l 
            (fun (e1 e2 : nat) (H : In (e1, e2) l) =>
              pf e1 e2
                (eq_ind ((x, y) :: l)
                   (fun E0 : list (nat * nat) => In (e1, e2) E0)
                   (or_intror H) E Heq)) 

)
  end).
(* Next Obligation. *)
(*   specialize (pf x y (in_eq (x,y) l)). *)
(*   destruct pf. *)
(*   exact H0. *)
(* Defined. *)
(* Next Obligation. *)
(*   assert (In (x, y) ((x, y) :: t)). *)
(*   constructor; auto. *)
(*   apply pf in H. *)
(*   intuition. *)
(* Defined. *)
(* Next Obligation. *)
(*   apply pf; auto. *)
(*   constructor 2; auto. *)
(* Defined. *)


Lemma lookup_help : forall n m pf1 pf1' ,
      lookup n m pf1 = lookup n m pf1'.
Proof.
  simplify_dep_elim.
  induction m; 
  simpl; auto.
  unfold lookup_false_case.
  destruct (existsb_exists (fun elt : nat * index => snd elt =? n) []).
  simplify_dep_elim.
  destruct (e (lookup_helper2 n [] pf1 eq_refl)).
  exfalso.
  intuition.
  intros.
  destruct a.
  destruct (Nat.eq_dec n v); auto.
Qed.

Lemma lookup_index_help : forall n m pf1 pf1' ,
      lookup_index n m pf1 = lookup_index n m pf1'.
Proof.
  simplify_dep_elim.
  induction m; 
  simpl; auto.
  {
    unfold lookup_false_case.
    destruct (existsb_exists (fun elt : nat * index => snd elt =? n) []).
    simplify_dep_elim.
    destruct (e (lookup_helper2 n [] pf1 eq_refl)).
    exfalso.
    intuition.
  }
  intros.
  destruct a.
  destruct (Nat.eq_dec n i); auto.
Qed.

Lemma upd_in_ : forall c1 c2 m E pf1' pf1,
  In (c1, c2)
        (update_edges m E pf1)
         <->
  In (c1, c2) (update_edges m E pf1').
Proof.
  clear.
  split.
  +
  simplify_dep_elim.
  induction E; auto.
  simpl in x.
  simpl.
  destruct a.
  destruct x.
  {
    rewrite <- H.
    left.
    clear.
    generalize dependent ((update_edges_1 m ((n, n0) :: E) pf1' n n0 E eq_refl)).
    generalize dependent ((update_edges_2 m E n n0 ((n, n0) :: E) pf1' eq_refl)).
    generalize dependent (update_edges_1 m ((n, n0) :: E) pf1 n n0 E eq_refl).
    generalize dependent (update_edges_2 m E n n0 ((n, n0) :: E) pf1 eq_refl).
    intros.
    assert (lookup n m e2 = lookup n m e0).
    apply lookup_help.
    assert (lookup n0 m e1 = lookup n0 m e).
    apply lookup_help.
    auto.
  }
  right.
  eapply IHE; eauto.
+
  simplify_dep_elim.
  induction E; auto.
  simpl in x.
  simpl.
  destruct a.
  destruct x.
  {
    rewrite <- H.
    left.
    clear.
    generalize dependent ((update_edges_1 m ((n, n0) :: E) pf1' n n0 E eq_refl)).
    generalize dependent ((update_edges_2 m E n n0 ((n, n0) :: E) pf1' eq_refl)).
    generalize dependent (update_edges_1 m ((n, n0) :: E) pf1 n n0 E eq_refl).
    generalize dependent (update_edges_2 m E n n0 ((n, n0) :: E) pf1 eq_refl).
    intros.
    assert (lookup n m e2 = lookup n m e0).
    apply lookup_help.
    assert (lookup n0 m e1 = lookup n0 m e).
    apply lookup_help.
    auto.
  }
  right.
  eapply IHE; eauto.
Qed.
    
Lemma help : forall m n n0 E pf1 pf1'
  pfl1 pfl1' ,
    forall (c1 c2 : nat),
  In (c1, c2)
     (update_edges m ((n, n0) :: E) pf1)
  ->  (c1,c2) = (lookup n m pfl1, lookup n0 m  pfl1') \/
  In (c1, c2)
     (update_edges m E pf1').
Proof.
  intros.
  clear - H.
  simpl in H.
  destruct H; auto.
  {
    left.
    rewrite <- H.
    rewrite <- lookup_help with (pf1 := pfl1).
    rewrite <- lookup_help with (pf1 := pfl1').
    auto.
  }
  {
    right.
    generalize dependent ((fun (e1 e2 : nat) (H : In (e1, e2) E) =>
            pf1 e1 e2 (or_intror H))).
    intros.
    eapply upd_in_; eauto.
  }
Qed.

Lemma nat_pair_dec : forall (x y: nat*nat),
      {x = y} + {~ x = y}.
Proof.
  intros.
  destruct x,y.
  destruct (Nat.eq_dec n n1);
    destruct (Nat.eq_dec n0 n2); subst; auto.
  all: (right;
  intros Hnot;
  inversion Hnot;
  subst;
  contradiction).
Qed.

Definition ix_to_nat V(i : Ix V) : nat :=
  match i with
  | @Index.mk _ i0 _ => i0
  end.


Inductive EquivList_map {V : list nat}
(* {Adec : forall (x y : (A*A)), {x = y} + {~ x = y}} *)
  : list (nat * nat) ->
    list (nat * nat)
    -> Prop :=
| empty_same : EquivList_map nil nil
| cons_eq : forall (x y : nat) (x' y' : nat)
        (l l' : list (nat*nat)) pf pf1,
    let ind_map := (vertex_data_map V 0) in
      lookup x ind_map pf = x'->
      lookup y ind_map pf1 = y'->
    EquivList_map l l' ->
    EquivList_map ((x,y)::l) ((x',y')::l').

(* Fixpoint unupdate_edges (ind_map :  *)

(* Lemma update_edges_bij : forall E V pf, *)
(*     let ind_map := (vertex_data_map V 0) in *)
(*     let f := (update_edges ind_map E pf) *)


Program Definition IndexEdges_from_edges (G : @GenGraph nat) :
  (list (nat * nat)) :=
  match G with
  | {| gV := gV0; gE := gE0;
       gE_irref := gE_irref0; gE_symm := gE_symm0;
       gV_simplset := gV_simplset0; gE_simplset := gE_simplset0;
       gE_subset_l := gE_subset_l0
    |}
    =>
    let edges := update_edges (vertex_data_map gV0 0) gE0
                              _ in edges
                              
(*     match *)
(*       (update_edges_Option (vertex_data_map gV0 0) gE0 (length gV0) *)
(*                            (fun (v : value) (c : index) *)
(*   (H : In (v, c) (vertex_data_map gV0 0)) => *)
(* let H0 : c < length gV0 := vertex_map_fact3 v c gV0 H in H0)  *)
(*       ) *)
(*     with *)
(*     | Some l => l *)
(*     | None => nil *)
(*     end *)
  end.
Next Obligation.
  pose proof vertex_map_fact3.
  pose proof vertex_map_fact1.
  assert (In e1 gV0).
  {
    eapply gE_subset_l0; eauto.
  }
  assert (In e2 gV0).
  {
    eapply gE_subset_l0; eauto.
  }
  pose proof H2.
  pose proof H3.
  apply vertex_map_fact1 with (C := 0)in H2.
  apply vertex_map_fact1 with (C := 0)in H3.
  destruct H2,H3.
  split;
    apply existsb_exists; eauto;
    [ exists (e1,x) |  exists (e2,x0)];
    intuition;
    simpl;
    apply Nat.eqb_eq; auto.
Defined.
(* Next Obligation. *)
(*   apply vertex_map_fact3 in H; auto. *)
(* Defined. *)

Lemma lookup_In : forall V n C,
    forall e,
      In (n, lookup n (vertex_data_map V C) e) (vertex_data_map V C).
Proof.
  clear.
  intros.
  generalize dependent C.
  induction V.
  {
    intros.
    exfalso; intuition.
  }
  intros.
  simpl.
  destruct (Nat.eq_dec n a).
  subst.
  left; auto.
  right.
  eapply IHV.
Qed.

Lemma lookup_bounds : forall V n ,
    forall e,
    lookup n (vertex_data_map V 0) e < length V.
Proof.
  clear.
  intros.
  pose proof (lookup_In V n 0 e).
  apply vertex_map_fact3 in H.
  auto.
Qed.

(* Lemma lookup_index_bounds : forall V n, *)
(*     forall e, *)
(*       lookup_index n (vertex_data_map V 0) e < length V. *)

Lemma update_edges_bound : forall e1 e2 V E pf,
  In (e1, e2)
  (update_edges (vertex_data_map V 0) E pf) ->
   e1 < (length V) /\ e2 < length V.
Proof.
  clear.
  simplify_dep_elim.
  induction E.
  exfalso; intuition.
  {
    simplify_dep_elim.
    simpl in x.
    destruct a.
    destruct x.
    {
      assert (lookup n (vertex_data_map V 0)
                     (update_edges_1 (vertex_data_map V 0) 
                                     ((n, n0) :: E) pf n n0 E eq_refl) = e1).
      {
        inversion H; auto.
      }
      assert (lookup n0 (vertex_data_map V 0)
                     (update_edges_2 (vertex_data_map V 0) E n n0 
                                     ((n, n0) :: E) pf eq_refl) = e2).
      {
        inversion H; auto.
      }
      split.
      {
        rewrite <- H0.
        apply lookup_bounds.
      }
      {
        rewrite <- H1.
        apply lookup_bounds.
      }
    }
    eapply IHE; eauto.
  }
Qed.

Lemma IndexEdges_from_edges_to_index : forall G e1 e2,
    In (e1,e2) (IndexEdges_from_edges G) ->
    e1 < (length (gV _ G)) /\ e2 < (length (gV _ G)).
Proof.
  clear.
  intros.
  unfold IndexEdges_from_edges in H.
  destruct G.
  simpl in *.
  eapply update_edges_bound; eauto.
Qed.

Lemma bsdf : forall V E,
    (NoDup E) -> 
    (forall x y : nat, In (x, y) E -> In x V) -> 
    (forall x y : nat, In (x, y) E -> In (y, x) E) -> 
    exists l, update_edges_Option (vertex_data_map V 0) E 
        (length V)
        (fun (v : value) (c : index)
           (H : In (v, c) (vertex_data_map V 0)) =>
         vertex_map_fact3 v c V H) = Some l.
Proof.
  Admitted.

(* I think I need to fix this function and the proofs will be 
   easyish *)

  Lemma edges_to_index_1 : forall x y xs (E : list (nat * nat)), E = (x, y) :: xs ->
              In (x, y) ((x, y) :: xs) -> In (x, y) E.
  Proof.
    intros.
    rewrite H.
    exact H0.
  Qed.
  Lemma edge_to_index_2 : forall (E : list (nat*nat)) V x y xs,
E = (x, y) :: xs -> 
(forall e1 e2 : nat, In (e1, e2) E -> e1 < V /\ e2 < V) ->
  forall e1 e2 : nat, In (e1, e2) xs -> e1 < V /\ e2 < V.
Proof.
  intros.
  apply H0.
  rewrite H.
  right; auto.
Qed.

Fixpoint edges_to_index
         (E : list (nat * nat)) V
         (pf : forall e1 e2, In (e1,e2) E -> e1 < V /\ e2 < V)
         {struct E}
  : list (Ix V * Ix V) :=  
  (match E as E' return (E = E') -> list (Ix V * Ix V) with
  | nil => fun _ => nil
  | (x,y)::xs  => fun pf0 => 
                    (Index.mk (proj1 (pf x y (edges_to_index_1 x y xs E pf0
                                                (in_eq (x,y) _)))),
                     Index.mk (proj1 (pf x y (
                                           edges_to_index_1 x y xs E pf0 (in_eq (x,y) _))))) :: (edges_to_index xs V (edge_to_index_2 E V x y xs pf0 pf))
  end eq_refl) .

Lemma not_in_index' : forall V E e1 e2,
    forall pf pf1,
      ~ In ((ix_to_nat _ e1),(ix_to_nat _ e2))
        (update_edges (vertex_data_map V 0) E pf
  )->
    ~In (e1, e2)
           (edges_to_index
              (update_edges (vertex_data_map V 0) E pf) (length V) pf1).
Proof.
  Admitted.
  
Lemma not_in_index : forall G,
    forall e1 e2,
  ~ In ((ix_to_nat _ e1),(ix_to_nat _ e2)) (IndexEdges_from_edges G)->
  ~ In (e1,e2) (edges_to_index (IndexEdges_from_edges G) (length (gV nat G))
       (IndexEdges_from_edges_to_index G)).
Proof.
  intros.
  intros Hnot.
  unfold IndexEdges_from_edges in *.
  destruct G; simpl in *.
  eapply not_in_index' in H; eauto.
Qed.

(* generalize this first *)
Lemma in_index : forall G,
    forall e1 e2,
  In ((ix_to_nat _ e1),(ix_to_nat _ e2)) (IndexEdges_from_edges G) <->
  In (e1,e2) (edges_to_index (IndexEdges_from_edges G) (length (gV nat G))
       (IndexEdges_from_edges_to_index G)).
Proof.
  split.
  +
    intros.
  destruct G.
  simpl in *.
  assert (forall e1 e2 : nat,
        In (e1, e2) gE0 ->
        existsb (fun elt : nat * index => fst elt =? e1) (vertex_data_map gV0 0) = true /\
        existsb (fun elt : nat * index => fst elt =? e2) (vertex_data_map gV0 0) = true).
  apply (fun (e1 e2 : nat) (H : In (e1, e2) gE0) =>
            IndexEdges_from_edges_obligation_1 gV0 gE0 gE_symm0
              gE_subset_l0 e1 e2 H).
  apply upd_in_ with (pf1' := H0) in H.
  (* clear gE_irref0 gE_symm0 gV_simplset0 gE_simplset0 gE_subset_l0. *)
  induction (gE0).
  { contradiction. }
  {
    intros.
    simpl in H.
    destruct a.
    inversion H.
    {
      simpl.
      left; eauto.
      intros.
  Admitted.

Lemma in_update_edges : forall G e1 e2,
    forall pf pf' ,
    In (e1,e2) (gE _ G) <-> 
    In (lookup e1 (vertex_data_map (gV _ G) 0) pf,
        lookup e2 (vertex_data_map (gV _ G) 0) pf')
    (IndexEdges_from_edges G).
Proof.
  clear.
  split.
  simplify_dep_elim.
  destruct G.
  simpl in *.
  assert (forall e1 e2 : nat,
        In (e1, e2) gE0 ->
        existsb (fun elt : nat * index => fst elt =? e1) (vertex_data_map gV0 0) = true /\
        existsb (fun elt : nat * index => fst elt =? e2) (vertex_data_map gV0 0) = true).
  apply (fun (e0 e3 : nat) (H0 : In (e0, e3) gE0) =>
       IndexEdges_from_edges_obligation_1 gV0 gE0 gE_symm0 gE_subset_l0
         e0 e3 H0).
  apply upd_in_ with (pf1 := H).
  clear gE_irref0 gE_symm0 gV_simplset0 gE_simplset0 gE_subset_l0.
  revert x pf pf' H.
  induction (gE0).
  { contradiction. }
  {
    intros.
    inversion x.
    {
      destruct a; subst.
      inversion H0; subst.
      clear H0.
      simpl.
      left.
      clear.
      simpl.
      rewrite lookup_help.
      assert (lookup e2 (vertex_data_map gV0 0)
    (update_edges_2 (vertex_data_map gV0 0) l e1 e2 
       ((e1, e2) :: l) H eq_refl)
          = lookup e2 (vertex_data_map gV0 0) pf') by
      apply lookup_help.
      rewrite H0;
      auto.
    }
    {
      simpl.
      destruct a.
      simpl.
      right.
      apply IHl; auto.
    }
  }
  +
  simplify_dep_elim.
  destruct G.
  simpl in *.
  assert (forall e1 e2 : nat,
        In (e1, e2) gE0 ->
        existsb (fun elt : nat * index => fst elt =? e1) (vertex_data_map gV0 0) = true /\
        existsb (fun elt : nat * index => fst elt =? e2) (vertex_data_map gV0 0) = true).
  apply (fun (e0 e3 : nat) (H0 : In (e0, e3) gE0) =>
       IndexEdges_from_edges_obligation_1 gV0 gE0 gE_symm0 gE_subset_l0
         e0 e3 H0).
  apply upd_in_ with (pf1 := H) in x.
  clear gE_irref0 gE_symm0 gV_simplset0 gE_simplset0 gE_subset_l0.
  induction (gE0).
  { contradiction. }
  {
    intros.
    simpl in x.
    destruct a; subst.
    inversion x.
    {
      inversion H0; subst.
      clear H0.
      simpl.
      left.
      (* need a proof about lookup being unique *)
      admit.
    }
    {
      simpl.
      simpl.
      right.
      eapply IHl; eauto.
    }
  }
Admitted.

Lemma in_index_lookup'' : forall e1  E V pf,
    In (e1,e1) (update_edges (vertex_data_map V 0) E pf) ->
    exists e1',
      exists pf1 pf1',
        In (lookup e1' (vertex_data_map V 0) pf1,
            lookup e1' (vertex_data_map V 0) pf1' )
           (update_edges (vertex_data_map V 0) E pf).
Proof.
  clear.
  intros.
  induction E.
  simpl in *.
  contradiction.
  {
    simpl in *.
    destruct a.
    simpl in *.
    intros.
    destruct H.
    {
      inversion H.
      subst.
      clear H.
      exists n;
      eauto.
    }
    {
      specialize (IHE (fun (e0 e3 : nat) (H0 : In (e0, e3) E) =>
          pf e0 e3 (or_intror H0)) H).
      destruct IHE.
      do  2destruct H0.
      exists x; eauto.
    }
  }
Qed.

Lemma in_index_lookup' : forall e1 e2 E V pf,
    In (e1,e2) (update_edges (vertex_data_map V 0) E pf) ->
    exists e1' e2',
      exists pf1 pf1',
        In (lookup e1' (vertex_data_map V 0) pf1,
            lookup e2' (vertex_data_map V 0) pf1' )
           (update_edges (vertex_data_map V 0) E pf).
Proof.
  clear.
  intros.
  induction E.
  simpl in *.
  contradiction.
  {
    simpl in *.
    destruct a.
    simpl in *.
    intros.
    destruct H.
    {
      inversion H.
      subst.
      clear H.
      exists n.
      exists n0; eauto.
    }
    {
      specialize (IHE (fun (e0 e3 : nat) (H0 : In (e0, e3) E) =>
          pf e0 e3 (or_intror H0)) H).
      destruct IHE.
      do  3destruct H0.
      exists x.
      exists x0; eauto.
    }
  }
Qed.

Lemma in_index_lookup : forall e1 e2 G,
    In (e1,e2) (IndexEdges_from_edges G) ->
    exists e1' e2',
      exists pf1 pf1',
        In (lookup e1' (vertex_data_map (gV _ G) 0) pf1,
            lookup e2' (vertex_data_map (gV _ G) 0) pf1')
           (IndexEdges_from_edges G).
Proof.
  intros.
  destruct G.
  simpl in *.
  eapply in_index_lookup'; eauto.
Qed.

Lemma in_index_lookup_one : forall e1 G,
    In (e1,e1) (IndexEdges_from_edges G) ->
    exists e1',
      exists pf1 pf1',
        In (lookup e1' (vertex_data_map (gV _ G) 0) pf1,
            lookup e1' (vertex_data_map (gV _ G) 0) pf1')
           (IndexEdges_from_edges G).
Proof.
  intros.
  destruct G.
  simpl in *.
  eapply in_index_lookup''; eauto.
Qed.

Lemma helppppp : forall A a n0 (l l0 : list A),
    incl (n0::l0) (a :: l) -> In n0 l0 -> incl l0 (a::l).
Proof.
  intros.
  red in H.
  destruct l0.
  inversion H0.
  inversion H0.
  subst.
  red; intros.
  apply H; auto.
  right; auto.
  red; intros.
  apply H.
  right; auto.
Qed.

Lemma map_cons : forall s' a s,
    In s' (map (fun l1 : list nat => a :: l1) s) <->
    In a s' /\ (In s' s \/ In (remove Nat.eq_dec a s') s).
Proof.
  intros.
  split; intros.
  {
    assert (In a s').
    {
      rewrite -> in_map_iff in H.
      destruct H; intuition; subst ;auto.
      left; auto.
    }
    split; auto.
    rewrite -> in_map_iff in H.
    destruct H.
    do 2 destruct H; subst.
    destruct (in_dec Nat.eq_dec a x).
    {
      
      
      assert (remove Nat.eq_dec a (a :: x) = x).
      {
        simpl.
        destruct (Nat.eq_dec a a).
        simpl.

        assert (forall (l1 l2 : list nat), {l1=l2}+{~l1=l2}).
        admit.
Admitted.

          
(* This needs no dups in both lists to be true *)
Lemma all_subsets_list_subset :
  forall (A : Type) (l l0 : list nat),
  In l0 (fintype.all_subsets l) <-> incl l0 l.
Proof.
  intros.
  generalize dependent l0.
  induction l.
  {
    split; intros.
    {
      red; intros.
      simpl in H.
      destruct H; subst; contradiction.
    }
    destruct l0.
    simpl; left; auto.
    simpl in H.
    red in H.
    assert (In n []).
    apply H; left; auto.
    contradiction.
  }
  intros.
  simpl.
  rewrite  in_app_iff.
  rewrite map_cons.
  do 2 rewrite IHl.
  split; intros.
  {
    intuition.
    red; intros.
    red in H0.
    destruct (Nat.eq_dec a0 a).
    subst; left; auto.
    right.
    apply H0.
    apply remove_mem; intuition.
  }
  {
    destruct (in_dec Nat.eq_dec a l0).    
    {
      red in H.
      right.
      split; auto.
      right.
      red; intros.
      apply remove_mem in H0.
      destruct H0.
      simpl in *.
      apply H in H0.
      intuition.
    }
    {
      left.
      clear - H n.
      red.
      intros.
      destruct (Nat.eq_dec a0 a).
      subst.
      contradiction.
      red in H.
      apply H in H0.
      inversion H0.
      subst.
      contradiction.
      auto.
    }
  }
Qed.

Definition lGraph_of (G : @GenGraph nat) : 
  lGraph.

  refine (mkListGraph (length (gV _ G))
                      (edges_to_index (IndexEdges_from_edges G)
                                      (length (gV _ G))
                                      (IndexEdges_from_edges_to_index G)
                      )
                      _ _).
  {
    intros.
    simpl.
    apply not_in_index.
    intros Hnot.
    apply in_index_lookup_one in Hnot.
    destruct Hnot.
    do 2destruct H.
    apply in_update_edges in H.
    destruct G; simpl in *.
    intuition.
    apply (gE_irref0 x0); auto.
  }
  {
    split; intros.
    {
      (* This proof is going to be hard. 
         Need to rewrite edges_to_index maybe and make it easier to 
         work with
       *)
      apply in_index;
        apply in_index in H.
      generalize dependent (ix_to_nat (length (gV nat G)) x).
      generalize dependent (ix_to_nat (length (gV nat G)) y).
      intros.
      (* need a proof that n0 and n have an element in the vertex data map
         and one that the thing that maps to it is lookup_index, might 
         be able to derive one of these but I'm tired.
       *)
      (* This lemma also needs an additional assumption to be proved
         so we also need to figure out what it is...should be easy...
         and then derive it from In (n0,n) (IndexEdges_from_edges G)
       *)
      erewrite <- (lookup_inverse n0 (vertex_data_map (gV _ G) 0)) in H.
      erewrite <- (lookup_inverse n (vertex_data_map (gV _ G) 0)) in H.
      erewrite <- (lookup_inverse n0 (vertex_data_map (gV _ G) 0)).
      erewrite <- (lookup_inverse n (vertex_data_map (gV _ G) 0)).
      apply in_update_edges.
      apply in_update_edges in H.
      destruct G; simpl in *.
      eapply gE_symm0 in H; auto.
      (* 
         Can use this to finish off the lemma once the proofs are there
         rewrite lookup_index_help.
         rewrite lookup_index_help in H.
         auto.
       *)
      admit.
  (* this can be transformed close to how in_update_edges works 
     I think then it's done after everthing is completed*)
    }
    {
      (* same as the other direction  *)
      admit.
    }
Admitted.




Lemma MIS_exists : 
  forall G, 
    exists (l : list (list T)), MIS_set_gGraph G l.
Proof.
  (* There exists an ind
     induction *)
  (* transform result of all_mis program *)
Admitted.

Require Import Reals.
Require Import Omega.
Require Import Fourier.
Open Scope R_scope.


Lemma MIS_Bounds :
  forall G (l : list (list T)),
    MIS_set_gGraph G l -> 
    INR (length l) <= I (length (gV _ G)).
Proof.
  intros G. induction G using GenGraph_StrongInd_aux.
  {
    intros. rewrite H. replace (I 0) with 1.
    simpl.
    admit.
    unfold I. simpl. replace (0/3) with 0. rewrite Rpower_O.
    auto. fourier. field.
    unfold Rdiv.
    field.
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
      unfold I. simpl. replace (0 / 3) with 0.
      rewrite Rpower_O. fourier. fourier. field.
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
    admit.
  }
  destruct H2.
  {
    do 3 destruct H2. destruct H4. destruct H5.
    destruct x0. simpl in H6. omega.
    destruct x0. 2:{ simpl in H6. omega. }
    destruct (MIS_exists (removeVerts T Tdec G (t :: Datatypes.nil))).
    destruct (MIS_exists (removeVerts T Tdec G (t :: genNeighborhood G t))).
    eapply Rle_trans. apply le_INR.
    apply Prop4_vatter with (G := G) (x := t) (Nx := genNeighborhood G t).
    eapply gE_subset_l. apply H4. left. auto. apply genNeighborhood_spec1.
    auto. exact H7. exact H8. rewrite plus_INR.
    apply Rle_trans with
      (r2 := ((I (length (gV T G) -2)) + (I (length (gV T G) -2)))).
    apply Rplus_le_compat.
    apply Rle_trans with
      (r2 := I (length (gV T (removeVerts T Tdec G (t :: Datatypes.nil))))).
    apply H.
    admit.
    auto.
    admit.
    apply Rle_trans with
      (r2 := I (length (gV T (removeVerts T Tdec G (t :: genNeighborhood G t))))).
    apply H.
    admit. auto.
    admit.
    (* Nate's inequalities *)
    admit.    
  }
  destruct H2.
  {
    do 3 destruct H2. destruct H4. destruct H5.
    destruct (MIS_exists (removeVerts T Tdec G (x :: Datatypes.nil))).
    destruct (MIS_exists (removeVerts T Tdec G (x :: genNeighborhood G x))).
    eapply Rle_trans. apply le_INR.
    apply Prop4_vatter with (G := G) (x := x) (Nx := genNeighborhood G x).
    auto. apply genNeighborhood_spec1. auto. eauto. eauto.
    rewrite plus_INR.
    apply Rle_trans with
      (r2 := I (length (gV T G) - 1) + I (length (gV T G) - 4)).
    apply Rplus_le_compat;
    eapply Rle_trans. apply H. admit. eauto.
    admit.  
    apply H. admit. eauto. eauto. admit.
    (* Nate's inequalities *)
    admit.
  }
  { (* This needs the finished proof from Wood's paper *)
    admit.
  }
Admitted.
