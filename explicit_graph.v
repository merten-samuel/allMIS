Require Import SetoidList Omega.
Require Import moon_lemma.
Require Import graph_basics.
Require Import all_MIS_unique.
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
  intros H1 H2 H.
induction H1.
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

(*TODO:  Fill me in with MIS TRANSFORM *)
Variable mkG_MIS :  (GenGraph T) -> list (list T).

Lemma mkG_MIS_spec : forall G,
  MIS_set_gGraph G (mkG_MIS G).
Proof.

Admitted.

Lemma MIS_exists : 
  forall G, 
    exists (l : list (list T)), MIS_set_gGraph G l.
Proof. intros. exists (mkG_MIS G). apply mkG_MIS_spec. Qed.

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
  mkG_MIS (removeVerts T Tdec G (x::(genNeighborhood G x))).

Definition list_excised_MIS G x :=
  map (fun k => list_excised_MIS_step G k) (x::genNeighborhood G x).

(*
Fixpoint list_excised_MIS_aux G l :=
  match l with 
  | nil => nil
  | cons x l' => (list_excised_MIS_step G x) ++ (list_excised_MIS_aux G l')
  end.

Definition list_excised_MIS G x : list (list T) :=
  list_excised_MIS_aux G (x::(genNeighborhood G x)).
*)

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
      specialize (mkG_MIS_spec
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
(* Possible prove of ALL_MIS exists *)
Lemma all_subsets_list_subset :
  forall  (l l' : list T),
    InA (equivlistA eq) l' (fintype.all_subsets l) <-> (forall x, InA eq x l' -> InA eq x l).
Proof.
Admitted.


Lemma no_dups_powerset :
  forall (A : Type) (l: list T),
    NoDup l -> 
    NoDupA (equivlistA eq)  (fintype.all_subsets l).
Proof.
  Admitted.

Definition MaximalIndSetProg (G : @GenGraph T) (x : list T) :
  bool.
  Admitted.

Lemma MaxProg_iff :forall G x, MaximalIndSetProg G x = true <->
                          MaximalIndSet_E G x.
Proof.
  Admitted.

Definition AllMIS (G : @GenGraph T) :=
  filter (fun x => MaximalIndSetProg G x) (fintype.all_subsets (gV _ G)).

(*Lemma MIS_exists : 
  forall G, 
    exists (l : list (list T)), MIS_set_gGraph G l.
Proof.
  intros.
  exists (AllMIS G).
  unfold AllMIS.
  constructor.
  intros.
  apply filter_In in H.
  destruct H.
  apply MaxProg_iff.
  auto.
  apply filter_NoDupA.
  assert (NoDup (gV T G)).
  {
    destruct G; auto.
  }
  {
    apply no_dups_powerset in H; auto.
  }
  intros.
  apply filter_InA.
  {
    red.
    red.
    intros.
    (* I think this will work *)
    admit.
  }
  split.
  {
    destruct G.
    simpl in *.
    assert (forall x0 : T, In x0 x -> In x0 gV0).
    {
      inversion H; intuition; simpl in *; subst.
      inversion H0; subst.
      simpl in *.
      unfold valid_E in H3.
      simpl in *.
      clear -H3 H2.
      apply H3.
      auto.
    }
    apply all_subsets_list_subset; auto.
    intros.
    rewrite In_InAeq_iff.
    apply H0; auto.
    apply In_InAeq_iff.
    auto.
  }
  {
    apply MaxProg_iff; auto.
  }
Admitted.
 *)

Require Import Reals.
Require Import Omega.
Require Import Fourier.
Open Scope R_scope.

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
    SearchAbout INR.
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
    SearchAbout Rpower.
    apply Rpower_O.
    fourier.
    }
    (* unfold mod.
    
        rewrite 
      induction 
      apply 
      rewrite H12 in H9.
      assert (List.In x (gV T G) ->
     ~ List.In x l1 ->
     exists y : T,
       List.In y (gV T G) /\ List.In y l1 /\ List.In (x, y) (gE T G)).
      apply H7.
      destruct H8.

    assert (MIS_set_gGraph G [[]]).
    apply mkMIS_set.
    {
      intros.
      simpl in H1.
      destruct H1.
      rewrite <-H1.
      simpl.
      constructor.
      constructor.
      unfold valid_E.
      intros.
      simpl in H2.
      contradiction.
      unfold independent_E.
      intros.
      simpl in H2.
      contradiction.
      intros.
      assert (exists n:nat, (n < length(gV T G))%nat /\ nth n (gV T G) x0 = x0).
      apply In_nth.
      exact H2.
      destruct H4.
      destruct H4.
      assert (x1 < 0)%nat.
      rewrite <-H.
      exact H4.
      {
        clear -H6.
        omega.
      }
      contradiction.
    }
    constructor.
    intro.
    inversion H1.
    constructor.
    intros.
    constructor.
    constructor.
    intro.
    contradiction.
    inversion.
    unfold InA. 

    }
    {
     constructor.
    }
    {
       
    simpl.
    Basically, l = [[]] ).
    admit.
    unfold I. simpl. replace (0/3) with 0. rewrite Rpower_O.
    auto. fourier. field.*)
  
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
    { assert (Hx: forall y0, MIS_set_gGraph (removeVerts T Tdec G (t::x::[])) y0 ->
                             (length x0 <= length y0)%nat).
      { intros.
        apply excise_0_degree_vert with (G:=removeVerts T Tdec G [t]) (x:=x) (l:=[]).
        unfold removeVerts.
        simpl.
        SearchAbout remove.
        apply remove_mem.
        split.
        exact H2.
        unfold neighborhood_E in H4.
        (* Prove that x is still in the graph *) 

        admit. }
      destruct (MIS_exists (removeVerts T Tdec G (t::x::[]))) as [y0 Hy0].
      specialize (Hx _ Hy0).
      assert (INR(length x0) <= INR(length y0)).
      apply le_INR.
      exact Hx.
      apply Rle_trans with (r2:= INR(length y0) + INR (length x1)).
      fourier.
      
      apply Rplus_le_compat.
      { 
      apply Rle_trans with
          (r2 := I (length (gV T (removeVerts T Tdec G (t :: x :: Datatypes.nil))))).
      apply H.
      unfold neighborhood_E in H4.
      assert (List.In t (gV T G)).
      assert (List.In t [t] <-> List.In (t,x) (gE T G)).
      apply H4.
      assert (List.In t [t]).
      simpl.
      left; reflexivity.
      assert (List.In (t, x) (gE T G)).
      apply H10.
      exact H11.
      apply gE_subset_l with (y:=x).
      exact H12.
      unfold removeVerts.
      simpl.
      assert ((length (remove Tdec t (gV T G))) < length (gV T G))%nat.
      { 
        apply remove_length_in.
        exact H10.
      }
      { eapply Nat.le_trans.
        apply remove_length.
        omega.
      }
      exact Hy0.
      apply I_monontonic2.
      assert (Hw:
                (length (gV T (removeVerts T Tdec G [t; x]))
                 < length (gV T G) - 1)%nat).
      {
      eapply Nat.lt_le_trans.        
      apply remove_length_in; auto.
      { rewrite remove_mem.
        split; auto.
        intros Hcontra.
        generalize (gE_irref _ G); intros Hz.
        unfold neighborhood_E in H4.
        subst.
        specialize (H4 t).
        destruct H4 as [A B]; apply (Hz t); apply A; left; auto. }
      cut (length (remove Tdec t (gV T G)) < length (gV T G))%nat.
      { intros; omega. }
      apply remove_length_in.
      apply gE_subset_l with (y:=x).
      apply H4; left; auto. }
      omega. }
    admit. (* This is true, since t has degree 1 *)
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
  (* This needs the finished proof from Wood's paper (where all vertices 
     of degree 2) *)
  admit.
Admitted.
End GraphInequalities.