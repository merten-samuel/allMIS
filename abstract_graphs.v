Require Import Arith ProofIrrelevance.

Require Import index eqtype.

Notation "f $ x" := (f x) (only parsing, left associativity, at level 50).

Module Type GRAPH.
  (** The hidden type of graphs *)
  Parameter T : Type.

  (** A module-local invariant *)
  Parameter PRIVATE : nat * T -> Prop.
  
  (** The unhidden type of graphs *)
  Definition graph := {p : (nat * T) | PRIVATE p}. 

  Definition graphOf (g : graph) : (nat * T) := projT1 g.
  Coercion graphOf : graph >-> prod.
  
  (** The number of vertices *)
  Definition Vs (g : graph) : nat := fst g.

  Notation "'edge' t" := ((Ix (Vs t) * Ix (Vs t))%type) (at level 30).
  
  Parameter has : forall t : graph, edge t -> bool.
  Parameter Has : forall t : graph, edge t -> Prop.
  Axiom hasP : forall t e, reflect (Has t e) (has t e).

  Parameter empty : nat -> graph.
  Axiom emptyP : forall n e, ~Has (empty n) e.
  Axiom empty_Vs : forall n, Vs (empty n) = n.

  (** Normalize applies a (private) module-local operation to reestablish 
      the PRIVATE invariant. *)
  Parameter normalize : forall (n : nat) (t : T), {t' : T | PRIVATE (n, t')}.

  (** [lift] takes a graph [g] and inserts the new hidden "pregraph" [t]. 
      The interesting thing is, it resolves definitionally to a graph 
      with the same number of vertices as [g]. This is useful when stating 
      lemmas like [add_same], etc., below. *)
  Definition lift (g : graph) (t : T) : graph :=
    let r := normalize (fst g) t
    in existT _ (fst g, projT1 r) (projT2 r).

  (** Edge operations *)  
  Parameter add : forall t : graph, edge t -> T.
  Axiom add_same : forall t e, Has (lift t $ add t e) e.
  Axiom add_other : forall t e e', e<>e' -> has (lift t $ add t e) e' = has t e'.

  Parameter rem : forall t : graph, edge t -> T.
  Axiom rem_same : forall t e, ~Has (lift t $ rem t e) e.
  Axiom rem_other : forall t e e', e<>e' -> has (lift t $ rem t e) e' = has t e'.

  (** The n-vertex induced subgraph *)
  Parameter induced : forall (n : nat) (t : graph), graph.
  Axiom inducedP : forall n t, Vs (induced n t) = n.

  (** The "induced-graph" induction principle *)
  Axiom ind :
    forall (P : graph -> Prop),
      P (empty 0) ->
      (forall g n, P (induced n g) -> P (induced (S n) g)) ->
      forall g, P g.
End GRAPH.  

Module Graph : GRAPH.
  Definition T := list (nat * nat).
  
  Definition pregraph := (nat * T)%type.

  Definition PRIVATE (g : pregraph) : Prop :=
    List.Forall (fun p =>
                   match p with
                     | (x, y) => x < fst g /\ y < fst g
                   end) (snd g).

  Definition graph := {p : pregraph | PRIVATE p}.

  Definition graphOf (g : graph) : (nat * T) := projT1 g.
  Coercion graphOf : graph >-> prod.
  
  Definition Vs (g : graph) : nat := fst g.

  Notation "'edge' t" := ((Ix (Vs t) * Ix (Vs t))%type) (at level 30).

  Fixpoint listHas (l : list (nat * nat)) (e : nat * nat) : bool :=
    match l with
      | nil => false
      | cons e' l' => if e == e' then true else listHas l' e
    end.

  Definition unIndex g (e : edge g) : (nat * nat)%type :=
    match e with
      | (Index.mk x _, Index.mk y _) => (x, y)        
    end.
  
  Definition has (g : graph) (e : edge g) : bool :=
    listHas (snd g) (unIndex g e).
  Definition Has g e := has g e = true.

  Lemma hasP g e : reflect (Has g e) (has g e).
  Proof.
    unfold Has.
    destruct (has g e); constructor; auto.
  Qed.    

  Definition empty' n : pregraph := (n, nil).

  Definition empty (n : nat) : graph.
    refine (existT _ (empty' n) _).
    unfold PRIVATE; constructor.
  Defined.    

  Lemma emptyP n e : ~Has (empty n) e.
  Proof.
    unfold empty, Has, has; simpl; auto.
  Qed.

  Lemma empty_Vs n : Vs (empty n) = n.
  Proof. reflexivity. Qed.    

  Definition lift' (g : graph) (t : T) : pregraph := (fst g, t).

  Fixpoint filterInduced (n : nat) (l : T) : T :=
    match l with
      | nil => nil
      | cons (x, y) l' => if andb (NPeano.ltb x n) (NPeano.ltb y n)
                          then cons (x, y) (filterInduced n l')
                          else filterInduced n l'
    end.

  Lemma filterInduced_PRIVATE n l : PRIVATE (n, filterInduced n l).
  Proof.
    unfold PRIVATE. 
    revert n; induction l; simpl; auto.
    intros n. simpl in IHl.
    destruct a.
    destruct ((NPeano.ltb n0 n && NPeano.ltb n1 n)%bool) eqn:H.
    { constructor.
      symmetry in H. apply Bool.andb_true_eq in H. destruct H as [H1 H2].
      symmetry in H1, H2.
      split; apply NPeano.ltb_lt; auto.
      apply IHl.
    }
    apply IHl.
  Defined.

  Definition induced (n : nat) (g : graph) : graph.
    refine (existT _ (n, filterInduced n $ snd g) _).
    apply filterInduced_PRIVATE.
  Defined.    

  Lemma inducedP n g : Vs (induced n g) = n.
  Proof. reflexivity. Qed.
  
  Definition normalize (n : nat) (t : T) : {t' : T | PRIVATE (n, t')}.
    exists (filterInduced n t).
    apply filterInduced_PRIVATE.
  Defined.

  Definition lift (g : graph) (t : T) : graph.
    exists (fst g, (projT1 (normalize (fst g) t))).
    apply filterInduced_PRIVATE.
  Defined.    
  
  Definition add (g : graph) (e : edge g) : T := cons (unIndex g e) (snd g).

  Lemma add_same (g : graph) e : Has (lift g $ add g e) e.
  Proof.
    unfold lift, add, Has, has, unIndex; simpl.
    destruct e as [ix iy].
    destruct ix, iy.
    destruct (eqP (i, i0) (i, i0)); auto.
    destruct g; simpl in *.
    unfold Vs, fst, graphOf in *.
    simpl in *.
    destruct x.
    rewrite <-NPeano.Nat.ltb_lt in pf, pf0.
    rewrite pf, pf0.
    simpl.
    destruct (eqP (i, i0) (i, i0)); auto.
  Qed.    

  Lemma listHas_filterInduced n t e :
    PRIVATE (n, t) ->
    listHas (filterInduced n t) e = listHas t e.
  Proof.
    revert n.
    induction t; auto.
    intros n. inversion 1; subst. simpl in *.
    destruct a.
    destruct H2 as [H2 H4].
    rewrite <-NPeano.Nat.ltb_lt in H2, H4.
    rewrite H2, H4; simpl.
    destruct (eqP e (n0, n1)); auto.
  Qed.
  
  Lemma add_other g e e' : e <> e' -> has (lift g $ add g e) e' = has g e'.
  Proof.
    unfold lift, add, Has, has, unIndex; simpl.
    destruct e as [ix iy].
    destruct e' as [ix' iy'].    
    destruct ix', iy', ix, iy.
    destruct (eqP (i, i0) (i1, i2)); auto.
    intros H. elimtype False. apply H. inversion e; subst. f_equal.
    { f_equal. apply proof_irrelevance.
    }
    f_equal. apply proof_irrelevance.
    unfold Vs, fst, graphOf in *.
    simpl in *. destruct g. simpl in *. destruct x. simpl in *.
    intros _.
    rewrite <-NPeano.Nat.ltb_lt in pf1, pf2.
    rewrite pf1, pf2.
    simpl.
    destruct (eqP (i, i0) (i1, i2)); auto.
    inversion e; elimtype False; apply n; auto.
    apply listHas_filterInduced; auto.
  Qed.    

  Fixpoint listRem (l : T) (e : nat * nat) : T :=
    match l with
      | nil => nil
      | cons e' l' => if e == e' then listRem l' e else cons e' (listRem l' e)
    end.

  Definition rem (g : graph) (e : edge g) : T := listRem (snd g) (unIndex g e).

  Lemma rem_same g e : ~Has (lift g $ rem g e) e.
  Proof.
    unfold lift, rem, Has, has, unIndex; simpl.
    destruct e as [ix iy]; destruct ix, iy.
    generalize (snd g) as l.
    revert i pf i0 pf0.
    induction l; simpl; auto.
    destruct (eqP (i, i0) a); auto.
    simpl; destruct (eqP (i, i0) a); auto.
    unfold Vs, fst, graphOf in *.
    simpl in *. destruct a, g; simpl in *.
    destruct x; simpl in *.
    destruct ((NPeano.ltb n1 n3 && NPeano.ltb n2 n3)%bool); auto.
    simpl.
    destruct (eqP (i, i0) (n1, n2)).
    inversion e; subst; auto.
    auto.
  Qed.    

  Lemma rem_PRIVATE n t e :
    PRIVATE (n, t) -> 
    PRIVATE (n, listRem t e).
  Proof.
    induction t; auto.
    simpl. inversion 1. subst.
    destruct (eqP e a); auto.
    constructor; auto. inversion H; subst; auto. apply IHt; auto.
  Qed.    
  
  Lemma rem_other g e e' : e <> e' -> has (lift g $ rem g e) e' = has g e'.
  Proof.
    destruct g.
    destruct x.
    revert n p e e'.
    induction t; auto.
    intros n H0 e e' H.
    unfold lift, rem, Has, has, unIndex, Vs in *; simpl in *.
    destruct e as [ix iy]; destruct ix, iy.
    destruct e' as [ix' iy']; destruct ix', iy'.
    rewrite listHas_filterInduced.
    destruct (eqP (i, i0) a).
    destruct (eqP (i1, i2) a); auto.
    subst. inversion e0. subst. 
    clear e0.
    { elimtype False.
      apply H.
      f_equal.
      f_equal.
      apply proof_irrelevance.
      f_equal.
      apply proof_irrelevance.
    }
    { subst.
      inversion H0; subst.
      simpl in *.
      specialize (IHt n H4 _ _ H); simpl in IHt.
      rewrite <-IHt.
      rewrite listHas_filterInduced; auto.
      apply rem_PRIVATE.
      inversion H0; subst; auto.
    }
    { simpl.
      destruct (eqP (i1, i2) a); auto.
      inversion H0; subst.
      specialize (IHt n H4 _ _ H); simpl in IHt.
      rewrite <-IHt.
      rewrite listHas_filterInduced; auto.
      apply rem_PRIVATE.
      inversion H0; subst; auto.
    }
    unfold PRIVATE; simpl.
    destruct (eqP (i, i0) a). subst.
    inversion H0; subst. simpl in *.
    apply rem_PRIVATE; auto.
    constructor. inversion H0; auto.
    inversion H0; subst. simpl in *. apply rem_PRIVATE; auto.
  Qed.    

  Lemma filterInduced_fix n t : PRIVATE (n, t) -> filterInduced n t = t.
  Proof.
    revert n.
    induction t; auto.
    intros n; inversion 1; subst.
    simpl. destruct a.
    destruct ((NPeano.ltb n0 n && NPeano.ltb n1 n)%bool) eqn:H4.
    f_equal. rewrite IHt; auto.
    simpl in *.
    rewrite Bool.andb_false_iff in H4.
    destruct H2.
    rewrite <-NPeano.Nat.ltb_lt in H0, H1.
    rewrite H0, H1 in H4. destruct H4; congruence.
  Qed.    
  
  Lemma induced_fix g : induced (Vs g) g = g.
  Proof.
    unfold induced.
    destruct g.
    unfold Vs.
    simpl.
    destruct x.
    simpl.
    generalize (filterInduced_PRIVATE n t).
    rewrite (filterInduced_fix n t); auto.
    intros.
    f_equal.
    apply proof_irrelevance.
  Qed.
  
  Lemma induced0 g : induced 0 g = empty 0.
  Proof.
    unfold induced.
    generalize (snd g) as l.
    induction l; auto.
    simpl. destruct a. apply IHl.
  Qed.
  
  Lemma ind_lemma (P : graph -> Prop) :
    P (empty 0) ->
    (forall g n, P (induced n g) -> P (induced (S n) g)) ->
    forall g n, P (induced n g).
  Proof.    
    intros H IH. induction n; auto. rewrite induced0; auto.
  Qed.    
  
  Lemma ind (P : graph -> Prop) :
    P (empty 0) ->
    (forall g n, P (induced n g) -> P (induced (S n) g)) ->
    forall g, P g.
  Proof.
    intros. rewrite <-induced_fix. apply ind_lemma; auto.
  Qed.    
End Graph.  