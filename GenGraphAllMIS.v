Require Import GenGraph.
Require Import fintype.
Require Import SetoidList List.
Require Import FunctionalExtensionality.

Ltac in_inv :=
  simpl in *; 
  match goal with
  | H : InA ?eq ?elt nil |- _ =>
    inversion H
  | H : InA ?eq ?x (?h::?t) |- _ =>
    inversion H; subst
  end.

Ltac solve_InA_In :=
  match goal with
  | H : InA eq ?x ?l |- In ?x ?l =>
    apply In_InAeq_iff; auto
  | H : In  ?x ?l |- InA eq ?x ?l =>
    apply In_InAeq_iff; auto
  end.
                          
Lemma equivlistAeq_refl : forall A eqA (a : list A) ,
    Equivalence eqA -> 
    equivlistA eqA a a.
Proof.
  split; intros; auto.
Qed.

Ltac rewrite_equiv :=
  match goal with
  | H : equivlistA eq ?s ?s' |- _ =>
    rewrite H in *
  | H : equivlistA eq (_::?s) nil |- _ =>
    apply equivlistA_cons_nil in H; [exfalso; exact H |typeclasses eauto]
  | |- equivlistA eq ?a ?a =>
    apply equivlistAeq_refl; try typeclasses eauto
  end.

Hint Extern 1 => in_inv : equiv.
Hint Extern 1 => rewrite_equiv; auto : equiv.
Hint Extern 1 => solve_InA_In : equiv.
Hint Constructors InA.

Section AllMIS.
Variable T : Type.
Variable Tdec : forall t1 t2 : T, {t1 = t2} + {t1 <> t2}.

Lemma map_InA_cons : forall s' a s,
    InA (equivlistA eq) s' (map (fun l1 : list T => a :: l1) s) ->
    InA eq a s'.
Proof.
  intros.
  {
    induction s; simpl in H; auto with equiv.
  }
Qed.

Lemma inA_map_iff:
  forall (A B : Type) (f : A -> B) (l : list A) (y : B)
         (eqB : relation B)
         (eqA : relation A),
    (* (forall a, Proper (eqA ==> flip impl) (eq (f a))) -> *)
    Proper (eqA ==> eqB) f -> 
    Equivalence eqA -> 
    Equivalence eqB -> 
  InA eqB y (map f l) <-> (exists x : A, eqB (f x) y /\ InA eqA x l).
Proof.
  intros A B f l y eqB eqA Hprop Aeq Beq.
  split; intros H0.
  {
    induction l; eauto with equiv.
    +
      simpl in H0.
      inversion H0.
      {
        subst.
        exists a.
        split; auto.
        {
          apply eqasym; auto with equiv.
        }
        {
          left; auto.
          apply Aeq.
      (*   apply IHl in H1; eauto. *)
      (*   destruct H2; eauto. *)
      (* exists x; eauto. *)
      (* intuition. *)
        }
      }
      {
        subst.
        apply IHl in H1; eauto.
        destruct H1; eauto.
        exists x; eauto.
        intuition.
      }
  }
  {
    induction l; eauto with equiv.
    {
      simpl in *.
      destruct H0; intuition.
    }
    {
      simpl.
      destruct H0.
      destruct H; auto.
      inversion H0; subst; eauto.
      left.
      rewrite <- H2.
      apply Beq; auto.
    }
  }
Qed.

Lemma remove_NotIn_Id :
  forall a x, ~InA eq a x ->
              remove Tdec a (a :: x) = x.
  intros a0 x Hnot.
  simpl.
  destruct Tdec; subst; auto.
  {
    {
      induction x; auto with equiv.
      simpl.
      destruct Tdec; subst; auto with equiv.
      exfalso; auto.
      rewrite IHx; auto.
    }
  }
  {
    contradiction.
  }
Qed.

Lemma equivlistA_remove : forall a x s' s,
  equivlistA eq (a :: x) s' -> 
      InA eq x s -> 
      ~ InA eq a x -> 
      equivlistA eq x (remove Tdec a s').
Proof.
  intros.
  replace (remove Tdec a s') with
      (removeA Tdec a s') by
      (unfold removeA; auto).
  apply removeA_equivlistA; auto; typeclasses eauto.
Qed.

Lemma InAeq_InAequivlistA : forall A (x : list A) (s : list (list A)),
    InA eq x s ->
    InA (equivlistA eq) x s.
Proof.
  induction s; intros; auto with equiv.
Qed.
  
Lemma map_cons : forall (s' : list T) (a : T) (s : list (list T)),
    InA (equivlistA eq)  s' (map (fun l1 : list T => a :: l1) s) <->
    InA eq a s' /\
    (InA (equivlistA eq) s' s \/ InA (equivlistA eq)  (remove Tdec a s') s).
Proof.
  intros.
  split; intros; auto.
  {
    split.
    {
      eapply map_InA_cons; eauto.
    }
    {
      rewrite inA_map_iff in H; try typeclasses eauto; auto.
      destruct H.
      destruct H; subst.
      destruct (InA_dec Tdec a x).
      {
        left.
        rewrite <- H.
        induction s; [inversion H0| ].
        inversion H0; subst.
        auto with equiv.
        left; auto.
        rewrite H.
        {
          split; intros; auto with equiv.
          {
            rewrite <- H in H1.
            inversion H1; subst; auto.
          }
          {
            rewrite <- H; auto.
          }
        }
        auto with equiv.
      }
      {
        assert (equivlistA eq x (remove Tdec a s')) by
            (eapply equivlistA_remove; eauto).
        right.
        rewrite <- H1.
        clear -H0.
        apply InAeq_InAequivlistA; auto.
      }
    }
  }
  {
    destruct H.
    destruct H0.
    {
      apply inA_map_iff with (eqA := (equivlistA eq)) ; try typeclasses eauto.
      {
        do 2 red; intros.
        rewrite H1; auto with equiv.
      }
      exists s'.
      split; auto.
      {
        split; intros; auto with equiv.
      }
    }
    apply inA_map_iff with (eqA := (equivlistA eq));
      try typeclasses eauto.
    {
      do 2 red; intros;
        rewrite H1; auto with equiv.
    }
    {
      exists (remove Tdec a s').
      split; auto with equiv.
      clear - H.
      {
        replace (remove Tdec a s') with
            (removeA Tdec a s') by
            (unfold removeA; auto).
        destruct (InA_dec Tdec a s').
        {
          split; intros; auto with equiv.
          {
            inversion H0; subst; auto with equiv.
            +
              apply removeA_InA in H2; try typeclasses eauto.
              destruct H2.
              auto.
          }
          {
            destruct (Tdec x a); subst; auto.
            right.
            apply removeA_InA; try typeclasses eauto.
            split; auto with equiv.
          }
        }
        {
          split; intros; auto with equiv.
          {
            inversion H0; subst; auto with equiv.
            +
              apply removeA_InA in H2; try typeclasses eauto.
              destruct H2.
              contradiction.
          }
          {
            right.
            apply removeA_InA; try typeclasses eauto.
            split; auto.
          }
        }
      }
    }
  }
Qed.

Lemma all_subsets_list_subset :
  forall  (l l0 : list T),
    InA (equivlistA eq) l0 (fintype.all_subsets l) <-> (forall x, InA eq x l0 -> InA eq x l).
Proof.
  intros.
  generalize dependent l0.
  induction l.
  {
    split; intros.
    {
      simpl in H.
      inversion H; subst;
        try rewrite H2 in H0.
      inversion H0.
      inversion H2.
    }
    destruct l0.
    simpl; left; auto.
    {
      constructor; intros; auto.
    }
    assert (InA eq t nil).
    apply H; left; auto.
    inversion H0.
  }
  intros.
  simpl.
  rewrite InA_app_iff.
  rewrite map_cons.
  do 2 rewrite IHl.
  split; intros.
  {
    intuition.
    destruct (Tdec x a).
    subst; auto with equiv.
    right.
    apply H1.
    rewrite In_InAeq_iff.
    apply remove_mem; intuition.
  }
  {
    destruct (InA_dec Tdec a l0); auto with equiv.
    {
      right.
      intuition.
      {
        right.
        intros.
        auto with equiv.
        apply In_InAeq_iff in H0.
        apply remove_mem in H0.
        destruct H0; auto with equiv.
        simpl in *.
        apply In_InAeq_iff in H0.
        apply H in H0.
        inversion H0; 
        intuition.
      }
    }
    {
      clear - H n.
      left.
      intros.
      destruct (Tdec x a).
      subst.
      contradiction.
      apply H in H0.
      inversion H0.
      subst.
      contradiction.
      auto.
    }
  }
Qed.


Hint Constructors NoDup.
Hint Constructors NoDupA.

Lemma NoDupA_map : forall a l,
    (forall sub : list T,
       InA (equivlistA eq) sub l -> ~ InA eq a sub) ->
    NoDupA (equivlistA eq) l -> 
    NoDupA (equivlistA eq)
         (map (fun l0 : list T => a :: l0) l).
Proof.
  intros.
  induction H0.
  simpl in *.
  auto.
  {
    simpl.
    constructor; auto.
    intros Hnot.
    rewrite inA_map_iff in Hnot; try typeclasses eauto; eauto.
    destruct Hnot.
    destruct H2.
    clear IHNoDupA.
    assert (~ InA eq a x).
    {
      apply H; left; auto.
      apply equivlistAeq_refl; try typeclasses eauto.
    }
    assert (~ InA eq a x0).
    {
      apply H.
      right; auto.
      apply InAeq_InAequivlistA; auto.
    }
    assert (equivlistA eq x0 x).
    {
      red in H2.
      split; intros; eauto.
      +
        assert (InA eq x1 (a :: x)).
        apply H2; auto.
        inversion H7; subst; eauto.
        contradiction.
      +
        assert (InA eq x1 (a :: x0)).
        apply H2; auto.
        inversion H7; subst; eauto.
        contradiction.
    }
    apply H0.
    rewrite<-  H6.
    apply InAeq_InAequivlistA; auto.
  }
Qed.

Lemma no_dups_powerset :
  forall (A : Type) (l: list T),
    NoDup l -> 
    NoDupA (equivlistA eq)  (fintype.all_subsets l).
Proof.
  intros.
  pose proof (map_cons).
  assert (forall l (a : T) (s : list (list T)),
             InA (equivlistA eq) l (map (fun l1 : list T => a :: l1) s) ->
             InA eq a l /\
       (InA (equivlistA eq) l s \/
        InA (equivlistA eq) (remove Tdec a l) s)).
  intros.
  apply H0; auto.
  clear H0.
  induction l.
  simpl.
  apply NoDupA_singleton.
  simpl.
  apply SetoidList.NoDupA_app; try typeclasses eauto; eauto.
  {
    apply IHl; auto.
    inversion H; subst; auto.
  }
  {
    inversion H; subst.
    apply IHl in H4.
    apply NoDupA_map; auto.
    intros.
    clear -H3 H0 Tdec.
    induction l.
    simpl in H0.
    inversion H0; subst; auto with equiv.
    {
      rewrite all_subsets_list_subset in H0.
      intros Hnot.
      apply H0 in Hnot.
      apply In_InAeq_iff in Hnot.
      contradiction.
    }
  }
  {
    inversion H; subst.
    intros.
    apply map_cons in H2.
    destruct H2; eauto.
    destruct H5; eauto.
    {
      rewrite all_subsets_list_subset in H0.
      assert (InA eq a l) by auto.
      apply In_InAeq_iff in H6.
      contradiction.
    }
    {      
      rewrite all_subsets_list_subset in H0.
      assert (InA eq a l).
      auto.
      apply In_InAeq_iff in H6; eauto.
    }
  }
Qed.
  
Definition Teq (t1 t2 : T) :=
  match Tdec t1 t2 with
  | left _ => true
  | right _ => false
  end.

Require Import Bool.
Definition list_mem (x : T) (l : list T) : bool :=
  existsb (fun elt => if Tdec elt x then true else false) l.

Definition IndependentProg (G : @GenGraph T) (x : list T) :
  bool :=
  forallb (fun v1 => (forallb
        (fun v2 => negb (existsb
        (fun edge => 
           Teq (fst edge) v1 &&
           Teq (snd edge) v2)
        (gE _ G))) x))  x.

Definition ValidSetProg (G : @GenGraph T) (x : list T) :=
  forallb (fun elt => list_mem elt (gV _ G)) x.

Definition MaximalIndSetProg (G : @GenGraph T) (x : list T) :
  bool :=
  (ValidSetProg G x) &&
  (IndependentProg G x) &&
  (forallb (fun v1 => if negb (list_mem v1 x) then
     (existsb (fun edge =>
                 Teq (fst edge) v1 &&
                     Teq v1 (fst edge) &&
                     (list_mem (snd edge) x) &&
                     (list_mem (snd edge) (gV T G)))
              (gE _ G))
                 else
                   true) (gV _ G)).
(* forall x y : T, In x l -> In y l -> ~ In (x, y) (gE T G) *)

(* IndSet_E G l -> *)
(*               (forall x : T, *)
(*                In x (gV T G) -> *)
(*                ~ In x l -> *)
(*                exists y : T, *)
(*                  In y (gV T G) /\ In y l /\ In (x, y) (gE T G)) -> *)
(*               MaximalIndSet_E G l *)


Lemma list_mem_In : forall x1 x,
  In x1 x <-> list_mem x1 x = true.
Proof.
  split;
  intros.
  {
    unfold list_mem.
    apply existsb_exists.
    exists x1; intuition.
    destruct Tdec; subst; auto.
  }
  {
    unfold list_mem in H.
    apply existsb_exists in H.
    destruct H.
    destruct H; auto.
    destruct Tdec; subst; auto.
    discriminate.
  }
Qed.

Lemma MaxProg_iff :forall G x, MaximalIndSetProg G x = true <->
                          MaximalIndSet_E G x.
Proof.
  split; intros.
  unfold MaximalIndSetProg in H.
  unfold IndependentProg in H.
  destruct G.
  simpl in *.
  rewrite andb_true_iff in H.
  rewrite andb_true_iff in H.
  do 2 destruct H.
  unfold ValidSetProg in H.
  rewrite  forallb_forall in H0,H,H1.
  induction gV; simpl in *; auto.
  {
    constructor; eauto.
    {
      constructor; auto.
      {
        red; intros.
        simpl in *.
        apply H in H2; discriminate.
      }
      {
        red; intros.
        simpl.
        intros Hnot.
        apply gE_subset_l in Hnot.
        exact Hnot.
      }
    }
    {
      intros.
      simpl in *.
      inversion H2.
    }
  }
  {
    constructor.
    {
      constructor.
      {
        red; intros.
        simpl.
        specialize (H _ H2).
        destruct (Tdec a x0).
        { subst; auto. }
        rewrite orb_false_l in H.
        unfold list_mem in H.
        rewrite existsb_exists in H.
        destruct H as [y [Hx Hy]].
        right.
        destruct (Tdec y x0).
        { subst; auto. }
        inversion Hy.
      }
      red; intros.
      simpl.
      intros Hnot.
      specialize (gE_subset_l _ _ Hnot).
      generalize (H _ H2).
      generalize (H _ H3).      
      destruct gE_subset_l.
      { subst.
        destruct (Tdec x0 x0); intros A B; try inversion B. clear B.
        destruct (Tdec x0 y).
        { clear A.
          subst.
          eapply gE_irref; eauto. }
        rewrite orb_false_l in A.
        unfold list_mem in A.
        rewrite existsb_exists in A. destruct A as [z [Hz1 Hz2]].
        destruct (Tdec z y); try inversion Hz2.
        subst. clear Hz2.
        clear e.
        generalize (H1 _ H2).
        generalize (H1 _ H3).
        do 2 rewrite forallb_forall.
        intros A B.
        specialize (A _ H2).
        specialize (B _ H3).
        rewrite negb_true_iff in A, B.
        clear A.
        assert (B' : existsb (fun edge : T * T => Teq (fst edge) x0 && Teq (snd edge) y) gE = true).
        { rewrite existsb_exists.
          exists (x0,y).
          split; auto.
          simpl.
          rewrite andb_true_iff.
          split.
          unfold Teq; destruct (Tdec _ _); auto.
          unfold Teq; destruct (Tdec _ _); auto. }
        rewrite B' in B; congruence.
        apply n; auto. }
      admit.
      }
    simpl.
    admit.
  }
  inversion H.
  unfold MaximalIndSetProg.
  destruct G; simpl in *.
  do 2 rewrite andb_true_iff.
  split.
  {
    split.
    {
      unfold ValidSetProg.
      rewrite  forallb_forall.
      intros.
      inversion H0.
      red in H3.
      apply H3 in H2.
      clear -H2.
      simpl in *.
      unfold list_mem.
      apply existsb_exists; auto.
      exists x0.
      split; auto.
      destruct Tdec; subst; auto.
    }
    {
      unfold IndependentProg.
      rewrite  forallb_forall.
      intros.      
      rewrite  forallb_forall.
      intros.
      simpl.
      inversion H0.
      red in H5.
      clear -H5 H2 H3.
      simpl in H5.
      specialize (H5 x0 x1 H2 H3).
      destruct ((existsb
                   (fun edge : T * T => Teq (fst edge) x0 && Teq (snd edge) x1) gE))
               eqn:N.
      {
        rewrite existsb_exists in N.
        destruct N; auto.
        destruct H.
        rewrite andb_true_iff in H0.
        destruct H0.
        unfold Teq in *.
        destruct (Tdec (fst x2) x0); subst; auto.
        destruct (Tdec (snd x2) x1); subst; auto.
        exfalso.
        apply H5.
        destruct x2; auto.
      }
      {
        auto.
      }
    }
  }
  {
    rewrite  forallb_forall.
    intros.
    destruct (negb (list_mem x0 x)) eqn:N; auto.
    unfold negb in N.
    unfold list_mem in N.
    destruct (existsb (fun elt : T => if Tdec elt x0 then true else false) x) eqn:Hn.
    {
      discriminate.
    }
    assert ( ~ In x0 x).
    {
      clear -Hn.
      intros Hnot.
      assert ((exists x' , In x' x /\
                (if Tdec x' x0 then true else false) = true)).
      exists x0.
      split; auto.
      {
        destruct Tdec; subst; auto.
      }
      apply existsb_exists in H.
      rewrite Hn in H.
      discriminate.
    }
    {
      apply H1 in H3; auto.
      {
        clear -H3.
        apply existsb_exists.
        destruct H3.
        exists (x0,x1).
        simpl.
        intuition.
        unfold Teq.
        destruct (Tdec x0 x0); subst; simpl; auto.
        apply list_mem_In in H.
        apply list_mem_In in H0.
        rewrite H0,H.
        auto.
      }
    }
  }
Admitted.

Definition AllMIS (G : @GenGraph T) :=
  filter (fun x => MaximalIndSetProg G x) (fintype.all_subsets (gV _ G)).

Lemma forallb_false1
      (f: T -> bool)
      (l: list T) :
  forallb f l = false ->
  (exists x: T, In x l /\ f x = false).
Proof.
  induction l.
  { inversion 1. }
  simpl.
  rewrite andb_false_iff.
  intros H.
  destruct H.
  { exists a; split; auto. }
  destruct (IHl H) as [x [H3 H4]].
  exists x; split; auto.
Qed.

Lemma forallb_false2
      (f: T -> bool)
      (l: list T) :
  (exists x: T, In x l /\ f x = false) -> 
  forallb f l = false.
Proof.
  induction l.
  { intros [x [A B]]. inversion A. }
  intros [x [A B]].
  simpl.
  inversion A.
  { subst.
    rewrite B; auto. }
  rewrite andb_false_iff; right.
  apply IHl.
  exists x.
  split; auto.
Qed.  

Lemma forallb_false
      (f: T -> bool)
      (l: list T) :
  forallb f l = false <->
  (exists x: T, In x l /\ f x = false).
Proof. split. apply forallb_false1. apply forallb_false2. Qed.

Lemma forallb_equivlistA
      (f: T -> bool)
      (l1 l2: list T)
      (H: equivlistA eq l1 l2) :
      forallb f l1 = forallb f l2.
Proof.
  destruct (forallb f l2) eqn:H2.
  { rewrite forallb_forall; intros x Hin.
    { destruct (H x) as [A B].
      rewrite forallb_forall in H2.
      apply H2; auto.
      rewrite <-In_InAeq_iff; apply A; rewrite In_InAeq_iff; auto. }}
  rewrite forallb_false in H2.
  destruct H2 as [x [Hin H3]].
  rewrite forallb_false.
  exists x; split; auto.
  destruct (H x); rewrite <-In_InAeq_iff; apply H1; rewrite In_InAeq_iff; auto.
Qed.  

Lemma existsb_demorgan
      (f: T -> bool)
      (l: list T) :
  existsb f l = negb (forallb (fun x => negb (f x)) l).
Proof.
  induction l; auto.
  simpl.
  rewrite negb_andb, negb_involutive.
  f_equal.
  rewrite IHl; auto.
Qed.

Lemma existsb_equivlistA
      (f: T -> bool)
      (l1 l2: list T)
      (H: equivlistA eq l1 l2) :
      existsb f l1 = existsb f l2.
Proof.
  do 2 rewrite existsb_demorgan.
  f_equal.
  apply forallb_equivlistA; auto.
Qed.  

Lemma MaximalIndSetProg_equivlistA
  (G : GenGraph T)
  (x : list T)
  (H : MaximalIndSet_E G x)
  (x0 y : list T)
  (H0 : equivlistA eq x0 y) :
  MaximalIndSetProg G x0 = MaximalIndSetProg G y.
Proof.
  unfold MaximalIndSetProg.
  f_equal.
  { 
    f_equal.
    { unfold ValidSetProg.
      apply forallb_equivlistA; auto. }
    unfold IndependentProg.
    rewrite (forallb_equivlistA _ x0 y); auto.
    f_equal.
    apply functional_extensionality; intros x1.
    rewrite (forallb_equivlistA _ x0 y); auto.
  }
  f_equal.
  apply functional_extensionality; intros x1.
  unfold list_mem.
  rewrite (existsb_equivlistA _ x0 y); auto.
  destruct (negb _); auto.
  f_equal.
  apply functional_extensionality; intros x2.
  f_equal.
  f_equal.
  apply existsb_equivlistA; auto.
Qed.
                                                        
Lemma AllMIS_spec : forall G,
  MIS_set_gGraph G (AllMIS G).
Proof.
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
    eapply MaximalIndSetProg_equivlistA; eauto.
  }
  split.
  {
    destruct G.
    simpl in *.
    assert (forall x0 : T, In x0 x -> In x0 gV).
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
Qed.

Lemma MIS_exists : 
  forall G, 
    exists (l : list (list T)), MIS_set_gGraph G l.
Proof.
  intros.
  exists (AllMIS G).
  apply AllMIS_spec.
Qed.

End AllMIS.