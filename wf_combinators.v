Require Import List.
Require Import Wellfounded.
Require Import Relations.
Require Import Omega.
Require Import Coq.Program.Wf.
Require Import FunInd.
Require Import Permutation.
Require Import  Coq.Classes.RelationClasses.
(*
    This file contains a number of combinators  for well-founded relations.

    Ultimately, these are used to build the well-founded relations
    used to construct the refined versions of allMIS.

*)

    (* TO DO ~ 
          RENAME AND ADD DESCRIPTIONS FOR:
            WfLeftProd
            WfIterStack
            ProdLeftOrder.
            OptionOrder
     *)

(* Ordering only by left element in pair *)
Section WfLeftProd.
  Variables A B : Type.
  Variable R : A -> A -> Prop.
  Variable R_wf : well_founded R.
  
  Inductive LeftProdRel : (A * B) -> (A * B) -> Prop :=
  | introLPR : forall p1 p2, R (fst p1) (fst p2) -> LeftProdRel p1 p2.
  
  Lemma LeftProdEquiv :
    forall a1 a2 b1 b2, LeftProdRel (a1, b1) (a2, b2) <-> R a1 a2.
  Proof.
    split; intros.
    inversion H. auto.
    constructor. auto.
  Defined.

  Lemma LeftProdRel_wf : well_founded LeftProdRel.
  Proof.  
    unfold well_founded. intros a.
    destruct a. generalize dependent b. induction (R_wf a). constructor.
    intros. destruct y. apply H0. rewrite <- LeftProdEquiv.
    apply H1.
  Defined.
End WfLeftProd.


(* Order first by left type, then if at bottom of
    left order, step by right type *)
Section ProdLeftOrder.
  Variable A : Type.
  Variable B : Type.

  Variable Ra : A -> A -> Prop.
  Variable Rb : B -> B -> Prop.

  Variable Ra_wf : well_founded Ra.
  Variable Rb_wf : well_founded Rb.

  Inductive isBottom {X : Type} : (X -> X -> Prop) -> X -> Prop :=
  | introIsBot : forall R x0, (forall x1, ~ R x1 x0) -> isBottom R x0.

  Inductive prodOrderLeft : A * B -> A * B -> Prop :=
  | introProdOrderLeft_r :
      forall p1 p2 (a1 a2 : A) (b : B),
        p1 = (a1, b) ->
        p2 = (a2, b) ->
        Ra a2 a1 -> prodOrderLeft p2 p1
  | introProdOrderLeft_l :
      forall p1 p2 (a1 a2 : A) (b1 b2 : B),
        p1 = (a1, b1) ->
        p2 = (a2, b2) ->
        isBottom Ra a1 ->
        Rb b2 b1 -> prodOrderLeft p2 p1.

  Lemma prodOrderLeft_wf : well_founded prodOrderLeft.
  Proof.
    unfold well_founded. 
    intros p. destruct p.
    generalize dependent a.
    induction b using (well_founded_ind Rb_wf).
    induction a using (well_founded_ind Ra_wf).
    constructor. intros p H1. inversion H1; subst.
    + inversion H2; subst. clear H2. apply H0. auto.
    + inversion H2; subst. clear H2. apply H. auto.
  Qed.
End ProdLeftOrder.

(* Extend a WF relation with a None as a new bottom element *)
Section OptionOrder.
Variable A : Type.
Variable R : A -> A -> Prop.
Variable R_wf : well_founded R.

Inductive optR : option A -> option A -> Prop :=
| introNoneOR : forall o a, o = Some a -> optR None o
| introSomeOR :
    forall o1 o2 a1 a2,
      o1 = Some a1 ->
      o2 = Some a2 ->
      R a2 a1 -> optR o2 o1.

Lemma optR_wf : well_founded optR.
Proof.
  unfold well_founded. intros a.
  destruct a.
  + induction a using (well_founded_ind R_wf).
    constructor. intros. inversion H0; subst.
    constructor. intros. inversion H2; congruence.
    subst. apply H. inversion H1. auto.
  + constructor. intros. inversion H; congruence.
Qed.
End OptionOrder.

(* A well-founded relation over lists acting as stacks *)
Section WfIterStack.

  Variable A : Type.
  Variable R : A -> A -> Prop.
  Variable R_wf : well_founded R.

  Inductive iterStackRel : list A -> list A -> Prop :=
  | introIterStack :
      forall n l' l,
        (forall x, In x l' -> R x n) ->
        iterStackRel (l'++l) (n::l).

  Theorem iterStackRel_wf : well_founded iterStackRel.
  Proof.
    unfold well_founded.
    intros a. induction a.
    + constructor. intros. inversion H.
    + generalize dependent a0. induction a using (well_founded_ind R_wf).
      intros. constructor. intros. inversion H0; subst.
      - generalize dependent l'.
        induction 0.
        * intros. rewrite app_nil_l in *. intros. auto.
        * intros. rewrite <- app_comm_cons. apply H.
          { apply H3. left. auto. }
          { apply IHl'. constructor. intros. apply H3. right. auto.
            intros. apply H3. right. auto.
          }
  Defined.
End WfIterStack.

(*
~~~~ Goal: We want to show that given :

    A : Type
    Ra : A -> A -> Prop
    Ra_wf : well_founded Ra

    The following relation is well-founded:

    - Inductive QueueR : list A -> list A -> Prop :=
      | forall a l l', In a l' -> Ra a' a -> QueueR (l++l') (a::l)
 
~~~~ Problem: A direct proof is annoying and require some means to split/commute
       the well-foundedness across applications of app.

~~~~ Solution:
      Intuitively, it should be the case that everytime
      we step according to the queue relation, we either
      remove the maximum element from the queue, or
      we reduce the maximum distance from the maximum element
      by one.

      However, just because Ra is well-founded doesn't mean we have
      maximum elements. Furthermore, since we want to pass data around
      we need to loosen the notion of what a maximum element looks like.
      To accomplish this, we do the following:

      1.) For two types A B, with well-founded realtions Ra, Rb,
            we define a well-founded relation (ProdLeftOrder)
            over (A*B) which satisfies the following:
              a.) (Ra a1 a2) -> \forall b, (ProdLeftOrder (a2, b) (a1,b))
              b.) isBottom a1 -> Rb b1 b2 -> (\forall a2, ProdLeftOrder (a2, b2) (a1, b1))

          Intuitively, the relation holds if you decrease the first element of some
          pair and hold the second element constant, OR if you can no longer decrease
          the first element, then you can reset it, provided the second element decreases
    
          This is simply an abstraction of what's going on with our queue relation

    2.) For a type A and well-founded relation Ra, we build a well-founded
          relation over Option A, by simply introducing None as the new
          bottom of the relation.

    3.) We define a function which finds the location of a maximum element in
          a list of As. In order for this to make sense, we need the following :
          
            a.) An ordering relation Ra over A which is
              - well-founded
              - transitive (any wf relation can be extended to be transitive)
              - irreflexive (no proof in std. library, but true forall wf_rel)
              - total with respect to Eqa below
                  (i.e. forall a1 a2, {Ra a1 a2} + {Eqa a1 a2} + {Ra a2 a1}

            b.) An equivalence relation Req over A. Strict equality won't
                suffice for our purposes.

          Using these realtions along with our totality property, we
          can find the last occurance of maximum elements in a list of As.
          This function returns None if the list is empty.

    4.) Show that applying the function from 3.) to two queues sharing
        the queue relation respects the well-founded relation constructed
        by applying the results from 2.) to the ProdLeftOrder (nat * A).
  
        This suffices to show well-foundedness of the queue relation provided
        we can satisfy the restrictions from 3.). This will be
        fine for our MIS program since we're essentially ordering
        by natural numbers anyway.

*)
Section WFIterQueue.
  Variable A : Type.
  Variable Ra : A -> A -> Prop.
  Variable Eqa : A -> A -> Prop.

  Variable Ra_wf : well_founded Ra.
  Variable Ra_trans : forall a1 a2 a3, Ra a1 a2 -> Ra a2 a3 -> Ra a1 a3.

  Variable Eqb_eq : equivalence _ Eqa.

  Definition Rord := optR _ (prodOrderLeft _ _ lt Ra).

  Definition Rord_wf := optR_wf _ _ (prodOrderLeft_wf _ _ _ _ lt_wf Ra_wf).

  Variable R_total :
    forall a1 a2, {Ra a1 a2} + {Eqa a1 a2} + {Ra a2 a1}.

  Variable Ra_irref :
    forall a1 a2, Ra a1 a2 -> ~ Eqa a1 a2.

  Program Instance Ra_t : Transitive Ra.
  Program Instance Ra_strict : StrictOrder Ra.
  Next Obligation.
    unfold Irreflexive.
    unfold Reflexive.
    unfold complement.
    intros.
    apply Ra_irref in H.
    apply H.
    apply Eqb_eq.
  Defined.

  Lemma Eqb_resp_RaL : forall a1 a2 a3,
    Eqa a1 a2 -> Ra a1 a3 -> Ra a2 a3.
  Proof.
    intros. destruct (R_total a2 a3) as [[H1 | H1] | H1]; auto.
    + apply False_rec. apply (Ra_irref a1 a3); auto.
      destruct Eqb_eq. apply (equiv_trans a1 a2 a3); auto.
    + apply False_rec. apply (Ra_irref a1 a2).
      apply (Ra_trans a1 a3 a2); auto. auto.
  Qed. 

  Lemma Eqb_resp_RaR : forall a1 a2 a3,
    Eqa a1 a2 -> Ra a3 a1 -> Ra a3 a2.
  Proof.
    intros. destruct (R_total a3 a2) as [[H1 | H1] | H1]; auto.
    + apply False_rec. apply (Ra_irref a3 a1); auto.
      destruct Eqb_eq. apply (equiv_trans a3 a2 a1); auto.
    + apply False_rec. apply (Ra_irref a2 a1); auto.
      apply (Ra_trans a2 a3 a1); auto.
      destruct Eqb_eq. apply equiv_sym. auto.
  Qed.    

    Add Parametric Relation : A Eqa
      reflexivity proved by (@equiv_refl A Eqa Eqb_eq) 
      symmetry proved by (@equiv_sym A Eqa Eqb_eq)
      transitivity proved by (@equiv_trans A Eqa Eqb_eq)
    as eqA.

    
    Require Import Setoid.

    Add Morphism Ra
        with signature Eqa ==> Eqa ==> iff
          as Ra_morph.
    Proof.
      intros.
      split; intros.
      eapply Eqb_resp_RaL in H; eauto.
      eapply Eqb_resp_RaR in H0; eauto.
      assert (Ra y x0).
      eapply Eqb_resp_RaR; eauto.
      symmetry.
      auto.
      eapply Eqb_resp_RaL in H2; eauto.
      symmetry.
      auto.
    Qed.


    Lemma Ra_Asym:
      forall a a',
        Ra a a' ->  Ra a' a -> False.
    Proof.
      intros a a' H Hnot.
      specialize (StrictOrder_Asymmetric Ra_strict).
      intros.
      unfold Asymmetric in H0.
      exfalso; eauto.
    Qed.
    
    Hint Resolve Ra_Asym.


  Fixpoint maxLocR (l : list A) : option (nat * A) :=
    match l with
    | nil => None
    | a::l' =>
      match maxLocR l' with
      | None => Some (0, a)
      | Some (n, a') =>
        match R_total a a' with
        | inright _ => Some (0, a)
        | inleft _ => Some (S n, a')
        end
      end
    end.

  Inductive MaxLocR : list A -> option (nat * A) -> Prop :=
  | max_nil : MaxLocR nil None
  | max_None : forall l a, MaxLocR l None ->
                           MaxLocR (a :: l) (Some (0, a))
  | max_Some_right : forall n l a a' x,
      MaxLocR l (Some (n,a')) -> R_total a a' = inright x ->
      MaxLocR (a :: l) (Some (0, a))
  | max_Some_left : forall n l a a' x,
      MaxLocR l (Some (n,a')) -> R_total a a' = inleft x ->
      MaxLocR (a :: l) (Some (S n, a')).

  Hint Constructors MaxLocR.

  Lemma maxLocR_nil : forall l, 
    maxLocR l = None <-> l = nil.
  Proof.
    induction l.
    + split; intros; auto.
    + split; intros; inversion H.
      destruct (maxLocR l);
      [destruct p | inversion H1]. 
      destruct (R_total a a0); inversion H1.
  Qed.

  Lemma maxLocR_equiv : forall l loc, 
      maxLocR l = loc <-> MaxLocR l loc.
  Proof.
    split; intros.
    Focus 2.
    induction H; auto; simpl; try rewrite IHMaxLocR; simpl;
      try rewrite H0; auto.
    generalize dependent loc.
    induction l; intros.
    inversion H.
    simpl.
    constructor.
    simpl in H.
    case_eq (maxLocR l); intros.
    destruct p.
    rewrite H0 in H.
    case_eq (R_total a a0); intros;
      assert (MaxLocR l (Some (n, a0)));
      auto;
      subst.
      rewrite H1.
      econstructor; eauto.
    +
      rewrite H1; econstructor 3; eauto.
    +
      assert (MaxLocR l None).
      auto.
      rewrite H0 in H.
      subst.
      constructor; auto.
  Qed.

  Lemma maxLocR_mem : forall l a n,
    maxLocR l = Some (n, a) -> In a l.
  Proof.
    induction l.
    + simpl. congruence.
    + intros. simpl in H.
      destruct (maxLocR l).
      - destruct p. destruct (R_total a a1).
        * inversion H; subst. right.
          apply (IHl a0 n0). auto.
        * left. inversion H; auto.
      - inversion H. left; auto.
  Qed.

  Lemma maxLocR_max : forall l a n, 
    maxLocR l = Some (n, a) -> (forall a', In a' l -> Ra a' a \/ Eqa a' a).
  Proof.
    induction l.
    + simpl. congruence.
    + intros. destruct H0 as [H0 | H0]; subst; simpl in H.
      - case_eq (maxLocR l); intros;
        rewrite H0 in H.
        * destruct p; subst.
          destruct (R_total a' a). inversion H. subst.
          destruct s; auto. inversion H; subst. right.
          apply Eqb_eq.
        * inversion H. subst. right. apply Eqb_eq.
      - case_eq (maxLocR l); intros;
        rewrite H1 in H.
        * destruct p; subst.
          destruct (R_total a a1); inversion H; subst.
          destruct s; auto;
          apply IHl with (a' := a') in H1; auto.
          apply IHl with (a' := a') in H1; auto.
          destruct H1; [left | left].
          eapply Ra_trans; eauto. eapply Eqb_resp_RaL; eauto.
          apply Eqb_eq. auto.
        * apply maxLocR_nil in H1. subst. inversion H0.
  Qed.

  Lemma maxLocR_consR : forall l a' a n,
    maxLocR (a::l) = Some (S n, a') ->
      maxLocR l = Some (n, a').
  Proof.
    intros;
    inversion H;
    destruct (maxLocR l); inversion H1;
    destruct p;
      destruct (R_total a a0);
      inversion H1;
        destruct s;
          subst;
          auto.
  Qed.

  Lemma maxLocR_uniqR : forall l a a',
    maxLocR (a::l) = Some (0, a') -> a = a'.
  Proof.
    intros. simpl in H. destruct (maxLocR l).
    destruct p. destruct R_total; inversion H.
    auto. inversion H. auto.
  Qed.

  Lemma maxLocR_hdR : forall l a, 
    maxLocR (a::l) = Some (0, a) ->
    (forall a', In a' l -> Ra a' a).
  Proof.
    intros.
    apply maxLocR_equiv in H.
    generalize dependent a.
    generalize dependent a'.
    induction l.
    inversion 1.
    intros.
    inversion H;
    subst.
    apply maxLocR_equiv in H2.
    apply maxLocR_nil in H2.
    inversion H2.
    clear H4.
    clear H.
    destruct H0.
    -
      subst.
      clear IHl.
      inversion H3;
        subst; auto.
      clear H5.
      clear H3.
      destruct x0.
      eapply Ra_trans; eauto.
      rewrite e.
      auto.
    -
      inversion H3; subst.
      { inversion H1; eauto. }
      { apply IHl with (a' := a') in H3; eauto. }
      { clear H6.
        destruct x0.
        apply maxLocR_equiv in H3.
        apply maxLocR_max  with (a' := a') in H3.
        destruct H3; eauto.
        rewrite H0.
        auto.        
        intuition.
        rewrite <- e in x.
        apply maxLocR_equiv in H3.
        apply maxLocR_max  with (a' := a') in H3.          
        destruct H3; eauto.
        rewrite <- e in H0.
        transitivity a; eauto.
        rewrite H0.
        rewrite <- e.
        auto.
        right; auto.
      }
  Qed.

  Hint Resolve eqA_Reflexive.
  Hint Resolve eqA_Symmetric.
  Hint Resolve eqA_Transitive.

  Lemma maxLocR_weaken : forall l a a' n,
      maxLocR l = Some (n, a') ->
      Ra a a' -> 
      maxLocR (l ++ a :: nil) = Some (n, a').
  Proof.
    induction l.
    + intros.
    inversion H.
    + intros.
      case_eq n.
      intros; subst.
      assert (a = a') by (apply maxLocR_uniqR in H; auto).
    subst. specialize (maxLocR_hdR _ _ H).
    intros. simpl. case_eq (maxLocR (l++a0::nil)).
    intros. destruct p.
    specialize (maxLocR_mem _ _ _ H2).
    intros.
    apply in_app_or in H3.
    destruct H3.
    apply H1 in H3.
    destruct (R_total a' a); auto.
    destruct s; eauto.
    exfalso; eauto.
    rewrite e in H3.
    apply Ra_irref in H3.
    exfalso; eauto.
    {
      inversion H3;
      subst.
      destruct (R_total a' a); auto.
      destruct s; auto.
      exfalso.
      eauto.
      rewrite e in H0.
      exfalso.
      apply Ra_irref in H0; eauto.
      inversion H4.
    }
    auto.
    intros.
    specialize (maxLocR_mem _ _ _ H).
    intros.
    subst.
    destruct H2; eauto.
    subst.
    apply maxLocR_consR in H.
    simpl.
    erewrite IHl; eauto.
    {
      destruct (R_total a' a').
      auto.
      exfalso.
      apply Ra_irref in r; eauto.
    }
    simpl.
    specialize (maxLocR_consR _ _ _ _ H).
    intros.
    erewrite IHl; eauto.
    destruct (R_total a a'); eauto.
    apply maxLocR_max with (a' := a) in H; eauto.
    destruct H; eauto.
    exfalso.
    eauto.
    rewrite H in r.
    exfalso.
    apply Ra_irref in r; eauto.
    left.
    auto.
  Qed.

  Lemma maxLocR_app : forall l l' a n,
    maxLocR l = Some (n, a) ->
    (forall a', In a' l' -> Ra a' a) ->
    maxLocR (l ++ l') = Some (n, a).
  Proof.
    intros.
    generalize dependent a.
    generalize dependent n.
    generalize dependent l.
    induction l';
    intros; simpl.
    subst.
    rewrite app_nil_r; auto.
    replace (l ++ a :: l') with ((l ++ a :: nil) ++ l'); simpl; eauto.
    apply IHl'; eauto.
    {
      apply maxLocR_weaken; eauto.
      apply H0.
      left. auto.
    }
    intros.
    apply H0.
    right; auto.
    replace (l ++ a :: nil) with (l ++ (a :: nil)); auto.
    rewrite <- app_assoc.
    simpl.
    auto.
  Qed.

  Definition maxLoC_ord := (wf_inverse_image  _ _ Rord maxLocR Rord_wf).

  Inductive queueR : list A -> list A -> Prop :=
  | introQueueR : forall a l l',
      (forall a', In a' l' -> Ra a' a) -> queueR (l++l') (a::l).

  Lemma QueueR_incl_Rord : forall y x : list A, queueR x y -> Rord (maxLocR x) (maxLocR y).
  Proof.
    intros y. case_eq (maxLocR y).
    + intros. destruct p. inversion H0; subst.
      case_eq n. 
      - intros; subst. case_eq (maxLocR (l++l')).
        * intros. destruct p. apply maxLocR_mem in H2.
          unfold Rord. eapply introSomeOR; eauto.
          eapply introProdOrderLeft_l; eauto.
          { constructor. intros. omega. }
          { apply in_app_or in H2.
            assert (a0 = a). apply maxLocR_uniqR  in H; auto.
            destruct H2 as [H2 | H2].
            + subst. apply maxLocR_hdR with (a' :=  a1) in H; auto.
            + subst. apply H1. auto.
          }
        * intros. unfold Rord. apply introNoneOR with (a := (0, a)). auto.
      - intros; subst. case_eq (maxLocR l). intros.
        * destruct p. apply (maxLocR_app l l') in H2.
          assert (Ra a0 a \/ Eqa a0 a).
          { apply maxLocR_max with (a' := a0) in H. auto. left. auto. }
          destruct H3.
          { apply maxLocR_consR in H.
            simpl in H. unfold Rord. eapply introSomeOR; eauto.
            eapply introProdOrderLeft_r; eauto.
            assert (Some (n, a1) = Some (n0, a)).
            rewrite <- H2. eapply maxLocR_app; eauto. inversion H4; auto.
          }
          { assert (Some (n, a1) = Some (n0, a)).
            rewrite <- H2. eapply maxLocR_app; eauto.
            apply maxLocR_consR in H. auto.
            intros. apply H1 in H4. eapply Eqb_resp_RaR; eauto.
            rewrite H2, H4. unfold Rord. eapply introSomeOR; eauto.
            eapply introProdOrderLeft_r; eauto.
          }
          { intros. assert (Eqa a a1). apply maxLocR_consR in H.
            rewrite H in H2. inversion H2. subst. apply Eqb_eq.
            assert (Ra a' a0). apply H1; auto.
            assert (Ra a0 a \/ Eqa a0 a).
            apply maxLocR_max with (a' := a0) in H. auto. left. auto.
            destruct H6. eapply Eqb_resp_RaR; eauto.
            rewrite <- H4.
            rewrite <- H6.
            auto.
          }
        * intros. apply maxLocR_nil in H2. subst. rewrite app_nil_l in *.
          simpl in H. inversion H. 
    + intros. apply maxLocR_nil in H. subst.
      inversion H0.
  Qed.
  

  (** All that, just for this: *)
  Lemma queueR_wf : well_founded queueR.
  Proof.
    refine (wf_incl _ _ _ _ maxLoC_ord).
    unfold inclusion. intros x y H. apply QueueR_incl_Rord. auto.
  Qed.

End WFIterQueue.

(* A means of constructing programs which loop over a list
    using the stack well-foundedness defined above. *)
Section AccStack.
  
  (* The type used in the list *)
  Variable A : Type.

  (* The return type of the accumulator *)
  Variable B : Type.

  (* The well founded relation over A *)
  Variable R : A -> A -> Prop.
  Variable R_wf : well_founded R.

  (* A method for updating the accumulator *)
  Variable Accum : A -> B -> B.
  (* The stack update rule *)
  Variable f : A -> list A.
  
  (* Stack updates respect the stack relation *)
  Variable f_desc : forall a a', In a' (f a) -> R a' a.

  (* The relation used by these sorts of programs *)
  Definition IterStackR : (list A * B) -> (list A * B) -> Prop :=
    @LeftProdRel (list A) B (iterStackRel A R).

  Lemma IterStackR_wf : well_founded IterStackR.
  Proof.
    apply LeftProdRel_wf. apply iterStackRel_wf. auto.
  Defined.

  (* A decision procedure for whether to continue or stop *)
  Definition mkSmallerStack : forall p, {p' | p = p' & fst p = nil} + {p' | IterStackR p' p}.
  Proof.
    destruct p. case_eq l.
    + left. subst. exists (nil, b); auto.
    + right. subst. exists ((f a)++ l0, Accum a b).
      do 2 constructor. auto.
  Defined.

  (* A program which iterates over a stack until empty, carrying
      around the accumulator in B *)
  Definition IterStackWithAccum : (list A) * B -> (list A) * B :=
      (Fix IterStackR_wf _
      (fun (p : (list A) * B)
           (IterStackWithAccum :
            forall (p' : (list A) * B), (IterStackR p' p -> (list A) * B))
              => match (mkSmallerStack p) with
                | inl _ => p
                | inr (exist _ x pf) => IterStackWithAccum x pf
                end)).
End AccStack.

Section AccQueue.
  
  (* The type used in the list *)
  Variable A : Type.

  (* The return type of the accumulator *)
  Variable B : Type.

  (* The well founded relation over A *)
  Variable R : A -> A -> Prop.
  (* The equivalence relation over A *)
  Variable Eqa : A -> A -> Prop.

  (**Properties of R and Eqa *)
  Variable R_wf : well_founded R.
  Variable R_trans : forall a1 a2 a3, R a1 a2 -> R a2 a3 -> R a1 a3.
  Variable Eqa_eq : equivalence _ Eqa.
  Variable R_total :
    forall a1 a2, {R a1 a2} + {Eqa a1 a2} + {R a2 a1}.
  Variable R_irref :
    forall a1 a2, R a1 a2 -> ~ Eqa a1 a2.

  (* A method for updating the accumulator *)
  Variable Accum : A -> B -> B.

  (* The queue update rule *)
  Variable f : A -> list A.
  
  (* Stack updates respect the queue relation *)
  Variable f_desc : forall a a', In a' (f a) -> R a' a.

  Definition IterQueueR : (list A * B) -> (list A * B) -> Prop :=
    @LeftProdRel (list A) B (queueR A R).

  Lemma IterQueueR_wf : well_founded IterQueueR.
  Proof.
    apply LeftProdRel_wf. 
    apply (queueR_wf A R Eqa R_wf R_trans Eqa_eq R_total R_irref).
  Defined.

  (* A decision procedure for whether to continue or stop *)
  Definition mkSmallerQueue :
    forall p, {p' | p = p' & fst p = nil} + {p' | IterQueueR p' p}.
  Proof.
    destruct p. case_eq l.
    + left. subst. exists (nil, b); auto.
    + right. subst. exists (l0 ++ (f a), Accum a b).
      do 2 constructor. auto.
  Defined.

  (* A program which iterates over a stack until empty, carrying
      around the accumulator in B *)
  Definition IterQueueWithAccum : (list A) * B -> (list A) * B :=
      (Fix IterQueueR_wf _
      (fun (p : (list A) * B)
           (IterQueueWithAccum :
            forall (p' : (list A) * B), (IterQueueR p' p -> (list A) * B))
              => match (mkSmallerQueue p) with
                | inl _ => p
                | inr (exist _ x pf) => IterQueueWithAccum x pf
                end)).

End AccQueue.

Section QueueStackSimulation.
  (* The type used in the list *)
  Variable A : Type.

  (* The return type of the accumulator *)
  Variable B : Type.

  (* The well founded relation over A *)
  Variable R : A -> A -> Prop.
  (* The equivalence relation over A *)
  Variable Eqa : A -> A -> Prop.

  (**Properties of R and Eqa *)
  Variable R_wf : well_founded R.
  Variable R_trans : forall a1 a2 a3, R a1 a2 -> R a2 a3 -> R a1 a3.
  Variable Eqa_eq : equivalence _ Eqa.
  Variable R_total :
    forall a1 a2, {R a1 a2} + {Eqa a1 a2} + {R a2 a1}.
  Variable R_irref :
    forall a1 a2, R a1 a2 -> ~ Eqa a1 a2.

  (* A method for updating the accumulator *)
  Variable Accum : A -> B -> B.

  (* The queue update rule *)
  Variable f : A -> list A.
  
  (* Stack updates respect the queue relation *)
  Variable f_desc : forall a a', In a' (f a) -> R a' a.

  (* A program constructed using IterQueueWithAccum *)
  Definition QueueProg :=
    IterQueueWithAccum A B R Eqa R_wf R_trans Eqa_eq
      R_total R_irref Accum f f_desc.

  (* A program constructed using IterStackWithAccum *)
  Definition StackProg :=
    IterStackWithAccum A B R R_wf Accum f f_desc.

  (* Some property of the accumlated value *)
  Variable P : B -> Prop.

  Lemma QP_nil : 
    forall b, QueueProg (nil, b) = (nil, b).
  Proof.
    intros. unfold QueueProg.
    unfold IterQueueWithAccum.
    rewrite Init.Wf.Fix_eq; auto.
    intros. destruct mkSmallerQueue; auto. destruct s. apply H.
  Qed.

  Lemma QP_cons :
    forall p l b, QueueProg ((p::l), b) = QueueProg ((l ++ (f p)), Accum p b).
  Proof.
    intros. unfold QueueProg, IterQueueWithAccum.
    rewrite Init.Wf.Fix_eq; simpl. auto.
    intros. destruct mkSmallerQueue; auto. destruct s. apply H.
  Qed.

  Lemma SP_nil : 
    forall b, StackProg (nil, b) = (nil, b).
  Proof.
    intros. unfold StackProg.
    unfold IterStackWithAccum.
    rewrite Init.Wf.Fix_eq; auto.
    intros. destruct mkSmallerStack; auto. destruct s. apply H.
  Qed.

  Lemma SP_cons :
    forall p l b, StackProg ((p::l), b) = StackProg (((f p) ++ (l)), Accum p b).
  Proof.
    intros. unfold StackProg, IterStackWithAccum.
    rewrite Init.Wf.Fix_eq; simpl. auto.
    intros. destruct mkSmallerStack; auto. destruct s. apply H.
  Qed.


Notation indStackR := (iterStackRel_wf A R R_wf).
Notation indQueueR := (queueR_wf A R Eqa R_wf R_trans Eqa_eq R_total R_irref).

 Lemma StackApp : 
    forall l1 l2 b, StackProg ((l1 ++ l2), b) =
                  StackProg ((l2, (snd (StackProg (l1, b))))).
  Proof.
    induction l1 using (well_founded_induction indStackR).
    induction l1.
    + intros. rewrite app_nil_l. simpl; auto.
    + intros. simpl; do 2 rewrite SP_cons.
      specialize (H (f a ++ l1)).
      assert (iterStackRel A R (f a ++ l1) (a :: l1)).
      constructor. apply f_desc. eapply H in H0.
      rewrite <- H0. rewrite app_assoc. auto.
  Qed.

  Variable Peq : B -> B -> Prop.
  Variable Peq_eq : equivalence _ Peq.

  Variable Accum_comm :
    forall a1 a2 b, Peq (Accum a1 (Accum a2 b)) (Accum a2 (Accum a1 b)).

  Variable Accum_resp :
    forall a b1 b2, Peq b1 b2 -> Peq (Accum a b1) (Accum a b2).

  Lemma Stack_resp :
    forall l b1 b2, Peq b1 b2 -> Peq (snd (StackProg (l, b1))) (snd (StackProg (l, b2))).
  Proof.
    induction l using (well_founded_induction indStackR). case_eq l.
    + intros. auto.
    + intros. do 2 rewrite SP_cons. apply H. subst.
      constructor. auto. apply Accum_resp. auto.
  Qed. 

  Lemma Accum_SP_comm :
    forall l a b, Peq (Accum a (snd (StackProg (l, b))))
                      (snd (StackProg (l, (Accum a b)))).
  Proof.
    induction l using (well_founded_induction indStackR).
    case_eq l.
    + intros. subst. simpl; auto. apply Peq_eq.
    + intros. subst. do 2 rewrite SP_cons.
      assert (iterStackRel A R (f a ++ l0) (a :: l0)).
      { constructor. auto. }
      specialize (H (f a ++ l0) H0 a0 (Accum a b)).
      inversion Peq_eq. eapply equiv_trans.
      apply H. apply Stack_resp.
      apply Accum_comm.
  Qed.
    
  Lemma Stack_App_eq :
    forall l1 l2 b, Peq (snd (StackProg (l2 ++ l1, b)))
                        (snd (StackProg (l1 ++ l2, b))).
  Proof.
    intros. do 2 rewrite StackApp.
    generalize dependent b. generalize dependent l2.
    induction l1 using (well_founded_induction indStackR).
    case_eq l1.
    - intros. subst. rewrite SP_nil; simpl. apply Peq_eq.
    - intros. subst. do 2 rewrite SP_cons.
      assert (iterStackRel A R (f a ++ l) (a :: l)).
      { constructor. auto. }
      specialize (H (f a ++ l) H0).
      assert (Peq (Accum a (snd (StackProg (l2, b))))
                 (snd (StackProg (l2, (Accum a b))))).
      apply Accum_SP_comm.
      inversion Peq_eq. eapply equiv_trans.
      eapply Stack_resp. apply H1.
      apply H.
  Qed.

  Lemma Stack_comm : 
    forall x y l b, Peq (snd (StackProg (x::y::l, b)))
                        (snd (StackProg (y::x::l, b))).
  Proof.
    intros x y l.
    replace (y::x::l) with (((y::nil)++(x::nil)) ++ l); [|simpl; auto].
    replace (x::y::l) with (((x::nil)++(y::nil)) ++ l); [|simpl; auto].
    intros.
    rewrite (StackApp ((x :: nil) ++ y :: nil) l b).
    rewrite (StackApp ((y :: nil) ++ x :: nil) l b).
    apply Stack_resp. apply Stack_App_eq.
  Qed.

  Lemma StackPerm :
    forall l1 l2, Permutation l1 l2 ->
      forall b, Peq (snd (StackProg (l1, b))) (snd (StackProg (l2, b))).
  Proof.
    intros l1 l2 H.
    induction H.
    + intros. apply Peq_eq.
    + intros. do 2 rewrite SP_cons. do 2 rewrite StackApp.
      apply IHPermutation.
    + intros. apply Stack_comm.
    + intros. destruct Peq_eq. eapply equiv_trans.
      apply IHPermutation1. apply IHPermutation2.
  Qed.

  Inductive QueueStepR : (list A * B) -> (list A * B) -> Prop :=
  | QStep : forall p1 p2 a l b,
              p1 = (a::l, b) ->
              p2 = (l ++ f a, Accum a b) -> QueueStepR p1 p2.

  Inductive StackStepR : (list A * B) -> (list A * B) -> Prop :=
  | SStep : forall p1 p2 a l b,
              p1 = (a::l, b) ->
              p2 = (f a ++ l, Accum a b) -> StackStepR p1 p2.


  Definition QueueBigStepR := clos_refl_trans  _ QueueStepR.
  Definition StackBigStepR := clos_refl_trans  _ StackStepR.

  Lemma QueueStepR_eq : forall p1 p2,
    QueueStepR p1 p2 -> QueueProg p1 = QueueProg p2.
  Proof.
    intros. inversion H; subst. rewrite QP_cons. auto.
  Qed.

  Lemma StackStepR_eq : forall p1 p2, 
    StackStepR p1 p2 -> StackProg p1 = StackProg p2.
  Proof.
    intros. inversion H; subst. rewrite SP_cons. auto.
  Qed.

  Lemma QueueBigStepR_end : forall p, QueueBigStepR p (QueueProg p).
  Proof.
    intros. destruct p. generalize b.
    induction l using (well_founded_induction indQueueR).
    intros. case_eq l.
    + intros. rewrite QP_nil. apply rt_refl.
    + intros. subst. rewrite QP_cons.
      eapply rt_trans. Focus 2.
      apply H. constructor. apply f_desc.
      apply rt_step. eapply QStep; eauto.
  Qed.

  Lemma StackBigStepR_end : forall p, StackBigStepR p (StackProg p).
  Proof.
    intros. destruct p. generalize b.
    induction l using (well_founded_induction indStackR).
    intros. case_eq l.
    + intros. apply rt_refl.
    + intros. subst. rewrite SP_cons.
      eapply rt_trans. Focus 2.
      apply H. constructor. apply f_desc.
      apply rt_step. eapply SStep; eauto.
  Qed.

  Lemma Simulation :
    forall l b, Peq (snd (StackProg (l, b))) (snd (QueueProg (l, b))).
  Proof.
    induction l using (well_founded_induction indQueueR).
    case_eq l.
    + intros. rewrite SP_nil, QP_nil. apply Peq_eq.
    + intros. subst. rewrite SP_cons, QP_cons.
      destruct Peq_eq. eapply equiv_trans.
      apply StackPerm with (l2 := l0 ++ f a).
      apply Permutation_app_comm.
      apply H. constructor. auto. 
  Qed.

End QueueStackSimulation.

Section TestAccStack.

  Definition genSingletonPred n : list nat :=
    match n with 
    | O => nil
    | S n' => n'::nil
    end.

  Definition genPairedSingletonPred (p : nat * bool) : list (nat * bool) :=
    match p with (n, b) =>
      match n with 
      | O => nil
      | S n' => (n',b)::nil
      end
    end.

  Definition Accum (p : nat * bool) (l : list bool) : list bool :=
    match p with (n, b) =>
      match n with
      | O => l
      | _ => cons b l
      end
    end.

  Lemma genPairedSingletonPred_desc :
    forall a a' : nat * bool,
      In a' (genPairedSingletonPred a) -> LeftProdRel nat bool lt a' a.
  Proof.
      intros a. destruct a. intros. case_eq n.
      - intros. subst. unfold genPairedSingletonPred in H. simpl. inversion H.
      - intros. subst. unfold genPairedSingletonPred in H. destruct a'.
        constructor. inversion H. inversion H0. subst. auto. inversion H0.
  Defined.

  Definition makeNBools : list (nat*bool) * list bool -> list (nat*bool) * list bool :=
    (IterStackWithAccum (nat * bool) (list bool)
          (LeftProdRel _ _ lt)
          (LeftProdRel_wf _ _ lt lt_wf)
          Accum
          genPairedSingletonPred genPairedSingletonPred_desc).

  Definition x := (makeNBools (((2, true)::nil), nil)).

  Ltac simplify_step :=
    repeat (auto; match goal with 
            | [ |- _ -> _] => intro
            | [ |- match ?x with _ => _ end = _] => destruct x 
            end).
  Ltac simplWf :=
    rewrite Init.Wf.Fix_eq; [simpl | simplify_step].

  Lemma bleh : x = (nil, (true::true::nil)).
  Proof.
    unfold x, makeNBools, IterStackWithAccum.
    repeat simplWf.
    auto.
  Qed.
End TestAccStack.