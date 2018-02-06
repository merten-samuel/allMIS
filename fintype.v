Set Implicit Arguments.

Require Import List.

Require Import eqtype.

Inductive uniq (A : Type) : list A -> Prop :=
| uniq_nil : uniq nil
| uniq_cons : forall x l, ~In x l -> uniq l -> uniq (x :: l).

Lemma filter_uniq (A : Type) (l : list A) (f : A -> bool) :
  uniq l -> uniq (filter f l).
Proof.
  induction l; auto.
  inversion 1; subst. simpl. destruct (f a). constructor; auto.
  intros H4. rewrite filter_In in H4. destruct H4. apply H2; auto.
  apply IHl; auto.
Qed.

Lemma filterEq_notIn (A : eqType) (l : list A) (a : A) :
  ~In a l ->
  filter (fun a' => negb (a == a')) l = l.
Proof.
  induction l; auto. simpl. destruct (eqP a a0); simpl.
  { subst a0. intros Contra. elimtype False. apply Contra. left; auto.
  }
  intros Contra. f_equal. rewrite IHl; auto.
Qed.  

Lemma length_filterEq_uniq (A : eqType) (l : list A) (a : A) :
  uniq l ->   
  In a l ->
  S (length (filter (fun a' => negb (a == a')) l)) = length l.
Proof.
  induction 1. inversion 1. inversion 1; subst; simpl.
  { destruct (eqP a a); simpl. rewrite filterEq_notIn; auto.
    elimtype False; apply n; auto.
  }
  destruct (eqP a x); simpl. subst x. contradiction.
  f_equal. apply IHuniq; auto.
Qed.  

Module FinType. 
  Record mixin_of (T : Type) :=
    Mixin { mx_enum : list T
          ; _ : forall t : T, In t mx_enum
          ; _ : uniq mx_enum
          }.

  Section classDef.
    Record class_of (T : Type) :=
      Class { base : EqType.class_of T
            ; mixin : mixin_of T
            }.
    
    Structure type : Type := Pack { sort; _ : class_of sort; _ : Type}.
    Local Coercion sort : type >-> Sortclass.

    Variable (T : Type) (cT : type).
    
    Definition class : class_of cT :=
      match cT as cT' return class_of cT' with
        | @Pack _ c _ => c
      end.

    Definition clone (c : class_of T) (ph : phant_id class c) := @Pack T c T.

    Definition pack (m0 : mixin_of T) :=
      fun bT b (_ : phant_id (EqType.class bT) b) =>      
        fun m (_ : phant_id m0 m) => Pack (@Class T b m) T.

    Definition enum := mx_enum (mixin class).
  End classDef.

  Module Exports.
    Coercion sort : type >-> Sortclass.

    Definition eqType_of (fT : type) : eqType := EqType.Pack (base (class fT)) fT.
    Canonical Structure eqType_of.
    
    Notation finType := FinType.type.
    Notation finTypeMixin := FinType.Mixin.
    Notation FinType T m := (@pack T _ _ _ id m id).

    Notation "[ 'finType' 'of' T 'for' cT ]" := (@clone T cT _ id)
      (at level 0, format "[ 'finType'  'of'  T  'for'  cT ]").
    Notation "[ 'finType' 'of' T ]" := (@clone T _ _ id)
      (at level 0, format "[ 'finType'  'of'  T ]").

    Definition enum := enum.
    
    Section laws.
      Context {T : finType}.

      Lemma enumP : forall t : T, In t (@enum T).
      Proof. destruct T; destruct c; destruct mixin0; auto. Qed.

      Lemma uniqP : uniq (@enum T).
      Proof. destruct T; destruct c; destruct mixin0; auto. Qed.  
    End laws.
      
    Arguments enum [cT].
  End Exports.
End FinType.

Export FinType.Exports.

(* The cardinality of a finType *)

Definition card (A : finType) := length (enum (cT:=A)).

Inductive bij {A B : eqType} : list A -> list B -> Prop :=
| bij_nil : bij nil nil
| bij_cons : forall a b l1 l2,
               uniq (a :: l1) ->
               uniq l2 ->
               In b l2 -> 
               bij l1 (filter (fun b' => negb (b == b')) l2) ->
               bij (a :: l1) l2.

Lemma bijP (A B : finType) (f : A -> B) :
  (forall b, exists a, f a = b) ->
  (forall a1 a2, f a1 = f a2 -> a1 = a2) -> 
  bij (enum (cT:=A)) (enum (cT:=B)).
Proof.
  intros H H2.
  generalize (uniqP (T:=A)). intros H3.
  generalize (uniqP (T:=B)). intros H4.
  generalize (enumP (T:=A)). intros H5.  
  generalize (enumP (T:=B)). intros H6.
  revert H4. induction H3.
Abort.  (* TODO *)

Lemma bij_card (A B : finType) :
  bij (enum (cT:=A)) (enum (cT:=B)) ->
  card A = card B.
Proof.
  intros H; unfold card. induction H; auto.
  simpl. rewrite IHbij. rewrite length_filterEq_uniq; auto.
Qed.  
  
(* finType unit *)

Program Definition finType_unit_mixin := @finTypeMixin _ (tt::nil) _ _.
Next Obligation.
  destruct t; left; auto.
Qed.
Next Obligation.
  constructor; auto.
  constructor.
Qed.  

Definition finType_unit : finType :=
  Eval hnf in FinType unit finType_unit_mixin.

Canonical Structure finType_unit.

Lemma card_unit : card [finType of unit] = 1.
Proof.
  unfold card; auto.
Qed.    
    
(* finType bool *)

Program Definition finType_bool_mixin := @finTypeMixin _ (false::true::nil) _ _.
Next Obligation.
  destruct t.
  right; left; auto.
  left; auto.
Qed.
Next Obligation.
  constructor; auto.
  intros H; inversion H; try congruence. inversion H0.
  constructor; auto.
  constructor.
Qed.  

Definition finType_bool : finType :=
  Eval hnf in FinType bool finType_bool_mixin.

Canonical Structure finType_bool.

Lemma card_bool : card [finType of bool] = 2.
Proof.
  unfold card.
  unfold enum.
  simpl; auto.
Qed.    

(* finType prod *)

Fixpoint all_pairs_aux (A B : Type) (x : A) (l2 : list B) : list (A*B) :=
  match l2 with
    | nil => nil
    | y :: l2' => (x,y) :: all_pairs_aux x l2'
  end.

Lemma all_pairs_auxP (A B : Type) (x : A) (l2 : list B) (b : B) :
  In b l2 ->
  In (x,b) (all_pairs_aux x l2).
Proof.
  induction l2; auto; simpl; inversion 1; subst; auto.
Qed.  

Fixpoint all_pairs (A B : Type) (l1 : list A) (l2 : list B) : list (A*B) :=
  match l1 with
    | nil => nil
    | x :: l1' => all_pairs_aux x l2 ++ all_pairs l1' l2
  end.

Lemma all_pairsP (A B : Type) (l1 : list A) (l2 : list B) (a : A) (b : B) :
  In a l1 ->
  In b l2 ->
  In (a,b) (all_pairs l1 l2).
Proof.
  induction l1; auto; inversion 1; subst.
  { intros H2; simpl; rewrite in_app_iff; left.
    apply all_pairs_auxP; auto.
  }
  intros H1; simpl; rewrite in_app_iff; right.
  apply IHl1; auto.
Qed.  

Fixpoint remove_dups {A : Type} {B : eqType} (f : A -> B) (l : list A) :=
  match l with
    | nil => nil
    | x :: l' => x :: filter (fun y => negb (f x == f y)) (remove_dups f l')
  end.

Lemma remove_dupsP (A : eqType) (l : list A) x :
  In x l ->
  In x (remove_dups id l).
Proof.
  induction l; auto; destruct (eqP x a).
  { subst x; intros H; simpl. left; auto.
  }
  inversion 1; subst. elimtype False; auto. 
  simpl. right. rewrite filter_In. split; auto.
  unfold id. destruct (eqP a x); auto.
Qed.  

Lemma remove_dups_uniq (A : eqType) (l : list A) : uniq (remove_dups id l).
Proof.
  induction l.
  { simpl; constructor.
  }
  simpl; constructor.
  intros H. rewrite filter_In in H. destruct H. unfold id in H0.
  destruct (eqP a a). simpl in H0. congruence. apply n; auto.
  apply filter_uniq; auto.
Qed.  

Program Definition finType_pair_mixin (A B : finType) :=
  @finTypeMixin _ (remove_dups id (all_pairs (A:=A) (B:=B) enum enum)) _ _.
Next Obligation.
  apply remove_dupsP.
  apply all_pairsP.
  apply enumP.
  apply enumP.
Qed.
Next Obligation.
  apply remove_dups_uniq.
Qed.  

Definition finType_pair (A B : finType) : finType :=
  Eval hnf in FinType (A*B) (finType_pair_mixin A B).

Canonical Structure finType_pair.
  
(* eqTypes lift through arrow. We put this instance in fintype.v
   because it depends on [finType]. *)

Require Import FunctionalExtensionality.

Lemma map_enum_eq {A : finType} {B : eqType} (f g : A -> B) :
  map f enum = map g enum <-> f = g.
Proof.
  generalize (enumP (T:=A)).
  generalize (enum (cT:=A)).
  intros l H. split.
  { intros H2.
    extensionality x.
    specialize (H x).
    induction l. inversion H.
    inversion H.
    { subst. clear H. simpl in H2. inversion H2; auto. }
    simpl in H2. inversion H2. apply IHl; auto.
  }
  intros <-; auto.
Qed.  

Program Definition eqType_fun_mixin (A : finType) (B : eqType) :=
  @eqTypeMixin (A -> B) (fun f g => map f enum == map g enum) _.
Next Obligation.
  specialize (map_enum_eq x y).
  generalize (enum (cT:=A)).
  intros l.
  destruct (eqP (map x l) (map y l)).
  { intros; constructor; rewrite <-H; auto.
  }
  intros H; constructor; intros Contra; apply n.
  rewrite H; auto.
Qed.  

Definition eqType_fun (A : finType) (B : eqType) : eqType :=
  Eval hnf in EqType (A -> B) (eqType_fun_mixin A B).

Canonical Structure eqType_fun.

(* finTypes lift through arrow.  The construction is, enumerate all
   graphs of A -> B. *)

Definition list_subset (A : Type) (l1 l2 : list A) :=
  forall x, In x l1 -> In x l2.

Lemma list_subset_refl (A : Type) (l : list A) : list_subset l l.
Proof.
  unfold list_subset; intros x; auto.
Qed.  

Fixpoint all_subsets {A : Type} (l : list A) : list (list A) :=
  match l with
    | nil => nil::nil
    | x :: l' =>
      let s := all_subsets l'
      in s ++ map (fun l0 => x :: l0) s
  end.

Lemma all_subsets_list_subset A (l : list A) :
  forall l0, In l0 (all_subsets l) -> list_subset l0 l.
Proof.
  induction l.
  { simpl. intros. destruct H. subst l0. apply list_subset_refl.
    destruct H.
  }
  intros l0; simpl; rewrite in_app_iff; intros [H|H].
  { apply IHl in H. intros x H2. right. apply H; auto.
  }
  intros x H2; rewrite in_map_iff in H; destruct H as [l' [H H3]].
  subst l0. inversion H2; subst. left; auto.
  right. apply IHl in H3; apply H3; auto.
Qed.  

Fixpoint listrel_in {A : eqType} (B : Type) (l : list (A*B)) (x : A) : bool :=
  match l with
    | nil => false
    | (y,_) :: l' => orb (x == y) (listrel_in l' x)
  end.

Lemma listrel_inP {A : eqType} B (l : list (A*B)) x :
  listrel_in l x = true ->
  sigT (fun y => In (x,y) l).
Proof.
  induction l; simpl.
  { inversion 1.
  }
  destruct a; intros H; destruct (eqP x s); simpl in H.
  { subst s; exists b; left; auto.
  }
  apply IHl in H; destruct H as [y H].
  exists y; right; auto.
Defined.
  
Definition listrel_total {A : finType} {B : Type} (l : list (A*B)) : bool :=
  forallb (fun x => listrel_in l x) (enum (cT:=A)).  
  
Fixpoint listrel_bind_of_aux {A : eqType} (B : Type) (l : list (A*B)) (x : A) :=
  match l with
    | nil => None
    | (y,b) :: l' => if x == y then Some b else listrel_bind_of_aux l' x
  end.

Lemma listrel_total_bind_of_some {A : finType} (B : Type) (l : list (A*B)) x :
  listrel_total l = true ->
  sigT (fun y => listrel_bind_of_aux l x = Some y).
Proof.
  unfold listrel_total; intros H; rewrite forallb_forall in H.
  specialize (H x (enumP x)); induction l.
  { inversion H.
  }
  simpl in H. destruct a. destruct (eqP x s).
  { subst s. simpl. destruct (eqP x x); auto. exists b; auto.
  }
  simpl in H. apply IHl in H. destruct H as [y H]. exists y.
  simpl. destruct (eqP x s); auto. elimtype False; apply n; auto.
Defined.

Definition fun_of_listrel
           {A : finType} {B : Type}
           (l : list (A*B)) (H : listrel_total l = true) : A -> B :=
  fun a => projT1 (listrel_total_bind_of_some l a H).

Definition all_graphs (A B : finType) :=
  filter listrel_total (all_subsets (enum (cT:=[finType of (A*B)%type]))).

Lemma filter_forallb A (l : list A) (f : A -> bool) :
  forallb f (filter f l) = true.
Proof.
  induction l; auto.
  simpl. destruct (f a) eqn:H. simpl. rewrite H. auto. apply IHl.
Defined.

Lemma all_graphs_total (A B : finType) :
  forallb listrel_total (all_graphs A B) = true.
Proof.
  unfold all_graphs; rewrite filter_forallb; auto.
Defined.

Fixpoint map_filter_aux
        A B (l : list A)
        (f : A -> bool) (g : forall x : A, f x = true -> B)
        (H : forallb f l = true) {struct l} : list B.
  destruct l as [|x l'].
  refine nil.
  simpl in H. rewrite Bool.andb_comm in H. destruct (forallb f l') eqn:H2.
  refine (let l'' := map_filter_aux _ _ l' f g H2 in _).
  rewrite Bool.andb_comm in H. destruct (f x) eqn:H3.
  refine (g x H3 :: l'').
  simpl in H. congruence.
  simpl in H. congruence.
Defined.

Definition map_filter
           A B (l : list A)
           (f : A -> bool) (g : forall x : A, f x = true -> B) : list B :=
  (match filter f l as l' return l' = _ -> _ with
     | l' => fun Heq => map_filter_aux l' f g (filter_forallb _ _)
   end) eq_refl.
