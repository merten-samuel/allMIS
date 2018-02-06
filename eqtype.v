Set Implicit Arguments.

Require Import Arith List.

CoInductive phantom (T : Type) (p : T) : Type := Phantom : @phantom T p.

Definition phant_id (T1 T2 : Type) (v1 : T1) (v2 : T2) : Prop :=
  @phantom T1 v1 -> @phantom T2 v2.

Inductive reflect (P : Prop) : bool -> Type :=
| ReflectT : P -> reflect P true
| ReflectF : ~P -> reflect P false.                     

Module EqType. 
  Record mixin_of (T : Type) :=
    Mixin { mx_eq : T -> T -> bool; _ : forall x y : T, reflect (x = y) (mx_eq x y) }.

  Section classDef.
    Record class_of (T : Type) := Class {mixin : mixin_of T}.
    
    Structure type : Type := Pack { sort : Type; _ : class_of sort; _ : Type}.
    Local Coercion sort : type >-> Sortclass.

    Variable (T : Type) (cT : type).
    
    Definition class : class_of cT :=
      match cT as cT' return class_of cT' with
        | @Pack _ c _ => c
      end.

    Definition clone (c : class_of T) (ph : phant_id class c) := @Pack T c T.

    Definition pack (m0 : mixin_of T) := fun m (_ : phant_id m0 m) => Pack (@Class T m) T.

    Definition eq := mx_eq (mixin class).    
  End classDef.

  Module Exports.
    Coercion sort : type >-> Sortclass.
    Notation eqType := EqType.type.
    Notation eqTypeMixin := EqType.Mixin.
    Notation EqType T m := (@pack T _ m (fun x => x)).

    Notation "[ 'eqType' 'of' T 'for' cT ]" := (@clone T cT _ id)
      (at level 0, format "[ 'eqType'  'of'  T  'for'  cT ]").
    Notation "[ 'eqType' 'of' T ]" := (@clone T _ _ id)
      (at level 0, format "[ 'eqType'  'of'  T ]").

    Notation "x == y" := (@eq _ x y) (at level 70).

    Arguments EqType.eq [cT] _ _.

    Section laws.
      Variable T : eqType.

      Lemma eqP (t1 t2 : T) : reflect (t1 = t2) (t1 == t2).
      Proof. destruct T; destruct c; destruct mixin0; apply r. Qed.
    End laws.

    Arguments eqP [_] _ _.
  End Exports.
End EqType.

Export EqType.Exports.

(* unit is an eqType *)

Program Definition eqType_unit_mixin :=
  @eqTypeMixin unit (fun _ _ => true) _.
Next Obligation. destruct x. destruct y. constructor; auto. Qed.

Definition eqType_unit : eqType := Eval hnf in EqType unit eqType_unit_mixin.

Canonical Structure eqType_unit.

(* nat is an eqType *)

Program Definition eqType_nat_mixin :=
  @eqTypeMixin nat beq_nat _.
Next Obligation.
  destruct (beq_nat x y) eqn:H.
  apply beq_nat_true in H; subst y; constructor; auto.
  apply beq_nat_false in H; constructor; auto.
Qed.

Definition eqType_nat : eqType := Eval hnf in EqType nat eqType_nat_mixin.

Canonical Structure eqType_nat.

(* bool is an eqType *)

Program Definition eqType_bool_mixin :=
  @eqTypeMixin bool Bool.eqb _.
Next Obligation.
  destruct (Bool.eqb x y) eqn:H.
  constructor. rewrite Bool.eqb_true_iff in H. auto.
  constructor. rewrite Bool.eqb_false_iff in H. auto.
Qed.  

Definition eqType_bool : eqType := Eval hnf in EqType bool eqType_bool_mixin.

Canonical Structure eqType_bool.

(* eqTypes lift through pair *)

Program Definition eqType_pair_mixin (A B : eqType) :=
  @eqTypeMixin (A*B) (fun p1 p2 =>
                        match p1, p2 with
                          | (a1,b1), (a2,b2) => andb (a1==a2) (b1==b2)
                        end) _.
Next Obligation.
  destruct (eqP s1 s); destruct (eqP s2 s0); try subst s s0; constructor; auto.
  intros Contra; elimtype False; inversion Contra; subst; auto.
  intros Contra; elimtype False; inversion Contra; subst; auto.
  intros Contra; elimtype False; inversion Contra; subst; auto.
Qed.  

Definition eqType_pair (A B : eqType) : eqType :=
  Eval hnf in EqType (A*B) (eqType_pair_mixin A B).

Canonical Structure eqType_pair.

(* eqTypes lift through list *)

Fixpoint lists_eq {A : eqType} (l1 l2 : list A) : bool :=
  match l1, l2 with
    | nil, nil => true
    | x :: l1', y :: l2' => andb (x == y) (lists_eq l1' l2')
    | _, _ => false
  end.

Lemma lists_eq_refl {A : eqType} (l : list A) : lists_eq l l = true.
Proof.
  induction l; auto. simpl. rewrite IHl. destruct (eqP a a); auto.
Qed.  

Lemma lists_eq_eq {A : eqType} (l1 l2 : list A) :
  reflect (l1 = l2) (lists_eq l1 l2).
Proof.
  revert l2; induction l1.
  { destruct l2.
    { constructor; auto. }
    constructor; inversion 1.
  }
  destruct l2.
  { constructor; inversion 1. }
  destruct (IHl1 l2).
  { subst l1. simpl. rewrite lists_eq_refl, Bool.andb_comm. simpl.
    destruct (eqP a s). subst s. constructor; auto.
    constructor. inversion 1. apply n; subst; auto.
  }
  simpl. destruct (IHl1 l2). subst l1; elimtype False; auto.
  rewrite Bool.andb_comm. constructor. inversion 1; subst; auto.
Qed.  

Definition eqType_list_mixin (A : eqType) :=
  @eqTypeMixin (list A) lists_eq lists_eq_eq.

Definition eqType_list (A : eqType) : eqType :=
  Eval hnf in EqType _ (eqType_list_mixin A).

Canonical Structure eqType_list.


