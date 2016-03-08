Require Import List.
Require Import Arith.
Require Import Omega.

Require Import graph_basics.
Require Import all_MIS.
Require Import index.


Fixpoint raise_EdgeList (x : nat) (L : list (nat*nat)) :  list ((Ix x)*(Ix x)) := 
  match L with
  | nil => nil
  | l::L' =>
    match l with (l1, l2) =>
      match lt_dec l1 x with
      | left H0 => 
        match lt_dec l2 x with
        | left H1 => ((@Index.mk x l1 H0), (@Index.mk x l2 H1)) :: raise_EdgeList x L' 
        | right H1 => raise_EdgeList x L' 
        end
      | right H0 => raise_EdgeList x L' 
      end
    end
  end.

Ltac split_disj :=
  repeat match goal with 
  | [ H : ?H1 \/ ?H2 |- _ ] => destruct H
  end. 

(*
Ltac solve_disj :=
*)

(*

  0    1

*)

Definition edge_list1 :=
  raise_EdgeList (2) (nil).

Theorem edge_list1_irref :
  forall x, ~ In (x,x) edge_list1.
Proof.
  intros. simpl. auto.
Qed.

Theorem edge_list1_symm :
  forall x y, In (x,y) edge_list1 <-> In (y,x) edge_list1.
Proof.
  intros. simpl; split; auto.
Qed.

Definition test_graph1 :=
  mkListGraph 2 edge_list1 edge_list1_irref edge_list1_symm.

Example MIS_test1 : PrintMIS test_graph1 = (1::0::nil)::nil.
Proof.
  reflexivity.
Qed.

(*

  0 1 2 3 4

*)

Definition edge_list2 :=
  raise_EdgeList (5) (nil).

Theorem edge_list2_irref :
  forall x, ~ In (x,x) edge_list2.
Proof.
  intros. simpl. auto.
Qed.

Theorem edge_list2_symm :
  forall x y, In (x,y) edge_list2 <-> In (y,x) edge_list2.
Proof.
  intros. simpl; split; auto.
Qed.

Definition test_graph2 :=
  mkListGraph 5 edge_list2 edge_list2_irref edge_list2_symm.

Example MIS_test2 : PrintMIS test_graph2 = (4::3::2::1::0::nil)::nil.
Proof.
  reflexivity.
Qed.

(* 

  0---1

*)
Definition edge_list3 :=
  raise_EdgeList (2) ((0,1)::(1,0)::nil).

Theorem edge_list3_irref :
  forall x, ~ In (x,x) edge_list3.
Proof.
  intros x H0. unfold edge_list3 in H0. simpl raise_EdgeList in H0.
  simpl In in H0; split_disj; try (inversion H; inversion H2).
Qed.

Theorem edge_list3_symm :
  forall x y, In (x,y) edge_list3 <-> In (y,x) edge_list3.
Proof.
  intros x H0. unfold edge_list3 in *. simpl. split; intros;
  simpl In in H; split_disj; inversion H; intuition.
Qed.

Definition test_graph3 :=
  mkListGraph 2 edge_list3 edge_list3_irref edge_list3_symm.

Example MIS_test3 : PrintMIS test_graph3 = (1::nil)::(0::nil)::nil.
Proof.
  reflexivity. 
Qed.

(*

  0
 / \
1---2

*)
Definition edge_list4 :=
  raise_EdgeList 
    3
    ((0,1)::(1,0)::
     (1,2)::(2,1)::
     (2,0)::(0,2)::nil).

Theorem edge_list4_irref :
  forall x, ~ In (x,x) edge_list4.
Proof.
  intros x H0. unfold edge_list4 in H0. simpl raise_EdgeList in H0.
  simpl In in H0; split_disj; try (inversion H; inversion H2).
Qed.

Theorem edge_list4_symm :
forall x y, In (x,y) edge_list4 <-> In (y,x) edge_list4.
Proof.
  intros x H0. unfold edge_list3 in *. simpl. split; intros;
  simpl In in H; split_disj; inversion H; intuition.
Qed.

Definition test_graph4 :=
  mkListGraph 3 edge_list4 edge_list4_irref edge_list4_symm.

Example MIS_test4 : PrintMIS test_graph4 = (1::nil)::(2::nil)::(0::nil)::nil.
Proof. reflexivity. Qed.

(*
  1
 / \
0   2
*)

Definition edge_list5 :=
  raise_EdgeList
    3
    ((0,1)::(1,0)::
     (1,2)::(2,1):: nil).

Theorem edge_list5_irref :
  forall x, ~ In (x,x) edge_list5.
Proof.
  intros x H0. unfold edge_list5 in H0. simpl raise_EdgeList in H0.
  simpl In in H0; split_disj; try (inversion H; inversion H2).
Qed.

Theorem edge_list5_symm :
forall x y, In (x,y) edge_list5 <-> In (y,x) edge_list5.
Proof.
  intros x H0. unfold edge_list3 in *. simpl. split; intros;
  simpl In in H; split_disj; inversion H; intuition.
Qed.

Definition test_graph5 :=
  mkListGraph 3 edge_list5 edge_list5_irref edge_list5_symm.

Example MIS_test5 : PrintMIS test_graph5 = ((1::nil)::(2::0::nil)::nil).
Proof. reflexivity. Qed.

Definition edge_list6 :=
  raise_EdgeList
    4
    ((0,1)::(1,0)::
     (1,2)::(2,1)::
     (2,3)::(3,2)::
     (3,0)::(0,3)::nil).

Theorem edge_list6_irref :
  forall x, ~ In (x,x) edge_list6.
Proof.
  intros x H0. unfold edge_list6 in H0. simpl raise_EdgeList in H0.
  simpl In in H0; split_disj; try (inversion H; inversion H2).
Qed.

Theorem edge_list6_symm :
forall x y, In (x,y) edge_list6 <-> In (y,x) edge_list6.
Proof.
  intros x H0. unfold edge_list3 in *. simpl. split; intros;
  simpl In in H; split_disj; inversion H; intuition.
Qed.

Definition test_graph6 :=
  mkListGraph 4 edge_list6 edge_list6_irref edge_list6_symm.

Example MIS_test6 : PrintMIS test_graph6 = ((3::1::nil)::(2::0::nil)::nil).
Proof. reflexivity. Qed.
