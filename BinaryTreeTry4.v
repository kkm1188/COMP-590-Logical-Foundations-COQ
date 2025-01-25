Require Import FunctionalExtensionality. 
From Coq Require Import String.
From Coq Require Export Arith Omega.
From Coq Require Export Lia.
From Coq Require Export Datatypes.

Require Import Notations.
Require Import Ltac.
Require Import Logic.



Inductive reflect (P : Prop) : bool -> Set :=
  | ReflectT : P -> reflect P true
  | ReflectF : ~ P -> reflect P false.
#[global]
Hint Constructors reflect : bool.

(** if P is provable when b = true is provable, then P reflects b 

and vise versa **)

Theorem iff_reflect : forall P b, (P <-> b = true) -> reflect P b.
Proof.
  intros P b H. destruct b.
  - apply ReflectT. rewrite H. reflexivity.
  - apply ReflectF. rewrite H. intros H'. inversion H'.
Qed.


Theorem reflect_iff : forall P b, reflect P b -> (P <-> b = true).
Proof.
  intros P b H; split.
  - intro H'.
    inversion H. clear H. subst.
    + reflexivity.
    + contradiction.
  - intro H'; subst.
    inversion H. clear H. subst. assumption.
Qed.

(** proving propositional inequality operators are replections of boolean operators **)

Lemma eqb_reflect : forall x y, reflect (x = y) (x =? y).
Proof.
  intros x y. apply iff_reflect. symmetry.
  apply Nat.eqb_eq.
Qed.

Lemma ltb_reflect : forall x y, reflect (x < y) (x <? y).
Proof.
  intros x y. apply iff_reflect. symmetry.
  apply Nat.ltb_lt.
Qed.

Lemma leb_reflect : forall x y, reflect (x <= y) (x <=? y).
Proof.
  intros x y. apply iff_reflect. symmetry.
  apply Nat.leb_le.
Qed.

Ltac bdestruct X :=
  let H := fresh "H" in
    match X with
    | (?x =? ?y) =>
        destruct X eqn:H;
        [ apply beq_nat_true in H; subst |
          apply beq_nat_false in H ]
    | (?x <? ?y) =>
        destruct X eqn:H;
        [ apply Nat.ltb_lt in H; subst |
          apply Nat.ltb_ge in H ]
    | (?x <=? ?y) =>
        destruct X eqn:H;
        [ apply leb_complete in H; subst |
          apply leb_complete_conv in H ]
    | (?x ?= ?y) =>
        destruct X eqn:H;
        [ apply Nat.compare_eq_iff in H; subst |
          apply Nat.compare_lt_iff in H |
          apply Nat.compare_gt_iff in H ]
    end.

Inductive BT :=
  | Leaf: BT
  | Tree: BT -> nat -> BT -> BT.

Fixpoint ForallT (P : nat -> nat -> Prop) (tree : BT) (n : nat) : Prop :=
  match tree with
  | Leaf => True
  | Tree l v r => P v n /\ ForallT P l n /\ ForallT P r n
  end.

Definition lt_tree (tree : BT) (n : nat) : Prop :=
     ForallT lt tree n.
Definition gt_tree (tree : BT) (n : nat) : Prop := 
      ForallT gt tree n.

(* Binary search tree is a binary tree, such that, for every node, the
   left child and right child is a BST, and all left children is less
   than this node, all right children is greater than this node. *)
Fixpoint BT_Inv (tree : BT) : Prop :=
  match tree with
  | Leaf => True
  | Tree l v r => BT_Inv l /\ BT_Inv r /\ lt_tree l v /\ gt_tree r v
  end.

(**
Hint Constructors BT.
Hint Unfold ForallT lt_tree gt_tree BT_Inv.
**)

Definition is_empty (tree : BT) : bool :=
  match tree with
  | Leaf => true
  | Tree _ _ _ => false
  end.
(**
Fixpoint insert (value : nat) (tree : BT) : BT :=
  match tree with
  | Leaf => Node value Leaf Leaf
  | Node value' l r => if value <? value' then Node value' (insert value l) r
                        else if value' <? value then Node value' l (insert value r)
                        else Node value l r
  end.
**)
Fixpoint insert (t : BT) (n : nat) : BT :=
  match t with
  | Leaf => Tree Leaf n Leaf
  | Tree l v r => match n ?= v with
                  | Eq => t
                  | Lt => Tree (insert l n) v r
                  | Gt => Tree l  v(insert r n)
                  end
  end.

Fixpoint minimum (tree: BT) : option nat :=
  match tree with
  | Leaf => None
  | Tree Leaf v _ => Some v
  | Tree l _ _ => minimum l
  end.

Fixpoint delete_minimum (tree : BT) : BT :=
  match tree with
  | Leaf => Leaf
  | Tree Leaf _ r => r
  | Tree l v r => Tree (delete_minimum l) v r
  end.

Fixpoint delete (tree : BT) (n : nat) : BT :=
  match tree with
  | Leaf => Leaf
  | Tree l v r =>
      match n ?= v with
      | Lt => Tree (delete l n) v r
      | Gt => Tree l v (delete r n)
      | Eq => match l with
              | Leaf => r
              | _ => match minimum r with
                     | Some v' => Tree l v' (delete_minimum r) 
                     | None => l
                     end
              end
      end
  end.

Fixpoint lookup (d : nat)(t : BT) : bool :=
   match t with
  | Leaf => false
  | Tree l v r => match d ?= v with
                  | Eq => true
                  | Lt => lookup d l 
                  | Gt => lookup d r
                  end
  end.

Theorem empty_tree_BT : forall (n : nat), BT_Inv Leaf.
Proof.
 unfold is_empty.
 constructor. 
Qed.

Definition correct_tree : BT :=
  (Tree (Tree Leaf 2 Leaf) 4 (Tree Leaf 5 Leaf)).

Definition incorrect_tree : BT :=
    Tree (Tree Leaf 5 Leaf) 4 (Tree Leaf 2 Leaf).

Definition empty_BT : BT := Leaf.

Example is_BT_ex :
  BT_Inv correct_tree.
Proof.
  unfold correct_tree.
  repeat (constructor).
Qed.

Example not_BT_ex :
  BT_Inv incorrect_tree.
Proof.
  unfold incorrect_tree.  Abort.

Ltac unfold_tree :=
  repeat (
    unfold BT_Inv in *; 
    fold BT_Inv in *;
    unfold ForallT in *; 
    fold ForallT in *;
    unfold lt_tree in *; 
    fold lt_tree in *;
    unfold gt_tree in *; 
    fold gt_tree in *;
    unfold insert in *; 
    fold insert in *;
    unfold minimum in *; 
    fold minimum in *;
    unfold delete_minimum in *; 
    fold delete_minimum in *;
    unfold delete in *; 
    fold delete in *
  ).

(** Helper method for insert preservation **)

Lemma ForallT_insert :
  forall (P : nat -> nat -> Prop) (t : BT) (n0 n : nat),
    ForallT P t n -> P n0 n -> ForallT P (insert t n0) n.
Proof.
  intros op t.
  induction t; intros; unfold_tree.
  - auto.
  - intuition.
    bdestruct (n0 ?= n); unfold_tree; auto.
Qed.

(** Proves preservation when insert is less than value **)

Corollary lt_insert_preserve :
  forall (t : BT) (n0 n : nat),
    lt_tree t n -> n0 < n -> lt_tree (insert t n0) n.
Proof. intros. apply (ForallT_insert  lt t n0 n); auto. Qed.

(** Proves preservation when insert is greater than value **)

Corollary gt_insert_preserve :
  forall (t : BT) (n0 n : nat),
    gt_tree t n -> n < n0 -> gt_tree (insert t n0) n.
Proof. intros. apply (ForallT_insert  gt t n0 n); auto. Qed.

(** proves the correctness of insert + preservation **)

Theorem insert_proof :
  forall (t : BT) (n : nat), BT_Inv t -> BT_Inv (insert t n).
Proof.
  intros t.
  induction t; intros; unfold_tree.
  - simpl. auto.
  - bdestruct (n0 ?= n); unfold_tree.
    + auto.
    + intuition; auto.
      apply lt_insert_preserve; auto.
    + intuition; auto.
      apply gt_insert_preserve; auto.
Qed.

(** checks to ensure the new node is in the tree **)

Theorem is_nat_inserted :
  forall (t : BT) (n : nat), BT_Inv t -> lookup n (insert t n) = true.
Proof.
  intros. induction t.
  - simpl.
    rewrite Nat.compare_refl. auto.
  - simpl. unfold_tree. intuition.
    destruct (n ?= n0) eqn:H5; simpl; rewrite H5; auto.
Qed.

Lemma check_minimum_helper :
  forall (P : nat -> nat -> Prop) (t : BT) (n n0 : nat),
  ForallT P t n -> minimum t = Some n0 -> P n0 n.
Proof.
  intros op t.
  induction t; intros; unfold_tree.
  - inversion H0.
  - destruct t1.
    + inversion H0. subst. intuition.
    + apply IHt1; intuition.
Qed.

Corollary check_minimum_lt :
  forall (t : BT) (n n0 : nat),
  lt_tree t n -> minimum t = Some n0 -> n0 < n.
Proof. intros. apply (check_minimum_helper lt t n n0); auto. Qed.

Corollary check_minimum_gt :
  forall (t : BT) (n n0 : nat),
  gt_tree t n -> minimum t = Some n0 -> n0 > n.
Proof. intros. apply (check_minimum_helper gt t n n0); auto. Qed.

Lemma delete_minimum_proof :
  forall (t : BT) (n : nat),
  BT_Inv t -> minimum t = Some n -> delete_minimum t = delete t n.
Proof.
  intros t.
  induction t; intros; unfold_tree.
  - simpl. auto.
  - destruct t1.
    + inversion H0; clear H0. rewrite Nat.compare_refl. auto.
    + assert (n0 < n).
      { eapply check_minimum_lt; eauto. intuition. }
      rewrite nat_compare_lt in H1. rewrite H1.
      assert (delete_minimum (Tree t1_1 n1 t1_2) = delete (Tree t1_1 n1 t1_2) n0).
      { apply IHt1. intuition. auto. }
      rewrite H2. auto.
Qed. 
 
Lemma delete_preserve_helper :
  forall (P : nat -> nat -> Prop) (t : BT) (n0 n : nat),
    BT_Inv t -> ForallT P t n -> ForallT P (delete t n0) n.
Proof.
  intros op t.
  induction t; intros; unfold_tree.
  - auto.
  - bdestruct (n0 ?= n).
    + destruct t1; intuition.
      remember (Tree t1_1 n0 t1_2) as t1. clear Heqt1.
      destruct (minimum t2) eqn:H7.
      * assert (op n2 n1). { apply (check_minimum_helper op t2 n1 n2); auto. }
        rewrite (delete_minimum_proof t2 n2); auto.
        unfold_tree. intuition.
      * auto.
    + unfold_tree. intuition.
    + unfold_tree. intuition.
Qed.

Lemma tree_cmp_trans :
  forall (P : nat -> nat -> Prop) (t : BT) (n n0 : nat),
  (forall a b c, P a b -> P b c -> P a c) ->
  ForallT P t n -> P n n0 -> ForallT P t n0.
Proof.
  intros op t.
  induction t; intros; unfold_tree; auto; try intuition; eauto.
Qed. 

Corollary tree_lt_trans :
  forall (t : BT) (n n0 : nat), 
  lt_tree t n -> n < n0 -> lt_tree t n0.
Proof. intros. apply (tree_cmp_trans lt t n n0); auto. intros. omega. Qed.

Corollary tree_gt_trans :
  forall (t : BT) (n n0 : nat),
  gt_tree t n -> n > n0 -> gt_tree t n0.
Proof. intros. apply (tree_cmp_trans gt t n n0); auto. intros. omega. Qed.

Corollary tree_lt_n_delete_preserve :
  forall (t : BT) (n0 n : nat),
    BT_Inv t -> lt_tree t n -> lt_tree (delete t n0) n.
Proof. intros. apply (delete_preserve_helper lt t n0 n); auto. Qed.

Corollary tree_gt_n_delete_preserve :
  forall (t : BT) (n0 n : nat),
    BT_Inv t -> gt_tree t n -> gt_tree (delete t n0) n.
Proof. intros. apply (delete_preserve_helper gt t n0 n); auto. Qed.

Lemma delete_leftmost_gt_n :
  forall (t : BT) (n n0 : nat),
    BT_Inv t -> minimum t = Some n0 -> gt_tree t n -> gt_tree (delete_minimum t) n0.
Proof.
  intros t.
  induction t; intros; unfold_tree.
  - auto.
  - destruct t1.
    + inversion H0. subst. intuition.
    + remember (Tree t1_1 n2 t1_2) as t1. clear Heqt1.
      unfold_tree.
      assert (n1 < n). { intuition. eapply check_minimum_lt; eauto. }
      intuition.
      * eapply IHt1; eauto.
      * eapply tree_gt_trans; eauto.
Qed.
 

Theorem delete_correct : 
  forall (t : BT) (n : nat), BT_Inv t -> BT_Inv (delete t n).
Proof.
  intros t.
  induction t; intros; unfold_tree.
  - simpl. auto.
  - bdestruct (n0 ?= n); unfold_tree.
    + destruct t1.
      * intuition.
      * { destruct (minimum t2) eqn:H1.
          - remember (Tree t1_1 n0 t1_2) as t1. clear Heqt1.
            unfold_tree. intuition.
            + rewrite (delete_minimum_proof t2 n1); auto.
            + assert (n1 > n). { eapply check_minimum_gt. apply H4. apply H1. }
              eapply tree_lt_trans. eauto. omega.
            + eapply delete_leftmost_gt_n; eauto.
          - intuition.
        } 
    + intuition. auto. apply tree_lt_n_delete_preserve; auto.
    + intuition. auto. apply tree_gt_n_delete_preserve; auto.
Qed.


(**
Hint Resolve ltb_reflect leb_reflect eqb_reflect : bdestruct.

(** simplifies reflection and destruction so that we don't have to keep using the
tactics created above, it will do this for us **)

Ltac bdestruct X :=
  let H := fresh in let e := fresh "e" in
   evar (e: Prop);
   assert (H: reflect e X); subst e;
    [eauto with bdestruct
    | destruct H as [H|H];
       [ | try first [apply not_lt in H | apply not_le in H]]].
**)





