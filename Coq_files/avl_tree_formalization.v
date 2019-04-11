(* Formalization of Professor Danvy's formalization of AVL Trees 
 * in Coq; refer to the implementation in week-02b_balanced-binary-trees.ml *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Oishik Ganguly <oishik.ganguly@u.yale-nus.edu.sg> *)


(* ********** *)

(* Paraphernalia: *)
 
Ltac unfold_tactic name := intros; unfold name; (* fold name; *) reflexivity.

Require Import Arith Bool.

Notation "A =n= B" :=
  (beq_nat A B) (at level 70, right associativity).

(* ********** *)

(* Coq formalization of polymorphic ordinary binary tree implementation *)

Inductive ordinary_binary_tree (A : Type) : Type :=
| OLeaf : ordinary_binary_tree A
| ONode : ordinary_binary_tree A -> A -> ordinary_binary_tree A.

(* ********** *)

(* Coq formalization of polymorphic AVL tree implementation *)

Inductive triple (A : Type) : Type :=
                       

(* ********** *)

(* To be implemented: 
 * Formalization of 'a heightened_binary_tree
 * flatten_binary_tree
 * is_sound
 * is_balanced
 * is_ordered
 * occurs (both list and listless?) 
 * rotate_left
 * rotate_right
 * insert
 * factor_rightmost
 * factor_leftmost
 * delete
 *) 
