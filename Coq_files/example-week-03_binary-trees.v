(* week-03_binary-trees.v *)
(* YSC3236 2017-2018, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of 29 Aug 2017 *)

(* ********** *)

(* Paraphernalia: *)
 
Ltac unfold_tactic name := intros; unfold name; (* fold name; *) reflexivity.

Require Import Arith Bool.

Notation "A =n= B" :=
  (beq_nat A B) (at level 70, right associativity).

(* ********** *)

(* Inductive defintion of binary tree type *)
Inductive binary_tree : Type :=
| Leaf : nat -> binary_tree
| Node : binary_tree -> binary_tree -> binary_tree.

(* Unit test (clarify why this is requried)  *)
Definition test_number_of_leaves (candidate: binary_tree -> nat) :=
  (candidate (Leaf 1) =n= 1)
  &&
  (candidate (Node (Leaf 1) (Leaf 2)) =n= 2)
  &&
  (candidate (Node (Node (Leaf 1) (Leaf 2)) (Leaf 3)) =n= 3)
  (* etc. *)
  .

  (*Recursive function defined on number of leaves in tree *)
Fixpoint number_of_leaves (t : binary_tree) : nat :=
  match t with
    Leaf n =>
    1
  | Node t1 t2 =>
    (number_of_leaves t1) + (number_of_leaves t2)
  end.

  Compute (test_number_of_leaves number_of_leaves).
  
(* What is an unfold lemma? Given a particular datastructure
 and a particular property of its, in this case, number_of_leaves, 
nwe require an unfold lemma to make use of this property.  *)
Lemma unfold_number_of_leaves_Leaf :
  forall n : nat,
    number_of_leaves (Leaf n) =
    1.
Proof.
  unfold_tactic number_of_leaves.
Qed.

Lemma unfold_number_of_leaves_Nodes :
  forall t1 t2 : binary_tree,
    number_of_leaves (Node t1 t2) =
    (number_of_leaves t1) + (number_of_leaves t2).
Proof.
  unfold_tactic number_of_leaves.
Qed.

Fixpoint number_of_nodes (t : binary_tree) : nat :=
  match t with
    Leaf n =>
    0
  | Node t1 t2 =>
    S ((number_of_nodes t1) + (number_of_nodes t2))
  end.

Lemma unfold_number_of_nodes_Leaf :
  forall n : nat,
    number_of_nodes (Leaf n) =
    0.
Proof.
  unfold_tactic number_of_nodes.
Qed.

Lemma unfold_number_of_nodes_Node :
  forall t1 t2 : binary_tree,
    number_of_nodes (Node t1 t2) =
    S ((number_of_nodes t1) + (number_of_nodes t2)).
Proof.
  unfold_tactic number_of_nodes.
Qed.

Theorem on_the_relative_number_of_leaves_and_nodes_in_a_binary_tree :
  forall t : binary_tree,
    number_of_leaves t = S (number_of_nodes t).
Proof.
  (* We introduce the tree t that we use in our proofs*)
  intro t.
  (* n refers to a leaf in the base case;
   * t1 and t2 are the subtrees in the induction hypothesis case. IH refers to the
   * induction hypotheses *)
  induction t as [n| t1 IH_t1 t2 IH_t2 ].

  (* finish this proof! *)
(* ********** *)

(* end of week-03_binary-trees.v *)
