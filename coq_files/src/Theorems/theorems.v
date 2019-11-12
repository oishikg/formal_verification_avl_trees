(* ********** theorems.v ********** *)

(** The [theorems] library contains the specifications for the lookup and insert 
functions on AVL trees, and the theorems which show that our implementation of these
operations (see the [hbt] library) meet the specifications *)

Require Import Hbt.Lemmas.Ordered.Main.ordered_main.

Require dpdgraph.dpdgraph.

(* ********** *)

(** * Lookup *)

(** Defining the specification for a lookup function looking for some value <<x>>: 
- if the tree is a leaf, then the function should always return a [false] value
- if the tree is a node with a left sub-tree <<hbt1>>, a payload <<e>>, and a right sub-tree <<hbt2>>, then the function should compare <<x>> and <<e>>, returning true if the equality holds, checking <<hbt1>> if <<x>> is less than <<e>>, checking <<hbt2>> otherwise *)
Definition specification_of_occurs_hbt
           (A : Type)
           (compare : A -> A -> element_comparison)
           (occ_hbt : forall (A' : Type),
               (A' -> A' -> element_comparison)
               -> A'
               -> heightened_binary_tree A'
               -> bool) :=
  forall (hbt : heightened_binary_tree A)
         (x : A),
    specification_of_compare_defining_total_order A compare -> 
    (hbt = (HNode A 0 (Leaf A)) -> occ_hbt A compare x hbt = false)
    /\
    (forall (hbt1 hbt2 : heightened_binary_tree A)
            (h_hbt : nat)
            (e : A),
        hbt = (HNode A h_hbt (Node A (Triple A hbt1 e hbt2))) ->
        occ_hbt A compare x hbt =
        match compare x e with
        | Lt =>
          occ_hbt A compare x hbt1
        | Eq =>
          true
        | Gt =>
          occ_hbt A compare x hbt2
        end).

(** Theorem to show that our implementation of lookup on AVL trees, [occurs_hbt], 
meets the [specification_of_occurs_hbt] *)
Theorem occurs_implementation_satisfies_its_specification:
  forall (A : Type)
         (compare : A -> A -> element_comparison),
    specification_of_occurs_hbt A compare occurs_hbt.
Proof.
  intros.
  unfold specification_of_occurs_hbt.
  intros.
  split. 

  (* hbt is a leaf *)
  - intro.
    rewrite -> H0.
    rewrite -> unfold_occurs_hbt.
    rewrite -> unfold_occurs_bt_leaf.
    reflexivity.

  (* hbt is a node *)  
  - intros.
    rewrite -> H0.
    rewrite -> unfold_occurs_hbt.
    rewrite -> unfold_occurs_bt_node.
    rewrite -> unfold_occurs_t.
    reflexivity.
Qed.

(* ********** *)

(* ********** *)

(** * Insertion *)

(** Defining the specification for an insertion function on AVL trees: given a sound,
balanced, and ordered tree, inserting some element into this tree should give a tree 
that is also sound, balanced, and ordered *)
Definition specification_of_insert_hbt
           (A : Type)
           (compare : A -> A -> element_comparison)
           (x : A)
           (insert_hbt : forall (A' : Type),
               (A' -> A' -> element_comparison)
               -> A'
               -> heightened_binary_tree A'
               -> heightened_binary_tree A') :=
  forall (hbt : heightened_binary_tree A),
    (is_sound_hbt A hbt = true) ->
    (is_balanced_hbt A hbt = true) ->
    (is_ordered_hbt A hbt compare = true) ->
    (specification_of_compare_defining_total_order A compare) -> 
    (is_sound_hbt A (insert_hbt A compare x hbt) = true)
    /\
    (is_balanced_hbt A (insert_hbt A compare x hbt) = true)
    /\
    (is_ordered_hbt A (insert_hbt A compare x hbt) compare = true).
  
(** Theorem to show that our implementation of insertion on AVL trees, 
[insert_hbt] meets the [specifiction_of_insert_hbt] *)
Theorem insert_hbt_satisfies_its_specification:
  forall (A : Type)
         (compare : A -> A -> element_comparison)
         (x : A),
    specification_of_insert_hbt A compare x insert_hbt. 
Proof.
  intros A compare.
  unfold specification_of_insert_hbt.
  intros x hbt H_sound_init H_bal_init H_order_init H_compare.
  unfold insert_hbt.
  case (insert_hbt_helper A compare x hbt) as [ hbt' | ] eqn : C.

  - destruct (insertion_preserves_soundness A compare x) as
        [H_hbt_sound _].
    split.

    + exact (H_hbt_sound hbt hbt' H_sound_init C).

    + destruct (insertion_preserves_balance A compare x) as
          [H_hbt_balance _].
      split.
      exact (H_hbt_balance hbt hbt' H_sound_init H_bal_init C).

      destruct (insertion_preserves_order A compare x H_compare) as [H_ord _].
      exact (H_ord hbt hbt' H_sound_init H_bal_init H_order_init C).

  - split.
    exact H_sound_init.
    split.

    exact H_bal_init.

    exact H_order_init.
Qed.

(* To print dependnacy graph *)
(* Print DependGraph insert_hbt_satisfies_its_specification. *)

(* ********** *)

(* ********** End of theorems.v ********** *)
