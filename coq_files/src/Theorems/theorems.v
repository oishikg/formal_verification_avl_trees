(* Imports: *) 
Require Import Hbt.Lemmas.Ordered.ordered_main.


(* ***** Section 1: Specification and associated theorems for lookup ***** *)

(* The specification *)
Definition specification_of_occurs_hbt
           (A : Type)
           (compare : A -> A -> element_comparison)
           (occ_hbt : forall (A' : Type),
               (A' -> A' -> element_comparison)
               -> A'
               -> heightened_binary_tree A'
               -> bool) :=
  forall (e : A)
         (h : nat)
         (bt : binary_tree A),
  exists (occ_bt : forall (A' : Type),
             (A' -> A' -> element_comparison) -> A' -> binary_tree A' -> bool),
    occ_hbt A compare e (HNode A h bt) = occ_bt A compare e bt.

Definition specification_of_occurs_bt
           (A : Type)
           (compare : A -> A -> element_comparison)
           (occ_bt : forall (A' : Type),
               (A' -> A' -> element_comparison)
               -> A'
               -> binary_tree A'
               -> bool) :=
  (forall (e : A),
      occ_bt A compare e (Leaf A) = false)
  /\
  (forall (e : A)
          (t : triple A),
      exists (occ_t : forall (A' : Type),
                 (A' -> A' -> element_comparison) -> A' -> triple A' -> bool),
        occ_bt A compare e (Node A t) = occ_t A compare e t).

Definition specification_of_occurs_t
           (A : Type)
           (compare : A -> A -> element_comparison)
           (occ_t : forall (A' : Type),
               (A' -> A' -> element_comparison)
               -> A'
               -> triple A'
               -> bool) :=
  forall (e e' : A)
         (hbt1 hbt2 : heightened_binary_tree A),
    exists (occ_hbt : forall (A' : Type),
               (A' -> A' -> element_comparison)
               -> A'
               -> heightened_binary_tree A'
               -> bool),
      occ_t A compare e (Triple A hbt1 e' hbt2) =
      match compare e e' with
      | Lt =>
        occ_hbt A compare e hbt1
      | Eq =>
        true
      | Gt =>
        occ_hbt A compare e hbt2
      end.
                
    

(* Theorem to show that occurs_hbt, occurs_bt, and occurs_t meet their respective  *)
(*  * specifications *)
Theorem occurs_implementation_satisfies_its_specification:
  forall (A : Type)
         (compare : A -> A -> element_comparison),
  (specification_of_occurs_hbt A compare occurs_hbt)
  /\
  (specification_of_occurs_bt A compare occurs_bt)
  /\
  (specification_of_occurs_t A compare occurs_t).
Proof.
  intros A compare.
  split.

  - unfold specification_of_occurs_hbt.
    intros e h bt.
    exists occurs_bt.
    reflexivity.

  - split.
    unfold specification_of_occurs_bt.
    split.
    intro e.
    rewrite -> (unfold_occurs_bt_leaf A compare e).
    reflexivity.
    intros e t.
    exists occurs_t.
    Check (unfold_occurs_bt_node).
    rewrite -> (unfold_occurs_bt_node A compare e t).
    reflexivity.

    unfold specification_of_occurs_t.
    intros e e' hbt1 hbt2.
    exists occurs_hbt.
    Check (unfold_occurs_t).
    rewrite -> (unfold_occurs_t A compare e e' hbt1 hbt2).
    reflexivity.
Qed.

(* ***** Section 2: The specifications and theorems for insert  ***** *)

Definition specifiction_of_insert_hbt
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
  
Theorem insert_hbt_satisfies_its_specification:
  forall (A : Type)
         (compare : A -> A -> element_comparison)
         (x : A),
    specifiction_of_insert_hbt A compare x insert_hbt. 
Proof.
  intros A compare.
  unfold specifiction_of_insert_hbt.
  intros x hbt H_sound_init H_bal_init H_order_init H_compare.
  unfold insert_hbt.
  case (insert_hbt_helper A compare x hbt) as [ hbt' | ] eqn : C.

  - Check (insertion_preserves_soundness).
    destruct (insertion_preserves_soundness A compare x) as
        [H_hbt_sound _].
    split.

    + exact (H_hbt_sound hbt hbt' H_sound_init C).

    + destruct (insertion_preserves_balance A compare x) as
          [H_hbt_balance _].
      split.
      exact (H_hbt_balance hbt hbt' H_sound_init H_bal_init C).

      
      Check (insertion_preserves_order).
      destruct (insertion_preserves_order A compare x H_compare) as [H_ord _].
      exact (H_ord hbt hbt' H_sound_init H_bal_init H_order_init C).

  - split.
    exact H_sound_init.
    split.

    exact H_bal_init.

    exact H_order_init.
Qed.