(* Imports: *) 
Require Import Hbt.Lemmas.sound_balanced.
Require Import Hbt.Lemmas.ordered_main.


(* ***** Section 1: The specifications and theorems for insert  ***** *)

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
  intros x hbt H_sound_init H_bal_init H_order_init.
  unfold insert_hbt.
  case (insert_hbt_helper A compare x hbt) as [ hbt' | ] eqn : C.

  - assert (H_sound_bal:
            is_sound_hbt A hbt' = true
            /\
            is_balanced_hbt A hbt' = true).
    Check (insertion_preserves_soundness_and_balance).
    destruct (insertion_preserves_soundness_and_balance
                A compare x) as [H_for_soundness _].
    exact (H_for_soundness hbt hbt' H_sound_init H_bal_init C).

    destruct H_sound_bal as [H_sound H_bal].
    split.

    exact H_sound.
    split.

    exact H_bal.
    
    Check (insertion_preserves_order).
    destruct (insertion_preserves_order A compare x) as [H_ord _].
    exact (H_ord hbt hbt' H_sound_init H_bal_init H_order_init C).

  - split.
    exact H_sound_init.
    split.

    exact H_bal_init.

    exact H_order_init.
Qed.


(* ***** Section 2: Specifications and theorems for delete *)
Definition specifiction_of_delete_hbt
           (A : Type)
           (compare : A -> A -> element_comparison)
           (x : A)
           (delete_hbt : forall (A' : Type),
               (A' -> A' -> element_comparison)
               -> A'
               -> heightened_binary_tree A'
               -> heightened_binary_tree A') :=
  forall (hbt : heightened_binary_tree A),
    (is_sound_hbt A hbt = true) ->
    (is_balanced_hbt A hbt = true) ->
    (is_ordered_hbt A hbt compare = true) -> 
    (is_sound_hbt A (delete_hbt A compare x hbt) = true)
    /\
    (is_balanced_hbt A (delete_hbt A compare x hbt) = true)
    /\
    (is_ordered_hbt A (delete_hbt A compare x hbt) compare = true).




Theorem delete_hbt_satisfies_its_specification:
  forall (A : Type)
         (compare : A -> A -> element_comparison)
         (x : A),
    specifiction_of_delete_hbt A compare x delete_hbt.
Proof.
  intros.
  unfold specifiction_of_delete_hbt.
  intros.
  unfold delete_hbt.
  case (delete_hbt_helper A compare x hbt) as [hbt' | ] eqn: C_del.

  Focus 2.
  split.
  exact H.
  split.

  exact H0.
  exact H1.

  destruct (deletion_preserves_soundness_and_balance A compare x) as [H_s_b _].
  destruct (H_s_b hbt hbt' H H0 C_del) as [H_sound H_bal].
  
  destruct (deletion_preserves_order A compare x) as [H_o _].         
  assert (H_ord : is_ordered_hbt A hbt' compare = true).
  exact (H_o hbt hbt' H H0 H1 C_del).
  split.

  exact H_sound.
  split.

  exact H_bal.
  exact H_ord.
Qed.


(* ***** Section 3: Specification and associated theorems for lookup ***** *)

(* (* The specification *) *)
(* Definition specification_of_occurs_hbt *)
(*            (A : Type) *)
(*            (compare : A -> A -> element_comparison) *)
(*            (occ_hbt : forall (A' : Type), *)
(*                (A' -> A' -> element_comparison) *)
(*                -> A' *)
(*                -> heightened_binary_tree A' *)
(*                -> bool) := *)
(*   forall (e : A) *)
(*          (h : nat)  *)
(*          (bt : binary_tree A), *)
(*   exists (occ_bt : forall (A' : Type), *)
(*              (A' -> A' -> element_comparison) -> A' -> binary_tree A' -> bool), *)
(*     occ_hbt A compare e (HNode A h bt) = occ_bt A compare e bt. *)

(* Definition specification_of_occurs_bt  *)
(*            (A : Type) *)
(*            (compare : A -> A -> element_comparison) *)
(*            (occ_bt : forall (A' : Type), *)
(*                (A' -> A' -> element_comparison) *)
(*                -> A' *)
(*                -> binary_tree A' *)
(*                -> bool) := *)
(*   (forall (e : A), *)
(*       occ_bt A compare e (Leaf A) = false) *)
(*   /\ *)
(*   (forall (e : A) *)
(*           (t : triple A), *)
(*       exists (occ_t : forall (A' : Type), *)
(*                  (A' -> A' -> element_comparison) -> A' -> triple A' -> bool), *)
(*         occ_bt A compare e (Node A t) = occ_t A compare e t). *)

(* Definition specification_of_occurs_t *)
(*            (A : Type) *)
(*            (compare : A -> A -> element_comparison) *)
(*            (occ_t : forall (A' : Type), *)
(*                (A' -> A' -> element_comparison) *)
(*                -> A' *)
(*                -> triple A' *)
(*                -> bool) := *)
(*   forall (e e' : A) *)
(*          (hbt1 hbt2 : heightened_binary_tree A), *)
(*     exists (occ_hbt : forall (A' : Type), *)
(*                (A' -> A' -> element_comparison) *)
(*                -> A' *)
(*                -> heightened_binary_tree A' *)
(*                -> bool), *)
(*       occ_t A compare e (Triple A hbt1 e' hbt2) = *)
(*       match compare e e' with *)
(*       | Lt => *)
(*         occ_hbt A compare e hbt1 *)
(*       | Eq => *)
(*         true *)
(*       | Gt => *)
(*         occ_hbt A compare e hbt2 *)
(*       end. *)
                
(* (* Theorem for the soundness of the specification *) *)
(* Theorem there_is_only_one_occurs: *)
(*   forall (A : Type) *)
(*          (compare : A -> A -> element_comparison),  *)
(*     (forall (hbt : heightened_binary_tree A) *)
(*             (e : A) *)
(*             (occ_hbt1 occ_hbt2 : forall (A' : Type), *)
(*                 (A' -> A' -> element_comparison) *)
(*                 -> A' *)
(*                 -> heightened_binary_tree A' *)
(*                 -> bool), *)
(*         specification_of_occurs_hbt A compare occ_hbt1 -> *)
(*         specification_of_occurs_hbt A compare occ_hbt2 -> *)
(*         occ_hbt1 A compare e hbt = occ_hbt2 A compare e hbt) *)
(*     /\ *)
(*     (forall (bt : binary_tree A) *)
(*             (e : A) *)
(*             (occ_bt1 occ_bt2 : forall (A' : Type), *)
(*                 (A' -> A' -> element_comparison) *)
(*                 -> A' *)
(*                 -> binary_tree A' *)
(*                 -> bool), *)
(*         specification_of_occurs_bt A compare occ_bt1 -> *)
(*         specification_of_occurs_bt A compare occ_bt2 -> *)
(*         occ_bt1 A compare e bt = occ_bt2 A compare e bt) *)
(*     /\ *)
(*     (forall (t : triple A) *)
(*             (e : A) *)
(*             (occ_t1 occ_t2 : forall (A' : Type), *)
(*                 (A' -> A' -> element_comparison) *)
(*                 -> A' *)
(*                 -> triple A' *)
(*                 -> bool), *)
(*         specification_of_occurs_t A compare occ_t1 -> *)
(*         specification_of_occurs_t A compare occ_t2 -> *)
(*         occ_t1 A compare e t = occ_t2 A compare e t). *)
(* Proof.  *)
(*   intros A compare. *)
(*   apply heightened_binary_tree_mutual_induction. *)
(*   - intros h bt bt_ind_hyp. *)
(*     intros e occ_hbt1 occ_hbt2 spec_hbt1 spec_hbt2. *)
(*     unfold specification_of_occurs_hbt in spec_hbt1. *)
(*     unfold specification_of_occurs_hbt in spec_hbt2. *)
(*     destruct (spec_hbt1 e h bt) as [occ_bt_hyp1 hyp1]. *)
(*     destruct (spec_hbt2 e h bt) as [occ_bt_hyp2 hyp2]. *)
(*     rewrite -> hyp1. *)
(*     rewrite -> hyp2. *)
(*     apply (bt_ind_hyp e occ_bt_hyp1 occ_bt_hyp2). *)
(* Abort.  *)
  
    

(* (* Theorem to show that occurs_hbt, occurs_bt, and occurs_t meet their respective  *)
(*  * specifications *)  *)
(* Theorem occurs_implementation_satisfies_its_specification: *)
(*   forall (A : Type) *)
(*          (compare : A -> A -> element_comparison), *)
(*   (specification_of_occurs_hbt A compare occurs_hbt) *)
(*   /\ *)
(*   (specification_of_occurs_bt A compare occurs_bt) *)
(*   /\ *)
(*   (specification_of_occurs_t A compare occurs_t). *)
(* Proof.     *)
(*   intros A compare. *)
(*   split.  *)

(*   - unfold specification_of_occurs_hbt. *)
(*     intros e h bt. *)
(*     exists occurs_bt. *)
(*     reflexivity. *)

(*   - split. *)
(*     unfold specification_of_occurs_bt. *)
(*     split. *)
(*     intro e. *)
(*     rewrite -> (unfold_occurs_bt_leaf A compare e). *)
(*     reflexivity. *)
(*     intros e t. *)
(*     exists occurs_t. *)
(*     Check (unfold_occurs_bt_node). *)
(*     rewrite -> (unfold_occurs_bt_node A compare e t). *)
(*     reflexivity. *)

(*     unfold specification_of_occurs_t. *)
(*     intros e e' hbt1 hbt2. *)
(*     exists occurs_hbt. *)
(*     Check (unfold_occurs_t). *)
(*     rewrite -> (unfold_occurs_t A compare e e' hbt1 hbt2). *)
(*     reflexivity. *)
(* Qed. *)

(* (* Finish the heightened_binary_tree_alternative proofs later *) *)

