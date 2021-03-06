(* ********** ordered_helper.v ********** *)

(** The [ordered_helper] library contains all the lemmas that serve as 'helper'
lemmas to prove the main lemmas for orderedness in [ordered_main]. Please see how
the predicate to check orderedness is defined in the [hbt] library to understand the
motivation for the lemmas in this libray. *)

Require Import Hbt.Lemmas.Balanced.balanced.
Require Export Hbt.Lemmas.Balanced.balanced.

(* ********** *)

(** * General Lemmas Concerning Orderedness *)

(** Lemma to show that an ordered [triple] must have ordered subtrees *)
Lemma triple_ordered_implies_hbts_ordered:
  forall (A : Type)
         (compare : A -> A -> element_comparison)
         (h_hbt : nat)
         (hbt1 : heightened_binary_tree A)
         (e : A)
         (hbt2 : heightened_binary_tree A),
    is_ordered_hbt A (HNode A h_hbt (Node A (Triple A hbt1 e hbt2))) compare = true ->
    is_ordered_hbt A hbt1 compare = true /\ is_ordered_hbt A hbt2 compare = true.
Proof.
  intros.

  unfold is_ordered_hbt in H.
  rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H.
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_node in H.
  rewrite -> fold_unfold_traverse_to_check_ordered_t in H.
  split.
  
  unfold is_ordered_hbt.
  case (traverse_to_check_ordered_hbt A hbt1 compare)
    as [ | | (min1, max1)] eqn : C_traverse_ord_hbt1.
  discriminate.
  case (traverse_to_check_ordered_hbt A hbt2 compare )
       as [ | | (min2, max2)].
  discriminate.
  reflexivity.
  case (compare e min2) as [ | | ].
  reflexivity.
  discriminate.
  discriminate.
  reflexivity.
  
  case (traverse_to_check_ordered_hbt A hbt1 compare)
    as [ | | (min1, max1)].
  discriminate.
  case (traverse_to_check_ordered_hbt A hbt2 compare )
    as [ | | (min2, max2)] eqn : C_traverse_ord_hbt2.
  discriminate.
  unfold is_ordered_hbt.
  rewrite -> C_traverse_ord_hbt2.
  reflexivity.
  case (compare e min2) as [ | | ].
  unfold is_ordered_hbt.
  rewrite -> C_traverse_ord_hbt2.
  reflexivity.
  discriminate.
  discriminate. 
  case (compare max1 e) as [ | | ].
  case (traverse_to_check_ordered_hbt A hbt2 compare )
    as [ | | (min2, max2)] eqn : C_traverse_ord_hbt2.
  discriminate.
  unfold is_ordered_hbt.
  rewrite -> C_traverse_ord_hbt2.
  reflexivity.
  case (compare e min2) as [ | | ].
  unfold is_ordered_hbt.
  rewrite -> C_traverse_ord_hbt2.
  reflexivity.
  discriminate.
  discriminate. 
  discriminate.
  discriminate. 
Qed.

(** Lemma to show that traversing a [binary_tree] constructed with a [Node] 
constructor to check orderedness can never yield a [TNone] value *)
Lemma traverse_node_impossible_case:
  forall (A : Type)
         (compare : A -> A -> element_comparison)
         (t1 : triple A),
    traverse_to_check_ordered_bt A (Node A t1) compare = TNone (A * A) -> False. 
Proof.
  intros A compare t1 H.
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_node in H.
  induction t1 as [hbt11 e1 hbt12].
  rewrite -> fold_unfold_traverse_to_check_ordered_t in H.
  case (traverse_to_check_ordered_hbt A hbt11 compare) as [ | | (min11, max11)].
  case (traverse_to_check_ordered_hbt A hbt12 compare) as [ | | (min12, max12)].
  discriminate.
  discriminate.
  discriminate.
  case (traverse_to_check_ordered_hbt A hbt12 compare) as [ | | (min12, max12)].
  discriminate.
  discriminate.
  case (compare e1 min12) as [ | | ].
  discriminate.
  discriminate.
  discriminate.
  case (traverse_to_check_ordered_hbt A hbt12 compare) as [ | | (min12, max12)].
  case (compare max11 e1) as [ | | ].
  discriminate.
  discriminate.
  discriminate.
  case (compare max11 e1) as [ | | ].
  discriminate.
  discriminate.
  discriminate.
  case (compare max11 e1) as [ | | ].
  case (compare e1 min12) as [ | | ].
  discriminate.
  discriminate.
  discriminate.
  discriminate.
  discriminate.
Qed.

(** Lemma to show that if traversing a [heightened_binary_tree] to check orderedness
yields a [TNone] value, then the tree is a leaf *)
Lemma tnone_implies_leaf:
  forall (A : Type)
         (h : nat)
         (bt : binary_tree A)
         (compare : A -> A -> element_comparison),
    traverse_to_check_ordered_hbt A (HNode A h bt) compare =
    TNone (A * A) ->
    bt = Leaf A.
Proof.
  intros.
  rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H.
  induction bt as [ | t].
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_leaf in H.
  reflexivity.

  apply False_ind.
  exact (traverse_node_impossible_case A compare t H).
Qed.

(** Lemma to show that if a [heightened_binary_tree] is ordered, then it is either:
  - a leaf, in which case [traverse_to_check_ordered_hbt] returns a [TNone] value
  - or a node, in which case [traverse_to_check_ordered_hbt] returns a [TSome] value
 *)
Lemma is_ordered_true_implies_leaf_or_ordered_node:
  forall (A : Type)
         (compare : A -> A -> element_comparison)
         (hbt : heightened_binary_tree A),
    is_ordered_hbt A hbt compare = true ->
    (traverse_to_check_ordered_hbt A hbt compare =
     TNone (A * A)
     \/
     exists (min max : A), 
       traverse_to_check_ordered_hbt A hbt compare =
       TSome (A * A) (min, max)).
Proof.  
  intros. 
  unfold is_ordered_hbt in H.
  induction hbt as [h bt].
  case bt as [ | t] eqn : C_bt.
  rewrite -> fold_unfold_traverse_to_check_ordered_hbt.
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_leaf.
  apply or_introl.
  reflexivity.
  rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H.
  case (traverse_to_check_ordered_bt A (Node A t) compare)
    as [ | |(min, max)] eqn : C_traverse_bt. 
  discriminate.
  
  assert (H_false : False).
  exact (traverse_node_impossible_case A compare t C_traverse_bt).
  apply False_ind.
  exact H_false.

  apply or_intror.
  exists min.
  exists max.
  exact C_traverse_bt.
Qed.

(** Lemma to show that a tree with a triple (i.e., a tree that is not a leaf) is
ordered, i.e., traversing the tree to check for orderedness returns a [TSome] value
with minimum and maximum payloads *)
Lemma single_node_tree_is_ordered: 
  forall (A : Type)
         (compare : A -> A -> element_comparison)
         (h1 : nat)
         (bt1 : binary_tree A)
         (e : A)
         (h2 : nat)
         (bt2 : binary_tree A),
    is_ordered_hbt A (HNode A h1 bt1) compare = true -> 
    (forall min1 max1 : A,
        traverse_to_check_ordered_hbt A (HNode A h1 bt1) compare =
        TSome (A * A) (min1, max1) -> compare max1 e = Lt) ->
    is_ordered_hbt A (HNode A h2 bt2) compare = true -> 
    (forall min2 max2 : A,
        traverse_to_check_ordered_hbt A (HNode A h2 bt2) compare =
        TSome (A * A) (min2, max2) -> compare e min2 = Lt) ->
    exists min1 max2, 
      traverse_to_check_ordered_hbt
        A
        (HNode A (1 + max h1 h2)
               (Node A
                     (Triple A
                             (HNode A h1 bt1)
                             e
                             (HNode A h2 bt2))))
        compare = TSome (A * A) (min1, max2).
Proof.  
  intros.

  (* assert that hbt1 and hbt2 are either leaves or nodes *)
  Check (is_ordered_true_implies_leaf_or_ordered_node).
  assert (H_hbt1_leaf_or_node:
            traverse_to_check_ordered_hbt A (HNode A h1 bt1) compare =
            TNone (A * A)
            \/
            (exists min max : A,
                traverse_to_check_ordered_hbt A (HNode A h1 bt1) compare =
                TSome (A * A) (min, max))).
  exact (is_ordered_true_implies_leaf_or_ordered_node
           A compare (HNode A h1 bt1) H).
  
  assert (H_hbt2_leaf_or_node:
            traverse_to_check_ordered_hbt A (HNode A h2 bt2) compare =
            TNone (A * A)
            \/
            (exists min max : A,
                traverse_to_check_ordered_hbt A (HNode A h2 bt2) compare =
                TSome (A * A) (min, max))).
  exact (is_ordered_true_implies_leaf_or_ordered_node
           A compare (HNode A h2 bt2) H1).

  (* unfold the goal before destructing to avoid repeated unfolds *)
  rewrite -> fold_unfold_traverse_to_check_ordered_hbt.
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_node.
  rewrite -> fold_unfold_traverse_to_check_ordered_t.
  
  destruct H_hbt1_leaf_or_node as [H_hbt1_leaf | H_hbt1_node].

  (* hbt1 is a leaf *)
  - destruct H_hbt2_leaf_or_node as [H_hbt2_leaf | H_hbt2_node].

    (* hbt2 is a leaf *)
    {
      rewrite -> H_hbt1_leaf.
      rewrite -> H_hbt2_leaf.
      exists e.
      exists e.
      reflexivity.
    }

    (* hbt2 is a node *)
    {
      rewrite -> H_hbt1_leaf.
      destruct H_hbt2_node as [min2 [max2 H_hbt2_node]].
      rewrite -> H_hbt2_node.
      rewrite -> (H2 min2 max2 H_hbt2_node).
      exists e.
      exists max2.
      reflexivity.
    }

    (* hbt1 is a node *)
  - destruct H_hbt2_leaf_or_node as [H_hbt2_leaf | H_hbt2_node].

    (* hbt2 is a leaf *)
    {
      destruct H_hbt1_node as [min1 [max1 H_hbt1_node]].
      rewrite -> H_hbt1_node.
      rewrite -> H_hbt2_leaf.
      rewrite -> (H0 min1 max1 H_hbt1_node).
      exists min1.
      exists e.
      reflexivity.
    }

    (* hbt2 is a node *)
    {
      destruct H_hbt1_node as [min1 [max1 H_hbt1_node]].
      destruct H_hbt2_node as [min2 [max2 H_hbt2_node]].
      rewrite -> H_hbt1_node.
      rewrite -> (H0 min1 max1 H_hbt1_node).
      rewrite -> H_hbt2_node.
      rewrite -> (H2 min2 max2 H_hbt2_node).
      exists min1.
      exists max2.
      reflexivity.
    }
Qed.

(** Lemma to show that a sound tree with non-zero height must be a node *)
Lemma non_zero_height_implies_node:
  forall (A : Type)
         (h_ret h1 h2 : nat)
         (bt1 : binary_tree A),
    (h_ret = h1) \/ (h_ret = 1 + h1) -> 
    (h_ret =n= 2 + h2) = true ->
    is_sound_hbt A (HNode A h1 bt1) = true ->
    exists (t1 : triple A),
      bt1 = Node A t1.
Proof.
  intros.
  apply beq_nat_true in H0.
  destruct H as [H_ret_eq_h1 | H_ret_eq_S_h1].

  - rewrite -> H_ret_eq_h1 in H0.
    rewrite H0 in H1.
    case bt1 as [ | t1].
    unfold is_sound_hbt in H1.
    rewrite -> fold_unfold_traverse_to_check_soundness_hbt in H1.
    rewrite -> fold_unfold_traverse_to_check_soundness_bt_leaf in H1.
    case h2 as [ | h2'].
    rewrite -> plus_0_r in H1.
    unfold beq_nat in H1.
    discriminate.
    rewrite -> plus_Sn_m in H1.
    unfold beq_nat in H1.
    discriminate.
    exists t1.
    reflexivity.

  - rewrite H_ret_eq_S_h1 in H0.
    Check (succ_eq).
    apply succ_eq in H0.
    rewrite H0 in H1.
    case bt1 as [ | t1].    
    unfold is_sound_hbt in H1.
    rewrite -> fold_unfold_traverse_to_check_soundness_hbt in H1.
    rewrite -> fold_unfold_traverse_to_check_soundness_bt_leaf in H1.
    case h2 as [ | h2'].
    unfold beq_nat in H1.
    discriminate.
    unfold beq_nat in H1.
    discriminate.
    exists t1.
    reflexivity.
Qed.    

(** Lemma to show that if traversing a [heightened_binary_tree] to check its
orderedness yields a [TSome] value containg the minimum and maximum payload
values, then reducing the left subtree to a leaf also yields an ordered 
[heightened_binary_tree] such that: 
- the maximum value is the same as the maximum value of the original tree
- the minimum value is the payload at the root of the tree concerned *)
Lemma reduce_ordered_hbt_left:
  forall (A : Type)
         (compare : A -> A -> element_comparison)
         (h : nat)
         (hbt1 : heightened_binary_tree A)
         (e : A)
         (hbt2 : heightened_binary_tree A)
         (min max : A),
    traverse_to_check_ordered_hbt
      A (HNode A h (Node A (Triple A hbt1 e hbt2))) compare = TSome (A * A) (min, max) ->
    traverse_to_check_ordered_hbt
      A (HNode A h (Node A (Triple A
                                   (HNode A 0 (Leaf A))
                                   e
                                   hbt2))) compare = TSome (A * A) (e, max).
Proof.    
  intros.
  rewrite -> fold_unfold_traverse_to_check_ordered_hbt.
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_node.
  rewrite -> fold_unfold_traverse_to_check_ordered_t.   
  rewrite -> fold_unfold_traverse_to_check_ordered_hbt.
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_leaf.
  rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H. 
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_node in H.
  rewrite -> fold_unfold_traverse_to_check_ordered_t in H.
  case (traverse_to_check_ordered_hbt A hbt1 compare) as [ | | (min1, max1)].
  discriminate.
  case (traverse_to_check_ordered_hbt A hbt2 compare) as [ | | (min2, max2)].
  discriminate.
  rewrite -> tsome_x_equal_tsome_y in H.
  rewrite -> pairwise_equality in H.
  destruct H as [_ H'].
  rewrite <- H'.
  reflexivity.
  case (compare e min2) as [ | | ].
  rewrite -> tsome_x_equal_tsome_y in H.
  rewrite -> pairwise_equality in H.
  destruct H as [_ H'].
  rewrite <- H'.
  reflexivity.
  discriminate.
  discriminate.
  case (compare max1 e) as [ | | ].
  case (traverse_to_check_ordered_hbt A hbt2 compare) as [ | | (min2, max2)]. 
  discriminate.
  rewrite -> tsome_x_equal_tsome_y in H.
  rewrite -> pairwise_equality in H.
  destruct H as [_ H'].
  rewrite <- H'.
  reflexivity.
  case (compare e min2) as [ | | ].
  rewrite -> tsome_x_equal_tsome_y in H.
  rewrite -> pairwise_equality in H.
  destruct H as [_ H'].
  rewrite <- H'.
  reflexivity.
  discriminate.
  discriminate.
  discriminate.
  discriminate.
Qed.

(** Lemma to show that if traversing a [heightened_binary_tree] to check its
orderedness yields a [TSome] value containg the minimum and maximum payload
values, then reducing the right subtree to a leaf also yields an ordered 
[heightened_binary_tree] such that: 
- the minimum value is the same as the minimum value of the original tree
- the maximum value is the payload at the root of the tree concerned *)
Lemma reduce_ordered_hbt_right:
  forall (A : Type)
         (compare : A -> A -> element_comparison)
         (h : nat)
         (hbt1 : heightened_binary_tree A)
         (e : A)
         (hbt2 : heightened_binary_tree A)
         (min max : A),
    traverse_to_check_ordered_hbt
      A (HNode A h (Node A (Triple A hbt1 e hbt2))) compare = TSome (A * A) (min, max) ->
    traverse_to_check_ordered_hbt
      A (HNode A h (Node A (Triple A
                                   hbt1
                                   e
                                   (HNode A 0 (Leaf A))))) compare = TSome (A * A) (min, e).
Proof.
  intros. 
  rewrite -> fold_unfold_traverse_to_check_ordered_hbt.
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_node.
  rewrite -> fold_unfold_traverse_to_check_ordered_t.   
  rewrite -> fold_unfold_traverse_to_check_ordered_hbt.
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_leaf.
  rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H. 
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_node in H.
  rewrite -> fold_unfold_traverse_to_check_ordered_t in H.
  case (traverse_to_check_ordered_hbt A hbt1 compare) as [ | | (min1, max1)].
  discriminate.
  case (traverse_to_check_ordered_hbt A hbt2 compare) as [ | | (min2, max2)].
  discriminate.
  rewrite -> tsome_x_equal_tsome_y in H.
  rewrite -> pairwise_equality in H.
  destruct H as [H' _].
  rewrite <- H'.
  reflexivity.
  case (compare e min2) as [ | | ].
  rewrite -> tsome_x_equal_tsome_y in H.
  rewrite -> pairwise_equality in H.
  destruct H as [H' _].
  rewrite <- H'.
  reflexivity.  
  discriminate.
  discriminate.
  case (compare max1 e) as [ | | ].
  case (traverse_to_check_ordered_hbt A hbt2 compare) as [ | | (min2, max2)].
  discriminate.
  rewrite -> tsome_x_equal_tsome_y in H.
  rewrite -> pairwise_equality in H.
  destruct H as [H' _].
  rewrite <- H'.
  reflexivity.
  case (compare e min2) as [ | | ].
  rewrite -> tsome_x_equal_tsome_y in H.
  rewrite -> pairwise_equality in H.
  destruct H as [H' _].
  rewrite <- H'.
  reflexivity.  
  discriminate.
  discriminate.
  discriminate.
  discriminate.
Qed.

(** Lemma to show that if traversing a [heightened_binary_tree] to check its
 orderedness yields a maximum and a minimum value, then it must be ordered *)
Lemma traverse_to_check_ordered_hbt_some_implies_is_ordered:
  forall (A : Type)
         (compare : A -> A -> element_comparison)
         (hbt : heightened_binary_tree A)
         (min max : A),
    traverse_to_check_ordered_hbt A hbt compare = TSome (A * A) (min, max) ->
    is_ordered_hbt A hbt compare = true. 
Proof. 
  intros.
  induction hbt as [h bt].
  rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H.
  induction bt as [ | t].
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_leaf in H.
  discriminate.
  induction t as [hbt1 e hbt2].
  unfold is_ordered_hbt.
  rewrite -> fold_unfold_traverse_to_check_ordered_hbt.
  rewrite -> H.
  reflexivity.
Qed.

(** This lemma is not concerned with orderedness but is required to prove orderedness
lemmas in the <<rotate_right_2>> and <<rotate_left_2>> cases *) 
Lemma non_zero_height:
  forall (A : Type)
         (h1 h2 h h' : nat)
         (bt' : binary_tree A),
    h2 = h1 ->
    1 + max h1 h2 = h ->
    compare_int h (2 + project_height_hbt A (HNode A h' bt')) = Eq -> 
    exists x, h2 = S x.
Proof.
  intros.
  rewrite <- H in H0.
  rewrite -> Nat.max_idempotent in H0.
  rewrite <- H0 in H1.
  unfold project_height_hbt in H1.

  unfold compare_int in H1.
  case (1 + h2 <? 2 + h') as [ | ]. 
  discriminate.
  case (1 + h2 =n= 2 + h') as [ | ] eqn : C_S_h2_SS_h'.

  apply beq_nat_true in C_S_h2_SS_h'.
  apply succ_eq in C_S_h2_SS_h'.

  exists h'.
  exact C_S_h2_SS_h'.

  discriminate.
Qed.


(* ********** *)

(* ********** *)

(** * Orderedness Lemmas Concerning Insertion *)

(** This section contains the orderedness lemmas directly related to the insertion
operation. It is divided into 3 subsections, all 3 of which are concerned with 
the maximum and minimum elements in an AVL tree after insertion. These lemmas are
required since the predicate to check orderedness relies on finding the maximum and
minimum payloads for sub-trees and comparing them to payloads. *)

(* ***** *)

(** ** Impossible Insertion Case *)

(** Lemma to show that a tree cannot be a leaf if an element is inserted into it *)
Lemma insertion_impossible_case:
  forall (A : Type)
         (compare : A -> A -> element_comparison)
         (x : A) 
         (hbt : heightened_binary_tree A)
         (hbt' : heightened_binary_tree A),
    insert_hbt_helper A compare x hbt = Some hbt' ->
    traverse_to_check_ordered_hbt A hbt' compare <> TNone (A * A).
Proof.                                                                    
    intros A compare x  hbt hbt' H_ins.
    unfold not.
    induction hbt' as [h' bt'].
    rewrite -> (fold_unfold_traverse_to_check_ordered_hbt A h' bt' compare).
    case bt' as [ | t'].

    (* bt' is a leaf *)
    - induction hbt as [h bt].
      rewrite -> (fold_unfold_insert_hbt_helper A compare x h bt) in H_ins.
      case bt as [ | t].

      (* bt is a leaf *)
      + rewrite -> (fold_unfold_insert_bt_helper_leaf A compare) in H_ins.
        discriminate.

      (* bt is a node: unfold the isnert function in H_ins *)
      + induction t as [ hbt1 e hbt2].
        rewrite -> (fold_unfold_insert_bt_helper_node A compare x h (Triple A hbt1 e hbt2))
          in H_ins.
        rewrite -> (fold_unfold_insert_t_helper A compare x h hbt1 e hbt2) in H_ins.
        case (compare x e) as [ | | ] eqn : C_comp_x_e.
        
        * case (insert_hbt_helper A compare x hbt1)
            as [hbt1_ret | ] eqn : C_ins_hbt1.
          induction hbt1_ret as [h1_ret bt_01_ret]. 
          case (compare_int h1_ret (2 + project_height_hbt A hbt2)) as [ | | ].
          rewrite -> some_x_equal_some_y in H_ins.
          discriminate.
          unfold rotate_right_hbt in H_ins.
          induction hbt2 as [h2 bt2]. 
          unfold rotate_right_bt in H_ins.
          case (bt_01_ret) as [ t1 | ].
          discriminate.
          induction t as [ hbt11 e1 hbt12].
          induction hbt11 as [h11 bt11].
          induction hbt12 as [h12 bt12].
          case (h11 + 1 =n= h12) as [ | ].
          case bt12 as [ | t12].
          discriminate.
          induction t12 as [ hbt121 e12 hbt122 ].
          induction hbt121 as [ h121 bt121 ].
          induction hbt122 as [ h122 bt122 ].
          rewrite -> some_x_equal_some_y in H_ins.
          discriminate.
          case ((h12 + 1 =n= h11) || (h12 =n= h11)) as [ | ].
          rewrite -> some_x_equal_some_y in H_ins.
          discriminate.
          discriminate.
          discriminate.
          discriminate.

        * discriminate.

        * case (insert_hbt_helper A compare x hbt2) as [hbt2_ret | ].
          induction hbt2_ret as [h2_ret bt2_ret].
          case (compare_int h2_ret (2 + project_height_hbt A hbt1)) as [ | | ].
          rewrite -> some_x_equal_some_y in H_ins.
          discriminate.
          unfold rotate_left_hbt in H_ins.
          induction hbt1 as [h1 bt1].
          unfold rotate_left_bt in H_ins.
          case bt2_ret as [ | t2].
          discriminate.
          induction t2 as [hbt21 e2 hbt22].
          induction hbt21 as [h21 bt21].
          induction hbt22 as [h22 bt22].
          case (h22 + 1 =n= h21) as [ | ].
          case bt21 as [ | t21 ].
          discriminate.
          induction t21 as [hbt211 e21 hbt212].
          induction hbt211 as [h211 bt211].
          induction hbt212 as [h212 bt212].
          rewrite -> some_x_equal_some_y in H_ins.
          discriminate.
          case ((h21 + 1 =n= h22) || (h21 =n= h22)) as [ | ].
          rewrite -> some_x_equal_some_y in H_ins.
          discriminate.
          discriminate.
          discriminate.
          discriminate.

    (* bt' is a node *)
    - intro H_check_ord.
      rewrite -> (fold_unfold_traverse_to_check_ordered_bt_node A t' compare)
        in H_check_ord.
      induction t' as [hbt1'' e hbt2''].
      rewrite -> (fold_unfold_traverse_to_check_ordered_t A hbt1'' e hbt2'' compare)
        in H_check_ord.
      case (traverse_to_check_ordered_hbt A hbt1'' compare) as [ | | (min1, max1)].
      discriminate.
      case (traverse_to_check_ordered_hbt A hbt2'' compare) as [ | | (min2, max2)].
      discriminate.
      discriminate.
      case (compare e min2) as [ | | ].
      discriminate.
      discriminate.
      discriminate.
      case (compare max1 e) as [ | | ].
      case (traverse_to_check_ordered_hbt A hbt2'' compare) as [ | | (min2, max2)].
      discriminate.
      discriminate.
      case (compare e min2) as [ | | ].
      discriminate.
      discriminate.
      discriminate.
      discriminate.
      discriminate.
Qed.

(** Lemma to show that given the (false) hypothesis that a tree modified by the
insertion operation is a leaf, any proposition will be true *)
Lemma insertion_impossible_case_implies_true:
  forall (A : Type)
         (hbt hbt' : heightened_binary_tree A)
         (compare : A -> A -> element_comparison)
         (x : A)
         (P : Prop),
    insert_hbt_helper A compare x hbt = Some hbt' ->
    traverse_to_check_ordered_hbt A hbt' compare = TNone (A * A) ->
    P.
Proof.
  intros A hbt hbt' compare x P H_insertion H_traverse.
  induction hbt' as [h' bt'].
  assert (H_impossible_case : 
            traverse_to_check_ordered_hbt A (HNode A h' bt')  compare <>
            TNone (A * A)).
    exact (insertion_impossible_case
             A
             compare x hbt (HNode A h' bt')
             H_insertion).
    unfold not in H_impossible_case.
    assert (H_false : False).
    exact (H_impossible_case H_traverse).
    exact (False_ind P H_false).
Qed.

(* ***** *)

(* ***** *)

(** ** General Lemmas Concerning the Minimum and Maximum Payloads in an AVL Tree *)

(** Lemma to show that an element inserted into a leaf will be both its minimum and
its maximum element *)
Lemma insertion_in_leaf_min_max:
  forall (A : Type)
         (compare : A -> A -> element_comparison)
         (hbt : heightened_binary_tree A)
         (hbt' : heightened_binary_tree A)
         (x min' max' : A),
    insert_hbt_helper A compare x hbt = Some hbt' ->
    traverse_to_check_ordered_hbt A hbt' compare = TSome (A * A) (min', max') ->
    traverse_to_check_ordered_hbt A hbt compare = TNone (A * A) ->
    min' = x /\ max' = x.
Proof.
  intros A compare hbt hbt' x min' max' H_insert H_hbt' H_hbt.

  induction hbt as [h bt].
  
  assert (H_form_of_bt: bt = (Leaf A)).
  rewrite -> (fold_unfold_traverse_to_check_ordered_hbt A h bt compare) in H_hbt.
  case bt as [ | t] eqn : C_bt.
  reflexivity.
  rewrite -> (fold_unfold_traverse_to_check_ordered_bt_node A t compare) in H_hbt.
  case t as [hbt1 e hbt2].
  rewrite -> (fold_unfold_traverse_to_check_ordered_t A hbt1 e hbt2 compare) in H_hbt. 
  case (traverse_to_check_ordered_hbt A hbt1 compare)
    as [ | | (min1, max1)] eqn : C_ord_hbt1.
  discriminate.
  case (traverse_to_check_ordered_hbt A hbt2 compare)
    as [ | | (min2, max2)] eqn : C_ord_hbt2.
  discriminate.
  discriminate.
  case (compare e min2) as [ | | ] eqn : C_comp_e_min2.
  discriminate.
  discriminate.
  discriminate.
  case (compare max1 e) as [ | | ] eqn : C_comp_e_min1.
  case (traverse_to_check_ordered_hbt A hbt2 compare)
    as [ | | (min2, max2)] eqn : C_ord_hbt2.
  discriminate.
  discriminate.
  case (compare e min2) as [ | | ] eqn : C_comp_e_min2.
  discriminate.
  discriminate.
  discriminate.
  discriminate.
  discriminate.

  rewrite -> H_form_of_bt in H_insert.
  rewrite -> (fold_unfold_insert_hbt_helper A compare x h (Leaf A)) in H_insert.
  rewrite -> (fold_unfold_insert_bt_helper_leaf A compare x h) in H_insert.
  rewrite ->  some_x_equal_some_y in H_insert.
  rewrite <- H_insert in H_hbt'.
  rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H_hbt'.
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_node in H_hbt'.
  rewrite -> fold_unfold_traverse_to_check_ordered_t in H_hbt'.
  rewrite -> (fold_unfold_traverse_to_check_ordered_hbt A 0 (Leaf A) compare) in H_hbt'.
  rewrite -> (fold_unfold_traverse_to_check_ordered_bt_leaf A compare) in H_hbt'.
  rewrite -> (tsome_x_equal_tsome_y (A * A) (x, x) (min', max')) in H_hbt'.
  apply (pairwise_equality A x x min' max') in H_hbt'.
  destruct H_hbt' as [G1 G2].
  split.

  rewrite -> G1.
  reflexivity.
  
  rewrite -> G2.
  reflexivity.
Qed.

(** Lemma to show that a tree that is not a leaf and is ordered has a maximum and a 
 * minimum element *)
Lemma ordered_node_has_min_max:
  forall (A : Type)
         (compare : A -> A -> element_comparison)
         (h1 : nat)
         (hbt11 : heightened_binary_tree A)
         (e1 : A)
         (hbt12 : heightened_binary_tree A),
    is_ordered_hbt A (HNode A h1 (Node A (Triple A hbt11 e1 hbt12))) compare = true ->
    exists (some_min some_max : A), 
      traverse_to_check_ordered_bt A (Node A (Triple A hbt11 e1 hbt12)) compare = 
      TSome (A * A) (some_min, some_max).
Proof.
  intros.
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_node.
  rewrite -> fold_unfold_traverse_to_check_ordered_t.
  
  unfold is_ordered_hbt in H.
  rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H.
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_node in H.
  rewrite -> fold_unfold_traverse_to_check_ordered_t in H.
  
  case (traverse_to_check_ordered_hbt A hbt11 compare) as
      [ | | (min11, max11)] eqn : C_traverse_ord_hbt11.

  (* hbt11 unordered *)
  - discriminate.

  (* hbt11 is leaf *)
  - case (traverse_to_check_ordered_hbt A hbt12 compare) as
        [ | | (min12, max12)] eqn : C_traverse_ord_hbt12.

    (* hbt12 unordered *)
    + discriminate.

    (* hbt12 is leaf *)
    + exists e1.
      exists e1.
      reflexivity.

    (* hbt12 is node *)
    + case (compare e1 min12) as [ | | ].
      exists e1.
      exists max12.
      reflexivity.

      discriminate.

      discriminate.

  (* hbt11 is node *)
  - case (traverse_to_check_ordered_hbt A hbt12 compare) as
        [ | | (min12, max12)] eqn : C_traverse_ord_hbt12.

    (* hbt12 is unorderd *)
    + case (compare max11 e1) as [ | | ].
      discriminate.

      discriminate.

      discriminate.

    (* hbt12 is leaf *)
    + case (compare max11 e1) as [ | | ].

      exists min11.
      exists e1.
      reflexivity.

      discriminate.

      discriminate.

    (* hbt12 is a node *)
    + case (compare max11 e1) as [ | | ].
      case (compare e1 min12) as [ | | ].

      exists min11.
      exists max12.
      reflexivity.

      discriminate.

      discriminate.

      discriminate.

      discriminate.
Qed.      

(* ***** *)

(* ***** *)

(** ** Right Rotation Lemmas *)

(** Lemma to show that the maximum element of a right rotated tree is the same as the 
maximum element of the left reduced form of the original sub-tree into which the
insertion was performed. Note that because the lemma can be used in both the 
<<rotate_right_1>> and the <<rotate_right_2>> cases *)
Lemma rotate_right_max:
  forall (A : Type)
         (compare : A -> A -> element_comparison)
         (h_rot_root : nat)
         (e : A)
         (h_rot_left : nat)
         (hbt_left : heightened_binary_tree A)
         (e' : A)
         (hbt_right : heightened_binary_tree A)
         (max' : A)
         (h_org : nat)
         (max : A),
    traverse_to_check_ordered_hbt
      A
      (HNode A h_rot_root
             (Node A
                   (Triple A
                           (HNode A 0 (Leaf A))
                           e
                           (HNode A h_rot_left
                                  (Node A
                                        (Triple A
                                                hbt_left
                                                e'
                                                hbt_right))))))
      compare = TSome (A * A) (e, max') ->
    traverse_to_check_ordered_hbt
      A (HNode A h_org
               (Node A (Triple A
                               (HNode A 0 (Leaf A))
                               e'
                               hbt_right)))
      compare = TSome (A * A) (e', max) ->
    max' = max.
Proof.
  intros. 
  induction hbt_right as [h_r bt_r].
  induction hbt_left as [h_l bt_l].
  
  rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H.
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_node in H.    
  rewrite -> fold_unfold_traverse_to_check_ordered_t in H.
  rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H.    
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_leaf in H.
  rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H.
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_node in H.    
  rewrite -> fold_unfold_traverse_to_check_ordered_t in H.

    (* now we do a case analysis on hbt2 *)
  case bt_r as [ | t_r].

    (* bt_l is a leaf *)
    + (* obtain the t_max value from H0 first *)
      rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H0.
      rewrite -> fold_unfold_traverse_to_check_ordered_bt_node in H0.
      rewrite -> fold_unfold_traverse_to_check_ordered_t in H0.      
      rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H0.
      rewrite -> fold_unfold_traverse_to_check_ordered_bt_leaf in H0.      
      rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H0.
      rewrite -> fold_unfold_traverse_to_check_ordered_bt_leaf in H0.      
      rewrite -> tsome_x_equal_tsome_y in H0.
      rewrite -> pairwise_equality in H0.
      destruct H0 as [_ H_e_t_max].

      (* now case analyse our way through the goal *)
      case (traverse_to_check_ordered_hbt A (HNode A h_l bt_l) compare)
           as [ | | (min_l, max_l)].
      discriminate.
      rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H.
      rewrite -> fold_unfold_traverse_to_check_ordered_bt_leaf in H.
      case (compare e e') as [ | | ].
      rewrite -> tsome_x_equal_tsome_y in H.
      rewrite -> pairwise_equality in H.
      destruct H as [_ H_e_t_max'].
      rewrite <- H_e_t_max'.
      exact H_e_t_max.

      discriminate.
      
      discriminate.
      
      case (compare max_l e') as [ | | ].
      rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H.
      rewrite -> fold_unfold_traverse_to_check_ordered_bt_leaf in H.
      case (compare e min_l) as [ | | ].
      rewrite -> tsome_x_equal_tsome_y in H.
      rewrite -> pairwise_equality in H.
      destruct H as [_ H_e_t_max'].
      rewrite <- H_e_t_max'.
      exact H_e_t_max.

      discriminate.

      discriminate.

      discriminate.

      discriminate.

    (* bt_l is a node *)
    + (* obtain the t_max value from H0 first *)
      rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H0.
      rewrite -> fold_unfold_traverse_to_check_ordered_bt_node in H0.
      rewrite -> fold_unfold_traverse_to_check_ordered_t in H0.      
      rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H0.
      rewrite -> fold_unfold_traverse_to_check_ordered_bt_leaf in H0.
      rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H0.      
      case (traverse_to_check_ordered_bt A (Node A t_r) compare)
        as [ | | (minr, maxr)] eqn : C_traverse_ord_hbt_r.
      discriminate.
      
      assert (H_false: False).
      exact (traverse_node_impossible_case A compare t_r C_traverse_ord_hbt_r).

      apply (False_ind).
      exact H_false.

      case (compare e' minr) as [ | | ] eqn : H_comp_e_minr.
      rewrite -> tsome_x_equal_tsome_y in H0.
      rewrite -> pairwise_equality in H0.
      destruct H0 as [_ H_maxr_t_max].

      (* now return to the goal *)
      case (traverse_to_check_ordered_hbt A (HNode A h_l bt_l) compare)
           as [ | | (min_l, max_l)].
      discriminate.
      rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H.
      rewrite -> C_traverse_ord_hbt_r in H.
      rewrite -> H_comp_e_minr in H.
      case (compare e e') as [ | | ].
      rewrite -> tsome_x_equal_tsome_y in H.
      rewrite -> pairwise_equality in H.
      destruct H as [_ H_maxr_t_max'].
      rewrite <- H_maxr_t_max'.
      exact H_maxr_t_max.

      discriminate.

      discriminate.

      case (compare max_l e') as [ | | ].
      rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H.
      rewrite -> C_traverse_ord_hbt_r in H.
      rewrite -> H_comp_e_minr in H.
      case (compare e min_l) as [ | | ].
      rewrite -> tsome_x_equal_tsome_y in H.
      rewrite -> pairwise_equality in H.
      destruct H as [_ H_maxr_t_max'].
      rewrite <- H_maxr_t_max'.
      exact H_maxr_t_max.

      discriminate.

      discriminate.

      discriminate.

      discriminate.

      discriminate.

      discriminate.
Qed.

(** Lemma to show that post an insertion operation on a tree which necessitates a 
right rotation rebalance operation,  the minimum element of a right rotated tree
is either
- the element originally inserted
- or the minimum value of the subtree on which the insertion operation was
performed *)
Lemma rotate_right_min:
  forall (A : Type)
         (compare : A -> A -> element_comparison)
         (hbt1 : heightened_binary_tree A)
         (e : A)
         (h2 : nat)
         (bt2 : binary_tree A)
         (t_min t_max min1 max1 t_min' x : A),
    traverse_to_check_ordered_t A (Triple A hbt1 e (HNode A h2 bt2)) compare =
    TSome (A * A) (t_min, t_max) ->
    traverse_to_check_ordered_hbt A hbt1 compare = TSome (A * A) (min1, max1) -> 
    t_min' = x \/ t_min' = min1 ->
    t_min' = x \/ t_min' = t_min.
Proof.
  intros A compare hbt1 e h2 bt2 t_min t_max min1 max1 t_min' x H0 H1 H2.
  destruct H2 as [H_t_min'_x | H_t_min'_min1].

  (* H_t_min'_x *)
  apply or_introl.
  exact H_t_min'_x.

  (* H_t_min'_min1 *)
  apply or_intror.
  rewrite -> fold_unfold_traverse_to_check_ordered_t in H0.
  rewrite -> H1 in H0.
  case (compare max1 e) as [ | | ].
  case (traverse_to_check_ordered_hbt A (HNode A h2 bt2) compare)
    as [ | | (min2, max2)].
  discriminate.
  rewrite -> tsome_x_equal_tsome_y in H0.
  rewrite -> pairwise_equality in H0.
  destruct H0 as [H_min1_t_min' _].
  rewrite -> H_t_min'_min1.
  exact H_min1_t_min'.
  case (compare e min2) as [ | | ].
  rewrite -> tsome_x_equal_tsome_y in H0.
  rewrite -> pairwise_equality in H0.
  destruct H0 as [H_min1_t_min' _].
  rewrite -> H_t_min'_min1.
  exact H_min1_t_min'.  
  discriminate.
  discriminate.
  discriminate.
  discriminate.
Qed.  

(** Lemma to show that if a tree subject to <<rotate_right_1>> (double rotation) 
is ordered, then the original subtree into which an element was inserted was also
ordered *)
Lemma rotate_right_1_tree_ordered_implies_returned_tree_ordered:
  forall (A : Type)
         (compare : A -> A -> element_comparison)
         (h11' h121' h122' h2 h1' h12': nat)
         (bt11' bt121' bt122' bt2 : binary_tree A)
         (e1 e12 e t_min' t_max' : A), 
         traverse_to_check_ordered_hbt
         A
         (HNode A
                (1 + max (1 + max h11' h121') (1 + max h122' h2))
                (Node A
                      (Triple A
                              (HNode A (1 + max h11' h121')
                                     (Node A (Triple A
                                                     (HNode A h11' bt11')
                                                     e1
                                                     (HNode A h121' bt121'))))
                              e12
                              (HNode A (1 + max h122' h2)
                                     (Node A (Triple A
                                                     (HNode A h122' bt122')
                                                     e
                                                     (HNode A h2 bt2)))))))
         compare =
         TSome (A * A) (t_min', t_max') ->
         exists t_max'', 
         traverse_to_check_ordered_hbt
           A
           (HNode A h1'
                  (Node A
                        (Triple A (HNode A h11' bt11') e1
                                (HNode A h12'
                                       (Node A
                                             (Triple A
                                                     (HNode A h121' bt121')
                                                     e12
                                                     (HNode A h122' bt122')))))))
           compare = TSome (A * A) (t_min', t_max'').
Proof. 
  intros.

  (* first, show that all the subtrees are ordered *)
  assert (H_ord:
            is_ordered_hbt
              A
              (HNode A (1 + max (1 + max h11' h121') (1 + max h122' h2))
                     (Node A
                           (Triple A
                                   (HNode A (1 + max h11' h121')
                                          (Node A (Triple A
                                                          (HNode A h11' bt11')
                                                          e1
                                                          (HNode A h121' bt121'))))
                                   e12
                                   (HNode A (1 + max h122' h2)
                                          (Node A (Triple A
                                                          (HNode A h122' bt122')
                                                          e
                                                          (HNode A h2 bt2)))))))
              compare = true).
  exact (traverse_to_check_ordered_hbt_some_implies_is_ordered
           A compare
           (HNode A (1 + max (1 + max h11' h121') (1 + max h122' h2))
                  (Node A
                        (Triple A
                                (HNode A (1 + max h11' h121')
                                       (Node A (Triple A
                                                       (HNode A h11' bt11')
                                                       e1
                                                       (HNode A h121' bt121'))))
                                e12
                                (HNode A (1 + max h122' h2)
                                       (Node A (Triple A
                                                       (HNode A h122' bt122')
                                                       e
                                                       (HNode A h2 bt2)))))))
           t_min' t_max' H). 
  destruct (triple_ordered_implies_hbts_ordered
              A compare
              (1 + max (1 + max h11' h121') (1 + max h122' h2))
              (HNode A (1 + max h11' h121')
                     (Node A (Triple A (HNode A h11' bt11')
                                     e1
                                     (HNode A h121' bt121'))))
              e12
              (HNode A (1 + max h122' h2)
                     (Node A (Triple A (HNode A h122' bt122') e (HNode A h2 bt2))))
              H_ord) as [H_left_ord H_right_ord].
  destruct (triple_ordered_implies_hbts_ordered
              A compare
              (1 + max h11' h121')
              (HNode A h11' bt11')
              e1
              (HNode A h121' bt121')
              H_left_ord) as [H_bt11'_ord H_bt121'_ord].
  destruct (triple_ordered_implies_hbts_ordered
              A compare
              (1 + max h122' h2)
              (HNode A h122' bt122')
              e
              (HNode A h2 bt2)
              H_right_ord) as [H_bt122'_ord H_bt2_ord].

  (* assert inequalities *)
  assert (H_comp_max_bt11'_e1:
            forall  (min11' max11' : A),
              traverse_to_check_ordered_hbt
                A (HNode A h11' bt11') compare = TSome (A * A) (min11', max11') ->
              compare max11' e1 = Lt). 
  intros min11' max11' H_traverse_ord_bt11'.
  rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H.
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_node in H.  
  rewrite -> fold_unfold_traverse_to_check_ordered_t in H.    
  rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H.
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_node in H.  
  rewrite -> fold_unfold_traverse_to_check_ordered_t in H.    
  rewrite -> H_traverse_ord_bt11' in H.  
  case (compare max11' e1) as [ | | ] eqn : C_comp_max11'_e1.
  reflexivity.
  discriminate.
  discriminate.

  assert (H_comp_max_bt121'_e12:
            forall  (min121' max121' : A),
              traverse_to_check_ordered_hbt
                A (HNode A h121' bt121') compare = TSome (A * A) (min121', max121') ->
              compare max121' e12 = Lt). 
  intros.
  rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H.
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_node in H.  
  rewrite -> fold_unfold_traverse_to_check_ordered_t in H.    
  rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H.
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_node in H.  
  rewrite -> fold_unfold_traverse_to_check_ordered_t in H.
  rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H.
  rewrite -> H0 in H.  
  case (traverse_to_check_ordered_bt A bt11' compare)
       as [ | | (min11', max11')].
  discriminate.
  case (compare e1 min121') as [ | | ].
  case (compare max121' e12) as [ | | ] eqn : C_comp_max121'_e12.
  reflexivity.
  discriminate.
  discriminate.
  discriminate.
  discriminate.
  case (compare max11' e1) as [ | | ].
  case (compare e1 min121') as [ | | ].
  case (compare max121' e12) as [ | | ] eqn : C_comp_max121'_e12.
  reflexivity.
  discriminate.
  discriminate.
  discriminate.
  discriminate.
  discriminate.
  discriminate.

  (* to prove this inequality, clevery reduce the original rotated tree while 
   * preserving order *)
  assert (H_comp_e12_min_122': 
            forall  (min122' max122' : A),
              traverse_to_check_ordered_hbt
                A (HNode A h122' bt122') compare = TSome (A * A) (min122', max122') ->
              compare e12 min122' = Lt). 
  intros.
  assert (H_reduced_tree:
            traverse_to_check_ordered_hbt
              A
              (HNode A (1 + max (1 + max h11' h121') (1 + max h122' h2))
                     (Node A
                           (Triple A (HNode A 0 (Leaf A)) e12
                                   (HNode A (1 + max h122' h2)
                                          (Node A (Triple A
                                                          (HNode A h122' bt122')
                                                          e
                                                          (HNode A h2 bt2)))))))
              compare = TSome (A * A) (e12, t_max')).
  exact (reduce_ordered_hbt_left
           A compare
           (1 + max (1 + max h11' h121') (1 + max h122' h2))
           (HNode A (1 + max h11' h121')
                  (Node A (Triple A (HNode A h11' bt11') e1 (HNode A h121' bt121'))))
           e12
           (HNode A (1 + max h122' h2)
                  (Node A (Triple A (HNode A h122' bt122') e (HNode A h2 bt2))))
           t_min' t_max'
           H).
  rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H_reduced_tree.
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_node in H_reduced_tree.  
  rewrite -> fold_unfold_traverse_to_check_ordered_t in H_reduced_tree.    
  rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H_reduced_tree.
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_leaf in H_reduced_tree.
  rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H_reduced_tree.
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_node in H_reduced_tree.    
  rewrite -> fold_unfold_traverse_to_check_ordered_t in H_reduced_tree.
  rewrite -> H0 in H_reduced_tree.
  case (compare max122' e) as [ | | ].
  case (traverse_to_check_ordered_hbt A (HNode A h2 bt2) compare)
    as [ | | (min2, max2)].
  discriminate.
  case (compare e12 min122') as [ | | ] eqn : C_comp_e12_min122'.
  reflexivity.
  discriminate.
  discriminate.
  case (compare e min2) as [ | | ].
  case (compare e12 min122') as [ | | ] eqn : C_comp_e12_min122'.
  reflexivity.
  discriminate.
  discriminate.
  discriminate.
  discriminate.
  discriminate.
  discriminate.

  (* Fortunately, we can simply use H_left_ord *)
  assert (H_comp_e1_min_121': 
            forall  (min121' max121' : A),
              traverse_to_check_ordered_hbt
                A (HNode A h121' bt121') compare = TSome (A * A) (min121', max121') ->
              compare e1 min121' = Lt). 
  intros.
  unfold is_ordered_hbt in H_left_ord.
  rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H_left_ord.
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_node in H_left_ord.  
  rewrite -> fold_unfold_traverse_to_check_ordered_t in H_left_ord.
  case (traverse_to_check_ordered_hbt A (HNode A h11' bt11') compare)
    as [ | | (min11', max11')].
  discriminate.
  rewrite -> H0 in H_left_ord.
  case (compare e1 min121') as [ | | ] eqn : C_comp_e1_min121'.
  reflexivity.
  discriminate.
  discriminate.
  case (compare max11' e1) as [ | | ].
  rewrite -> H0 in H_left_ord.
  case (compare e1 min121') as [ | | ] eqn : C_comp_e1_min121'.
  reflexivity.
  discriminate.
  discriminate.
  discriminate.
  discriminate.

  (* With all our theorems in place, we now unfold the goal *)
  rewrite -> fold_unfold_traverse_to_check_ordered_hbt.
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_node.
  rewrite -> fold_unfold_traverse_to_check_ordered_t.
  rewrite ->
          (fold_unfold_traverse_to_check_ordered_hbt
             A h12'
             (Node A (Triple A (HNode A h121' bt121') e12 (HNode A h122' bt122')))
             compare).
  rewrite ->
          (fold_unfold_traverse_to_check_ordered_bt_node
             A 
             (Triple A (HNode A h121' bt121') e12 (HNode A h122' bt122'))
             compare).
  rewrite ->
          (fold_unfold_traverse_to_check_ordered_t
             A
             (HNode A h121' bt121')
             e12
             (HNode A h122' bt122')
             compare).

  (* to retrieve the minimum value in each case *)
  assert (H_for_t_min':
            traverse_to_check_ordered_hbt
              A
              (HNode A (1 + max (1 + max h11' h121') (1 + max h122' h2))
                     (Node A
                           (Triple A
                                   (HNode A (1 + max h11' h121')
                                          (Node A (Triple A (HNode A h11' bt11') e1 (HNode A h121' bt121')))) e12
                                   (HNode A 0 (Leaf A))))) compare = 
            TSome (A * A) (t_min', e12)).
  exact (reduce_ordered_hbt_right
           A compare
           (1 + max (1 + max h11' h121') (1 + max h122' h2))
           (HNode A (1 + max h11' h121')
                  (Node A (Triple A (HNode A h11' bt11') e1 (HNode A h121' bt121'))))
           e12
           (HNode A (1 + max h122' h2)
                  (Node A (Triple A (HNode A h122' bt122') e (HNode A h2 bt2))))
           t_min' t_max' H).
  rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H_for_t_min'.
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_node in H_for_t_min'.
  rewrite -> fold_unfold_traverse_to_check_ordered_t in H_for_t_min'.
  rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H_for_t_min'.
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_node in H_for_t_min'.
  rewrite -> fold_unfold_traverse_to_check_ordered_t in H_for_t_min'.
  rewrite -> (fold_unfold_traverse_to_check_ordered_hbt A 0 (Leaf A) compare)  in H_for_t_min'.
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_leaf in H_for_t_min'.

  (* Finally, we may tackle the 8 possible cases *) 
  case (is_ordered_true_implies_leaf_or_ordered_node
          A compare (HNode A h11' bt11') H_bt11'_ord)
    as [H_bt11'_leaf | H_bt11'_node].
  
  (* bt11' = leaf *)
  - case (is_ordered_true_implies_leaf_or_ordered_node
          A compare (HNode A h121' bt121') H_bt121'_ord)
    as [H_bt121'_leaf | H_bt121'_node].
    
    (* bt121' = leaf *)
    + case (is_ordered_true_implies_leaf_or_ordered_node
              A compare (HNode A h122' bt122') H_bt122'_ord)
      as [H_bt122'_leaf | H_bt122'_node].

      (* bt122' = leaf *)
      {
        rewrite -> H_bt11'_leaf.
        rewrite -> H_bt121'_leaf.
        rewrite -> H_bt122'_leaf.
        rewrite -> H_bt11'_leaf in H_for_t_min'.
        rewrite -> H_bt121'_leaf in H_for_t_min'.
        case (compare e1 e12) as [ | | ].
        rewrite -> tsome_x_equal_tsome_y in H_for_t_min'.
        rewrite -> pairwise_equality in H_for_t_min'.
        destruct H_for_t_min' as [H_t_min' _].
        exists e12.
        rewrite -> H_t_min'.
        reflexivity.

        discriminate.

        discriminate.
      }

      (* bt122' = node *)
      {
        destruct H_bt122'_node as [min122' [max122' H_bt122'_node]].
        rewrite -> H_bt11'_leaf.
        rewrite -> H_bt121'_leaf.
        rewrite -> H_bt122'_node.
        rewrite -> H_bt11'_leaf in H_for_t_min'.
        rewrite -> H_bt121'_leaf in H_for_t_min'.
        case (compare e1 e12) as [ | | ] eqn : C_comp_e1_e12.
        rewrite -> (H_comp_e12_min_122' min122' max122' H_bt122'_node).
        rewrite -> C_comp_e1_e12.
        exists max122'.
        rewrite -> tsome_x_equal_tsome_y in H_for_t_min'.
        rewrite -> pairwise_equality in H_for_t_min'.
        destruct H_for_t_min' as [H_t_min' _].
        rewrite -> H_t_min'.
        reflexivity.

        discriminate.

        discriminate.
      }

    (* bt121' = node *)
    + case (is_ordered_true_implies_leaf_or_ordered_node
              A compare (HNode A h122' bt122') H_bt122'_ord)
        as [H_bt122'_leaf | H_bt122'_node].

      (* bt122' = leaf *)
      {
        destruct H_bt121'_node as [min121' [max121' H_bt121'_node]].
        rewrite -> H_bt11'_leaf.
        rewrite -> H_bt122'_leaf.
        rewrite -> H_bt121'_node.
        rewrite -> H_bt11'_leaf in H_for_t_min'.
        rewrite -> H_bt121'_node in H_for_t_min'.
        rewrite -> (H_comp_max_bt121'_e12 min121' max121' H_bt121'_node).
        rewrite -> (H_comp_e1_min_121' min121' max121' H_bt121'_node).
        rewrite -> (H_comp_e1_min_121' min121' max121' H_bt121'_node) in H_for_t_min'.        
        rewrite -> (H_comp_max_bt121'_e12 min121' max121' H_bt121'_node) in H_for_t_min'.
        exists e12.
        rewrite -> tsome_x_equal_tsome_y in H_for_t_min'.
        rewrite -> pairwise_equality in H_for_t_min'.
        destruct H_for_t_min' as [H_t_min' _].
        rewrite -> H_t_min'.
        reflexivity. 
      }

      (* bt122' = node *)
      {
        destruct H_bt122'_node as [min122' [max122' H_bt122'_node]].
        destruct H_bt121'_node as [min121' [max121' H_bt121'_node]].
        rewrite -> H_bt121'_node.
        rewrite -> H_bt122'_node.
        rewrite -> H_bt11'_leaf.
        rewrite -> H_bt11'_leaf in H_for_t_min'.
        rewrite -> H_bt121'_node in H_for_t_min'.
        rewrite -> (H_comp_max_bt121'_e12 min121' max121' H_bt121'_node).
        rewrite -> (H_comp_e12_min_122' min122' max122' H_bt122'_node).
        rewrite -> (H_comp_e1_min_121' min121' max121' H_bt121'_node) in H_for_t_min'.        
        rewrite -> (H_comp_max_bt121'_e12 min121' max121' H_bt121'_node) in H_for_t_min'.
        rewrite -> (H_comp_e1_min_121' min121' max121' H_bt121'_node).
        exists max122'.
        rewrite -> tsome_x_equal_tsome_y in H_for_t_min'.
        rewrite -> pairwise_equality in H_for_t_min'.
        destruct H_for_t_min' as [H_t_min' _].
        rewrite -> H_t_min'.
        reflexivity. 
      }

  (* bt11' = node *)
  - case (is_ordered_true_implies_leaf_or_ordered_node
            A compare (HNode A h121' bt121') H_bt121'_ord)
      as [H_bt121'_leaf | H_bt121'_node].
    
    (* bt121' = leaf *)
    + case (is_ordered_true_implies_leaf_or_ordered_node
              A compare (HNode A h122' bt122') H_bt122'_ord)
        as [H_bt122'_leaf | H_bt122'_node].
    
      (* bt122' = leaf *)
      {
        destruct H_bt11'_node as [min11' [max11' H_bt11'_node]].
        rewrite -> H_bt11'_node.
        rewrite -> H_bt121'_leaf.
        rewrite -> H_bt122'_leaf.
        rewrite -> H_bt11'_node in H_for_t_min'.
        rewrite -> H_bt121'_leaf in H_for_t_min'.
        rewrite -> (H_comp_max_bt11'_e1 min11' max11' H_bt11'_node).
        rewrite -> (H_comp_max_bt11'_e1 min11' max11' H_bt11'_node) in H_for_t_min'.
        (* this should've been asserted, be more careful *)
        case (compare e1 e12) as [ | | ].
        exists e12.
        rewrite -> tsome_x_equal_tsome_y in H_for_t_min'.
        rewrite -> pairwise_equality in H_for_t_min'.
        destruct H_for_t_min' as [H_t_min' _].
        rewrite -> H_t_min'.
        reflexivity. 

        discriminate.
        
        discriminate.
      }

      (* bt122' = node *)
      {
        destruct H_bt11'_node as [min11' [max11' H_bt11'_node]].
        destruct H_bt122'_node as [min122' [max122' H_bt122'_node]].
        rewrite -> H_bt11'_node.
        rewrite -> H_bt121'_leaf.        
        rewrite -> H_bt122'_node.
        rewrite -> (H_comp_max_bt11'_e1 min11' max11' H_bt11'_node).
        rewrite -> (H_comp_e12_min_122' min122' max122' H_bt122'_node).
        rewrite -> H_bt11'_node in H_for_t_min'.
        rewrite -> H_bt121'_leaf in H_for_t_min'.
        rewrite -> (H_comp_max_bt11'_e1 min11' max11' H_bt11'_node) in H_for_t_min'.        
        case (compare e1 e12) as [ | | ].
        exists max122'.
        rewrite -> tsome_x_equal_tsome_y in H_for_t_min'.
        rewrite -> pairwise_equality in H_for_t_min'.
        destruct H_for_t_min' as [H_t_min' _].
        rewrite -> H_t_min'.
        reflexivity. 

        discriminate.
        
        discriminate.
      }

    + case (is_ordered_true_implies_leaf_or_ordered_node
              A compare (HNode A h122' bt122') H_bt122'_ord)
        as [H_bt122'_leaf | H_bt122'_node].

      (* bt122' = leaf *)
      {
        destruct H_bt11'_node as [min11' [max11' H_bt11'_node]].
        destruct H_bt121'_node as [min121' [max121' H_bt121'_node]].
        rewrite -> H_bt11'_node.
        rewrite -> H_bt121'_node.
        rewrite -> H_bt122'_leaf.
        rewrite -> (H_comp_max_bt11'_e1 min11' max11' H_bt11'_node).
        rewrite -> (H_comp_max_bt121'_e12 min121' max121' H_bt121'_node).
        rewrite -> (H_comp_e1_min_121' min121' max121' H_bt121'_node).
        rewrite -> H_bt11'_node in H_for_t_min'.
        rewrite -> H_bt121'_node in H_for_t_min'.
        rewrite -> (H_comp_max_bt11'_e1 min11' max11' H_bt11'_node) in H_for_t_min'.        
        rewrite -> (H_comp_e1_min_121' min121' max121' H_bt121'_node) in H_for_t_min'.
        rewrite -> (H_comp_max_bt121'_e12 min121' max121' H_bt121'_node) in H_for_t_min'.
        exists e12.
        rewrite -> tsome_x_equal_tsome_y in H_for_t_min'.
        rewrite -> pairwise_equality in H_for_t_min'.
        destruct H_for_t_min' as [H_t_min' _].
        rewrite -> H_t_min'.
        reflexivity. 
      }

      (* bt122' = node *)
      {
        destruct H_bt11'_node as [min11' [max11' H_bt11'_node]].
        destruct H_bt121'_node as [min121' [max121' H_bt121'_node]].
        destruct H_bt122'_node as [min122' [max122' H_bt122'_node]].
        rewrite -> H_bt11'_node.
        rewrite -> H_bt121'_node.
        rewrite -> H_bt122'_node.
        rewrite -> (H_comp_max_bt121'_e12 min121' max121' H_bt121'_node).
        rewrite -> (H_comp_e12_min_122' min122' max122' H_bt122'_node).
        rewrite -> (H_comp_max_bt11'_e1 min11' max11' H_bt11'_node).
        rewrite -> (H_comp_e1_min_121' min121' max121' H_bt121'_node).
        rewrite -> H_bt11'_node in H_for_t_min'.
        rewrite -> H_bt121'_node in H_for_t_min'.
        rewrite -> (H_comp_max_bt11'_e1 min11' max11' H_bt11'_node) in H_for_t_min'.
        rewrite -> (H_comp_e1_min_121' min121' max121' H_bt121'_node) in H_for_t_min'.
        rewrite -> (H_comp_max_bt121'_e12 min121' max121' H_bt121'_node)
          in H_for_t_min'.
        exists max122'.
        rewrite -> tsome_x_equal_tsome_y in H_for_t_min'.
        rewrite -> pairwise_equality in H_for_t_min'.
        destruct H_for_t_min' as [H_t_min' _].
        rewrite -> H_t_min'.
        reflexivity.         
      }
Qed.

(** Lemma to show that if an insertion operation led to a <<rotate_right_1>>
operation, then the subtree on which the insertion operation was performed cannot
be a leaf *)
Lemma rotate_right_1_impossible_case:
  forall (A : Type)
         (compare : A -> A -> element_comparison)
         (x : A)
         (h1 : nat)
         (bt1 : binary_tree A)
         (h1' h11' h12' h121' h122' : nat)
         (bt11' bt121' bt122' : binary_tree A)
         (e1 e12 : A), 
    insert_hbt_helper A compare x (HNode A h1 bt1) =
    Some
      (HNode A h1'
             (Node A
                   (Triple A (HNode A h11' bt11') e1
                           (HNode A h12'
                                  (Node A
                                        (Triple A
                                                (HNode A h121' bt121')
                                                e12
                                                (HNode A h122' bt122'))))))) ->
    bt1 <> (Leaf A).
Proof.
  intros A compare x h1 bt1 h1' h11' h12' h121' h122' bt11' bt121' bt122' e1 e12 H.
  induction bt1 as [ | t1].

  rewrite -> fold_unfold_insert_hbt_helper in H.
  rewrite -> fold_unfold_insert_bt_helper_leaf in H.
  rewrite -> some_x_equal_some_y in H.
  discriminate.
  unfold not.
  intro H'.
  discriminate.
Qed.

(** Lemma to show that post the insertion of some element <<x>> in a tree which 
unbalances the tree and necessitates a <<rotate_right_1>> operation, 
- the minimum element of a tree subjected to a <<rotate_right_1>> operation is either <<x>> or the minimum element of the original tree 
- the maximum element of a tree subjected to a <<rotate_right_1>> operation is either <<x>> or the maximum element of the original tree *)
Lemma rotate_right_1_min_max: 
  forall (A : Type)
         (compare : A -> A -> element_comparison)
         (h11' h121' h122' h2 : nat)
         (bt11' bt121' bt122' bt2 : binary_tree A)
         (e1 e12 e : A)
         (hbt1 : heightened_binary_tree A)
         (t_min' t_max' t_min t_max min1 max1 x : A),
    traverse_to_check_ordered_t
      A 
      (Triple A
              (HNode A (1 + max h11' h121')
                     (Node A (Triple A
                                     (HNode A h11' bt11')
                                     e1
                                     (HNode A h121' bt121'))))
              e12
              (HNode A (1 + max h122' h2)
                     (Node A (Triple A
                                     (HNode A h122' bt122')
                                     e
                                     (HNode A h2 bt2))))) compare =
    TSome (A * A) (t_min', t_max') ->
    traverse_to_check_ordered_t A (Triple A hbt1 e (HNode A h2 bt2)) compare =
    TSome (A * A) (t_min, t_max) ->
    traverse_to_check_ordered_hbt A hbt1 compare = TSome (A * A) (min1, max1) ->
    t_min' = x \/ t_min' = min1 ->
    (t_max' = x \/ t_max' = t_max) /\ (t_min' = x \/ t_min' = t_min).
Proof.
  intros.

  split.
  
  (* prove min case first, since it is more straightforward *)
  Focus 2.
  exact (rotate_right_min A compare hbt1 e h2 bt2 t_min t_max min1 max1 t_min' x H0 H1 H2).

  - apply or_intror.

    (* t_max' is max2 in our case; to show this, we will left reduce the rotated tree
     * twice *)

    (* we first reduce our original triple to only consider hbt2 *)
    assert (H_traverse_hbt_org:
              traverse_to_check_ordered_hbt
                A
                (HNode A h2 (Node A ((Triple A hbt1 e (HNode A h2 bt2))))) compare = 
              TSome (A * A) (t_min, t_max)).
    rewrite -> fold_unfold_traverse_to_check_ordered_hbt.
    rewrite -> fold_unfold_traverse_to_check_ordered_bt_node.  
    exact H0.


    assert (H_hbt_org_reduceed:
              traverse_to_check_ordered_hbt
                A
                (HNode A h2 (Node A (Triple A (HNode A 0 (Leaf A)) e (HNode A h2 bt2)))) compare =
              TSome (A * A) (e, t_max)).
    exact (reduce_ordered_hbt_left
             A compare h2 hbt1 e (HNode A h2 bt2) t_min t_max H_traverse_hbt_org).
    
    (* next, we must get the returned triple in to hbt form *)
    assert (H_traverse_hbt_rotated:
              traverse_to_check_ordered_hbt
                A
                (HNode A (1 + max (1 + max h11' h121') (1 + max h122' h2))
                       (Node A 
                             (Triple A
                                     (HNode A (1 + max h11' h121')
                                            (Node A (Triple A (HNode A h11' bt11') e1 (HNode A h121' bt121')))) e12
                                     (HNode A (1 + max h122' h2)
                                            (Node A (Triple A (HNode A h122' bt122') e (HNode A h2 bt2))))))) compare = TSome (A * A) (t_min', t_max')).
    rewrite -> fold_unfold_traverse_to_check_ordered_hbt.
    rewrite -> fold_unfold_traverse_to_check_ordered_bt_node.  
    exact H.

    (* next, use reduce_ordered_hbt_left *)
    assert (H_reconstrcuted_1 :
              traverse_to_check_ordered_hbt
                A
                (HNode A (1 + max (1 + max h11' h121') (1 + max h122' h2))
                       (Node A
                             (Triple A (HNode A 0 (Leaf A)) e12
                                     (HNode A (1 + max h122' h2)
                                            (Node A (Triple A (HNode A h122' bt122') e (HNode A h2 bt2))))))) compare =
              TSome (A * A) (e12, t_max')).
    exact (reduce_ordered_hbt_left
             A compare (1 + max (1 + max h11' h121') (1 + max h122' h2))
             (HNode A (1 + max h11' h121')
                    (Node A
                          (Triple A 
                                  (HNode A h11' bt11') e1 
                                  (HNode A h121' bt121'))))
             e12
             (HNode A (1 + max h122' h2)
                    (Node A
                          (Triple A (HNode A h122' bt122') e (HNode A h2 bt2))))
             t_min' t_max' H_traverse_hbt_rotated).
    exact (rotate_right_max
             A compare (1 + max (1 + max h11' h121') (1 + max h122' h2))
             e12 (1 + max h122' h2)
             (HNode A h122' bt122') e (HNode A h2 bt2)
             t_max' h2 t_max
             H_reconstrcuted_1
             H_hbt_org_reduceed).
Qed.    

(** Lemma to show that if a tree subject to <<rotate_right_2>> (single rotation) 
is ordered, then the original subtree into which an element was inserted was also
ordered *)
Lemma rotate_right_2_tree_ordered_implies_returned_tree_ordered:
  forall (A : Type)
         (compare : A -> A -> element_comparison)
         (h1' h11' h12' h2 : nat)
         (bt11' bt12' bt2 : binary_tree A)
         (e1 e : A)
         (t_min' t_max' : A),
    traverse_to_check_ordered_hbt
      A
      (HNode A (1 + max h11' (1 + max h12' h2))
             (Node A
                   (Triple A
                           (HNode A h11' bt11')
                           e1
                           (HNode A (1 + max h12' h2)
                                  (Node A (Triple A
                                                  (HNode A h12' bt12')
                                                  e
                                                  (HNode A h2 bt2)))))))
      compare = TSome (A * A) (t_min', t_max') ->
    exists t_max'',
      traverse_to_check_ordered_hbt
        A
        (HNode A h1'
               (Node A (Triple A (HNode A h11' bt11') e1 (HNode A h12' bt12'))))
        compare = TSome (A * A) (t_min', t_max'').
Proof.
  intros.
  
  (* fold traverse_to_check_ordered_hbt in H *)
  assert (H_fold_traverse:
            is_ordered_hbt
              A
              (HNode A (1 + max h11' (1 + max h12' h2))
                     (Node A
                           (Triple A (HNode A h11' bt11') e1
                                   (HNode A (1 + max h12' h2)
                                          (Node A (Triple A (HNode A h12' bt12') e (HNode A h2 bt2))))))) compare = true).
  unfold is_ordered_hbt.
  rewrite -> H.
  reflexivity.

  (* assert orderedness of bt11' and bt12' *)
  destruct (triple_ordered_implies_hbts_ordered
              A compare (1 + max h11' (1 + max h12' h2))
              (HNode A h11' bt11')
              e1
              (HNode A (1 + max h12' h2)
                     (Node A (Triple A (HNode A h12' bt12') e (HNode A h2 bt2))))
              H_fold_traverse) as [H_ord_bt11' H_ord_right_subtree].
  destruct (triple_ordered_implies_hbts_ordered
              A compare (1 + max h12' h2)
              (HNode A h12' bt12')
              e
              (HNode A h2 bt2)
              H_ord_right_subtree) as [H_ord_bt12' H_ord_bt2].

  (* assert required inequalities *)

  (* max11' < e1 *)
  assert (H_comp_max11'_e1:
            forall (min11' max11' : A),
              traverse_to_check_ordered_hbt A (HNode A h11' bt11') compare =
              TSome (A * A) (min11', max11') ->
              compare max11' e1 = Lt).
  intros.
  
  (* reconstuct the rotated tree to isolate section of the tree we need *)
  assert (H_reduced_tree:
            traverse_to_check_ordered_hbt
              A
              (HNode A (1 + max h11' (1 + max h12' h2))
                     (Node A (Triple A (HNode A h11' bt11') e1 (HNode A 0 (Leaf A))))) compare =
            TSome (A * A) (t_min', e1)).
  exact (reduce_ordered_hbt_right
           A compare (1 + max h11' (1 + max h12' h2))
           (HNode A h11' bt11')
           e1
           (HNode A (1 + max h12' h2)
                  (Node A (Triple A (HNode A h12' bt12') e (HNode A h2 bt2))))
           t_min' t_max' H).
  
  rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H_reduced_tree.
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_node in H_reduced_tree.
  rewrite -> fold_unfold_traverse_to_check_ordered_t in H_reduced_tree.
  rewrite -> H0 in H_reduced_tree.
  rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H_reduced_tree.
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_leaf in H_reduced_tree.
  case (compare max11' e1) as [ | | ] eqn : C_comp_max11'_e1.
  reflexivity.
  discriminate.
  discriminate.

  (* e1 < max12' *)
  assert (H_comp_e1_min12':
            forall (min12' max12' : A),
              traverse_to_check_ordered_hbt A (HNode A h12' bt12') compare =
              TSome (A * A) (min12', max12') ->
              compare e1 min12' = Lt).
  intros.
  (* reduce tree *)
  assert (H_reduced_tree:
            traverse_to_check_ordered_hbt
              A
              (HNode A (1 + max h11' (1 + max h12' h2))
                     (Node A
                           (Triple A (HNode A 0 (Leaf A)) e1
                                   (HNode A (1 + max h12' h2)
                                          (Node A (Triple A (HNode A h12' bt12') e (HNode A h2 bt2))))))) compare =
            TSome (A * A) (e1, t_max')).
  exact (reduce_ordered_hbt_left
           A compare (1 + max h11' (1 + max h12' h2))
           (HNode A h11' bt11')
           e1
           (HNode A (1 + max h12' h2)
                  (Node A (Triple A (HNode A h12' bt12') e (HNode A h2 bt2))))
           t_min' t_max' H).
  rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H_reduced_tree.
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_node in H_reduced_tree.
  rewrite -> fold_unfold_traverse_to_check_ordered_t in H_reduced_tree.
  rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H_reduced_tree.
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_leaf in H_reduced_tree.
  rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H_reduced_tree.
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_node in H_reduced_tree.
  rewrite -> fold_unfold_traverse_to_check_ordered_t in H_reduced_tree.
  rewrite -> H0 in H_reduced_tree.
  case (compare max12' e) as [ | | ].
  case (traverse_to_check_ordered_hbt A (HNode A h2 bt2) compare) as
      [ | | (min2, max2)].
  discriminate.
  case (compare e1 min12') as [ | | ] eqn : C_comp_e1_min12'.
  reflexivity.
  discriminate.
  discriminate.
  case (compare e min2) as [ | | ].
  case (compare e1 min12') as [ | | ] eqn : C_comp_e1_min12'.
  reflexivity.
  discriminate.
  discriminate.  
  discriminate.
  discriminate.
  discriminate.
  discriminate.  

  (* right reduce the rotated tree to obtain the minimum value for each case *)
  assert (H_reduced_tree:
            traverse_to_check_ordered_hbt
              A
              (HNode A (1 + max h11' (1 + max h12' h2))
                     (Node A (Triple A (HNode A h11' bt11') e1 (HNode A 0 (Leaf A))))) compare =
            TSome (A * A) (t_min', e1)).
  exact (reduce_ordered_hbt_right
           A compare (1 + max h11' (1 + max h12' h2))
           (HNode A h11' bt11')
           e1
           (HNode A (1 + max h12' h2)
                  (Node A (Triple A (HNode A h12' bt12') e (HNode A h2 bt2))))
           t_min' t_max' H).
  
  rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H_reduced_tree.
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_node in H_reduced_tree.
  rewrite -> fold_unfold_traverse_to_check_ordered_t in H_reduced_tree.
  rewrite -> (fold_unfold_traverse_to_check_ordered_hbt A 0 (Leaf A) compare) in H_reduced_tree.
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_leaf in H_reduced_tree.

  (* finally, work through all possible cases for bt11' and bt12' *)
  case (is_ordered_true_implies_leaf_or_ordered_node
          A compare (HNode A h11' bt11') H_ord_bt11') as [H_bt11'_leaf | H_bt11'_node].

  (* bt11' = leaf *)
  - case (is_ordered_true_implies_leaf_or_ordered_node
            A compare (HNode A h12' bt12') H_ord_bt12') as [H_bt12'_leaf | H_bt12'_node]. 

    (* bt12' = leaf *)
    + rewrite -> fold_unfold_traverse_to_check_ordered_hbt.
      rewrite -> fold_unfold_traverse_to_check_ordered_bt_node.
      rewrite -> fold_unfold_traverse_to_check_ordered_t.      
      rewrite -> H_bt11'_leaf.
      rewrite -> H_bt12'_leaf.
      rewrite -> H_bt11'_leaf in H_reduced_tree.
      rewrite -> tsome_x_equal_tsome_y in H_reduced_tree.
      rewrite -> pairwise_equality in H_reduced_tree.
      destruct H_reduced_tree as [H_e1_t_min' _].
      rewrite -> H_e1_t_min'.
      exists t_min'.
      reflexivity.
      
    (* bt12' = node *)
    + destruct H_bt12'_node as [min12' [max12' H_bt12'_node]].
      rewrite -> fold_unfold_traverse_to_check_ordered_hbt.
      rewrite -> fold_unfold_traverse_to_check_ordered_bt_node.
      rewrite -> fold_unfold_traverse_to_check_ordered_t.
      rewrite -> H_bt11'_leaf.
      rewrite -> H_bt12'_node.
      rewrite -> (H_comp_e1_min12' min12' max12' H_bt12'_node).
      rewrite -> H_bt11'_leaf in H_reduced_tree.
      rewrite -> tsome_x_equal_tsome_y in H_reduced_tree.
      rewrite -> pairwise_equality in H_reduced_tree.
      destruct H_reduced_tree as [H_e1_t_min' _].
      rewrite -> H_e1_t_min'.
      exists max12'.
      reflexivity.

  (* bt11' = node *)
  - case (is_ordered_true_implies_leaf_or_ordered_node
            A compare (HNode A h12' bt12') H_ord_bt12') as [H_bt12'_leaf | H_bt12'_node]. 

    (* bt12' = leaf *)
    + destruct H_bt11'_node as [min11' [max11' H_bt11'_node]].
      rewrite -> fold_unfold_traverse_to_check_ordered_hbt.
      rewrite -> fold_unfold_traverse_to_check_ordered_bt_node.
      rewrite -> fold_unfold_traverse_to_check_ordered_t.
      rewrite -> H_bt11'_node.
      rewrite -> H_bt12'_leaf. 
      rewrite -> H_bt11'_node in H_reduced_tree.
      rewrite -> (H_comp_max11'_e1 min11' max11' H_bt11'_node).
      rewrite -> (H_comp_max11'_e1 min11' max11' H_bt11'_node) in H_reduced_tree.
      rewrite -> tsome_x_equal_tsome_y in H_reduced_tree.
      rewrite -> pairwise_equality in H_reduced_tree.
      destruct H_reduced_tree as [H_min11'_t_min' _].
      rewrite -> H_min11'_t_min'.
      exists e1.
      reflexivity.

    (* bt12' = node *)
    + destruct H_bt11'_node as [min11' [max11' H_bt11'_node]].
      destruct H_bt12'_node as [min12' [max12' H_bt12'_node]].
      rewrite -> fold_unfold_traverse_to_check_ordered_hbt.
      rewrite -> fold_unfold_traverse_to_check_ordered_bt_node.
      rewrite -> fold_unfold_traverse_to_check_ordered_t.
      rewrite -> H_bt11'_node.
      rewrite -> H_bt12'_node. 
      rewrite -> H_bt11'_node in H_reduced_tree.
      rewrite -> (H_comp_max11'_e1 min11' max11' H_bt11'_node).
      rewrite -> (H_comp_max11'_e1 min11' max11' H_bt11'_node) in H_reduced_tree.      
      rewrite -> (H_comp_e1_min12' min12' max12' H_bt12'_node).
      rewrite -> tsome_x_equal_tsome_y in H_reduced_tree.
      rewrite -> pairwise_equality in H_reduced_tree.
      destruct H_reduced_tree as [H_min11'_t_min' _].
      rewrite -> H_min11'_t_min'.
      exists max12'.
      reflexivity.      
Qed.

(** The lemmas [rotate_right_2_impossible_case_1] and 
[rotate_right_2_impossible_case_2] concern the two sub-cases which arise in case of 
the <<rotate_right_2>> operation, and show that if an insertion operation led to
a <<rotate_right_2>> operation, then the subtree on which the insertion operation
was performed cannot be a leaf *)
Lemma rotate_right_2_impossible_case_1:
  forall (A : Type)
         (compare : A -> A -> element_comparison)
         (x : A)
         (h1 : nat)
         (bt1 : binary_tree A)
         (h1' h11' h12' : nat)
         (bt11' bt12' : binary_tree A)
         (e1 : A),
    insert_hbt_helper A compare x (HNode A h1 bt1) =
    Some
      (HNode A h1'
             (Node A
                   (Triple A
                           (HNode A h11' bt11')
                           e1
                           (HNode A h12' bt12')))) ->
    (h12' + 1 =n= h11') = true -> 
    bt1 <> (Leaf A).
Proof.
  intros.

  induction bt1 as [ | t1].

  rewrite -> fold_unfold_insert_hbt_helper in H.
  rewrite -> fold_unfold_insert_bt_helper_leaf in H.
  rewrite -> some_x_equal_some_y in H.

  apply  beq_nat_true in H0.
  rewrite <- H0 in H.

  assert (H_unequal: False).
  case h12' as [ | h12''].
  rewrite -> plus_O_n in H0.
  rewrite -> plus_O_n in H.
  discriminate.
  discriminate.
  
  unfold not.
  intro H'.
  exact H_unequal.

  unfold not.
  intro H'.
  discriminate.
Qed.

Lemma rotate_right_2_impossible_case_2:
  forall (A : Type)
         (compare : A -> A -> element_comparison)
         (x : A)
         (h1 : nat)
         (bt1 : binary_tree A)
         (h1' h11' h12' : nat)
         (bt11' bt12' : binary_tree A)
         (e1 : A)
         (h2 : nat)
         (bt2 : binary_tree A),
    is_sound_hbt A (HNode A h1 bt1) = true -> 
    is_balanced_hbt A (HNode A h1 bt1) = true -> 
    insert_hbt_helper A compare x (HNode A h1 bt1) =
    Some
      (HNode A h1' (Node A (Triple A
                                   (HNode A h11' bt11')
                                   e1
                                   (HNode A h12' bt12')))) ->
    (h12' =n= h11') = true ->
    compare_int h1' (2 + project_height_hbt A (HNode A h2 bt2)) = Eq -> 
    bt1 <> (Leaf A).
Proof.
  intros.

  (* first, obtain a relationship between h11' and h12' *)
  assert (H_hbt_ret_sound:
            is_sound_hbt A (HNode A h1' (Node A (Triple A
                                                        (HNode A h11' bt11')
                                                        e1
                                                        (HNode A h12' bt12')))) =
            true).
  destruct (insertion_preserves_soundness A compare x) as [H_hbt _].

  assert (H_sound:
            is_sound_hbt
              A
              (HNode A h1' (Node A (Triple A
                                           (HNode A h11' bt11')
                                           e1
                                           (HNode A h12' bt12')))) = true).
  exact (H_hbt
           (HNode A h1 bt1)
           (HNode A h1' (Node A (Triple A (HNode A h11' bt11') e1 (HNode A h12' bt12'))))
           H H1).
  
  exact H_sound.
  
  assert (H_h1'_h11'_h12' :
            1 + max h11' h12' = h1').
  symmetry.
  exact (relate_heights A h1' h11' bt11' e1 h12' bt12' H_hbt_ret_sound).

  (* next, show that h11' cannot be 0 *)
  apply beq_nat_true in H2.
  destruct (non_zero_height A h11' h12' h1' h2 bt2 H2 H_h1'_h11'_h12' H3)
    as [n H_h12'_non_zero].
  rewrite <- H2 in H1.
  rewrite -> H_h12'_non_zero in H1.

  (* now use induction *)
  case bt1 as [ | t1].

  rewrite -> fold_unfold_insert_hbt_helper in H1.
  rewrite -> fold_unfold_insert_bt_helper_leaf in H1.
  rewrite -> some_x_equal_some_y in H1.
  discriminate.

  discriminate.
Qed.

(** Lemma to show that post the insertion of some element <<x>> in a tree which 
unbalances the tree, 
- the minimum element of a tree subjected to a <<rotate_right_2>> operation is either
<<x>> or the minimum element of the original tree 
- the maximum element of a tree subjected to a <<rotate_right_2>> operation is either
<<x>> or the maximum element of the original tree *)
Lemma rotate_right_2_min_max: 
  forall (A : Type)
         (compare : A -> A -> element_comparison)
         (h11' h12' h2 : nat)
         (bt11' bt12' bt2 : binary_tree A)
         (e1 e : A)
         (hbt1 : heightened_binary_tree A)
         (t_min' t_max' t_min t_max min1 max1 x : A),
    traverse_to_check_ordered_hbt
      A
      (HNode A (1 + max h11' (1 + max h12' h2))
             (Node A
                   (Triple A (HNode A h11' bt11') e1
                           (HNode A (1 + max h12' h2)
                                  (Node A (Triple A
                                                  (HNode A h12' bt12')
                                                  e
                                                  (HNode A h2 bt2)))))))
                                  compare = TSome (A * A) (t_min', t_max') ->     
    traverse_to_check_ordered_t A (Triple A hbt1 e (HNode A h2 bt2)) compare =
    TSome (A * A) (t_min, t_max) ->
    traverse_to_check_ordered_hbt A hbt1 compare = TSome (A * A) (min1, max1) ->
    t_min' = x \/ t_min' = min1 ->
    (t_max' = x \/ t_max' = t_max) /\ (t_min' = x \/ t_min' = t_min).
Proof.
  intros.
  split.

  (* prove min first *)
  Focus 2.
  exact (rotate_right_min
           A compare hbt1 e h2 bt2 t_min t_max min1 max1 t_min' x H0 H1 H2).

  (* prove max *)
  apply or_intror.
  
  (* first, fold traverse for oridinal tree *)
  assert (H_fold_traverse:
            traverse_to_check_ordered_hbt
              A
              (HNode A (1 + max (project_height_hbt A hbt1) h2)
                     (Node A (Triple A hbt1 e (HNode A h2 bt2)))) compare =
            TSome (A * A) (t_min, t_max)).
  unfold is_ordered_hbt.
  rewrite -> fold_unfold_traverse_to_check_ordered_hbt.
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_node.
  exact H0.

  (* then left reduce it *)
  assert (H_hbt_org_reduced:
            traverse_to_check_ordered_hbt
              A
              (HNode A (1 + max (project_height_hbt A hbt1) h2)
                     (Node A (Triple A (HNode A 0 (Leaf A)) e (HNode A h2 bt2)))) compare =
            TSome (A * A) (e, t_max)).
  exact (reduce_ordered_hbt_left
           A compare (1 + max (project_height_hbt A hbt1) h2)
           hbt1 e (HNode A h2 bt2) t_min t_max H_fold_traverse).

  (* next, left reduce the rotated tree *)
  assert (H_hbt_rot_reduced:
            traverse_to_check_ordered_hbt
              A
              (HNode A (1 + max h11' (1 + max h12' h2))
                     (Node A
                           (Triple A (HNode A 0 (Leaf A)) e1
                                   (HNode A (1 + max h12' h2)
                                          (Node A (Triple A (HNode A h12' bt12') e (HNode A h2 bt2))))))) compare =
            TSome (A * A) (e1, t_max')).
  exact (reduce_ordered_hbt_left
           A compare (1 + max h11' (1 + max h12' h2))
           (HNode A h11' bt11')
           e1
           (HNode A (1 + max h12' h2)
                  (Node A (Triple A (HNode A h12' bt12') e (HNode A h2 bt2))))
           t_min' t_max' H).

  (* finally, invoke the rotate_right_max lemma *)
  exact (rotate_right_max
           A compare (1 + max h11' (1 + max h12' h2))
           e1 (1 + max h12' h2)
           (HNode A h12' bt12') e (HNode A h2 bt2)
           t_max' (1 + max (project_height_hbt A hbt1) h2) t_max
           H_hbt_rot_reduced
           H_hbt_org_reduced).
Qed.

(* ***** *)

(* ***** *)

(** ** Left Rotation Lemmas *)

(** Lemma to show that the maximum element of a left rotated tree is the same as the 
maximum element of the left reduced form of the original sub-tree into which the
insertion was performed. Note that because the lemma can be used in both the 
<<rotate_left_1>> and the <<rotate_left_2>> cases *)
Lemma rotate_left_max:
  forall (A : Type)
         (compare : A -> A -> element_comparison)
         (h1 : nat)
         (bt1 : binary_tree A)
         (e : A)
         (hbt2 : heightened_binary_tree A)
         (t_min t_max min2 max2 t_max' x : A),
    traverse_to_check_ordered_t A (Triple A (HNode A h1 bt1) e hbt2) compare =
    TSome (A * A) (t_min, t_max) ->
    traverse_to_check_ordered_hbt A hbt2 compare = TSome (A * A) (min2, max2) ->
    t_max' = x \/ t_max' = max2 ->
    (t_max' = x \/ t_max' = t_max).
Proof.
  intros.
  destruct H1 as [H_t_max'_x | H_t_max'_max2].

  (* H_t_max'_x *)
  apply or_introl.
  exact H_t_max'_x.

  (* H_t_max'_max2 *)
  apply or_intror.

  (* left reduce the original tree *)
  assert (H': traverse_to_check_ordered_hbt
            A (HNode A (1 + max h1 (project_height_hbt A hbt2))
                                (Node A (Triple A (HNode A h1 bt1) e hbt2)))
            compare = TSome (A * A) (t_min, t_max)).
  rewrite -> fold_unfold_traverse_to_check_ordered_hbt.
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_node.
  exact H.
  
  assert (H_t_left_reduced:
            traverse_to_check_ordered_hbt
              A
              (HNode A (1 + max h1 (project_height_hbt A hbt2))
                     (Node A (Triple A (HNode A 0 (Leaf A)) e hbt2))) compare = 
            TSome (A * A) (e, t_max)).
  exact (reduce_ordered_hbt_left
           A compare (1 + max h1 (project_height_hbt A hbt2))
           (HNode A h1 bt1) e hbt2 t_min t_max H').

  (* unfold the left reduced tree *)
  rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H_t_left_reduced.
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_node in H_t_left_reduced.
  rewrite -> fold_unfold_traverse_to_check_ordered_t in H_t_left_reduced.  
  rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H_t_left_reduced.
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_leaf in H_t_left_reduced.
  rewrite -> H0 in H_t_left_reduced.
  case (compare e min2) as [ | | ].
  rewrite -> tsome_x_equal_tsome_y in H_t_left_reduced.
  rewrite -> pairwise_equality in H_t_left_reduced.
  destruct H_t_left_reduced as [_ H_max2_t_max].
  rewrite -> H_max2_t_max in H_t_max'_max2.
  exact H_t_max'_max2.

  discriminate.

  discriminate.
Qed.

(** Lemma to show that post an insertion operation on a tree which necessitates a 
left rotation rebalance operation,  the minimum element of a left rotated tree
is either
- the element originally inserted
- or the minimum value of the subtree on which the insertion operation was
performed *)
Lemma rotate_left_min:
  forall (A : Type)
         (compare : A -> A -> element_comparison)
         (h_rot_root : nat)
         (h_rot_left : nat)
         (hbt_left : heightened_binary_tree A)
         (e' : A)
         (hbt_right : heightened_binary_tree A)
         (e : A)
         (min' : A)
         (h_org : nat)
         (min : A),
    traverse_to_check_ordered_hbt
      A
      (HNode A h_rot_root 
           (Node A
                 (Triple A
                         (HNode A 
                                h_rot_left
                                (Node A
                                      (Triple A hbt_left e' hbt_right)))
                         e
                         (HNode A 0 (Leaf A))))) compare = 
    TSome (A * A) (min', e) ->
    traverse_to_check_ordered_hbt
      A (HNode A h_org
               (Node A (Triple A hbt_left e' (HNode A 0 (Leaf A)))))
      compare = TSome (A * A) (min, e') ->
    min' = min.
Proof.
  intros.

  (* unfold the original tree first *)
  rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H0.
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_node in H0.
  rewrite -> fold_unfold_traverse_to_check_ordered_t in H0.  
  rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H0.
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_leaf in H0.
  
  (* unfold the reduced rotated tree *)
  rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H.
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_node in H.
  rewrite -> fold_unfold_traverse_to_check_ordered_t in H.  
  rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H.
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_node in H.
  rewrite -> fold_unfold_traverse_to_check_ordered_t in H.  
  rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H.
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_leaf in H.
  case (traverse_to_check_ordered_hbt A hbt_left compare)
    as [ | | (minl, maxl)].

  (* hbt_left is unordered *)
  - discriminate.

  (* hbt_left is a leaf *)
  - case (traverse_to_check_ordered_hbt A hbt_right compare)
      as [ | | (minr, maxr)].

    (* hbt_right is unordered *)
    discriminate.

    (* hbt_right is a leaf *)
    case (compare e' e) as [ | | ].
    rewrite -> tsome_x_equal_tsome_y in H.
    rewrite -> pairwise_equality in H.
    destruct H as [H_e'_min' _].
    rewrite -> tsome_x_equal_tsome_y in H0.
    rewrite -> pairwise_equality in H0.
    destruct H0 as [H_e'_min _].
    rewrite <- H_e'_min'.
    exact H_e'_min.
    
    discriminate.

    discriminate.
    
    (* hbt_right is a node *)
    case (compare e' minr) as [ | | ].
    case (compare maxr e) as [ | | ].
    rewrite -> tsome_x_equal_tsome_y in H.
    rewrite -> pairwise_equality in H.
    destruct H as [H_e'_min' _].
    rewrite -> tsome_x_equal_tsome_y in H0.
    rewrite -> pairwise_equality in H0.
    destruct H0 as [H_e'_min _].
    rewrite <- H_e'_min'.
    exact H_e'_min.

    discriminate.

    discriminate.
    
    discriminate.

    discriminate.

  (* hbt_left is a node *)
  - case (traverse_to_check_ordered_hbt A hbt_right compare)
      as [ | | (minr, maxr)].

    (* hbt_right is unordered *)
    case (compare maxl e') as [ | | ].
    discriminate.
    
    discriminate.

    discriminate.

    (* hbt_right is a leaf *)
    case (compare maxl e') as [ | | ].
    case (compare e' e) as [ | | ].
    rewrite -> tsome_x_equal_tsome_y in H.
    rewrite -> pairwise_equality in H.
    destruct H as [H_minl_min' _].
    rewrite -> tsome_x_equal_tsome_y in H0.
    rewrite -> pairwise_equality in H0.
    destruct H0 as [H_minl_min _].
    rewrite <- H_minl_min'.
    exact H_minl_min.

    discriminate.
    
    discriminate.

    discriminate.
    
    discriminate.

    (* hbt_right is a node *)
    case (compare maxl e') as [ | | ].
    case (compare e' minr) as [ | | ].
    case (compare maxr e) as [ | | ].
    rewrite -> tsome_x_equal_tsome_y in H.
    rewrite -> pairwise_equality in H.
    destruct H as [H_minl_min' _].
    rewrite -> tsome_x_equal_tsome_y in H0.
    rewrite -> pairwise_equality in H0.
    destruct H0 as [H_minl_min _].
    rewrite <- H_minl_min'.
    exact H_minl_min.
    
    discriminate.
    
    discriminate.

    discriminate.
    
    discriminate.

    discriminate.
    
    discriminate.
Qed.    

(** Lemma to show that if a tree subject to <<rotate_left_1>> (double rotation) 
is ordered, then the original subtree into which an element was inserted was also
ordered *)
Lemma rotate_left_1_tree_ordered_implies_returned_tree_ordered:
  forall (A : Type)
         (compare : A -> A -> element_comparison)
         (h1 h211' h212' h22' h2' h21' : nat)
         (bt1 bt211' bt212' bt22' : binary_tree A)
         (e e21 e2 t_min' t_max' : A),
    traverse_to_check_ordered_hbt
      A
      (HNode A (1 + max (1 + max h1 h211') (1 + max h212' h22'))
             (Node A
                   (Triple A
                           (HNode A (1 + max h1 h211')
                                  (Node A (Triple A
                                                  (HNode A h1 bt1)
                                                  e
                                                  (HNode A h211' bt211'))))
                           e21
                           (HNode A (1 + max h212' h22')
                                  (Node A (Triple A
                                                  (HNode A h212' bt212')
                                                  e2
                                                  (HNode A h22' bt22')))))))
      compare = TSome (A * A) (t_min', t_max') ->
    exists t_min'',
      traverse_to_check_ordered_hbt
        A
        (HNode A h2'
               (Node A
                     (Triple A
                             (HNode A h21'
                                    (Node A
                                          (Triple A
                                                  (HNode A h211' bt211')
                                                  e21
                                                  (HNode A h212' bt212'))))
                             e2
                             (HNode A h22' bt22'))))
        compare = TSome (A * A) (t_min'', t_max').
Proof.
  intros.

  (* assert that bt211' bt212' bt22' are ordered *)
  assert (H_fold_H:
            is_ordered_hbt
              A
              (HNode A (1 + max (1 + max h1 h211') (1 + max h212' h22'))
                     (Node A
                           (Triple A
                                   (HNode A (1 + max h1 h211')
                                          (Node A (Triple A
                                                          (HNode A h1 bt1)
                                                          e
                                                          (HNode A h211' bt211'))))
                                   e21
                                   (HNode A (1 + max h212' h22')
                                          (Node A (Triple A
                                                          (HNode A h212' bt212')
                                                          e2
                                                          (HNode A h22' bt22')))))))
              compare = true).
  exact (traverse_to_check_ordered_hbt_some_implies_is_ordered
           A compare
           (HNode A (1 + max (1 + max h1 h211') (1 + max h212' h22'))
                  (Node A
                        (Triple A
                                (HNode A (1 + max h1 h211')
                                       (Node A (Triple A
                                                       (HNode A h1 bt1)
                                                       e
                                                       (HNode A h211' bt211'))))
                                e21
                                (HNode A (1 + max h212' h22')
                                       (Node A (Triple A (HNode A h212' bt212')
                                                       e2
                                                       (HNode A h22' bt22')))))))
           t_min' t_max' H).
  destruct (triple_ordered_implies_hbts_ordered
              A compare (1 + max (1 + max h1 h211') (1 + max h212' h22'))
              (HNode A (1 + max h1 h211')
                     (Node A (Triple A (HNode A h1 bt1) e (HNode A h211' bt211'))))
              e21
              (HNode A (1 + max h212' h22')
                     (Node A (Triple A
                                     (HNode A h212' bt212')
                                     e2
                                     (HNode A h22' bt22'))))
              H_fold_H) as [H_left_ord H_right_ord].
  destruct (triple_ordered_implies_hbts_ordered
              A compare (1 + max h1 h211')
              (HNode A h1 bt1) e (HNode A h211' bt211')
              H_left_ord) as [_ H_bt211'_ord].
  destruct (triple_ordered_implies_hbts_ordered
              A compare (1 + max h212' h22')
              (HNode A h212' bt212') e2 (HNode A h22' bt22')
              H_right_ord) as [H_bt212'_ord H_bt22'_ord].

  (* construct left reduced tree: to be used for inequality proofs and the main one *)
  (* left reduce rotated tree *)
  assert (H_rotate_left_reduced:
            traverse_to_check_ordered_hbt
              A
              (HNode A (1 + max (1 + max h1 h211') (1 + max h212' h22'))
                     (Node A
                           (Triple A (HNode A 0 (Leaf A)) e21
                                   (HNode A (1 + max h212' h22')
                                          (Node A (Triple A (HNode A h212' bt212')
                                                          e2
                                                          (HNode A h22' bt22')))))))
              compare = TSome (A * A) (e21, t_max')).
  exact (reduce_ordered_hbt_left
           A compare (1 + max (1 + max h1 h211') (1 + max h212' h22'))
           (HNode A (1 + max h1 h211')
                  (Node A (Triple A (HNode A h1 bt1) e (HNode A h211' bt211'))))
           e21
           (HNode A (1 + max h212' h22')
                  (Node A (Triple A (HNode A h212' bt212') e2 (HNode A h22' bt22'))))
           t_min' t_max' H).

  
  (* assert inequalities *)

  (* max211' < e21 *)
  assert (H_comp_max211'_e21:
            forall (min211' max211' : A),
              traverse_to_check_ordered_hbt
                A (HNode A h211' bt211') compare = TSome (A * A) (min211', max211') ->
              compare max211' e21 = Lt).
  intros.

  (* reduce rotated tree first *)
  assert (H_rotate_right_reduced:
            traverse_to_check_ordered_hbt
              A
              (HNode A (1 + max (1 + max h1 h211') (1 + max h212' h22'))
                     (Node A
                           (Triple A
                                   (HNode A (1 + max h1 h211')
                                          (Node A (Triple A (HNode A h1 bt1) e (HNode A h211' bt211')))) e21
                                   (HNode A 0 (Leaf A))))) compare = 
            TSome (A * A) (t_min', e21)).
  exact (reduce_ordered_hbt_right
           A compare (1 + max (1 + max h1 h211') (1 + max h212' h22'))
           (HNode A (1 + max h1 h211')
                  (Node A (Triple A (HNode A h1 bt1) e (HNode A h211' bt211'))))
           e21
           (HNode A (1 + max h212' h22')
                  (Node A (Triple A (HNode A h212' bt212') e2 (HNode A h22' bt22'))))
           t_min' t_max' H).
  
  (* unfold H_right_reduced until inequality is proved *)
  rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H_rotate_right_reduced.
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_node in H_rotate_right_reduced.
  rewrite -> fold_unfold_traverse_to_check_ordered_t in H_rotate_right_reduced.
  rewrite -> (fold_unfold_traverse_to_check_ordered_hbt A 0 (Leaf A)) in H_rotate_right_reduced.
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_leaf in H_rotate_right_reduced.
  rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H_rotate_right_reduced.
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_node in H_rotate_right_reduced.
  rewrite -> fold_unfold_traverse_to_check_ordered_t in H_rotate_right_reduced.  
  case (traverse_to_check_ordered_hbt A (HNode A h1 bt1) compare)
       as [ | | (min1, max1)]. 

  (* unordered bt1 *)
  discriminate.

  (* bt1 is a leaf *)
  rewrite -> H0 in H_rotate_right_reduced.
  case (compare e min211') as [ | | ].
  case (compare max211' e21) as [ | | ].
  reflexivity.
  discriminate.
  discriminate.
  discriminate.
  discriminate.

  (* bt1 is a node *)
  case (compare max1 e) as [ | | ].
  rewrite -> H0 in H_rotate_right_reduced.
  case (compare e min211') as [ | | ].
  case (compare max211' e21) as [ | | ].
  reflexivity.
  discriminate.
  discriminate.
  discriminate.
  discriminate.    
  discriminate.
  discriminate.        

  (* max211' < e21 *)
  assert (H_comp_e21_min212':
            forall (min212' max212' : A),
              traverse_to_check_ordered_hbt
                A (HNode A h212' bt212') compare = TSome (A * A) (min212', max212') ->
              compare e21 min212' = Lt).
  intros.

  (* unfold and prove *)
  rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H_rotate_left_reduced.
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_node in H_rotate_left_reduced.
  rewrite -> fold_unfold_traverse_to_check_ordered_t in H_rotate_left_reduced.
  rewrite -> (fold_unfold_traverse_to_check_ordered_hbt A 0 (Leaf A)) in H_rotate_left_reduced.
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_leaf in H_rotate_left_reduced.
  rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H_rotate_left_reduced.
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_node in H_rotate_left_reduced.
  rewrite -> fold_unfold_traverse_to_check_ordered_t in H_rotate_left_reduced.  
  rewrite -> H0 in H_rotate_left_reduced.
  case (compare max212' e2) as [ | | ].
  case (traverse_to_check_ordered_hbt A (HNode A h22' bt22') compare) as
      [ | | (min22', max22')].

  (* unordered *)
  discriminate.

  (* leaf *)
  case (compare e21 min212') as [ | | ].
  reflexivity.
  discriminate.
  discriminate.

  (* node *)
  case (compare e2 min22') as [ | | ].
  case (compare e21 min212') as [ | | ].
  reflexivity.
  discriminate.
  discriminate.

  discriminate.
  discriminate.

  discriminate.
  discriminate.

  (* max212' < e2 *)
  assert (H_comp_max212'_e2:
            forall (min212' max212' : A),
              traverse_to_check_ordered_hbt
                A (HNode A h212' bt212') compare = TSome (A * A) (min212', max212') ->
              compare max212' e2 = Lt).
  intros.
  
  (* we can simply use H_right_ord *)
  unfold is_ordered_hbt in H_right_ord.
  rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H_right_ord.
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_node in H_right_ord.
  rewrite -> fold_unfold_traverse_to_check_ordered_t in H_right_ord.  
  rewrite -> H0 in H_right_ord.
  case (compare max212' e2) as [ | | ].
  case (traverse_to_check_ordered_hbt A (HNode A h22' bt22') compare)
       as [ | | (min22', max22')].
  discriminate.
  reflexivity.
  reflexivity.
  discriminate.
  discriminate.

  (* e2 < min22' *)
  assert (H_comp_e2_min22':
            forall (min22' max22' : A),
              traverse_to_check_ordered_hbt
                A (HNode A h22' bt22') compare = TSome (A * A) (min22', max22') ->
              compare e2 min22' = Lt).
  intros.

  (* again, we can use H_right_ord *)
  unfold is_ordered_hbt in H_right_ord.
  rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H_right_ord.
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_node in H_right_ord.
  rewrite -> fold_unfold_traverse_to_check_ordered_t in H_right_ord.  
  case (traverse_to_check_ordered_hbt A (HNode A h212' bt212') compare)
       as [ | | (min212', max212')].

  (* bt212' unordered *)
  discriminate.

  (* bt121' leaf *)
  rewrite -> H0 in H_right_ord.
  case (compare e2 min22') as [ | | ].
  reflexivity.
  discriminate.
  discriminate.

  (* bt121' node *)
  case (compare max212' e2) as [ | | ].
  rewrite -> H0 in H_right_ord.
  case (compare e2 min22') as [ | | ].
  reflexivity.
  discriminate.
  discriminate.

  discriminate.
  discriminate.

  (* left reduce the rotated tree and unfold *)
  rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H_rotate_left_reduced.
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_node in H_rotate_left_reduced.
  rewrite -> fold_unfold_traverse_to_check_ordered_t in H_rotate_left_reduced.
  rewrite -> (fold_unfold_traverse_to_check_ordered_hbt A 0 (Leaf A)) in H_rotate_left_reduced.
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_leaf in H_rotate_left_reduced.
  rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H_rotate_left_reduced.
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_node in H_rotate_left_reduced.
  rewrite -> fold_unfold_traverse_to_check_ordered_t in H_rotate_left_reduced.

  (* With all our theorems in place, we now unfold the goal *)
  rewrite -> fold_unfold_traverse_to_check_ordered_hbt.
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_node.
  rewrite -> fold_unfold_traverse_to_check_ordered_t.
  rewrite -> fold_unfold_traverse_to_check_ordered_hbt.
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_node.
  rewrite -> fold_unfold_traverse_to_check_ordered_t.
  
  (* with the reduced tree unfolded, work on the 8 cases *)
  case (is_ordered_true_implies_leaf_or_ordered_node
          A compare (HNode A h211' bt211') H_bt211'_ord)
    as [H_bt211'_leaf | H_bt211'_node].

  (* bt211' leaf *)
  - case (is_ordered_true_implies_leaf_or_ordered_node
            A compare (HNode A h212' bt212') H_bt212'_ord)
      as [H_bt212'_leaf | H_bt212'_node].

    (* bt212' leaf *)
    + case (is_ordered_true_implies_leaf_or_ordered_node
            A compare (HNode A h22' bt22') H_bt22'_ord)
      as [H_bt22'_leaf | H_bt22'_node].

      (* bt22' leaf *)
      {
        rewrite -> H_bt211'_leaf.
        rewrite -> H_bt212'_leaf.
        rewrite -> H_bt22'_leaf.
        rewrite -> H_bt212'_leaf in H_rotate_left_reduced.
        rewrite -> H_bt22'_leaf in H_rotate_left_reduced.
        case (compare e21 e2) as [ | | ].
        rewrite -> tsome_x_equal_tsome_y in H_rotate_left_reduced.
        rewrite -> pairwise_equality in H_rotate_left_reduced.        
        destruct H_rotate_left_reduced as [_ H_e2_t_max'].
        rewrite -> H_e2_t_max'.
        exists e21.
        reflexivity.
        discriminate.
        discriminate.
      }

      (* bt22' node *)
      {
        destruct H_bt22'_node as [min22' [max22' H_bt22'_node]].
        rewrite -> H_bt211'_leaf.
        rewrite -> H_bt212'_leaf.
        rewrite -> H_bt22'_node.
        rewrite -> H_bt212'_leaf in H_rotate_left_reduced.
        rewrite -> H_bt22'_node in H_rotate_left_reduced.
        rewrite -> (H_comp_e2_min22' min22' max22' H_bt22'_node) in H_rotate_left_reduced. 
        case (compare e21 e2) as [ | | ] eqn : C_comp_e21_e2.
        rewrite -> (H_comp_e2_min22' min22' max22' H_bt22'_node).
        rewrite -> tsome_x_equal_tsome_y in H_rotate_left_reduced.
        rewrite -> pairwise_equality in H_rotate_left_reduced.        
        destruct H_rotate_left_reduced as [_ H_max22'_t_max'].
        rewrite -> H_max22'_t_max'.
        exists e21.
        reflexivity.
        discriminate.
        discriminate.
      }
      
    (* bt212' node *)
    + case (is_ordered_true_implies_leaf_or_ordered_node
            A compare (HNode A h22' bt22') H_bt22'_ord)
      as [H_bt22'_leaf | H_bt22'_node].

      (* bt22' leaf *)
      {
        destruct H_bt212'_node as [min212' [max212' H_bt212'_node]].
        rewrite -> H_bt211'_leaf.
        rewrite -> H_bt212'_node.
        rewrite -> H_bt22'_leaf.
        rewrite -> H_bt212'_node in H_rotate_left_reduced.
        rewrite -> H_bt22'_leaf in H_rotate_left_reduced.
        rewrite -> (H_comp_max212'_e2 min212' max212' H_bt212'_node) in H_rotate_left_reduced.
        rewrite -> (H_comp_e21_min212' min212' max212' H_bt212'_node).
        rewrite -> (H_comp_e21_min212' min212' max212' H_bt212'_node) in H_rotate_left_reduced.
        rewrite -> (H_comp_max212'_e2 min212' max212' H_bt212'_node).
        rewrite -> tsome_x_equal_tsome_y in H_rotate_left_reduced.
        rewrite -> pairwise_equality in H_rotate_left_reduced.        
        destruct H_rotate_left_reduced as [_ H_e2_t_max'].
        rewrite -> H_e2_t_max'.
        exists e21.
        reflexivity.
      }

      (* bt22' node *)
      {
        destruct H_bt212'_node as [min212' [max212' H_bt212'_node]].
        destruct H_bt22'_node as [min22' [max22' H_bt22'_node]].
        rewrite -> H_bt211'_leaf.
        rewrite -> H_bt212'_node.
        rewrite -> H_bt22'_node.
        rewrite -> H_bt212'_node in H_rotate_left_reduced.
        rewrite -> H_bt22'_node in H_rotate_left_reduced.
        rewrite -> (H_comp_max212'_e2 min212' max212' H_bt212'_node) in H_rotate_left_reduced.
        rewrite -> (H_comp_e2_min22' min22' max22' H_bt22'_node) in H_rotate_left_reduced.
        rewrite -> (H_comp_e21_min212' min212' max212' H_bt212'_node)
          in H_rotate_left_reduced.
        rewrite -> (H_comp_e21_min212' min212' max212' H_bt212'_node).
        rewrite -> (H_comp_max212'_e2 min212' max212' H_bt212'_node).
        rewrite -> (H_comp_e2_min22' min22' max22' H_bt22'_node).
        rewrite -> tsome_x_equal_tsome_y in H_rotate_left_reduced.
        rewrite -> pairwise_equality in H_rotate_left_reduced.        
        destruct H_rotate_left_reduced as [_ H_max22'_t_max'].
        rewrite -> H_max22'_t_max'.
        exists e21.
        reflexivity.
      }

  (* bt211' node *)
  - case (is_ordered_true_implies_leaf_or_ordered_node
            A compare (HNode A h212' bt212') H_bt212'_ord)
      as [H_bt212'_leaf | H_bt212'_node].

    (* bt212' leaf *)
    + case (is_ordered_true_implies_leaf_or_ordered_node
              A compare (HNode A h22' bt22') H_bt22'_ord)
        as [H_bt22'_leaf | H_bt22'_node].

      (* bt22' leaf *)
      {
        destruct H_bt211'_node as [min211' [max211' H_bt211'_node]].
        rewrite -> H_bt211'_node.
        rewrite -> H_bt212'_leaf.
        rewrite -> H_bt22'_leaf.
        rewrite -> H_bt212'_leaf in H_rotate_left_reduced.
        rewrite -> H_bt22'_leaf in H_rotate_left_reduced.
        case (compare e21 e2) as [ | | ] eqn : C_comp_e21_e2.
        rewrite -> (H_comp_max211'_e21 min211' max211' H_bt211'_node).
        rewrite -> C_comp_e21_e2.
        rewrite -> tsome_x_equal_tsome_y in H_rotate_left_reduced.
        rewrite -> pairwise_equality in H_rotate_left_reduced.        
        destruct H_rotate_left_reduced as [_ H_e2_t_max'].
        rewrite -> H_e2_t_max'.
        exists min211'.
        reflexivity.
        discriminate.
        discriminate.
      }

      (* bt22' node *)
      {
        destruct H_bt211'_node as [min211' [max211' H_bt211'_node]].
        destruct H_bt22'_node as [min22' [max22' H_bt22'_node]].
        rewrite -> H_bt211'_node.
        rewrite -> H_bt212'_leaf.
        rewrite -> H_bt22'_node.
        rewrite -> H_bt212'_leaf in H_rotate_left_reduced.
        rewrite -> H_bt22'_node in H_rotate_left_reduced.
        rewrite -> (H_comp_e2_min22' min22' max22' H_bt22'_node) in H_rotate_left_reduced.
        case (compare e21 e2) as [ | | ] eqn : C_comp_e21_e2.
        rewrite -> (H_comp_max211'_e21 min211' max211' H_bt211'_node).
        rewrite -> C_comp_e21_e2.
        rewrite -> (H_comp_e2_min22' min22' max22' H_bt22'_node).
        rewrite -> tsome_x_equal_tsome_y in H_rotate_left_reduced.
        rewrite -> pairwise_equality in H_rotate_left_reduced.        
        destruct H_rotate_left_reduced as [_ H_max22'_t_max'].
        rewrite -> H_max22'_t_max'.
        exists min211'.
        reflexivity.
        discriminate.
        discriminate.
      }

    (* bt212' node *)
    + case (is_ordered_true_implies_leaf_or_ordered_node
              A compare (HNode A h22' bt22') H_bt22'_ord)
        as [H_bt22'_leaf | H_bt22'_node].

      (* bt22' leaf *)
      {
        destruct H_bt211'_node as [min211' [max211' H_bt211'_node]].
        destruct H_bt212'_node as [min212' [max212' H_bt212'_node]].
        rewrite -> H_bt211'_node.
        rewrite -> H_bt212'_node.
        rewrite -> H_bt22'_leaf.
        rewrite -> H_bt212'_node in H_rotate_left_reduced.
        rewrite -> H_bt22'_leaf in H_rotate_left_reduced.
        rewrite -> (H_comp_max212'_e2 min212' max212' H_bt212'_node) in H_rotate_left_reduced.
        rewrite -> (H_comp_e21_min212' min212' max212' H_bt212'_node) in H_rotate_left_reduced.
        rewrite -> (H_comp_max211'_e21 min211' max211' H_bt211'_node).
        rewrite -> (H_comp_e21_min212' min212' max212' H_bt212'_node).
        rewrite -> (H_comp_max212'_e2 min212' max212' H_bt212'_node).
        rewrite -> tsome_x_equal_tsome_y in H_rotate_left_reduced.
        rewrite -> pairwise_equality in H_rotate_left_reduced. 
        destruct H_rotate_left_reduced as [_ H_e2_t_max'].
        rewrite -> H_e2_t_max'.
        exists min211'.
        reflexivity.
      }

      (* bt22' node *)
      {
        destruct H_bt211'_node as [min211' [max211' H_bt211'_node]].
        destruct H_bt212'_node as [min212' [max212' H_bt212'_node]].
        destruct H_bt22'_node as [min22' [max22' H_bt22'_node]].
        rewrite -> H_bt211'_node.
        rewrite -> H_bt212'_node.
        rewrite -> H_bt22'_node.
        rewrite -> H_bt212'_node in H_rotate_left_reduced.
        rewrite -> H_bt22'_node in H_rotate_left_reduced.
        rewrite -> (H_comp_max212'_e2 min212' max212' H_bt212'_node) in H_rotate_left_reduced.
        rewrite -> (H_comp_e2_min22' min22' max22' H_bt22'_node) in H_rotate_left_reduced.
        rewrite -> (H_comp_e21_min212' min212' max212' H_bt212'_node) in H_rotate_left_reduced.
        rewrite -> (H_comp_max211'_e21 min211' max211' H_bt211'_node).
        rewrite -> (H_comp_e21_min212' min212' max212' H_bt212'_node).
        rewrite -> (H_comp_max212'_e2 min212' max212' H_bt212'_node).
        rewrite -> (H_comp_e2_min22' min22' max22' H_bt22'_node).
        rewrite -> tsome_x_equal_tsome_y in H_rotate_left_reduced.
        rewrite -> pairwise_equality in H_rotate_left_reduced. 
        destruct H_rotate_left_reduced as [_ H_max22'_t_max'].
        rewrite -> H_max22'_t_max'.
        exists min211'.
        reflexivity.
      }
Qed.

(** Lemma to show that if an insertion operation led to a <<rotate_left_1>>
operation, then the subtree on which the insertion operation was performed cannot
be a leaf *)
Lemma rotate_left_1_impossible_case:
  forall (A : Type)
         (compare : A -> A -> element_comparison)
         (x : A)
         (h2 : nat)
         (bt2 : binary_tree A)
         (h2' h21' h211' h212' h22' : nat)
         (bt211' bt212' bt22' : binary_tree A)
         (e21 e2 : A),
    insert_hbt_helper A compare x (HNode A h2 bt2) =
    Some
      (HNode A h2'
             (Node A
                   (Triple A
                           (HNode A h21'
                                  (Node A
                                        (Triple A
                                                (HNode A h211' bt211')
                                                e21
                                                (HNode A h212' bt212'))))
                           e2
                           (HNode A h22' bt22')))) -> bt2 <> Leaf A.
Proof.
  intros.
  case bt2 as [ | t2].

  rewrite -> fold_unfold_insert_hbt_helper in H.
  rewrite -> fold_unfold_insert_bt_helper_leaf in H.  
  rewrite -> some_x_equal_some_y in H.
  discriminate.

  unfold not.
  intro H'.
  discriminate.
Qed.

(** Lemma to show that post the insertion of some element <<x>> in a tree which 
unbalances the tree and necessitates a <<rotate_right_1>> operation, 
- the minimum element of a tree subjected to a <<rotate_left_1>> operation is either
<<x>> or the minimum element of the original tree 
- the maximum element of a tree subjected to a <<rotate_left_1>> operation is either
<<x>> or the maximum element of the original tree *)
Lemma rotate_left_1_min_max:
  forall (A : Type)
         (compare : A -> A -> element_comparison)
         (h1 h211' h212' h22' : nat)
         (bt1 bt211' bt212' bt22' : binary_tree A)
         (e e21 e2 : A)
         (hbt2 : heightened_binary_tree A)
         (t_min' t_max' t_min t_max min2 max2 x : A),
    traverse_to_check_ordered_hbt
      A
      (HNode A (1 + max (1 + max h1 h211') (1 + max h212' h22'))
             (Node A
                   (Triple A
                           (HNode A (1 + max h1 h211')
                                  (Node A (Triple A
                                                  (HNode A h1 bt1)
                                                  e
                                                  (HNode A h211' bt211'))))
                           e21
                           (HNode A (1 + max h212' h22')
                                  (Node A (Triple A
                                                  (HNode A h212' bt212')
                                                  e2
                                                  (HNode A h22' bt22')))))))
      compare = TSome (A * A) (t_min', t_max') ->
    traverse_to_check_ordered_t A (Triple A (HNode A h1 bt1) e hbt2) compare =
    TSome (A * A) (t_min, t_max) ->
    traverse_to_check_ordered_hbt A hbt2 compare =
    TSome (A * A) (min2, max2) ->
    t_max' = x \/ t_max' = max2 ->
    (t_max' = x \/ t_max' = t_max) /\ (t_min' = x \/ t_min' = t_min).
Proof.
  intros.
  split. 

  (* max *)
  exact (rotate_left_max
           A compare h1 bt1 e hbt2 t_min t_max min2 max2 t_max' x H0 H1 H2).

  (* min *)

  (* right reduce the rotated tree *)
  assert (H_rotated_tree_right_reduced:
            traverse_to_check_ordered_hbt
              A
              (HNode A (1 + max (1 + max h1 h211') (1 + max h212' h22'))
                     (Node A
                           (Triple A
                                   (HNode A (1 + max h1 h211')
                                          (Node A (Triple A
                                                          (HNode A h1 bt1)
                                                          e
                                                          (HNode A h211' bt211'))))
                                   e21
                                   (HNode A 0 (Leaf A))))) compare = 
            TSome (A * A) (t_min', e21)).
  exact (reduce_ordered_hbt_right
           A compare (1 + max (1 + max h1 h211') (1 + max h212' h22'))
           (HNode A (1 + max h1 h211')
                  (Node A (Triple A (HNode A h1 bt1) e (HNode A h211' bt211')))) e21
           (HNode A (1 + max h212' h22')
                  (Node A (Triple A (HNode A h212' bt212') e2 (HNode A h22' bt22'))))
           t_min' t_max' H).

  (* right reduce the original tree *)
  assert (H_org_tree_reduced:
            traverse_to_check_ordered_hbt
              A
              (HNode A (1 + max h1 (project_height_hbt A hbt2))
                     (Node A (Triple A (HNode A h1 bt1) e (HNode A 0 (Leaf A)))))
              compare = TSome (A * A) (t_min, e)).
  exact (reduce_ordered_hbt_right
           A compare (1 + max h1 (project_height_hbt A hbt2))
           (HNode A h1 bt1) e hbt2 t_min t_max H0).

  apply or_intror.
  (* invoke rotate_left_max *)
  exact (rotate_left_min
           A compare (1 + max (1 + max h1 h211') (1 + max h212' h22'))
           (1 + max h1 h211')
           (HNode A h1 bt1) e (HNode A h211' bt211')
           e21 t_min' (1 + max h1 (project_height_hbt A hbt2)) t_min 
           H_rotated_tree_right_reduced H_org_tree_reduced).
Qed.

(** Lemma to show that if a tree subject to <<rotate_left_2>> (single rotation) 
is ordered, then the original subtree into which an element was inserted was also
ordered *)
Lemma rotate_left_2_tree_ordered_implies_returned_tree_ordered:
  forall (A : Type)
         (compare : A -> A ->element_comparison)
         (h1 h21' h22' h2' : nat)
         (bt1 bt21' bt22' : binary_tree A)
         (e e2 : A)
         (t_min' t_max' : A),
    traverse_to_check_ordered_hbt
      A
      (HNode A (1 + max (1 + max h1 h21') h22')
             (Node A
                   (Triple A
                           (HNode A (1 + max h1 h21')
                                  (Node A (Triple A
                                                  (HNode A h1 bt1)
                                                  e
                                                  (HNode A h21' bt21'))))
                           e2
                           (HNode A h22' bt22')))) compare = 
    TSome (A * A) (t_min', t_max') ->
    exists t_min'',
      traverse_to_check_ordered_hbt
        A
        (HNode A h2'
               (Node A (Triple A
                               (HNode A h21' bt21')
                               e2
                               (HNode A h22' bt22')))) compare =
      TSome (A * A) (t_min'', t_max').
Proof.  
  intros.

  (* show that bt21' and bt22' are ordered *)

  (* fold the traverse for the rotated tree *)
  assert (H_fold_H:
            is_ordered_hbt
              A 
              (HNode A (1 + max (1 + max h1 h21') h22')
                     (Node A
                           (Triple A
                                   (HNode A (1 + max h1 h21')
                                          (Node A (Triple A
                                                          (HNode A h1 bt1)
                                                          e
                                                          (HNode A h21' bt21'))))
                                   e2
                                   (HNode A h22' bt22')))) compare = true).
  exact (traverse_to_check_ordered_hbt_some_implies_is_ordered
           A compare
           (HNode A (1 + max (1 + max h1 h21') h22')
                  (Node A
                        (Triple A
                                (HNode A (1 + max h1 h21')
                                       (Node A (Triple A
                                                       (HNode A h1 bt1)
                                                       e
                                                       (HNode A h21' bt21'))))
                                e2
                                (HNode A h22' bt22'))))
           t_min' t_max' H).

  (* show the left and right subtrees are ordered *)
  destruct (triple_ordered_implies_hbts_ordered
              A compare
              (1 + max (1 + max h1 h21') h22')
              (HNode A (1 + max h1 h21')
                     (Node A (Triple A (HNode A h1 bt1) e (HNode A h21' bt21'))))
              e2
              (HNode A h22' bt22')
              H_fold_H) as [H_left_subtree_ord H_bt22'_ord].

  (* show the bt1 and bt21' in the left subtree are ordered *)
  destruct (triple_ordered_implies_hbts_ordered
              A compare (1 + max h1 h21')
              (HNode A h1 bt1) e (HNode A h21' bt21')
              H_left_subtree_ord) as [H_ord_bt1 H_bt21'_ord].

  (* left reduce rotated tree for 2nd inequality proof and final proof *)
  assert (H_rotate_left_reduced:
            traverse_to_check_ordered_hbt
              A
              (HNode A (1 + max (1 + max h1 h21') h22')
                     (Node A (Triple A
                                     (HNode A 0 (Leaf A))
                                     e2
                                     (HNode A h22' bt22')))) compare =
            TSome (A * A) (e2, t_max')).
  exact (reduce_ordered_hbt_left
           A compare
           (1 + max (1 + max h1 h21') h22')
           (HNode A (1 + max h1 h21')
                  (Node A (Triple A (HNode A h1 bt1) e (HNode A h21' bt21'))))
           e2
           (HNode A h22' bt22')
           t_min' t_max' H).

  (* unfold the tree in preparation *)
  rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H_rotate_left_reduced.
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_node in H_rotate_left_reduced.
  rewrite -> fold_unfold_traverse_to_check_ordered_t in H_rotate_left_reduced.
  rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H_rotate_left_reduced.
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_leaf in H_rotate_left_reduced.

  (* assert inequalites *)

  (* max21' < e2 *)
  assert (H_comp_max21'_e2:
            forall (min21' max21' : A),
              traverse_to_check_ordered_hbt A (HNode A h21' bt21') compare =
              TSome (A * A) (min21', max21') ->
              compare max21' e2 = Lt).
  intros.
  
  (* right reduce the rotated subtree to obtain inequalities *)
  assert (H_rotate_right_reduced:
            traverse_to_check_ordered_hbt
              A
              (HNode A (1 + max (1 + max h1 h21') h22')
                     (Node A
                           (Triple A
                                   (HNode A (1 + max h1 h21')
                                          (Node A (Triple A (HNode A h1 bt1) e (HNode A h21' bt21')))) e2
                                   (HNode A 0 (Leaf A))))) compare = 
            TSome (A * A) (t_min', e2)).
  exact (reduce_ordered_hbt_right
           A compare (1 + max (1 + max h1 h21') h22')
           (HNode A (1 + max h1 h21')
                  (Node A (Triple A (HNode A h1 bt1) e (HNode A h21' bt21'))))
           e2
           (HNode A h22' bt22') t_min' t_max' H).
  (* unfold the reduced tree *)
  rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H_rotate_right_reduced.
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_node in H_rotate_right_reduced.
  rewrite -> fold_unfold_traverse_to_check_ordered_t in H_rotate_right_reduced.
  rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H_rotate_right_reduced.
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_node in H_rotate_right_reduced.
  rewrite -> fold_unfold_traverse_to_check_ordered_t in H_rotate_right_reduced.
  rewrite ->
          (fold_unfold_traverse_to_check_ordered_hbt
            A 0 (Leaf A) compare) in H_rotate_right_reduced.
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_leaf in H_rotate_right_reduced.


  rewrite -> H0 in H_rotate_right_reduced.
  case (traverse_to_check_ordered_hbt A (HNode A h1 bt1) compare)
       as [ | | (min1, max1)].

  (* bt1 is unordered *)
  discriminate.

  (* bt1 is a leaf *)
  case (compare e min21') as [ | | ].
  case (compare max21' e2) as [ | | ].
  reflexivity.

  discriminate.

  discriminate.

  discriminate.

  discriminate.    

  (* bt1 is a node *)
  case (compare max1 e) as [ | | ].
  case (compare e min21') as [ | | ].
  case (compare max21' e2) as [ | | ].
  reflexivity.

  discriminate.

  discriminate.

  discriminate.

  discriminate.    

  discriminate.

  discriminate.

  (* e2 < min22' *)
  assert (H_comp_e2_min22':
            forall (min22' max22' : A),
              traverse_to_check_ordered_hbt A (HNode A h22' bt22') compare =
              TSome (A * A) (min22', max22') ->
              compare e2 min22' = Lt).
  intros.
  rewrite -> H0 in H_rotate_left_reduced.
  case (compare e2 min22') as [ | | ].
  reflexivity.
  discriminate.
  discriminate.

  (* finally, unfold the tree in the goal, and perform the required case analyses *)
  rewrite -> fold_unfold_traverse_to_check_ordered_hbt.
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_node.
  rewrite -> fold_unfold_traverse_to_check_ordered_t.

  case (is_ordered_true_implies_leaf_or_ordered_node
            A compare (HNode A h21' bt21') H_bt21'_ord)
      as [H_bt21'_leaf | H_bt21'_node].

  (* bt21' leaf *)
  + case (is_ordered_true_implies_leaf_or_ordered_node
            A compare (HNode A h22' bt22') H_bt22'_ord)
      as [H_bt22'_leaf | H_bt22'_node].

    (* bt22' leaf *)
    {
      rewrite -> H_bt21'_leaf. 
      rewrite -> H_bt22'_leaf.
      rewrite -> H_bt22'_leaf in H_rotate_left_reduced.
      rewrite -> tsome_x_equal_tsome_y in H_rotate_left_reduced.
      rewrite -> pairwise_equality in H_rotate_left_reduced.
      destruct H_rotate_left_reduced as [_ H'].
      rewrite -> H'.
      exists t_max'.
      reflexivity.
    }

    (* bt22' node *)
    {
      destruct H_bt22'_node as [min22' [max22' H_bt22'_node]].
      rewrite -> H_bt21'_leaf. 
      rewrite -> H_bt22'_node.
      rewrite -> H_bt22'_node in H_rotate_left_reduced.
      case (compare e2 min22') as [ | | ].
      rewrite -> tsome_x_equal_tsome_y in H_rotate_left_reduced.
      rewrite -> pairwise_equality in H_rotate_left_reduced.
      destruct H_rotate_left_reduced as [_ H'].
      rewrite -> H'.
      exists e2.
      reflexivity.

      discriminate.
      
      discriminate.
    }

  (* bt21' node *)
  + (* in this case, we need to use the entire rotated tree *) 
    rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H.
    rewrite -> fold_unfold_traverse_to_check_ordered_bt_node in H.
    rewrite -> fold_unfold_traverse_to_check_ordered_t in H.
    rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H.
    rewrite -> fold_unfold_traverse_to_check_ordered_bt_node in H.
    rewrite -> fold_unfold_traverse_to_check_ordered_t in H.
    
    case (is_ordered_true_implies_leaf_or_ordered_node
            A compare (HNode A h22' bt22') H_bt22'_ord)
      as [H_bt22'_leaf | H_bt22'_node].

    (* bt22' leaf *)
    {
      destruct H_bt21'_node as [min21' [max21' H_bt21'_node]].
      rewrite -> H_bt21'_node. 
      rewrite -> H_bt22'_leaf.
      rewrite -> H_bt21'_node in H.
      rewrite -> H_bt22'_leaf in H.
      case (traverse_to_check_ordered_hbt A (HNode A h1 bt1) compare)
           as [ | | (min1, max1)] eqn : C_bt1.

      (* unordered bt1 *)
      discriminate.

      (* bt1 leaf *)
      case (compare e min21') as [ | | ].
      case (compare max21' e2) as [ | | ].
      rewrite -> tsome_x_equal_tsome_y in H.
      rewrite -> pairwise_equality in H.
      destruct H as [_ H'].
      rewrite -> H'.
      exists min21'.
      reflexivity.
      discriminate.
      discriminate.
      discriminate.
      discriminate.
      
      (* bt1 node *) 
      case (compare max1 e) as [ | | ].
      case (compare e min21') as [ | | ].
      rewrite -> (H_comp_max21'_e2 min21' max21' H_bt21'_node) in H.
      rewrite -> (H_comp_max21'_e2 min21' max21' H_bt21'_node).
      rewrite -> tsome_x_equal_tsome_y in H.
      rewrite -> pairwise_equality in H.
      destruct H as [_ H'].
      rewrite -> H'.
      exists min21'.
      reflexivity.
      discriminate.
      discriminate.
      discriminate.
      discriminate.
    } 

    (* bt22' node *)
    {
      destruct H_bt21'_node as [min21' [max21' H_bt21'_node]].
      destruct H_bt22'_node as [min22' [max22' H_bt22'_node]].
      rewrite -> H_bt21'_node. 
      rewrite -> H_bt22'_node.
      rewrite -> H_bt21'_node in H.
      rewrite -> H_bt22'_node in H.

      case (traverse_to_check_ordered_hbt A (HNode A h1 bt1) compare)
        as [ | | (min1, max1)] eqn : C_bt1.

      (* bt1 unordered *)
      discriminate.

      (* bt1 leaf *)
      case (compare e min21') as [ | | ].
      rewrite -> (H_comp_max21'_e2  min21' max21' H_bt21'_node) in H.
      rewrite -> (H_comp_e2_min22'  min22' max22' H_bt22'_node) in H.
      rewrite -> (H_comp_e2_min22'  min22' max22' H_bt22'_node).
      rewrite -> (H_comp_max21'_e2  min21' max21' H_bt21'_node).
      rewrite -> tsome_x_equal_tsome_y in H.
      rewrite -> pairwise_equality in H.
      destruct H as [_ H'].
      rewrite -> H'.
      exists min21'.
      reflexivity.
      discriminate.
      discriminate.

      (* bt1 node *) 
      case (compare max1 e) as [ | | ].
      case (compare e min21') as [ | | ].
      rewrite -> (H_comp_max21'_e2 min21' max21' H_bt21'_node) in H.
      rewrite -> (H_comp_e2_min22'  min22' max22' H_bt22'_node) in H.
      rewrite -> (H_comp_e2_min22'  min22' max22' H_bt22'_node).      
      rewrite -> (H_comp_max21'_e2 min21' max21' H_bt21'_node).
      rewrite -> tsome_x_equal_tsome_y in H.
      rewrite -> pairwise_equality in H.
      destruct H as [_ H'].
      rewrite -> H'.
      exists min21'.
      reflexivity.
      discriminate.
      discriminate.
      discriminate.
      discriminate.
    }
Qed.
  
(** The lemmas [rotate_left_2_impossible_case_1] and 
[rotate_left_2_impossible_case_2] concern the two sub-cases which arise in case of 
the <<rotate_left_2>> operation, and show that if an insertion operation led to
a <<rotate_left_2>> operation, then the subtree on which the insertion operation
was performed cannot be a leaf *)
Lemma rotate_left_2_impossible_case_1:
  forall (A :Type)
         (compare : A -> A -> element_comparison)
         (x : A) 
         (h2 : nat)
         (bt2 : binary_tree A)
         (h2' h21' h22' : nat)
         (bt21' bt22' : binary_tree A)
         (e2 : A),
    insert_hbt_helper A compare x (HNode A h2 bt2) =
    Some
      (HNode A h2'
             (Node A (Triple A (HNode A h21' bt21') e2 (HNode A h22' bt22')))) ->
    (h21' + 1 =n= h22') = true ->
    bt2 <> Leaf A.
Proof.
  intros.

  case bt2 as [ | t2].

  (* leaf *)
  rewrite -> fold_unfold_insert_hbt_helper in H.
  rewrite -> fold_unfold_insert_bt_helper_leaf in H.
  rewrite -> some_x_equal_some_y in H.
  apply beq_nat_true in H0.
  rewrite <- H0 in H.
  case h21' as [ | h21''].
  
  rewrite -> plus_O_n in H.
  discriminate.

  discriminate.

  (* node *)
  unfold not.
  intro H'.
  discriminate.
Qed.

Lemma rotate_left_2_impossible_case_2:
  forall (A : Type)
         (compare : A -> A -> element_comparison)
         (x : A)
         (h2 : nat)
         (bt2 : binary_tree A)
         (h2' h21' h22' : nat)
         (e2 : A) 
         (bt21' bt22' : binary_tree A)
         (h1 : nat)
         (bt1 : binary_tree A),
    is_sound_hbt A (HNode A h2 bt2) = true ->
    is_balanced_hbt A (HNode A h2 bt2) = true ->
    insert_hbt_helper A compare x (HNode A h2 bt2) =
    Some
      (HNode A h2'
             (Node A (Triple A (HNode A h21' bt21') e2 (HNode A h22' bt22')))) ->
    (h21' =n= h22') = true ->
    compare_int h2' (2 + project_height_hbt A (HNode A h1 bt1)) = Eq -> 
    bt2 <> Leaf A.
Proof.
  intros.

  assert (H_hbt_ret_sound:
            is_sound_hbt A (HNode A h2' (Node A (Triple A
                                                        (HNode A h21' bt21')
                                                        e2
                                                        (HNode A h22' bt22')))) =
            true).
  destruct (insertion_preserves_soundness A compare x) as [H_hbt _].

  assert (H_sound:
            is_sound_hbt
              A
              (HNode A h2' (Node A (Triple A
                                           (HNode A h21' bt21')
                                           e2
                                           (HNode A h22' bt22')))) = true).
  exact (H_hbt
           (HNode A h2 bt2)
           (HNode A h2' (Node A (Triple A
                                        (HNode A h21' bt21')
                                        e2
                                        (HNode A h22' bt22')))) H H1).
  
  exact H_sound.

  assert (H_h2'_h21'_h22' :
            1 + max h21' h22' = h2').
  symmetry.
  exact (relate_heights A h2' h21' bt21' e2 h22' bt22' H_hbt_ret_sound).
  
  (* next, show that h11' cannot be 0 *)
  apply beq_nat_true in H2.
  apply (EqdepFacts.internal_eq_sym_internal) in H2.
  destruct (non_zero_height A h21' h22' h2' h1 bt1 H2 H_h2'_h21'_h22' H3)
    as [n H_h22'_non_zero].
  rewrite <- H2 in H1.
  rewrite -> H_h22'_non_zero in H1.

  (* now use induction *)
  case bt2 as [ | t1].

  rewrite -> fold_unfold_insert_hbt_helper in H1.
  rewrite -> fold_unfold_insert_bt_helper_leaf in H1.
  rewrite -> some_x_equal_some_y in H1.
  discriminate.

  discriminate.
Qed.

(** Lemma to show that post the insertion of some element <<x>> in a tree which 
unbalances the tree, 
- the minimum element of a tree subjected to a <<rotate_left_2>> operation is either <<x>> or the minimum element of the original tree 
- the maximum element of a tree subjected to a <<rotate_left_2>> operation is either <<x>> or the maximum element of the original tree *)
Lemma rotate_left_2_min_max:
  forall (A : Type)
         (compare : A -> A -> element_comparison)
         (h1 h21' h22' : nat)
         (bt1 bt21' bt22' : binary_tree A)
         (e e2 : A)
         (hbt2 : heightened_binary_tree A)
         (t_min' t_max' t_min t_max min2 max2 x : A),         
    traverse_to_check_ordered_hbt
      A
      (HNode A (1 + max (1 + max h1 h21') h22')
             (Node A
                   (Triple A
                           (HNode A (1 + max h1 h21')
                                  (Node A (Triple A
                                                  (HNode A h1 bt1)
                                                  e
                                                  (HNode A h21' bt21'))))
                           e2
                           (HNode A h22' bt22')))) compare = 
    TSome (A * A) (t_min', t_max') ->
    traverse_to_check_ordered_t A (Triple A (HNode A h1 bt1) e hbt2) compare =
    TSome (A * A) (t_min, t_max) ->
    traverse_to_check_ordered_hbt A hbt2 compare = TSome (A * A) (min2, max2) ->     
    t_max' = x \/ t_max' = max2 ->
    (t_max' = x \/ t_max' = t_max) /\ (t_min' = x \/ t_min' = t_min).
Proof.
  intros.
  split. 

  (* min *)
  exact (rotate_left_max
           A compare
           h1 bt1 e hbt2
           t_min t_max min2 max2 t_max' x H0 H1 H2).

  (* max *)

  (* first, right reduce rotated tree *)
  assert (H_rotate_right_reduced:
            traverse_to_check_ordered_hbt
              A
              (HNode A (1 + max (1 + max h1 h21') h22')
                     (Node A
                           (Triple A
                                   (HNode A (1 + max h1 h21')
                                          (Node A (Triple A (HNode A h1 bt1) e (HNode A h21' bt21')))) e2
                                   (HNode A 0 (Leaf A))))) compare = 
            TSome (A * A) (t_min', e2)).
  exact (reduce_ordered_hbt_right
           A compare
           (1 + max (1 + max h1 h21') h22')
           (HNode A (1 + max h1 h21')
                  (Node A (Triple A (HNode A h1 bt1) e (HNode A h21' bt21'))))
           e2
           (HNode A h22' bt22')
           t_min' t_max' H).

  (* next, right reduce original tree *)
  assert (H_org_tree_reduced:
            traverse_to_check_ordered_hbt
              A
              (HNode A (1 + max h1 (project_height_hbt A hbt2))
                     (Node A (Triple A (HNode A h1 bt1) e (HNode A 0 (Leaf A))))) compare =
            TSome (A * A) (t_min, e)).
  exact (reduce_ordered_hbt_right
           A compare (1 + max h1 (project_height_hbt A hbt2))
           (HNode A h1 bt1) e hbt2 t_min t_max H0).

  apply or_intror.
  exact (rotate_left_min
           A compare
           (1 + max (1 + max h1 h21') h22')
           (1 + max h1 h21')
           (HNode A h1 bt1) e (HNode A h21' bt21')
           e2 t_min' (1 + max h1 (project_height_hbt A hbt2)) t_min
           H_rotate_right_reduced
           H_org_tree_reduced).
Qed.

(* ***** *)

(* ********** *)

(* ********** End of ordered_helper.v ********** *)