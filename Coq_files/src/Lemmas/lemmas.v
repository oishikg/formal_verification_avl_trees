(* ********** Imports ********** *)
Require Import Hbt.Implementation.hbt.
Require Export Hbt.Implementation.hbt.

(* ***** Section 5.4: Lemmas concerning soundness ***** *)

(* Given a triple that is sound, its binary trees should also be sound *)

Lemma triple_sound_implies_hbts_sound:
  forall (A : Type)
         (h_hbt : nat)
         (hbt1 : heightened_binary_tree A)
         (e : A)
         (hbt2 : heightened_binary_tree A),
    is_sound_hbt A (HNode A h_hbt (Node A (Triple A hbt1 e hbt2))) = true ->
    is_sound_hbt A hbt1 = true /\ is_sound_hbt A hbt2 = true.
Proof.
  intros A h_hbt hbt1 e hbt2 H_t.
  split.
  unfold is_sound_hbt in H_t.
  rewrite ->
          (unfold_traverse_to_check_soundness_hbt
             A
             h_hbt
             (Node A (Triple A hbt1 e hbt2))) in H_t.
  rewrite ->
          (unfold_traverse_to_check_soundness_bt_node
             A
             (Triple A hbt1 e hbt2)) in H_t.
  rewrite -> (unfold_traverse_to_check_soundness_t A hbt1 hbt2 e) in H_t.
  case (traverse_to_check_soundness_hbt A hbt1) as [ret_h1 | ] eqn : C_sound_hbt1.
  unfold is_sound_hbt.
  rewrite -> C_sound_hbt1.
  reflexivity.

  discriminate.

  unfold is_sound_hbt in H_t.
  rewrite ->
          (unfold_traverse_to_check_soundness_hbt
             A
             h_hbt
             (Node A (Triple A hbt1 e hbt2))) in H_t.
  rewrite ->
          (unfold_traverse_to_check_soundness_bt_node
             A
             (Triple A hbt1 e hbt2)) in H_t.
  rewrite -> (unfold_traverse_to_check_soundness_t A hbt1 hbt2 e) in H_t.
  case (traverse_to_check_soundness_hbt A hbt1) as [ret_h1 | ] eqn : C_sound_hbt1.
  case (traverse_to_check_soundness_hbt A hbt2) as [ret_h2 | ] eqn : C_sound_hbt2.
  
  unfold is_sound_hbt.
  rewrite -> C_sound_hbt2.
  reflexivity.

  discriminate.

  discriminate.
Qed.

(* If the helper function to check soundness for hbts returns some hbt, then 
 * the helper function to check soundness for bts should give the same hbt *)
Lemma traverse_to_check_soundness_hbt_bt_same:
  forall (A : Type)
         (h h_hbt : nat)
         (bt : binary_tree A),
    traverse_to_check_soundness_hbt A (HNode A h bt) = Some h_hbt ->
    traverse_to_check_soundness_bt A bt = Some h_hbt.
Proof.
  intros A h h_hbt bt H.
  rewrite -> (unfold_traverse_to_check_soundness_hbt A h bt) in H.
  case (traverse_to_check_soundness_bt A bt) as [h_ret | ]  eqn : C_soundness.
  case (h_ret =n= h) as [ | ] eqn : C_equal_heights.
  Check (beq_nat_true).
  apply (beq_nat_true h_ret h) in C_equal_heights.
  rewrite <- C_equal_heights in H.
  exact H.

  discriminate.

  discriminate.
Qed.

(* If the helper function to check soundness for bts returns some hbt, then 
 * the helper function to check soundness for ts should give the same hbt *)
Lemma traverse_to_check_soundness_bt_t_same:
  forall (A : Type)
         (h_hbt : nat)
         (t : triple A),
    traverse_to_check_soundness_bt A (Node A t) = Some h_hbt ->
    traverse_to_check_soundness_t A t = Some h_hbt.
Proof.
  intros A h_hbt t H.
  rewrite -> (unfold_traverse_to_check_soundness_bt_node A t) in H.
  case (traverse_to_check_soundness_t A t) as [h_ret | ] eqn : C_h.
  exact H.
  discriminate.
Qed.

(* This is an important lemma: it provides the condition for which sound hbts 
 * imply soundness of a triple that they are part of *)
Lemma hbts_sound_implies_triple_sound_weak:
    forall (A : Type)
           (h_hbt : nat)
           (hbt1 : heightened_binary_tree A)
           (e : A)
           (hbt2 : heightened_binary_tree A),
      is_sound_hbt A hbt1 = true ->
      is_sound_hbt A hbt2 = true ->
      h_hbt = 1 + max (project_height_hbt A hbt1) (project_height_hbt A hbt2) ->
      is_sound_hbt A (HNode A h_hbt (Node A (Triple A hbt1 e hbt2))) = true.
Proof.      
  intros A h_hbt hbt1 e hbt2 H_hbt1 H_hbt2 H_h_hbt.
  unfold is_sound_hbt.
  rewrite ->
          (unfold_traverse_to_check_soundness_hbt
             A
             h_hbt
             (Node A (Triple A hbt1 e hbt2))).
  rewrite ->
          (unfold_traverse_to_check_soundness_bt_node
             A
             (Triple A hbt1 e hbt2)).
  rewrite -> (unfold_traverse_to_check_soundness_t A hbt1 hbt2 e).
  unfold is_sound_hbt in H_hbt1.

  case (traverse_to_check_soundness_hbt A hbt1) as [h1_ret | ] eqn : C_check_hbt1.
  case (traverse_to_check_soundness_hbt A hbt2) as [h2_ret | ] eqn : C_check_hbt2.
  (* the proof shouldn't be too hard from here on; return to this later *)
Admitted.

(* ***** *)

(* ***** Section 5.5: Balancedness lemmas ***** *)

(* Given a balanced triple, its constituent hbts should also be balanced *)
Lemma triple_balanced_implies_hbts_balanced:
  forall (A : Type)
         (h_hbt : nat)
         (hbt1 : heightened_binary_tree A)
         (e : A)
         (hbt2 : heightened_binary_tree A),
    is_balanced_hbt A (HNode A h_hbt (Node A (Triple A hbt1 e hbt2))) = true ->
    is_balanced_hbt A hbt1 = true /\ is_balanced_hbt A hbt2 = true.
Proof.
  (* same structure as above, write later *)
Admitted.

(* If the helper function to check the balancedness of an hbt returns some hbt,
 * then the helper function to check the balancedness of the bt returns the same
 * hbt *)
Lemma traverse_to_check_balanced_hbt_bt_same:
  forall (A : Type)
         (h h_hbt : nat)
         (bt : binary_tree A),
    traverse_to_check_balanced_hbt A (HNode A h bt) = Some h_hbt ->
    traverse_to_check_balanced_bt A bt = Some h_hbt.
Proof.
  intros A h h_hbt bt H.
  rewrite -> (unfold_traverse_to_check_balanced_hbt A h bt) in H.  
  case (traverse_to_check_balanced_bt A bt) as [bt_ret | ] eqn : C_check_bal.
  exact H.
  discriminate.
Qed.

(* If the helper function to check the balancedness of an bt returns some hbt,
 * then the helper function to check the balancedness of the t returns the same
 * hbt *)
Lemma traverse_to_check_balanced_bt_t_same:
  forall (A : Type)
         (h_hbt : nat)
         (t : triple A),
    traverse_to_check_balanced_bt A (Node A t) = Some h_hbt ->
    traverse_to_check_balanced_t A t = Some h_hbt.
Proof.
  intros A h_hbt t H.
  rewrite -> (unfold_traverse_to_check_balanced_bt_node A t) in H.
  case (traverse_to_check_balanced_t A t) as [h_ret | ] eqn : C_h.
  exact H.
  discriminate.
Qed.

(* The relationship between the helper functions for soundness and balancedness. The
 * statement of the proof allows us to use the heightened_binary_tree_mutual_induction
 * principle *)
Lemma relating_soundness_and_balancedness:
  forall (A : Type),
    (forall (hbt : heightened_binary_tree A)
            (h_sound h_bal : nat),
        traverse_to_check_soundness_hbt A hbt = Some h_sound ->
        traverse_to_check_balanced_hbt A hbt = Some h_bal ->
        h_sound = h_bal)
    /\
    (forall (bt : binary_tree A)
            (h_sound h_bal : nat),
        traverse_to_check_soundness_bt A bt = Some h_sound ->
        traverse_to_check_balanced_bt A bt = Some h_bal ->
        h_sound = h_bal)
    /\
    (forall (t : triple A)
            (h_sound h_bal : nat),
        traverse_to_check_soundness_t A t = Some h_sound ->
        traverse_to_check_balanced_t A t = Some h_bal ->
        h_sound = h_bal).
Proof.           
  intro A.
  apply heightened_binary_tree_mutual_induction.

  - intros h bt H_inductive_bt h_sound h_bal H_sound_hbt H_balanced_hbt.
    Check (traverse_to_check_soundness_hbt_bt_same).
    exact (H_inductive_bt h_sound h_bal
                          (traverse_to_check_soundness_hbt_bt_same A h h_sound bt H_sound_hbt)
                          (traverse_to_check_balanced_hbt_bt_same A h h_bal bt
                                                            H_balanced_hbt)).

  - intros h_sound h_bal H_sound_leaf H_balanced_leaf.
    rewrite -> (unfold_traverse_to_check_soundness_bt_leaf A) in H_sound_leaf.
    rewrite -> (unfold_traverse_to_check_balanced_bt_leaf A) in H_balanced_leaf.    
    rewrite -> (some_x_equal_some_y nat 0 h_sound) in H_sound_leaf.
    rewrite -> (some_x_equal_some_y nat 0 h_bal) in H_balanced_leaf.    
    rewrite <- H_sound_leaf.
    rewrite <- H_balanced_leaf.
    reflexivity.

  - intros t H_inductive_t h_sound h_bal H_sound_bt H_balanced_bt.
    exact (H_inductive_t h_sound h_bal
                         (traverse_to_check_soundness_bt_t_same A h_sound t H_sound_bt)
                         (traverse_to_check_balanced_bt_t_same A h_bal t H_balanced_bt)).

  - intros hbt1 H_inductive_hbt1 e hbt2 H_inductive_hbt2
           h_sound h_bal H_sound_t H_balanced_t.
    rewrite -> (unfold_traverse_to_check_soundness_t A hbt1 hbt2 e) in H_sound_t.
    rewrite -> (unfold_traverse_to_check_balanced_t A hbt1 hbt2 e) in H_balanced_t. 
    case (traverse_to_check_soundness_hbt A hbt1)
      as [h_sound_sub_1 | ] eqn : C_sound_hbt1.
    case (traverse_to_check_soundness_hbt A hbt2)
      as [h_sound_sub_2 | ] eqn : C_sound_hbt2.
    case (traverse_to_check_balanced_hbt A hbt1)
      as [h_balanced_sub_1 | ] eqn : C_balanced_hbt1.
    case (traverse_to_check_balanced_hbt A hbt2)
      as [h_balanced_sub_2 | ] eqn : C_balanced_hbt2.
    assert (H_sound_sub1_equal:
              (Some h_sound_sub_1 = Some h_sound_sub_1)).
    reflexivity.
    assert (H_balanced_sub1_equal:
              Some h_balanced_sub_1 = Some h_balanced_sub_1).
    reflexivity.
    assert (H_sub1_equals :
              h_sound_sub_1 = h_balanced_sub_1).
    exact (H_inductive_hbt1 h_sound_sub_1 h_balanced_sub_1
                            H_sound_sub1_equal
                            H_balanced_sub1_equal).
    assert (H_sound_sub2_equal:
              (Some h_sound_sub_2 = Some h_sound_sub_2)).
    reflexivity.
    assert (H_balanced_sub2_equal:
              Some h_balanced_sub_2 = Some h_balanced_sub_2).
    reflexivity.
    assert (H_sub2_equals :
              h_sound_sub_2 = h_balanced_sub_2).
    exact (H_inductive_hbt2 h_sound_sub_2 h_balanced_sub_2
                            H_sound_sub2_equal
                            H_balanced_sub2_equal).
    apply (some_x_equal_some_y
             nat
             (1 + max h_sound_sub_1 h_sound_sub_2)
             h_sound) in H_sound_t.
    case (differ_by_one h_balanced_sub_1 h_balanced_sub_2) as [ | ] eqn : C_diff_1.
    apply (some_x_equal_some_y
             nat
             (1 + max h_balanced_sub_1 h_balanced_sub_2)
             h_bal) in H_balanced_t.
    rewrite <- H_sound_t.
    rewrite <- H_balanced_t.
    rewrite <- H_sub1_equals.
    rewrite <- H_sub2_equals.
    reflexivity.

    discriminate.

    discriminate.

    discriminate.

    discriminate.

    discriminate.
Qed.

(* This lemma relates the projected height of an hbt to that returned by the helper
 * function for soundness *)
Lemma relating_soundness_and_projection:
  forall (A : Type)
         (hbt : heightened_binary_tree A)
         (h_ret : nat),
    traverse_to_check_soundness_hbt A hbt = Some h_ret ->
    project_height_hbt A hbt = h_ret.
Proof.
  intros A hbt h H_traverse_sound.
  induction hbt as [h_given bt_given].
  unfold project_height_hbt.
  rewrite -> (unfold_traverse_to_check_soundness_hbt A h_given bt_given)
    in H_traverse_sound.
  case (traverse_to_check_soundness_bt A bt_given) as [h_ret | ] eqn : C_check_bt.
  case (h_ret =n= h_given) as [ | ] eqn : C_equal_heights.
  apply (beq_nat_true h_ret h_given) in C_equal_heights.  
  apply (some_x_equal_some_y nat h_given h) in H_traverse_sound.
  exact H_traverse_sound.

  discriminate.

  discriminate.
Qed.

(* Essential lemma to related height differences between 2 trees and the 
 * differ_by_one defintion *)  
Lemma relating_compare_int_and_differ_by_one:
  forall (ha hb : nat),
    ((compare_int (ha - hb) 2 = Lt)
    \/
    (compare_int (hb - ha) 2 = Lt))
    ->
    differ_by_one ha hb = true.
Proof.
  intros ha hb [H_ab | H_ba].
  
  - unfold compare_int in H_ab.
    case (ha - hb) as [ | hd] eqn : C_height_diff.
    
    + unfold differ_by_one.
      apply (diff_equal_0_implies_equal ha hb) in C_height_diff.
      rewrite -> C_height_diff.
      Check (beq_nat_refl hb).
      rewrite <- (beq_nat_refl hb).
      Check (orb_true_r ((hb =n= hb + 1) || (hb =n= hb + 1))).
      exact (orb_true_r ((hb =n= hb + 1) || (hb =n= hb + 1))).
    
    + case hd as [ | hd'] eqn : C_height_diff_succ.
      unfold differ_by_one.
      Check (diff_equal_1_implies_greater_by_1).
      apply (diff_equal_1_implies_greater_by_1 ha hb) in C_height_diff.
      rewrite -> C_height_diff.
      rewrite <- (beq_nat_refl (hb + 1)).
      Search (true || _ = _).
      exact (orb_true_l ((hb =n= hb + 1 + 1) || (hb =n= hb + 1))).
      
      rewrite -> (unfold_ltb_Sn_Sm (S hd') 1) in H_ab.
      rewrite -> (unfold_ltb_Sn_Sm hd' 0) in H_ab.
      case hd' as [ | hd''].
      rewrite -> (unfold_ltb_0_0) in H_ab.
      unfold beq_nat in H_ab.
      discriminate.

      rewrite -> (unfold_ltb_Sn_0 hd'') in H_ab.
      unfold beq_nat in H_ab.
      discriminate.
      
  - unfold compare_int in H_ba.
    case (hb - ha) as [ | hd] eqn : C_height_diff.
    
    + unfold differ_by_one.
      apply (diff_equal_0_implies_equal hb ha) in C_height_diff.
      rewrite -> C_height_diff.
      rewrite <- (beq_nat_refl ha).
      Check (orb_true_r ((hb =n= ha + 1) || (ha =n= ha + 1))).
      exact (orb_true_r ((ha =n= ha + 1) || (ha =n= ha + 1))).
    
    + case hd as [ | hd'] eqn : C_height_diff_succ.
      unfold differ_by_one.
      Check (diff_equal_1_implies_greater_by_1).
      apply (diff_equal_1_implies_greater_by_1 hb ha) in C_height_diff.
      rewrite -> C_height_diff.
      rewrite <- (beq_nat_refl (ha + 1)).
      Search (true || _ = _).
      rewrite -> (orb_true_r (ha =n= ha + 1 + 1)).
      rewrite -> (orb_true_l (ha + 1 =n= ha)).
      reflexivity.
      
      rewrite -> (unfold_ltb_Sn_Sm (S hd') 1) in H_ba.
      rewrite -> (unfold_ltb_Sn_Sm hd' 0) in H_ba.
      case hd' as [ | hd''].
      rewrite -> (unfold_ltb_0_0) in H_ba.
      unfold beq_nat in H_ba.
      discriminate.

      rewrite -> (unfold_ltb_Sn_0 hd'') in H_ba.
      unfold beq_nat in H_ba.
      discriminate.
Qed.

(* The most important lemma for balancedness: it provides the conditions for which
 * balanced hbts imply a balanced triple *)
Lemma hbts_balanced_implies_triple_balanced_weak:
    forall (A : Type)
           (h_hbt : nat)
           (hbt1 : heightened_binary_tree A)
           (e : A)
           (hbt2 : heightened_binary_tree A),
      is_balanced_hbt A hbt1 = true ->
      is_balanced_hbt A hbt2 = true ->
      is_sound_hbt A hbt1 = true ->
      is_sound_hbt A hbt2 = true -> 
      ((compare_int ((project_height_hbt A hbt1) - (project_height_hbt A hbt2))
                   2 = Lt)
      \/
      (compare_int ((project_height_hbt A hbt2) - (project_height_hbt A hbt1))
                   2 = Lt)) ->
      is_balanced_hbt A (HNode A h_hbt (Node A (Triple A hbt1 e hbt2))) = true.
Proof.
  intros A h_hbt hbt1 e hbt2 H_bal_hbt1 H_bal_hbt2
         H_sound_hbt1 H_sound_hbt2 H_height_diff.
  unfold is_balanced_hbt.
  rewrite ->
          (unfold_traverse_to_check_balanced_hbt
             A h_hbt
             (Node A (Triple A hbt1 e hbt2))).
  rewrite ->
          (unfold_traverse_to_check_balanced_bt_node
             A
             (Triple A hbt1 e hbt2)).
  rewrite -> (unfold_traverse_to_check_balanced_t A hbt1 hbt2 e).
  unfold is_balanced_hbt in H_bal_hbt1.
  unfold is_balanced_hbt in H_bal_hbt2.
  unfold is_sound_hbt in H_sound_hbt1.
  unfold is_sound_hbt in H_sound_hbt2.
  
  case (traverse_to_check_balanced_hbt A hbt1) as [h1_ret_bal | ] eqn : C_bal_hbt1.
  case (traverse_to_check_balanced_hbt A hbt2) as [h2_ret_bal | ] eqn : C_bal_hbt2.
  case (traverse_to_check_soundness_hbt A hbt1)
    as [h1_ret_sound | ] eqn : C_sound_hbt1.
  case (traverse_to_check_soundness_hbt A hbt2)
    as [h2_ret_sound | ] eqn : C_sound_hbt2.
  
  - destruct (relating_soundness_and_balancedness A) as [H_relate_sound_bal_hbt _].
    Check (H_relate_sound_bal_hbt hbt1 h1_ret_sound h1_ret_bal
                                  C_sound_hbt1 C_bal_hbt1).
    assert (H_h1_ret_sound_equals_h1_ret_bal :
              h1_ret_sound = h1_ret_bal).
    exact (H_relate_sound_bal_hbt hbt1 h1_ret_sound h1_ret_bal
                                  C_sound_hbt1 C_bal_hbt1).
    assert (H_h2_ret_sound_equals_h2_ret_bal :
              h2_ret_sound = h2_ret_bal).
    exact (H_relate_sound_bal_hbt hbt2 h2_ret_sound h2_ret_bal
                                  C_sound_hbt2 C_bal_hbt2).
    assert (H_project_height_hbt1_equals_h1_ret_sound :
              project_height_hbt A hbt1 = h1_ret_sound).
    exact (relating_soundness_and_projection A hbt1 h1_ret_sound C_sound_hbt1).
    assert (H_project_height_hbt2_equals_h2_ret_sound :
              project_height_hbt A hbt2 = h2_ret_sound).
    exact (relating_soundness_and_projection A hbt2 h2_ret_sound C_sound_hbt2).
    rewrite -> H_h1_ret_sound_equals_h1_ret_bal
      in H_project_height_hbt1_equals_h1_ret_sound.
    rewrite -> H_h2_ret_sound_equals_h2_ret_bal
      in H_project_height_hbt2_equals_h2_ret_sound.
    rewrite -> H_project_height_hbt1_equals_h1_ret_sound in H_height_diff.
    rewrite -> H_project_height_hbt2_equals_h2_ret_sound in H_height_diff.
    Check (relating_compare_int_and_differ_by_one h1_ret_bal h2_ret_bal
                                                  H_height_diff).
    rewrite ->
            (relating_compare_int_and_differ_by_one h1_ret_bal h2_ret_bal
                                                    H_height_diff).
    reflexivity.

  - discriminate.

  - discriminate.

  - discriminate.

  - discriminate.
Qed.

(* ***** *)

(* ***** Section 5.6: Lemmas for orderedness ***** *)
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
  rewrite -> unfold_traverse_to_check_ordered_hbt in H.
  rewrite -> unfold_traverse_to_check_ordered_bt_node in H.
  rewrite -> unfold_traverse_to_check_ordered_t in H.
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
  rewrite -> (unfold_traverse_to_check_ordered_hbt A h bt compare) in H_hbt.
  case bt as [ | t] eqn : C_bt.
  reflexivity.
  rewrite -> (unfold_traverse_to_check_ordered_bt_node A t compare) in H_hbt.
  case t as [hbt1 e hbt2].
  rewrite -> (unfold_traverse_to_check_ordered_t A hbt1 e hbt2 compare) in H_hbt. 
  case (traverse_to_check_ordered_hbt A hbt1 compare) as [ | | (min1, max1)] eqn : C_ord_hbt1.
  discriminate.
  case (traverse_to_check_ordered_hbt A hbt2 compare) as [ | | (min2, max2)] eqn : C_ord_hbt2.
  discriminate.
  discriminate.
  case (compare e min2) as [ | | ] eqn : C_comp_e_min2.
  discriminate.
  discriminate.
  discriminate.
  case (compare max1 e) as [ | | ] eqn : C_comp_e_min1.
  case (traverse_to_check_ordered_hbt A hbt2 compare) as [ | | (min2, max2)] eqn : C_ord_hbt2.
  discriminate.
  discriminate.
  case (compare e min2) as [ | | ] eqn : C_comp_e_min2.
  discriminate.
  discriminate.
  discriminate.
  discriminate.
  discriminate.

  rewrite -> H_form_of_bt in H_insert.
  rewrite -> (unfold_insert_hbt_helper A compare x h (Leaf A)) in H_insert.
  rewrite -> (unfold_insert_bt_helper_leaf A compare x h) in H_insert.
  rewrite ->  some_x_equal_some_y in H_insert.
  rewrite <- H_insert in H_hbt'.
  rewrite ->
          (unfold_traverse_to_check_ordered_hbt
             A
             1
             (Node A (Triple A (HNode A 0 (Leaf A)) x (HNode A 0 (Leaf A))))
             compare) in H_hbt'.
  rewrite ->
          (unfold_traverse_to_check_ordered_bt_node
             A
             (Triple A (HNode A 0 (Leaf A)) x (HNode A 0 (Leaf A)))) in H_hbt'.
  rewrite ->
          (unfold_traverse_to_check_ordered_t
             A
             (HNode A 0 (Leaf A))
             x
             (HNode A 0 (Leaf A))) in H_hbt'.
  rewrite -> (unfold_traverse_to_check_ordered_hbt A 0 (Leaf A) compare) in H_hbt'.
  rewrite -> (unfold_traverse_to_check_ordered_bt_leaf A compare) in H_hbt'.
  rewrite -> (tsome_x_equal_tsome_y (A * A) (x, x) (min', max')) in H_hbt'.
  apply (pairwise_equality A x x min' max') in H_hbt'.
  destruct H_hbt' as [G1 G2].
  split.

  rewrite -> G1.
  reflexivity.
  
  rewrite -> G2.
  reflexivity.
Qed.


Lemma insertion_impossible_case:
  forall (A : Type)
         (compare : A -> A -> element_comparison)
         (x : A) 
         (hbt0 : heightened_binary_tree A)
         (hbt'' : heightened_binary_tree A),
    insert_hbt_helper A compare x hbt0 = Some hbt'' ->
    traverse_to_check_ordered_hbt A hbt'' compare <> TNone (A * A).
Proof.                                                                    
    intros A compare x  hbt0 hbt'' H_ins.
    unfold not.
    induction hbt'' as [h'' bt''].
    rewrite -> (unfold_traverse_to_check_ordered_hbt A h'' bt'' compare).
    case bt'' as [ | t''].
    
    induction hbt0 as [h0 bt0].
    rewrite -> (unfold_insert_hbt_helper A compare x h0 bt0) in H_ins.
    case bt0 as [ | t0].
    rewrite -> (unfold_insert_bt_helper_leaf A compare) in H_ins.
    discriminate.
    induction t0 as [ hbt01 e0 hbt02].
    rewrite -> (unfold_insert_bt_helper_node A compare x h0 (Triple A hbt01 e0 hbt02))
      in H_ins.
    rewrite -> (unfold_insert_t_helper A compare x h0 hbt01 e0 hbt02) in H_ins.
    case (compare x e0) as [ | | ] eqn : C_comp_x_e0.
    case (insert_hbt_helper A compare x hbt01) as [ hbt01_ret | ]  eqn : C_ins_hbt01.
    induction hbt01_ret as [h01_ret bt_01_ret].
    case (compare_int (h01_ret - project_height_hbt A hbt02) 2)
         as [ | | ] eqn : C_h_diff.
    rewrite -> (some_x_equal_some_y
                  (heightened_binary_tree A)
                  (HNode A (1 + max h01_ret (project_height_hbt A hbt02))
                         (Node A (Triple A (HNode A h01_ret bt_01_ret) e0 hbt02)))
                  (HNode A h'' (Leaf A))) in H_ins.
    discriminate.
    unfold rotate_right_hbt in H_ins.
    induction hbt02 as [h02 bt02]. 
    unfold rotate_right_bt in H_ins.
    case (bt_01_ret) as [ t01 | ].
    discriminate.
    induction t as [ hbt011 e01 hbt012].
    induction hbt011 as [h011 bt011].
    induction hbt012 as [h012 bt012].
    case (h011 + 1 =n= h012) as [ | ].
    case bt012 as [ | t012].
    discriminate.
    induction t012 as [ hbt0121 e012 hbt0122 ].
    induction hbt0121 as [ h0121 bt0121 ].
    induction hbt0122 as [ h0122 bt0122 ].
    rewrite -> some_x_equal_some_y in H_ins.
    discriminate.
    case (h012 + 1 =n= h011) as [ | ].
    rewrite -> some_x_equal_some_y in H_ins.
    discriminate.
    discriminate.
    discriminate.
    discriminate.
    discriminate.
    
    case (insert_hbt_helper A compare x hbt02) as [hbt02_ret | ].
    induction hbt02_ret as [h02_ret bt02_ret].
    case (compare_int (h02_ret - project_height_hbt A hbt01) 2) as [ | | ].
    rewrite -> some_x_equal_some_y in H_ins.
    discriminate.
    unfold rotate_left_hbt in H_ins.
    induction hbt01 as [h01 bt01].
    unfold rotate_left_bt in H_ins.
    case bt02_ret as [ | t02].
    discriminate.
    induction t02 as [hbt021 e2 hbt022].
    induction hbt021 as [h021 bt021].
    induction hbt022 as [h022 bt022].
    case (h022 + 1 =n= h021) as [ | ].
    case bt021 as [ | t021 ].
    discriminate.
    induction t021 as [hbt0211 e21 hbt0212].
    induction hbt0211 as [h0211 bt0211].
    induction hbt0212 as [h0212 bt0212].
    rewrite -> some_x_equal_some_y in H_ins.
    discriminate.
    case (h021 + 1 =n= h022) as [ | ].
    rewrite -> some_x_equal_some_y in H_ins.
    discriminate.
    discriminate.
    discriminate.
    discriminate.

    intro H_check_ord.
    rewrite -> (unfold_traverse_to_check_ordered_bt_node A t'' compare)
      in H_check_ord.
    induction t'' as [hbt1'' e hbt2''].
    rewrite -> (unfold_traverse_to_check_ordered_t A hbt1'' e hbt2'' compare)
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
    exact (False_ind
             P
             H_false).
Qed.

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
  rewrite -> unfold_traverse_to_check_ordered_bt_node.
  rewrite -> unfold_traverse_to_check_ordered_t.
  
  unfold is_ordered_hbt in H.
  rewrite -> unfold_traverse_to_check_ordered_hbt in H.
  rewrite -> unfold_traverse_to_check_ordered_bt_node in H.
  rewrite -> unfold_traverse_to_check_ordered_t in H.
  
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
  rewrite -> unfold_traverse_to_check_ordered_hbt in H.
  induction bt as [ | t].
  rewrite -> unfold_traverse_to_check_ordered_bt_leaf in H.
  discriminate.
  induction t as [hbt1 e hbt2].
  unfold is_ordered_hbt.
  rewrite -> unfold_traverse_to_check_ordered_hbt.
  rewrite -> H.
  reflexivity.
Qed.

Lemma traverse_node_impossible_case:
  forall (A : Type)
         (compare : A -> A -> element_comparison)
         (t1 : triple A),
    traverse_to_check_ordered_bt A (Node A t1) compare = TNone (A * A) -> False. 
Proof.
  intros A compare t1 H.
  rewrite -> unfold_traverse_to_check_ordered_bt_node in H.
  induction t1 as [hbt11 e1 hbt12].
  rewrite -> unfold_traverse_to_check_ordered_t in H.
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
  rewrite -> unfold_traverse_to_check_ordered_hbt.
  rewrite -> unfold_traverse_to_check_ordered_bt_leaf.
  apply or_introl.
  reflexivity.
  rewrite -> unfold_traverse_to_check_ordered_hbt in H.
  case (traverse_to_check_ordered_bt A (Node A t) compare)
    as [ | |(min, max)] eqn : C_traverse_bt. 
  discriminate.
  
  assert (H_false : False).
  Check (traverse_node_impossible_case).
  exact (traverse_node_impossible_case A compare t C_traverse_bt).
  apply False_ind.
  exact H_false.

  apply or_intror.
  exists min.
  exists max.
  exact C_traverse_bt.
Qed.

Lemma reconstruct_ordered_hbt_left:
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
  rewrite -> unfold_traverse_to_check_ordered_hbt.
  rewrite -> unfold_traverse_to_check_ordered_bt_node.
  rewrite -> unfold_traverse_to_check_ordered_t.   
  rewrite -> unfold_traverse_to_check_ordered_hbt.
  rewrite -> unfold_traverse_to_check_ordered_bt_leaf.
  rewrite -> unfold_traverse_to_check_ordered_hbt in H. 
  rewrite -> unfold_traverse_to_check_ordered_bt_node in H.
  rewrite -> unfold_traverse_to_check_ordered_t in H.
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

Lemma reconstruct_ordered_hbt_right:
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
  rewrite -> unfold_traverse_to_check_ordered_hbt.
  rewrite -> unfold_traverse_to_check_ordered_bt_node.
  rewrite -> unfold_traverse_to_check_ordered_t.   
  rewrite -> unfold_traverse_to_check_ordered_hbt.
  rewrite -> unfold_traverse_to_check_ordered_bt_leaf.
  rewrite -> unfold_traverse_to_check_ordered_hbt in H. 
  rewrite -> unfold_traverse_to_check_ordered_bt_node in H.
  rewrite -> unfold_traverse_to_check_ordered_t in H.
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
                                          (Node A (Triple A (HNode A h11' bt11') e1 (HNode A h121' bt121')))) e12
                                   (HNode A (1 + max h122' h2)
                                          (Node A (Triple A (HNode A h122' bt122') e (HNode A h2 bt2))))))) compare = true).
  Check (traverse_to_check_ordered_hbt_some_implies_is_ordered).
  exact (traverse_to_check_ordered_hbt_some_implies_is_ordered
           A compare
           (HNode A (1 + max (1 + max h11' h121') (1 + max h122' h2))
                  (Node A
                        (Triple A
                                (HNode A (1 + max h11' h121')
                                       (Node A (Triple A (HNode A h11' bt11') e1 (HNode A h121' bt121')))) e12
                                (HNode A (1 + max h122' h2)
                                       (Node A (Triple A (HNode A h122' bt122') e (HNode A h2 bt2)))))))
           t_min' t_max' H).
  Check (triple_ordered_implies_hbts_ordered).
  destruct (triple_ordered_implies_hbts_ordered
              A compare
              (1 + max (1 + max h11' h121') (1 + max h122' h2))
              (HNode A (1 + max h11' h121')
                     (Node A (Triple A (HNode A h11' bt11') e1 (HNode A h121' bt121'))))
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
  rewrite -> unfold_traverse_to_check_ordered_hbt in H.
  rewrite -> unfold_traverse_to_check_ordered_bt_node in H.  
  rewrite -> unfold_traverse_to_check_ordered_t in H.    
  rewrite -> unfold_traverse_to_check_ordered_hbt in H.
  rewrite -> unfold_traverse_to_check_ordered_bt_node in H.  
  rewrite -> unfold_traverse_to_check_ordered_t in H.    
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
  rewrite -> unfold_traverse_to_check_ordered_hbt in H.
  rewrite -> unfold_traverse_to_check_ordered_bt_node in H.  
  rewrite -> unfold_traverse_to_check_ordered_t in H.    
  rewrite -> unfold_traverse_to_check_ordered_hbt in H.
  rewrite -> unfold_traverse_to_check_ordered_bt_node in H.  
  rewrite -> unfold_traverse_to_check_ordered_t in H.
  rewrite -> unfold_traverse_to_check_ordered_hbt in H.
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

  (* to prove this inequality, clevery reduce the original rotated tree while preserving 
   * order *)
  assert (H_comp_e12_min_122': 
            forall  (min122' max122' : A),
              traverse_to_check_ordered_hbt
                A (HNode A h122' bt122') compare = TSome (A * A) (min122', max122') ->
              compare e12 min122' = Lt). 
  intros.
  Check (reconstruct_ordered_hbt_left).
  assert (H_reduced_tree:
            traverse_to_check_ordered_hbt
              A
              (HNode A (1 + max (1 + max h11' h121') (1 + max h122' h2))
                     (Node A
                           (Triple A (HNode A 0 (Leaf A)) e12
                                   (HNode A (1 + max h122' h2)
                                          (Node A (Triple A (HNode A h122' bt122') e (HNode A h2 bt2))))))) compare =
            TSome (A * A) (e12, t_max')).
  exact (reconstruct_ordered_hbt_left
           A compare
           (1 + max (1 + max h11' h121') (1 + max h122' h2))
           (HNode A (1 + max h11' h121')
                  (Node A (Triple A (HNode A h11' bt11') e1 (HNode A h121' bt121'))))
           e12
           (HNode A (1 + max h122' h2)
                  (Node A (Triple A (HNode A h122' bt122') e (HNode A h2 bt2))))
           t_min' t_max'
           H).
  rewrite -> unfold_traverse_to_check_ordered_hbt in H_reduced_tree.
  rewrite -> unfold_traverse_to_check_ordered_bt_node in H_reduced_tree.  
  rewrite -> unfold_traverse_to_check_ordered_t in H_reduced_tree.    
  rewrite -> unfold_traverse_to_check_ordered_hbt in H_reduced_tree.
  rewrite -> unfold_traverse_to_check_ordered_bt_leaf in H_reduced_tree.
  rewrite -> unfold_traverse_to_check_ordered_hbt in H_reduced_tree.
  rewrite -> unfold_traverse_to_check_ordered_bt_node in H_reduced_tree.    
  rewrite -> unfold_traverse_to_check_ordered_t in H_reduced_tree.
  rewrite -> H0 in H_reduced_tree.
  case (compare max122' e) as [ | | ].
  case (traverse_to_check_ordered_hbt A (HNode A h2 bt2) compare) as [ | | (min2, max2)].
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
  rewrite -> unfold_traverse_to_check_ordered_hbt in H_left_ord.
  rewrite -> unfold_traverse_to_check_ordered_bt_node in H_left_ord.  
  rewrite -> unfold_traverse_to_check_ordered_t in H_left_ord.
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
  rewrite -> unfold_traverse_to_check_ordered_hbt.
  rewrite -> unfold_traverse_to_check_ordered_bt_node.
  rewrite -> unfold_traverse_to_check_ordered_t.
  rewrite ->
          (unfold_traverse_to_check_ordered_hbt
             A h12'
             (Node A (Triple A (HNode A h121' bt121') e12 (HNode A h122' bt122')))
             compare).
  rewrite ->
          (unfold_traverse_to_check_ordered_bt_node
             A 
             (Triple A (HNode A h121' bt121') e12 (HNode A h122' bt122'))
             compare).
  rewrite ->
          (unfold_traverse_to_check_ordered_t
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
  exact (reconstruct_ordered_hbt_right
           A compare
           (1 + max (1 + max h11' h121') (1 + max h122' h2))
           (HNode A (1 + max h11' h121')
                  (Node A (Triple A (HNode A h11' bt11') e1 (HNode A h121' bt121'))))
           e12
           (HNode A (1 + max h122' h2)
                  (Node A (Triple A (HNode A h122' bt122') e (HNode A h2 bt2))))
           t_min' t_max' H).
  rewrite -> unfold_traverse_to_check_ordered_hbt in H_for_t_min'.
  rewrite -> unfold_traverse_to_check_ordered_bt_node in H_for_t_min'.
  rewrite -> unfold_traverse_to_check_ordered_t in H_for_t_min'.
  rewrite -> unfold_traverse_to_check_ordered_hbt in H_for_t_min'.
  rewrite -> unfold_traverse_to_check_ordered_bt_node in H_for_t_min'.
  rewrite -> unfold_traverse_to_check_ordered_t in H_for_t_min'.
  rewrite -> (unfold_traverse_to_check_ordered_hbt A 0 (Leaf A) compare)  in H_for_t_min'.
  rewrite -> unfold_traverse_to_check_ordered_bt_leaf in H_for_t_min'.

  (* Finally, we may tackle the 8 possible cases *) 
  Check (is_ordered_true_implies_leaf_or_ordered_node).
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
        rewrite -> (H_comp_max_bt121'_e12 min121' max121' H_bt121'_node) in H_for_t_min'.
        exists max122'.
        rewrite -> tsome_x_equal_tsome_y in H_for_t_min'.
        rewrite -> pairwise_equality in H_for_t_min'.
        destruct H_for_t_min' as [H_t_min' _].
        rewrite -> H_t_min'.
        reflexivity.         
      }
Qed.

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

  rewrite -> unfold_insert_hbt_helper in H.
  rewrite -> unfold_insert_bt_helper_leaf in H.
  rewrite -> some_x_equal_some_y in H.
  discriminate.
  unfold not.
  intro H'.
  discriminate.
Qed.

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
  rewrite -> unfold_traverse_to_check_ordered_t in H0.
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
                   (Triple A (HNode A 0 (Leaf A)) e
                           (HNode A h_rot_left
                                  (Node A
                                        (Triple A hbt_left e' hbt_right))))))
      compare = TSome (A * A) (e, max') ->
    traverse_to_check_ordered_hbt
      A (HNode A h_org
               (Node A (Triple A (HNode A 0 (Leaf A)) e' hbt_right)))
      compare = TSome (A * A) (e', max) ->
    max' = max.
Proof.
  intros. 
  induction hbt_right as [h_r bt_r].
  induction hbt_left as [h_l bt_l].
  
  rewrite -> unfold_traverse_to_check_ordered_hbt in H.
  rewrite -> unfold_traverse_to_check_ordered_bt_node in H.    
  rewrite -> unfold_traverse_to_check_ordered_t in H.
  rewrite -> unfold_traverse_to_check_ordered_hbt in H.    
  rewrite -> unfold_traverse_to_check_ordered_bt_leaf in H.
  rewrite -> unfold_traverse_to_check_ordered_hbt in H.
  rewrite -> unfold_traverse_to_check_ordered_bt_node in H.    
  rewrite -> unfold_traverse_to_check_ordered_t in H.

    (* now we do a case analysis on hbt2 *)
  case bt_r as [ | t_r].

    (* bt_l is a leaf *)
    + (* obtain the t_max value from H0 first *)
      rewrite -> unfold_traverse_to_check_ordered_hbt in H0.
      rewrite -> unfold_traverse_to_check_ordered_bt_node in H0.
      rewrite -> unfold_traverse_to_check_ordered_t in H0.      
      rewrite -> unfold_traverse_to_check_ordered_hbt in H0.
      rewrite -> unfold_traverse_to_check_ordered_bt_leaf in H0.      
      rewrite -> unfold_traverse_to_check_ordered_hbt in H0.
      rewrite -> unfold_traverse_to_check_ordered_bt_leaf in H0.      
      rewrite -> tsome_x_equal_tsome_y in H0.
      rewrite -> pairwise_equality in H0.
      destruct H0 as [_ H_e_t_max].

      (* now case analyse our way through the goal *)
      case (traverse_to_check_ordered_hbt A (HNode A h_l bt_l) compare)
           as [ | | (min_l, max_l)].
      discriminate.
      rewrite -> unfold_traverse_to_check_ordered_hbt in H.
      rewrite -> unfold_traverse_to_check_ordered_bt_leaf in H.
      case (compare e e') as [ | | ].
      rewrite -> tsome_x_equal_tsome_y in H.
      rewrite -> pairwise_equality in H.
      destruct H as [_ H_e_t_max'].
      rewrite <- H_e_t_max'.
      exact H_e_t_max.

      discriminate.
      
      discriminate.
      
      case (compare max_l e') as [ | | ].
      rewrite -> unfold_traverse_to_check_ordered_hbt in H.
      rewrite -> unfold_traverse_to_check_ordered_bt_leaf in H.
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
      rewrite -> unfold_traverse_to_check_ordered_hbt in H0.
      rewrite -> unfold_traverse_to_check_ordered_bt_node in H0.
      rewrite -> unfold_traverse_to_check_ordered_t in H0.      
      rewrite -> unfold_traverse_to_check_ordered_hbt in H0.
      rewrite -> unfold_traverse_to_check_ordered_bt_leaf in H0.
      rewrite -> unfold_traverse_to_check_ordered_hbt in H0.      
      case (traverse_to_check_ordered_bt A (Node A t_r) compare)
        as [ | | (minr, maxr)] eqn : C_traverse_ord_hbt_r.
      discriminate.
      Check (traverse_node_impossible_case).
      
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
      rewrite -> unfold_traverse_to_check_ordered_hbt in H.
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
      rewrite -> unfold_traverse_to_check_ordered_hbt in H.
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
  
Lemma rotate_right_1_min_max: 
  forall (A : Type)
         (compare : A -> A -> element_comparison)
         (h11' h121' h122' h2 : nat)
         (bt11' bt121' bt122' bt2 : binary_tree A)
         (e1 e12 e : A)
         (hbt1 : heightened_binary_tree A)
         (t_min' t_max' t_min t_max min1 max1 x : A),
    traverse_to_check_ordered_t A 
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
  Check (rotate_right_min).
  exact (rotate_right_min A compare hbt1 e h2 bt2 t_min t_max min1 max1 t_min' x H0 H1 H2).

  - apply or_intror.

    (* t_max' is max2 in our case; to show this, we will left reconstruct the rotated tree
     * twice *)

    (* we first reconstruct our original triple to only consider hbt2 *)
    assert (H_traverse_hbt_org:
              traverse_to_check_ordered_hbt
                A
                (HNode A h2 (Node A ((Triple A hbt1 e (HNode A h2 bt2))))) compare = 
              TSome (A * A) (t_min, t_max)).
    rewrite -> unfold_traverse_to_check_ordered_hbt.
    rewrite -> unfold_traverse_to_check_ordered_bt_node.  
    exact H0.

    Check (reconstruct_ordered_hbt_left).
    assert (H_hbt_org_reconstructed:
              traverse_to_check_ordered_hbt
                A
                (HNode A h2 (Node A (Triple A (HNode A 0 (Leaf A)) e (HNode A h2 bt2)))) compare =
              TSome (A * A) (e, t_max)).
    exact (reconstruct_ordered_hbt_left
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
    rewrite -> unfold_traverse_to_check_ordered_hbt.
    rewrite -> unfold_traverse_to_check_ordered_bt_node.  
    exact H.

    (* next, use reconstruct_ordered_hbt_left *)
    Check reconstruct_ordered_hbt_left.

    assert (H_reconstrcuted_1 :
              traverse_to_check_ordered_hbt
                A
                (HNode A (1 + max (1 + max h11' h121') (1 + max h122' h2))
                       (Node A
                             (Triple A (HNode A 0 (Leaf A)) e12
                                     (HNode A (1 + max h122' h2)
                                            (Node A (Triple A (HNode A h122' bt122') e (HNode A h2 bt2))))))) compare =
              TSome (A * A) (e12, t_max')).
    exact (reconstruct_ordered_hbt_left
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
    Check (rotate_right_max).
    Check (rotate_right_max
             A compare (1 + max (1 + max h11' h121') (1 + max h122' h2))
             e12 (1 + max h122' h2)
             (HNode A h122' bt122') e (HNode A h2 bt2)
             t_max' h2 t_max
             H_reconstrcuted_1
             H_hbt_org_reconstructed).
    exact (rotate_right_max
             A compare (1 + max (1 + max h11' h121') (1 + max h122' h2))
             e12 (1 + max h122' h2)
             (HNode A h122' bt122') e (HNode A h2 bt2)
             t_max' h2 t_max
             H_reconstrcuted_1
             H_hbt_org_reconstructed).
Qed.    
    
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
  Check (triple_ordered_implies_hbts_ordered).
  destruct (triple_ordered_implies_hbts_ordered
              A compare (1 + max h11' (1 + max h12' h2))
              (HNode A h11' bt11')
              e1
              (HNode A (1 + max h12' h2)
                     (Node A (Triple A (HNode A h12' bt12') e (HNode A h2 bt2))))
              H_fold_traverse) as [H_ord_bt11' H_ord_right_subtree].
  Check (triple_ordered_implies_hbts_ordered).
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
  Check (reconstruct_ordered_hbt_right).
  assert (H_reduced_tree:
            traverse_to_check_ordered_hbt
              A
              (HNode A (1 + max h11' (1 + max h12' h2))
                     (Node A (Triple A (HNode A h11' bt11') e1 (HNode A 0 (Leaf A))))) compare =
            TSome (A * A) (t_min', e1)).
  exact (reconstruct_ordered_hbt_right
           A compare (1 + max h11' (1 + max h12' h2))
           (HNode A h11' bt11')
           e1
           (HNode A (1 + max h12' h2)
                  (Node A (Triple A (HNode A h12' bt12') e (HNode A h2 bt2))))
           t_min' t_max' H).
  
  rewrite -> unfold_traverse_to_check_ordered_hbt in H_reduced_tree.
  rewrite -> unfold_traverse_to_check_ordered_bt_node in H_reduced_tree.
  rewrite -> unfold_traverse_to_check_ordered_t in H_reduced_tree.
  rewrite -> H0 in H_reduced_tree.
  rewrite -> unfold_traverse_to_check_ordered_hbt in H_reduced_tree.
  rewrite -> unfold_traverse_to_check_ordered_bt_leaf in H_reduced_tree.
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
  (* reconstruct tree *)
  Check (reconstruct_ordered_hbt_left).
  assert (H_reduced_tree:
            traverse_to_check_ordered_hbt
              A
              (HNode A (1 + max h11' (1 + max h12' h2))
                     (Node A
                           (Triple A (HNode A 0 (Leaf A)) e1
                                   (HNode A (1 + max h12' h2)
                                          (Node A (Triple A (HNode A h12' bt12') e (HNode A h2 bt2))))))) compare =
            TSome (A * A) (e1, t_max')).
  exact (reconstruct_ordered_hbt_left
           A compare (1 + max h11' (1 + max h12' h2))
           (HNode A h11' bt11')
           e1
           (HNode A (1 + max h12' h2)
                  (Node A (Triple A (HNode A h12' bt12') e (HNode A h2 bt2))))
           t_min' t_max' H).
  rewrite -> unfold_traverse_to_check_ordered_hbt in H_reduced_tree.
  rewrite -> unfold_traverse_to_check_ordered_bt_node in H_reduced_tree.
  rewrite -> unfold_traverse_to_check_ordered_t in H_reduced_tree.
  rewrite -> unfold_traverse_to_check_ordered_hbt in H_reduced_tree.
  rewrite -> unfold_traverse_to_check_ordered_bt_leaf in H_reduced_tree.
  rewrite -> unfold_traverse_to_check_ordered_hbt in H_reduced_tree.
  rewrite -> unfold_traverse_to_check_ordered_bt_node in H_reduced_tree.
  rewrite -> unfold_traverse_to_check_ordered_t in H_reduced_tree.
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
  Check (reconstruct_ordered_hbt_right).
  assert (H_reduced_tree:
            traverse_to_check_ordered_hbt
              A
              (HNode A (1 + max h11' (1 + max h12' h2))
                     (Node A (Triple A (HNode A h11' bt11') e1 (HNode A 0 (Leaf A))))) compare =
            TSome (A * A) (t_min', e1)).
  exact (reconstruct_ordered_hbt_right
           A compare (1 + max h11' (1 + max h12' h2))
           (HNode A h11' bt11')
           e1
           (HNode A (1 + max h12' h2)
                  (Node A (Triple A (HNode A h12' bt12') e (HNode A h2 bt2))))
           t_min' t_max' H).
  
  rewrite -> unfold_traverse_to_check_ordered_hbt in H_reduced_tree.
  rewrite -> unfold_traverse_to_check_ordered_bt_node in H_reduced_tree.
  rewrite -> unfold_traverse_to_check_ordered_t in H_reduced_tree.
  rewrite -> (unfold_traverse_to_check_ordered_hbt A 0 (Leaf A) compare) in H_reduced_tree.
  rewrite -> unfold_traverse_to_check_ordered_bt_leaf in H_reduced_tree.

  (* finally, work through all possible cases for bt11' and bt12' *)
  Check (is_ordered_true_implies_leaf_or_ordered_node).
  
  case (is_ordered_true_implies_leaf_or_ordered_node
          A compare (HNode A h11' bt11') H_ord_bt11') as [H_bt11'_leaf | H_bt11'_node].

  (* bt11' = leaf *)
  - case (is_ordered_true_implies_leaf_or_ordered_node
            A compare (HNode A h12' bt12') H_ord_bt12') as [H_bt12'_leaf | H_bt12'_node]. 

    (* bt12' = leaf *)
    + rewrite -> unfold_traverse_to_check_ordered_hbt.
      rewrite -> unfold_traverse_to_check_ordered_bt_node.
      rewrite -> unfold_traverse_to_check_ordered_t.      
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
      rewrite -> unfold_traverse_to_check_ordered_hbt.
      rewrite -> unfold_traverse_to_check_ordered_bt_node.
      rewrite -> unfold_traverse_to_check_ordered_t.
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
      rewrite -> unfold_traverse_to_check_ordered_hbt.
      rewrite -> unfold_traverse_to_check_ordered_bt_node.
      rewrite -> unfold_traverse_to_check_ordered_t.
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
      rewrite -> unfold_traverse_to_check_ordered_hbt.
      rewrite -> unfold_traverse_to_check_ordered_bt_node.
      rewrite -> unfold_traverse_to_check_ordered_t.
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

Lemma rotate_right_2_impossible_case:
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
      (HNode A h1' (Node A (Triple A (HNode A h11' bt11') e1 (HNode A h12' bt12')))) -> 
    (h12' + 1 =n= h11') = true ->
    bt1 <> (Leaf A).
Proof.
  intros.
  induction bt1 as [ | t1].

  rewrite -> unfold_insert_hbt_helper in H.
  rewrite -> unfold_insert_bt_helper_leaf in H.
  rewrite -> some_x_equal_some_y in H.
  Search (( _ =n= _) = _ -> _).
  apply  beq_nat_true in H0.
  rewrite <- H0 in H.

  assert (H_unequal: False).
  case h12' as [ | h12''].
  Search (0 + _ = _).
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
  Check (rotate_right_min).
  Check (rotate_right_min
           A compare hbt1 e h2 bt2 t_min t_max min1 max1 t_min' x H0 H1 H2).
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
  rewrite -> unfold_traverse_to_check_ordered_hbt.
  rewrite -> unfold_traverse_to_check_ordered_bt_node.
  exact H0.

  (* then left reduce it *)
  Check (reconstruct_ordered_hbt_left).
  assert (H_hbt_org_reduced:
            traverse_to_check_ordered_hbt
              A
              (HNode A (1 + max (project_height_hbt A hbt1) h2)
                     (Node A (Triple A (HNode A 0 (Leaf A)) e (HNode A h2 bt2)))) compare =
            TSome (A * A) (e, t_max)).
  exact (reconstruct_ordered_hbt_left
           A compare (1 + max (project_height_hbt A hbt1) h2)
           hbt1 e (HNode A h2 bt2) t_min t_max H_fold_traverse).

  (* next, left reduce the rotated tree *)
  Check (reconstruct_ordered_hbt_left).
  assert (H_hbt_rot_reduced:
            traverse_to_check_ordered_hbt
              A
              (HNode A (1 + max h11' (1 + max h12' h2))
                     (Node A
                           (Triple A (HNode A 0 (Leaf A)) e1
                                   (HNode A (1 + max h12' h2)
                                          (Node A (Triple A (HNode A h12' bt12') e (HNode A h2 bt2))))))) compare =
            TSome (A * A) (e1, t_max')).
  exact (reconstruct_ordered_hbt_left
           A compare (1 + max h11' (1 + max h12' h2))
           (HNode A h11' bt11')
           e1
           (HNode A (1 + max h12' h2)
                  (Node A (Triple A (HNode A h12' bt12') e (HNode A h2 bt2))))
           t_min' t_max' H).

  (* finally, invoke the rotate_right_max lemma *)
  Check (rotate_right_max).
  Check (rotate_right_max
           A compare (1 + max h11' (1 + max h12' h2))
           e1 (1 + max h12' h2)
           (HNode A h12' bt12') e (HNode A h2 bt2)
           t_max' (1 + max (project_height_hbt A hbt1) h2) t_max
           H_hbt_rot_reduced
           H_hbt_org_reduced).
  exact (rotate_right_max
           A compare (1 + max h11' (1 + max h12' h2))
           e1 (1 + max h12' h2)
           (HNode A h12' bt12') e (HNode A h2 bt2)
           t_max' (1 + max (project_height_hbt A hbt1) h2) t_max
           H_hbt_rot_reduced
           H_hbt_org_reduced).
Qed.



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
  Check (traverse_to_check_ordered_hbt_some_implies_is_ordered).
  assert (H_fold_H:
            is_ordered_hbt
              A
              (HNode A (1 + max (1 + max h1 h211') (1 + max h212' h22'))
                     (Node A
                           (Triple A
                                   (HNode A (1 + max h1 h211')
                                          (Node A (Triple A (HNode A h1 bt1) e (HNode A h211' bt211')))) e21
                                   (HNode A (1 + max h212' h22')
                                          (Node A (Triple A (HNode A h212' bt212') e2 (HNode A h22' bt22')))))))
              compare = true).
  exact (traverse_to_check_ordered_hbt_some_implies_is_ordered
           A compare
           (HNode A (1 + max (1 + max h1 h211') (1 + max h212' h22'))
                  (Node A
                        (Triple A
                                (HNode A (1 + max h1 h211')
                                       (Node A (Triple A (HNode A h1 bt1) e (HNode A h211' bt211')))) e21
                                (HNode A (1 + max h212' h22')
                                       (Node A (Triple A (HNode A h212' bt212') e2 (HNode A h22' bt22')))))))
           t_min' t_max' H).
  Check (triple_ordered_implies_hbts_ordered).  
  destruct (triple_ordered_implies_hbts_ordered
              A compare (1 + max (1 + max h1 h211') (1 + max h212' h22'))
              (HNode A (1 + max h1 h211')
                     (Node A (Triple A (HNode A h1 bt1) e (HNode A h211' bt211'))))
              e21
              (HNode A (1 + max h212' h22')
                     (Node A (Triple A (HNode A h212' bt212') e2 (HNode A h22' bt22'))))
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
  Check (reconstruct_ordered_hbt_left).
  assert (H_rotate_left_reduced:
            traverse_to_check_ordered_hbt
              A
              (HNode A (1 + max (1 + max h1 h211') (1 + max h212' h22'))
                     (Node A
                           (Triple A (HNode A 0 (Leaf A)) e21
                                   (HNode A (1 + max h212' h22')
                                          (Node A (Triple A (HNode A h212' bt212') e2 (HNode A h22' bt22')))))))
              compare = TSome (A * A) (e21, t_max')).
  exact (reconstruct_ordered_hbt_left
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
  Check (reconstruct_ordered_hbt_right).
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
  exact (reconstruct_ordered_hbt_right
           A compare (1 + max (1 + max h1 h211') (1 + max h212' h22'))
           (HNode A (1 + max h1 h211')
                  (Node A (Triple A (HNode A h1 bt1) e (HNode A h211' bt211'))))
           e21
           (HNode A (1 + max h212' h22')
                  (Node A (Triple A (HNode A h212' bt212') e2 (HNode A h22' bt22'))))
           t_min' t_max' H).
  
  (* unfold H_right_reduced until inequality is proved *)
  rewrite -> unfold_traverse_to_check_ordered_hbt in H_rotate_right_reduced.
  rewrite -> unfold_traverse_to_check_ordered_bt_node in H_rotate_right_reduced.
  rewrite -> unfold_traverse_to_check_ordered_t in H_rotate_right_reduced.
  rewrite -> (unfold_traverse_to_check_ordered_hbt A 0 (Leaf A)) in H_rotate_right_reduced.
  rewrite -> unfold_traverse_to_check_ordered_bt_leaf in H_rotate_right_reduced.
  rewrite -> unfold_traverse_to_check_ordered_hbt in H_rotate_right_reduced.
  rewrite -> unfold_traverse_to_check_ordered_bt_node in H_rotate_right_reduced.
  rewrite -> unfold_traverse_to_check_ordered_t in H_rotate_right_reduced.  
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
  rewrite -> unfold_traverse_to_check_ordered_hbt in H_rotate_left_reduced.
  rewrite -> unfold_traverse_to_check_ordered_bt_node in H_rotate_left_reduced.
  rewrite -> unfold_traverse_to_check_ordered_t in H_rotate_left_reduced.
  rewrite -> (unfold_traverse_to_check_ordered_hbt A 0 (Leaf A)) in H_rotate_left_reduced.
  rewrite -> unfold_traverse_to_check_ordered_bt_leaf in H_rotate_left_reduced.
  rewrite -> unfold_traverse_to_check_ordered_hbt in H_rotate_left_reduced.
  rewrite -> unfold_traverse_to_check_ordered_bt_node in H_rotate_left_reduced.
  rewrite -> unfold_traverse_to_check_ordered_t in H_rotate_left_reduced.  
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
  rewrite -> unfold_traverse_to_check_ordered_hbt in H_right_ord.
  rewrite -> unfold_traverse_to_check_ordered_bt_node in H_right_ord.
  rewrite -> unfold_traverse_to_check_ordered_t in H_right_ord.  
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
  rewrite -> unfold_traverse_to_check_ordered_hbt in H_right_ord.
  rewrite -> unfold_traverse_to_check_ordered_bt_node in H_right_ord.
  rewrite -> unfold_traverse_to_check_ordered_t in H_right_ord.  
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
  rewrite -> unfold_traverse_to_check_ordered_hbt in H_rotate_left_reduced.
  rewrite -> unfold_traverse_to_check_ordered_bt_node in H_rotate_left_reduced.
  rewrite -> unfold_traverse_to_check_ordered_t in H_rotate_left_reduced.
  rewrite -> (unfold_traverse_to_check_ordered_hbt A 0 (Leaf A)) in H_rotate_left_reduced.
  rewrite -> unfold_traverse_to_check_ordered_bt_leaf in H_rotate_left_reduced.
  rewrite -> unfold_traverse_to_check_ordered_hbt in H_rotate_left_reduced.
  rewrite -> unfold_traverse_to_check_ordered_bt_node in H_rotate_left_reduced.
  rewrite -> unfold_traverse_to_check_ordered_t in H_rotate_left_reduced.

  (* With all our theorems in place, we now unfold the goal *)
  rewrite -> unfold_traverse_to_check_ordered_hbt.
  rewrite -> unfold_traverse_to_check_ordered_bt_node.
  rewrite -> unfold_traverse_to_check_ordered_t.
  rewrite -> unfold_traverse_to_check_ordered_hbt.
  rewrite -> unfold_traverse_to_check_ordered_bt_node.
  rewrite -> unfold_traverse_to_check_ordered_t.
  
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

  rewrite -> unfold_insert_hbt_helper in H.
  rewrite -> unfold_insert_bt_helper_leaf in H.  
  rewrite -> some_x_equal_some_y in H.
  discriminate.

  unfold not.
  intro H'.
  discriminate.
Qed.


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
Admitted. 

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
Admitted.

Lemma rotate_left_2_impossible_case:
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
Admitted.

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
  Admitted.


Lemma insertion_in_node_min_max: 
  forall (A : Type)
         (compare : A -> A -> element_comparison),
    (forall (hbt : heightened_binary_tree A)
            (hbt' : heightened_binary_tree A)
            (x min min' max max' : A),
        insert_hbt_helper A compare x hbt = Some hbt' ->
        traverse_to_check_ordered_hbt A hbt' compare = TSome (A * A) (min', max') ->
        traverse_to_check_ordered_hbt A hbt compare = TSome (A * A) (min, max) ->
        (max' = x \/ max' = max) /\ (min' = x \/ min' = min))
    /\
    (forall (bt : binary_tree A)
            (h : nat)
            (hbt' : heightened_binary_tree A)
            (x min min' max max' : A),
        insert_bt_helper A compare x h bt = Some hbt' ->
        traverse_to_check_ordered_hbt A hbt' compare = TSome (A * A) (min', max') ->
        traverse_to_check_ordered_bt A bt compare = TSome (A * A) (min, max) ->
        (max' = x \/ max' = max) /\ (min' = x \/ min' = min))
    /\
    (forall (t : triple A)
            (h : nat)
            (hbt' : heightened_binary_tree A)
            (x min min' max max' : A),
        insert_t_helper A compare x h t = Some hbt' ->
        traverse_to_check_ordered_hbt A hbt' compare = TSome (A * A) (min', max') ->
        traverse_to_check_ordered_t A t compare = TSome (A * A) (min, max) ->
        (max' = x \/ max' = max) /\ (min' = x \/ min' = min)).
Proof.    
  intros A compare.
  apply heightened_binary_tree_mutual_induction.

  (* proof for hbt, with bt as inductive hypothesis *)
  intros h bt H_ind_bt hbt' x min min' max max' H_insert_hbt H_ord_hbt' H_ord_hbt.
  rewrite -> (unfold_insert_hbt_helper A compare x h bt) in H_insert_hbt.
  rewrite -> (unfold_traverse_to_check_ordered_hbt A h bt compare) in H_ord_hbt.
  Check (H_ind_bt h hbt' x min min' max max' H_insert_hbt H_ord_hbt' H_ord_hbt).
  exact (H_ind_bt h hbt' x min min' max max' H_insert_hbt H_ord_hbt' H_ord_hbt).

  (* a leaf provides a vacuous case *)
  intros h  hbt' x min min' max max' H_insert_hbt H_ord_hbt' H_ord_hbt.
  rewrite -> (unfold_traverse_to_check_ordered_bt_leaf A compare) in H_ord_hbt.
  discriminate.

  (* proof for node, with t as inductive hypothesis *)
  intros t H_ind_t h hbt' x min min' max max' H_insert_bt H_ord_hbt' H_ord_bt.
  rewrite -> (unfold_insert_bt_helper_node A compare x h t) in H_insert_bt.
  rewrite -> (unfold_traverse_to_check_ordered_bt_node A t compare) in H_ord_bt.
  Check (H_ind_t h hbt' x min min' max max' H_insert_bt H_ord_hbt' H_ord_bt).
  exact (H_ind_t h hbt' x min min' max max' H_insert_bt H_ord_hbt' H_ord_bt).

  (* proof for t, with inductive hypotheses for hbt1 and hbt2 *)
  intros hbt1 H_hbt1 e hbt2 H_hbt2 h hbt' x t_min t_min' t_max t_max'
         H_insert_hbt H_ord_hbt' H_ord_t.  
  
  (* the long and arduous journey into the insert function *)
  rewrite -> (unfold_insert_t_helper A compare x h hbt1 e hbt2) in H_insert_hbt.
  case (compare x e) as [ | | ] eqn : C_comp_x_e.
  case (insert_hbt_helper A compare x hbt1) as [ hbt1'| ] eqn : C_insert_hbt1.
  induction hbt1' as [h1' bt1'].
  case (compare_int (h1' - project_height_hbt A hbt2) 2) as [ | | ] eqn : C_comp_heights.

  (* height diff is less than 2: no rotations required *)
  - rewrite -> (some_x_equal_some_y
                  (heightened_binary_tree A)
                  (HNode A (1 + max h1' (project_height_hbt A hbt2))
                         (Node A (Triple A (HNode A h1' bt1') e hbt2)))
                  hbt') in H_insert_hbt.
    rewrite <- H_insert_hbt in H_ord_hbt'.
    (* unfold for hbt' *)
    rewrite -> 
            (unfold_traverse_to_check_ordered_hbt
               A
               (1 + max h1' (project_height_hbt A hbt2))
               (Node A (Triple A (HNode A h1' bt1') e hbt2))) in H_ord_hbt'.
    rewrite ->
            (unfold_traverse_to_check_ordered_bt_node
               A
               (Triple A (HNode A h1' bt1') e hbt2)) in H_ord_hbt'.
    rewrite ->
            (unfold_traverse_to_check_ordered_t
               A
               (HNode A h1' bt1')
               e
               hbt2) in H_ord_hbt'.
    case (traverse_to_check_ordered_hbt A (HNode A h1' bt1') compare)
      as [ | | (min_hbt', max_hbt')] eqn : C_check_ord_hbt'.
    (* unordered insertion subtree *)
    + discriminate.

    (* impossible case: insertion subtree as leaf *)
    + case (traverse_to_check_ordered_hbt A hbt2 compare)
        as [ | | (min_hbt2, max_hbt2)] eqn : C_check_ord_hbt2.
      discriminate.
      exact (insertion_impossible_case_implies_true
             A hbt1 (HNode A h1' bt1') compare x
             ((t_max' = x \/ t_max' = t_max) /\ (t_min' = x \/ t_min' = t_min))
             C_insert_hbt1
             C_check_ord_hbt').
      exact (insertion_impossible_case_implies_true
               A hbt1 (HNode A h1' bt1') compare x
               ((t_max' = x \/ t_max' = t_max) /\ (t_min' = x \/ t_min' = t_min))
               C_insert_hbt1
               C_check_ord_hbt').

      (* insertion subtree is ordered, has max' and min' *)
    + case (compare max_hbt' e) as [ | | ] eqn : C_comp_max_hbt'_e.
      case (traverse_to_check_ordered_hbt A hbt2 compare) as
          [ | | (min2, max2)] eqn : C_check_ord_hbt2.
 
      (* hbt2 is unordered *)
      * discriminate.

      (* hbt2 is a leaf: make use of inductive hypothesis for hbt1 *)
      * rewrite -> (unfold_traverse_to_check_ordered_t A hbt1 e hbt2 compare)
          in H_ord_t.
        case (traverse_to_check_ordered_hbt A hbt1 compare)
          as [ | | (min1, max1)] eqn : C_check_ord_hbt1.
 
        (* hbt1 was unordered *)
        { discriminate. }

        (* hbt1 was a leaf: use lemmas defined earlier *)
        {
          rewrite -> C_check_ord_hbt2 in H_ord_t.
          assert (H_equalities:
                    min_hbt' = x /\ max_hbt' = x).
          exact (insertion_in_leaf_min_max
                   A compare
                   hbt1
                   (HNode A h1' bt1')
                   x min_hbt' max_hbt'
                   C_insert_hbt1
                   C_check_ord_hbt'
                   C_check_ord_hbt1).
          rewrite -> tsome_x_equal_tsome_y in H_ord_hbt'.
          rewrite -> tsome_x_equal_tsome_y in H_ord_t.
          rewrite -> pairwise_equality in H_ord_hbt'.
          rewrite -> pairwise_equality in H_ord_t.
          split.
          destruct H_ord_hbt' as [_ H_t_max'].
          destruct H_ord_t as [_ H_t_max].
          rewrite -> H_t_max in H_t_max'.
          rewrite -> H_t_max'.
          apply or_intror.
          reflexivity.
          destruct H_ord_hbt' as [H_min_hbt' _].
          destruct H_equalities as [H_x _].
          rewrite -> H_min_hbt' in H_x.
          apply or_introl.
          exact H_x.
        }

        (* hbt1 was an ordered subtree with min1 and max1 *)
        {
          case (compare max1 e) as [ | | ] eqn : C_comp_max1_e.

          (* max1 < e *)
          - assert (H_equals_trivial:
                      TSome (A * A) (min1, max1) = TSome (A * A) (min1, max1)).
            reflexivity.
            
            assert (H_equalities_from_ind_h :
                      (max_hbt' = x \/ max_hbt' = max1) /\ (min_hbt' = x \/ min_hbt' = min1)).
            exact (H_hbt1 (HNode A h1' bt1')
                          x min1 min_hbt' max1 max_hbt'
                          C_insert_hbt1
                          C_check_ord_hbt'
                          H_equals_trivial).
            rewrite -> C_check_ord_hbt2 in H_ord_t.
            (* Note: (A \/ B) -> C <-> (A -> C) /\ (B -> C). So the following 
             * destruct will necessitate two proofs, one with A as the hypothesis,
             * and one with B *)
            destruct H_equalities_from_ind_h as [_ [H_min_x | H_min_min1]].

            (* H_min_x as hypothesis *)
            + rewrite -> tsome_x_equal_tsome_y in H_ord_t.
              rewrite -> tsome_x_equal_tsome_y in H_ord_hbt'.
              rewrite -> pairwise_equality in H_ord_t.
              rewrite -> pairwise_equality in H_ord_hbt'.
              destruct H_ord_hbt' as [H_min_hbt' H_t_max'].
              destruct H_ord_t as [_ H_e].
              split.
              apply or_intror.
              rewrite <- H_t_max'.
              rewrite <- H_e.
              reflexivity.
              apply or_introl.
              rewrite <- H_min_hbt'.
              rewrite -> H_min_x.
              reflexivity.

            (* H_min_min1 as hypothesis *)
            + rewrite -> tsome_x_equal_tsome_y in H_ord_hbt'.
              rewrite -> tsome_x_equal_tsome_y in H_ord_t.
              rewrite -> pairwise_equality in H_ord_hbt'.
              rewrite -> pairwise_equality in H_ord_t.
              destruct H_ord_hbt' as [H_t_min'  H_t_max'].
              destruct H_ord_t as [H_t_min H_t_max].
              split.
              apply or_intror.
              rewrite <- H_t_max'.
              rewrite <- H_t_max.
              reflexivity.
              apply or_intror.
              rewrite <- H_t_min.
              rewrite <- H_t_min'.
              exact H_min_min1.
            
            (* max1 = e : impossible case *)
          - discriminate.

            (* max1 > e : impossible case *)
          - discriminate.
        }

      (* hbt2 is a node with a min2 and max2: once again, we unfold H_ord_t, and 
       * do a case analysis on hbt1  *)
      * rewrite -> (unfold_traverse_to_check_ordered_t A hbt1 e hbt2 compare)
          in H_ord_t.
        case (traverse_to_check_ordered_hbt A hbt1 compare)
          as [ | | (min1, max1)] eqn : C_check_ord_hbt1.
 
        (* hbt1 was unordered *)
        { discriminate. }

        (* hbt1 was a leaf: use lemmas defined earlier *)
        {
          rewrite -> C_check_ord_hbt2 in H_ord_t.
          assert (H_equalities:
                    min_hbt' = x /\ max_hbt' = x).
          exact (insertion_in_leaf_min_max
                   A compare
                   hbt1
                   (HNode A h1' bt1')
                   x min_hbt' max_hbt'
                   C_insert_hbt1
                   C_check_ord_hbt'
                   C_check_ord_hbt1).
          case (compare e min2 ) as [ | | ] eqn : C_comp_e_min2.

          (* e < min2 *) 
          + rewrite -> tsome_x_equal_tsome_y in H_ord_hbt'.
            rewrite -> tsome_x_equal_tsome_y in H_ord_t.
            rewrite -> pairwise_equality in H_ord_hbt'.
            rewrite -> pairwise_equality in H_ord_t.
            split.
            destruct H_ord_hbt' as [_ H_t_max'].
            destruct H_ord_t as [_ H_t_max].
            rewrite -> H_t_max in H_t_max'.
            rewrite -> H_t_max'.
            apply or_intror.
            reflexivity.
            destruct H_ord_hbt' as [H_min_hbt' _].
            destruct H_equalities as [H_x _].
            rewrite -> H_min_hbt' in H_x.
            apply or_introl.
            exact H_x.

          (* e = min2: impossible case *)
          + discriminate.

          (* e > min2 : impossible case *)
          + discriminate.
        }

        (* hbt1 is a node with a max1 and min1 *)
        {
          rewrite -> C_check_ord_hbt2 in H_ord_t.
          case (compare max1 e ) as [ | | ] eqn : C_comp_max1_e.

          (* max1 < e *)
          -  case (compare e min2 ) as [ | | ] eqn : C_comp_e_min2.

             (* e < min2 *)
             + rewrite -> tsome_x_equal_tsome_y in H_ord_t.
               rewrite -> tsome_x_equal_tsome_y in H_ord_hbt'.
               rewrite -> pairwise_equality in H_ord_t.
               rewrite -> pairwise_equality in H_ord_hbt'.
               destruct H_ord_hbt' as [H_t_min' H_t_max' ].
               destruct H_ord_t as [H_t_min H_t_max].

               assert (H_equals_trivial:
                         TSome (A * A) (min1, max1) = TSome (A * A) (min1, max1)).
               reflexivity.
             
            assert (H_equalities_from_ind_h :
                      (max_hbt' = x \/ max_hbt' = max1) /\ (min_hbt' = x \/ min_hbt' = min1)).
            exact (H_hbt1 (HNode A h1' bt1')
                          x min1 min_hbt' max1 max_hbt'
                          C_insert_hbt1
                          C_check_ord_hbt'
                          H_equals_trivial).
            split.
            apply or_intror.
            rewrite <- H_t_max'.
            rewrite <- H_t_max.
            reflexivity.

            destruct H_equalities_from_ind_h as [_ [H_min_hbt'_is_x
                                                   | H_min_hbt'_is_min1]].
            (* With H_min_hbt'_is_x as hypothesis *) 
               * apply or_introl.
                 rewrite <- H_t_min'.
                 rewrite -> H_min_hbt'_is_x.
                 reflexivity.
               (* Wiht H_min_hbt'_is_min1 as hypothesis *)
               * apply or_intror.
                 rewrite -> H_t_min in H_min_hbt'_is_min1.
                 rewrite <- H_t_min'.
                 rewrite <- H_min_hbt'_is_min1.
                 reflexivity.
             (* e = min2 : impossible case *)
             + discriminate.

             (* e > min2 : impossible case *)
             + discriminate.
               
          (* max1 = e :  impossible case *)
          - discriminate.
            
          (* max1 >  e : impossible case *)
          - discriminate.
        }

      * discriminate.

      * discriminate.

  (* height difference is 2: rotation required *)
  - unfold rotate_right_hbt in H_insert_hbt. 
    induction hbt2 as [h2 bt2].
    unfold rotate_right_bt in H_insert_hbt.
    case bt1' as [ | t1'].

    (* bt1' is a leaf: impossible case *)
    discriminate.

    (* bt1' is a node *)
    induction t1' as [hbt11' e1 hbt12'].
    induction hbt11' as [h11' bt11'].
    induction hbt12' as [h12' bt12'].
    
    (* required also for the inductive hypothesis: hbt1 is ordered *) 
    assert (H_hbt1_is_ord: is_ordered_hbt A hbt1 compare = true).
    rewrite -> unfold_traverse_to_check_ordered_t in H_ord_t.
    unfold is_ordered_hbt.
    case (traverse_to_check_ordered_hbt A hbt1 compare)
      as [ | | (min1, max1)] eqn : C_traverse_ord_hbt1.
    discriminate.
    reflexivity.
    case (compare max1 e) as [ | | ].
    reflexivity.
    discriminate.
    discriminate.
     
    case (h11' + 1 =n= h12') as [ | ] eqn : C_h11'_h12'. 
    
    (* h11' + 1 = h12' *)
    + case bt12' as [ | t12'].
      
      discriminate.

      (* destruct bt12 as required *)
      induction t12' as [hbt121' e12 hbt122'].
      induction hbt121' as [h121' bt121'].
      induction hbt122' as [h122' bt122'].
      rewrite -> some_x_equal_some_y in H_insert_hbt. 
      rewrite <- H_insert_hbt in H_ord_hbt'.  

      (* crucial assertion to use inductive hypothesis: the tree returned after insertion and
       * before rotation is also ordered *)
      destruct (rotate_right_1_tree_ordered_implies_returned_tree_ordered A
                           compare 
                           h11' h121' h122' h2 h1' h12'
                           bt11' bt121' bt122' bt2 
                           e1 e12 e t_min' t_max' H_ord_hbt')
               as [t_max'' H_traverse_ord_hbt_ret_org].
       
      (* work through base cases for traverse_to_check_ordered_hbt hbt1 until we get to the 
       * point where it is a node *)
      unfold is_ordered_hbt in H_hbt1_is_ord.
      case (traverse_to_check_ordered_hbt A hbt1 compare)
        as [ | | (min1, max1)] eqn : C_traverse_ord_hbt1.
      discriminate.
 
      induction hbt1 as [h1 bt1].
      assert (H_impossible_hbt1 : bt1 <> Leaf A).
      Check (rotate_right_1_impossible_case).
      exact (rotate_right_1_impossible_case
               A compare x h1 bt1
               h1' h11' h12' h121' h122' 
               bt11' bt121' bt122' e1 e12
               C_insert_hbt1).
      rewrite -> unfold_traverse_to_check_ordered_hbt in C_traverse_ord_hbt1.
      induction bt1 as [ | t1].
      rewrite -> unfold_traverse_to_check_ordered_bt_leaf in C_traverse_ord_hbt1.      
      unfold not in H_impossible_hbt1.
      assert (H_trivial_leaf : Leaf A = Leaf A).
      reflexivity.
      apply H_impossible_hbt1 in H_trivial_leaf.
      discriminate.
      Check (traverse_node_impossible_case).
      apply traverse_node_impossible_case in C_traverse_ord_hbt1.
      apply False_ind.
      exact C_traverse_ord_hbt1.
      
      (* finally, we have what is required to apply the inductive hypothesis *)
      assert (H_trivial_equality:
                TSome (A * A) (min1, max1) = TSome (A * A) (min1, max1)).
      reflexivity.
      
      destruct (H_hbt1
                  (HNode A h1'
                         (Node A
                               (Triple A
                                       (HNode A h11' bt11')
                                       e1
                                       (HNode A h12'
                                              (Node A
                                                    (Triple A
                                                            (HNode A h121' bt121')
                                                            e12
                                                            (HNode A h122' bt122')))))))
                  x min1 t_min' max1 t_max''
                  C_insert_hbt1
                  H_traverse_ord_hbt_ret_org
                  H_trivial_equality) as [_ H_t_min'].
      Check (rotate_right_1_min_max).
      exact (rotate_right_1_min_max
               A
               compare
               h11' h121' h122' h2 bt11' bt121' bt122' bt2
               e1 e12 e hbt1
               t_min' t_max' t_min t_max min1 max1 x
               H_ord_hbt'
               H_ord_t
               C_traverse_ord_hbt1
               H_t_min').

    + case (h12' + 1 =n= h11') as [ | ] eqn : C_h12'_h11'.
      rewrite -> some_x_equal_some_y in H_insert_hbt.
      rewrite <- H_insert_hbt in H_ord_hbt'.

      (* important lemma: assert that the returned tree is ordered to 
       * use inductive hypothesis *) 
      Check (rotate_right_2_tree_ordered_implies_returned_tree_ordered).
      destruct (rotate_right_2_tree_ordered_implies_returned_tree_ordered
                  A compare
                  h1' h11' h12' h2 bt11' bt12' bt2
                  e1 e t_min' t_max'
                  H_ord_hbt') as [t_max'' H_traverse_ord_hbt_ret_org].

      (* work through base cases for traverse_to_check_ordered_hbt hbt1 until we get to the 
       * point where it is a node *)
      unfold is_ordered_hbt in H_hbt1_is_ord.
      case (traverse_to_check_ordered_hbt A hbt1 compare)
        as [ | | (min1, max1)] eqn : C_traverse_ord_hbt1.
      discriminate.
      
      induction hbt1 as [h1 bt1].
      
      assert (H_impossible_hbt1 : bt1 <> Leaf A).
      Check (rotate_right_2_impossible_case).
      exact (rotate_right_2_impossible_case
               A compare x h1 bt1
               h1' h11' h12'
               bt11' bt12' e1
               C_insert_hbt1
               C_h12'_h11').

      rewrite -> unfold_traverse_to_check_ordered_hbt in C_traverse_ord_hbt1.
      induction bt1 as [ | t1].
      rewrite -> unfold_traverse_to_check_ordered_bt_leaf in C_traverse_ord_hbt1.      
      unfold not in H_impossible_hbt1.
      assert (H_trivial_leaf : Leaf A = Leaf A).
      reflexivity.
      apply H_impossible_hbt1 in H_trivial_leaf.
      apply False_ind.
      exact H_trivial_leaf.
      
      Check (traverse_node_impossible_case).
      apply traverse_node_impossible_case in C_traverse_ord_hbt1.
      apply False_ind.
      exact C_traverse_ord_hbt1.

      (* finally, we have what is required to apply the inductive hypothesis *)
      assert (H_trivial_equality:
                TSome (A * A) (min1, max1) = TSome (A * A) (min1, max1)).
      reflexivity.
      
      destruct (H_hbt1
                  (HNode A h1'
                         (Node A (Triple A (HNode A h11' bt11') e1 (HNode A h12' bt12'))))
                  x min1 t_min' max1 t_max''
                  C_insert_hbt1
                  H_traverse_ord_hbt_ret_org
                  H_trivial_equality) as [_ H_t_min']. 
      Check (rotate_right_2_min_max).
      exact (rotate_right_2_min_max
               A compare
               h11' h12' h2 bt11' bt12' bt2
               e1 e hbt1
               t_min' t_max' t_min t_max min1 max1 x
               H_ord_hbt'
               H_ord_t
               C_traverse_ord_hbt1
               H_t_min').

      (* case when the subtrees of the returned binary tree do not differ in height by at 
       * most 1: impossible case *)
      discriminate.

  (* height difference greater than 2: given tree was unbalanced to start with *)
  - discriminate.

  - discriminate.

  - discriminate.
    
  - case (insert_hbt_helper A compare x hbt2) as [ hbt2'| ] eqn : C_insert_hbt2.
  induction hbt2' as [h2' bt2'].
  case (compare_int (h2' - project_height_hbt A hbt1) 2) as [ | | ] eqn : C_comp_heights.

    (* height diff is less than 2: no rotations required *) 
    + rewrite -> some_x_equal_some_y in H_insert_hbt.
      rewrite <- H_insert_hbt in H_ord_hbt'.
      (* unfold for hbt' *)
      rewrite -> unfold_traverse_to_check_ordered_hbt in H_ord_hbt'.
      rewrite -> unfold_traverse_to_check_ordered_bt_node in H_ord_hbt'.
      rewrite -> unfold_traverse_to_check_ordered_t in H_ord_hbt'.      

      case (traverse_to_check_ordered_hbt A (HNode A h2' bt2') compare)
        as [ | | (min_hbt', max_hbt')] eqn : C_check_ord_hbt'.
    (* unordered insertion subtree *)
      * case (traverse_to_check_ordered_hbt A hbt1 compare)
          as [ | | (min_hbt1, max_hbt1)] eqn : C_check_ord_hbt1.
        discriminate.
        discriminate.
        case (compare max_hbt1 e) as [ | | ] eqn : C_comp_max_hbt1_e.
        discriminate.
        discriminate.
        discriminate.

      (* impossible case: insertion subtree as leaf *)
      *  case (traverse_to_check_ordered_hbt A hbt1 compare)
          as [ | | (min_hbt1, max_hbt1)] eqn : C_check_ord_hbt1.
         discriminate.
         exact (insertion_impossible_case_implies_true
                  A hbt2 (HNode A h2' bt2') compare x
                  ((t_max' = x \/ t_max' = t_max) /\ (t_min' = x \/ t_min' = t_min))
                  C_insert_hbt2
                  C_check_ord_hbt').
         exact (insertion_impossible_case_implies_true
                  A hbt2 (HNode A h2' bt2') compare x
                  ((t_max' = x \/ t_max' = t_max) /\ (t_min' = x \/ t_min' = t_min))
                  C_insert_hbt2
                  C_check_ord_hbt').

      (* insertion subtree is ordered, has max' and min' *)
      * case (traverse_to_check_ordered_hbt A hbt1 compare) as
            [ | | (min1, max1)] eqn : C_check_ord_hbt1.
  
        (* hbt1 is unordered *) 
        { discriminate. }

        (* hbt1 is a leaf: destruct traverse_to_check_ordered_hbt hbt2 and used inductive
         * hypothesis *)
        {
          case (traverse_to_check_ordered_hbt A hbt2 compare)
            as [ | | (min2, max2)] eqn : C_check_ord_hbt2.

          (* hbt2 is unordered *)
          rewrite -> unfold_traverse_to_check_ordered_t in H_ord_t.
          rewrite -> C_check_ord_hbt1 in H_ord_t.
          rewrite -> C_check_ord_hbt2 in H_ord_t.
          discriminate.

          (* hbt2 is a leaf: use lemmas defined earlier *)
          rewrite -> unfold_traverse_to_check_ordered_t in H_ord_t.
          rewrite -> C_check_ord_hbt1 in H_ord_t.
          rewrite -> C_check_ord_hbt2 in H_ord_t.

          assert (H_equalities:
                    min_hbt' = x /\ max_hbt' = x).
          exact (insertion_in_leaf_min_max
                   A compare
                   hbt2
                   (HNode A h2' bt2')
                   x min_hbt' max_hbt'
                   C_insert_hbt2
                   C_check_ord_hbt'
                   C_check_ord_hbt2).

          case (compare e min_hbt') as [ | | ].
          rewrite -> tsome_x_equal_tsome_y in H_ord_hbt'.
          rewrite -> tsome_x_equal_tsome_y in H_ord_t.
          rewrite -> pairwise_equality in H_ord_hbt'.
          rewrite -> pairwise_equality in H_ord_t.
          split.
          
          destruct H_ord_hbt' as [_ H_t_max'_max'_hbt].
          destruct H_equalities as [_ H_max'_hbt_x].
          apply or_introl.
          rewrite -> H_max'_hbt_x in H_t_max'_max'_hbt.
          rewrite -> H_t_max'_max'_hbt.
          reflexivity.
          
          destruct H_ord_hbt' as [H_min_hbt' _].
          destruct H_ord_t as [H_t_min _].
          apply or_intror.
          rewrite -> H_t_min in H_min_hbt'.
          rewrite -> H_min_hbt'.
          reflexivity.

          discriminate.
          discriminate.
          
          (* hbt2 is a node: make use of inductive hypothesis *)
          case (compare e min_hbt') as [ | | ].

          assert (H_equals_trivial:
                    TSome (A * A) (min2, max2) = TSome (A * A) (min2, max2)).
          reflexivity.
          
          assert (H_equalities_from_ind_h :
                    (max_hbt' = x \/ max_hbt' = max2) /\ (min_hbt' = x \/ min_hbt' = min2)).
          exact (H_hbt2 (HNode A h2' bt2')
                        x min2 min_hbt' max2 max_hbt'
                        C_insert_hbt2
                        C_check_ord_hbt'
                        H_equals_trivial).

          rewrite -> unfold_traverse_to_check_ordered_t in H_ord_t.
          rewrite -> C_check_ord_hbt1 in H_ord_t.
          rewrite -> C_check_ord_hbt2 in H_ord_t.
          case (compare e min2) as [ | | ].
          
          (* Note: (A \/ B) -> C <-> (A -> C) /\ (B -> C). So the following 
           * destruct will necessitate two proofs, one with A as the hypothesis,
           * and one with B *)
          destruct H_equalities_from_ind_h as [[H_max_x | H_max_max1] _].

          (* H_max_x *)
          rewrite -> tsome_x_equal_tsome_y in H_ord_t.
          rewrite -> tsome_x_equal_tsome_y in H_ord_hbt'.
          rewrite -> pairwise_equality in H_ord_t.
          rewrite -> pairwise_equality in H_ord_hbt'.
          destruct H_ord_hbt' as [H_min_hbt' H_t_max'].
          destruct H_ord_t as [H_e _].
          split.
          
          apply or_introl.
          rewrite <- H_t_max'.
          exact H_max_x.
          
          apply or_intror.
          rewrite -> H_min_hbt' in H_e.
          exact H_e.

          (* H_max_max1 *)
          rewrite -> tsome_x_equal_tsome_y in H_ord_hbt'.
          rewrite -> tsome_x_equal_tsome_y in H_ord_t.
          rewrite -> pairwise_equality in H_ord_hbt'.
          rewrite -> pairwise_equality in H_ord_t.
          destruct H_ord_hbt' as [H_t_min'  H_t_max'].
          destruct H_ord_t as [H_t_min H_t_max].
          
          split.
          apply or_intror.
          rewrite -> H_max_max1 in H_t_max'.
          rewrite -> H_t_max' in H_t_max.
          exact H_t_max.
          
          apply or_intror.
          rewrite <- H_t_min.
          rewrite <- H_t_min'.
          reflexivity.

          discriminate.
          discriminate.
          discriminate.
          discriminate.
        }

        (* hbt1 is a node *)
        {
          case (compare max1 e) as [ | | ] eqn : C_comp_max1_e.
          case (compare e min_hbt') as [ | | ] eqn : C_comp_e_min_hbt'.
          
          rewrite -> unfold_traverse_to_check_ordered_t in H_ord_t.
          rewrite -> C_check_ord_hbt1 in H_ord_t.
          rewrite -> C_comp_max1_e in H_ord_t.

          case (traverse_to_check_ordered_hbt A hbt2 compare)
            as [ | | (min2, max2)] eqn : C_check_ord_hbt2.

          (* hbt2 is unordered *)
          discriminate.

          (* hbt2 is a leaf: use lemmas defined earlier *)
          assert (H_equalities:
                    min_hbt' = x /\ max_hbt' = x).
          exact (insertion_in_leaf_min_max
                   A compare
                   hbt2
                   (HNode A h2' bt2')
                   x min_hbt' max_hbt'
                   C_insert_hbt2
                   C_check_ord_hbt'
                   C_check_ord_hbt2).

          rewrite -> tsome_x_equal_tsome_y in H_ord_hbt'.
          rewrite -> tsome_x_equal_tsome_y in H_ord_t.
          rewrite -> pairwise_equality in H_ord_hbt'.
          rewrite -> pairwise_equality in H_ord_t.
          split.
          
          destruct H_ord_hbt' as [_ H_t_max'_max'_hbt].
          destruct H_equalities as [_ H_max'_hbt_x].
          apply or_introl.
          rewrite -> H_max'_hbt_x in H_t_max'_max'_hbt.
          rewrite -> H_t_max'_max'_hbt.
          reflexivity.
          
          destruct H_ord_hbt' as [H_min_hbt' _].
          destruct H_ord_t as [H_t_min _].
          apply or_intror.
          rewrite -> H_t_min in H_min_hbt'.
          rewrite -> H_min_hbt'.
          reflexivity.
          
          (* hbt2 is a node: make use of inductive hypothesis *)
          case (compare e min2) as [ | | ] eqn : C_comp_e_min2.
          
          assert (H_equals_trivial:
                    TSome (A * A) (min2, max2) = TSome (A * A) (min2, max2)).
          reflexivity.
          
          assert (H_equalities_from_ind_h :
                    (max_hbt' = x \/ max_hbt' = max2) /\ (min_hbt' = x \/ min_hbt' = min2)).
          exact (H_hbt2 (HNode A h2' bt2')
                        x min2 min_hbt' max2 max_hbt'
                        C_insert_hbt2
                        C_check_ord_hbt'
                        H_equals_trivial).
          
          (* Note: (A \/ B) -> C <-> (A -> C) /\ (B -> C). So the following 
           * destruct will necessitate two proofs, one with A as the hypothesis,
           * and one with B *)
          destruct H_equalities_from_ind_h as [[H_max_x | H_max_max1] _].

          (* H_max_x *)
          rewrite -> tsome_x_equal_tsome_y in H_ord_t.
          rewrite -> tsome_x_equal_tsome_y in H_ord_hbt'.
          rewrite -> pairwise_equality in H_ord_t.
          rewrite -> pairwise_equality in H_ord_hbt'.
          destruct H_ord_hbt' as [H_min_hbt' H_t_max'].
          destruct H_ord_t as [H_e _].
          split.
          
          apply or_introl.
          rewrite <- H_t_max'.
          exact H_max_x.
          
          apply or_intror.
          rewrite -> H_min_hbt' in H_e.
          exact H_e.
          
          (* H_max_max1 *)
          rewrite -> tsome_x_equal_tsome_y in H_ord_hbt'.
          rewrite -> tsome_x_equal_tsome_y in H_ord_t.
          rewrite -> pairwise_equality in H_ord_hbt'.
          rewrite -> pairwise_equality in H_ord_t.
          destruct H_ord_hbt' as [H_t_min'  H_t_max'].
          destruct H_ord_t as [H_t_min H_t_max].
          
          split.
          apply or_intror.
          rewrite -> H_max_max1 in H_t_max'.
          rewrite -> H_t_max' in H_t_max.
          exact H_t_max.
          
          apply or_intror.
          rewrite <- H_t_min.
          rewrite <- H_t_min'.
          reflexivity.
          
          discriminate.
          discriminate.
          discriminate.
          discriminate.
          discriminate.
          discriminate.
        }

    (* height difference is 2: rotation required *)
    + unfold rotate_left_hbt in H_insert_hbt. 
      induction hbt1 as [h1 bt1].
      unfold rotate_left_bt in H_insert_hbt.
      case bt2' as [ | t2'].

      (* bt2' is a leaf: impossible case *)
      discriminate.

      (* bt2' is a node *)
      induction t2' as [hbt21' e2 hbt22'].
      induction hbt21' as [h21' bt21'].
      induction hbt22' as [h22' bt22'].
      
      (* required also for the inductive hypothesis: hbt2 is ordered *)
      Check (triple_ordered_implies_hbts_ordered).
      
      assert (H_fold_t_ord:
                is_ordered_hbt A (HNode A h (Node A ((Triple A (HNode A h1 bt1) e hbt2))))
                               compare = true).
      unfold is_ordered_hbt.
      rewrite -> unfold_traverse_to_check_ordered_hbt. 
      rewrite -> unfold_traverse_to_check_ordered_bt_node.     
      rewrite -> H_ord_t.
      reflexivity.
      
      destruct (triple_ordered_implies_hbts_ordered
                  A compare h (HNode A h1 bt1) e hbt2 H_fold_t_ord)
        as [H_hbt1_is_ord H_hbt2_is_ord]. 

      case (h22' + 1 =n= h21') as [ | ] eqn : C_h22'_h21'.
      
      (* h22' + 1 = h21' *)
      * case bt21' as [ | t21'].
         
        discriminate.
        
        (* destruct bt12 as required *)
        induction t21' as [hbt211' e21 hbt212'].
        induction hbt211' as [h211' bt211'].
        induction hbt212' as [h212' bt212'].
        rewrite -> some_x_equal_some_y in H_insert_hbt. 
        rewrite <- H_insert_hbt in H_ord_hbt'.  
        
      (* crucial assertion to use inductive hypothesis: the tree returned after insertion and
       * before rotation is also ordered *)
        Check (rotate_left_1_tree_ordered_implies_returned_tree_ordered).
        destruct (rotate_left_1_tree_ordered_implies_returned_tree_ordered
                    A
                    compare
                    h1 h211' h212' h22' h2' h21'
                    bt1 bt211' bt212' bt22'
                    e e21 e2 t_min' t_max'
                    H_ord_hbt') as [t_min'' H_traverse_ord_hbt_ret_org].
      
      (* work through base cases for traverse_to_check_ordered_hbt hbt1 until we get to the 
       * point where it is a node *)
      unfold is_ordered_hbt in H_hbt2_is_ord.
      case (traverse_to_check_ordered_hbt A hbt2 compare)
        as [ | | (min2, max2)] eqn : C_traverse_ord_hbt2.
      discriminate.
      
      induction hbt2 as [h2 bt2].
      
      assert (H_impossible_hbt2 : bt2 <> Leaf A).
      Check (rotate_left_1_impossible_case).
      exact (rotate_left_1_impossible_case
               A compare
               x h2 bt2 h2' h21' h211' h212' h22'
               bt211' bt212' bt22'
               e21 e2
               C_insert_hbt2).
      
      rewrite -> unfold_traverse_to_check_ordered_hbt in C_traverse_ord_hbt2.
      induction bt2 as [ | t2].
      rewrite -> unfold_traverse_to_check_ordered_bt_leaf in C_traverse_ord_hbt2.      
      unfold not in H_impossible_hbt2.
      assert (H_trivial_leaf : Leaf A = Leaf A).
      reflexivity.
      apply H_impossible_hbt2 in H_trivial_leaf.
      discriminate.
      Check (traverse_node_impossible_case).
      apply traverse_node_impossible_case in C_traverse_ord_hbt2.
      apply False_ind.
      exact C_traverse_ord_hbt2.
      
      (* finally, we have what is required to apply the inductive hypothesis *)
      assert (H_trivial_equality:
                TSome (A * A) (min2, max2) = TSome (A * A) (min2, max2)).
      reflexivity.

      destruct (H_hbt2
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
                  x min2 t_min'' max2 t_max'
                  C_insert_hbt2
                  H_traverse_ord_hbt_ret_org
                  H_trivial_equality) as [H_t_max' _].
      Check (rotate_left_1_min_max).
      exact (rotate_left_1_min_max
               A
               compare
               h1 h211' h212' h22'
               bt1 bt211' bt212' bt22'
               e e21 e2
               hbt2
               t_min' t_max' t_min t_max min2 max2 x 
               H_ord_hbt'
               H_ord_t
               C_traverse_ord_hbt2
               H_t_max').

      * case (h21' + 1 =n= h22') as [ | ] eqn : C_h21'_h22'.
        rewrite -> some_x_equal_some_y in H_insert_hbt.
        rewrite <- H_insert_hbt in H_ord_hbt'.

      (* important lemma: assert that the returned tree is ordered to 
       * use inductive hypothesis *)
      Check (rotate_left_2_tree_ordered_implies_returned_tree_ordered).
      destruct (rotate_left_2_tree_ordered_implies_returned_tree_ordered
                  A compare
                  h1 h21' h22' h2'
                  bt1 bt21' bt22' 
                  e e2 t_min' t_max'
                  H_ord_hbt') as [t_min'' H_traverse_ord_hbt_ret_org].

      (* work through base cases for traverse_to_check_ordered_hbt hbt1 until we get to the 
       * point where it is a node *)
      unfold is_ordered_hbt in H_hbt2_is_ord.
      case (traverse_to_check_ordered_hbt A hbt2 compare)
        as [ | | (min2, max2)] eqn : C_traverse_ord_hbt2.
      discriminate.
      
      induction hbt2 as [h2 bt2].
      
      assert (H_impossible_hbt2 : bt2 <> Leaf A).
      Check (rotate_left_2_impossible_case).
      exact (rotate_left_2_impossible_case
               A compare x h2 bt2
               h2' h21' h22'
               bt21' bt22' e2
               C_insert_hbt2
               C_h21'_h22').
      
      rewrite -> unfold_traverse_to_check_ordered_hbt in C_traverse_ord_hbt2.
      induction bt2 as [ | t2].
      rewrite -> unfold_traverse_to_check_ordered_bt_leaf in C_traverse_ord_hbt2.      
      unfold not in H_impossible_hbt2.
      assert (H_trivial_leaf : Leaf A = Leaf A).
      reflexivity.
      apply H_impossible_hbt2 in H_trivial_leaf.
      apply False_ind.
      exact H_trivial_leaf.
      unfold not in H_impossible_hbt2.
      apply traverse_node_impossible_case in C_traverse_ord_hbt2.
      apply False_ind.
      exact C_traverse_ord_hbt2.
      
      (* finally, we have what is required to apply the inductive hypothesis *)
      assert (H_trivial_equality:
                TSome (A * A) (min2, max2) = TSome (A * A) (min2, max2)).
      reflexivity.
      
      destruct (H_hbt2
                  (HNode A h2'
                         (Node A (Triple A (HNode A h21' bt21') e2 (HNode A h22' bt22'))))
                  x min2 t_min'' max2 t_max'
                  C_insert_hbt2
                  H_traverse_ord_hbt_ret_org
                  H_trivial_equality) as [H_t_max' _].
      Check (rotate_left_2_min_max).
      exact (rotate_left_2_min_max
               A compare
               h1 h21' h22'
               bt1 bt21' bt22'
               e e2
               hbt2
               t_min' t_max' t_min t_max min2 max2
               x
               H_ord_hbt'
               H_ord_t
               C_traverse_ord_hbt2
               H_t_max').

      discriminate.

    + discriminate.

    + discriminate.
Qed.


(* ***** *)

(* ***** Section 5.7 Lemmas concerning rotations ***** *)
Lemma rotate_right_preserves_soundness:
  forall (A : Type)
         (h_ret : nat)
         (bt_ret : binary_tree A)
         (e : A) 
         (hbt2 : heightened_binary_tree A) 
         (hbt' : heightened_binary_tree A), 
    is_sound_hbt A (HNode A h_ret bt_ret) = true ->
    is_sound_hbt A hbt2 = true -> 
    rotate_right_hbt A (HNode A h_ret bt_ret) e hbt2 = Some hbt' ->
    is_sound_hbt A hbt' = true.
Proof.
Admitted.

Lemma rotate_left_preserves_soundness:
  forall (A : Type)
         (hbt1 : heightened_binary_tree A)
         (e : A)
         (h_ret : nat)
         (bt_ret : binary_tree A)
         (hbt' : heightened_binary_tree A),
    is_sound_hbt A hbt1 = true -> 
    is_sound_hbt A (HNode A h_ret bt_ret) = true ->
    rotate_left_hbt A hbt1 e (HNode A h_ret bt_ret) = Some hbt' -> 
    is_sound_hbt A hbt' = true.
Proof.
Admitted.


Lemma rotate_right_preserves_balance:
  forall (A : Type)
         (h_ret : nat)
         (bt_ret : binary_tree A)
         (e : A)
         (hbt2 : heightened_binary_tree A)
         (hbt' : heightened_binary_tree A),
    is_balanced_hbt A (HNode A h_ret bt_ret) = true ->
    is_balanced_hbt A hbt2 = true ->
    is_sound_hbt A (HNode A h_ret bt_ret) = true ->
    is_sound_hbt A hbt2 = true -> 
    rotate_right_hbt A (HNode A h_ret bt_ret) e hbt2 = Some hbt' ->
    is_balanced_hbt A hbt' = true.
Proof.
Admitted.

Lemma rotate_left_preserves_balance:
  forall (A : Type)
         (hbt1 : heightened_binary_tree A)
         (e : A)
         (h_ret : nat)
         (bt_ret : binary_tree A)
         (hbt' : heightened_binary_tree A),
    is_balanced_hbt A hbt1 = true -> 
    is_balanced_hbt A (HNode A h_ret bt_ret) = true ->
    is_sound_hbt A hbt1 = true -> 
    is_sound_hbt A (HNode A h_ret bt_ret) = true ->
    rotate_left_hbt A hbt1 e (HNode A h_ret bt_ret) = Some hbt' -> 
    is_balanced_hbt A hbt' = true.
Proof.
Admitted.

Lemma rotate_right_preserves_order:
  forall (A : Type)
         (compare : A -> A -> element_comparison)
         (h_hbt : nat)
         (hbt1 : heightened_binary_tree A)
         (e : A)
         (hbt2 : heightened_binary_tree A)
         (h_ret : nat)
         (bt_ret : binary_tree A)
         (hbt' : heightened_binary_tree A),
    is_ordered_hbt A (HNode A h_hbt (Node A (Triple A hbt1 e hbt2))) compare = true -> 
    is_ordered_hbt A (HNode A h_ret bt_ret) compare = true ->
    is_ordered_hbt A hbt2 compare = true ->
    rotate_right_hbt A (HNode A h_ret bt_ret) e hbt2 = Some hbt' ->
    is_ordered_hbt A hbt' compare = true.
Proof.
Admitted.

Lemma rotate_left_preserves_order:
  forall (A : Type)
         (compare : A -> A -> element_comparison)
         (h_hbt : nat)
         (hbt1 : heightened_binary_tree A)
         (e : A)
         (hbt2 : heightened_binary_tree A)
         (h_ret : nat)
         (bt_ret : binary_tree A)
         (hbt' : heightened_binary_tree A),
    is_ordered_hbt A (HNode A h_hbt (Node A (Triple A hbt1 e hbt2))) compare = true ->     
    is_ordered_hbt A hbt1 compare = true -> 
    is_ordered_hbt A (HNode A h_ret bt_ret) compare = true ->
    rotate_left_hbt A hbt1 e (HNode A h_ret bt_ret) = Some hbt' -> 
    is_ordered_hbt A hbt' compare = true.
Proof.
Admitted.





(* Admitted.  *)


