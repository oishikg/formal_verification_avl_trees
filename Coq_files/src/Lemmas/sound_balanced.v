Require Import Hbt.Implementation.hbt.
Require Export Hbt.Implementation.hbt.

(* ********** Lemmas concerning soundness ********** *)

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

Lemma soundness_implies_some_height:
  forall (A : Type)
         (h : nat)
         (bt : binary_tree A),
    is_sound_hbt A (HNode A h bt) = true ->
    traverse_to_check_soundness_hbt A (HNode A h bt) = Some h.
Proof.
  intros.
  unfold is_sound_hbt in H.
  rewrite -> unfold_traverse_to_check_soundness_hbt in H.
  case (traverse_to_check_soundness_bt A bt) as [h' | ] eqn : C_traverse_bt.
  case (h' =n= h) as [ | ] eqn: C_h'h.
  assert (H0 : h' = h).
  exact (beq_nat_true h' h C_h'h).
  rewrite -> unfold_traverse_to_check_soundness_hbt.
  rewrite -> C_traverse_bt.
  rewrite -> C_h'h.
  reflexivity.

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

(* ********** Lemmas concerning balancedness ********** *)

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

Lemma equal_heights:
  forall (h1 h2 : nat),
    (1 + max h1 h2 =n= 1 + max h1 h2) = true.
Proof.
  intros.
  
  case h1 as [ | h1'].
  case h2 as [ | h2'].
  
  unfold max.
  Search (_ + 0 = _).
  rewrite -> plus_0_r.
  unfold beq_nat.
  reflexivity.

  (* finish the proof *)
Admitted.


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
  intros.

  (* destruct and unfold *)
  unfold rotate_right_hbt in H1.
  induction hbt2 as [h2 bt2].
  unfold rotate_right_bt in H1.
  induction bt_ret as [ | t_ret].
  discriminate.
  induction t_ret as [[h11 bt11] e1 [h12 bt12]].
  case (h11 + 1 =n= h12) as [ | ].

  (* h11 + 1 = h12 *)
  induction bt12 as [ | [[h121 bt121] e12 [h122 bt122]]].

  (* bt12 is leaf : impossible case *)
  - discriminate.

  (* bt12 is node *)
  - rewrite -> some_x_equal_some_y in H1.
    rewrite <- H1.

    (* show that all the subtrees are sound *)
    Check (triple_sound_implies_hbts_sound).
    destruct (triple_sound_implies_hbts_sound
                A h_ret
                (HNode A h11 bt11) e1
                (HNode A h12 (Node A (Triple A (HNode A h121 bt121) e12 (HNode A h122 bt122))))
                H) as [H_bt11_sound H_right_subtree_sound].
    destruct (triple_sound_implies_hbts_sound
                A h12
                (HNode A h121 bt121)
                e12
                (HNode A h122 bt122) H_right_subtree_sound) as [ H_bt121_sound H_bt122_sound].

    (* now obtain the heights for the subtrees by unfolding *)
    Check (soundness_implies_some_height).
    assert (H_bt11_h11:
              traverse_to_check_soundness_hbt A (HNode A h11 bt11) = Some h11).
    exact (soundness_implies_some_height A h11 bt11 H_bt11_sound).

    assert (H_bt121_h121:
              traverse_to_check_soundness_hbt A (HNode A h121 bt121) = Some h121).
    exact (soundness_implies_some_height A h121 bt121 H_bt121_sound).

    assert (H_bt122_h122:
              traverse_to_check_soundness_hbt A (HNode A h122 bt122) = Some h122).
    exact (soundness_implies_some_height A h122 bt122 H_bt122_sound).

    assert (H_bt2_h2:
              traverse_to_check_soundness_hbt A (HNode A h2 bt2) = Some h2).
    exact (soundness_implies_some_height A h2 bt2 H0).

    (* unfold goal *)
    unfold is_sound_hbt.
    rewrite -> unfold_traverse_to_check_soundness_hbt.
    rewrite -> unfold_traverse_to_check_soundness_bt_node.
    rewrite -> unfold_traverse_to_check_soundness_t.
    rewrite -> unfold_traverse_to_check_soundness_hbt.
    rewrite -> unfold_traverse_to_check_soundness_bt_node.
    rewrite -> unfold_traverse_to_check_soundness_t.
    rewrite -> (unfold_traverse_to_check_soundness_hbt
                  A (1 + max h122 h2)
                  (Node A (Triple A (HNode A h122 bt122) e (HNode A h2 bt2)))).
    rewrite -> (unfold_traverse_to_check_soundness_bt_node
                  A (Triple A (HNode A h122 bt122) e (HNode A h2 bt2))).
    rewrite -> (unfold_traverse_to_check_soundness_t
                  A (HNode A h122 bt122) (HNode A h2 bt2) e).

    (* now rewrite the height hypotheses *)
    rewrite -> H_bt11_h11.                
    rewrite -> H_bt121_h121.            
    rewrite -> H_bt122_h122.        
    rewrite -> H_bt2_h2.
    (* finish the proof *)
Admitted.

(* ********** Lemmas concerning rotation ********** *)

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



Lemma insertion_preserves_soundness_and_balance: 
  forall (A : Type)
         (compare : A -> A -> element_comparison)
         (x : A),
    (forall (hbt : heightened_binary_tree A)
            (hbt' : heightened_binary_tree A),
        is_sound_hbt A hbt = true ->
        is_balanced_hbt A hbt = true ->        
        insert_hbt_helper A compare x hbt = Some hbt' ->
        is_sound_hbt A hbt' = true /\ is_balanced_hbt A hbt' = true)
    /\
    (forall (bt : binary_tree A)
            (h_hbt : nat)
            (hbt' : heightened_binary_tree A),    
        is_sound_hbt A (HNode A h_hbt bt) = true ->
        is_balanced_hbt A (HNode A h_hbt bt) = true ->                
        insert_bt_helper A compare x h_hbt bt = Some hbt' ->
        is_sound_hbt A hbt' = true /\ is_balanced_hbt A hbt' = true)
    /\
    (forall (t : triple A)
            (h_hbt : nat)
            (hbt' : heightened_binary_tree A),    
        is_sound_hbt A (HNode A h_hbt (Node A t)) = true ->
        is_balanced_hbt A (HNode A h_hbt (Node A t)) = true ->                        
        insert_t_helper A compare x h_hbt t = Some hbt' ->
        is_sound_hbt A hbt' = true /\ is_balanced_hbt A hbt' = true).
Proof.
  intros.
  apply heightened_binary_tree_mutual_induction.

  (* Specification for hbt holds, given bt as inductive case *)  
  - intros h bt H_bt_inductive_assumption hbt' H_sound_hbt_init H_bal_hbt_init H_insert_hbt.
    Check (H_bt_inductive_assumption h hbt' H_sound_hbt_init H_bal_hbt_init H_insert_hbt).
    exact (H_bt_inductive_assumption h hbt' H_sound_hbt_init H_bal_hbt_init H_insert_hbt).

    (* Specification for bt leaf constructor holds *)
  - intros h_hbt hbt' H_sound_bt_init H_bal_hbt_init H_insert_bt.
    rewrite -> (unfold_insert_bt_helper_leaf A compare x)
      in H_insert_bt.
    rewrite -> some_x_equal_some_y in H_insert_bt.
    rewrite <- H_insert_bt.

    split.

    (* prove soundness *)
    + unfold is_sound_hbt.
      rewrite -> unfold_traverse_to_check_soundness_hbt.
      rewrite -> unfold_traverse_to_check_soundness_bt_node.
      rewrite -> unfold_traverse_to_check_soundness_t.
      rewrite -> unfold_traverse_to_check_soundness_hbt.
      rewrite -> unfold_traverse_to_check_soundness_bt_leaf.
      unfold beq_nat at 1.
      unfold beq_nat at 1.
      unfold max at 1.
      Search (_ + 0 = _).
      rewrite -> (plus_0_r 1) at 1.
      unfold beq_nat at 1.
      reflexivity.

    (* prove balancedness *)
    + unfold is_balanced_hbt.
      rewrite -> unfold_traverse_to_check_balanced_hbt.
      rewrite -> unfold_traverse_to_check_balanced_bt_node.
      rewrite -> unfold_traverse_to_check_balanced_t.
      rewrite -> unfold_traverse_to_check_balanced_hbt.
      rewrite -> unfold_traverse_to_check_balanced_bt_leaf.
      unfold differ_by_one.
      rewrite -> (plus_0_l 1).
      unfold beq_nat.
      unfold max.
      rewrite -> (plus_0_r 1).
      (* why does the boolean statement not evaluate here? *)
        reflexivity.


    (* Specification for bt with node constructor holds, given t as inductive case *)
  - intros t H_t_inductive_assumption h_hbt hbt' H_sound_bt_init H_bal_bt_init H_insert_bt.
    exact (H_t_inductive_assumption h_hbt hbt' H_sound_bt_init H_bal_bt_init H_insert_bt).
    
  (* Specification for t holds, given hbt as inductive case *)    
  - intros hbt1 H_hbt1_inductive_assumption
           e
           hbt2 H_hbt2_inductive_assumption
           h_hbt hbt'
           H_sound_t_init H_bal_t_init H_insert_t.
    
    (* Before working on the particular subgoals, assert some essential 
     * hypotheses *)
    destruct (triple_sound_implies_hbts_sound
                A h_hbt hbt1 e hbt2 H_sound_t_init) as [H_hbt1_is_sound H_hbt2_is_sound].
    destruct (triple_balanced_implies_hbts_balanced
                A h_hbt hbt1 e hbt2 H_bal_t_init) as [H_hbt1_is_balanced H_hbt2_is_balanced].
    
        rewrite -> (unfold_insert_t_helper A compare x h_hbt hbt1 e hbt2)
      in H_insert_t.
    (* Element to be inserted is Lt current element considered *)
    case (compare x e) as [ | | ] eqn : C_comp.

    (* Case 1: x <e *)
    + case (insert_hbt_helper A compare x hbt1) as [hbt_ret | ] eqn : C_insert_hbt1.
      induction hbt_ret as [h_ret bt_ret].

      (* Trivial hypothesis required to use other hypotheses *)
      assert (P_some_eq : Some (HNode A h_ret bt_ret) =
                          Some (HNode A h_ret bt_ret)).
      reflexivity. 

      case (compare_int (h_ret - project_height_hbt A hbt2) 2)
        as [ | | ] eqn : C_height_diff.

      (* The insertion does not unbalance the tree *) 
      *  unfold beq_nat in H_insert_t.
        apply (some_x_equal_some_y
                 (heightened_binary_tree A)
                 (HNode A (1 + max h_ret (project_height_hbt A hbt2))
                        (Node A (Triple A (HNode A h_ret bt_ret) e hbt2)))
                 hbt') in H_insert_t.
        rewrite <- H_insert_t.

        split.
        
        (* The resultant tree is sound *)
        {
          destruct (H_hbt1_inductive_assumption (HNode A h_ret bt_ret)
                                                H_hbt1_is_sound
                                                H_hbt1_is_balanced
                                                P_some_eq) as
              [H_hbt_ret_is_sound _].
          assert (P_relating_heights :
                    (1 + max h_ret (project_height_hbt A hbt2)) =
                    (1 + max (project_height_hbt A (HNode A h_ret bt_ret))
                             (project_height_hbt A hbt2))).
          unfold project_height_hbt at 2.
          reflexivity.
          exact (hbts_sound_implies_triple_sound_weak
                   A
                   (1 + max h_ret (project_height_hbt A hbt2))
                   (HNode A h_ret bt_ret)
                   e
                   hbt2
                   H_hbt_ret_is_sound
                   H_hbt2_is_sound
                   P_relating_heights).
        }

        (* The resultant tree is balanced *)
        {
          destruct (H_hbt1_inductive_assumption (HNode A h_ret bt_ret)
                                                H_hbt1_is_sound
                                                H_hbt1_is_balanced
                                                P_some_eq) as
              [_ H_hbt_ret_is_balanced].
          destruct (H_hbt1_inductive_assumption (HNode A h_ret bt_ret)
                                                H_hbt1_is_sound
                                                H_hbt1_is_balanced
                                                P_some_eq) as
              [H_hbt_ret_is_sound _].
          assert (H_hbts_balanced_triple_balanced_with_da:
                    compare_int (project_height_hbt A (HNode A h_ret bt_ret) -
                                 project_height_hbt A hbt2) 2 = Lt
                    \/
                    compare_int (project_height_hbt A hbt2 -
                                 project_height_hbt A (HNode A h_ret bt_ret)) 2 =
                    Lt ->
                    is_balanced_hbt
                      A
                      (HNode A (1 + max h_ret (project_height_hbt A hbt2))
                             (Node A (Triple A (HNode A h_ret bt_ret) e hbt2))) =
                    true).
          exact (hbts_balanced_implies_triple_balanced_weak
                   A
                   (1 + max h_ret (project_height_hbt A hbt2))
                   (HNode A h_ret bt_ret)
                   e
                   hbt2
                   H_hbt_ret_is_balanced
                   H_hbt2_is_balanced
                   H_hbt_ret_is_sound
                   H_hbt2_is_sound).
          destruct (or_implication
                      (compare_int
                         (project_height_hbt A (HNode A h_ret bt_ret) -
                          project_height_hbt A hbt2) 2 = Lt)
                      (compare_int
                         (project_height_hbt A hbt2 -
                          project_height_hbt A (HNode A h_ret bt_ret)) 2 = Lt)
                      (is_balanced_hbt
                         A
                         (HNode A (1 + max h_ret (project_height_hbt A hbt2))
                                (Node A (Triple A (HNode A h_ret bt_ret) e hbt2)))
                       = true)
                      H_hbts_balanced_triple_balanced_with_da)
            as [H_we_need_12  H_we_need_21].
          exact (H_we_need_12 C_height_diff).
        }

      (* the insertion unbalances the tree: rotations required *) 
      * Check (H_hbt1_inductive_assumption
                 (HNode A h_ret bt_ret)
                 H_hbt1_is_sound H_hbt1_is_balanced P_some_eq).
        destruct (H_hbt1_inductive_assumption
                    (HNode A h_ret bt_ret)
                    H_hbt1_is_sound H_hbt1_is_balanced P_some_eq)
          as [H_hbt_ret_sound H_hbt_ret_balanced].
        split.

        (* rotated tree is sound *)        
        {
          Check (rotate_right_preserves_soundness).
          Check (rotate_right_preserves_soundness
                   A h_ret bt_ret e hbt2 hbt'
                   H_hbt_ret_sound H_hbt2_is_sound H_insert_t).
          exact (rotate_right_preserves_soundness
                   A h_ret bt_ret e hbt2 hbt'
                   H_hbt_ret_sound H_hbt2_is_sound H_insert_t).
        }

        (* rotated tree is balanced *)
        {
          Check (rotate_right_preserves_balance).
          Check (rotate_right_preserves_balance
                   A h_ret bt_ret e hbt2 hbt'
                   H_hbt_ret_balanced H_hbt2_is_balanced
                   H_hbt_ret_sound H_hbt2_is_sound H_insert_t).
          exact (rotate_right_preserves_balance
                   A h_ret bt_ret e hbt2 hbt'
                   H_hbt_ret_balanced H_hbt2_is_balanced
                   H_hbt_ret_sound H_hbt2_is_sound H_insert_t).
        }

      * discriminate.

      * discriminate.

    + discriminate.

    (* Case 3: x > e *)      
    + case (insert_hbt_helper A compare x hbt2) as [hbt_ret | ] eqn : C_insert_hbt2.
      induction hbt_ret as [h_ret bt_ret].

      (* Trivial hypothesis required to use other hypotheses *)
      assert (P_some_eq : Some (HNode A h_ret bt_ret) =
                          Some (HNode A h_ret bt_ret)).
      reflexivity. 

      case (compare_int (h_ret - project_height_hbt A hbt1) 2)
        as [ | | ] eqn : C_height_diff.

      (* The insertion does not unbalance the tree *) 
      * unfold beq_nat in H_insert_t.
        rewrite -> some_x_equal_some_y in H_insert_t.
        rewrite <- H_insert_t.

        split.

        (* The resultant tree is sound *)
        {
          destruct (H_hbt2_inductive_assumption (HNode A h_ret bt_ret)
                                                H_hbt2_is_sound
                                                H_hbt2_is_balanced
                                                P_some_eq) as
              [H_hbt_ret_is_sound _].
          
          assert (P_relating_heights :
                    (1 + max (project_height_hbt A hbt1) h_ret) =
                    (1 + max (project_height_hbt A hbt1)
                             (project_height_hbt A (HNode A h_ret bt_ret)))).
          unfold project_height_hbt at 3.
          reflexivity.

          Check (hbts_sound_implies_triple_sound_weak).
          exact (hbts_sound_implies_triple_sound_weak
                   A
                   (1 + max (project_height_hbt A hbt1) h_ret)
                   hbt1
                   e
                   (HNode A h_ret bt_ret)
                   H_hbt1_is_sound
                   H_hbt_ret_is_sound
                   P_relating_heights).
        }
        
        (* The resultant tree is balanced *)
        {
          destruct (H_hbt2_inductive_assumption (HNode A h_ret bt_ret)
                                                H_hbt2_is_sound
                                                H_hbt2_is_balanced
                                                P_some_eq) as
              [_ H_hbt_ret_is_balanced].
          destruct (H_hbt2_inductive_assumption (HNode A h_ret bt_ret)
                                                H_hbt2_is_sound
                                                H_hbt2_is_balanced
                                                P_some_eq) as
              [H_hbt_ret_is_sound _].
          assert (H_hbts_balanced_triple_balanced_with_da:
                    compare_int (project_height_hbt A hbt1 -
                                 project_height_hbt A (HNode A h_ret bt_ret)) 2 = Lt
                    \/
                    compare_int (project_height_hbt A (HNode A h_ret bt_ret) -
                                 project_height_hbt A hbt1) 2 = Lt
                    ->
                    is_balanced_hbt
                      A
                      (HNode A (1 + max (project_height_hbt A hbt2) h_ret)
                             (Node A (Triple A hbt1 e (HNode A h_ret bt_ret)))) =
                    true). 
          Check (hbts_balanced_implies_triple_balanced_weak).
          exact (hbts_balanced_implies_triple_balanced_weak
                   A
                   (1 + max (project_height_hbt A hbt2) h_ret)
                   hbt1
                   e
                   (HNode A h_ret bt_ret)
                   H_hbt1_is_balanced
                   H_hbt_ret_is_balanced
                   H_hbt1_is_sound
                   H_hbt_ret_is_sound).
          destruct (or_implication
                      (compare_int
                         (project_height_hbt A hbt1 -
                          project_height_hbt A (HNode A h_ret bt_ret)) 2 = Lt)
                      (compare_int
                         (project_height_hbt A (HNode A h_ret bt_ret) -
                          project_height_hbt A hbt1) 2 = Lt)
                      (is_balanced_hbt
                         A
                         (HNode A (1 + max (project_height_hbt A hbt1) h_ret)
                                (Node A (Triple A hbt1 e (HNode A h_ret bt_ret)))) = true)
                      H_hbts_balanced_triple_balanced_with_da) 
            as [H_we_need_12  H_we_need_21].
          exact (H_we_need_21 C_height_diff).
        }

      (* the insertion unbalances the tree: rotations required *) 
      * Check (H_hbt2_inductive_assumption
                 (HNode A h_ret bt_ret)
                 H_hbt2_is_sound H_hbt2_is_balanced P_some_eq).
        destruct (H_hbt2_inductive_assumption
                    (HNode A h_ret bt_ret)
                    H_hbt2_is_sound H_hbt2_is_balanced P_some_eq)
          as [H_hbt_ret_sound H_hbt_ret_balanced].
        split.

        (* rotated tree is sound *)
        {
          Check (rotate_left_preserves_soundness).
          Check (rotate_left_preserves_soundness
                   A hbt1 e h_ret bt_ret hbt'
                   H_hbt1_is_sound H_hbt_ret_sound H_insert_t).
          exact (rotate_left_preserves_soundness
                   A hbt1 e h_ret bt_ret hbt'
                   H_hbt1_is_sound H_hbt_ret_sound H_insert_t).
        }

        (* rotated tree is balanced *)
        {
          Check (rotate_left_preserves_balance).
          Check (rotate_left_preserves_balance
                   A hbt1 e h_ret bt_ret hbt'
                   H_hbt1_is_balanced H_hbt_ret_balanced
                   H_hbt1_is_sound H_hbt_ret_sound H_insert_t).
          exact (rotate_left_preserves_balance
                   A hbt1 e h_ret bt_ret hbt'
                   H_hbt1_is_balanced H_hbt_ret_balanced
                   H_hbt1_is_sound H_hbt_ret_sound H_insert_t).
        }

      * discriminate.

      * discriminate.
Qed.