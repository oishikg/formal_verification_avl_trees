(* Imports: *)
Require Import Hbt.Lemmas.lemmas.


(* ***** Section 5.3: The specifications  ***** *)
Check (element_comparison).

Definition specification_of_insert_hbt_helper
           (A : Type)
           (compare : A -> A -> element_comparison)
           (x : A)
           (insert_hbt_helper : forall (A' : Type),
               (A' -> A' -> element_comparison)
               -> A'
               -> heightened_binary_tree A'
               -> option (heightened_binary_tree A')) :=
  forall (hbt hbt' : heightened_binary_tree A),
    is_sound_hbt A hbt = true ->
    is_balanced_hbt A hbt = true ->
    is_ordered_hbt A hbt compare = true -> 
    insert_hbt_helper A compare x hbt = Some hbt' ->
    (is_sound_hbt A hbt' = true)
    /\ 
    (is_balanced_hbt A hbt' = true)
    /\
    (is_ordered_hbt A hbt' compare = true).


Definition specification_of_insert_bt_helper 
           (A : Type)
           (compare : A -> A -> element_comparison)
           (x : A)
           (insert_bt_helper : forall (A' : Type),
               (A' -> A' -> element_comparison)
               -> A'
               -> nat
               -> binary_tree A'
               -> option (heightened_binary_tree A')) :=
  forall (bt : binary_tree A)
         (h_hbt : nat)
         (hbt' : heightened_binary_tree A),
    is_sound_hbt A (HNode A h_hbt bt) = true ->
    is_balanced_hbt A (HNode A h_hbt bt) = true ->
    is_ordered_hbt A (HNode A h_hbt bt) compare = true ->
    insert_bt_helper A compare x h_hbt bt = Some hbt' ->
    (is_sound_hbt A hbt' = true)
    /\
    (is_balanced_hbt A hbt' = true)
    /\
    (is_ordered_hbt A hbt' compare = true).

Definition specification_of_insert_t_helper
           (A : Type)
           (compare : A -> A -> element_comparison)
           (x : A)
           (insert_t_helper : forall (A' : Type),
               (A' -> A' -> element_comparison)
               -> A'
               -> nat
               -> triple A'
               -> option (heightened_binary_tree A')) :=
  forall (t : triple A)
         (h_hbt : nat)
         (hbt' : heightened_binary_tree A),
    is_sound_hbt A (HNode A h_hbt (Node A t)) = true ->
    is_balanced_hbt A (HNode A h_hbt (Node A t)) = true ->
    is_ordered_hbt A (HNode A h_hbt (Node A t)) compare = true ->
    insert_t_helper A compare x h_hbt t = Some hbt' ->
    (is_sound_hbt A hbt' = true)
    /\
    (is_balanced_hbt A hbt' = true)
    /\
    (is_ordered_hbt A hbt' compare = true).

(* ***** *)




  
(* ***** 
        SECTION 5.7: The main theorem: implementations meet their specifications
 * *****)


Lemma the_helper_functions_meet_their_specifications:
  forall (A : Type)
         (compare : A -> A -> element_comparison)
         (x : A),
    (specification_of_insert_hbt_helper A compare x insert_hbt_helper)
    /\
    (specification_of_insert_bt_helper A compare x insert_bt_helper)
    /\
    (specification_of_insert_t_helper A compare x insert_t_helper).
Proof.
  intros A compare x.
  unfold specification_of_insert_hbt_helper.
  unfold specification_of_insert_bt_helper.
  unfold specification_of_insert_t_helper.
  apply heightened_binary_tree_mutual_induction.
  
  (* Specification for hbt holds, given bt as inductive case *)
  {
    intros h bt H_bt_inductive_assumption hbt' H_sound_hbt_init
           H_bal_hbt_init H_ord_hbt_init H_insert_hbt.
    split.
    Check (H_bt_inductive_assumption h hbt' H_sound_hbt_init H_bal_hbt_init H_ord_hbt_init H_insert_hbt).
    destruct (H_bt_inductive_assumption h hbt' H_sound_hbt_init H_bal_hbt_init H_ord_hbt_init H_insert_hbt) as [H_sound _].
    exact H_sound.

    split.
    destruct (H_bt_inductive_assumption h hbt' H_sound_hbt_init H_bal_hbt_init H_ord_hbt_init H_insert_hbt) as [_ [H_bal _]].
    exact H_bal.
    
    destruct (H_bt_inductive_assumption h hbt' H_sound_hbt_init H_bal_hbt_init H_ord_hbt_init H_insert_hbt) as [_ [_ H_ord]].
    exact H_ord.
  }
  
  (* Specification for bt leaf constructor holds *)
  {
    intros h_hbt hbt' H_sound_bt_init H_bal_bt_init H_ord_bt_init H_insert_bt.
    rewrite -> (unfold_insert_bt_helper_leaf A compare x)
      in H_insert_bt.
    rewrite -> some_x_equal_some_y in H_insert_bt.
    rewrite <- H_insert_bt.
     
    (* prove soundness *)
    - split.
      unfold is_sound_hbt.
      Check (unfold_traverse_to_check_soundness_hbt).
      rewrite ->
              (unfold_traverse_to_check_soundness_hbt
                 A
                 1
                 (Node A (Triple A (HNode A 0 (Leaf A)) x (HNode A 0 (Leaf A))))).
      Check (unfold_traverse_to_check_soundness_bt_node).
      rewrite ->
              (unfold_traverse_to_check_soundness_bt_node
                 A
                 (Triple A (HNode A 0 (Leaf A)) x (HNode A 0 (Leaf A)))).
      Check (unfold_traverse_to_check_soundness_t).
      rewrite ->
              (unfold_traverse_to_check_soundness_t
                 A
                 (HNode A 0 (Leaf A))
                 (HNode A 0 (Leaf A))
                 x).
      rewrite ->
              (unfold_traverse_to_check_soundness_hbt
                 A
                 0
                 (Leaf A)).
      Check (unfold_traverse_to_check_soundness_bt_leaf).
      rewrite -> (unfold_traverse_to_check_soundness_bt_leaf A).
      unfold beq_nat at 1.
      unfold beq_nat at 1.
      unfold max at 1.
      Search (_ + 0 = _).
      rewrite -> (plus_0_r 1) at 1.
      unfold beq_nat at 1.
      reflexivity.

      split.
      
      (* prove balancedness *)
      + unfold is_balanced_hbt.
        Check (unfold_traverse_to_check_balanced_hbt).
        rewrite ->
                (unfold_traverse_to_check_balanced_hbt
                   A
                   1
                   (Node A (Triple A (HNode A 0 (Leaf A)) x (HNode A 0 (Leaf A))))).
        Check (unfold_traverse_to_check_balanced_bt_node).
        rewrite ->
                (unfold_traverse_to_check_balanced_bt_node
                   A
                   (Triple A (HNode A 0 (Leaf A)) x (HNode A 0 (Leaf A)))).
        Check (unfold_traverse_to_check_balanced_t).
        rewrite ->
                (unfold_traverse_to_check_balanced_t
                   A
                   (HNode A 0 (Leaf A))
                   (HNode A 0 (Leaf A))
                   x).
        rewrite ->
                (unfold_traverse_to_check_balanced_hbt
                   A
                   0
                   (Leaf A)).
        rewrite -> (unfold_traverse_to_check_balanced_bt_leaf A).
        unfold differ_by_one.
        rewrite -> (plus_0_l 1).
        unfold beq_nat.
        unfold max.
        rewrite -> (plus_0_r 1).
        (* why does the boolean statement not evaluate here? *)
        reflexivity.

    (* show orderedness *)
      + unfold is_ordered_hbt.
        rewrite -> unfold_traverse_to_check_ordered_hbt.
        rewrite -> unfold_traverse_to_check_ordered_bt_node.
        rewrite -> unfold_traverse_to_check_ordered_t.
        rewrite -> unfold_traverse_to_check_ordered_hbt.
        rewrite -> unfold_traverse_to_check_ordered_bt_leaf.        
        reflexivity.
  }
  
  (* Specification for bt with node constructor holds, given t as inductive case *)
  {
    intros t H_t_inductive_assumption h_hbt hbt' H_sound_bt_init
           H_bal_bt_init H_ord_bt_init H_insert_bt.
    exact (H_t_inductive_assumption h_hbt hbt' H_sound_bt_init H_bal_bt_init
                                    H_ord_bt_init H_insert_bt).
  }

    (* Specification for t holds, given hbt as inductive case *)
  { 
    intros hbt1 H_hbt1_inductive_assumption
           e
           hbt2 H_hbt2_inductive_assumption
           h_hbt hbt'
           H_sound_t_init H_bal_t_init H_ord_t_init H_insert_t.

    (* Before working on the particular subgoals, assert some essential 
     * hypotheses *)
    destruct (triple_sound_implies_hbts_sound
                A h_hbt hbt1 e hbt2 H_sound_t_init) as [H_hbt1_is_sound H_hbt2_is_sound].
    destruct (triple_balanced_implies_hbts_balanced
                A h_hbt hbt1 e hbt2 H_bal_t_init) as [H_hbt1_is_balanced H_hbt2_is_balanced].
    destruct (triple_ordered_implies_hbts_ordered
                A compare h_hbt hbt1 e hbt2 H_ord_t_init)
      as [H_hbt1_is_ordered H_hbt2_is_ordered].
    rewrite -> (unfold_insert_t_helper A compare x h_hbt hbt1 e hbt2)
      in H_insert_t.
    (* Element to be inserted is Lt current element considered *)
    case (compare x e) as [ | | ] eqn : C_comp.

    (* Case 1: x <e *)
    - case (insert_hbt_helper A compare x hbt1) as [hbt_ret | ] eqn : C_insert_hbt1.
      induction hbt_ret as [h_ret bt_ret].

      (* Trivial hypothesis required to use other hypotheses *)
      assert (P_some_eq : Some (HNode A h_ret bt_ret) =
                          Some (HNode A h_ret bt_ret)).
      reflexivity. 

      case (compare_int (h_ret - project_height_hbt A hbt2) 2)
        as [ | | ] eqn : C_height_diff.

      (* The insertion does not unbalance the tree *) 
      + unfold beq_nat in H_insert_t.
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
                                                H_hbt1_is_ordered
                                                P_some_eq) as
              [H_hbt_ret_is_sound [_ _]].
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
        split.
        
        (* The resultant tree is balanced *)
        {
          destruct (H_hbt1_inductive_assumption (HNode A h_ret bt_ret)
                                                H_hbt1_is_sound
                                                H_hbt1_is_balanced
                                                H_hbt1_is_ordered
                                                P_some_eq) as
              [_ [H_hbt_ret_is_balanced _]].
          destruct (H_hbt1_inductive_assumption (HNode A h_ret bt_ret)
                                                H_hbt1_is_sound
                                                H_hbt1_is_balanced
                                                H_hbt1_is_ordered
                                                P_some_eq) as
              [H_hbt_ret_is_sound [_ _]].
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
        
        (* The resultant tree is ordered *)
        {
          Check (insertion_in_node_min_max).
          destruct (insertion_in_node_min_max A compare) as [H_hbt_ret_min_max _].
          unfold is_ordered_hbt in H_ord_t_init. 
          destruct (H_hbt1_inductive_assumption
                      (HNode A h_ret bt_ret)
                      H_hbt1_is_sound
                      H_hbt1_is_balanced
                      H_hbt1_is_ordered
                      P_some_eq) as [_ [_ H_hbt_ret_is_ordered]].
          unfold is_ordered_hbt.
          rewrite -> unfold_traverse_to_check_ordered_hbt.
          rewrite -> unfold_traverse_to_check_ordered_bt_node.
          rewrite -> unfold_traverse_to_check_ordered_t.
          unfold is_ordered_hbt in H_hbt_ret_is_ordered.
          unfold is_ordered_hbt in H_hbt2_is_ordered.  
          case (traverse_to_check_ordered_hbt A (HNode A h_ret bt_ret) compare)
            as [ | | (min_ret, max_ret)] eqn : C_traverse_ord_hbt_ret.
          
          (* the returned tree is unorderd : vacuous case *)
          discriminate.
          case (traverse_to_check_ordered_hbt A hbt2 compare)
            as [ | | (min2, max2)] eqn : C_traverse_ord_hbt2.
          discriminate.

          (* the returned tree is a leaf: impossible case  *)
          reflexivity.
          
          apply (insertion_impossible_case_implies_true
                   A hbt1 (HNode A h_ret bt_ret) compare x).
          exact C_insert_hbt1.
          exact C_traverse_ord_hbt_ret.

          (* the returned tree is a node *) 
          Check (triple_ordered_implies_hbts_ordered).
          Check (triple_ordered_implies_hbts_ordered
                   A compare h_hbt hbt1 e hbt2 H_ord_t_init).
          destruct (triple_ordered_implies_hbts_ordered
                      A compare h_hbt hbt1 e hbt2 H_ord_t_init)
            as [H_ord_hbt1 H_ord_hbt2].
          unfold is_ordered_hbt in H_ord_hbt1.
          induction hbt1 as [h1 bt1].
          rewrite -> unfold_traverse_to_check_ordered_hbt in H_ord_hbt1.
          case bt1 as [ | t1] eqn : C_bt1.

          (* the insertion took place for a leaf *)
          rewrite -> unfold_traverse_to_check_ordered_bt_leaf in H_ord_hbt1.
          Check (insertion_in_leaf_min_max).
          
          assert (H_traverse_leaf :
                    traverse_to_check_ordered_hbt A (HNode A h1 (Leaf A)) compare
                    = TNone (A * A)).
          rewrite -> unfold_traverse_to_check_ordered_hbt.
          rewrite -> unfold_traverse_to_check_ordered_bt_leaf.
          reflexivity.

          Check (insertion_in_leaf_min_max).
          Check (insertion_in_leaf_min_max
                   A compare (HNode A h1 (Leaf A)) (HNode A h_ret bt_ret) x min_ret max_ret
                   C_insert_hbt1 C_traverse_ord_hbt_ret H_traverse_leaf).
          destruct (insertion_in_leaf_min_max
                      A compare (HNode A h1 (Leaf A)) (HNode A h_ret bt_ret) x
                      min_ret max_ret C_insert_hbt1 C_traverse_ord_hbt_ret H_traverse_leaf)
            as [H_min_ret H_max_ret].
          rewrite -> H_max_ret.
          rewrite -> C_comp.
          unfold is_ordered_hbt in H_ord_hbt2.
          case (traverse_to_check_ordered_hbt A hbt2 compare)
            as [ | | (min2, max2)] eqn : C_traverse_ord_hbt2.
          discriminate.
          reflexivity.
          rewrite -> unfold_traverse_to_check_ordered_hbt in H_ord_t_init.
          rewrite -> unfold_traverse_to_check_ordered_bt_node in H_ord_t_init.
          rewrite -> unfold_traverse_to_check_ordered_t in H_ord_t_init.
          rewrite -> unfold_traverse_to_check_ordered_hbt in H_ord_t_init.
          rewrite -> unfold_traverse_to_check_ordered_bt_leaf in H_ord_t_init.
          rewrite -> C_traverse_ord_hbt2 in H_ord_t_init.
          case (compare e min2) as [ | | ] eqn : C_comp_e_min2.
          reflexivity.
          discriminate.
          discriminate.
          Check (H_hbt_ret_min_max).
          rewrite -> unfold_traverse_to_check_ordered_hbt in H_ord_t_init.
          rewrite -> unfold_traverse_to_check_ordered_bt_node in H_ord_t_init.
          rewrite -> unfold_traverse_to_check_ordered_t in H_ord_t_init.

          (* the insertion took place in a node *)
          case (traverse_to_check_ordered_bt A (Node A t1) compare)
            as [ | | (min1, max1)] eqn : C_traverse_ord_hbt1.
          discriminate.
          induction t1 as [hbt11 e1 hbt12].
          Check (ordered_node_has_min_max).
          Check (ordered_node_has_min_max
                   A compare h1 hbt11 e1 hbt12 H_hbt1_is_ordered).
          destruct (ordered_node_has_min_max
                      A compare h1 hbt11 e1 hbt12 H_hbt1_is_ordered)
            as [some_min [some_max H_contradictory]].
          rewrite -> H_contradictory in C_traverse_ord_hbt1.
          discriminate.
          Check (H_hbt_ret_min_max
                   (HNode A h1 (Node A t1))
                   (HNode A h_ret bt_ret)
                   x min1 min_ret max1 max_ret
                   C_insert_hbt1
                   C_traverse_ord_hbt_ret).
          
          assert (H_traverse_ord_hbt1 :
                    traverse_to_check_ordered_hbt A (HNode A h1 (Node A t1)) compare =
                    TSome (A * A) (min1, max1)).
          rewrite -> unfold_traverse_to_check_ordered_hbt.
          exact C_traverse_ord_hbt1.
          
          destruct (H_hbt_ret_min_max
                      (HNode A h1 (Node A t1))
                      (HNode A h_ret bt_ret)
                      x min1 min_ret max1 max_ret
                      C_insert_hbt1
                      C_traverse_ord_hbt_ret
                      H_traverse_ord_hbt1) as [[H_max_ret_x | H_max_ret_max1] _].
          
          (* prove case for H_max_ret_x *)
          rewrite -> H_max_ret_x.
          rewrite -> C_comp.
          case (traverse_to_check_ordered_hbt A hbt2 compare)
            as [ | | (min2, max2)].
          discriminate.
          reflexivity. 
          case (compare e min2) as [ | | ] eqn : C_comp_e_min2.
          reflexivity.
          rewrite -> H_traverse_ord_hbt1 in H_ord_t_init.
          case (compare max1 e) as [ | | ] eqn : C_comp_max1_e.
          discriminate.
          discriminate.
          discriminate.
          rewrite -> H_traverse_ord_hbt1 in H_ord_t_init.
          case (compare max1 e) as [ | | ] eqn : C_comp_max1_e.
          discriminate.
          discriminate.
          discriminate.

          (* prove case for H_max_ret_max1 *)
          rewrite -> H_max_ret_max1.
          rewrite -> H_traverse_ord_hbt1 in H_ord_t_init.
          case (compare max1 e) as [ | | ] eqn : C_comp_max1_e.
          case (traverse_to_check_ordered_hbt A hbt2 compare)
            as [ | | (min2, max2)].
          discriminate.
          reflexivity. 
          case (compare e min2) as [ | | ] eqn : C_comp_e_min2.
          reflexivity.
          discriminate.
          discriminate.
          discriminate.
          discriminate.
        }
        
      (* the insertion unbalances the tree: rotations required *) 
      + Check (H_hbt1_inductive_assumption
                 (HNode A h_ret bt_ret)
                 H_hbt1_is_sound H_hbt1_is_balanced H_hbt1_is_ordered P_some_eq).
        destruct (H_hbt1_inductive_assumption
                    (HNode A h_ret bt_ret)
                    H_hbt1_is_sound H_hbt1_is_balanced H_hbt1_is_ordered P_some_eq)
          as [H_hbt_ret_sound [H_hbt_ret_balanced H_hbt_ret_ordered]].
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

        split.
        
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

        (* rotated tree is ordered *)
        {
          Check (rotate_right_preserves_order).
          Check (rotate_right_preserves_order
                   A compare h_hbt hbt1 e hbt2 h_ret bt_ret hbt'
                   H_ord_t_init H_hbt_ret_ordered H_hbt2_is_ordered H_insert_t).
          exact (rotate_right_preserves_order
                   A compare h_hbt hbt1 e hbt2 h_ret bt_ret hbt'
                   H_ord_t_init H_hbt_ret_ordered H_hbt2_is_ordered H_insert_t).
        }

      (* impossible case: the height differnce is greater than 2 *)
      + discriminate.

      (* A None value is returned on insertion *)
      + discriminate.

    (* Case 2: x = e, in which case a None value is returned *)
    - discriminate.

    (* Case 3: x > e *)
    - case (insert_hbt_helper A compare x hbt2) as [hbt_ret | ] eqn : C_insert_hbt2.
      induction hbt_ret as [h_ret bt_ret].

      (* Trivial hypothesis required to use other hypotheses *)
      assert (P_some_eq : Some (HNode A h_ret bt_ret) =
                          Some (HNode A h_ret bt_ret)).
      reflexivity. 

      case (compare_int (h_ret - project_height_hbt A hbt1) 2)
        as [ | | ] eqn : C_height_diff.

      (* The insertion does not unbalance the tree *) 
      + unfold beq_nat in H_insert_t.
        rewrite -> some_x_equal_some_y in H_insert_t.
        rewrite <- H_insert_t.

        split.
        (* The resultant tree is sound *)
        {
          destruct (H_hbt2_inductive_assumption (HNode A h_ret bt_ret)
                                                H_hbt2_is_sound
                                                H_hbt2_is_balanced
                                                H_hbt2_is_ordered
                                                P_some_eq) as
              [H_hbt_ret_is_sound [_ _]].
          
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
        split.
        
        (* The resultant tree is balanced *)
        {
          destruct (H_hbt2_inductive_assumption (HNode A h_ret bt_ret)
                                                H_hbt2_is_sound
                                                H_hbt2_is_balanced
                                                H_hbt2_is_ordered
                                                P_some_eq) as
              [_ [H_hbt_ret_is_balanced _]].
          destruct (H_hbt2_inductive_assumption (HNode A h_ret bt_ret)
                                                H_hbt2_is_sound
                                                H_hbt2_is_balanced
                                                H_hbt2_is_ordered
                                                P_some_eq) as
              [H_hbt_ret_is_sound [_ _]].
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
        
        (* The resultant tree is ordered *)
        {
          (* Duplicate hypothesis, since H_hbt2_is_ordered will be destructed *)
          assert (H_hbt2_is_ordered_duplication:
                    is_ordered_hbt A hbt2 compare = true).
          exact H_hbt2_is_ordered.
          Check (insertion_in_node_min_max).
          destruct (insertion_in_node_min_max A compare) as [H_hbt_ret_min_max _].
          unfold is_ordered_hbt in H_ord_t_init. 
          destruct (H_hbt2_inductive_assumption
                      (HNode A h_ret bt_ret)
                      H_hbt2_is_sound
                      H_hbt2_is_balanced
                      H_hbt2_is_ordered
                      P_some_eq) as [_ [_ H_hbt_ret_is_ordered]].
          unfold is_ordered_hbt.
          rewrite -> unfold_traverse_to_check_ordered_hbt.
          rewrite -> unfold_traverse_to_check_ordered_bt_node.
          rewrite -> unfold_traverse_to_check_ordered_t.
          unfold is_ordered_hbt in H_hbt_ret_is_ordered.
          unfold is_ordered_hbt in H_hbt1_is_ordered.
          case (traverse_to_check_ordered_hbt A hbt1 compare)
            as [ | | (min1, max1)] eqn : C_traverse_ord_hbt1.

          (* vacuous case: hbt1 is unordered *)
          discriminate.

          (* hbt1 is a leaf *)
          case (traverse_to_check_ordered_hbt A (HNode A h_ret bt_ret) compare)
            as [ | | (min_ret, max_ret)] eqn : C_traverse_ord_hbt_ret.
          
          (* the returned tree is unorderd : vacuous case *)
          discriminate.

          (* the returned tree is a leaf: impossible case  *)
          reflexivity.
          
          (* the returned tree is a node *)
          
          unfold is_ordered_hbt in H_hbt2_is_ordered.
          induction hbt2 as [h2 bt2].
          rewrite -> unfold_traverse_to_check_ordered_hbt in H_hbt2_is_ordered.
          case bt2 as [ | t2] eqn : C_bt2.

          (* the insertion took place for a leaf *)
          rewrite -> unfold_traverse_to_check_ordered_bt_leaf in H_hbt2_is_ordered.
          Check (insertion_in_leaf_min_max).
          
          assert (H_traverse_leaf :
                    traverse_to_check_ordered_hbt A (HNode A h2 (Leaf A)) compare
                    = TNone (A * A)).
          rewrite -> unfold_traverse_to_check_ordered_hbt.
          rewrite -> unfold_traverse_to_check_ordered_bt_leaf.
          reflexivity.

          Check (insertion_in_leaf_min_max).
          Check (insertion_in_leaf_min_max
                   A compare (HNode A h2 (Leaf A)) (HNode A h_ret bt_ret) x min_ret max_ret
                   C_insert_hbt2 C_traverse_ord_hbt_ret H_traverse_leaf).
          destruct (insertion_in_leaf_min_max
                      A compare (HNode A h2 (Leaf A)) (HNode A h_ret bt_ret) x min_ret max_ret
                      C_insert_hbt2 C_traverse_ord_hbt_ret H_traverse_leaf)
            as [H_min_ret H_max_ret].
          rewrite -> H_min_ret.
          rewrite <- (relating_lt_gt A e x compare) in C_comp.
          rewrite -> C_comp.
          reflexivity. 

          (* the insertion took place in a node *)
          case (traverse_to_check_ordered_bt A (Node A t2) compare)
            as [ | | (min2, max2)] eqn : C_traverse_ord_hbt2.
          (* impossible case: hbt2 was unordered *)
          discriminate.

          (* impossible case: hbt2 was a leaf *)
          induction t2 as [hbt21 e2 hbt22].
          
          Check (ordered_node_has_min_max
                   A compare h2 hbt21 e2 hbt22 H_hbt2_is_ordered_duplication).
          destruct (ordered_node_has_min_max
                      A compare h2 hbt21 e2 hbt22 H_hbt2_is_ordered_duplication)
            as [some_min [some_max H_contradictory]].
          rewrite -> H_contradictory in C_traverse_ord_hbt2.
          discriminate.

          (* traverse_to_check_ordered_bt hbt2 has a max and min *)
          Check (H_hbt_ret_min_max).
          Check (H_hbt_ret_min_max
                   (HNode A h2 (Node A t2))
                   (HNode A h_ret bt_ret)
                   x min2 min_ret max2 max_ret
                   C_insert_hbt2
                   C_traverse_ord_hbt_ret
                   C_traverse_ord_hbt2).
          destruct (H_hbt_ret_min_max
                      (HNode A h2 (Node A t2))
                      (HNode A h_ret bt_ret)
                      x min2 min_ret max2 max_ret
                      C_insert_hbt2
                      C_traverse_ord_hbt_ret
                      C_traverse_ord_hbt2)
            as [_ [H_min_ret_x | H_min_ret_min2]].
          
          (* prove case for H_min_ret_x *)
          rewrite -> H_min_ret_x.
          rewrite <- relating_lt_gt in C_comp.
          rewrite -> C_comp.
          reflexivity.

          (* prove case for H_min_ret_min2 *)
          rewrite -> H_min_ret_min2.
          rewrite -> unfold_traverse_to_check_ordered_hbt in H_ord_t_init.
          rewrite -> unfold_traverse_to_check_ordered_bt_node in H_ord_t_init.
          rewrite -> unfold_traverse_to_check_ordered_t in H_ord_t_init.
          rewrite -> unfold_traverse_to_check_ordered_hbt in H_ord_t_init.
          rewrite -> unfold_traverse_to_check_ordered_bt_node in H_ord_t_init.
          rewrite -> C_traverse_ord_hbt1 in H_ord_t_init.
          rewrite -> unfold_traverse_to_check_ordered_bt_node in C_traverse_ord_hbt2.
          rewrite -> C_traverse_ord_hbt2 in H_ord_t_init.
          case (compare e min2) as [ | | ] eqn : C_comp_e_min2.
          reflexivity.
          discriminate.
          discriminate.

          (* hbt1 is a node *)
          rewrite -> unfold_traverse_to_check_ordered_hbt in H_ord_t_init.
          rewrite -> unfold_traverse_to_check_ordered_bt_node in H_ord_t_init.
          rewrite -> unfold_traverse_to_check_ordered_t in H_ord_t_init.
          rewrite -> C_traverse_ord_hbt1 in H_ord_t_init.
          case (compare max1 e) as [ | | ] eqn : C_comp_max1_e.
          case (traverse_to_check_ordered_hbt A (HNode A h_ret bt_ret) compare)
            as [ | | (min_ret, max_ret)] eqn : C_traverse_ord_hbt_ret.
          discriminate.
          reflexivity.
          unfold is_ordered_hbt in H_hbt2_is_ordered.
          induction hbt2 as [h2 bt2].
          rewrite -> unfold_traverse_to_check_ordered_hbt in H_hbt2_is_ordered.
          case bt2 as [ | t2] eqn : C_bt2.
          
          (* the insertion took place in a leaf *)
          rewrite -> unfold_traverse_to_check_ordered_bt_leaf in H_hbt2_is_ordered.
          Check (insertion_in_leaf_min_max).
          
          assert (H_traverse_leaf :
                    traverse_to_check_ordered_hbt A (HNode A h2 (Leaf A)) compare
                    = TNone (A * A)).
          rewrite -> unfold_traverse_to_check_ordered_hbt.
          rewrite -> unfold_traverse_to_check_ordered_bt_leaf.
          reflexivity.

          Check (insertion_in_leaf_min_max).
          Check (insertion_in_leaf_min_max
                   A compare (HNode A h2 (Leaf A)) (HNode A h_ret bt_ret) x min_ret max_ret
                   C_insert_hbt2 C_traverse_ord_hbt_ret H_traverse_leaf).
          destruct (insertion_in_leaf_min_max
                      A compare (HNode A h2 (Leaf A)) (HNode A h_ret bt_ret) x min_ret max_ret
                      C_insert_hbt2 C_traverse_ord_hbt_ret H_traverse_leaf)
            as [H_min_ret H_max_ret].
          rewrite -> H_min_ret.
          rewrite <- (relating_lt_gt A e x compare) in C_comp.
          rewrite -> C_comp.
          reflexivity. 

          (* the insertion took place in a node *)
          case (traverse_to_check_ordered_bt A (Node A t2) compare)
            as [ | | (min2, max2)] eqn : C_traverse_ord_hbt2.
          (* impossible case: hbt2 was unordered *)
          discriminate.

          (* impossible case: hbt2 was a leaf *)
          induction t2 as [hbt21 e2 hbt22].
          
          Check (ordered_node_has_min_max
                   A compare h2 hbt21 e2 hbt22 H_hbt2_is_ordered_duplication).
          destruct (ordered_node_has_min_max
                      A compare h2 hbt21 e2 hbt22 H_hbt2_is_ordered_duplication)
            as [some_min [some_max H_contradictory]].
          rewrite -> H_contradictory in C_traverse_ord_hbt2.
          discriminate.

          (* traverse_to_check_ordered_bt hbt2 has a max and min *)
          Check (H_hbt_ret_min_max
                   (HNode A h2 (Node A t2))
                   (HNode A h_ret bt_ret)
                   x min2 min_ret max2 max_ret
                   C_insert_hbt2
                   C_traverse_ord_hbt_ret
                   C_traverse_ord_hbt2).
          destruct (H_hbt_ret_min_max
                      (HNode A h2 (Node A t2))
                      (HNode A h_ret bt_ret)
                      x min2 min_ret max2 max_ret
                      C_insert_hbt2
                      C_traverse_ord_hbt_ret
                      C_traverse_ord_hbt2)
            as [_ [H_min_ret_x | H_min_ret_min2]].
          
          (* prove case for H_min_ret_x *)
          rewrite -> H_min_ret_x.
          rewrite <- relating_lt_gt in C_comp.
          rewrite -> C_comp.
          reflexivity.

          (* prove case for H_min_ret_min2 *)
          rewrite -> H_min_ret_min2.
          rewrite -> unfold_traverse_to_check_ordered_hbt in H_ord_t_init.
          rewrite -> C_traverse_ord_hbt2 in H_ord_t_init.
          case (compare e min2) as [ | | ] eqn : C_comp_e_min2. 
          reflexivity.
          discriminate.
          discriminate.
          discriminate.
          discriminate.
        }
        
      (* the insertion unbalances the tree: rotations required *) 
      + Check (H_hbt2_inductive_assumption
                 (HNode A h_ret bt_ret)
                 H_hbt2_is_sound H_hbt2_is_balanced H_hbt2_is_ordered P_some_eq).
        destruct (H_hbt2_inductive_assumption
                    (HNode A h_ret bt_ret)
                    H_hbt2_is_sound H_hbt2_is_balanced H_hbt2_is_ordered P_some_eq)
          as [H_hbt_ret_sound [H_hbt_ret_balanced H_hbt_ret_ordered]].
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

        split.
        
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

        (* rotated tree is ordered *)
        {
          Check (rotate_left_preserves_order).
          Check (rotate_left_preserves_order
                   A compare h_hbt hbt1 e hbt2 h_ret bt_ret hbt'
                   H_ord_t_init H_hbt1_is_ordered H_hbt_ret_ordered H_insert_t).
          exact (rotate_left_preserves_order
                   A compare h_hbt hbt1 e hbt2 h_ret bt_ret hbt'
                   H_ord_t_init H_hbt1_is_ordered H_hbt_ret_ordered H_insert_t).
        }

      (* the insertion results in a None value *)
      + discriminate.

      + discriminate.
  }


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


(* Theorem insert_hbt_satisfies_its_specification:  *)
(*   forall (A : Type) *)
(*          (compare : A -> A -> element_comparison) *)
(*          (x : A), *)
(*     specifiction_of_insert_hbt A compare x insert_hbt. *)
(* Proof.           *)
(*   intros A compare.   *)
(*   unfold specifiction_of_insert_hbt. *)
(*   intros x hbt H_sound_init H_bal_init H_order_init. *)
(*   unfold insert_hbt. *)
(*   (* destruct (the_helper_functions_meet_their_specifications A compare x) as [H_hbt [_ _]]. *) *)
  
(*   unfold specification_of_insert_hbt_helper in H_hbt. *)
(*   case (insert_hbt_helper A compare x hbt) as [ hbt' | ] eqn : C. *)
(*   apply (H_hbt hbt hbt'). *)
(*   exact C. *)

(*   split. *)
(*   exact H_sound_init. *)
(*   split. *)
(*   exact H_bal_init. *)
(*   exact H_order_init. *)
(* Qed. *)



(* (* ***** Section 4.2: Formal specification and associated theorems for lookup ***** *) *)



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

