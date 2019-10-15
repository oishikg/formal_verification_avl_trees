Require Import Hbt.Implementation.hbt.
Require Export Hbt.Implementation.hbt.

Require Import Hbt.Lemmas.sound_balanced.
Require Export Hbt.Lemmas.sound_balanced.

Require Import Hbt.Lemmas.ordered_sub.
Require Export Hbt.Lemmas.ordered_sub.


(* The main lemma required to prove the orderedness case of the insertion specification in 
 * Hbt.Theorems.theorems: given an insertion into a subtree, show that the maximum and 
 * minimum values of a subtree are as specified in the theorem *)
Lemma insertion_in_node_min_max: 
  forall (A : Type)
         (compare : A -> A -> element_comparison),
    (forall (hbt : heightened_binary_tree A)
            (hbt' : heightened_binary_tree A)
            (x min min' max max' : A),
        is_sound_hbt A hbt = true ->
        is_balanced_hbt A hbt = true -> 
        insert_hbt_helper A compare x hbt = Some hbt' ->
        traverse_to_check_ordered_hbt A hbt' compare = TSome (A * A) (min', max') ->
        traverse_to_check_ordered_hbt A hbt compare = TSome (A * A) (min, max) ->
        (max' = x \/ max' = max) /\ (min' = x \/ min' = min))
    /\
    (forall (bt : binary_tree A)
            (h : nat)
            (hbt' : heightened_binary_tree A)
            (x min min' max max' : A),
        is_sound_hbt A (HNode A h bt) = true ->
        is_balanced_hbt A (HNode A h bt) = true -> 
        insert_bt_helper A compare x h bt = Some hbt' ->
        traverse_to_check_ordered_hbt A hbt' compare = TSome (A * A) (min', max') ->
        traverse_to_check_ordered_bt A bt compare = TSome (A * A) (min, max) ->
        (max' = x \/ max' = max) /\ (min' = x \/ min' = min))
    /\
    (forall (t : triple A)
            (h : nat)
            (hbt' : heightened_binary_tree A)
            (x min min' max max' : A),
        is_sound_hbt A (HNode A h (Node A t)) = true ->
        is_balanced_hbt A (HNode A h (Node A t)) = true -> 
        insert_t_helper A compare x h t = Some hbt' ->
        traverse_to_check_ordered_hbt A hbt' compare = TSome (A * A) (min', max') ->
        traverse_to_check_ordered_t A t compare = TSome (A * A) (min, max) ->
        (max' = x \/ max' = max) /\ (min' = x \/ min' = min)).
Proof.    
  intros A compare.
  apply heightened_binary_tree_mutual_induction.

  (* proof for hbt, with bt as inductive hypothesis *)
  intros h bt H_ind_bt hbt' x min min' max max' H_sound_hbt H_bal_hbt H_insert_hbt H_ord_hbt' H_ord_hbt.
  rewrite -> (unfold_insert_hbt_helper A compare x h bt) in H_insert_hbt.
  rewrite -> (unfold_traverse_to_check_ordered_hbt A h bt compare) in H_ord_hbt.
  Check (H_ind_bt h hbt' x min min' max max' H_sound_hbt H_bal_hbt H_insert_hbt H_ord_hbt' H_ord_hbt).
  exact (H_ind_bt h hbt' x min min' max max' H_sound_hbt H_bal_hbt H_insert_hbt H_ord_hbt' H_ord_hbt).

  (* a leaf provides a vacuous case *)
  intros h hbt' x min min' max max' H_insert_hbt H_sound_hbt H_bal_hbt H_ord_hbt' H_ord_hbt.
  rewrite -> (unfold_traverse_to_check_ordered_bt_leaf A compare) in H_ord_hbt.
  discriminate.

  (* proof for node, with t as inductive hypothesis *)
  intros t H_ind_t h hbt' x min min' max max' H_sound_hbt H_bal_hbt H_insert_bt H_ord_hbt' H_ord_bt.
  rewrite -> (unfold_insert_bt_helper_node A compare x h t) in H_insert_bt.
  rewrite -> (unfold_traverse_to_check_ordered_bt_node A t compare) in H_ord_bt.
  Check (H_ind_t h hbt' x min min' max max' H_sound_hbt H_bal_hbt H_insert_bt H_ord_hbt' H_ord_bt).
  exact (H_ind_t h hbt' x min min' max max' H_sound_hbt H_bal_hbt H_insert_bt H_ord_hbt' H_ord_bt).

  (* proof for t, with inductive hypotheses for hbt1 and hbt2 *)
  intros hbt1 H_hbt1 e hbt2 H_hbt2 h hbt' x t_min t_min' t_max t_max' H_sound_hbt H_bal_hbt
         H_insert_hbt H_ord_hbt' H_ord_t.  
  
  (* the long and arduous journey into the insert function *)

  destruct (triple_sound_implies_hbts_sound A h hbt1 e hbt2 H_sound_hbt)
    as [H_hbt1_sound H_hbt2_sound].
  destruct (triple_balanced_implies_hbts_balanced A h hbt1 e hbt2 H_bal_hbt)
    as [H_hbt1_bal H_hbt2_bal].

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
                          H_hbt1_sound
                          H_hbt1_bal
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
                          H_hbt1_sound H_hbt1_bal
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
                  H_hbt1_sound H_hbt1_bal
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

    + case ((h12' + 1 =n= h11') || (h12' =n= h11')) as [ | ] eqn : C_h12'_h11'.
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

      Check (disjunction_to_prop).
      destruct (disjunction_to_prop (h12' + 1 =n= h11') (h12' =n= h11') C_h12'_h11')
               as [H_h12'_gt_h11' | H_ht12'_eq_h11'].

      (* case 1: H_h12'_gt_h11' *) 
      assert (H_impossible_hbt1 : bt1 <> Leaf A).
      Check (rotate_right_2_impossible_case_1).
      exact (rotate_right_2_impossible_case_1
               A compare x h1 bt1
               h1' h11' h12'
               bt11' bt12' e1
               C_insert_hbt1
               H_h12'_gt_h11').
      
      assert (H_contradiction: bt1 = Leaf A).
      Check (tnone_implies_leaf).
      exact (tnone_implies_leaf A h1 bt1 compare C_traverse_ord_hbt1).

      apply False_ind.
      rewrite -> H_contradiction in H_impossible_hbt1.
      unfold not in H_impossible_hbt1.
      assert (H_trivial_equality: Leaf A = Leaf A).
      reflexivity.
      apply H_impossible_hbt1 in H_trivial_equality.
      exact H_trivial_equality.


      (* case 2: H_h12'_eq_h11' *)
      assert (H_impossible_hbt1 : bt1 <> Leaf A).
      Check (rotate_right_2_impossible_case_2).
      exact (rotate_right_2_impossible_case_2
               A compare 
               x h1 bt1 h1' h11' h12'
               bt11' bt12' e1 h2 bt2
               H_hbt1_sound
               H_hbt1_bal
               C_insert_hbt1
               H_ht12'_eq_h11'
               C_comp_heights).
      
      assert (H_contradiction: bt1 = Leaf A).
      Check (tnone_implies_leaf).
      exact (tnone_implies_leaf A h1 bt1 compare C_traverse_ord_hbt1).

      apply False_ind.
      rewrite -> H_contradiction in H_impossible_hbt1.
      unfold not in H_impossible_hbt1.
      assert (H_trivial_equality: Leaf A = Leaf A).
      reflexivity.
      apply H_impossible_hbt1 in H_trivial_equality.
      exact H_trivial_equality.
      
      (* finally, we have what is required to apply the inductive hypothesis *)
      assert (H_trivial_equality:
                TSome (A * A) (min1, max1) = TSome (A * A) (min1, max1)).
      reflexivity.
      
      destruct (H_hbt1
                  (HNode A h1'
                         (Node A (Triple A (HNode A h11' bt11') e1 (HNode A h12' bt12'))))
                  x min1 t_min' max1 t_max''
                  H_hbt1_sound
                  H_hbt1_bal
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
                        H_hbt2_sound
                        H_hbt2_bal
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
                        H_hbt2_sound
                        H_hbt2_bal
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
                  H_hbt2_sound
                  H_hbt2_bal
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

      * case ((h21' + 1 =n= h22') || (h21' =n= h22')) as [ | ] eqn : C_h21'_h22'.
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

      destruct (disjunction_to_prop (h21' + 1 =n= h22') (h21' =n= h22') C_h21'_h22')
               as [H_h22'_gt_h21' | H_ht12'_eq_h21'].

      (* case 1: H_h22'_ht_h21' *)
      assert (H_impossible_hbt2 : bt2 <> Leaf A).
      Check (rotate_left_2_impossible_case_1).
      exact (rotate_left_2_impossible_case_1
               A compare x h2 bt2
               h2' h21' h22'
               bt21' bt22' e2
               C_insert_hbt2
               H_h22'_gt_h21').
      
      assert (H_contradiction: bt2 = Leaf A).
      Check (tnone_implies_leaf).
      exact (tnone_implies_leaf A h2 bt2 compare C_traverse_ord_hbt2).

      apply False_ind.
      rewrite -> H_contradiction in H_impossible_hbt2.
      unfold not in H_impossible_hbt2.
      assert (H_trivial_equality: Leaf A = Leaf A).
      reflexivity.
      apply H_impossible_hbt2 in H_trivial_equality.
      exact H_trivial_equality.
      
      (* case 2: H_ht12'_eq_h21' *)
      assert (H_impossible_hbt2 : bt2 <> Leaf A).
      Check (rotate_left_2_impossible_case_2).
      exact (rotate_left_2_impossible_case_2
               A compare
               x h2 bt2 h2' h21' h22'
               e2 bt21' bt22' h1 bt1
               H_hbt2_sound
               H_hbt2_bal
               C_insert_hbt2
               H_ht12'_eq_h21'
               C_comp_heights).
      
      assert (H_contradiction: bt2 = Leaf A).
      Check (tnone_implies_leaf).
      exact (tnone_implies_leaf A h2 bt2 compare C_traverse_ord_hbt2).

      apply False_ind.
      rewrite -> H_contradiction in H_impossible_hbt2.
      unfold not in H_impossible_hbt2.
      assert (H_trivial_equality: Leaf A = Leaf A).
      reflexivity.
      apply H_impossible_hbt2 in H_trivial_equality.
      exact H_trivial_equality.

      
      (* finally, we have what is required to apply the inductive hypothesis *)
      assert (H_trivial_equality:
                TSome (A * A) (min2, max2) = TSome (A * A) (min2, max2)).
      reflexivity.
      
      destruct (H_hbt2
                  (HNode A h2'
                         (Node A (Triple A (HNode A h21' bt21') e2 (HNode A h22' bt22'))))
                  x min2 t_min'' max2 t_max'
                  H_hbt2_sound
                  H_hbt2_bal
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

(* Rotation lemmas *) 
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


Lemma insertion_preserves_order: 
  forall (A : Type)
         (compare : A -> A -> element_comparison)
         (x : A),
    (forall (hbt : heightened_binary_tree A)
            (hbt' : heightened_binary_tree A),
        is_sound_hbt A hbt = true ->
        is_balanced_hbt A hbt = true ->
        is_ordered_hbt A hbt compare = true -> 
        insert_hbt_helper A compare x hbt = Some hbt' ->
        is_ordered_hbt A hbt' compare = true)
    /\
    (forall (bt : binary_tree A)
            (h_hbt : nat)
            (hbt' : heightened_binary_tree A),    
        is_sound_hbt A (HNode A h_hbt bt) = true ->
        is_balanced_hbt A (HNode A h_hbt bt) = true ->
        is_ordered_hbt A (HNode A h_hbt bt) compare = true ->
        insert_bt_helper A compare x h_hbt bt = Some hbt' ->
        is_ordered_hbt A hbt' compare = true)
    /\
    (forall (t : triple A)
            (h_hbt : nat)
            (hbt' : heightened_binary_tree A),    
        is_sound_hbt A (HNode A h_hbt (Node A t)) = true ->
        is_balanced_hbt A (HNode A h_hbt (Node A t)) = true ->
        is_ordered_hbt A (HNode A h_hbt (Node A t)) compare = true ->        
        insert_t_helper A compare x h_hbt t = Some hbt' ->
        is_ordered_hbt A hbt' compare = true).
Proof.
  intros A compare x.
  apply heightened_binary_tree_mutual_induction.

  (* Specification for hbt holds, given bt as inductive case *)
  - intros h bt H_bt_inductive_assumption hbt' H_sound_hbt_init
           H_bal_hbt_init H_ord_hbt_init H_insert_hbt.
    
    exact (H_bt_inductive_assumption h hbt' H_sound_hbt_init H_bal_hbt_init H_ord_hbt_init H_insert_hbt).

  (* Specification for bt leaf constructor holds *)
  -intros h_hbt hbt' H_sound_bt_init H_bal_bt_init H_ord_bt_init H_insert_bt.
   rewrite -> (unfold_insert_bt_helper_leaf A compare x) in H_insert_bt.
   rewrite -> some_x_equal_some_y in H_insert_bt.
   rewrite <- H_insert_bt.
   unfold is_ordered_hbt.
   rewrite -> unfold_traverse_to_check_ordered_hbt.
   rewrite -> unfold_traverse_to_check_ordered_bt_node.
   rewrite -> unfold_traverse_to_check_ordered_t.
   rewrite -> unfold_traverse_to_check_ordered_hbt.
   rewrite -> unfold_traverse_to_check_ordered_bt_leaf.        
   reflexivity.

   (* Specification for bt with node constructor holds, given t as inductive case *)
  - intros t H_t_inductive_assumption h_hbt hbt' H_sound_bt_init
           H_bal_bt_init H_ord_bt_init H_insert_bt.
    exact (H_t_inductive_assumption h_hbt hbt' H_sound_bt_init H_bal_bt_init
                                    H_ord_bt_init H_insert_bt).

  (* Specification for t holds, given hbt as inductive case *)
  - intros hbt1 H_hbt1_inductive_assumption
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
    + case (insert_hbt_helper A compare x hbt1) as [hbt_ret | ] eqn : C_insert_hbt1.
      induction hbt_ret as [h_ret bt_ret].

    (* Trivial hypothesis required to use other hypotheses *)
      assert (P_some_eq : Some (HNode A h_ret bt_ret) =
                          Some (HNode A h_ret bt_ret)).
      reflexivity. 

      case (compare_int (h_ret - project_height_hbt A hbt2) 2)
        as [ | | ] eqn : C_height_diff.

    (* The insertion does not unbalance the tree *) 
      * unfold beq_nat in H_insert_t.
        apply (some_x_equal_some_y
                 (heightened_binary_tree A)
                 (HNode A (1 + max h_ret (project_height_hbt A hbt2))
                        (Node A (Triple A (HNode A h_ret bt_ret) e hbt2)))
                 hbt') in H_insert_t.
        rewrite <- H_insert_t.

        {
          Check (insertion_in_node_min_max).
          destruct (insertion_in_node_min_max A compare) as [H_hbt_ret_min_max _].
          unfold is_ordered_hbt in H_ord_t_init.
          assert (H_hbt_ret_is_ordered:
                    is_ordered_hbt A (HNode A h_ret bt_ret) compare = true).
          exact (H_hbt1_inductive_assumption
                   (HNode A h_ret bt_ret)
                   H_hbt1_is_sound
                   H_hbt1_is_balanced
                   H_hbt1_is_ordered
                   P_some_eq). 
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
          
          assert (H_traverse_ord_hbt1 :
                    traverse_to_check_ordered_hbt A (HNode A h1 (Node A t1)) compare =
                    TSome (A * A) (min1, max1)).
          rewrite -> unfold_traverse_to_check_ordered_hbt.
          exact C_traverse_ord_hbt1.

          Check (H_hbt_ret_min_max
                      (HNode A h1 (Node A t1))
                      (HNode A h_ret bt_ret)
                      x min1 min_ret max1 max_ret
                      H_hbt1_is_sound
                      H_hbt1_is_balanced
                      C_insert_hbt1
                      C_traverse_ord_hbt_ret
                      C_traverse_ord_hbt1).
          destruct (H_hbt_ret_min_max
                      (HNode A h1 (Node A t1))
                      (HNode A h_ret bt_ret)
                      x min1 min_ret max1 max_ret
                      H_hbt1_is_sound
                      H_hbt1_is_balanced
                      C_insert_hbt1
                      C_traverse_ord_hbt_ret
                      C_traverse_ord_hbt1) as [[H_max_ret_x | H_max_ret_max1] _].
          
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
      * Check (H_hbt1_inductive_assumption
                 (HNode A h_ret bt_ret)
                 H_hbt1_is_sound H_hbt1_is_balanced H_hbt1_is_ordered P_some_eq).
        assert (H_hbt_ret_ordered:
                  is_ordered_hbt A (HNode A h_ret bt_ret) compare = true).
        exact (H_hbt1_inductive_assumption
                    (HNode A h_ret bt_ret)
                    H_hbt1_is_sound H_hbt1_is_balanced H_hbt1_is_ordered P_some_eq).

        Check (rotate_right_preserves_order
                 A compare h_hbt hbt1 e hbt2 h_ret bt_ret hbt'
                 H_ord_t_init H_hbt_ret_ordered H_hbt2_is_ordered H_insert_t).
        exact (rotate_right_preserves_order
                 A compare h_hbt hbt1 e hbt2 h_ret bt_ret hbt'
                 H_ord_t_init H_hbt_ret_ordered H_hbt2_is_ordered H_insert_t).

      * discriminate.

      * discriminate.

    (* Case 2: x = e, in which case a None value is returned *)        
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

        {
          (* Duplicate hypothesis, since H_hbt2_is_ordered will be destructed *)
          assert (H_hbt2_is_ordered_duplication:
                    is_ordered_hbt A hbt2 compare = true).
          exact H_hbt2_is_ordered.
          Check (insertion_in_node_min_max).
          destruct (insertion_in_node_min_max A compare) as [H_hbt_ret_min_max _].
          unfold is_ordered_hbt in H_ord_t_init.

          assert ( H_hbt_ret_is_ordered:
                     is_ordered_hbt A (HNode A h_ret bt_ret) compare = true).
          exact (H_hbt2_inductive_assumption
                   (HNode A h_ret bt_ret)
                   H_hbt2_is_sound
                   H_hbt2_is_balanced
                   H_hbt2_is_ordered
                   P_some_eq). 
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
                   H_hbt2_is_sound
                   H_hbt2_is_balanced
                   C_insert_hbt2
                   C_traverse_ord_hbt_ret
                   C_traverse_ord_hbt2).
          destruct (H_hbt_ret_min_max
                   (HNode A h2 (Node A t2))
                   (HNode A h_ret bt_ret)
                   x min2 min_ret max2 max_ret
                   H_hbt2_is_sound
                   H_hbt2_is_balanced
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
                   H_hbt2_is_sound
                   H_hbt2_is_balanced
                   C_insert_hbt2
                   C_traverse_ord_hbt_ret
                   C_traverse_ord_hbt2).
          destruct (H_hbt_ret_min_max
                      (HNode A h2 (Node A t2))
                      (HNode A h_ret bt_ret)
                      x min2 min_ret max2 max_ret
                      H_hbt2_is_sound
                      H_hbt2_is_balanced
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
      * Check (H_hbt2_inductive_assumption
                 (HNode A h_ret bt_ret)
                 H_hbt2_is_sound H_hbt2_is_balanced H_hbt2_is_ordered P_some_eq).
        assert (H_hbt_ret_ordered:
                  is_ordered_hbt A (HNode A h_ret bt_ret) compare = true).
        exact (H_hbt2_inductive_assumption
                 (HNode A h_ret bt_ret)
                 H_hbt2_is_sound H_hbt2_is_balanced H_hbt2_is_ordered P_some_eq).
        Check (rotate_left_preserves_order).
        Check (rotate_left_preserves_order
                 A compare h_hbt hbt1 e hbt2 h_ret bt_ret hbt'
                 H_ord_t_init H_hbt1_is_ordered H_hbt_ret_ordered H_insert_t).
          exact (rotate_left_preserves_order
                   A compare h_hbt hbt1 e hbt2 h_ret bt_ret hbt'
                   H_ord_t_init H_hbt1_is_ordered H_hbt_ret_ordered H_insert_t).

      * discriminate.

      * discriminate.
Qed.
