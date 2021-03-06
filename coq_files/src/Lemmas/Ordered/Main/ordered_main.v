(* ********** ordered_main.v ********** *)

(** The [ordered_main] library contains all the main lemmas concerned with the 
orderedness of AVL trees. These lemmas build on those define in [ordered_helper] *)

Require Import Hbt.Lemmas.Ordered.Helper.ordered_helper.
Require Export Hbt.Lemmas.Ordered.Helper.ordered_helper.

(* ********** *)

(** * Maximum and Minimum Elements After Insertion *)

(** Lemma to show that post an operation on a tree to insert some element <<x>>:
- the maximum element is either <<x>> or the maximum element of the original tree
- the minimum element is either <<x>> or the minimum element of the original tree *)
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
  rewrite -> (fold_unfold_insert_hbt_helper A compare x h bt) in H_insert_hbt.
  rewrite -> (fold_unfold_traverse_to_check_ordered_hbt A h bt compare) in H_ord_hbt.
  exact (H_ind_bt h hbt' x min min' max max' H_sound_hbt H_bal_hbt H_insert_hbt H_ord_hbt' H_ord_hbt).

  (* a leaf provides a vacuous case *)
  intros h hbt' x min min' max max' H_insert_hbt H_sound_hbt H_bal_hbt H_ord_hbt' H_ord_hbt.
  rewrite -> (fold_unfold_traverse_to_check_ordered_bt_leaf A compare) in H_ord_hbt.
  discriminate.

  (* proof for node, with t as inductive hypothesis *)
  intros t H_ind_t h hbt' x min min' max max' H_sound_hbt H_bal_hbt H_insert_bt H_ord_hbt' H_ord_bt.
  rewrite -> (fold_unfold_insert_bt_helper_node A compare x h t) in H_insert_bt.
  rewrite -> (fold_unfold_traverse_to_check_ordered_bt_node A t compare) in H_ord_bt.
  exact (H_ind_t h hbt' x min min' max max' H_sound_hbt H_bal_hbt H_insert_bt H_ord_hbt' H_ord_bt).

  (* proof for t, with inductive hypotheses for hbt1 and hbt2 *)
  intros hbt1 H_hbt1 e hbt2 H_hbt2 h hbt' x t_min t_min' t_max t_max' H_sound_hbt H_bal_hbt
         H_insert_hbt H_ord_hbt' H_ord_t.  
  
  (* the long and arduous journey into the insert function *)

  destruct (triple_sound_implies_hbts_sound A h hbt1 e hbt2 H_sound_hbt)
    as [H_hbt1_sound H_hbt2_sound].
  destruct (triple_balanced_implies_hbts_balanced A h hbt1 e hbt2 H_bal_hbt)
    as [H_hbt1_bal H_hbt2_bal].

  rewrite -> (fold_unfold_insert_t_helper A compare x h hbt1 e hbt2) in H_insert_hbt.
  case (compare x e) as [ | | ] eqn : C_comp_x_e.
  case (insert_hbt_helper A compare x hbt1) as [ hbt1'| ] eqn : C_insert_hbt1.
  induction hbt1' as [h1' bt1'].

  case (compare_int h1' (2 + project_height_hbt A hbt2))
    as [ | | ] eqn : C_comp_heights.       

  (* height diff is less than 2: no rotations required *)
  - rewrite -> (some_x_equal_some_y
                  (heightened_binary_tree A)
                  (HNode A (1 + max h1' (project_height_hbt A hbt2))
                         (Node A (Triple A (HNode A h1' bt1') e hbt2)))
                  hbt') in H_insert_hbt.
    rewrite <- H_insert_hbt in H_ord_hbt'.
    (* unfold for hbt' *)
    rewrite -> 
            (fold_unfold_traverse_to_check_ordered_hbt
               A
               (1 + max h1' (project_height_hbt A hbt2))
               (Node A (Triple A (HNode A h1' bt1') e hbt2))) in H_ord_hbt'.
    rewrite ->
            (fold_unfold_traverse_to_check_ordered_bt_node
               A
               (Triple A (HNode A h1' bt1') e hbt2)) in H_ord_hbt'.
    rewrite ->
            (fold_unfold_traverse_to_check_ordered_t
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
      * rewrite -> (fold_unfold_traverse_to_check_ordered_t A hbt1 e hbt2 compare)
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
      * rewrite -> (fold_unfold_traverse_to_check_ordered_t A hbt1 e hbt2 compare)
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
    rewrite -> fold_unfold_traverse_to_check_ordered_t in H_ord_t.
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
      exact (rotate_right_1_impossible_case
               A compare x h1 bt1
               h1' h11' h12' h121' h122' 
               bt11' bt121' bt122' e1 e12
               C_insert_hbt1).
      rewrite -> fold_unfold_traverse_to_check_ordered_hbt in C_traverse_ord_hbt1.
      induction bt1 as [ | t1].
      rewrite -> fold_unfold_traverse_to_check_ordered_bt_leaf in C_traverse_ord_hbt1.      
      unfold not in H_impossible_hbt1.
      assert (H_trivial_leaf : Leaf A = Leaf A).
      reflexivity.
      apply H_impossible_hbt1 in H_trivial_leaf.
      discriminate.
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

      destruct (disjunction_to_prop (h12' + 1 =n= h11') (h12' =n= h11') C_h12'_h11')
               as [H_h12'_gt_h11' | H_ht12'_eq_h11'].

      (* case 1: H_h12'_gt_h11' *) 
      assert (H_impossible_hbt1 : bt1 <> Leaf A).
      exact (rotate_right_2_impossible_case_1
               A compare x h1 bt1
               h1' h11' h12'
               bt11' bt12' e1
               C_insert_hbt1
               H_h12'_gt_h11').
      
      assert (H_contradiction: bt1 = Leaf A).
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
    case (compare_int h2' (2 + project_height_hbt A hbt1))
      as [ | | ] eqn : C_comp_heights.
    
    (* height diff is less than 2: no rotations required *) 
    + rewrite -> some_x_equal_some_y in H_insert_hbt.
      rewrite <- H_insert_hbt in H_ord_hbt'.
      (* unfold for hbt' *)
      rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H_ord_hbt'.
      rewrite -> fold_unfold_traverse_to_check_ordered_bt_node in H_ord_hbt'.
      rewrite -> fold_unfold_traverse_to_check_ordered_t in H_ord_hbt'.      

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
          rewrite -> fold_unfold_traverse_to_check_ordered_t in H_ord_t.
          rewrite -> C_check_ord_hbt1 in H_ord_t.
          rewrite -> C_check_ord_hbt2 in H_ord_t.
          discriminate.

          (* hbt2 is a leaf: use lemmas defined earlier *)
          rewrite -> fold_unfold_traverse_to_check_ordered_t in H_ord_t.
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

          rewrite -> fold_unfold_traverse_to_check_ordered_t in H_ord_t.
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
          
          rewrite -> fold_unfold_traverse_to_check_ordered_t in H_ord_t.
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
      assert (H_fold_t_ord:
                is_ordered_hbt A (HNode A h (Node A ((Triple A (HNode A h1 bt1) e hbt2))))
                               compare = true).
      unfold is_ordered_hbt.
      rewrite -> fold_unfold_traverse_to_check_ordered_hbt. 
      rewrite -> fold_unfold_traverse_to_check_ordered_bt_node.     
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
      exact (rotate_left_1_impossible_case
               A compare
               x h2 bt2 h2' h21' h211' h212' h22'
               bt211' bt212' bt22'
               e21 e2
               C_insert_hbt2).
      
      rewrite -> fold_unfold_traverse_to_check_ordered_hbt in C_traverse_ord_hbt2.
      induction bt2 as [ | t2].
      rewrite -> fold_unfold_traverse_to_check_ordered_bt_leaf in C_traverse_ord_hbt2.      
      unfold not in H_impossible_hbt2.
      assert (H_trivial_leaf : Leaf A = Leaf A).
      reflexivity.
      apply H_impossible_hbt2 in H_trivial_leaf.
      discriminate.
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
      exact (rotate_left_2_impossible_case_1
               A compare x h2 bt2
               h2' h21' h22'
               bt21' bt22' e2
               C_insert_hbt2
               H_h22'_gt_h21').
      
      assert (H_contradiction: bt2 = Leaf A).
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

(* ********** *)

(* ********** *)

(** * Rotations Preserves Order *)

(** When dealing with rotations in [ordered_helper], the notions of a first rotation
and a second rotation were used to refer to the double and single rotations. While
this corresponds to the way rotations are treated in the implementation of
rotations in [hbt], the resulting proofs were repetitive and long. Thus, in this
section, we instead develop our proofs with the following ideas in mind:

- <<rotate_right_2>> and <<rotate_left_2>> correspond to the elementary rotate right and rotate left opertations
- The double rotation <<rotate_right_1>> results from composing an elementery rotate left operation on a sub-tree followed by an elementary rotate right operation on the entire tree
- The double rotation <<rotate_left_1>> results from composing an elementery rotate right operation on a sub-tree followed by an elementary rotate left operation on the entire tree. 
*)

(* ***** *)

(** ** Helper Lemmas for Rotations *)

(** Lemma to show that given two sub-trees <<hbt1>>, <<hbt2>> and a payload <<e>> such that: 

- <<hbt1>> is ordered and has a minimum and maximum payload
- the maximum payload of <<hbt1>> is less than <<e>>
- <<hbt2>> is ordered
- if <<hbt2>> has a minimum and a maximum, then <<e>> is less than this minimum, 

then the tree with <<e>> as root, <<hbt1>> as left sub-tree and <<hbt2>> as right 
sub-tree is ordered, i.e., traversing the tree to check if it is ordered returns a 
minimum and maximum
*)
Lemma rotate_right_intermediate_tree_ordered:
  forall (A : Type)
         (compare : A -> A -> element_comparison)
         (h1 : nat)
         (bt1 : binary_tree A)
         (e : A)
         (h2 : nat)
         (bt2 : binary_tree A)
         (min1 max1 : A),
    traverse_to_check_ordered_hbt A (HNode A h1 bt1) compare =
    TSome (A * A) (min1, max1) ->
    compare max1 e = Lt ->
    is_ordered_hbt A (HNode A h2 bt2) compare = true -> 
    (forall min2 max2 : A,
        traverse_to_check_ordered_hbt A (HNode A h2 bt2) compare =
        TSome (A * A) (min2, max2) -> compare e min2 = Lt) ->
    exists max2,
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

  (* unfold goal first *)
  rewrite -> fold_unfold_traverse_to_check_ordered_hbt.
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_node.
  rewrite -> fold_unfold_traverse_to_check_ordered_t.
  rewrite -> H.

  (* next, consider the two cases for bt2 *)
  destruct (is_ordered_true_implies_leaf_or_ordered_node
              A compare (HNode A h2 bt2) H1)
    as [H_hbt2_leaf | [min2 [max2 H_hbt2_node]]].

  (* bt2 is a leaf *)
  - rewrite -> H0.
    rewrite -> H_hbt2_leaf.
    exists e.
    reflexivity.

  (* bt2 is a node *)
  - rewrite -> H0.
    rewrite -> H_hbt2_node.
    rewrite -> (H2 min2 max2 H_hbt2_node).
    exists max2.
    reflexivity.
Qed.

(** Lemma to show that given two sub-trees <<hbt1>>, <<hbt2>> and a payload <<e>> such that: 

- <<hbt2>> is ordered and has a minimum and maximum payload
- the minimum payload of <<hbt2>> is less than <<e>>
- <<hbt1>> is ordered
- if <<hbt1>> has a minimum and a maximum, then this maximum is less than <<e>>, 

then the tree with <<e>> as root, <<hbt1>> as left sub-tree and <<hbt2>> as right 
sub-tree is ordered, i.e., traversing the tree to check if it is ordered returns a 
minimum and maximum
*)
Lemma rotate_left_intermediate_tree_ordered:
  forall (A : Type)
         (compare : A -> A -> element_comparison)
         (h1 : nat)
         (bt1 : binary_tree A)
         (e : A)
         (h2 : nat)
         (bt2 : binary_tree A)
         (min2 max2 : A),
    is_ordered_hbt A (HNode A h1 bt1) compare = true ->     
    (forall min1 max1 : A,
        traverse_to_check_ordered_hbt A (HNode A h1 bt1) compare =
        TSome (A * A) (min1, max1) -> compare max1 e = Lt) ->
    traverse_to_check_ordered_hbt A (HNode A h2 bt2) compare =
    TSome (A * A) (min2, max2) ->
    compare e min2 = Lt ->
    exists min1,
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

  (* unfold all the values first *)
  rewrite -> fold_unfold_traverse_to_check_ordered_hbt.
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_node.
  rewrite -> fold_unfold_traverse_to_check_ordered_t.
  rewrite -> H1.

  (* now consider the two cases for bt1 *)
  destruct (is_ordered_true_implies_leaf_or_ordered_node
              A compare (HNode A h1 bt1) H) as [H_hbt1_leaf | H_hbt1_node].

  (* hbt1 is a leaf *)
  - rewrite -> H_hbt1_leaf.
    rewrite -> H2.
    exists e.
    reflexivity.

  (* hbt2 is a node *)
  - destruct H_hbt1_node as [min1 [max1 H_hbt1_node]].
    rewrite -> H_hbt1_node.
    rewrite -> (H0 min1 max1 H_hbt1_node).
    rewrite -> H2.
    exists min1.
    reflexivity.
Qed.

(** Lemma to show that an elementary right rotation operation preserves order *)
Lemma rotate_right_preserves_order:
  forall (A : Type)
         (compare : A -> A -> element_comparison)
         (h11 : nat)
         (bt11 : binary_tree A)
         (e1 : A)
         (h12 : nat)
         (bt12 : binary_tree A)
         (e : A)
         (h2 : nat)
         (bt2 : binary_tree A)
         (t_min t_max : A), 
    traverse_to_check_ordered_hbt
      A (HNode A (1 + max (1 + max h11 h12) h2)
               (Node A (Triple A
                               (HNode A (1 + max h11 h12)
                                      (Node A (Triple A
                                                      (HNode A h11 bt11)
                                                      e1
                                                      (HNode A h12 bt12))))
                               e
                               (HNode A h2 bt2)))) compare =
    TSome (A * A) (t_min, t_max) -> 
    traverse_to_check_ordered_hbt
      A (HNode A (1 + max h11 (1 + max h12 h2))
               (Node A (Triple A
                               (HNode A h11 bt11)
                               e1
                               (HNode A (1 + max h12 h2)
                                      (Node A (Triple A
                                                      (HNode A h12 bt12)
                                                      e
                                                      (HNode A h2 bt2)))))))
      compare = TSome (A * A) (t_min, t_max).
Proof.
  intros.

  (* we must first assert that the subtrees are ordered *)

  (* fold H *)
  assert (H_fold_traverse:
            is_ordered_hbt
              A
              (HNode A (1 + max (1 + max h11 h12) h2)
                     (Node A
                           (Triple A
                                   (HNode A (1 + max h11 h12)
                                          (Node A (Triple A
                                                          (HNode A h11 bt11)
                                                          e1
                                                          (HNode A h12 bt12))))
                                   e
                                   (HNode A h2 bt2)))) compare = true). 
  unfold is_ordered_hbt.
  rewrite -> H.
  reflexivity.

  (* next, we left reduce the original tree; this will be helpful in our proofs *)
  assert (H_hbt_org_left_reduced:
            traverse_to_check_ordered_hbt
              A
              (HNode A (1 + max (1 + max h11 h12) h2)
                     (Node A (Triple A (HNode A 0 (Leaf A)) e (HNode A h2 bt2))))
              compare = TSome (A * A) (e, t_max)).
  exact (reduce_ordered_hbt_left
           A compare (1 + max (1 + max h11 h12) h2)
           (HNode A (1 + max h11 h12)
                  (Node A (Triple A (HNode A h11 bt11) e1 (HNode A h12 bt12))))
           e
           (HNode A h2 bt2)
           t_min t_max H).
  
  (* assert orderedness of the left subtree and hbt2 *)
  destruct (triple_ordered_implies_hbts_ordered
              A compare (1 + max (1 + max h11 h12) h2)
              (HNode A (1 + max h11 h12)
                     (Node A (Triple A (HNode A h11 bt11) e1 (HNode A h12 bt12))))
              e
              (HNode A h2 bt2) H_fold_traverse) as [H_left_subtree_ord H_bt2_ord].
  destruct (triple_ordered_implies_hbts_ordered
              A compare (1 + max h11 h12)
              (HNode A h11 bt11) e1 (HNode A h12 bt12) H_left_subtree_ord)
    as [H_bt11_ord H_bt12_ord].

  (* assert required inequalities *)
  
  (* max11 < e1 *)
  assert (H_comp_max11_e1:
            forall (min11 max11 : A),
              traverse_to_check_ordered_hbt A (HNode A h11 bt11) compare =
              TSome (A * A) (min11, max11) ->
              compare max11 e1 = Lt).
  intros.
  unfold is_ordered_hbt in H_left_subtree_ord.
  rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H_left_subtree_ord.
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_node in H_left_subtree_ord.
  rewrite -> fold_unfold_traverse_to_check_ordered_t in H_left_subtree_ord.
  rewrite -> H0 in H_left_subtree_ord.
  case (compare max11 e1) as [ | | ].
  reflexivity.
  discriminate.
  discriminate.

  (* e1 < min12  *)
  assert (H_comp_e1_min12:
            forall (min12 max12 : A),
              traverse_to_check_ordered_hbt A (HNode A h12 bt12) compare =
              TSome (A * A) (min12, max12) ->
              compare e1 min12 = Lt).
  intros.
  unfold is_ordered_hbt in H_left_subtree_ord.
  rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H_left_subtree_ord.
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_node in H_left_subtree_ord.
  rewrite -> fold_unfold_traverse_to_check_ordered_t in H_left_subtree_ord.
  case (traverse_to_check_ordered_hbt A (HNode A h11 bt11) compare)
       as [ | | (min11, max11)].
  discriminate.
  rewrite -> H0 in H_left_subtree_ord.
  case (compare e1 min12) as [ | | ].
  reflexivity.
  discriminate.
  discriminate.
  assert (H_trivial_equality :
            TSome (A * A) (min11, max11) = TSome (A * A) (min11, max11)).
  reflexivity.
  rewrite -> (H_comp_max11_e1 min11 max11 H_trivial_equality) in H_left_subtree_ord.
  rewrite -> H0 in H_left_subtree_ord.
  case (compare e1 min12) as [ | | ].
  reflexivity.
  discriminate.
  discriminate.
  
  (* max12 < e *)
  assert (H_comp_max12_e:
            forall (min12 max12 : A),
              traverse_to_check_ordered_hbt A (HNode A h12 bt12) compare =
              TSome (A * A) (min12, max12) ->
              compare max12 e = Lt).
  intros.
  rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H.
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_node in H.
  rewrite -> fold_unfold_traverse_to_check_ordered_t in H.
  rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H.
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_node in H.
  rewrite -> fold_unfold_traverse_to_check_ordered_t in H.
  case (traverse_to_check_ordered_hbt A (HNode A h11 bt11) compare)
    as [ | | (min11, max11)].
  discriminate.
  rewrite -> H0 in H.
  rewrite -> (H_comp_e1_min12 min12 max12 H0) in H.
  case (compare max12 e) as [ | | ].
  reflexivity.
  discriminate.
  discriminate.
  rewrite -> (H_comp_max11_e1
                min11 max11
                (trivial_equality (triple_option (A * A))
                                  (TSome (A * A) (min11, max11)))) in H.
  rewrite -> H0 in H.
  rewrite -> (H_comp_e1_min12 min12 max12 H0) in H.
  case (compare max12 e) as [ | | ].
  reflexivity.
  discriminate.
  discriminate.

  (* e < min bt2 *)
  assert (H_comp_e_min2:
            forall (min2 max2 : A),
              traverse_to_check_ordered_hbt A (HNode A h2 bt2) compare =
              TSome (A * A) (min2, max2) ->
              compare e min2 = Lt).
  intros.
  rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H_hbt_org_left_reduced.
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_node in H_hbt_org_left_reduced.  
  rewrite -> fold_unfold_traverse_to_check_ordered_t in H_hbt_org_left_reduced.
  rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H_hbt_org_left_reduced.
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_leaf in H_hbt_org_left_reduced.  
  rewrite -> H0 in H_hbt_org_left_reduced.  
  case (compare e min2) as [ | | ].
  reflexivity.
  discriminate.
  discriminate.

  (* with the inequalities established, proceed to show the orderedness of the 
   * rotated tree *)

  (* we first show that the right subtree in the goal is ordered *)
  destruct (single_node_tree_is_ordered
              A compare h12 bt12 e h2 bt2 H_bt12_ord H_comp_max12_e
              H_bt2_ord H_comp_e_min2)
    as [min12 [max2 H_right_subtree_in_goal_ordered]].

  
  
  (* next, show that max2 = t_max; use the reduced tree for this *)
  assert (H_relate_max2_t_max: max2 = t_max).
  
  (* we may conveniently reduce the right subtree in the goal *)
  assert (H_right_subtree_in_goal_reduced_ord:
            traverse_to_check_ordered_hbt
              A
              (HNode A
                     (1 + max h12 h2)
                     (Node A (Triple A (HNode A 0 (Leaf A)) e (HNode A h2 bt2))))
              compare = TSome (A * A) (e, max2)).
  exact (reduce_ordered_hbt_left
           A compare (1 + max h12 h2)
           (HNode A h12 bt12) e (HNode A h2 bt2)
           min12 max2 H_right_subtree_in_goal_ordered).

  (* now unfold H_right_subtree_in_goal_reduced_ord *) 
  rewrite -> fold_unfold_traverse_to_check_ordered_hbt
    in H_right_subtree_in_goal_reduced_ord.
  rewrite -> fold_unfold_traverse_to_check_ordered_hbt
    in H_hbt_org_left_reduced.
  rewrite -> H_hbt_org_left_reduced in H_right_subtree_in_goal_reduced_ord.
  rewrite -> tsome_x_equal_tsome_y in H_right_subtree_in_goal_reduced_ord.
  rewrite -> pairwise_equality in H_right_subtree_in_goal_reduced_ord.
  destruct H_right_subtree_in_goal_reduced_ord as [_ H_we_need].
  symmetry.
  exact H_we_need.

  rewrite -> H_relate_max2_t_max in H_right_subtree_in_goal_ordered.

  (* next, we need to show that compare e1 min12 = Lt, to be able to use 
   * rotate_left_intermediate_tree_ordered *)
  assert (H_e1_lt_min12: compare e1 min12 = Lt).

  (* first, right reduce the right subtree in goal *)
  assert (H_right_subtree_right_reduced:
            traverse_to_check_ordered_hbt
              A
              (HNode A (1 + max h12 h2)
                     (Node A (Triple A (HNode A h12 bt12) e (HNode A 0 (Leaf A)))))
              compare = TSome (A * A) (min12, e)).
  exact (reduce_ordered_hbt_right
           A compare (1 + max h12 h2)
           (HNode A h12 bt12) e (HNode A h2 bt2) min12 t_max
           H_right_subtree_in_goal_ordered).

  (* now traverse this tree to get the different cases for hbt12 *)
  rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H_right_subtree_right_reduced.
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_node
    in H_right_subtree_right_reduced.
  rewrite -> fold_unfold_traverse_to_check_ordered_t in H_right_subtree_right_reduced.
  rewrite -> (fold_unfold_traverse_to_check_ordered_hbt A 0 (Leaf A))
    in H_right_subtree_right_reduced.
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_leaf
    in H_right_subtree_right_reduced.
  case (traverse_to_check_ordered_hbt A (HNode A h12 bt12) compare)
    as [ | | (min12', max12')] eqn : C_check_ord_bt12.

  (* consider the 3 cases *)
  discriminate.

  rewrite -> tsome_x_equal_tsome_y in H_right_subtree_right_reduced.
  rewrite -> pairwise_equality in H_right_subtree_right_reduced.
  destruct H_right_subtree_right_reduced as [H_e_min12 _].
  rewrite <- H_e_min12.

  (* traverse the original tree *)
  rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H.
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_node in H.
  rewrite -> fold_unfold_traverse_to_check_ordered_t in H.
  rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H.
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_node in H.
  rewrite -> fold_unfold_traverse_to_check_ordered_t in H.
  rewrite -> C_check_ord_bt12 in H.
  case (traverse_to_check_ordered_hbt A (HNode A h11 bt11) compare)
    as [ | | (min11, max11)] eqn : C_check_ord_bt11.
    
  discriminate.
    
  case (compare e1 e) as [ | | ].
  reflexivity.
  discriminate.
  discriminate.

  rewrite -> (H_comp_max11_e1
                min11 max11
                (trivial_equality (triple_option (A * A))
                                  (TSome (A * A) (min11, max11)))) in H.
  case (compare e1 e) as [ | | ].
    reflexivity.
    discriminate.
    discriminate.

    rewrite -> (H_comp_max12_e
                  min12' max12'
                  (trivial_equality (triple_option (A * A))
                                    (TSome (A * A) (min12', max12'))))
      in H_right_subtree_right_reduced.
    rewrite -> tsome_x_equal_tsome_y in H_right_subtree_right_reduced.
    rewrite -> pairwise_equality in H_right_subtree_right_reduced.
    destruct H_right_subtree_right_reduced as [H_min12'_min12 _].
    
    assert (H_comp_e1_min12': compare e1 min12' = Lt).
    exact (H_comp_e1_min12
             min12' max12'
             (trivial_equality (triple_option (A * A))
                               (TSome (A * A) (min12', max12')))).
    
    rewrite <- H_min12'_min12.
    exact H_comp_e1_min12'.

    (* with H_e1_lt_min12 finally established, we may use 
     * rotate_left_intermediate_tree_ordered to show that the tree in the 
     * goal is ordered *)
    destruct (rotate_left_intermediate_tree_ordered
                A compare h11 bt11 e1 (1 + max h12 h2)
                (Node A (Triple A (HNode A h12 bt12) e (HNode A h2 bt2)))
                min12 t_max
                H_bt11_ord
                H_comp_max11_e1
                H_right_subtree_in_goal_ordered
                H_e1_lt_min12) as [min11 H_rotated_tree_ordered].

    (* Finally, we must show that min11 = t_min *)

    assert (H_min11_t_min: min11 = t_min). 
    
    (* first, right reduce the rotated tree *)
    assert (H_rotated_tree_reduced:
              traverse_to_check_ordered_hbt
                A
                (HNode A (1 + max h11 (1 + max h12 h2))
                       (Node A (Triple A
                                       (HNode A h11 bt11)
                                       e1
                                       (HNode A 0 (Leaf A))))) compare =
              TSome (A * A) (min11, e1)).
    exact (reduce_ordered_hbt_right
             A compare (1 + max h11 (1 + max h12 h2))
             (HNode A h11 bt11)
             e1
             (HNode A (1 + max h12 h2)
                    (Node A
                          (Triple A (HNode A h12 bt12) e (HNode A h2 bt2))))
             min11 t_max H_rotated_tree_ordered).

    (* now unfold the reduced rotated tree *)
    rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H_rotated_tree_reduced.
    rewrite -> fold_unfold_traverse_to_check_ordered_bt_node in H_rotated_tree_reduced.
    rewrite -> fold_unfold_traverse_to_check_ordered_t in H_rotated_tree_reduced.
    rewrite -> (fold_unfold_traverse_to_check_ordered_hbt A 0 (Leaf A))
      in H_rotated_tree_reduced.
    rewrite -> fold_unfold_traverse_to_check_ordered_bt_leaf in H_rotated_tree_reduced.
    
    (* now left reduce the original tree *)
    assert (H_org_tree_right_reduced:
              traverse_to_check_ordered_hbt
                A
                (HNode A (1 + max (1 + max h11 h12) h2)
                       (Node A
                             (Triple A
                                     (HNode A (1 + max h11 h12)
                                            (Node A (Triple A
                                                            (HNode A h11 bt11)
                                                            e1
                                                            (HNode A h12 bt12)))) e
                                     (HNode A 0 (Leaf A))))) compare = 
              TSome (A * A) (t_min, e)).
    exact (reduce_ordered_hbt_right
             A compare (1 + max (1 + max h11 h12) h2)
             (HNode A (1 + max h11 h12)
                    (Node A (Triple A (HNode A h11 bt11) e1 (HNode A h12 bt12))))
             e
             (HNode A h2 bt2)
             t_min t_max H).

    (* now unfold the reduced original tree *)
    rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H_org_tree_right_reduced.
    rewrite -> fold_unfold_traverse_to_check_ordered_bt_node in H_org_tree_right_reduced.
    rewrite -> fold_unfold_traverse_to_check_ordered_t in H_org_tree_right_reduced.
    rewrite -> (fold_unfold_traverse_to_check_ordered_hbt A 0 (Leaf A))
      in H_org_tree_right_reduced.
    rewrite -> fold_unfold_traverse_to_check_ordered_bt_leaf in H_org_tree_right_reduced.
    case (traverse_to_check_ordered_hbt
            A
            (HNode A (1 + max h11 h12)
                   (Node A
                         (Triple A (HNode A h11 bt11) e1 (HNode A h12 bt12))))
            compare) as [ | | (min11', max12)] eqn : C_check_ord_left_subtree.
    
    discriminate.
    
    destruct (ordered_node_has_min_max
                  A compare (1 + max h11 h12)
                  (HNode A h11 bt11) e1 (HNode A h12 bt12) H_left_subtree_ord)
      as [some_min [some_max H_we_need]].
    rewrite -> fold_unfold_traverse_to_check_ordered_hbt in C_check_ord_left_subtree.
    rewrite -> H_we_need in C_check_ord_left_subtree.
    discriminate.
    
    case (compare max12 e) as [ | | ].
    rewrite -> tsome_x_equal_tsome_y in H_org_tree_right_reduced.
    rewrite -> pairwise_equality in H_org_tree_right_reduced.
    destruct H_org_tree_right_reduced as [H_min11'_t_min _].

    (* with the required relationship between min11' and t_min established, we now
     * reduce thte left subtree further *)
    assert (H_reduced_left_subtree_ord:
              traverse_to_check_ordered_hbt
                A
                (HNode A (1 + max h11 h12)
                       (Node A (Triple A (HNode A h11 bt11) e1 (HNode A 0 (Leaf A)))))
                compare = TSome (A * A) (min11', e1)).
    exact (reduce_ordered_hbt_right
             A compare (1 + max h11 h12)
             (HNode A h11 bt11) e1 (HNode A h12 bt12)
             min11' max12 C_check_ord_left_subtree).

    (* now unfold the reduced tree *)
    rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H_reduced_left_subtree_ord.
    rewrite -> fold_unfold_traverse_to_check_ordered_bt_node
      in H_reduced_left_subtree_ord.    
    rewrite -> fold_unfold_traverse_to_check_ordered_t in H_reduced_left_subtree_ord.
    rewrite -> (fold_unfold_traverse_to_check_ordered_hbt A 0 (Leaf A))
      in H_reduced_left_subtree_ord.
    rewrite -> fold_unfold_traverse_to_check_ordered_bt_leaf
      in H_reduced_left_subtree_ord.

    (* now rewrite the hypothesis for the reduced goal tree in the reduced subtree *)
    rewrite -> H_rotated_tree_reduced in H_reduced_left_subtree_ord.
    rewrite -> tsome_x_equal_tsome_y in H_reduced_left_subtree_ord.
    rewrite -> pairwise_equality in H_reduced_left_subtree_ord.
    destruct H_reduced_left_subtree_ord as [H_min11_min11' _].

    (* finally, put togehter all the equalties to prove our goal *)
    rewrite <- H_min11_min11' in H_min11'_t_min.
    exact H_min11'_t_min.
    
    discriminate.
    discriminate.

    (* now rewrite min11 with t_min, and we're done! *)
    rewrite -> H_min11_t_min in H_rotated_tree_ordered.
    exact H_rotated_tree_ordered.
Qed.

(** Lemma to show that an elementary left rotation operation preserves order *)
Lemma rotate_left_preserves_order:
  forall (A : Type)
         (compare : A -> A -> element_comparison)
         (h1 : nat)
         (bt1 : binary_tree A)
         (e : A)
         (h21 : nat)
         (bt21 : binary_tree A)
         (e2 : A)
         (h22 : nat)
         (bt22 : binary_tree A)
         (t_min t_max : A),
    traverse_to_check_ordered_hbt
      A (HNode A (1 + max h1 (1 + max h21 h22))
               (Node A (Triple A
                               (HNode A h1 bt1)
                               e
                               (HNode A (1 + max h21 h22)
                                      (Node A (Triple A
                                                      (HNode A h21 bt21)
                                                      e2
                                                      (HNode A h22 bt22)))))))
      compare = TSome (A * A) (t_min, t_max) ->
    traverse_to_check_ordered_hbt
      A (HNode A (1 + max (1 + max h1 h21) h22)
               (Node A (Triple A
                               (HNode A (1 + max h1 h21)
                                      (Node A (Triple A
                                                      (HNode A h1 bt1)
                                                      e
                                                      (HNode A h21 bt21))))
                               e2
                               (HNode A h22 bt22)))) compare =
    TSome (A * A) (t_min, t_max).
Proof.
  intros.

  (* we must first assert that the subtrees are ordered *)

  (* fold H *)
  assert (H_fold_traverse:
            is_ordered_hbt
              A
              (HNode A (1 + max h1 (1 + max h21 h22))
                     (Node A
                           (Triple A
                                   (HNode A h1 bt1)
                                   e
                                   (HNode A (1 + max h21 h22)
                                          (Node A (Triple A (HNode A h21 bt21)
                                                          e2
                                                          (HNode A h22 bt22)))))))
              compare = true).
  unfold is_ordered_hbt.
  rewrite -> H.
  reflexivity.

  (* next, right reduce the original tree *)
  assert (H_hbt_org_right_reduced:
            traverse_to_check_ordered_hbt
              A
              (HNode A (1 + max h1 (1 + max h21 h22))
                     (Node A (Triple A
                                     (HNode A h1 bt1)
                                     e
                                     (HNode A 0 (Leaf A))))) compare =
            TSome (A * A) (t_min, e)).
  exact (reduce_ordered_hbt_right
           A compare (1 + max h1 (1 + max h21 h22))
           (HNode A h1 bt1)
           e
           (HNode A (1 + max h21 h22)
                  (Node A (Triple A (HNode A h21 bt21) e2 (HNode A h22 bt22))))
           t_min t_max H).

  

  (* assert orderedness of the left subtree and hbt2 *)
  destruct (triple_ordered_implies_hbts_ordered
              A compare (1 + max h1 (1 + max h21 h22))
              (HNode A h1 bt1)
              e
              (HNode A (1 + max h21 h22)
                     (Node A (Triple A (HNode A h21 bt21) e2 (HNode A h22 bt22))))
              H_fold_traverse) as [H_bt1_ord H_right_subtree_ord].
  destruct (triple_ordered_implies_hbts_ordered
              A compare (1 + max h21 h22)
              (HNode A h21 bt21) e2 (HNode A h22 bt22) H_right_subtree_ord)
    as [H_bt21_ord H_bt22_ord].



  (* left reduce the original tree *)
  assert (H_hbt_org_left_reduced:
            traverse_to_check_ordered_hbt
              A
              (HNode A (1 + max h1 (1 + max h21 h22))
                     (Node A
                           (Triple A (HNode A 0 (Leaf A))
                                   e
                                   (HNode A (1 + max h21 h22)
                                          (Node A (Triple A (HNode A h21 bt21)
                                                          e2
                                                          (HNode A h22 bt22)))))))
              compare = TSome (A * A) (e, t_max)).
  exact (reduce_ordered_hbt_left
           A compare (1 + max h1 (1 + max h21 h22))
           (HNode A h1 bt1)
           e
           (HNode A (1 + max h21 h22)
                  (Node A (Triple A (HNode A h21 bt21) e2 (HNode A h22 bt22))))
           t_min t_max H).

  (* assert a useful hypothesis concerning the right subtree *)
  assert (H_org_right_subtree:
            exists min_rs,
              traverse_to_check_ordered_hbt
                A
                (HNode A (1 + max h21 h22)
                       (Node A (Triple A (HNode A h21 bt21) e2 (HNode A h22 bt22))))
                compare = TSome (A * A) (min_rs, t_max)).
  rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H_hbt_org_left_reduced.
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_node in H_hbt_org_left_reduced.
  rewrite -> fold_unfold_traverse_to_check_ordered_t in H_hbt_org_left_reduced.
  rewrite -> (fold_unfold_traverse_to_check_ordered_hbt A 0 (Leaf A))
    in H_hbt_org_left_reduced.
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_leaf in H_hbt_org_left_reduced.
  case (traverse_to_check_ordered_hbt
          A
          (HNode A (1 + max h21 h22)
                 (Node A (Triple A (HNode A h21 bt21) e2 (HNode A h22 bt22))))
          compare) as [ | | (min21, max22)] eqn : C_check_ord_right_subtree.
  discriminate.
  destruct (ordered_node_has_min_max
              A compare (1 + max h21 h22)
              (HNode A h21 bt21) e2 (HNode A h22 bt22)
              H_right_subtree_ord) as [smin [smax H_we_need]].
  assert (H_we_actually_need:
            traverse_to_check_ordered_hbt
              A
              (HNode A (1 + max h21 h22)
                     (Node A (Triple A
                                     (HNode A h21 bt21)
                                     e2
                                     (HNode A h22 bt22)))) compare =
            TSome (A * A) (smin, smax)).
  rewrite -> fold_unfold_traverse_to_check_ordered_hbt.
  exact H_we_need.
  rewrite -> H_we_actually_need in C_check_ord_right_subtree.
  discriminate.
  case (compare e min21) as [ | | ].
  rewrite -> tsome_x_equal_tsome_y in H_hbt_org_left_reduced.
  rewrite -> pairwise_equality in H_hbt_org_left_reduced.
  destruct H_hbt_org_left_reduced as [_ H_max22_t_max].
  exists min21.
  rewrite -> H_max22_t_max.
  reflexivity.
  discriminate.
  discriminate.

  destruct H_org_right_subtree as [min_rs H_org_right_subtree].
  
  (* assert required inequalities *)
  
  (* max11 < e1 *)
  assert (H_comp_max1_e:
            forall (min1 max1 : A),
              traverse_to_check_ordered_hbt A (HNode A h1 bt1) compare =
              TSome (A * A) (min1, max1) ->
              compare max1 e = Lt).
  intros.
  (* use the right reduced version of the original tree *)
  rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H_hbt_org_right_reduced.
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_node in H_hbt_org_right_reduced.
  rewrite -> fold_unfold_traverse_to_check_ordered_t in H_hbt_org_right_reduced.
  rewrite -> (fold_unfold_traverse_to_check_ordered_hbt A 0 (Leaf A))
    in H_hbt_org_right_reduced.
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_leaf in H_hbt_org_right_reduced.
  rewrite -> H0 in H_hbt_org_right_reduced.
  case (compare max1 e) as [ | | ].
  reflexivity.
  discriminate.
  discriminate.
  
  (* max21 < e2 *)
  assert (H_comp_max21_e2:
            forall (min21 max21 : A),
              traverse_to_check_ordered_hbt A (HNode A h21 bt21) compare =
              TSome (A * A) (min21, max21) ->
              compare max21 e2 = Lt).
  intros.
  rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H_org_right_subtree.
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_node in H_org_right_subtree.
  rewrite -> fold_unfold_traverse_to_check_ordered_t in H_org_right_subtree.
  rewrite -> H0 in H_org_right_subtree.
  case (compare max21 e2) as [ | | ].
  reflexivity.
  discriminate.
  discriminate.

  (* e < min21 *)
  assert (H_comp_e_min21:
            forall (min21 max21 : A),
              traverse_to_check_ordered_hbt A (HNode A h21 bt21) compare =
              TSome (A * A) (min21, max21) ->
              compare e min21 = Lt).
  intros.
  rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H_hbt_org_left_reduced.
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_node in H_hbt_org_left_reduced.
  rewrite -> fold_unfold_traverse_to_check_ordered_t in H_hbt_org_left_reduced.
  rewrite -> (fold_unfold_traverse_to_check_ordered_hbt A 0 (Leaf A))
    in H_hbt_org_left_reduced. 
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_leaf in H_hbt_org_left_reduced.
  rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H_hbt_org_left_reduced.
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_node in H_hbt_org_left_reduced.
  rewrite -> fold_unfold_traverse_to_check_ordered_t in H_hbt_org_left_reduced.
  rewrite -> H0 in H_hbt_org_left_reduced.
  rewrite -> (H_comp_max21_e2 min21 max21 H0) in H_hbt_org_left_reduced.
  case (traverse_to_check_ordered_hbt A (HNode A h22 bt22) compare)
    as [ | | (min22, max22)].
  discriminate.
  case (compare e min21) as [ | | ].
  reflexivity.
  discriminate.
  discriminate.
  case (compare e2 min22) as [ | | ].
  case (compare e min21) as [ | | ].
  reflexivity.
  discriminate.
  discriminate.
  discriminate.
  discriminate.

  (* e2 < min22 *)
  assert (H_comp_e2_min22:
            forall (min22 max22 : A),
              traverse_to_check_ordered_hbt A (HNode A h22 bt22) compare =
              TSome (A * A) (min22, max22) ->
              compare e2 min22 = Lt).
  intros.
  rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H_org_right_subtree.
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_node in H_org_right_subtree.
  rewrite -> fold_unfold_traverse_to_check_ordered_t in H_org_right_subtree.
  case (traverse_to_check_ordered_hbt A (HNode A h21 bt21) compare)
    as [ | | (min21, max21)].
  discriminate.
  rewrite -> H0 in H_org_right_subtree.
  case (compare e2 min22) as [ | | ].
  reflexivity.
  discriminate.
  discriminate.
  rewrite -> H0 in H_org_right_subtree.
  case (compare max21 e2) as [ | | ].
  case (compare e2 min22) as [ | | ].
  reflexivity.
  discriminate.
  discriminate.
  discriminate.
  discriminate.

  (* with the inequalities established, proceed to show the orderedness of the 
   * rotated tree *)

  (* we first show that the left subtree in the goal is ordered *)
  destruct (single_node_tree_is_ordered
              A compare h1 bt1 e h21 bt21 H_bt1_ord H_comp_max1_e
              H_bt21_ord H_comp_e_min21)
    as [min1 [max21 H_left_subtree_in_goal_ordered]].

  (* next, show that min1 = t_min; use the reduced tree for this *)
  assert (H_relate_min1_t_min: min1 = t_min).
  
  assert (H_left_subtree_in_goal_reduced_ord:
            traverse_to_check_ordered_hbt
              A
              (HNode A (1 + max h1 h21)
                     (Node A (Triple A
                                     (HNode A h1 bt1)
                                     e
                                     (HNode A 0 (Leaf A)))))
              compare = TSome (A * A) (min1, e)).
  exact (reduce_ordered_hbt_right
           A compare
           (1 + max h1 h21)
           (HNode A h1 bt1) e (HNode A h21 bt21)
           min1 max21
           H_left_subtree_in_goal_ordered).
  (* now unfold H_left_subtree_in_goal_reduced_ord *) 
  rewrite -> fold_unfold_traverse_to_check_ordered_hbt
    in H_left_subtree_in_goal_reduced_ord.
  rewrite -> fold_unfold_traverse_to_check_ordered_hbt
    in H_hbt_org_right_reduced.
  rewrite -> H_hbt_org_right_reduced in H_left_subtree_in_goal_reduced_ord.
  rewrite -> tsome_x_equal_tsome_y in H_left_subtree_in_goal_reduced_ord.
  rewrite -> pairwise_equality in H_left_subtree_in_goal_reduced_ord.
  destruct H_left_subtree_in_goal_reduced_ord as [H_we_need _].
  symmetry.
  exact H_we_need.

  rewrite -> H_relate_min1_t_min in H_left_subtree_in_goal_ordered.

  (* next, we need to show that compare max21 e2 = Lt, to be able to use 
   * rotate_right_intermediate_tree_ordered *)
  assert (H_max21_lt_e2: compare max21 e2 = Lt).

  (* we first left reduce the left subtree of the goal *)
  assert (H_left_subtree_in_goal_reduced:
            traverse_to_check_ordered_hbt
              A
              (HNode A (1 + max h1 h21)
                     (Node A (Triple A (HNode A 0 (Leaf A)) e (HNode A h21 bt21))))
              compare = TSome (A * A) (e, max21)).
  exact (reduce_ordered_hbt_left
           A compare (1 + max h1 h21)
           (HNode A h1 bt1) e (HNode A h21 bt21)
           t_min max21
           H_left_subtree_in_goal_ordered).
  
  (* next, right reduce the right subtree of the orginal tree *)
  assert (H_hbt_org_right_subtree_reduced:
            traverse_to_check_ordered_hbt
              A
              (HNode A (1 + max h21 h22)
                     (Node A (Triple A
                                     (HNode A h21 bt21)
                                     e2
                                     (HNode A 0 (Leaf A))))) compare =
            TSome (A * A) (min_rs, e2)).
  exact (reduce_ordered_hbt_right
           A compare (1 + max h21 h22)
           (HNode A h21 bt21) e2 (HNode A h22 bt22)
           min_rs t_max H_org_right_subtree).

  (* now unfold both reduced trees *)
  rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H_left_subtree_in_goal_reduced.
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_node
    in H_left_subtree_in_goal_reduced.
  rewrite -> fold_unfold_traverse_to_check_ordered_t in H_left_subtree_in_goal_reduced.
  rewrite -> (fold_unfold_traverse_to_check_ordered_hbt A 0 (Leaf A))
    in H_left_subtree_in_goal_reduced.
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_leaf
    in H_left_subtree_in_goal_reduced.
  
  rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H_hbt_org_right_subtree_reduced.
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_node
    in H_hbt_org_right_subtree_reduced.
  rewrite -> fold_unfold_traverse_to_check_ordered_t in H_hbt_org_right_subtree_reduced.
  rewrite -> (fold_unfold_traverse_to_check_ordered_hbt A 0 (Leaf A))
    in H_hbt_org_right_subtree_reduced.
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_leaf
    in H_hbt_org_right_subtree_reduced. 

  (* now we can consider the cases for hbt21 *)
  case (traverse_to_check_ordered_hbt A (HNode A h21 bt21) compare)
    as [ | | (min21', max21')] eqn : C_check_ord_bt21.
  
  discriminate.
  
  rewrite -> tsome_x_equal_tsome_y in H_left_subtree_in_goal_reduced.
  rewrite -> pairwise_equality in H_left_subtree_in_goal_reduced.
  destruct H_left_subtree_in_goal_reduced as [_ H_e_max21].
  rewrite -> tsome_x_equal_tsome_y in H_hbt_org_right_subtree_reduced.
  rewrite -> pairwise_equality in H_hbt_org_right_subtree_reduced.
  destruct H_hbt_org_right_subtree_reduced as [H_e2_min_rs _].
  rewrite <- H_e_max21.

  (* for the leaf case, we must show that e < e2; unfold the left reduced
   * form of the original tree for this *)
  rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H_hbt_org_left_reduced.
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_node in H_hbt_org_left_reduced.
  rewrite -> fold_unfold_traverse_to_check_ordered_t in H_hbt_org_left_reduced.
  rewrite -> (fold_unfold_traverse_to_check_ordered_hbt A 0 (Leaf A))
    in H_hbt_org_left_reduced. 
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_leaf in H_hbt_org_left_reduced.
  rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H_hbt_org_left_reduced.
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_node in H_hbt_org_left_reduced.
  rewrite -> fold_unfold_traverse_to_check_ordered_t in H_hbt_org_left_reduced.
  rewrite -> C_check_ord_bt21 in H_hbt_org_left_reduced.
  case (traverse_to_check_ordered_hbt A (HNode A h22 bt22) compare)
    as [ | | (min22, max22)] eqn : C_check_ord_hbt22.
  discriminate.
  
  case (compare e e2) as [ | | ].
  reflexivity.
  discriminate.
  discriminate.
  
  rewrite -> (H_comp_e2_min22
                min22 max22
                (trivial_equality (triple_option (A * A))
                                  (TSome (A * A) (min22, max22))))
    in H_hbt_org_left_reduced.
  case (compare e e2) as [ | | ].
  reflexivity.
  discriminate.
  discriminate.

  (* for the node case, we use the inequalities already established *)
  rewrite ->  (H_comp_e_min21
                 min21' max21'
                 (trivial_equality (triple_option (A * A))
                                   (TSome (A * A) (min21', max21'))))
    in H_left_subtree_in_goal_reduced.
  rewrite -> tsome_x_equal_tsome_y in H_left_subtree_in_goal_reduced.
  rewrite -> pairwise_equality in H_left_subtree_in_goal_reduced.
  destruct H_left_subtree_in_goal_reduced as [_ H_max21'_max21].
  assert (H_we_need: compare max21' e2 = Lt).
  exact (H_comp_max21_e2
                 min21' max21'
                 (trivial_equality (triple_option (A * A))
                                   (TSome (A * A) (min21', max21')))).
  rewrite -> H_max21'_max21 in H_we_need.
  exact H_we_need.

  (* with H_max21_lt_e2 finally established, we may use 
   * rotate_right_intermediate_tree_ordered to show that the tree in the 
   * goal is ordered *)
  destruct (rotate_right_intermediate_tree_ordered
              A compare (1 + max h1 h21)
              (Node A (Triple A (HNode A h1 bt1) e (HNode A h21 bt21)))
              e2
              h22 bt22
              t_min max21
              H_left_subtree_in_goal_ordered
              H_max21_lt_e2
              H_bt22_ord
              H_comp_e2_min22) as [max2 H_rotated_tree_ordered].

  (* Finally, we must show that max2 = t_max *)
  assert (H_max2_t_max: max2 = t_max).

  (* first, left reduce the rotated tree *)
  assert (H_rotate_tree_reduced:
            traverse_to_check_ordered_hbt
              A
              (HNode A (1 + max (1 + max h1 h21) h22)
                     (Node A (Triple A (HNode A 0 (Leaf A)) e2 (HNode A h22 bt22))))
              compare = TSome (A * A) (e2, max2)).
  exact (reduce_ordered_hbt_left
           A compare (1 + max (1 + max h1 h21) h22)
           (HNode A (1 + max h1 h21)
                  (Node A
                        (Triple A (HNode A h1 bt1) e (HNode A h21 bt21))))
           e2
           (HNode A h22 bt22)
           t_min max2 H_rotated_tree_ordered).
  
  (* next, left reduce the right subtree of the original tree *)
  assert (H_hbt_org_right_subtree_left_reduced:
            traverse_to_check_ordered_hbt
              A
              (HNode A (1 + max h21 h22)
                     (Node A (Triple A (HNode A 0 (Leaf A)) e2 (HNode A h22 bt22))))
              compare = TSome (A * A) (e2, t_max)).
  exact (reduce_ordered_hbt_left
           A compare (1 + max h21 h22)
           (HNode A h21 bt21) e2 (HNode A h22 bt22)
           min_rs t_max H_org_right_subtree).

  (* now traverse both reduced trees *)
  rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H_rotate_tree_reduced.
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_node in H_rotate_tree_reduced.
  rewrite -> fold_unfold_traverse_to_check_ordered_t in H_rotate_tree_reduced.
  rewrite -> (fold_unfold_traverse_to_check_ordered_hbt A 0 (Leaf A))
    in H_rotate_tree_reduced.
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_leaf in H_rotate_tree_reduced.
  
  rewrite -> fold_unfold_traverse_to_check_ordered_hbt
    in H_hbt_org_right_subtree_left_reduced.
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_node
    in H_hbt_org_right_subtree_left_reduced.
  rewrite -> fold_unfold_traverse_to_check_ordered_t
    in H_hbt_org_right_subtree_left_reduced.
  rewrite -> (fold_unfold_traverse_to_check_ordered_hbt A 0 (Leaf A))
    in H_hbt_org_right_subtree_left_reduced.
  rewrite -> fold_unfold_traverse_to_check_ordered_bt_leaf
    in H_hbt_org_right_subtree_left_reduced.

  rewrite -> H_rotate_tree_reduced in H_hbt_org_right_subtree_left_reduced.
  rewrite -> tsome_x_equal_tsome_y in H_hbt_org_right_subtree_left_reduced.
  rewrite -> pairwise_equality in H_hbt_org_right_subtree_left_reduced.
  destruct H_hbt_org_right_subtree_left_reduced as [_ H_max2_t_max].
  exact H_max2_t_max.

  (* finally, rewrite H_max2_t_max in H_rotate_tree_ordered *)
  rewrite -> H_max2_t_max in H_rotated_tree_ordered.
  exact H_rotated_tree_ordered.
Qed.

(* ***** *)

(* ***** *)

(** ** Main Lemmas for Rotations *)

(** Lemma to show that post an insertion operation on the left sub-tree of a given tree such that the resultant tree is unbalanced, and assuming:

- the modified left sub-tree [hbt_ret] is sound, ordered, and not a leaf,
- the maximum payload of [hbt_ret] sub-tree is less than the root payload,
- the right sub-tree is ordered
- if the right sub-tree were a node with a maximum and minimum value, then the root payload would be less than the minimum value, 

applying [rotate_right_hbt] on this unbalanced tree returns a tree which is ordered *)
Lemma insertion_rotate_right_preserves_order:
  forall (A : Type)
         (compare : A -> A -> element_comparison)
         (hbt_ret : heightened_binary_tree A)
         (hbt2 : heightened_binary_tree A)
         (min_ret max_ret : A)
         (e : A)
         (hbt' : heightened_binary_tree A),
    traverse_to_check_ordered_hbt A hbt_ret compare =
    TSome (A * A) (min_ret, max_ret) ->
    is_ordered_hbt A hbt2 compare = true ->
    is_sound_hbt A hbt_ret = true ->
    compare max_ret e = Lt -> 
    (forall (min2 max2 : A),
        traverse_to_check_ordered_hbt A hbt2 compare =
        TSome (A * A) (min2, max2) ->
        compare e min2 = Lt) ->
    rotate_right_hbt A hbt_ret e hbt2 = Some hbt' ->
    is_ordered_hbt A hbt' compare = true. 
Proof.
  intros.

  (* unfold *)
  unfold rotate_right_hbt in H4.
  induction hbt_ret as [h_ret bt_ret].
  induction hbt2 as [h2 bt2].
  unfold rotate_right_bt in H4.
  case bt_ret as [ | t_ret].

  discriminate.

  induction t_ret as [[h11 bt11] e1 [h12 bt12]].
  case (h11 + 1 =n= h12) as [ | ] eqn : C_S_h11_eq_h12.

  (* rotate right case 1 *)
  - case bt12 as [ | [[h121 bt121] e12 [h122 bt122]]].
    discriminate.
    rewrite -> some_x_equal_some_y in H4.
    rewrite <- H4.

    (* We note that rotate right case 1 is a double rotation: we first rotate the 
     * returned sub-tree using a left rotation, then the entire tree is 
     * right rotated *)

    (* first, we must use the soundness of hbt_ret to rewrite the correct heights *)
    destruct (triple_sound_implies_hbts_sound
                A
                h_ret
                (HNode A h11 bt11)
                e1
                (HNode A h12
                       (Node A (Triple A
                                       (HNode A h121 bt121)
                                       e12 (HNode A h122 bt122)))) H1)
      as [_ H_right_subtree_sound].

    assert (H_h12_h121_h122: h12 = 1 + max h121 h122).
    exact (relate_heights A h12 h121 bt121 e12 h122 bt122 H_right_subtree_sound).

    rewrite -> H_h12_h121_h122 in H1.
    
    assert (H_h_ret_h11_h121_h122: h_ret = 1 + max h11 (1 + max h121 h122)).
    exact (relate_heights
             A h_ret h11 bt11 e1 (1 + max h121 h122) 
             (Node A (Triple A (HNode A h121 bt121) e12 (HNode A h122 bt122)))
             H1).

    rewrite -> H_h_ret_h11_h121_h122 in H.
    assert (H_first_left_rotation:
              traverse_to_check_ordered_hbt
                A
                (HNode A (1 + max (1 + max h11 h121) h122)
                       (Node A
                             (Triple A
                                     (HNode A (1 + max h11 h121)
                                            (Node A (Triple A (HNode A h11 bt11) e1 (HNode A h121 bt121)))) e12
                                     (HNode A h122 bt122)))) compare = 
       TSome (A * A) (min_ret, max_ret)).
    exact (rotate_left_preserves_order
             A compare h11 bt11 e1 h121 bt121 e12 h122 bt122 min_ret max_ret H).
    
    (* next, we attach the left rotate tree to e and hbt2, and show that the
     * intermediate tree is ordered *)
    destruct (rotate_right_intermediate_tree_ordered
                A compare
                (1 + max (1 + max h11 h121) h122)
                (Node A
                      (Triple A
                              (HNode A (1 + max h11 h121)
                                     (Node A
                                           (Triple A
                                                   (HNode A h11 bt11)
                                                   e1
                                                   (HNode A h121 bt121))))
                              e12 (HNode A h122 bt122)))
                e
                h2 bt2
                min_ret max_ret
                H_first_left_rotation H2 H0 H3)
      as [max2 H_intermediate_tree_is_ordered].
    
    (* now rotate the intermediate tree to the right, and show that the doubly
     * rotated tree is also ordered *)
      assert (H_double_rotation_preserves_order:
                traverse_to_check_ordered_hbt
                  A
                  (HNode A (1 + max (1 + max h11 h121) (1 + max h122 h2))
                         (Node A
                               (Triple A
                                       (HNode A (1 + max h11 h121)
                                              (Node A (Triple A
                                                              (HNode A h11 bt11)
                                                              e1
                                                              (HNode A h121 bt121))))
                                       e12
                                       (HNode A (1 + max h122 h2)
                                              (Node A (Triple A
                                                              (HNode A h122 bt122)
                                                              e
                                                              (HNode A h2 bt2)))))))
                  compare = TSome (A * A) (min_ret, max2)).
      exact (rotate_right_preserves_order
               A compare 
               (1 + max h11 h121)
               (Node A
                     (Triple A 
                             (HNode A h11 bt11) e1 
                             (HNode A h121 bt121)))
               e12
               h122 bt122
               e h2 bt2
               min_ret max2
               H_intermediate_tree_is_ordered).

      (* the final step involves using 
       * traverse_to_check_ordered_hbt_some_implies_is_ordered *)
      exact (traverse_to_check_ordered_hbt_some_implies_is_ordered
               A compare
               (HNode A (1 + max (1 + max h11 h121) (1 + max h122 h2))
                      (Node A
                            (Triple A
                                    (HNode A 
                                           (1 + max h11 h121)
                                           (Node A
                                                 (Triple A 
                                                         (HNode A h11 bt11) e1 
                                                         (HNode A h121 bt121)))) e12
                                    (HNode A 
                                           (1 + max h122 h2)
                                           (Node A
                                                 (Triple A 
                                                         (HNode A h122 bt122) e 
                                                         (HNode A h2 bt2)))))))
               min_ret max2
               H_double_rotation_preserves_order).

  (* rotate right case 2 *)
  - case ((h12 + 1 =n= h11) || (h12 =n= h11)) as [ | ].
    rewrite -> some_x_equal_some_y in H4.
    rewrite <- H4.

    (* Note that rotate right case 2 requires only a single right rotation *)

    (* first, rewrite h_ret correctly *)
    assert (H_h_ret_h11_h12: h_ret = 1 + max h11 h12).
    exact (relate_heights A h_ret h11 bt11 e1 h12 bt12 H1).

    rewrite -> H_h_ret_h11_h12 in H.
    
    (* next, assert that the intermediate tree is ordered *)
    destruct (rotate_right_intermediate_tree_ordered
                A compare
                (1 + max h11 h12)
                (Node A
                      (Triple A
                              (HNode A h11 bt11)
                              e1
                              (HNode A h12 bt12)))
                  e
                h2 bt2
                min_ret max_ret
                H H2 H0 H3) as [max2 H_intermediate_tree_is_ordered].

    (* now rotate the intermediate tree right and show that order is preserved *)
    assert (H_singly_rotated_tree_ordered:
              traverse_to_check_ordered_hbt
                A
                (HNode A (1 + max h11 (1 + max h12 h2))
                       (Node A
                             (Triple A
                                     (HNode A h11 bt11)
                                     e1
                                     (HNode A (1 + max h12 h2)
                                            (Node A (Triple A (HNode A h12 bt12)
                                                            e
                                                            (HNode A h2 bt2)))))))
                compare = TSome (A * A) (min_ret, max2)).
    exact  (rotate_right_preserves_order
              A compare h11 bt11 e1 h12 bt12 e h2 bt2 min_ret max2
              H_intermediate_tree_is_ordered).

    (* the final step involves using 
     * traverse_to_check_ordered_hbt_some_implies_is_ordered *)
    exact (traverse_to_check_ordered_hbt_some_implies_is_ordered
             A compare
             (HNode A (1 + max h11 (1 + max h12 h2))
                    (Node A
                          (Triple A 
                                  (HNode A h11 bt11) e1
                                  (HNode A 
                                         (1 + max h12 h2)
                                         (Node A
                                               (Triple A 
                                                       (HNode A h12 bt12) e 
                                                       (HNode A h2 bt2)))))))
              min_ret max2 H_singly_rotated_tree_ordered).

    discriminate.
Qed.

(** Lemma to show that post an insertion operation on the right sub-tree of a given tree such that the resultant tree is unbalanced, and assuming:

- the modified right sub-tree [hbt_ret] is sound, ordered, and not a leaf,
- the root payload is less than the minimum payload of [hbt_ret]
- the left sub-tree is ordered
- if the left sub-tree were a node with a maximum and minimum value, then maximum value would be less than the root payload, 

applying [rotate_left_hbt] on this unbalanced tree returns a tree which is ordered *)
Lemma insertion_rotate_left_preserves_order:
  forall (A : Type)
         (compare : A -> A -> element_comparison)
         (hbt1 : heightened_binary_tree A)
         (hbt_ret : heightened_binary_tree A)
         (min_ret max_ret : A)
         (e : A)
         (hbt' : heightened_binary_tree A),
    is_ordered_hbt A hbt1 compare = true ->
    traverse_to_check_ordered_hbt A hbt_ret compare =
    TSome (A * A) (min_ret, max_ret) ->
    is_sound_hbt A hbt_ret = true ->
    (forall (min1 max1 : A),
        traverse_to_check_ordered_hbt A hbt1 compare =
        TSome (A * A) (min1, max1) ->
        compare max1 e = Lt) ->
    compare e min_ret = Lt -> 
    rotate_left_hbt A hbt1 e hbt_ret = Some hbt' ->
    is_ordered_hbt A hbt' compare = true.
Proof.
 intros.

 (* unfold *)
 unfold rotate_left_hbt in H4.
 induction hbt1 as [h1 bt1]. 
 induction hbt_ret as [h_ret bt_ret].
 unfold rotate_left_bt in H4.
 case bt_ret as [ | t_ret].

 discriminate.

 induction t_ret as [[h21 bt21] e2 [h22 bt22]].
 case (h22 + 1 =n= h21) as [ | ] eqn : C_S_h22_eq_h21.

 (* rotate left case 1 *)
 - case bt21 as [ | [[h211 bt211] e21 [h212 bt212]]].
   discriminate.
   rewrite -> some_x_equal_some_y in H4.
   rewrite <- H4.
   
   (* We note that rotate left case 1 is a double rotation: we first rotate the 
    * returned sub-tree using a left rotation, then the entire tree is 
    * left rotated *)
   
   (* first, we must use the soundness of hbt_ret to rewrite the correct heights *)
   destruct (triple_sound_implies_hbts_sound
               A h_ret
               (HNode A h21
                      (Node A (Triple A
                                      (HNode A h211 bt211)
                                      e21
                                      (HNode A h212 bt212))))
               e2
               (HNode A h22 bt22)
               H1) as [H_left_subtree_sound _].
   
   assert (H_21_h211_h212: h21 = 1 + max h211 h212).
   exact (relate_heights A h21 h211 bt211 e21 h212 bt212 H_left_subtree_sound).
   
   rewrite -> H_21_h211_h212 in H1.

   assert (H_h_ret_h211_h212_h22: h_ret = 1 + max (1 + max h211 h212) h22).
   exact (relate_heights
            A h_ret
            (1 + max h211 h212)
            (Node A (Triple A (HNode A h211 bt211) e21 (HNode A h212 bt212)))
            e2
            h22 bt22
            H1).

   rewrite -> H_h_ret_h211_h212_h22 in H0.

   (* we can now perform the first right rotation on the originally returned tree *)
    assert (H_first_right_rotation:
              traverse_to_check_ordered_hbt
                A
                (HNode A (1 + max h211 (1 + max h212 h22))
                       (Node A
                             (Triple A
                                     (HNode A h211 bt211)
                                     e21
                                     (HNode A (1 + max h212 h22)
                                            (Node A (Triple A
                                                            (HNode A h212 bt212)
                                                            e2
                                                            (HNode A h22 bt22)))))))
                compare = TSome (A * A) (min_ret, max_ret)).
     exact (rotate_right_preserves_order
             A compare h211 bt211 e21 h212 bt212 e2 h22 bt22 min_ret max_ret H0).
     
     (* next, we attach the right rotated tree to e and hbt1, and show that the
      * intermediate tree is ordered *)
     destruct (rotate_left_intermediate_tree_ordered
                 A compare
                 h1 bt1
                 e
                 (1 + max h211 (1 + max h212 h22))
                 (Node A
                       (Triple A (HNode A h211 bt211) e21
                               (HNode A (1 + max h212 h22)
                                      (Node A
                                            (Triple A 
                                                    (HNode A h212 bt212) e2 
                                                    (HNode A h22 bt22))))))
                 min_ret max_ret
                 H H2
                 H_first_right_rotation
                 H3) as [min1 H_intermediate_tree_is_ordered].

     (* next, left rotate the intermediate tree *)
     assert (H_double_rotation_preserves_order:
               traverse_to_check_ordered_hbt
                 A
                 (HNode A (1 + max (1 + max h1 h211) (1 + max h212 h22))
                        (Node A
                              (Triple A
                                      (HNode A (1 + max h1 h211)
                                             (Node A (Triple A
                                                             (HNode A h1 bt1)
                                                             e
                                                             (HNode A h211 bt211))))
                                      e21
                                      (HNode A (1 + max h212 h22)
                                             (Node A (Triple A
                                                             (HNode A h212 bt212)
                                                             e2
                                                             (HNode A h22 bt22)))))))
                 compare = TSome (A * A) (min1, max_ret)).
     exact (rotate_left_preserves_order
              A compare h1 bt1 e h211 bt211 e21
              (1 + max h212 h22)
              (Node A
                    (Triple A 
                            (HNode A h212 bt212) e2 
                            (HNode A h22 bt22)))
              min1 max_ret
              H_intermediate_tree_is_ordered).

      (* the final step involves using 
       * traverse_to_check_ordered_hbt_some_implies_is_ordered *)
      exact (traverse_to_check_ordered_hbt_some_implies_is_ordered
               A compare 
               (HNode A (1 + max (1 + max h1 h211) (1 + max h212 h22))
                        (Node A
                              (Triple A
                                      (HNode A (1 + max h1 h211)
                                             (Node A (Triple A
                                                             (HNode A h1 bt1)
                                                             e
                                                             (HNode A h211 bt211))))
                                      e21
                                      (HNode A (1 + max h212 h22)
                                             (Node A (Triple A
                                                             (HNode A h212 bt212)
                                                             e2
                                                             (HNode A h22 bt22)))))))
               min1 max_ret H_double_rotation_preserves_order).

 - case ((h21 + 1 =n= h22) || (h21 =n= h22)) as [ | ].
   rewrite -> some_x_equal_some_y in H4.
   rewrite <- H4.
   
   (* Note that rotate right case 2 requires only a single right rotation *)

   (* first, rewrite h_ret correctly *)
   assert (H_h_ret_h21_h22: h_ret = 1 + max h21 h22).
   exact (relate_heights A h_ret h21 bt21 e2 h22 bt22 H1).
   
   rewrite -> H_h_ret_h21_h22 in H0.
   
   (* next, assert that the intermediate tree is ordered *)
    destruct (rotate_left_intermediate_tree_ordered
                A compare h1 bt1 e
                (1 + max h21 h22)
                (Node A (Triple A (HNode A h21 bt21) e2 (HNode A h22 bt22)))
                min_ret max_ret
                H H2 H0 H3) as [min1 H_intermediate_tree_is_ordered].

    (* now rotate the intermediate tree left and show that order is preserved *)
    assert (H_singly_rotated_tree_ordered:
              traverse_to_check_ordered_hbt
                A
                (HNode A (1 + max (1 + max h1 h21) h22)
                       (Node A
                             (Triple A
                                     (HNode A (1 + max h1 h21)
                                            (Node A (Triple A
                                                            (HNode A h1 bt1)
                                                            e
                                                            (HNode A h21 bt21))))
                                     e2
                                     (HNode A h22 bt22))))
                compare = TSome (A * A) (min1, max_ret)).
    exact (rotate_left_preserves_order
             A compare h1 bt1 e h21 bt21 e2 h22 bt22 min1 max_ret
             H_intermediate_tree_is_ordered).
    
    (* the final step involves using 
     * traverse_to_check_ordered_hbt_some_implies_is_ordered *)
    exact (traverse_to_check_ordered_hbt_some_implies_is_ordered
             A compare
             (HNode A (1 + max (1 + max h1 h21) h22)
                       (Node A
                             (Triple A
                                     (HNode A (1 + max h1 h21)
                                            (Node A (Triple A
                                                            (HNode A h1 bt1)
                                                            e
                                                            (HNode A h21 bt21))))
                                     e2
                                     (HNode A h22 bt22))))
             min1 max_ret
             H_singly_rotated_tree_ordered).

    discriminate.
Qed.

(* ***** *)

(* ********** *)

(* ********** *)

(** * Insertion Preserves Order *)

(** This lemma is the most important in this library, and shows that inserting an element into an ordered AVL tree gives results in an AVL tree which is ordered. The proof makes use of:

- the crucial [insertion_in_node_min_max] lemma (defined in this library) show the relationship between a payload and the maximum/minimum values of the sub-trees
- the lemmas concerning the preservation of orderedness post rotation operations *)
Lemma insertion_preserves_order: 
  forall (A : Type)
         (compare : A -> A -> element_comparison)
         (x : A),
    specification_of_compare_defining_total_order A compare -> 
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
  intros A compare x H_compare.
  apply heightened_binary_tree_mutual_induction.

  (* Specification for hbt holds, given bt as inductive case *)
  - intros h bt H_bt_inductive_assumption hbt' H_sound_hbt_init
           H_bal_hbt_init H_ord_hbt_init H_insert_hbt.
    
    exact (H_bt_inductive_assumption h hbt' H_sound_hbt_init H_bal_hbt_init H_ord_hbt_init H_insert_hbt).

  (* Specification for bt leaf constructor holds *)
  -intros h_hbt hbt' H_sound_bt_init H_bal_bt_init H_ord_bt_init H_insert_bt.
   rewrite -> (fold_unfold_insert_bt_helper_leaf A compare x) in H_insert_bt.
   rewrite -> some_x_equal_some_y in H_insert_bt.
   rewrite <- H_insert_bt.
   unfold is_ordered_hbt.
   rewrite -> fold_unfold_traverse_to_check_ordered_hbt.
   rewrite -> fold_unfold_traverse_to_check_ordered_bt_node.
   rewrite -> fold_unfold_traverse_to_check_ordered_t.
   rewrite -> fold_unfold_traverse_to_check_ordered_hbt.
   rewrite -> fold_unfold_traverse_to_check_ordered_bt_leaf.        
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

    destruct (insertion_preserves_soundness A compare x) as [H_hbt_insertion_sound _].

    destruct (relating_insertion_and_original_height A compare x)
      as [H_hbt_relating_heights _].


    rewrite -> (fold_unfold_insert_t_helper A compare x h_hbt hbt1 e hbt2)
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

      (* essential hypothesis for possible hbt1 heights *)
      assert (H_hbt_ret_is_sound: is_sound_hbt A (HNode A h_ret bt_ret) = true).
      exact (H_hbt_insertion_sound
               hbt1 (HNode A h_ret bt_ret)  H_hbt1_is_sound C_insert_hbt1).

      assert (C_hbt1_possible_heights:
                project_height_hbt A (HNode A h_ret bt_ret) =
                project_height_hbt A hbt1 \/
                project_height_hbt A (HNode A h_ret bt_ret) =
                1 + project_height_hbt A hbt1).
      exact (H_hbt_relating_heights
               hbt1 (HNode A h_ret bt_ret) C_insert_hbt1 H_hbt1_is_sound
               H_hbt1_is_balanced H_hbt_ret_is_sound).
      
      case (compare_int h_ret (2 + project_height_hbt A hbt2))
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
          rewrite -> fold_unfold_traverse_to_check_ordered_hbt.
          rewrite -> fold_unfold_traverse_to_check_ordered_bt_node.
          rewrite -> fold_unfold_traverse_to_check_ordered_t.
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
          destruct (triple_ordered_implies_hbts_ordered
                      A compare h_hbt hbt1 e hbt2 H_ord_t_init)
            as [H_ord_hbt1 H_ord_hbt2].
          unfold is_ordered_hbt in H_ord_hbt1.
          induction hbt1 as [h1 bt1].
          rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H_ord_hbt1.
          case bt1 as [ | t1] eqn : C_bt1.

          (* the insertion took place for a leaf *)
          rewrite -> fold_unfold_traverse_to_check_ordered_bt_leaf in H_ord_hbt1.
          
          assert (H_traverse_leaf :
                    traverse_to_check_ordered_hbt A (HNode A h1 (Leaf A)) compare
                    = TNone (A * A)).
          rewrite -> fold_unfold_traverse_to_check_ordered_hbt.
          rewrite -> fold_unfold_traverse_to_check_ordered_bt_leaf.
          reflexivity.

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
          rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H_ord_t_init.
          rewrite -> fold_unfold_traverse_to_check_ordered_bt_node in H_ord_t_init.
          rewrite -> fold_unfold_traverse_to_check_ordered_t in H_ord_t_init.
          rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H_ord_t_init.
          rewrite -> fold_unfold_traverse_to_check_ordered_bt_leaf in H_ord_t_init.
          rewrite -> C_traverse_ord_hbt2 in H_ord_t_init.
          case (compare e min2) as [ | | ] eqn : C_comp_e_min2.
          reflexivity.
          discriminate.
          discriminate.
          rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H_ord_t_init.
          rewrite -> fold_unfold_traverse_to_check_ordered_bt_node in H_ord_t_init.
          rewrite -> fold_unfold_traverse_to_check_ordered_t in H_ord_t_init.

          (* the insertion took place in a node *)
          case (traverse_to_check_ordered_bt A (Node A t1) compare)
            as [ | | (min1, max1)] eqn : C_traverse_ord_hbt1.
          discriminate.
          induction t1 as [hbt11 e1 hbt12].
          destruct (ordered_node_has_min_max
                      A compare h1 hbt11 e1 hbt12 H_hbt1_is_ordered)
            as [some_min [some_max H_contradictory]].
          rewrite -> H_contradictory in C_traverse_ord_hbt1.
          discriminate.
          
          assert (H_traverse_ord_hbt1 :
                    traverse_to_check_ordered_hbt A (HNode A h1 (Node A t1)) compare =
                    TSome (A * A) (min1, max1)).
          rewrite -> fold_unfold_traverse_to_check_ordered_hbt.
          exact C_traverse_ord_hbt1.

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
      * assert (H_hbt_ret_ordered:
                  is_ordered_hbt A (HNode A h_ret bt_ret) compare = true).
        exact (H_hbt1_inductive_assumption
                    (HNode A h_ret bt_ret)
                    H_hbt1_is_sound H_hbt1_is_balanced H_hbt1_is_ordered P_some_eq).
        
        (* obtain relation between max (hbt_ret) and e *)
        induction hbt1 as [h1 bt1].                
        induction hbt2 as [h2 bt2].
        case bt_ret as [ | t_ret].

        (* impossible case: bt_ret is leaf *)
        unfold rotate_right_hbt in H_insert_t.
        unfold rotate_right_bt in H_insert_t.
        discriminate.

        (* bt_ret is a triple: use lemma traverse_node_impossible_case *)
        assert (H_bt_ret_impossible_case:
                  traverse_to_check_ordered_bt A (Node A t_ret) compare =
                  TNone (A * A) -> False).
        exact (traverse_node_impossible_case A compare t_ret).

        (* now unfold is_ordered_hbt for hbt_ret *)
        unfold is_ordered_hbt in H_hbt_ret_ordered.
        case (traverse_to_check_ordered_hbt A (HNode A h_ret (Node A t_ret)) compare)
             as [ | | (min_ret, max_ret)] eqn : C_check_ord_hbt_ret.
        discriminate.
        apply H_bt_ret_impossible_case in C_check_ord_hbt_ret.
        apply False_ind.
        exact C_check_ord_hbt_ret.

        (* now show that hbt1 must be a node using information about heights *)

        (* first, unfold and set the hypotheses up as required *)
        unfold project_height_hbt in C_hbt1_possible_heights.
        unfold project_height_hbt in C_height_diff.
        unfold compare_int in C_height_diff.
        case (h_ret <? 2 + h2) as [ | ].
        discriminate.
        case (h_ret =n= 2 + h2) as [ | ] eqn : C_h_ret_eq_SS_h2.

        (* next, assert that hbt1 is a node *)
        destruct (non_zero_height_implies_node
                    A h_ret h1 h2 bt1 C_hbt1_possible_heights
                    C_h_ret_eq_SS_h2 H_hbt1_is_sound) as [t1 H_bt1_as_node].
        rewrite -> H_bt1_as_node in H_hbt1_is_ordered.
        unfold is_ordered_hbt in H_hbt1_is_ordered.
        case (traverse_to_check_ordered_hbt A (HNode A h1 (Node A t1)) compare)
             as [ | | (min1, max1)] eqn : C_check_ord_hbt1.
        discriminate.

        (* assert that traversing hbt1 to check ordered can never give a TNone 
         * constructor *)
        assert (H_bt1_impossible_case:
                  traverse_to_check_ordered_bt A (Node A t1) compare =
                  TNone (A * A) -> False).
        exact (traverse_node_impossible_case A compare t1).

        apply H_bt1_impossible_case in C_check_ord_hbt1.
        apply False_ind.
        exact C_check_ord_hbt1.

        (* finally, we may use insertion_in_node_min_max *)
        destruct (insertion_in_node_min_max A compare) as [H_hbt_min_max _].
        rewrite -> H_bt1_as_node in H_hbt1_is_sound.
        rewrite -> H_bt1_as_node in H_hbt1_is_balanced.
        rewrite -> H_bt1_as_node in C_insert_hbt1.
        destruct (H_hbt_min_max (HNode A h1 (Node A t1))
                                (HNode A h_ret (Node A t_ret))
                                x min1 min_ret max1 max_ret
                                H_hbt1_is_sound H_hbt1_is_balanced
                                C_insert_hbt1
                                C_check_ord_hbt_ret
                                C_check_ord_hbt1) as [H_hbt_ret_max _].

        (* assert relation between max_ret and e *)
        assert (H_max_ret_lt_e: compare max_ret e = Lt).
        destruct H_hbt_ret_max as [H_max_ret_eq_x | H_max_ret_eq_max1].
        rewrite -> H_max_ret_eq_x.
        exact C_comp.

        rewrite -> H_max_ret_eq_max1.
        
        (* unfold is_ordered_hbt in H_ord_t_init *)
        unfold is_ordered_hbt in H_ord_t_init.
        rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H_ord_t_init.
        rewrite -> fold_unfold_traverse_to_check_ordered_bt_node in H_ord_t_init.
        rewrite -> fold_unfold_traverse_to_check_ordered_t in H_ord_t_init.
        rewrite -> H_bt1_as_node in H_ord_t_init.
        rewrite -> C_check_ord_hbt1 in H_ord_t_init.
        case (compare max1 e) as [ | | ].
        reflexivity.
        discriminate.
        discriminate.

        (* obtain hypothesis relating hbt2 and e *)
        assert (H_e_hbt2:
                  forall (min2 max2 : A),
                    traverse_to_check_ordered_hbt A (HNode A h2 bt2) compare =
                    TSome (A * A) (min2, max2) ->
                    compare e min2 = Lt).
        intros.
        rewrite -> H_bt1_as_node in H_ord_t_init.
        unfold is_ordered_hbt in H_ord_t_init.
        rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H_ord_t_init.
        rewrite -> fold_unfold_traverse_to_check_ordered_bt_node in H_ord_t_init.
        rewrite -> fold_unfold_traverse_to_check_ordered_t in H_ord_t_init.
        rewrite -> C_check_ord_hbt1 in H_ord_t_init.
        case (compare max1 e) as [ | | ].
        rewrite -> H in H_ord_t_init.
        case (compare e min2) as [ | | ].
        reflexivity.
        discriminate.
        discriminate.
        discriminate.
        discriminate.

        (* we are finally in a position to apply the insertion rotation lemmas *)
        exact (insertion_rotate_right_preserves_order
                 A compare (HNode A h_ret (Node A t_ret)) (HNode A h2 bt2)
                 min_ret max_ret e hbt'
                 C_check_ord_hbt_ret H_hbt2_is_ordered
                 H_hbt_ret_is_sound H_max_ret_lt_e H_e_hbt2 H_insert_t).

        discriminate.

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

      (* essential hypothesis for possible hbt1 heights *)
      assert (H_hbt_ret_is_sound: is_sound_hbt A (HNode A h_ret bt_ret) = true).
      exact (H_hbt_insertion_sound
               hbt2 (HNode A h_ret bt_ret) H_hbt2_is_sound C_insert_hbt2).

      assert (C_hbt2_possible_heights:
                project_height_hbt A (HNode A h_ret bt_ret) =
                project_height_hbt A hbt2 \/
                project_height_hbt A (HNode A h_ret bt_ret) =
                1 + project_height_hbt A hbt2).
      exact (H_hbt_relating_heights
               hbt2 (HNode A h_ret bt_ret) C_insert_hbt2 H_hbt2_is_sound
               H_hbt2_is_balanced H_hbt_ret_is_sound).
      
      case (compare_int h_ret (2 + project_height_hbt A hbt1))
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
          rewrite -> fold_unfold_traverse_to_check_ordered_hbt.
          rewrite -> fold_unfold_traverse_to_check_ordered_bt_node.
          rewrite -> fold_unfold_traverse_to_check_ordered_t.
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
          rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H_hbt2_is_ordered.
          case bt2 as [ | t2] eqn : C_bt2.

          (* the insertion took place for a leaf *)
          rewrite -> fold_unfold_traverse_to_check_ordered_bt_leaf in H_hbt2_is_ordered.
          
          assert (H_traverse_leaf :
                    traverse_to_check_ordered_hbt A (HNode A h2 (Leaf A)) compare
                    = TNone (A * A)).
          rewrite -> fold_unfold_traverse_to_check_ordered_hbt.
          rewrite -> fold_unfold_traverse_to_check_ordered_bt_leaf.
          reflexivity.

          destruct (insertion_in_leaf_min_max
                      A compare (HNode A h2 (Leaf A)) (HNode A h_ret bt_ret) x min_ret max_ret
                      C_insert_hbt2 C_traverse_ord_hbt_ret H_traverse_leaf)
            as [H_min_ret H_max_ret].
          rewrite -> H_min_ret.
          destruct (relating_Lt_Gt_total_order A compare e x H_compare)
            as [_ H_we_need].
          apply H_we_need in C_comp.
          rewrite -> C_comp.
          reflexivity. 

          (* the insertion took place in a node *)
          case (traverse_to_check_ordered_bt A (Node A t2) compare)
            as [ | | (min2, max2)] eqn : C_traverse_ord_hbt2.
          (* impossible case: hbt2 was unordered *)
          discriminate.

          (* impossible case: hbt2 was a leaf *)
          induction t2 as [hbt21 e2 hbt22].
          
          destruct (ordered_node_has_min_max
                      A compare h2 hbt21 e2 hbt22 H_hbt2_is_ordered_duplication)
            as [some_min [some_max H_contradictory]].
          rewrite -> H_contradictory in C_traverse_ord_hbt2.
          discriminate.

          (* traverse_to_check_ordered_bt hbt2 has a max and min *)
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
          destruct (relating_Lt_Gt_total_order A compare e x H_compare)
            as [_ H_we_need].
          apply H_we_need in C_comp.
          rewrite -> C_comp.
          reflexivity.

          (* prove case for H_min_ret_min2 *)
          rewrite -> H_min_ret_min2.
          rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H_ord_t_init.
          rewrite -> fold_unfold_traverse_to_check_ordered_bt_node in H_ord_t_init.
          rewrite -> fold_unfold_traverse_to_check_ordered_t in H_ord_t_init.
          rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H_ord_t_init.
          rewrite -> fold_unfold_traverse_to_check_ordered_bt_node in H_ord_t_init.
          rewrite -> C_traverse_ord_hbt1 in H_ord_t_init.
          rewrite -> fold_unfold_traverse_to_check_ordered_bt_node in C_traverse_ord_hbt2.
          rewrite -> C_traverse_ord_hbt2 in H_ord_t_init.
          case (compare e min2) as [ | | ] eqn : C_comp_e_min2.
          reflexivity.
          discriminate.
          discriminate.

          (* hbt1 is a node *)
          rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H_ord_t_init.
          rewrite -> fold_unfold_traverse_to_check_ordered_bt_node in H_ord_t_init.
          rewrite -> fold_unfold_traverse_to_check_ordered_t in H_ord_t_init.
          rewrite -> C_traverse_ord_hbt1 in H_ord_t_init.
          case (compare max1 e) as [ | | ] eqn : C_comp_max1_e.
          case (traverse_to_check_ordered_hbt A (HNode A h_ret bt_ret) compare)
            as [ | | (min_ret, max_ret)] eqn : C_traverse_ord_hbt_ret.
          discriminate.
          reflexivity.
          unfold is_ordered_hbt in H_hbt2_is_ordered.
          induction hbt2 as [h2 bt2].
          rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H_hbt2_is_ordered.
          case bt2 as [ | t2] eqn : C_bt2.
          
          (* the insertion took place in a leaf *)
          rewrite -> fold_unfold_traverse_to_check_ordered_bt_leaf in H_hbt2_is_ordered.
          
          assert (H_traverse_leaf :
                    traverse_to_check_ordered_hbt A (HNode A h2 (Leaf A)) compare
                    = TNone (A * A)).
          rewrite -> fold_unfold_traverse_to_check_ordered_hbt.
          rewrite -> fold_unfold_traverse_to_check_ordered_bt_leaf.
          reflexivity.

          destruct (insertion_in_leaf_min_max
                      A compare (HNode A h2 (Leaf A)) (HNode A h_ret bt_ret) x min_ret max_ret
                      C_insert_hbt2 C_traverse_ord_hbt_ret H_traverse_leaf)
            as [H_min_ret H_max_ret].
          rewrite -> H_min_ret.
          destruct (relating_Lt_Gt_total_order A compare e x H_compare)
            as [_ H_we_need].
          apply H_we_need in C_comp.
          rewrite -> C_comp.
          reflexivity. 

          (* the insertion took place in a node *)
          case (traverse_to_check_ordered_bt A (Node A t2) compare)
            as [ | | (min2, max2)] eqn : C_traverse_ord_hbt2.
          (* impossible case: hbt2 was unordered *)
          discriminate.

          (* impossible case: hbt2 was a leaf *)
          induction t2 as [hbt21 e2 hbt22].
          
          destruct (ordered_node_has_min_max
                      A compare h2 hbt21 e2 hbt22 H_hbt2_is_ordered_duplication)
            as [some_min [some_max H_contradictory]].
          rewrite -> H_contradictory in C_traverse_ord_hbt2.
          discriminate.

          (* traverse_to_check_ordered_bt hbt2 has a max and min *)
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
          destruct (relating_Lt_Gt_total_order A compare e x H_compare)
            as [_ H_we_need].
          apply H_we_need in C_comp.
          rewrite -> C_comp.
          reflexivity.

          (* prove case for H_min_ret_min2 *)
          rewrite -> H_min_ret_min2.
          rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H_ord_t_init.
          rewrite -> C_traverse_ord_hbt2 in H_ord_t_init.
          case (compare e min2) as [ | | ] eqn : C_comp_e_min2. 
          reflexivity.
          discriminate.
          discriminate.
          discriminate.
          discriminate.
        }
        
        (* the insertion unbalances the tree: rotations required *) 
      * assert (H_hbt_ret_ordered:
                  is_ordered_hbt A (HNode A h_ret bt_ret) compare = true).
        exact (H_hbt2_inductive_assumption
                 (HNode A h_ret bt_ret)
                 H_hbt2_is_sound H_hbt2_is_balanced H_hbt2_is_ordered P_some_eq).

        (* obtain relation between e and min (hbt_ret); to do so we want to 
         * use insertion_in_node_min_max;
         * the key here is to assert that both hbt_ret and hbt are nodes, and then
         * unfold is_ordered_hbt to get the min and max values in both cases *)
        induction hbt1 as [h1 bt1].                
        induction hbt2 as [h2 bt2].
        case bt_ret as [ | t_ret].
        
        (* impossible case: bt_ret is leaf *)
        unfold rotate_left_hbt in H_insert_t.
        unfold rotate_left_bt in H_insert_t.
        discriminate.

        (* bt_ret is a triple: use lemma traverse_node_impossible_case *)
        assert (H_bt_ret_impossible_case:
                  traverse_to_check_ordered_bt A (Node A t_ret) compare =
                  TNone (A * A) -> False).
        exact (traverse_node_impossible_case A compare t_ret).
        

        (* now unfold is_ordered_hbt for hbt_ret *)
        unfold is_ordered_hbt in H_hbt_ret_ordered.
        case (traverse_to_check_ordered_hbt A (HNode A h_ret (Node A t_ret)) compare)
             as [ | | (min_ret, max_ret)] eqn : C_check_ord_hbt_ret.
        discriminate.
        apply H_bt_ret_impossible_case in C_check_ord_hbt_ret.
        apply False_ind.
        exact C_check_ord_hbt_ret.

        (* we have shown that hbt_ret has a min and a max; now we want to do so for
         * hbt2 *)

        (* first, unfold and set the hypotheses up as required *)
        unfold project_height_hbt in C_hbt2_possible_heights.
        unfold project_height_hbt in C_height_diff.
        unfold compare_int in C_height_diff.
        case (h_ret <? 2 + h1) as [ | ].
        discriminate.
        case (h_ret =n= 2 + h1) as [ | ] eqn : C_h_ret_eq_SS_h1.

        (* next, assert that hbt1 is a node *)
        destruct (non_zero_height_implies_node
                    A h_ret h2 h1 bt2 C_hbt2_possible_heights
                    C_h_ret_eq_SS_h1 H_hbt2_is_sound) as [t2 H_bt2_as_node].
        rewrite -> H_bt2_as_node in H_hbt2_is_ordered.
        unfold is_ordered_hbt in H_hbt2_is_ordered.
        case (traverse_to_check_ordered_hbt A (HNode A h2 (Node A t2)) compare)
             as [ | | (min2, max2)] eqn : C_check_ord_hbt2.
        discriminate.

        (* assert that traversing hbt2 to check ordered can never give a TNone 
         * constructor *)
        assert (H_bt2_impossible_case:
                  traverse_to_check_ordered_bt A (Node A t2) compare =
                  TNone (A * A) -> False).
        exact (traverse_node_impossible_case A compare t2).

        apply H_bt2_impossible_case in C_check_ord_hbt2.
        apply False_ind.
        exact C_check_ord_hbt2.

        (* finally, we may use insertion_in_node_min_max *)
        destruct (insertion_in_node_min_max A compare) as [H_hbt_min_max _].
        rewrite -> H_bt2_as_node in H_hbt2_is_sound.
        rewrite -> H_bt2_as_node in H_hbt2_is_balanced.
        rewrite -> H_bt2_as_node in C_insert_hbt2.
        destruct (H_hbt_min_max (HNode A h2 (Node A t2))
                                (HNode A h_ret (Node A t_ret))
                                x min2 min_ret max2 max_ret
                                H_hbt2_is_sound H_hbt2_is_balanced
                                C_insert_hbt2
                                C_check_ord_hbt_ret
                                C_check_ord_hbt2) as [_ H_hbt_ret_min].
        
        (* assert relation between e and min_ret *)
        assert (H_e_lt_min_ret: compare e min_ret = Lt).
        destruct H_hbt_ret_min as [H_min_ret_eq_x | H_min_ret_eq_min2].

        (* case 1 : min_ret = x *)
        rewrite -> H_min_ret_eq_x.
        destruct (relating_Lt_Gt_total_order A compare e x H_compare)
          as [_ H_we_need].
        apply H_we_need in C_comp.
        exact C_comp.
        
        (* case 2 : min_ret min2 *)
        rewrite -> H_min_ret_eq_min2.

        (* to solve this problem, we right reduce H_ord_t_init *)
        rewrite -> H_bt2_as_node in H_ord_t_init.
        destruct (ordered_node_has_min_max
                    A compare h_hbt (HNode A h1 bt1) e (HNode A h2 (Node A t2))
                    H_ord_t_init) as [min1 [max2_alias H_hbt_init_traverse_bt]].

        (* fold traverse_to_check_ordered_bt *)
        assert (H_hbt_init_traverse_hbt:
                  traverse_to_check_ordered_hbt
                    A
                    (HNode A h_hbt (Node A (Triple A
                                                   (HNode A h1 bt1)
                                                   e
                                                   (HNode A h2 (Node A t2)))))
                    compare = TSome (A * A) (min1, max2_alias)).
        rewrite -> fold_unfold_traverse_to_check_ordered_hbt.
        exact H_hbt_init_traverse_bt.
        
        (* now left reduce H_hbt_init_traverse *)
        assert (H_hbt_init_left_reduced:
                  traverse_to_check_ordered_hbt
                    A
                    (HNode A h_hbt (Node A (Triple A
                                                   (HNode A 0 (Leaf A))
                                                   e (HNode A h2 (Node A t2)))))
                    compare = TSome (A * A) (e, max2_alias)).
        exact (reduce_ordered_hbt_left
                 A compare h_hbt
                 (HNode A h1 bt1) e (HNode A h2 (Node A t2))
                 min1 max2_alias H_hbt_init_traverse_hbt).
        
        (* now unfold in H_hbt_init_traverse_hbt *)
        rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H_hbt_init_left_reduced.
        rewrite -> fold_unfold_traverse_to_check_ordered_bt_node
          in H_hbt_init_left_reduced.
        rewrite -> fold_unfold_traverse_to_check_ordered_t in H_hbt_init_left_reduced.
        rewrite -> (fold_unfold_traverse_to_check_ordered_hbt A 0 (Leaf A))
          in H_hbt_init_left_reduced.
        rewrite -> fold_unfold_traverse_to_check_ordered_bt_leaf
          in H_hbt_init_left_reduced.
        rewrite -> C_check_ord_hbt2 in H_hbt_init_left_reduced.
        case (compare e min2) as [ | | ].
        reflexivity.
        discriminate.
        discriminate.

        (* obtain hypothesis relating hbt1 and e *)
        assert (H_hbt1_e:
                  forall (min1 max1 : A),
                    traverse_to_check_ordered_hbt A (HNode A h1 bt1) compare =
                    TSome (A * A) (min1, max1) ->
                    compare max1 e = Lt).
        intros.
        unfold is_ordered_hbt in H_ord_t_init.
        rewrite -> fold_unfold_traverse_to_check_ordered_hbt in H_ord_t_init.
        rewrite -> fold_unfold_traverse_to_check_ordered_bt_node in H_ord_t_init.
        rewrite -> fold_unfold_traverse_to_check_ordered_t in H_ord_t_init.
        rewrite -> H in H_ord_t_init.
        case (compare max1 e) as [ | | ].
        reflexivity.
        discriminate.
        discriminate.

        (* we are finally in a position to apply 
         * insertion_rotate_right_preserves_order ! *)
        exact (insertion_rotate_left_preserves_order
                 A compare (HNode A h1 bt1) (HNode A h_ret (Node A t_ret))
                 min_ret max_ret e hbt'
                 H_hbt1_is_ordered
                 C_check_ord_hbt_ret
                 H_hbt_ret_is_sound
                 H_hbt1_e
                 H_e_lt_min_ret
                 H_insert_t).

        discriminate.
        
      * discriminate.

      * discriminate.
Qed.

(* ********** *)

(* ********** End of ordered_main.v ********** *)

