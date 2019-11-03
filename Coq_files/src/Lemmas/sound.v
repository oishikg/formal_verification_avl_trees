Require Import Hbt.Implementation.hbt.
Require Export Hbt.Implementation.hbt.

(* ********** Lemmas concerning soundness ********** *)

Lemma equal_nats_implies_true_prop:
  forall (h1 h2 : nat),
    (1 + max h1 h2 =n= 1 + max h1 h2) = true.
Proof.
  intros.
  
  assert (H_trivial:
            1 + max h1 h2 = 1 + max h1 h2).
  reflexivity.
  
  Check (prop_to_bool_helper (1 + max h1 h2) H_trivial).
  exact (prop_to_bool_helper (1 + max h1 h2) H_trivial).
Qed.

Lemma relate_heights:
  forall (A : Type)
         (h_res : nat)
         (h1 : nat)
         (bt1 : binary_tree A)
         (e : A)
         (h2 : nat)
         (bt2 : binary_tree A),
    is_sound_hbt
      A
      (HNode A h_res (Node A (Triple A (HNode A h1 bt1) e (HNode A h2 bt2)))) = true ->
    h_res = 1 + max h1 h2.
Proof.
  intros.
  unfold is_sound_hbt in H.
  rewrite -> unfold_traverse_to_check_soundness_hbt in H.
  rewrite -> unfold_traverse_to_check_soundness_bt_node in H.
  rewrite -> unfold_traverse_to_check_soundness_t in H.
  case (traverse_to_check_soundness_hbt A (HNode A h1 bt1))
       as [h1' | ] eqn : C_h1.
  case (traverse_to_check_soundness_hbt A (HNode A h2 bt2))
       as [h2' | ] eqn : C_h2.
  case (1 + max h1' h2' =n= h_res) as [ | ] eqn : C_sum.
  apply beq_nat_true in C_sum.
  
  assert (H_h1'_h1: h1 = h1').
  rewrite -> unfold_traverse_to_check_soundness_hbt in C_h1.
  case (traverse_to_check_soundness_bt A bt1) as [h' | ] eqn : C.
  case (h' =n= h1) as [ | ] eqn :C'.
  rewrite -> some_x_equal_some_y in C_h1.
  exact C_h1.
  discriminate.
  discriminate.

  assert (H_h2'_h2: h2 = h2').
  rewrite -> unfold_traverse_to_check_soundness_hbt in C_h2.
  case (traverse_to_check_soundness_bt A bt2) as [h' | ] eqn : C.
  case (h' =n= h2) as [ | ] eqn :C'.
  rewrite -> some_x_equal_some_y in C_h2.
  exact C_h2.
  discriminate.
  discriminate.  

  rewrite <- H_h1'_h1 in C_sum. 
  rewrite <- H_h2'_h2 in C_sum.
  symmetry.
  exact C_sum.
  discriminate.
  discriminate.
  discriminate.
Qed.


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
  case (h_ret =n= h) as [ | ] eqn : C_equal_nats_implies_true_prop.
  Check (beq_nat_true).
  apply (beq_nat_true h_ret h) in C_equal_nats_implies_true_prop.
  rewrite <- C_equal_nats_implies_true_prop in H.
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
  induction hbt1 as [h1 bt1].
  induction hbt2 as [h2 bt2].
  
  unfold is_sound_hbt.
  rewrite -> unfold_traverse_to_check_soundness_hbt.
  rewrite -> unfold_traverse_to_check_soundness_bt_node.
  rewrite -> unfold_traverse_to_check_soundness_t.
  unfold is_sound_hbt in H_hbt1.
  unfold is_sound_hbt in H_hbt2.
  case (traverse_to_check_soundness_hbt A (HNode A h1 bt1))
    as [h1_ret | ] eqn : C_check_hbt1.
  case (traverse_to_check_soundness_hbt A (HNode A h2 bt2))
    as [h2_ret | ] eqn : C_check_hbt2.
  
  unfold project_height_hbt in H_h_hbt.

  assert (H_h1_h1_ret:
            h1 = h1_ret).
  rewrite -> unfold_traverse_to_check_soundness_hbt in C_check_hbt1.
  case (traverse_to_check_soundness_bt A bt1) as [h' | ].
  case (h' =n= h1) as [ | ] eqn : C_h'_h1.
  rewrite -> some_x_equal_some_y in C_check_hbt1.
  exact C_check_hbt1.
  discriminate.
  discriminate.

  assert (H_h2_h2_ret:
            h2 = h2_ret).
  rewrite -> unfold_traverse_to_check_soundness_hbt in C_check_hbt2.
  case (traverse_to_check_soundness_bt A bt2) as [h' | ].
  case (h' =n= h2) as [ | ] eqn : C_h'_h2.
  rewrite -> some_x_equal_some_y in C_check_hbt2.
  exact C_check_hbt2.
  discriminate.
  discriminate.
  
  rewrite <- H_h1_h1_ret.
  rewrite <- H_h2_h2_ret.
  rewrite <- H_h_hbt.

  assert (H_trivial: h_hbt = h_hbt).
  reflexivity.
  
  Check (prop_to_bool).
  rewrite -> (prop_to_bool_helper h_hbt H_trivial).
  reflexivity.

  discriminate.

  discriminate.
Qed.

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
  case bt12 as [ | [[h121 bt121] e12 [h122 bt122]]].

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
    Check (equal_nats_implies_true_prop).
    rewrite -> equal_nats_implies_true_prop.
    rewrite -> equal_nats_implies_true_prop.
    rewrite -> equal_nats_implies_true_prop.    
    reflexivity.

  - case ((h12 + 1 =n= h11) || (h12 =n= h11)) as [ | ] eqn : C_h12_h11.
    rewrite -> some_x_equal_some_y in H1. 
    rewrite <- H1.

    (* show that all the subtrees are sound *)
    Check (triple_sound_implies_hbts_sound).
    destruct (triple_sound_implies_hbts_sound
                A h_ret (HNode A h11 bt11) e1 (HNode A h12 bt12) H)
             as [H_bt11_sound H_bt12_sound].

    (* now obtain the heights for the subtrees by unfolding *)
    Check (soundness_implies_some_height).
    assert (H_bt11_h11:
              traverse_to_check_soundness_hbt A (HNode A h11 bt11) = Some h11).
    exact (soundness_implies_some_height A h11 bt11 H_bt11_sound).

    assert (H_bt12_h12:
              traverse_to_check_soundness_hbt A (HNode A h12 bt12) = Some h12).
    exact (soundness_implies_some_height A h12 bt12 H_bt12_sound).

    assert (H_bt2_h2:
              traverse_to_check_soundness_hbt A (HNode A h2 bt2) = Some h2).
    exact (soundness_implies_some_height A h2 bt2 H0).

    unfold is_sound_hbt.
    rewrite -> unfold_traverse_to_check_soundness_hbt.
    rewrite -> unfold_traverse_to_check_soundness_bt_node.
    rewrite -> unfold_traverse_to_check_soundness_t.
    rewrite -> H_bt11_h11.
    rewrite -> unfold_traverse_to_check_soundness_hbt.
    rewrite -> unfold_traverse_to_check_soundness_bt_node.
    rewrite -> unfold_traverse_to_check_soundness_t.
    rewrite -> H_bt12_h12.
    rewrite -> H_bt2_h2.
    rewrite -> equal_nats_implies_true_prop.
    rewrite -> equal_nats_implies_true_prop.
    reflexivity.

    discriminate.
Qed.



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
    intros.

  (* destruct and unfold *)
  unfold rotate_left_hbt in H1.
  induction hbt1 as [h1 bt1].
  unfold rotate_left_bt in H1.
  induction bt_ret as [ | t_ret].
  discriminate.
  induction t_ret as [[h21 bt21] e2 [h22 bt22]].
  case (h22 + 1 =n= h21) as [ | ].

  (* h22 + 1 =n= h21 *)
  case bt21 as [ | [[h211 bt211] e21 [h212 bt212]]].

  (* bt12 is leaf : impossible case *)
  - discriminate.

  (* bt12 is node *)
  - rewrite -> some_x_equal_some_y in H1.
    rewrite <- H1.

    (* show that all the subtrees are sound *)
    Check (triple_sound_implies_hbts_sound).
    destruct (triple_sound_implies_hbts_sound
                A h_ret
                (HNode A h21
                       (Node A (Triple A
                                       (HNode A h211 bt211)
                                       e21
                                       (HNode A h212 bt212))))
                e2
                (HNode A h22 bt22) H0) as [H_left_subtree_sound H_bt22_sound].
    destruct (triple_sound_implies_hbts_sound
                A h21
                (HNode A h211 bt211) e21 (HNode A h212 bt212)
                H_left_subtree_sound) as [H_bt211_sound H_bt212_sound].
    
    (* now obtain the heights for the subtrees by unfolding *)
    Check (soundness_implies_some_height).
    assert (H_bt22_h22:
              traverse_to_check_soundness_hbt A (HNode A h22 bt22) = Some h22).
    exact (soundness_implies_some_height A h22 bt22 H_bt22_sound).

    assert (H_bt211_h211:
              traverse_to_check_soundness_hbt A (HNode A h211 bt211) = Some h211).
    exact (soundness_implies_some_height A h211 bt211 H_bt211_sound).

    assert (H_bt212_h212:
              traverse_to_check_soundness_hbt A (HNode A h212 bt212) = Some h212).
    exact (soundness_implies_some_height A h212 bt212 H_bt212_sound).

    assert (H_bt1_h1:
              traverse_to_check_soundness_hbt A (HNode A h1 bt1) = Some h1).
    exact (soundness_implies_some_height A h1 bt1 H).

    (* unfold goal *)
    unfold is_sound_hbt.
    rewrite -> unfold_traverse_to_check_soundness_hbt.
    rewrite -> unfold_traverse_to_check_soundness_bt_node.
    rewrite -> unfold_traverse_to_check_soundness_t.
    rewrite -> unfold_traverse_to_check_soundness_hbt.
    rewrite -> unfold_traverse_to_check_soundness_bt_node.
    rewrite -> unfold_traverse_to_check_soundness_t.
    rewrite -> H_bt1_h1.
    rewrite -> H_bt211_h211.
    rewrite -> equal_nats_implies_true_prop.
    rewrite -> unfold_traverse_to_check_soundness_hbt.
    rewrite -> unfold_traverse_to_check_soundness_bt_node.
    rewrite -> unfold_traverse_to_check_soundness_t.
    rewrite -> H_bt212_h212.
    rewrite -> H_bt22_h22.
    rewrite -> equal_nats_implies_true_prop.
    rewrite -> equal_nats_implies_true_prop.
    reflexivity.

  - case ((h21 + 1 =n= h22) || (h21 =n= h22)) as [ | ] eqn : C_h21_h22.
    rewrite -> some_x_equal_some_y in H1. 
    rewrite <- H1.

    (* show that all the subtrees are sound *)
    Check (triple_sound_implies_hbts_sound).
    destruct (triple_sound_implies_hbts_sound
                A h_ret
                (HNode A h21 bt21) e2 (HNode A h22 bt22) H0)
      as [H_bt21_sound H_bt22_sound].
    
    assert (H_bt22_h22:
              traverse_to_check_soundness_hbt A (HNode A h22 bt22) = Some h22).
    exact (soundness_implies_some_height A h22 bt22 H_bt22_sound).
    
    assert (H_bt1_h1:
              traverse_to_check_soundness_hbt A (HNode A h1 bt1) = Some h1).
    exact (soundness_implies_some_height A h1 bt1 H).

    Check (soundness_implies_some_height).
    assert (H_bt21_h21:
              traverse_to_check_soundness_hbt A (HNode A h21 bt21) = Some h21).
    exact (soundness_implies_some_height A h21 bt21 H_bt21_sound).

    unfold is_sound_hbt.
    rewrite -> unfold_traverse_to_check_soundness_hbt.
    rewrite -> unfold_traverse_to_check_soundness_bt_node.
    rewrite -> unfold_traverse_to_check_soundness_t.
    rewrite -> unfold_traverse_to_check_soundness_hbt.
    rewrite -> unfold_traverse_to_check_soundness_bt_node.
    rewrite -> unfold_traverse_to_check_soundness_t.
    rewrite -> H_bt1_h1.
    rewrite -> H_bt21_h21.
    rewrite -> equal_nats_implies_true_prop.
    rewrite -> H_bt22_h22.
    rewrite -> equal_nats_implies_true_prop.
    reflexivity.
    
    discriminate.
Qed.

Lemma insertion_preserves_soundness:
  forall (A : Type)
         (compare : A -> A -> element_comparison)
         (x : A),
    (forall (hbt : heightened_binary_tree A)
            (hbt' : heightened_binary_tree A),
        is_sound_hbt A hbt = true ->
        insert_hbt_helper A compare x hbt = Some hbt' ->
        is_sound_hbt A hbt' = true)
    /\
    (forall (bt : binary_tree A)
            (h_hbt : nat)
            (hbt' : heightened_binary_tree A),    
        is_sound_hbt A (HNode A h_hbt bt) = true ->
        insert_bt_helper A compare x h_hbt bt = Some hbt' ->
        is_sound_hbt A hbt' = true)
    /\
    (forall (t : triple A)
            (h_hbt : nat)
            (hbt' : heightened_binary_tree A),    
        is_sound_hbt A (HNode A h_hbt (Node A t)) = true ->
        insert_t_helper A compare x h_hbt t = Some hbt' ->
        is_sound_hbt A hbt' = true).
Proof.
  intros.
  apply heightened_binary_tree_mutual_induction.

  (* Specification for hbt holds, given bt as inductive case *)  
  - intros h bt H_bt_inductive_assumption hbt' H_sound_hbt_init H_insert_hbt.
    Check (H_bt_inductive_assumption h hbt' H_sound_hbt_init H_insert_hbt).
    exact (H_bt_inductive_assumption h hbt' H_sound_hbt_init H_insert_hbt).

    (* Specification for bt leaf constructor holds *)
  - intros h_hbt hbt' H_sound_bt_init H_insert_bt.
    rewrite -> (unfold_insert_bt_helper_leaf A compare x)
      in H_insert_bt.
    rewrite -> some_x_equal_some_y in H_insert_bt.
    rewrite <- H_insert_bt.

    unfold is_sound_hbt.
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

  (* Specification for bt with node constructor holds, given t as inductive case *)
  - intros t H_t_inductive_assumption h_hbt hbt' H_sound_bt_init H_insert_bt.
    exact (H_t_inductive_assumption h_hbt hbt' H_sound_bt_init  H_insert_bt).
    
  (* Specification for t holds, given hbt as inductive case *)    
  - intros hbt1 H_hbt1_inductive_assumption
           e
           hbt2 H_hbt2_inductive_assumption
           h_hbt hbt'
           H_sound_t_init H_insert_t.
    
    (* Before working on the particular subgoals, assert some essential 
     * hypotheses *)
    destruct (triple_sound_implies_hbts_sound
                A h_hbt hbt1 e hbt2 H_sound_t_init) as [H_hbt1_is_sound H_hbt2_is_sound].
    
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
      
      case (compare_int h_ret (2 + project_height_hbt A hbt2))
        as [ | | ] eqn : C_height_diff.

      (* The insertion does not unbalance the tree *) 
      *  unfold beq_nat in H_insert_t.
         apply (some_x_equal_some_y
                 (heightened_binary_tree A)
                 (HNode A (1 + max h_ret (project_height_hbt A hbt2))
                        (Node A (Triple A (HNode A h_ret bt_ret) e hbt2)))
                 hbt') in H_insert_t.
        rewrite <- H_insert_t.

        assert (H_hbt_ret_is_sound: is_sound_hbt A (HNode A h_ret bt_ret) = true).
        exact (H_hbt1_inductive_assumption (HNode A h_ret bt_ret)
                                           H_hbt1_is_sound
                                           P_some_eq).

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


      (* the insertion unbalances the tree: rotations required *) 
      * assert (H_hbt_ret_sound: is_sound_hbt A (HNode A h_ret bt_ret) = true).
        exact (H_hbt1_inductive_assumption
                 (HNode A h_ret bt_ret)
                 H_hbt1_is_sound P_some_eq).
        
        Check (rotate_right_preserves_soundness).
        Check (rotate_right_preserves_soundness
                 A h_ret bt_ret e hbt2 hbt'
                 H_hbt_ret_sound H_hbt2_is_sound H_insert_t).
        exact (rotate_right_preserves_soundness
                 A h_ret bt_ret e hbt2 hbt'
                 H_hbt_ret_sound H_hbt2_is_sound H_insert_t).

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

      case (compare_int h_ret (2 + project_height_hbt A hbt1))
        as [ | | ] eqn : C_height_diff.           

      (* The insertion does not unbalance the tree *) 
      * unfold beq_nat in H_insert_t.
        rewrite -> some_x_equal_some_y in H_insert_t.
        rewrite <- H_insert_t.

        assert (H_hbt_ret_is_sound: is_sound_hbt A (HNode A h_ret bt_ret) = true).
        exact (H_hbt2_inductive_assumption (HNode A h_ret bt_ret)
                                              H_hbt2_is_sound
                                              P_some_eq).
        
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
        


      (* the insertion unbalances the tree: rotations required *) 
      * assert (H_hbt_ret_sound: is_sound_hbt A (HNode A h_ret bt_ret) = true).
        exact (H_hbt2_inductive_assumption
                 (HNode A h_ret bt_ret)
                H_hbt2_is_sound P_some_eq).
        
        Check (rotate_left_preserves_soundness).
        Check (rotate_left_preserves_soundness
                 A hbt1 e h_ret bt_ret hbt'
                 H_hbt1_is_sound H_hbt_ret_sound H_insert_t).
        exact (rotate_left_preserves_soundness
                 A hbt1 e h_ret bt_ret hbt'
                 H_hbt1_is_sound H_hbt_ret_sound H_insert_t).

      * discriminate.

      * discriminate.
Qed.


