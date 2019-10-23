Require Import Hbt.Implementation.hbt.
Require Export Hbt.Implementation.hbt.


(* ********** Lemmas concerning soundness ********** *)

Lemma unfold_beq_nat_Sn_Sm:
  forall (n m : nat),
    beq_nat (S n) (S m) = beq_nat n m.
Proof.
  unfold_tactic beq_nat.
Qed.
    
Lemma unfold_max_Sn_Sm:
  forall (n m : nat),
    max (S n) (S m) = S (max n m).
Proof.
  unfold_tactic max.
Qed.

(* put this in paraphernalia *)
Lemma pred_succ:
  forall (n : nat),
    pred (S n) = n.
Proof.
  intros.
  unfold pred.
  reflexivity.
Qed.

Lemma succ_eq:
  forall (a b : nat),
    S a = S b -> a = b.
Proof.
  intros.
  
  assert (H_pred:
            pred (S a) = pred (S b)).
  rewrite H.
  reflexivity.
  
  Check (pred_succ).
  rewrite -> pred_succ in H_pred.
  rewrite -> pred_succ in H_pred.
  exact H_pred.
Qed.

Lemma add_to_both_sides:
  forall (x y z : nat),
    x = y -> x + z = y + z.
  intros.
  induction z as [ | z' IH_z'].
  rewrite -> plus_0_r.
  rewrite -> plus_0_r.
  exact H.

  rewrite <- plus_n_Sm.
  rewrite <- plus_n_Sm.
  rewrite -> IH_z'.
  reflexivity.
Qed.

Lemma minus_Sn_0:
  forall (n : nat),
    S n - 0 = S n.
Proof.
  unfold_tactic minus.
Qed.

Lemma minus_Sn_Sm:
  forall (n m : nat),
    S n - S m = n - m.
Proof.
  unfold_tactic minus.
Qed.

Lemma minus_n_0:
  forall (n : nat),
    n - 0 = n.
Proof.
  intros.
  case n as [ | n'].

  unfold minus.
  reflexivity.

  rewrite -> minus_Sn_0.
  reflexivity.
Qed.


Lemma prop_to_bool_helper:
  forall (a : nat),
    a = a -> ((a =n= a) = true).
Proof.
  intros.
  induction a as [ | a' IH_a].
  unfold beq_nat.
  reflexivity.
  
  rewrite -> unfold_beq_nat_Sn_Sm. 
  apply IH_a.
  exact (succ_eq a' a' H).
Qed.  

Lemma prop_to_bool:
  forall (a b : nat),
    a = b -> ((a =n= b) = true).
Proof.
  intros.
  induction a as [ | a' IH_a].
  case b as [ | b'].
  unfold beq_nat.
  reflexivity.
  discriminate.

  case b as [ | b'].
  discriminate.
  rewrite -> H.
  rewrite -> unfold_beq_nat_Sn_Sm.
  
  assert (H_trivial: b' = b').
  reflexivity.
  exact (prop_to_bool_helper b' H_trivial).
Qed.  



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
  intros. 
  unfold is_balanced_hbt in H.
  rewrite -> unfold_traverse_to_check_balanced_hbt in H.
  rewrite -> unfold_traverse_to_check_balanced_bt_node in H.
  rewrite -> unfold_traverse_to_check_balanced_t in H.  

  case (traverse_to_check_balanced_hbt A hbt1) as [h1 | ] eqn : C_check_hbt1. 
  case (traverse_to_check_balanced_hbt A hbt2) as [h2 | ] eqn : C_check_hbt2. 
  case (differ_by_one h1 h2) as [ | ] eqn : C_diff_by_one.
  split.
  
  unfold is_balanced_hbt.
  rewrite -> C_check_hbt1.
  reflexivity.

  unfold is_balanced_hbt.
  rewrite -> C_check_hbt2.
  reflexivity.

  discriminate.

  discriminate.

  discriminate.
Qed.

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
  case (h_ret =n= h_given) as [ | ] eqn : C_equal_nats_implies_true_prop.
  apply (beq_nat_true h_ret h_given) in C_equal_nats_implies_true_prop.  
  apply (some_x_equal_some_y nat h_given h) in H_traverse_sound.
  exact H_traverse_sound.

  discriminate.

  discriminate.
Qed.

(* Essential lemma to related height differences between 2 trees and the 
 * differ_by_one defintion *)  
Lemma relating_compare_int_and_differ_by_one:
  forall (ha hb : nat),
    (compare_int ha (2 + hb) = Lt)
    \/
    (compare_int hb (2 + ha) = Lt)
    ->
    differ_by_one ha hb = true.
Proof.
  intros ha hb [H_ab | H_ba].
  
  - unfold compare_int in H_ab.
    case (ha <n 2 + hb) as [ | ] eqn : C_ha_lt_hb.
    case ha as [ | ha'] eqn : C_ha.
    case hb as [ | hb'] eqn : C_hb.

    + unfold differ_by_one.
      unfold beq_nat at 3.
      Check (orb_true_r).
      apply orb_true_r.

  (*   + unfold ltb in C_ha_lt_hb. *)


  (*   case (ha - hb) as [ | hd] eqn : C_height_diff. *)
    
  (*   + unfold differ_by_one. *)
  (*     apply (diff_equal_0_implies_equal ha hb) in C_height_diff. *)
  (*     rewrite -> C_height_diff. *)
  (*     Check (beq_nat_refl hb). *)
  (*     rewrite <- (beq_nat_refl hb). *)
  (*     Check (orb_true_r ((hb =n= hb + 1) || (hb =n= hb + 1))). *)
  (*     exact (orb_true_r ((hb =n= hb + 1) || (hb =n= hb + 1))). *)
    
  (*   + case hd as [ | hd'] eqn : C_height_diff_succ. *)
  (*     unfold differ_by_one. *)
  (*     Check (diff_equal_1_implies_greater_by_1). *)
  (*     apply (diff_equal_1_implies_greater_by_1 ha hb) in C_height_diff. *)
  (*     rewrite -> C_height_diff. *)
  (*     rewrite <- (beq_nat_refl (hb + 1)). *)
  (*     Search (true || _ = _). *)
  (*     exact (orb_true_l ((hb =n= hb + 1 + 1) || (hb =n= hb + 1))). *)
      
  (*     rewrite -> (unfold_ltb_Sn_Sm (S hd') 1) in H_ab. *)
  (*     rewrite -> (unfold_ltb_Sn_Sm hd' 0) in H_ab. *)
  (*     case hd' as [ | hd'']. *)
  (*     rewrite -> (unfold_ltb_0_0) in H_ab. *)
  (*     unfold beq_nat in H_ab. *)
  (*     discriminate. *)

  (*     rewrite -> (unfold_ltb_Sn_0 hd'') in H_ab. *)
  (*     unfold beq_nat in H_ab. *)
  (*     discriminate. *)
      
  (* - unfold compare_int in H_ba. *)
  (*   case (hb - ha) as [ | hd] eqn : C_height_diff. *)
    
  (*   + unfold differ_by_one. *)
  (*     apply (diff_equal_0_implies_equal hb ha) in C_height_diff. *)
  (*     rewrite -> C_height_diff. *)
  (*     rewrite <- (beq_nat_refl ha). *)
  (*     Check (orb_true_r ((hb =n= ha + 1) || (ha =n= ha + 1))). *)
  (*     exact (orb_true_r ((ha =n= ha + 1) || (ha =n= ha + 1))). *)
    
  (*   + case hd as [ | hd'] eqn : C_height_diff_succ. *)
  (*     unfold differ_by_one. *)
  (*     Check (diff_equal_1_implies_greater_by_1). *)
  (*     apply (diff_equal_1_implies_greater_by_1 hb ha) in C_height_diff. *)
  (*     rewrite -> C_height_diff. *)
  (*     rewrite <- (beq_nat_refl (ha + 1)). *)
  (*     Search (true || _ = _). *)
  (*     rewrite -> (orb_true_r (ha =n= ha + 1 + 1)). *)
  (*     rewrite -> (orb_true_l (ha + 1 =n= ha)). *)
  (*     reflexivity. *)
      
  (*     rewrite -> (unfold_ltb_Sn_Sm (S hd') 1) in H_ba. *)
  (*     rewrite -> (unfold_ltb_Sn_Sm hd' 0) in H_ba. *)
  (*     case hd' as [ | hd'']. *)
  (*     rewrite -> (unfold_ltb_0_0) in H_ba. *)
  (*     unfold beq_nat in H_ba. *)
  (*     discriminate. *)

  (*     rewrite -> (unfold_ltb_Sn_0 hd'') in H_ba. *)
  (*     unfold beq_nat in H_ba. *)
  (*     discriminate. *)
      (*     Qed. *)
Admitted.


(* the most important lemma for balancedness: it provides the conditions for which
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
      ((compare_int (project_height_hbt A hbt1) (2 + (project_height_hbt A hbt2)) = Lt)
      \/
      (compare_int (project_height_hbt A hbt2) (2 + (project_height_hbt A hbt1)) = Lt)) ->
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
 
    Check (relating_compare_int_and_differ_by_one).
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

Lemma balanced_implies_some_height:
  forall (A : Type)
         (h : nat)
         (bt : binary_tree A),
    is_sound_hbt A (HNode A h bt) = true -> 
    is_balanced_hbt A (HNode A h bt) = true ->
    traverse_to_check_balanced_hbt A (HNode A h bt) = Some h.
Proof.
  intros.
  unfold is_balanced_hbt in H0.
  case (traverse_to_check_balanced_hbt A (HNode A h bt))
    as [h_ret_bal | ] eqn : C_traverse_bal.

  Check (soundness_implies_some_height).
  assert (H1 :
            traverse_to_check_soundness_hbt A (HNode A h bt) = Some h).
  exact (soundness_implies_some_height A h bt H).

  Check (relating_soundness_and_balancedness).
  destruct (relating_soundness_and_balancedness A) as [H_sound_bal_hbt _].

  assert (H_ret_bal_eq_h: h = h_ret_bal).
  exact (H_sound_bal_hbt (HNode A h bt) h h_ret_bal H1 C_traverse_bal).

  rewrite -> H_ret_bal_eq_h.
  reflexivity.

  discriminate.
Qed.

Lemma H_max_S:
  forall (a : nat),
    max (a + 1) a = a + 1.
Proof.                      
  intros.
  induction a as [ | a' IH_a'].
  rewrite -> plus_0_l.
  unfold max.
  reflexivity.
  
  Search (max _ _ = _).
  rewrite -> (plus_comm (S a') 1).
  Search (S _ = _).
  rewrite <- plus_n_Sm.
  rewrite -> unfold_max_Sn_Sm.
  rewrite -> plus_comm in IH_a'.
  rewrite -> IH_a'.
  reflexivity.
Qed.

Lemma ltb_false_case:
  forall (a x : nat),
    (a + x <n a + x) = false.
Proof.
  intros.
  induction a as [ | a' IH_a'].

  Focus 2.
  Search (S _ + _ = _).
  rewrite -> plus_Sn_m.
  rewrite -> unfold_ltb_Sn_Sm.
  exact IH_a'.

  rewrite -> plus_0_l.
  induction x as [ | x' IH_x'].
  unfold ltb.
  reflexivity.

  rewrite -> unfold_ltb_Sn_Sm.
  exact IH_x'.
Qed.

Lemma same_nat_differs_by_one:
  forall (n : nat),
    differ_by_one n n = true.
Proof.
  intros.
  unfold differ_by_one.
  induction n as [ | n' IH_n'].

  unfold beq_nat at 3.
  Search (_ || true = _).
  rewrite -> orb_true_r.
  reflexivity.

  rewrite -> plus_Sn_m.
  rewrite -> unfold_beq_nat_Sn_Sm.
  rewrite -> unfold_beq_nat_Sn_Sm.
  exact IH_n'.
Qed.

Lemma nat_and_succ_nat_differ_by_one:
  forall (n : nat),
    differ_by_one (1 + n) n = true.
Proof.  
  intros.
  unfold differ_by_one.
  rewrite -> (plus_comm n 1).

  induction n as [ | n' IH_n'].
  
  Focus 2.
  rewrite -> unfold_beq_nat_Sn_Sm.
  rewrite -> unfold_beq_nat_Sn_Sm.    
  rewrite -> unfold_beq_nat_Sn_Sm in IH_n'.
  rewrite -> unfold_beq_nat_Sn_Sm.
  rewrite -> plus_Sn_m.
  rewrite -> unfold_beq_nat_Sn_Sm.  
  exact IH_n'.

  rewrite -> plus_0_r.
  rewrite -> unfold_beq_nat_Sn_Sm.  
  unfold beq_nat at 1.
  rewrite -> orb_true_l.
  reflexivity.
Qed.

Lemma beq_nat_symm:
  forall (x y : nat),
    (x =n= y) = (y =n= x).
Proof.
  intros.
  
  case (x =n= y) as [ | ] eqn : C_xy.

  - apply beq_nat_true in C_xy.
    case (y =n= x) as [ | ] eqn : C_yx.
    reflexivity.

    apply beq_nat_false in C_yx.
    rewrite -> C_xy in C_yx.
    unfold not in C_yx.

    assert (H_trivial: y = y).
    reflexivity.

    apply C_yx in H_trivial.
    apply False_ind.

    exact H_trivial.

  - apply beq_nat_false in C_xy.
    unfold not in C_xy.
    case (y =n= x) as [ | ] eqn : C_yx.
    apply beq_nat_true in C_yx.
    symmetry in C_yx.
    apply C_xy in C_yx.
    apply False_ind.
    exact C_yx.
    reflexivity.
Qed.

Lemma differ_by_one_symm:
  forall (x y : nat),
    differ_by_one x y = differ_by_one y x.
Proof.  
  intros.
  unfold differ_by_one.
  rewrite -> (orb_comm (x =n= y + 1) (y =n= x + 1)).
  rewrite -> (beq_nat_symm y x) at 1.
  reflexivity.
Qed.

Lemma right_insert_differ_by_one:
  forall (h1 h2 h_ret : nat),
    differ_by_one h1 h2 = true ->
    (h_ret =n= h2) || (h_ret =n= 1 + h2) = true ->
    compare_int h_ret (2 + h1) = Lt ->
    differ_by_one h1 h_ret = true.
Proof.
  intros.
  case (h_ret =n= h2) as [ | ] eqn : C_h_ret_h2.

  - apply beq_nat_true in C_h_ret_h2.
    rewrite <- C_h_ret_h2 in H.
    exact H.

  - Search (false || _ = _).
    rewrite -> orb_false_l in H0.
    apply beq_nat_true in H0.
    unfold differ_by_one in H.

    case (h1 =n= h2 + 1) as [ | ] eqn : C_h1_eq_S_h2.

    + apply beq_nat_true in C_h1_eq_S_h2.
      rewrite -> plus_comm in C_h1_eq_S_h2.
      rewrite <- C_h1_eq_S_h2 in H0.
      rewrite <- H0.
      rewrite -> same_nat_differs_by_one.
      reflexivity.
      
    + rewrite -> orb_false_l in H.
      
      case (h2 =n= h1 + 1) as [ | ] eqn : C_h2_eq_S_h1.
      apply beq_nat_true in C_h2_eq_S_h1.
      rewrite -> C_h2_eq_S_h1 in H0.
      rewrite -> (plus_comm h1 1) in H0.
      rewrite -> plus_assoc in H0.
      rewrite <- BinInt.ZL0 in H0.
      rewrite -> H0 in H1.
      unfold compare_int in H1.
      rewrite -> ltb_false_case in H1.
      case (2 + h1 =n= 2 + h1) as [ | ].
      discriminate.
      discriminate.

      rewrite -> orb_false_l in H.
      apply beq_nat_true in H.
      rewrite H in H0.
      rewrite H0.
      rewrite -> differ_by_one_symm.
      rewrite -> (nat_and_succ_nat_differ_by_one h1).
      reflexivity.
Qed.


Lemma left_insert_differ_by_one:
  forall (h1 : nat)
         (h2 : nat)
         (h_ret : nat),
    differ_by_one h1 h2 = true ->
    (h_ret =n= h1) || (h_ret =n= 1 + h1) = true ->
    compare_int h_ret (2 + h2) = Lt ->     
    differ_by_one h_ret h2 = true. 
Proof.
  intros.
  case (h_ret =n= h1) as [ | ] eqn : C_h_ret_h1.

  - apply beq_nat_true in C_h_ret_h1.
    rewrite <- C_h_ret_h1 in H.
    exact H.

  - Search (false || _ = _).
    rewrite -> orb_false_l in H0.
    apply beq_nat_true in H0.
    unfold differ_by_one in H.

    case (h1 =n= h2 + 1) as [ | ] eqn : C_h1_eq_S_h2.

    + apply beq_nat_true in C_h1_eq_S_h2.
      rewrite -> C_h1_eq_S_h2 in H0.
      rewrite -> (plus_comm h2 1) in H0.
      rewrite -> plus_assoc in H0.
      rewrite <- BinInt.ZL0 in H0.
      rewrite -> H0 in H1.
      unfold compare_int in H1.
      rewrite -> ltb_false_case in H1.
      case (2 + h2 =n= 2 + h2) as [ | ].
      discriminate.
      discriminate.
      
    + rewrite -> orb_false_l in H.

      case (h2 =n= h1 + 1) as [ | ] eqn : C_h2_eq_S_h1.
      apply beq_nat_true in C_h2_eq_S_h1.
      rewrite -> plus_comm in C_h2_eq_S_h1.
      rewrite <- C_h2_eq_S_h1 in H0.
      rewrite H0.
      exact (same_nat_differs_by_one h2).
      
      rewrite -> orb_false_l in H.
      apply beq_nat_true in H.
      rewrite <- H in H0.
      rewrite H0.
      rewrite -> (nat_and_succ_nat_differ_by_one h2).
      reflexivity.
Qed.

Lemma rotate_right_differ_by_one_1: 
  forall (h121 h122 h11 h12: nat),
    h12 = 1 + max h121 h122 ->
    h11 + 1 = h12 -> 
    differ_by_one h121 h122 = true ->
    differ_by_one h11 (1 + max h121 h122) = true ->
    differ_by_one h11 h121 = true.
Proof.
  intros.
  rewrite -> H in H0.
  rewrite -> (plus_comm h11 1) in H0.
  Check (succ_eq).
  Check (succ_eq h11 (max h121 h122)).
  apply (succ_eq h11 (max h121 h122)) in H0.

  unfold differ_by_one in H1.
  unfold differ_by_one in H2.
  unfold differ_by_one. 
  case (h121 =n= h122 + 1) as [ | ] eqn : C_h121_h122.
  
  - apply beq_nat_true in C_h121_h122.
    rewrite -> C_h121_h122 in H0.
    rewrite -> C_h121_h122.
    rewrite -> H_max_S in H0.
    symmetry in H0.
    Check (prop_to_bool).
    apply prop_to_bool in H0.
    rewrite -> H0.
    Search (_ || _ = _).
     apply orb_true_r.

  - Search (_ || _ = _).
    rewrite -> orb_false_l in H1.
    case (h122 =n= h121 + 1) as [ | ] eqn : C_h122_h121.

    + apply beq_nat_true in C_h122_h121.
      rewrite C_h122_h121 in H0.
      Search (max _ _ = _).
      rewrite -> Max.max_comm in H0.
      rewrite -> H_max_S in H0.
      apply prop_to_bool in H0.      
      rewrite -> H0.
      apply orb_true_l.

    + rewrite -> orb_false_l in H1.
      apply beq_nat_true in H1.
      rewrite -> H1 in H0.
      Search (max _ _ = _).
      rewrite -> Max.max_idempotent in H0.
      symmetry in H0.
      apply prop_to_bool in H0.      
      rewrite -> H0.
      apply orb_true_r.
Qed.


Lemma rotate_right_differ_by_one_2:
  forall (h121 h122 h12 h11 h_ret h2: nat),
    differ_by_one h121 h122 = true -> 
    h12 = 1 + max h121 h122 ->
    h11 + 1 = h12 ->
    h_ret = 1 + max h11 h12 ->
    h_ret = 2 + h2 -> 
    differ_by_one h122 h2 = true.
Proof.  
  intros.
  rewrite -> H0 in H1.
  rewrite -> (plus_comm h11 1) in H1.
  Check (succ_eq).
  apply (succ_eq h11 (max h121 h122)) in H1.
  rewrite -> H0 in H2.
  rewrite -> H1 in H2.
  rewrite -> H2 in H3.

  (* now consider the 3 possible cases for h121 and h122 *)
  unfold differ_by_one in H.
  case (h121 =n= h122 + 1) as [ | ] eqn : C_h121_h122.

  (* h121 = h122 + 1; subsitute all instances of h121 with h122 *)
  - apply beq_nat_true in C_h121_h122.
    rewrite -> C_h121_h122 in H3.
    Check (H_max_S).
    rewrite -> H_max_S in H3.
    rewrite -> (plus_comm 1 (h122 + 1)) in H3.
    Search (max _ _ = _). 
    rewrite -> Max.max_comm in H3.
    rewrite -> H_max_S in H3. 
    Search (_ + _ = _).
    rewrite -> (plus_assoc_reverse h122 1 1) in H3.
    rewrite <- BinInt.ZL0 in H3.
    rewrite -> (plus_comm h122 2) in H3.
    apply (succ_eq (2 + h122) (1 + h2)) in H3.
    apply (succ_eq (1 + h122) h2) in H3.
    unfold differ_by_one.
    symmetry in H3.
    rewrite plus_comm in H3.
    apply prop_to_bool in H3.
    rewrite H3.
    rewrite -> orb_comm.
    rewrite -> orb_true_r.
    rewrite -> orb_true_r.
    reflexivity.

  - rewrite ->  orb_false_l in H.
    case (h122 =n= h121 + 1) as [ | ] eqn : C_h122_eq_succ_h121.

    (* h122 = h121 + 1 *)
    + apply beq_nat_true in C_h122_eq_succ_h121.
      rewrite -> C_h122_eq_succ_h121.
      rewrite -> C_h122_eq_succ_h121 in H3.
      rewrite -> (Max.max_comm h121 (h121 + 1)) in H3.
      rewrite -> H_max_S in H3.
      rewrite -> (Max.max_comm (h121 + 1) (1 + (h121 + 1))) in H3.
      rewrite -> (plus_comm 1 (h121 + 1)) in H3.
      rewrite -> H_max_S in H3.
      apply (succ_eq (h121 + 1 + 1) (1 + h2))in H3.
      rewrite -> (plus_comm h121 1) in H3.
      apply (succ_eq (h121 + 1) h2) in H3.
      rewrite -> H3.
      Check (same_nat_differs_by_one).
      rewrite -> same_nat_differs_by_one.
      reflexivity.

    (* h122 = h121 *)
    + rewrite ->  orb_false_l in H.
      apply beq_nat_true in H.
      rewrite <- H in H3.
      Search (max _ _ = _).
      rewrite -> Max.max_idempotent in H3.
      rewrite -> Max.max_comm in H3.
      rewrite -> (plus_comm 1 h122) in H3.
      rewrite -> H_max_S in H3.
      apply (succ_eq (h122 + 1) (1 + h2)) in H3.
      rewrite -> (plus_comm h122 1) in H3.
      apply succ_eq in H3.
      rewrite -> H3.
      rewrite -> same_nat_differs_by_one.
      reflexivity.
Qed.      

Lemma rotate_right_differ_by_one_3:
  forall (h121 h122 h12 h11 h_ret h2 : nat),
    differ_by_one h121 h122 = true -> 
    h12 = 1 + max h121 h122 ->
    h11 + 1 = h12 ->
    h_ret = 1 + max h11 h12 ->
    h_ret = 2 + h2 -> 
    differ_by_one (1 + max h11 h121) (1 + max h122 h2) = true.
Proof.
  intros.

  (* show that h11 = max h121 h122 *)
  rewrite H0 in H1.
  rewrite -> (plus_comm h11 1) in H1.
  apply succ_eq in H1.

  (* show that h2 = max h121 h122 *)
  rewrite -> H2 in H3.
  rewrite -> H1 in H3.
  rewrite -> H0 in H3.
  Search (max _ _ = _).
  rewrite -> Max.max_comm in H3.
  Check (H_max_S).
  rewrite -> (plus_comm 1 (max h121 h122)) in H3.
  rewrite -> H_max_S in H3.
  rewrite -> (plus_comm (max h121 h122) 1) in H3.
  apply succ_eq in H3.
  apply succ_eq in H3.  

  (* now substitute these values in *)
  rewrite <- H3.
  rewrite -> H1.

  (* finally, consider the three possible relationships between h121 h122 *)
  unfold differ_by_one in H.
  case (h121 =n= h122 + 1) as [ | ] eqn : C_h121_eq_S_h122.

  (* h121 = h122 + 1 *)
  - apply beq_nat_true in C_h121_eq_S_h122.
    rewrite -> C_h121_eq_S_h122.
    rewrite -> H_max_S.
    rewrite -> (Max.max_comm h122 (h122 + 1)).
    rewrite -> H_max_S.
    Search (max _ _ = _).
    rewrite -> Max.max_idempotent.
    rewrite -> same_nat_differs_by_one.
    reflexivity.

  - rewrite -> orb_false_l in H.
    case (h122 =n= h121 + 1) as [ | ] eqn : C_h122_eq_S_h121.

    (* h122 = h121 + 1 *)
    + apply beq_nat_true in C_h122_eq_S_h121.
      rewrite -> C_h122_eq_S_h121.
      rewrite -> (Max.max_comm h121 (h121 + 1)).
      rewrite -> H_max_S.
      rewrite -> H_max_S.      
      rewrite -> Max.max_idempotent.
      rewrite -> same_nat_differs_by_one.      
      reflexivity.

    (* h122 = h121 *)
    + rewrite -> orb_false_l in H.
      apply beq_nat_true in H.
      rewrite -> H.
      rewrite -> Max.max_idempotent.
      rewrite -> same_nat_differs_by_one.      
      reflexivity.
Qed.

Lemma rotate_right_differ_by_one_4:
  forall (h12 h11 h2 h_ret : nat),
    (h12 + 1 =n= h11) || (h12 =n= h11) = true ->
    h_ret = 2 + h2 ->
    h_ret = 1 + max h11 h12 ->
    differ_by_one h12 h2 = true /\ differ_by_one h11 (1 + max h12 h2) = true.
Proof.
  intros.
  case (h12 + 1 =n= h11) as [ | ] eqn : C_S_h12_eq_h11.

  - apply beq_nat_true in C_S_h12_eq_h11.
    rewrite <- C_S_h12_eq_h11 in H1.
    rewrite -> H_max_S in H1.
    rewrite -> H0 in H1.
    apply succ_eq in H1.
    rewrite -> plus_comm in H1.
    apply succ_eq in H1.
    rewrite H1.

    split.

    + rewrite -> same_nat_differs_by_one.
      reflexivity.

    + rewrite <- C_S_h12_eq_h11.
      rewrite -> Max.max_idempotent.
      rewrite -> plus_comm.
      rewrite -> same_nat_differs_by_one.
      reflexivity.

  - rewrite -> orb_false_l in H.
    apply beq_nat_true in H.
    rewrite -> H in H1.
    Search (max _ _ = _).
    rewrite -> Max.max_idempotent in H1.
    rewrite H0 in H1.
    apply succ_eq in H1.
    rewrite <- H in H1.
    rewrite <- H1.
    split.

    + unfold differ_by_one.

      assert (H_trivial: S h2 = h2 + 1).
      rewrite -> plus_comm.
      reflexivity.

      assert (H_we_need: (S h2 =n= h2 + 1) = true).
      Check (prop_to_bool).
      exact (prop_to_bool (S h2) (h2 + 1) H_trivial).

      rewrite -> H_we_need.
      rewrite -> orb_true_l.
      reflexivity.

    + rewrite <- H.
      rewrite <- H1.
      
      assert (H_trivial: S h2 = h2 + 1).
      rewrite -> plus_comm.
      reflexivity.

      rewrite -> H_trivial.
      rewrite -> H_max_S.
      Check (differ_by_one_symm).
      rewrite -> differ_by_one_symm.
      Check (nat_and_succ_nat_differ_by_one).
      rewrite -> nat_and_succ_nat_differ_by_one.
      reflexivity.
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
    compare_int h_ret (2 + project_height_hbt A hbt2)  = Eq ->  
    is_balanced_hbt A hbt' = true.
Proof.
  intros.

  (* destruct and unfold *)
  unfold rotate_right_hbt in H3.
  induction hbt2 as [h2 bt2].
  unfold rotate_right_bt in H3.
  induction bt_ret as [ | t_ret].
  discriminate.
  induction t_ret as [[h11 bt11] e1 [h12 bt12]].
  case (h11 + 1 =n= h12) as [ | ] eqn : C_h11_h12.

  (* h11 + 1 = h12 *)
  case bt12 as [ | [[h121 bt121] e12 [h122 bt122]]].

  (* bt12 is leaf : impossible case *)
  - discriminate.

  (* bt12 is node *)
  - rewrite -> some_x_equal_some_y in H3.
    rewrite <- H3.

    (* show that all the subtrees are sound *)
    Check (triple_sound_implies_hbts_sound).
    destruct (triple_sound_implies_hbts_sound
                A h_ret
                (HNode A h11 bt11) e1
                (HNode A h12 (Node A (Triple A (HNode A h121 bt121) e12 (HNode A h122 bt122))))
                H1) as [H_bt11_sound H_right_subtree_sound].
    destruct (triple_sound_implies_hbts_sound
                A h12
                (HNode A h121 bt121)
                e12
                (HNode A h122 bt122) H_right_subtree_sound) as [ H_bt121_sound H_bt122_sound].

    (* show that all the subtrees are balanced *)
    Check (triple_balanced_implies_hbts_balanced).
    destruct (triple_balanced_implies_hbts_balanced
                A h_ret
                (HNode A h11 bt11) e1
                (HNode A h12 (Node A (Triple A (HNode A h121 bt121) e12 (HNode A h122 bt122))))
                H) as [H_bt11_balanced H_right_subtree_balanced].
    destruct (triple_balanced_implies_hbts_balanced
                A h12
                (HNode A h121 bt121)
                e12
                (HNode A h122 bt122) H_right_subtree_balanced) as [ H_bt121_balanced H_bt122_balanced].

    (* since the bts are sound, the heights returned by the 
     * traverse_to_check_balanced_hbt are the heights stored in the tree itself *)
    Check (balanced_implies_some_height).

    assert (H_bt11_h11:
              traverse_to_check_balanced_hbt A (HNode A h11 bt11) = Some h11).
    exact (balanced_implies_some_height A h11 bt11 H_bt11_sound H_bt11_balanced).

    assert (H_bt121_h121:
              traverse_to_check_balanced_hbt A (HNode A h121 bt121) = Some h121).
    exact (balanced_implies_some_height A h121 bt121 H_bt121_sound H_bt121_balanced).

    assert (H_bt122_h122:
              traverse_to_check_balanced_hbt A (HNode A h122 bt122) = Some h122).
    exact (balanced_implies_some_height A h122 bt122 H_bt122_sound H_bt122_balanced).

    assert (H_bt2_h2:
              traverse_to_check_balanced_hbt A (HNode A h2 bt2) = Some h2).
    exact (balanced_implies_some_height A h2 bt2 H2 H0).

    (* unfold the goal *)
    unfold is_balanced_hbt.
    rewrite -> unfold_traverse_to_check_balanced_hbt.
    rewrite -> unfold_traverse_to_check_balanced_bt_node.
    rewrite -> unfold_traverse_to_check_balanced_t.
    rewrite -> unfold_traverse_to_check_balanced_hbt.
    rewrite -> unfold_traverse_to_check_balanced_bt_node.
    rewrite -> unfold_traverse_to_check_balanced_t.
    rewrite -> H_bt11_h11.
    rewrite -> H_bt121_h121.

    (* we now need to show that the resultant sub-trees are balanced; do so by unfolding 
     * H*)
    unfold is_balanced_hbt in H.
    case (traverse_to_check_balanced_hbt A
          (HNode A h_ret
             (Node A
                (Triple A (HNode A h11 bt11) e1
                   (HNode A h12
                      (Node A (Triple A (HNode A h121 bt121) e12 (HNode A h122 bt122)))))))) as [h_ret_bal | ] eqn : C_traverse_bt_ret.
    rewrite -> unfold_traverse_to_check_balanced_hbt in C_traverse_bt_ret.
    rewrite -> unfold_traverse_to_check_balanced_bt_node in C_traverse_bt_ret.
    rewrite -> unfold_traverse_to_check_balanced_t in C_traverse_bt_ret.
    rewrite -> H_bt11_h11 in C_traverse_bt_ret.
    rewrite -> unfold_traverse_to_check_balanced_hbt in C_traverse_bt_ret.
    rewrite -> unfold_traverse_to_check_balanced_bt_node in C_traverse_bt_ret.
    rewrite -> unfold_traverse_to_check_balanced_t in C_traverse_bt_ret.
    rewrite -> H_bt121_h121 in C_traverse_bt_ret.
    rewrite -> H_bt122_h122 in C_traverse_bt_ret.
    
    (* relate h121, h122, h11, and h12 from the tree that was originally returned *)
    case (differ_by_one h121 h122) as [ | ] eqn : C_diff_by_one_h121_h122.
    case (differ_by_one h11 (1 + max h121 h122))
         as [ | ] eqn : C_diff_by_one_h11_h121_h122.
    apply beq_nat_true in C_h11_h12.

    (* assert relation h12 = 1 + max h121 h122 *)
    assert (H_h12_h122_h121: h12 = 1 + max h121 h122).
    Check (relate_heights).    
    exact (relate_heights A h12 h121 bt121 e12 h122 bt122 H_right_subtree_sound).

    (* now proceed to show that the resultant sub-trees in the goal and also balanced *)

    (* first, sub-tree with h11 and h121 as sub-trees is balanced *)
    assert (H_h11_h121_diff_by_one: differ_by_one h11 h121 = true).
    Check (rotate_right_differ_by_one_1).
    Check (rotate_right_differ_by_one_1
             h121 h122 h11 h12 H_h12_h122_h121 C_h11_h12
             C_diff_by_one_h121_h122 C_diff_by_one_h11_h121_h122).
    exact (rotate_right_differ_by_one_1
             h121 h122 h11 h12 H_h12_h122_h121 C_h11_h12
             C_diff_by_one_h121_h122 C_diff_by_one_h11_h121_h122).
    
    (* continue unfolding *)
    rewrite -> H_h11_h121_diff_by_one.
    rewrite -> unfold_traverse_to_check_balanced_hbt.
    rewrite -> unfold_traverse_to_check_balanced_bt_node.
    rewrite -> unfold_traverse_to_check_balanced_t.    
    rewrite -> H_bt122_h122.
    rewrite -> H_bt2_h2. 

    (* assert that the sub-tree with h122 and h2 is balanced; to do so, we need the 
     * relation between h_ret and h2 *)
    unfold project_height_hbt in H4.
    unfold compare_int in H4.
    case (h_ret <n 2 + h2) as [ | ].
    discriminate.
    case (h_ret =n= 2 + h2) as [ | ] eqn : C_diff_h_ret_h2.
    apply beq_nat_true in C_diff_h_ret_h2.

    assert (H_h_ret_h11_h12: h_ret = 1 + max h11 h12).
    Check (relate_heights).
    exact  (relate_heights
             A h_ret
             h11 bt11
             e1 h12
             (Node A (Triple A (HNode A h121 bt121) e12 (HNode A h122 bt122)))
             H1).
    
    assert (H_h122_h2_diff_by_one: differ_by_one h122 h2 = true).
    Check (rotate_right_differ_by_one_2).
    exact (rotate_right_differ_by_one_2
             h121 h122 h12 h11 h_ret h2
             C_diff_by_one_h121_h122 H_h12_h122_h121 C_h11_h12 H_h_ret_h11_h12
             C_diff_h_ret_h2).

    (* continue unfolding *)
    rewrite -> H_h122_h2_diff_by_one.
    Check (rotate_right_differ_by_one_3).
    rewrite -> (rotate_right_differ_by_one_3
                  h121 h122 h12 h11 h_ret h2
                  C_diff_by_one_h121_h122 H_h12_h122_h121 C_h11_h12 H_h_ret_h11_h12
                  C_diff_h_ret_h2).
    reflexivity.

    discriminate.

    discriminate.

    discriminate.

    discriminate.

  - case ((h12 + 1 =n= h11) || (h12 =n= h11)) as [ | ] eqn : C_h12_leq_h11.
    rewrite -> some_x_equal_some_y in H3.
    rewrite <- H3.

    (* show all subtrees are sound *)
    Check (triple_sound_implies_hbts_sound).
    destruct (triple_sound_implies_hbts_sound
                A h_ret (HNode A h11 bt11) e1 (HNode A h12 bt12) H1)
      as [H_bt11_sound H_bt12_sound].

    (* show all subtree are balanced *)
    Check (triple_balanced_implies_hbts_balanced).
    destruct (triple_balanced_implies_hbts_balanced
                A h_ret (HNode A h11 bt11) e1 (HNode A h12 bt12) H)
      as [H_bt11_balanced H_bt12_balanced].

    (* relate heights and traverse_to_check_balanced_hbt *)
    assert (H_bt11_h11:
              traverse_to_check_balanced_hbt A (HNode A h11 bt11) = Some h11).
    exact (balanced_implies_some_height A h11 bt11 H_bt11_sound H_bt11_balanced).

    assert (H_bt12_h12:
              traverse_to_check_balanced_hbt A (HNode A h12 bt12) = Some h12).
    exact (balanced_implies_some_height A h12 bt12 H_bt12_sound H_bt12_balanced).

    assert (H_bt2_h2:
              traverse_to_check_balanced_hbt A (HNode A h2 bt2) = Some h2).
    exact (balanced_implies_some_height A h2 bt2 H2 H0).

    (* unfold the goal *)
    unfold is_balanced_hbt.
    rewrite -> unfold_traverse_to_check_balanced_hbt.
    rewrite -> unfold_traverse_to_check_balanced_bt_node.
    rewrite -> unfold_traverse_to_check_balanced_t.
    rewrite -> H_bt11_h11.
    rewrite -> unfold_traverse_to_check_balanced_hbt.
    rewrite -> unfold_traverse_to_check_balanced_bt_node.
    rewrite -> unfold_traverse_to_check_balanced_t.    
    rewrite -> H_bt12_h12.
    rewrite -> H_bt2_h2.

    (* small things to get the required lemmas in place *)
    assert (H_h_ret_h11_h12: h_ret = 1 + max h11 h12).
    Check (relate_heights).
    exact (relate_heights A h_ret h11 bt11 e1 h12 bt12 H1).

    unfold project_height_hbt in H4.
    unfold compare_int in H4.
    case (h_ret <n 2 + h2) as [ | ].
    discriminate.
    case (h_ret =n= 2 + h2) as [ | ] eqn : C_h_ret_eq_SS_h2.
    apply beq_nat_true in C_h_ret_eq_SS_h2.

    Check (rotate_right_differ_by_one_4).
    destruct (rotate_right_differ_by_one_4
                h12 h11 h2 h_ret C_h12_leq_h11 C_h_ret_eq_SS_h2 H_h_ret_h11_h12)
             as [H_diff_by_one_h12_h2 H_diff_by_one_h11_S_max_h12_h2].
    rewrite -> H_diff_by_one_h12_h2.
    rewrite -> H_diff_by_one_h11_S_max_h12_h2.
    reflexivity.

    discriminate.

    discriminate.
Qed.

Lemma rotate_left_differ_by_one_1:
  forall (h1 h211 h212 : nat),
    h1 = max h211 h212 ->
    differ_by_one h211 h212 = true ->
    differ_by_one h1 h211 = true.
Proof.
  intros.
  rewrite H.
  unfold differ_by_one in H0.
  case (h211 =n= h212 + 1) as [ | ] eqn : C_h211_eq_S_h212.

  (* h211 = h212 + 1 *)
  - apply beq_nat_true in C_h211_eq_S_h212.
    rewrite -> C_h211_eq_S_h212.
    Check (H_max_S).
    rewrite -> H_max_S.
    rewrite -> same_nat_differs_by_one.
    reflexivity.

  - rewrite -> orb_false_l in H0.
    case (h212 =n= h211 + 1) as [ | ] eqn : C_h212_eq_S_h211.

    (* h212 = h211 + 1 *)
    + apply beq_nat_true in C_h212_eq_S_h211.
      rewrite -> C_h212_eq_S_h211.
      Search (max _ _ = _).
      rewrite -> Max.max_comm.
      rewrite -> H_max_S.
      rewrite -> plus_comm.
      rewrite -> nat_and_succ_nat_differ_by_one.
      reflexivity.

    (* h212 = h211 *)
    + rewrite -> orb_false_l in H0.
      apply beq_nat_true in H0.
      rewrite -> H0.
      rewrite -> Max.max_idempotent.
      rewrite -> same_nat_differs_by_one.
      reflexivity.
Qed.

Lemma rotate_left_differ_by_one_2:
  forall (h211 h212 h22 : nat),
    differ_by_one h211 h212 = true ->
    h22 = max h211 h212 ->
    differ_by_one h212 h22 = true.
Proof.
  intros.
  rewrite H0.
  unfold differ_by_one in H.
  case (h211 =n= h212 + 1) as [ | ] eqn : C_h211_eq_S_h212.

  - apply beq_nat_true in C_h211_eq_S_h212.
    rewrite -> C_h211_eq_S_h212.
    rewrite -> H_max_S.
    rewrite -> differ_by_one_symm.
    rewrite -> plus_comm.
    rewrite -> nat_and_succ_nat_differ_by_one.
    reflexivity.

  - rewrite -> orb_false_l in H.
    case (h212 =n= h211 + 1) as [ | ] eqn : C_h212_eq_S_h211.

    + apply beq_nat_true in C_h212_eq_S_h211.
      rewrite -> C_h212_eq_S_h211.
      rewrite -> (Max.max_comm h211 (h211 + 1)).
      rewrite -> H_max_S.
      rewrite -> same_nat_differs_by_one.
      reflexivity.

    + apply beq_nat_true in H.
      rewrite -> H.
      rewrite -> Max.max_idempotent.
      rewrite -> same_nat_differs_by_one.
      reflexivity.
Qed.      

Lemma rotate_left_differ_by_one_3:
  forall (h1 h211 h212 h22 : nat),
    h1 = max h211 h212 ->
    h22 = max h211 h212 ->
    differ_by_one h211 h212 = true ->
    differ_by_one (1 + max h1 h211) (1 + max h212 h22) = true.
Proof.
  intros.
  rewrite H.
  rewrite H0.
  unfold differ_by_one in H1.
  case (h211 =n= h212 + 1) as [ | ] eqn : C_h211_eq_S_h212.

  - apply beq_nat_true in C_h211_eq_S_h212.
    rewrite -> C_h211_eq_S_h212.
    rewrite -> H_max_S.
    rewrite -> Max.max_idempotent.
    rewrite -> Max.max_comm.
    rewrite -> H_max_S.
    rewrite -> same_nat_differs_by_one.
    reflexivity.

  - rewrite -> orb_false_l in H1.
    case (h212 =n= h211 + 1) as [ | ] eqn : C_h212_eq_S_h212.

    + apply beq_nat_true in C_h212_eq_S_h212.
      rewrite -> C_h212_eq_S_h212.
      rewrite -> (Max.max_comm h211 (h211 + 1)).
      rewrite -> H_max_S.
      rewrite -> H_max_S.
      rewrite -> Max.max_idempotent.
      rewrite -> same_nat_differs_by_one.
      reflexivity.

    + apply beq_nat_true in H1.
      rewrite -> H1.
      rewrite -> Max.max_idempotent.
      rewrite -> Max.max_idempotent.      
      rewrite -> same_nat_differs_by_one.
      reflexivity.
Qed.

Lemma rotate_left_differ_by_one_4:
  forall (h1 h21 h22 h_ret : nat),
    (h21 + 1 =n= h22) || (h21 =n= h22) = true -> 
    h_ret = 1 + max h21 h22 ->
    h_ret = 2 + h1 ->
    differ_by_one h1 h21 = true /\ differ_by_one (1 + max h1 h21) h22 = true.
Proof.
  intros.
  case (h21 + 1 =n= h22) as [ | ] eqn : C_S_h21_eq_h22.

  - apply beq_nat_true in C_S_h21_eq_h22.
    rewrite <- C_S_h21_eq_h22 in H0.
    rewrite -> Max.max_comm in H0.
    rewrite -> H_max_S in H0.
    rewrite H0 in H1.
    apply succ_eq in H1.
    rewrite -> plus_comm in H1.
    apply succ_eq in H1.
    split.

    + rewrite H1.
      rewrite -> same_nat_differs_by_one.
      reflexivity.

    + rewrite <- C_S_h21_eq_h22.
      rewrite H1.
      rewrite -> Max.max_idempotent.
      rewrite -> plus_comm.
      rewrite -> same_nat_differs_by_one.
      reflexivity.

  - rewrite -> orb_false_l in H.
    apply beq_nat_true in H.
    rewrite H in H0.
    rewrite -> Max.max_idempotent in H0.
    rewrite H0 in H1.
    apply succ_eq in H1.
    rewrite -> H.
    rewrite -> H1.
    split.

    + rewrite -> differ_by_one_symm.
      rewrite -> nat_and_succ_nat_differ_by_one.
      reflexivity.

    + rewrite -> (Max.max_comm h1 (S h1)).

      assert (H_trivial: S h1 = h1 + 1).
      rewrite -> plus_comm.
      reflexivity.
      
      rewrite -> H_trivial.
      rewrite -> H_max_S.
      Check (nat_and_succ_nat_differ_by_one).
      rewrite -> nat_and_succ_nat_differ_by_one.
      reflexivity.
Qed.


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
    compare_int h_ret (2 + project_height_hbt A hbt1)  = Eq ->  
    is_balanced_hbt A hbt' = true.
Proof.
  intros.

  (* destruct and unfold *)
  unfold rotate_left_hbt in H3.
  induction hbt1 as [h1 bt1].
  unfold rotate_left_bt in H3.
  induction bt_ret as [ | t_ret].
  discriminate.
  induction t_ret as [[h21 bt21] e2 [h22 bt22]].
  case (h22 + 1 =n= h21) as [ | ] eqn : C_h22_h21.

  (* h22 + 1 = h21 *)
  case bt21 as [ | [[h211 bt211] e21 [h212 bt212]]].

  (* bt12 is leaf : impossible case *)
  - discriminate.

  (* bt12 is node *)
  - rewrite -> some_x_equal_some_y in H3.
    rewrite <- H3.

    (* show that all subtrees are sound *)
    Check (triple_sound_implies_hbts_sound).
    destruct (triple_sound_implies_hbts_sound
                A h_ret
                (HNode
                   A
                   h21
                   (Node A (Triple A (HNode A h211 bt211) e21 (HNode A h212 bt212))))
                e2
                (HNode A h22 bt22)
                H2) as [H_left_subtree_sound H_bt22_sound].
    Check (triple_sound_implies_hbts_sound).    
    destruct (triple_sound_implies_hbts_sound
                A h21
                (HNode A h211 bt211) e21 (HNode A h212 bt212)
                H_left_subtree_sound) as [ H_bt211_sound H_bt212_sound].

    (* show that all the subtrees are balanced *)
    Check (triple_balanced_implies_hbts_balanced).
    destruct (triple_balanced_implies_hbts_balanced
                A h_ret
                (HNode
                   A
                   h21
                   (Node A (Triple A (HNode A h211 bt211) e21 (HNode A h212 bt212))))
                e2
                (HNode A h22 bt22)
                H0) as [H_left_subtree_balanced H_bt22_balanced].
    destruct (triple_balanced_implies_hbts_balanced
                A
                h21
                (HNode A h211 bt211) e21 (HNode A h212 bt212)
                H_left_subtree_balanced) as [H_bt211_balanced H_bt212_balanced].
    
    (* since the bts are sound, the heights returned by the 
     * traverse_to_check_balanced_hbt are the heights stored in the tree itself *)
    assert (H_bt211_h211:
              traverse_to_check_balanced_hbt A (HNode A h211 bt211) = Some h211).
    Check (balanced_implies_some_height).
    exact (balanced_implies_some_height A h211 bt211 H_bt211_sound H_bt211_balanced).

    assert (H_bt212_h212:
              traverse_to_check_balanced_hbt A (HNode A h212 bt212) = Some h212).
    Check (balanced_implies_some_height).
    exact (balanced_implies_some_height A h212 bt212 H_bt212_sound H_bt212_balanced).

    assert (H_bt22_h22:
              traverse_to_check_balanced_hbt A (HNode A h22 bt22) = Some h22).
    Check (balanced_implies_some_height).
    exact (balanced_implies_some_height A h22 bt22 H_bt22_sound H_bt22_balanced).    

    assert (H_bt1_h1:
              traverse_to_check_balanced_hbt A (HNode A h1 bt1) = Some h1).
    Check (balanced_implies_some_height).
    exact (balanced_implies_some_height A h1 bt1 H1 H).
    
    (* get some required hypotheses *)
    unfold is_balanced_hbt in H0.
    case (traverse_to_check_balanced_hbt A
           (HNode A h_ret
              (Node A
                 (Triple A
                    (HNode A h21
                       (Node A (Triple A (HNode A h211 bt211) e21 (HNode A h212 bt212)))) e2
                    (HNode A h22 bt22)))))
      as [h_ret_bal | ] eqn : C_traverse_bt_ret.
    rewrite -> unfold_traverse_to_check_balanced_hbt in C_traverse_bt_ret.
    rewrite -> unfold_traverse_to_check_balanced_bt_node in C_traverse_bt_ret.
    rewrite -> unfold_traverse_to_check_balanced_t in C_traverse_bt_ret.
    rewrite -> unfold_traverse_to_check_balanced_hbt in C_traverse_bt_ret.
    rewrite -> unfold_traverse_to_check_balanced_bt_node in C_traverse_bt_ret.
    rewrite -> unfold_traverse_to_check_balanced_t in C_traverse_bt_ret.    
    rewrite -> H_bt211_h211 in C_traverse_bt_ret.
    rewrite -> H_bt212_h212 in C_traverse_bt_ret.

    (* hypothesis that h211 and h212 differ by one *)
    case (differ_by_one h211 h212) as [ | ] eqn : C_diff_by_one_h211_h212.
    rewrite -> H_bt22_h22 in C_traverse_bt_ret.

    (* hypothesis that h21 = 1 + max h211 212 *)
    assert (H_h21_h211_h212 : h21 = 1 + max h211 h212).
    Check (relate_heights).
    exact (relate_heights A h21 h211 bt211 e21 h212 bt212 H_left_subtree_sound).

    (* simplify C_h22_h21 to show that h22 = max h211 h212 *)
    apply beq_nat_true in C_h22_h21.
    rewrite -> H_h21_h211_h212 in C_h22_h21.
    rewrite -> plus_comm in C_h22_h21.
    apply succ_eq in C_h22_h21.
    
    (* show that h_ret = 1 + max h21 h22 *)
    assert (H_h_ret_h21_h22: h_ret = 1 + max h21 h22).
    Check (relate_heights).
    exact (relate_heights
             A h_ret h21
             (Node A (Triple A (HNode A h211 bt211) e21 (HNode A h212 bt212)))
             e2 h22 bt22 H2).
    (* show that h_ret = 1 + max (1 + max h211 h212) h22 
     *                 = 1 + max (1 + max h211 h212) (max h211 h212)
     *                 = 1 + (1 + max h211 h212) 
     *                 = 2 + max h211 h212 *)
    rewrite -> H_h21_h211_h212 in H_h_ret_h21_h22.
    rewrite -> C_h22_h21 in H_h_ret_h21_h22.
    rewrite -> (plus_comm 1 (max h211 h212)) in H_h_ret_h21_h22.
    rewrite -> H_max_S in H_h_ret_h21_h22.
    rewrite -> (plus_comm (max h211 h212) 1) in H_h_ret_h21_h22.
    rewrite -> plus_assoc in H_h_ret_h21_h22.
    rewrite <- BinInt.ZL0 in H_h_ret_h21_h22.

    (* finally, relate h1 and h_ret *)
    unfold compare_int in H4.
    case (h_ret <n 2 + project_height_hbt A (HNode A h1 bt1)) as [ | ].
    discriminate.
    case (h_ret =n= 2 + project_height_hbt A (HNode A h1 bt1))
         as [ | ] eqn : H_h_ret_h1.
    apply beq_nat_true in H_h_ret_h1.
    unfold project_height_hbt in H_h_ret_h1.
    
    (* with all the required hypotheses in place, unfold the goal *)
    unfold is_balanced_hbt.
    rewrite -> unfold_traverse_to_check_balanced_hbt.
    rewrite -> unfold_traverse_to_check_balanced_bt_node.
    rewrite -> unfold_traverse_to_check_balanced_t.
    rewrite -> unfold_traverse_to_check_balanced_hbt.
    rewrite -> unfold_traverse_to_check_balanced_bt_node.
    rewrite -> unfold_traverse_to_check_balanced_t.
    rewrite -> H_bt1_h1.
    rewrite -> H_bt211_h211.
    
    assert (H_h1_h211_h212: h1 = max h211 h212).
    rewrite -> H_h_ret_h1 in H_h_ret_h21_h22.
    apply succ_eq in H_h_ret_h21_h22.
    apply succ_eq in H_h_ret_h21_h22.
    exact H_h_ret_h21_h22.

    assert (H_differ_by_one_h1_h211: differ_by_one h1 h211 = true).
    Check (rotate_left_differ_by_one_1).
    exact (rotate_left_differ_by_one_1 h1 h211 h212 H_h1_h211_h212
                                       C_diff_by_one_h211_h212).

    rewrite -> H_differ_by_one_h1_h211.
    rewrite -> unfold_traverse_to_check_balanced_hbt.
    rewrite -> unfold_traverse_to_check_balanced_bt_node.
    rewrite -> unfold_traverse_to_check_balanced_t.    
    rewrite -> H_bt212_h212.
    rewrite -> H_bt22_h22.

    assert (H_differ_by_one_h212_h22: differ_by_one h212 h22 = true).
    Check (rotate_left_differ_by_one_2).
    exact (rotate_left_differ_by_one_2
             h211 h212 h22 C_diff_by_one_h211_h212 C_h22_h21).

    rewrite -> H_differ_by_one_h212_h22.
    Check (rotate_left_differ_by_one_3).
    rewrite -> (rotate_left_differ_by_one_3
                  h1 h211 h212 h22
                  H_h1_h211_h212 C_h22_h21 C_diff_by_one_h211_h212).
    reflexivity.

    discriminate.

    discriminate.

    discriminate.

  - case ((h21 + 1 =n= h22) || (h21 =n= h22)) as [ | ]  eqn : C_h21_h22.
    rewrite -> some_x_equal_some_y in H3.
    rewrite <- H3.

    (* show that all subtrees are sound *)
    Check (triple_sound_implies_hbts_sound).
    destruct (triple_sound_implies_hbts_sound
                A h_ret (HNode A h21 bt21) e2 (HNode A h22 bt22) H2)
             as [H_bt21_sound H_bt22_sound].
    
    (* show that all the subtrees are balanced *)
    Check (triple_balanced_implies_hbts_balanced).
    destruct (triple_balanced_implies_hbts_balanced
                A h_ret (HNode A h21 bt21) e2 (HNode A h22 bt22) H0)
             as [H_bt21_balanced H_bt22_balanced].

    (* assert relations for traverse_to_check_balanced_hbt *)
    assert (H_bt21_h21:
              traverse_to_check_balanced_hbt A (HNode A h21 bt21) = Some h21).
    Check (balanced_implies_some_height).
    exact (balanced_implies_some_height A h21 bt21 H_bt21_sound H_bt21_balanced).    
    
    assert (H_bt22_h22:
              traverse_to_check_balanced_hbt A (HNode A h22 bt22) = Some h22).
    Check (balanced_implies_some_height).
    exact (balanced_implies_some_height A h22 bt22 H_bt22_sound H_bt22_balanced).    

    assert (H_bt1_h1: 
              traverse_to_check_balanced_hbt A (HNode A h1 bt1) = Some h1).
    Check (balanced_implies_some_height).
    exact (balanced_implies_some_height A h1 bt1 H1 H).    

    (* get required hypotheses *)
    assert (H_h_ret_h21_h22: h_ret = 1 + max h21 h22).
    Check (relate_heights).
    exact (relate_heights A h_ret h21 bt21 e2 h22 bt22 H2).

    unfold project_height_hbt in H4.
    unfold compare_int in H4.
    case ( h_ret <n 2 + h1) as [ | ].
    discriminate.
    case (h_ret =n= 2 + h1) as [ | ] eqn : C_h_ret_h1.
    apply beq_nat_true in C_h_ret_h1.
    
    (* with all the required hypotheses in place, unfold the goal *)
    unfold is_balanced_hbt.
    rewrite -> unfold_traverse_to_check_balanced_hbt.
    rewrite -> unfold_traverse_to_check_balanced_bt_node.
    rewrite -> unfold_traverse_to_check_balanced_t.
    rewrite -> unfold_traverse_to_check_balanced_hbt.
    rewrite -> unfold_traverse_to_check_balanced_bt_node.
    rewrite -> unfold_traverse_to_check_balanced_t.
    rewrite -> H_bt1_h1.
    rewrite -> H_bt21_h21.

    Check (rotate_left_differ_by_one_4).
    destruct (rotate_left_differ_by_one_4
                h1 h21 h22 h_ret C_h21_h22 H_h_ret_h21_h22 C_h_ret_h1)
      as [H_differ_by_one_h1_h21 H_differ_by_one_S_max_h1_h21_h211].

    rewrite -> H_differ_by_one_h1_h21.
    rewrite -> H_bt22_h22.
    rewrite -> H_differ_by_one_S_max_h1_h21_h211.
    reflexivity.

    discriminate.
    
    discriminate.
Qed.    


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

      case ((h_ret =n= project_height_hbt A hbt1) || (h_ret =n= 1 + project_height_hbt A hbt1))
        as [ | ] eqn : C_h_ret_h1.
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
          
          unfold is_balanced_hbt.
          rewrite -> unfold_traverse_to_check_balanced_hbt.
          rewrite -> unfold_traverse_to_check_balanced_bt_node.
          rewrite -> unfold_traverse_to_check_balanced_t.          
          Check (balanced_implies_some_height).
          rewrite ->  (balanced_implies_some_height A h_ret bt_ret
                                                    H_hbt_ret_is_sound
                                                    H_hbt_ret_is_balanced).
          induction hbt1 as [h1 bt1].
          induction hbt2 as [h2 bt2].
          rewrite ->  (balanced_implies_some_height A h2 bt2
                                                    H_hbt2_is_sound
                                                    H_hbt2_is_balanced).
          unfold project_height_hbt in C_height_diff.
          unfold project_height_hbt in C_h_ret_h1.

          unfold is_balanced_hbt in H_bal_t_init.
          rewrite -> unfold_traverse_to_check_balanced_hbt in H_bal_t_init.
          rewrite -> unfold_traverse_to_check_balanced_bt_node in H_bal_t_init.
          rewrite -> unfold_traverse_to_check_balanced_t in H_bal_t_init.
          rewrite ->  (balanced_implies_some_height A h1 bt1
                                                    H_hbt1_is_sound
                                                    H_hbt1_is_balanced) in H_bal_t_init.
          rewrite ->  (balanced_implies_some_height A h2 bt2
                                                    H_hbt2_is_sound
                                                    H_hbt2_is_balanced) in H_bal_t_init.
          case (differ_by_one h1 h2) as [ | ] eqn : C_diff_by_one_h1_h2.
          Check (left_insert_differ_by_one).
          rewrite -> (left_insert_differ_by_one
                        h1 h2 h_ret C_diff_by_one_h1_h2 C_h_ret_h1 C_height_diff).
          reflexivity.
          
          discriminate.

          (* Check (hbts_balanced_implies_triple_balanced_weak). *)
          (* assert (H_hbts_balanced_triple_balanced_with_da: *)
          (*           compare_int (project_height_hbt A (HNode A h_ret bt_ret)) *)
          (*                       (2 + project_height_hbt A hbt2) = Lt \/ *)
          (*           compare_int (project_height_hbt A hbt2) *)
          (*                       (2 + project_height_hbt A (HNode A h_ret bt_ret)) = Lt -> *)
          (*           is_balanced_hbt *)
          (*             A *)
          (*             (HNode A (1 + max h_ret (project_height_hbt A hbt2)) *)
          (*                    (Node A (Triple A (HNode A h_ret bt_ret) e hbt2))) = *)
          (*           true). *)
          (* exact (hbts_balanced_implies_triple_balanced_weak *)
          (*          A *)
          (*          (1 + max h_ret (project_height_hbt A hbt2)) *)
          (*          (HNode A h_ret bt_ret) *)
          (*          e *)
          (*          hbt2 *)
          (*          H_hbt_ret_is_balanced *)
          (*          H_hbt2_is_balanced *)
          (*          H_hbt_ret_is_sound *)
          (*          H_hbt2_is_sound).  *)
          (* destruct (or_implication *)
          (*             (compare_int *)
          (*                (project_height_hbt A (HNode A h_ret bt_ret)) *)
          (*                (2 + project_height_hbt A hbt2) = Lt) *)
          (*             (compare_int  *)
          (*                (project_height_hbt A hbt2) *)
          (*                (2 + project_height_hbt A (HNode A h_ret bt_ret)) = Lt) *)
          (*             (is_balanced_hbt *)
          (*                A *)
          (*                (HNode A (1 + max h_ret (project_height_hbt A hbt2)) *)
          (*                       (Node A (Triple A (HNode A h_ret bt_ret) e hbt2))) *)
          (*              = true) *)
          (*             H_hbts_balanced_triple_balanced_with_da) *)
          (*   as [H_we_need_12  H_we_need_21]. *)
          (* exact (H_we_need_12 C_height_diff). *)
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
                   H_hbt_ret_sound H_hbt2_is_sound H_insert_t C_height_diff).
        }

      * discriminate.

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

      case ((h_ret =n= project_height_hbt A hbt2) || (h_ret =n= 1 + project_height_hbt A hbt2))
        as [ | ] eqn : C_h_ret_h2.
      case (compare_int h_ret (2 + project_height_hbt A hbt1))
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

          (* destruct hbt1 and hbt2 *)
          induction hbt1 as [h1 bt1].
          induction hbt2 as [h2 bt2].

          unfold is_balanced_hbt.
          rewrite -> unfold_traverse_to_check_balanced_hbt.
          rewrite -> unfold_traverse_to_check_balanced_bt_node.
          rewrite -> unfold_traverse_to_check_balanced_t.          
          Check (balanced_implies_some_height).
          rewrite ->  (balanced_implies_some_height A h1 bt1
                                                    H_hbt1_is_sound
                                                    H_hbt1_is_balanced).
          rewrite ->  (balanced_implies_some_height A h_ret bt_ret
                                                    H_hbt_ret_is_sound
                                                    H_hbt_ret_is_balanced).
          unfold project_height_hbt in C_height_diff.
          unfold project_height_hbt in C_h_ret_h2.

          unfold is_balanced_hbt in H_bal_t_init.
          rewrite -> unfold_traverse_to_check_balanced_hbt in H_bal_t_init.
          rewrite -> unfold_traverse_to_check_balanced_bt_node in H_bal_t_init.
          rewrite -> unfold_traverse_to_check_balanced_t in H_bal_t_init.
          rewrite ->  (balanced_implies_some_height A h1 bt1
                                                    H_hbt1_is_sound
                                                    H_hbt1_is_balanced) in H_bal_t_init.
          rewrite ->  (balanced_implies_some_height A h2 bt2
                                                    H_hbt2_is_sound
                                                    H_hbt2_is_balanced) in H_bal_t_init.
          case (differ_by_one h1 h2) as [ | ] eqn : C_diff_by_one_h1_h2.

              
          Check (right_insert_differ_by_one).
          rewrite -> (right_insert_differ_by_one
                        h1 h2 h_ret C_diff_by_one_h1_h2 C_h_ret_h2 C_height_diff).
          reflexivity.

          discriminate.


          (* assert (H_hbts_balanced_triple_balanced_with_da:  *)
          (*           compare_int (project_height_hbt A hbt1) *)
          (*                       (2 + project_height_hbt A (HNode A h_ret bt_ret)) = Lt *)

          (*           \/ *)
          (*           compare_int (project_height_hbt A (HNode A h_ret bt_ret)) *)
          (*                       (2 + project_height_hbt A hbt1) = Lt *)
          (*           -> *)
          (*           is_balanced_hbt *)
          (*             A *)
          (*             (HNode A (1 + max (project_height_hbt A hbt2) h_ret) *)
          (*                    (Node A (Triple A hbt1 e (HNode A h_ret bt_ret)))) = *)
          (*           true).  *)
          (* Check (hbts_balanced_implies_triple_balanced_weak). *)
          (* exact (hbts_balanced_implies_triple_balanced_weak *)
          (*          A *)
          (*          (1 + max (project_height_hbt A hbt2) h_ret) *)
          (*          hbt1 *)
          (*          e *)
          (*          (HNode A h_ret bt_ret) *)
          (*          H_hbt1_is_balanced *)
          (*          H_hbt_ret_is_balanced *)
          (*          H_hbt1_is_sound *)
          (*          H_hbt_ret_is_sound). *)
          (* destruct (or_implication *)
          (*             (compare_int  *)
          (*                (project_height_hbt A hbt1) *)
          (*                (2 + project_height_hbt A (HNode A h_ret bt_ret)) = Lt) *)
          (*             (compare_int *)
          (*                (project_height_hbt A (HNode A h_ret bt_ret)) *)
          (*                (2 + project_height_hbt A hbt1) = Lt) *)
          (*             (is_balanced_hbt *)
          (*                A *)
          (*                (HNode A (1 + max (project_height_hbt A hbt1) h_ret) *)
          (*                       (Node A (Triple A hbt1 e (HNode A h_ret bt_ret)))) = true) *)
          (*             H_hbts_balanced_triple_balanced_with_da)  *)
          (*   as [H_we_need_12  H_we_need_21]. *)
          (* exact (H_we_need_21 C_height_diff). *)
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
                   H_hbt1_is_sound H_hbt_ret_sound H_insert_t C_height_diff).
          exact (rotate_left_preserves_balance
                   A hbt1 e h_ret bt_ret hbt'
                   H_hbt1_is_balanced H_hbt_ret_balanced
                   H_hbt1_is_sound H_hbt_ret_sound H_insert_t C_height_diff).
        }

      * discriminate.

      * discriminate.
        
      * discriminate.
Qed.

(* main lemma for deletion concerning soundness and balance *)
Lemma deletion_preserves_soundness_and_balance: 
  forall (A : Type)
         (compare : A -> A -> element_comparison)
         (x : A),
    (forall (hbt : heightened_binary_tree A)
            (hbt' : heightened_binary_tree A),
        is_sound_hbt A hbt = true ->
        is_balanced_hbt A hbt = true ->        
        delete_hbt_helper A compare x hbt = Some hbt' ->
        is_sound_hbt A hbt' = true /\ is_balanced_hbt A hbt' = true)
    /\
    (forall (bt : binary_tree A)
            (h_hbt : nat)
            (hbt' : heightened_binary_tree A),    
        is_sound_hbt A (HNode A h_hbt bt) = true ->
        is_balanced_hbt A (HNode A h_hbt bt) = true ->                
        delete_bt_helper A compare x h_hbt bt = Some hbt' ->
        is_sound_hbt A hbt' = true /\ is_balanced_hbt A hbt' = true)
    /\
    (forall (t : triple A)
            (h_hbt : nat)
            (hbt' : heightened_binary_tree A),    
        is_sound_hbt A (HNode A h_hbt (Node A t)) = true ->
        is_balanced_hbt A (HNode A h_hbt (Node A t)) = true ->                        
        delete_t_helper A compare x h_hbt t = Some hbt' ->
        is_sound_hbt A hbt' = true /\ is_balanced_hbt A hbt' = true).
Proof.
Admitted.

