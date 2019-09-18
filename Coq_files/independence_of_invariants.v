(* ***** Section 3.4.1: Independence of soundness and balancedness ***** *)

Definition hbt_sound_but_unbalanced
           (A : Type) (a : A) : heightened_binary_tree A :=
  HNode A 3 (Node A (Triple A
                   (HNode A 0 (Leaf A))
                   a
                   (HNode A 2 (Node A (Triple A
                                     (HNode A 0 (Leaf A))
                                     a
                                     (HNode A 1 (Node A (Triple A
                                                       (HNode A 0 (Leaf A))
                                                       a
                                                       (HNode A 0 (Leaf A)))))))))).

Definition hbt_unsound_but_balanced
           (A : Type) (a : A) : heightened_binary_tree A :=
  HNode A 3 (Leaf A).

Proposition independence_of_soundness_and_balancedness_hbt: 
  forall (A : Type)
         (a : A),
    (exists hbt : heightened_binary_tree A,
        (is_sound_hbt A hbt = true) /\ (is_balanced_hbt A hbt = false))
    /\
    (exists hbt : heightened_binary_tree A,
        (is_sound_hbt A hbt = false) /\ (is_balanced_hbt A hbt = true)). 
Proof. 
  intros A a. 
  split.

  (* ***** Existence of hbt that is sound but not balanced ***** *)
  - exists (hbt_sound_but_unbalanced A a).
    split.
  (* Show that the counter example is sound *) 
    unfold is_sound_hbt.
    unfold hbt_sound_but_unbalanced.
    (* Unfold traverse_to_check_soundness_bt and apply to the counter-example *) 
 (*    Check (unfold_traverse_to_check_soundness_bt_node *)
(*              A 0 2 a (Leaf A) *)
(*              (Node A *)
(*                    (Triple A (HNode A 0 (Leaf A)) a *)
(*                            (HNode A 1 *)
(*                                   (Node A (Triple A *)
(*                                                   (HNode A 0 (Leaf A)) *)
(*                                                   a *)
(*                                                   (HNode A 0 (Leaf A)))))))). *)
(*     rewrite -> *)
(*             (unfold_traverse_to_check_soundness_bt_node *)
(*                A 0 2 a (Leaf A) *)
(*                (Node A *)
(*                      (Triple A (HNode A 0 (Leaf A)) a *)
(*                              (HNode A 1 *)
(*                                     (Node A (Triple A *)
(*                                                     (HNode A 0 (Leaf A)) *)
(*                                                     a *)
(*                                                     (HNode A 0 (Leaf A)))))))). *)
(*     rewrite -> (unfold_traverse_to_check_soundness_bt_leaf A). *)
(*     unfold beq_nat at 1. *)
(*     rewrite -> *)
(*             (unfold_traverse_to_check_soundness_bt_node *)
(*                A 0 1 a (Leaf A) (Node A (Triple A *)
(*                                                 (HNode A 0 (Leaf A)) *)
(*                                                 a *)
(*                                                 (HNode A 0 (Leaf A))))). *)
(*     rewrite -> (unfold_traverse_to_check_soundness_bt_leaf A). *)
(*     unfold beq_nat at 1. *)
(*     rewrite -> *)
(*             (unfold_traverse_to_check_soundness_bt_node *)
(*                A 0 0 a (Leaf A) (Leaf A)). *)
(*     rewrite -> (unfold_traverse_to_check_soundness_bt_leaf A). *)
(*     (* Now unfold functions in order of computation *) *)
(*     unfold beq_nat at 1. *)
(*     unfold beq_nat at 1. *)
(*     unfold max at 1. *)
(*     Search (_ + 0 = _ ). *)
(*     Check (plus_0_r 1). *)
(*     rewrite -> (plus_0_r 1). *)
(*     unfold beq_nat at 1. *)
(*     unfold max at 1. *)
(*     Search (_ + _ = _). *)
(*     Check (plus_Sn_m 0 1). *)
(*     rewrite -> (plus_Sn_m 0 1). *)
(*     rewrite -> (plus_0_l 1). *)
(*     unfold beq_nat at 1. *)
(*     unfold max. *)
(*     rewrite -> (plus_Sn_m 0 2). *)
(*     rewrite -> (plus_0_l 2). *)
(*     unfold beq_nat. *)
(*     reflexivity. *)

(*     (* Show that the counter-example is unbalanced *) *)
(*     unfold is_balanced_hbt. *)
(*     unfold hbt_sound_but_unbalanced. *)
(*     (* Unfold traverse_to_check_balanced_bt and apply to the counter-example *)  *)
(*     Check (unfold_traverse_to_check_balanced_bt_node *)
(*              A 0 2 a (Leaf A) *)
(*              (Node A *)
(*                    (Triple A (HNode A 0 (Leaf A)) a *)
(*                            (HNode A 1 *)
(*                                   (Node A (Triple A *)
(*                                                   (HNode A 0 (Leaf A)) *)
(*                                                   a *)
(*                                                   (HNode A 0 (Leaf A)))))))). *)
(*     rewrite -> *)
(*             (unfold_traverse_to_check_balanced_bt_node *)
(*                A 0 2 a (Leaf A) *)
(*                (Node A *)
(*                      (Triple A (HNode A 0 (Leaf A)) a *)
(*                              (HNode A 1 *)
(*                                     (Node A (Triple A *)
(*                                                     (HNode A 0 (Leaf A)) *)
(*                                                     a *)
(*                                                     (HNode A 0 (Leaf A)))))))). *)
(*     rewrite -> (unfold_traverse_to_check_balanced_bt_leaf A). *)
(*     rewrite -> *)
(*             (unfold_traverse_to_check_balanced_bt_node *)
(*                A 0 1 a (Leaf A) (Node A (Triple A *)
(*                                                 (HNode A 0 (Leaf A)) *)
(*                                                 a *)
(*                                                 (HNode A 0 (Leaf A))))). *)
(*     rewrite -> (unfold_traverse_to_check_balanced_bt_leaf A). *)
(*     rewrite -> *)
(*             (unfold_traverse_to_check_balanced_bt_node *)
(*                A 0 0 a (Leaf A) (Leaf A)). *)
(*     rewrite -> (unfold_traverse_to_check_balanced_bt_leaf A). *)
(*     (* Now unfold all remaining functions in order of computation *) *)
(*     unfold differ_by_one at 1. *)
(*     Search (0 + _ = _). *)
(*     rewrite -> (plus_O_n 1). *)
(*     unfold beq_nat at 1 2 3. *)
(*     unfold orb at 1 2. *)
(*     unfold max. *)
(*     Search (_ + 0 = _). *)
(*     rewrite -> (plus_0_r 1). *)
(*     unfold differ_by_one at 1. *)
(*     rewrite -> (plus_Sn_m 0 1). *)
(*     rewrite -> (plus_0_l 1). *)
(*     unfold beq_nat at 1 2 3. *)
(*     unfold orb at 1 2. *)
(*     unfold differ_by_one. *)
(*     rewrite -> (plus_Sn_m 1 1). *)
(*     rewrite -> (plus_Sn_m 0 1). *)
(*     rewrite -> (plus_0_l 1). *)
(*     unfold beq_nat at 1 2 3. *)
(*     unfold orb at 1 2. *)
(*     reflexivity.  *)

(*   (* ***** Existence of hbt that is unsound but balanced ***** *) *)
(*   - exists (hbt_unsound_but_balanced A a). *)

(*     split. *)
(*     (* Show that the counter-example is unsound *) *)
(*     unfold hbt_unsound_but_balanced. *)
(*     unfold is_sound_hbt. *)
(*     rewrite -> (unfold_traverse_to_check_soundness_bt_leaf A). *)
(*     unfold beq_nat. *)
(*     reflexivity. *)

(*     (* Show that the counter-example is balanced *) *)
(*     unfold hbt_unsound_but_balanced. *)
(*     unfold is_balanced_hbt. *)
(*     rewrite -> (unfold_traverse_to_check_balanced_bt_leaf A).  *)
(*     reflexivity. *)
    (* Qed. *)
Abort.    

(* ***** Section 3.4.2: Independence of soundness and orderedness  ***** *)

(* First attempt at a definition of a total order *)
(* Definition total_order *)
(*            (A : Type) *)
(*            (x y : A) *)
(*            (f : A -> A -> comparison) : Prop := *)
(*     (f x y = Lt) *)
(*     \/ *)
(*     (f x y = Eq) *)
(*     \/ *)
(*     (f x y = Gt). *)

(* Unforunately, this will not work because there is no transitivity requirement *)

(* Another attempt at defining a total order *)
Definition ordered
           (A : Type)
           (f : A -> A -> comparison) : Prop :=
  forall (x y z: A)
         (c : comparison), 
    ((f x y = Lt)
     \/
     (f x y = Eq)
     \/
     (f x y = Gt))
    /\
    ((f x y = c) /\ (f y z = c) -> (f x z = c)).

Definition Lt_implies
           (A : Type)
           (x y : A)
           (f : A -> A -> comparison) : Prop :=
  f x y = Lt -> (f y x = Gt) \/ (f y x = Eq).

Definition hbt_sound_but_unordered
           (A : Type) (a1 a2 : A) : heightened_binary_tree A :=
  HNode A 2 (Node A (Triple A
                            (HNode A 0 (Leaf A))
                            a2
                            (HNode A 1 (Node A (Triple A
                                                       (HNode A 0 (Leaf A))
                                                       a1
                                                       (HNode A 0 (Leaf A))))))).

Definition hbt_unsound_but_ordered (A : Type) : heightened_binary_tree A :=
  HNode A 1 (Leaf A).


(* note that this proposition will actually be a lemma in the final proof *) 
Proposition independence_of_soundness_and_orderedness_hbt:
  forall (A : Type),
    (exists (f : A -> A -> comparison)
            (a1 a2 : A),
            f a2 a1 = Gt) -> 
    (exists (hbt : heightened_binary_tree A)
            (cmp : A -> A -> comparison),
        (is_sound_hbt A hbt = true) /\ (is_ordered_hbt A hbt cmp = false))
    /\
    (exists (hbt : heightened_binary_tree A)
            (cmp : A -> A -> comparison),
        (is_sound_hbt A hbt = false) /\ (is_ordered_hbt A hbt cmp = true)). 
Proof.
  intros A [f [a1 [a2 H_f]]].
  split.

  (* ***** Existence of hbt that is sound but unordered ***** *)
  - exists (hbt_sound_but_unordered A a1 a2).
    exists f.
    split.

    (* Show that counter-example is sound *)
    unfold hbt_sound_but_unordered.
    unfold is_sound_hbt.
(*     rewrite -> *)
(*             (unfold_traverse_to_check_soundness_bt_node *)
(*                A 0 1 a2 *)
(*                (Leaf A) *)
(*                (Node A (Triple A (HNode A 0 (Leaf A)) a1 (HNode A 0 (Leaf A))))). *)
(*     rewrite -> (unfold_traverse_to_check_soundness_bt_leaf A). *)
(*     unfold beq_nat at 1. *)
(*     rewrite -> *)
(*             (unfold_traverse_to_check_soundness_bt_node *)
(*                A 0 0 a1 *)
(*                (Leaf A) *)
(*                (Leaf A)). *)
(*     rewrite -> (unfold_traverse_to_check_soundness_bt_leaf A). *)
(*     unfold beq_nat at 1. *)
(*     unfold beq_nat at 1. *)
(*     unfold max at 1. *)
(*     Search (_ + 0 = _). *)
(*     rewrite -> (plus_0_r 1). *)
(*     unfold beq_nat at 1. *)
(*     unfold max. *)
(*     rewrite -> (plus_Sn_m 0 1). *)
(*     rewrite -> (plus_0_l 1). *)
(*     unfold beq_nat. *)
(*     reflexivity.  *)

(*     (* Show that counter-example is unordered *) *)
(*     unfold hbt_sound_but_unordered. *)
(*     unfold is_ordered_hbt. *)
(*     unfold is_ordered_list. *)
(*     unfold hbt_to_list. *)
(*     (* Flatten the heightened_binary_tree first *) *)
(*     rewrite -> *)
(*             (unfold_flatten_binary_tree_node *)
(*                A *)
(*                (Leaf A) *)
(*                (Node A (Triple A (HNode A 0 (Leaf A)) a1 (HNode A 0 (Leaf A)))) *)
(*                0 1 *)
(*                a2 *)
(*                nil). *)
(*     rewrite -> *)
(*             (unfold_flatten_binary_tree_leaf *)
(*                A *)
(*                (a2 *)
(*                   :: flatten_binary_tree A *)
(*                   (Node A (Triple A (HNode A 0 *)
(*                                            (Leaf A)) *)
(*                                   a1 *)
(*                                   (HNode A 0 (Leaf A)))) nil)). *)
(*     rewrite -> *)
(*             (unfold_flatten_binary_tree_node *)
(*                A *)
(*                (Leaf A) (Leaf A) *)
(*                0 0 *)
(*                a1 *)
(*                nil). *)
(*     rewrite -> *)
(*             (unfold_flatten_binary_tree_leaf *)
(*                A *)
(*                (a1 :: flatten_binary_tree A (Leaf A) nil)). *)
(*     rewrite -> *)
(*             (unfold_flatten_binary_tree_leaf *)
(*                A *)
(*                nil). *)
(*     rewrite -> *)
(*             (unfold_is_ordered_cons_cons *)
(*                A a2 a1 *)
(*                nil *)
(*                f). *)
(*     rewrite -> H_f. *)
(*     reflexivity. *)

(*   (* ***** Existence of hbt that is unsound but ordered ***** *) *)
(*   - exists (hbt_unsound_but_ordered A). *)
(*     exists f. *)
(*     split. *)

(*     (* Show that counter-example is unsound *) *)
(*     unfold hbt_unsound_but_ordered. *)
(*     unfold is_sound_hbt. *)
(*     rewrite -> (unfold_traverse_to_check_soundness_bt_leaf A). *)
(*     unfold beq_nat.  *)
(*     reflexivity. *)

(*     (* Show that counter-example is ordered *) *)
(*     unfold hbt_unsound_but_ordered. *)
(*     unfold is_ordered_hbt. *)
(*     unfold is_ordered_list. *)
(*     unfold hbt_to_list. *)
(*     rewrite -> (unfold_flatten_binary_tree_leaf A nil). *)
(*     reflexivity. *)
    (* Qed. *)
Abort.


(* ***** *)

(* ***** Section 3.4.3: Independence of balancedness and orderedness  ***** *)

(* Tackle this section after clarifying with professor Danvy if the notion of an 
 * ordering has been correctly captured *) 

(* ***** *)

