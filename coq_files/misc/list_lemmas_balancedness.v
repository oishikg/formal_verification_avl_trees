(* Our strategy to check for in-orderedness will involve flattening trees into 
 * lists; we do so as follows: *)

(* Function to map a heightened_binary_tree into the in-order list of its elements *)
Fixpoint hbt_to_list (A : Type) (hbt : heightened_binary_tree A) : list A :=
    match hbt with
    | HNode _ bt =>
      bt_to_list A bt
    end
with bt_to_list (A : Type) (bt : binary_tree A) : list A :=
       match bt with
       | Leaf =>
         nil
       | Node t =>
         t_to_list A t
       end
with t_to_list (A : Type) (t : triple A) : list A :=
       match t with
       | Triple hbt1 e hbt2 =>
         (hbt_to_list A hbt1) ++ e :: (hbt_to_list A hbt2)
       end.

(* Unfold lemmas for hbt_to_list, bt_to_list, and t_to_list *)
Lemma unfold_hbt_to_list:
  forall (A : Type)
         (h : nat)
         (bt : binary_tree A),
    hbt_to_list A (HNode A h bt) = bt_to_list A bt.
Proof.      
  unfold_tactic hbt_to_list.
Qed.

Lemma unfold_bt_to_list_leaf:
  forall (A : Type),
    bt_to_list A (Leaf A) = nil.
Proof.
  unfold_tactic bt_to_list.
Qed.

Lemma unfold_bt_to_list_node:
  forall (A : Type)
         (t : triple A),
    bt_to_list A (Node A t) = t_to_list A t.
Proof.
  unfold_tactic bt_to_list.
Qed.

Lemma unfold_t_to_list:
  forall (A : Type)
         (hbt1 hbt2 : heightened_binary_tree A)
         (e : A),
    t_to_list A (Triple A hbt1 e hbt2) =
    (hbt_to_list A hbt1) ++ e :: (hbt_to_list A hbt2).
Proof.
  unfold_tactic t_to_list.
Qed.

(* Helper function to check if a list with at least one element is ordered *)
Fixpoint is_ordered_cons
         (A : Type) (e : A) (es' : list A) (compare : A -> A -> comparison) : bool :=
  match es' with
  | nil        =>
    true
  | e' :: es'' =>
    match compare e e' with
    | Lt =>
      is_ordered_cons A e' es'' compare
    | _  =>
      false
    end
  end.

(* Unfold lemmas for is_ordered_cons *)
Lemma unfold_is_ordered_cons_nil:
  forall (A : Type)
         (e : A)
         (compare : A -> A -> comparison),
    is_ordered_cons A e nil compare = true. 
Proof.
  unfold_tactic is_ordered_cons.
Qed.

Lemma unfold_is_ordered_cons_cons:
  forall (A : Type)
         (e e' : A)
         (es'' : list A)
         (compare : A -> A -> comparison),
    is_ordered_cons A e (e' :: es'') compare =
    match compare e e' with
    | Lt =>
      is_ordered_cons A e' es'' compare
    | _  =>
      false
    end.
Proof.      
  unfold_tactic is_ordered_cons.
Qed. 
    
(* Function to check if a list is ordered *)
Definition is_ordered_list (A : Type)
         (es : list A) (compare : A -> A -> comparison) :=
  match es with
  | nil      =>
    true
  | e :: es' =>
    is_ordered_cons A e es' compare
  end.
    
(* Unit tests for is_ordered_list *)
Definition test_is_ordered_list :=
  (is_ordered_list nat (0 :: 1 :: 2 :: 3 :: nil) compare_int =b= true)
    &&
    (is_ordered_list nat (1 :: 3 :: 5 :: 7 :: nil) compare_int =b= true)
    &&
    (is_ordered_list nat (3 :: 2 :: 17 :: 8 :: nil) compare_int =b= false)
    &&
    (is_ordered_list nat (1 :: 3 :: 5 :: 7 :: 6 :: nil) compare_int =b= false).

Compute (test_is_ordered_list).

(* Function to check whether heightened_binary_tree is in order *)
Definition is_ordered_hbt (A : Type)
           (hbt : heightened_binary_tree A)
           (compare : A -> A -> comparison) : bool :=
  is_ordered_list A (hbt_to_list A hbt) compare.
(* If a given list (x :: xs) is ordered, then so is the list xs *)
Lemma list_ordered_implies_reduced_list_ordered:
  forall (A : Type)
         (compare : A -> A -> comparison)         
         (x : A)
         (xs : list A),
    is_ordered_list A (x :: xs) compare = true ->
    is_ordered_list A xs compare = true.
Proof.
  intros A compare x xs H_xxs.
  unfold is_ordered_list in H_xxs.
  case xs as [ | x' xs''] eqn : C_xs.
  unfold is_ordered_list.
  reflexivity.

  rewrite -> (unfold_is_ordered_cons_cons A x x' xs'') in H_xxs.
  case (compare x x') as [ | | ] eqn : C_comp_x_x'.
  unfold is_ordered_list.
  exact H_xxs.
  discriminate.
  discriminate.
Qed.

(* If a list of the form (xs ++ e :: ys) is ordered, then so is the list 
 * (xs ++ ys) ordered *)
Lemma appended_lists_ordered_implies_middle_reduced_list_ordered:
  forall (A : Type)
         (compare : A -> A -> comparison)
         (xs : list A)
         (e : A)
         (ys : list A),
    is_ordered_list A (xs ++ e :: ys) compare = true ->
    is_ordered_list A (xs ++ ys) compare = true.
Proof.
  intros A compare xs e ys H_xyys.
  induction xs as [ | x xs' IH_xs'].

  - Search (nil ++ _ = _).
    rewrite -> (app_nil_l ys).
    rewrite -> (app_nil_l (e :: ys)) in H_xyys.
    exact (list_ordered_implies_reduced_list_ordered A compare e ys H_xyys).

  - rewrite <- (app_comm_cons xs' (e :: ys) x) in H_xyys.
    rewrite <- (app_comm_cons xs' ys x).

    assert (H_ordered_sublist : is_ordered_list A (xs' ++ e :: ys) compare = true).
    exact (list_ordered_implies_reduced_list_ordered
             A
             compare
             x
             (xs' ++ e :: ys)
             H_xyys).

    assert (IH_we_need : is_ordered_list A (xs' ++ ys) compare = true).
    exact (IH_xs' H_ordered_sublist).
    unfold is_ordered_list.
        
    case xs' as [ | x' xs''] eqn : C_xs'.

    + unfold is_ordered_list.
      rewrite -> (app_nil_l ys).
      unfold is_ordered_list in H_xyys.
      rewrite -> (app_nil_l (e :: ys)) in H_xyys.
      rewrite -> (app_nil_l ys) in IH_we_need.
      rewrite -> (unfold_is_ordered_cons_cons A x e ys compare) in H_xyys.
      case (compare x e) as [ | | ] eqn : C_comp_x_e.
      
      case ys as [ | y ys'] eqn : C_ys.
      exact (unfold_is_ordered_cons_nil A x compare).

      rewrite -> (app_nil_l (e :: y :: ys')) in H_ordered_sublist.
      unfold is_ordered_list in H_ordered_sublist.
      rewrite -> (unfold_is_ordered_cons_cons A e y ys' compare) in H_ordered_sublist.
      case (compare e y) as [ | | ] eqn : C_comp_e_y.

      assert (H_x_lt_y : compare x y = Lt).
      Check (transitivity_of_comparisons A x e y compare Lt C_comp_x_e C_comp_e_y).
      exact (transitivity_of_comparisons A x e y compare Lt C_comp_x_e C_comp_e_y).

      rewrite -> (unfold_is_ordered_cons_cons A x y  ys' compare).
      case (compare x y) as [ | | ] eqn : C_comp_x_y.
      unfold is_ordered_list in IH_we_need.
      exact IH_we_need.

      discriminate.
      
      discriminate.
      
      discriminate.
      
      discriminate.
      
      discriminate.
      
      discriminate.

    + rewrite <- (app_comm_cons xs'' ys x').
      rewrite <- (app_comm_cons xs'' ys x') in IH_we_need.
      rewrite <- (app_comm_cons xs'' (e :: ys) x') in H_ordered_sublist.
      unfold is_ordered_list in H_xyys.
      rewrite <- (app_comm_cons xs'' (e :: ys) x') in H_xyys.
      rewrite -> (unfold_is_ordered_cons_cons A x x' (xs'' ++ ys) compare).
      rewrite -> (unfold_is_ordered_cons_cons A x x' (xs'' ++ e :: ys) compare)
        in H_xyys.
      case (compare x x') as [ | | ] eqn : C_comp_x_x'.
      unfold is_ordered_list in IH_we_need.
      exact IH_we_need.

      discriminate.

      discriminate.
Qed.

(* A definition that aids in construction of the next lemma *)
Definition get_head_in_list (A : Type) (xs : list A) :=
  match xs with
  | nil =>
    nil
  | x :: _ =>
    (x :: nil)
  end.

(* Given a list (xs ++ ys) that is ordered, any element of xs concatenated to ys
 * should also give an ordered list. This idea is captured most easily by dealing 
 * with the head of the list *)
Lemma appended_lists_ordered_implies_left_reduced_list_ordered:   
  forall (A : Type)
         (compare : A -> A -> comparison)
         (xs ys : list A),
    is_ordered_list A (xs ++ ys) compare = true ->
    is_ordered_list A (get_head_in_list A xs ++ ys) compare = true.
Proof.
  intros A compare xs ys H_xy.
  induction xs as [ | x xs' IH_xs'].

  - rewrite -> (app_nil_l ys) in H_xy.
    unfold get_head_in_list.
    rewrite -> (app_nil_l ys).
    exact H_xy.

  - rewrite <- (app_comm_cons xs' ys x) in H_xy.

    assert (IH_we_need :
              is_ordered_list A (get_head_in_list A xs' ++ ys) compare = true).
    Check (list_ordered_implies_reduced_list_ordered).
    Check (list_ordered_implies_reduced_list_ordered
             A compare x (xs' ++ ys) H_xy).
    exact (IH_xs' (list_ordered_implies_reduced_list_ordered
             A compare x (xs' ++ ys) H_xy)).

    case xs' as [ | x' xs''] eqn : C_xs'.
    
    + unfold get_head_in_list.
      rewrite <- (app_comm_cons nil ys x).
      exact H_xy.

    + unfold get_head_in_list.
      unfold get_head_in_list in IH_xs'.
      rewrite <- (app_comm_cons nil ys x).
      rewrite -> (app_nil_l ys).
      unfold get_head_in_list in IH_we_need.
      rewrite <- (app_comm_cons nil ys x') in IH_we_need.
      rewrite -> (app_nil_l ys) in IH_we_need.
      
      rewrite <- (app_comm_cons xs'' ys x') in H_xy.
      unfold is_ordered_list in H_xy.
      rewrite -> (unfold_is_ordered_cons_cons
                    A x x' (xs'' ++ ys) compare) in H_xy.
      case (compare x x') as [ | | ] eqn : C_comp_x_x'.
      case ys as [ | y ys'] eqn : C_ys.
      
      * unfold is_ordered_list.
        rewrite -> (unfold_is_ordered_cons_nil).
        reflexivity.

      * unfold is_ordered_list in IH_we_need.
        rewrite -> (unfold_is_ordered_cons_cons A x' y ys' compare) in IH_we_need.
        case (compare x' y) as [ | | ] eqn : C_comp_x'_y.
        Check (transitivity_of_comparisons).
        Check (transitivity_of_comparisons A x x' y compare Lt
                                           C_comp_x_x' C_comp_x'_y).
        assert (H_x_lt_y : compare x y = Lt).
        exact (transitivity_of_comparisons A x x' y compare Lt
                                           C_comp_x_x' C_comp_x'_y).
        unfold is_ordered_list.
        rewrite -> (unfold_is_ordered_cons_cons A x y ys' compare).
        case (compare x y) as [ | | ] eqn : C_comp_x_y.

        exact IH_we_need.

        discriminate.

        discriminate.

        discriminate.

        discriminate.

      * discriminate.

      * discriminate.
Qed.

(* Finally, we arrive at our crucial lemma: if (xs ++ ys) is ordered, then both xs
 * and ys should also be ordered! *)
Lemma append_lists_ordered_implies_lists_ordered:
  forall (A : Type)
         (compare : A -> A -> comparison)
         (xs ys : list A),
    is_ordered_list A (xs ++ ys) compare = true ->
    (is_ordered_list A xs compare = true)
    /\
    (is_ordered_list A ys compare = true).
Proof.
  intros A compare xs ys H_xy.
  split.
  
  - induction xs as [ | x xs' IH_xs'].
    unfold is_ordered_list.
    reflexivity.

    Check (app_comm_cons).
    rewrite <- (app_comm_cons xs' ys x) in H_xy.
    
    assert (H_ordered_xs' : is_ordered_list A (xs' ++ ys) compare = true).
    exact (list_ordered_implies_reduced_list_ordered A compare x (xs' ++ ys) H_xy).

    assert (IH_we_need : is_ordered_list A xs' compare = true).
    exact (IH_xs' H_ordered_xs').
    
    unfold is_ordered_list.
    case xs' as [ | x' xs''] eqn : C_xs'.
    exact (unfold_is_ordered_cons_nil A x compare).

    unfold is_ordered_list in IH_we_need.
    rewrite -> (unfold_is_ordered_cons_cons A x x' xs'' compare).
    unfold is_ordered_list in H_xy.
    rewrite <- (app_comm_cons xs'' ys x') in H_xy.
    rewrite -> (unfold_is_ordered_cons_cons A x x' (xs'' ++ ys) compare) in H_xy.
    case (compare x x') as [ | | ] eqn : C_comp_x_x'.
    exact IH_we_need.

    discriminate.

    discriminate.
    
  - induction ys as [ | y ys' IH_ys']. 
    unfold is_ordered_list.
    reflexivity.

    assert (IH_we_need : is_ordered_list A ys' compare = true).
    Check (appended_lists_ordered_implies_middle_reduced_list_ordered
             A compare xs y ys' H_xy).
    exact (IH_ys' (appended_lists_ordered_implies_middle_reduced_list_ordered
             A compare xs y ys' H_xy)).

    unfold is_ordered_list. 
    case ys' as [ | y' ys''].

    rewrite -> (unfold_is_ordered_cons_nil A y compare).
    reflexivity.
    
    unfold is_ordered_list in IH_we_need.
    rewrite -> (unfold_is_ordered_cons_cons A y y' ys'' compare).
    Check (appended_lists_ordered_implies_left_reduced_list_ordered
             A compare xs (y :: y' :: ys'') H_xy).
    assert (H_xy_new :
              is_ordered_list A (get_head_in_list A xs ++ y :: y' :: ys'') compare
              = true).
    exact (appended_lists_ordered_implies_left_reduced_list_ordered
             A compare xs (y :: y' :: ys'') H_xy).
    case xs as [ | x' xs''] eqn : C_xs.
    
    + unfold get_head_in_list in H_xy_new.
      rewrite -> (app_nil_l (y :: y' :: ys'')) in H_xy_new.
      unfold is_ordered_list in H_xy_new.
      rewrite -> (unfold_is_ordered_cons_cons A y y' ys'' compare) in H_xy_new.
      case (compare y y') as [ | | ] eqn : C_comp_y_y'.

      exact H_xy_new.

      discriminate.

      discriminate.

    + unfold get_head_in_list in H_xy_new.
      rewrite <- (app_comm_cons nil (y :: y' :: ys'') x') in H_xy_new.
      rewrite -> (app_nil_l (y :: y' :: ys'')) in H_xy_new.
      unfold is_ordered_list in H_xy_new.
      rewrite -> (unfold_is_ordered_cons_cons A x' y (y' :: ys'') compare)
        in H_xy_new.
      case (compare x' y) as [ | | ] eqn : C_comp_x'_y. 
      rewrite -> (unfold_is_ordered_cons_cons A y y' ys'' compare)
        in H_xy_new.
      case (compare y y') as [ | | ] eqn : C_comp_y_y'.

      exact IH_we_need.

      discriminate.

      discriminate.

      discriminate.

      discriminate.
Qed.

(* If a triple is ordered, then the hbts in it should also be ordered *)
Lemma triple_ordered_implies_hbts_ordered:
  forall (A : Type)
         (compare : A -> A -> comparison)
         (h_hbt : nat)
         (hbt1 : heightened_binary_tree A)
         (e : A)
         (hbt2 : heightened_binary_tree A),
    is_ordered_hbt A (HNode A h_hbt (Node A (Triple A hbt1 e hbt2))) compare = true ->
    is_ordered_hbt A hbt1 compare = true /\ is_ordered_hbt A hbt2 compare = true.
Proof.
  intros A compare h_hbt hbt1 e hbt2 H_ordered_hbt.
  unfold is_ordered_hbt in H_ordered_hbt.
  rewrite -> (unfold_hbt_to_list A h_hbt (Node A (Triple A hbt1 e hbt2)))
    in H_ordered_hbt.
  rewrite -> (unfold_bt_to_list_node A (Triple A hbt1 e hbt2))
    in H_ordered_hbt.
  rewrite -> (unfold_t_to_list A hbt1 hbt2 e) in H_ordered_hbt.
  destruct (append_lists_ordered_implies_lists_ordered
              A
              compare
              (hbt_to_list A hbt1)
              (e :: hbt_to_list A hbt2)
              H_ordered_hbt) as [H_hbt1_list_ord H_e_hbt2_list_ord].
  assert (H_hbt2_list_ord :
            is_ordered_list A (hbt_to_list A hbt2) compare = true).
  exact (list_ordered_implies_reduced_list_ordered
           A compare e (hbt_to_list A hbt2) H_e_hbt2_list_ord).
  split.

  - unfold is_ordered_hbt.
    exact H_hbt1_list_ord.

  - unfold is_ordered_hbt.
    exact H_hbt2_list_ord.
Qed.

(* Function to check if a given element is Lt every element in a list *)
Fixpoint e_lt_list
         (A : Type)
         (compare : A -> A -> comparison)
         (e : A)
         (xs : list A) : bool :=
  match xs with
  | nil =>
    true
  | x :: xs' =>
    match compare e x with
    | Lt =>
      e_lt_list A compare e xs'
    | _ =>
      false
    end
  end.

(* Unfold lemmas for e_lt_list *)
Lemma unfold_e_lt_list_nil:
  forall (A : Type)
         (compare : A -> A -> comparison)
         (e : A),
    e_lt_list A compare e nil = true.
Proof.
  unfold_tactic e_lt_list.
Qed.

Lemma unfold_e_lt_list_cons:
    forall (A : Type)
           (compare : A -> A -> comparison)
           (e x : A)
           (xs' : list A),
      e_lt_list A compare e (x :: xs') =
      match compare e x with
      | Lt =>
        e_lt_list A compare e xs'
      | _ =>
        false
      end.
Proof.
  unfold_tactic e_lt_list.
Qed.


(* Function to check if every element in a list is Lt a given element in a list *)
Fixpoint list_lt_e
         (A : Type)
         (compare : A -> A -> comparison)
         (xs : list A)
         (e : A) : bool :=
  match xs with
  | nil =>
    true
  | x :: xs' =>
    match compare x e with
    | Lt =>
      list_lt_e A compare xs' e
    | _ =>
      false
    end
  end.

(* Unfold lemmas for list_lt_e *)
Lemma unfold_list_lt_e_nil:
  forall (A : Type)
         (compare : A -> A -> comparison)
         (e : A),
    list_lt_e A compare nil e = true.
Proof.
  unfold_tactic list_lt_e.
Qed.

Lemma unfold_list_lt_e_cons:
    forall (A : Type)
           (compare : A -> A -> comparison)
           (x : A)
           (xs' : list A)
           (e : A),
      list_lt_e A compare (x :: xs') e =
      match compare x e with
      | Lt =>
        list_lt_e A compare xs' e
      | _ =>
        false
      end.
Proof.
  unfold_tactic list_lt_e.
Qed.

(* The most important lemma: provides the condition for which two ordered lists
 * xs, ys, when appended, are also ordered *) 
Lemma lists_ordered_implies_append_lists_ordered_weak:
  forall (A : Type)
         (compare : A -> A -> comparison)
         (xs ys : list A)
         (e : A),
    is_ordered_list A xs compare = true ->
    is_ordered_list A (e :: ys) compare = true ->
    list_lt_e A compare xs e = true ->
    is_ordered_list A (xs ++ e :: ys) compare = true.
Proof.
  intros A compare xs ys e H_xs H_e_ys H_list_e.
  induction xs as [ | x xs' IH_xs'].

  - Search (nil ++ _ = _).
    rewrite -> (app_nil_l (e :: ys)).
    exact H_e_ys.

  - assert (H_ord_xs' : is_ordered_list A xs' compare = true).
    exact (list_ordered_implies_reduced_list_ordered A compare x xs' H_xs).
    
    assert (IH_we_need : is_ordered_list A (xs' ++ e :: ys) compare = true).
    rewrite -> (unfold_list_lt_e_cons A compare x xs' e) in H_list_e.
    case (compare x e) as [ | | ] eqn : C_comp_x_e.
    exact (IH_xs' H_ord_xs' H_list_e).
    discriminate.
    discriminate.

    rewrite <- (app_comm_cons xs' (e :: ys) x).
    unfold is_ordered_list.
    case xs' as [ | x' xs''] eqn : C_xs'.
    rewrite -> (app_nil_l (e :: ys)).
    rewrite -> (unfold_is_ordered_cons_cons A x e ys compare).
    rewrite -> (unfold_list_lt_e_cons A compare x nil e) in H_list_e.
    case (compare x e) as [ | | ] eqn : C_comp_x_e.
    unfold is_ordered_list in H_e_ys.
    exact H_e_ys.
    discriminate.
    discriminate.

    rewrite <- (app_comm_cons xs'' (e :: ys) x').
    rewrite <- (app_comm_cons xs'' (e :: ys) x') in IH_we_need.
    unfold is_ordered_list in IH_we_need.
    rewrite -> (unfold_is_ordered_cons_cons A x x' (xs'' ++ e :: ys) compare).

    assert (H_x_lt_x' : compare x x' = Lt).
    unfold is_ordered_list in H_xs.
    rewrite -> (unfold_is_ordered_cons_cons A x x' xs'' compare) in H_xs.
    case (compare x x') as [ | | ] eqn : C_comp_x_x'.
    reflexivity.
    discriminate.
    discriminate.

    rewrite -> H_x_lt_x'.
    exact IH_we_need.
Qed.
