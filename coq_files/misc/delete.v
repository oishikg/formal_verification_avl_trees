x(* ********** 6: Deletion operation on AVL trees ********** *)

(* ***** Factoring rightmost and leftmost elements in a tree ***** *) 

(* Unit tests for factor rightmost *)

Definition t_0 := Triple nat
                         (HNode nat 0 (Leaf nat))
                         10
                         (HNode nat 0 (Leaf nat)).

Definition fr_0 := Some ((HNode nat 0 (Leaf nat)), 10).

Definition t_1 :=
  Triple nat
         (HNode nat 0 (Leaf nat))
         10
         (HNode nat 1
                (Node nat
                      (Triple nat
                              (HNode nat 0 (Leaf nat))
                              20
                              (HNode nat 0 (Leaf nat))))).

Definition fr_1 :=
  Some ((HNode nat 1
               (Node nat
                     (Triple nat
                             (HNode nat 0 (Leaf nat))
                             10
                             (HNode nat 0 (Leaf nat)))))
        , 20).
  
Definition t_2 :=
  Triple nat
         (HNode nat 2
                (Node nat
                      (Triple nat
                              (HNode nat 0 (Leaf nat))
                              5
                              (HNode nat 1
                                     (Node nat
                                           (Triple nat
                                                   (HNode nat 0 (Leaf nat))
                                                   6
                                                   (HNode nat 0 (Leaf nat))))))))
         10
         (HNode nat 1
                (Node nat
                      (Triple nat
                              (HNode nat 0 (Leaf nat))
                              20
                              (HNode nat 0 (Leaf nat))))).

Definition fr_2 :=
  Some ((HNode nat 2
               (Node nat
                     (Triple nat
                             (HNode nat 1
                                    (Node nat
                                          (Triple nat
                                                  (HNode nat 0 (Leaf nat))
                                                  5
                                                  (HNode nat 0 (Leaf nat)))))
                             6
                             (HNode nat 1
                                    (Node nat
                                          (Triple nat
                                                  (HNode nat 0 (Leaf nat))
                                                  10
                                                  (HNode nat 0 (Leaf nat))))))))
        ,
        20).

Definition equal_pairs_factoring p1 p2 :=
  match p1 with
  | Some (hbt_ret, el) =>
    match p2 with
    | Some (hbt_ret_exp, el_exp) =>
      if ((equal_hbt nat compare_int hbt_ret hbt_ret_exp) && (el =n= el_exp))
      then true
      else false
    | _ => false
    end
  | _ =>
    false
  end.

Definition test_factor_rightmost_t
           (candidate : (forall A' : Type,
                            triple A' -> option (heightened_binary_tree A' * A'))) :=
  let b0 := equal_pairs_factoring (candidate nat t_0) (fr_0) in
  let b1 := equal_pairs_factoring (candidate nat t_1) (fr_1) in
  let b2 := equal_pairs_factoring (candidate nat t_2) (fr_2) in
  (b0 && b1 && b2). 

Fixpoint factor_rightmost_t (A : Type) (t : triple A) :=
  match t with
  | Triple hbt1 e hbt2 =>
    factor_rightmost_hbt A hbt1 e hbt2
  end
with factor_rightmost_hbt (A : Type)
                          (hbt1 : heightened_binary_tree A)
                          (e : A)
                          (hbt2 : heightened_binary_tree A) :=
       match hbt2 with
       | HNode h2 bt2 =>
         factor_rightmost_bt A hbt1 e bt2
       end
with factor_rightmost_bt (A : Type)
                         (hbt1 : heightened_binary_tree A)                         
                         (e : A)
                         (bt2 : binary_tree A) :=
       match bt2 with
       | Leaf => 
         Some (HNode A (project_height_hbt A hbt1) (project_bt_hbt A hbt1), e)
       | Node t2 => 
         match factor_rightmost_t A t2 with
         | Some (HNode h2' bt2', e') =>
           match compare_int (project_height_hbt A hbt1) (2 + h2') with
           | Lt =>
             Some ((HNode A
                          (1 + max (project_height_hbt A hbt1) h2')
                          (Node A
                                (Triple A
                                        (HNode A (project_height_hbt A hbt1) (project_bt_hbt A hbt1))
                                        e
                                        (HNode A h2' bt2'))))
                   , e') 
           | Eq =>
             match (rotate_right_hbt A (HNode A (project_height_hbt A hbt1) (project_bt_hbt A hbt1)) e (HNode A h2' bt2')) with
             | Some new_hbt =>
               Some (new_hbt, e')
             | None =>
               None
             end
           | Gt =>
             None
           end
         | None =>
           None
         end
       end.

Compute (test_factor_rightmost_t factor_rightmost_t).

Lemma unfold_factor_rightmost_t:
  forall (A : Type)
         (hbt1 : heightened_binary_tree A)
         (e : A)
         (hbt2 : heightened_binary_tree A),
    factor_rightmost_t A (Triple A hbt1 e hbt2) =
    factor_rightmost_hbt A hbt1 e hbt2.
Proof.
  unfold_tactic factor_rightmost_t.
Qed.

Lemma unfold_factor_rightmost_hbt:
  forall (A : Type)
         (hbt1 : heightened_binary_tree A)
         (e : A)
         (h2 : nat)
         (bt2 : binary_tree A),
    factor_rightmost_hbt A hbt1 e (HNode A h2 bt2) =
    factor_rightmost_bt A hbt1 e bt2.
Proof.
  unfold_tactic factor_rightmost_hbt.
Qed.

Lemma unfold_factor_rightmost_bt_leaf:
  forall (A : Type)
         (hbt1 : heightened_binary_tree A)
         (e : A),
    factor_rightmost_bt A hbt1 e (Leaf A) =
    Some (HNode A (project_height_hbt A hbt1) (project_bt_hbt A hbt1), e).
Proof.
  unfold_tactic factor_rightmost_bt.
Qed.

Lemma unfold_factor_rightmost_bt_node:
  forall (A : Type)
         (hbt1 : heightened_binary_tree A)
         (e : A)
         (t2 : triple A),
    factor_rightmost_bt A hbt1 e (Node A t2) =
    match factor_rightmost_t A t2 with
    | Some (HNode h2' bt2', e') =>
      match compare_int (project_height_hbt A hbt1) (2 + h2') with
      | Lt =>
        Some ((HNode A
                     (1 + max (project_height_hbt A hbt1) h2')
                     (Node A
                           (Triple A
                                   (HNode A (project_height_hbt A hbt1) (project_bt_hbt A hbt1))
                                   e
                                   (HNode A h2' bt2'))))
              , e') 
      | Eq =>
        match (rotate_right_hbt A (HNode A (project_height_hbt A hbt1) (project_bt_hbt A hbt1)) e (HNode A h2' bt2')) with
        | Some new_hbt =>
          Some (new_hbt, e')
        | None =>
          None
        end
      | Gt =>
        None
      end
    | None =>
      None
    end.
Proof.
  unfold_tactic factor_rightmost_bt.
Qed.

(* Unit tests for factor left most *)

(* use t0 *)

Definition t_3 :=
  Triple nat
         (HNode nat 1
                (Node nat
                      (Triple nat
                              (HNode nat 0 (Leaf nat))
                              8
                              (HNode nat 0 (Leaf nat)))))
         10 
         (HNode nat 0 (Leaf nat))
         .

Definition fr_3 :=
  Some ((HNode nat 1
               (Node nat
                     (Triple nat
                             (HNode nat 0 (Leaf nat))
                             10
                             (HNode nat 0 (Leaf nat)))))
        , 8).

Definition t_4 :=
  Triple nat
         (HNode nat 1
                (Node nat
                      (Triple nat
                              (HNode nat 0 (Leaf nat))
                              2
                              (HNode nat 0 (Leaf nat)))))
         10
         (HNode nat 2
                (Node nat
                      (Triple nat
                              (HNode nat 1
                                     (Node nat
                                           (Triple nat
                                                   (HNode nat 0 (Leaf nat))
                                                   12
                                                   (HNode nat 0 (Leaf nat)))))
                              15
                              (HNode nat 0 (Leaf nat))
                              ))).


Definition fr_4 :=
  Some ((HNode nat 2
               (Node nat
                     (Triple nat
                             (HNode nat 1
                                    (Node nat
                                          (Triple nat
                                                  (HNode nat 0 (Leaf nat))
                                                  10
                                                  (HNode nat 0 (Leaf nat)))))
                             12
                             (HNode nat 1
                                    (Node nat
                                          (Triple nat
                                                  (HNode nat 0 (Leaf nat))
                                                  15
                                                  (HNode nat 0 (Leaf nat))))))))
        ,
        2).

Definition test_factor_leftmost_t
           (candidate : (forall A' : Type,
                            triple A' -> option (heightened_binary_tree A' * A'))) :=
  let b0 := equal_pairs_factoring (candidate nat t_0) (fr_0) in
  let b3 := equal_pairs_factoring (candidate nat t_3) (fr_3) in
  let b4 := equal_pairs_factoring (candidate nat t_4) (fr_4) in
  (b0 && b3 && b4). 


(* Implementation of factor left most *)
Fixpoint factor_leftmost_t (A : Type) (t : triple A) :=
  match t with
  | Triple hbt1 e hbt2 =>
    factor_leftmost_hbt A hbt1 e hbt2
  end
with factor_leftmost_hbt (A : Type)
                         (hbt1 : heightened_binary_tree A)
                         (e : A)
                         (hbt2 : heightened_binary_tree A) :=
       match hbt1 with
       | HNode h1 bt1 =>
         factor_leftmost_bt A bt1 e hbt2
       end
with factor_leftmost_bt (A : Type)
                        (bt1 : binary_tree A)
                        (e : A)
                        (hbt2 : heightened_binary_tree A) :=
       match bt1 with
       | Leaf =>
         Some (HNode A (project_height_hbt A hbt2) (project_bt_hbt A hbt2), e)
       | Node t1 =>
         match factor_leftmost_t A t1 with
         | Some ((HNode h1' bt1'), e') =>
           match compare_int (project_height_hbt A hbt2) (2 + h1') with
           | Lt =>
             Some ((HNode A
                          (1 + max h1' (project_height_hbt A hbt2))
                          (Node A
                                (Triple A
                                        (HNode A h1' bt1')
                                        e
                                        (HNode A (project_height_hbt A hbt2) (project_bt_hbt A hbt2)))))
                   , e')
           | Eq =>
             match (rotate_left_hbt A (HNode A h1' bt1') e (HNode A (project_height_hbt A hbt2) (project_bt_hbt A hbt2))) with
             | Some new_hbt =>
               Some (new_hbt, e')
             | None =>
               None
             end
           | Gt =>
             None
           end
         | _ =>
           None
         end
       end.

Compute (test_factor_leftmost_t factor_leftmost_t).

(* Unfold lemmas *)        
Lemma unfold_factor_leftmost_t:
  forall (A : Type)
         (hbt1 : heightened_binary_tree A)
         (e : A)
         (hbt2 : heightened_binary_tree A),
    factor_leftmost_t A (Triple A hbt1 e hbt2) =
    factor_leftmost_hbt A hbt1 e hbt2.
Proof.
  unfold_tactic factor_leftmost_t.
Qed.

Lemma unfold_factor_leftmost_hbt:
  forall (A : Type)
         (h1 : nat)
         (bt1 : binary_tree A)
         (e : A)
         (hbt2 : heightened_binary_tree A),
    factor_leftmost_hbt A (HNode A h1 bt1) e hbt2 =
    factor_leftmost_bt A bt1 e hbt2.
Proof.    
  unfold_tactic factor_leftmost_hbt.
Qed.

Lemma unfold_factor_leftmost_bt_leaf:
  forall (A : Type)
         (e : A)
         (hbt2 : heightened_binary_tree A),
  factor_leftmost_bt A (Leaf A) e hbt2 =
  Some (HNode A (project_height_hbt A hbt2) (project_bt_hbt A hbt2), e).
Proof.
  unfold_tactic factor_leftmost_bt.
Qed.

Lemma unfold_factor_leftmost_bt_node:
  forall (A : Type)
         (t1 : triple A)
         (e : A)
         (hbt2 : heightened_binary_tree A),
    factor_leftmost_bt A (Node A t1) e hbt2 =
    match factor_leftmost_t A t1 with
    | Some ((HNode h1' bt1'), e') =>
      match compare_int (project_height_hbt A hbt2) (2 + h1') with
      | Lt =>
        Some ((HNode A
                     (1 + max h1' (project_height_hbt A hbt2))
                     (Node A
                           (Triple A
                                   (HNode A h1' bt1')
                                   e
                                   (HNode A (project_height_hbt A hbt2) (project_bt_hbt A hbt2)))))
              , e')
      | Eq =>
        match (rotate_left_hbt A (HNode A h1' bt1') e (HNode A (project_height_hbt A hbt2) (project_bt_hbt A hbt2))) with
        | Some new_hbt =>
          Some (new_hbt, e')
        | None =>
          None
        end
      | Gt =>
        None
      end
    | _ =>
      None
    end.
Proof.
  unfold_tactic factor_leftmost_t.
Qed.

(* Tests for delete *)

Definition t_del_leaf := (HNode nat 0 (Leaf nat)).

Definition t_del3 :=
  HNode nat 2
        (Node nat
              (Triple nat
                      (HNode nat 1
                             (Node nat
                                   (Triple nat
                                           (HNode nat 0 (Leaf nat))
                                           1
                                           (HNode nat 0 (Leaf nat)))))
                      3
                      (HNode nat 1
                             (Node nat
                                   (Triple nat
                                           (HNode nat 0 (Leaf nat))
                                           5
                                           (HNode nat 0 (Leaf nat))))))).

Compute (is_sound_hbt nat t_del3 && is_balanced_hbt nat t_del3
                      && is_ordered_hbt nat t_del3 compare_int).

Definition t_del3_r :=
  HNode nat 2
        (Node nat
              (Triple nat
                      (HNode nat 0 (Leaf nat))
                      1
                      (HNode nat 1
                             (Node nat
                                   (Triple nat
                                           (HNode nat 0 (Leaf nat))
                                           5
                                           (HNode nat 0 (Leaf nat))))))).

Compute (is_sound_hbt nat t_del3_r && is_balanced_hbt nat t_del3_r
                      && is_ordered_hbt nat t_del3_r compare_int).


Definition t_del3' :=
    HNode nat 3
        (Node nat
              (Triple nat
                      (HNode nat 1
                             (Node nat
                                   (Triple nat
                                           (HNode nat 0 (Leaf nat))
                                           1
                                           (HNode nat 0 (Leaf nat)))))
                      3
                      (HNode nat 2
                             (Node nat
                                   (Triple nat
                                           (HNode nat 1
                                                  (Node nat
                                                        (Triple nat
                                                                (HNode nat 0 (Leaf nat))
                                                                4
                                                                (HNode nat 0 (Leaf nat)))))
                                           5
                                           (HNode nat 0 (Leaf nat))))))).

Compute (is_sound_hbt nat t_del3'&& is_balanced_hbt nat t_del3'
                      && is_ordered_hbt nat t_del3' compare_int).

Definition t_del3'_r :=
  HNode nat 2
        (Node nat
              (Triple nat
                      (HNode nat 1
                             (Node nat
                                   (Triple nat
                                           (HNode nat 0 (Leaf nat))
                                           1
                                           (HNode nat 0 (Leaf nat)))))
                      4
                      (HNode nat 1
                             (Node nat
                                   (Triple nat
                                           (HNode nat 0 (Leaf nat))
                                           5
                                           (HNode nat 0 (Leaf nat))))))).

Compute (is_sound_hbt nat t_del3'_r&& is_balanced_hbt nat t_del3'_r
                      && is_ordered_hbt nat t_del3'_r compare_int).

  
Definition t_del1 := 
  HNode nat 3
        (Node nat
              (Triple nat
                      (HNode nat 1
                             (Node nat
                                   (Triple nat
                                           (HNode nat 0 (Leaf nat))
                                           1
                                           (HNode nat 0 (Leaf nat)))))
                      3
                      (HNode nat 2
                             (Node nat
                                   (Triple nat
                                           (HNode nat 1
                                                  (Node nat
                                                        (Triple nat
                                                                (HNode nat 0 (Leaf nat))
                                                                4
                                                                (HNode nat 0 (Leaf nat)))))
                                           5
                                           (HNode nat 1
                                                  (Node nat
                                                        (Triple nat
                                                                (HNode nat 0 (Leaf nat))
                                                                6
                                                                (HNode nat 0 (Leaf nat)))))
        ))))).

Compute (is_sound_hbt nat t_del1&& is_balanced_hbt nat t_del1
                      && is_ordered_hbt nat t_del1 compare_int).

Definition t_del1_r :=
  HNode nat 3
        (Node nat
              (Triple nat
                      (HNode nat 2
                             (Node nat
                                   (Triple nat
                                           (HNode nat 0 (Leaf nat))
                                           3
                                           (HNode nat 1
                                                  (Node nat
                                                        (Triple nat
                                                                (HNode nat 0 (Leaf nat))
                                                                4
                                                                (HNode nat 0 (Leaf nat)))))
                      )))
                      5
                      (HNode nat 1
                             (Node nat
                                   (Triple nat
                                           (HNode nat 0 (Leaf nat))
                                           6
                                           (HNode nat 0 (Leaf nat))))))).

Compute (is_sound_hbt nat t_del1_r&& is_balanced_hbt nat t_del1_r
                      && is_ordered_hbt nat t_del1_r compare_int).

Definition test_delete_hbt (candidate : (forall (A' : Type),
                                            (A' -> A' -> element_comparison)
                                            -> A'
                                            -> heightened_binary_tree A'
                                            -> heightened_binary_tree A')) :=
  let b0 :=
      equal_hbt nat compare_int (candidate nat compare_int 10 t_del_leaf) t_del_leaf in
  let b1 :=
      equal_hbt nat compare_int (candidate nat compare_int 3 t_del3) t_del3_r in
  let b2 :=
      equal_hbt nat compare_int (candidate nat compare_int 3 t_del3') t_del3'_r in
  let b3 :=
      equal_hbt nat compare_int (candidate nat compare_int 1 t_del1) t_del1_r in
  (b0 && b1 && b2 && b3). 

(* Implementation of delete *)

Fixpoint delete_hbt_helper (A : Type)
         (compare : A -> A -> element_comparison)
         (x : A)
         (hbt : heightened_binary_tree A) :=
  match hbt with
  | HNode h bt =>
    delete_bt_helper A compare x h bt
  end
with delete_bt_helper (A : Type)
         (compare : A -> A -> element_comparison)
         (x : A)
         (h : nat)
         (bt : binary_tree A) :=
       match bt with
       | Leaf =>
         None
       | Node t =>
         delete_t_helper A compare x h t
       end
with delete_t_helper (A : Type)
         (compare : A -> A -> element_comparison)
         (x : A)
         (h : nat)
         (t : triple A) :=
       match t with
       | Triple hbt1 e hbt2 =>
         match compare x e with
         | Lt =>
           match delete_hbt_helper A compare x hbt1 with
           | None =>
             None
           | Some (HNode h1' bt1') =>
             match compare_int (project_height_hbt A hbt2) (2 + h1') with
             | Lt =>
               Some (HNode A (1 + max h1' (project_height_hbt A hbt2))
                           (Node A (Triple A (HNode A h1' bt1') e hbt2)))
             | Eq =>
               rotate_left_hbt A (HNode A h1' bt1') e hbt2 
             | Gt =>
               None
             end
           end
           (* in this case, we have found the node to be deleted *)
         | Eq =>
           (* case 1: height (hbt1) > height (hbt2), factor rightmost *)
           if ((project_height_hbt A hbt1) =n= 1 + (project_height_hbt A hbt2))
           then
             match (project_bt_hbt A hbt1) with
             | Leaf =>
               None
             | Node t1 =>
               match factor_rightmost_t A t1 with
               | None =>
                 None
               | Some (HNode h1' bt1', e') =>
                 Some (HNode A (1 + max h1' (project_height_hbt A hbt2))
                             (Node A (Triple A (HNode A h1' bt1') e' hbt2)))
               end
             end
           else
             (* case 2: height (hbt1) = height (hbt2), factor rightmost, leaf not
              * invalid case *)
             if ((project_height_hbt A hbt1) =n= (project_height_hbt A hbt2))
             then
               match (project_bt_hbt A hbt1) with
               | Leaf =>
                 Some (HNode A 0 (Leaf A))
               | Node t1 =>
                 match factor_rightmost_t A t1 with
                 | None =>
                   None
                 | Some (HNode h1' bt1', e') =>
                   Some (HNode A (1 + max h1' (project_height_hbt A hbt2))
                               (Node A (Triple A (HNode A h1' bt1') e' hbt2)))
                 end
               end
             else
               (* case 3: height (hbt2) > height (hbt1) *) 
               if ((project_height_hbt A hbt2) =n= 1 + (project_height_hbt A hbt1))
               then
                 match (project_bt_hbt A hbt2) with
                 | Leaf =>
                   None
                 | Node t2 =>
                   match factor_leftmost_t A t2 with
                   | None =>
                     None
                   | Some (HNode h2' bt2', e') =>
                     Some (HNode A (1 + max (project_height_hbt A hbt1) h2')
                                 (Node A (Triple A hbt1 e' (HNode A h2' bt2'))))
                   end
                 end
               (* case 4: other height differences: impossible since the triple
                * should be balanced on input *)
               else None
         | Gt =>
           match delete_hbt_helper A compare x hbt2 with
           | None =>
             None
           | Some (HNode h2' bt2') =>
             match compare_int (project_height_hbt A hbt1) (2 + h2') with
             | Lt =>
               Some (HNode A (1 + max (project_height_hbt A hbt1) h2')
                           (Node A (Triple A hbt1 e (HNode A h2' bt2'))))
             | Eq =>
               rotate_right_hbt A hbt1 e (HNode A h2' bt2') 
             | Gt =>
               None
             end
           end
         end
       end.

(* Unfold lemmas for the delete helper functions *)

Lemma unfold_delete_hbt_helper:
  forall (A : Type)
         (compare : A -> A -> element_comparison)
         (x : A)
         (h : nat)
         (bt : binary_tree A),
    delete_hbt_helper A compare x (HNode A h bt) =
    delete_bt_helper A compare x h bt.
Proof.
  unfold_tactic delete_hbt_helper.
Qed.         
             
Lemma unfold_delete_bt_helper_leaf:
  forall (A : Type)
         (compare : A -> A -> element_comparison)
         (x : A)
         (h : nat),
    delete_bt_helper A compare x h (Leaf A) =
    None.
Proof.
  unfold_tactic delete_bt_helper.
Qed.         

Lemma unfold_delete_bt_helper_node:
  forall (A : Type)
         (compare : A -> A -> element_comparison)
         (x : A)
         (h : nat)
         (t : triple A),
    delete_bt_helper A compare x h (Node A t) =
    delete_t_helper A compare x h t.    
Proof.
  unfold_tactic delete_bt_helper.
Qed.         

Lemma unfold_delete_t_helper:
  forall (A : Type)
         (compare : A -> A -> element_comparison)
         (x : A)
         (h : nat)
         (hbt1 : heightened_binary_tree A)
         (e : A) 
         (hbt2 : heightened_binary_tree A),
    delete_t_helper A compare x h (Triple A hbt1 e hbt2) =
    match compare x e with
         | Lt =>
           match delete_hbt_helper A compare x hbt1 with
           | None =>
             None
           | Some (HNode h1' bt1') =>
             match compare_int (project_height_hbt A hbt2)  (2 + h1') with
             | Lt =>
               Some (HNode A (1 + max h1' (project_height_hbt A hbt2))
                           (Node A (Triple A (HNode A h1' bt1') e hbt2)))
             | Eq =>
               rotate_left_hbt A (HNode A h1' bt1') e hbt2 
             | Gt =>
               None
             end
           end
           (* in this case, we have found the node to be deleted *)
         | Eq =>
           (* case 1: height (hbt1) > height (hbt2), factor rightmost *)
           if ((project_height_hbt A hbt1) =n= 1 + (project_height_hbt A hbt2))
           then
             match (project_bt_hbt A hbt1) with
             | Leaf =>
               None
             | Node t1 =>
               match factor_rightmost_t A t1 with
               | None =>
                 None
               | Some (HNode h1' bt1', e') =>
                 Some (HNode A (1 + max h1' (project_height_hbt A hbt2))
                             (Node A (Triple A (HNode A h1' bt1') e' hbt2)))
               end
             end
           else
             (* case 2: height (hbt1) = height (hbt2), factor rightmost, leaf not
              * invalid case *)
             if ((project_height_hbt A hbt1) =n= (project_height_hbt A hbt2))
             then
               match (project_bt_hbt A hbt1) with
               | Leaf =>
                 Some (HNode A 0 (Leaf A))
               | Node t1 =>
                 match factor_rightmost_t A t1 with
                 | None =>
                   None
                 | Some (HNode h1' bt1', e') =>
                   Some (HNode A (1 + max h1' (project_height_hbt A hbt2))
                               (Node A (Triple A (HNode A h1' bt1') e' hbt2)))
                 end
               end
             else
               (* case 3: height (hbt2) > height (hbt1) *) 
               if ((project_height_hbt A hbt2) =n= 1 + (project_height_hbt A hbt1))
               then
                 match (project_bt_hbt A hbt2) with
                 | Leaf =>
                   None
                 | Node t2 =>
                   match factor_leftmost_t A t2 with
                   | None =>
                     None
                   | Some (HNode h2' bt2', e') =>
                     Some (HNode A (1 + max (project_height_hbt A hbt1) h2')
                                 (Node A (Triple A hbt1 e' (HNode A h2' bt2'))))
                   end
                 end
               (* case 4: other height differences: impossible since the triple
                * should be balanced on input *)
               else None
         | Gt =>
           match delete_hbt_helper A compare x hbt2 with
           | None =>
             None
           | Some (HNode h2' bt2') =>
             match compare_int (project_height_hbt A hbt1) (2 + h2') with
             | Lt =>
               Some (HNode A (1 + max (project_height_hbt A hbt1) h2')
                           (Node A (Triple A hbt1 e (HNode A h2' bt2'))))
             | Eq =>
               rotate_right_hbt A hbt1 e (HNode A h2' bt2') 
             | Gt =>
               None
             end
           end
         end.
Proof.
  unfold_tactic delete_t_helper.
Qed.

Definition delete_hbt (A : Type)
           (compare : A -> A -> element_comparison)
           (x : A)
           (hbt : heightened_binary_tree A) :=
  match delete_hbt_helper A compare x hbt with
  | None =>
    hbt
  | Some hbt' =>
    hbt'
  end.

Compute (test_delete_hbt delete_hbt).


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




(* ***** Section 2: Specifications and theorems for delete *)
Definition specifiction_of_delete_hbt
           (A : Type)
           (compare : A -> A -> element_comparison)
           (x : A)
           (delete_hbt : forall (A' : Type),
               (A' -> A' -> element_comparison)
               -> A'
               -> heightened_binary_tree A'
               -> heightened_binary_tree A') :=
  forall (hbt : heightened_binary_tree A),
    (is_sound_hbt A hbt = true) ->
    (is_balanced_hbt A hbt = true) ->
    (is_ordered_hbt A hbt compare = true) -> 
    (is_sound_hbt A (delete_hbt A compare x hbt) = true)
    /\
    (is_balanced_hbt A (delete_hbt A compare x hbt) = true)
    /\
    (is_ordered_hbt A (delete_hbt A compare x hbt) compare = true).



(* Main theorem for deletion concerning ordering *)
Lemma deletion_preserves_order: 
  forall (A : Type)
         (compare : A -> A -> element_comparison)
         (x : A),
    (forall (hbt : heightened_binary_tree A)
            (hbt' : heightened_binary_tree A),
        is_sound_hbt A hbt = true ->
        is_balanced_hbt A hbt = true ->
        is_ordered_hbt A hbt compare = true -> 
        delete_hbt_helper A compare x hbt = Some hbt' ->
        is_ordered_hbt A hbt' compare = true)
    /\
    (forall (bt : binary_tree A)
            (h_hbt : nat)
            (hbt' : heightened_binary_tree A),    
        is_sound_hbt A (HNode A h_hbt bt) = true ->
        is_balanced_hbt A (HNode A h_hbt bt) = true ->
        is_ordered_hbt A (HNode A h_hbt bt) compare = true ->
        delete_bt_helper A compare x h_hbt bt = Some hbt' ->
        is_ordered_hbt A hbt' compare = true)
    /\
    (forall (t : triple A)
            (h_hbt : nat)
            (hbt' : heightened_binary_tree A),    
        is_sound_hbt A (HNode A h_hbt (Node A t)) = true ->
        is_balanced_hbt A (HNode A h_hbt (Node A t)) = true ->
        is_ordered_hbt A (HNode A h_hbt (Node A t)) compare = true ->        
        delete_t_helper A compare x h_hbt t = Some hbt' ->
        is_ordered_hbt A hbt' compare = true).
Proof.
  Admitted.




Theorem delete_hbt_satisfies_its_specification:
  forall (A : Type)
         (compare : A -> A -> element_comparison)
         (x : A),
    specifiction_of_delete_hbt A compare x delete_hbt. 
Proof.
  intros.
  unfold specifiction_of_delete_hbt.
  intros.
  unfold delete_hbt.
  case (delete_hbt_helper A compare x hbt) as [hbt' | ] eqn: C_del.

  Focus 2.
  split.
  exact H.
  split.

  exact H0.
  exact H1.

  destruct (deletion_preserves_soundness_and_balance A compare x) as [H_s_b _].
  destruct (H_s_b hbt hbt' H H0 C_del) as [H_sound H_bal].
  
  destruct (deletion_preserves_order A compare x) as [H_o _].         
  assert (H_ord : is_ordered_hbt A hbt' compare = true).
  exact (H_o hbt hbt' H H0 H1 C_del).
  split.

  exact H_sound.
  split.

  exact H_bal.
  exact H_ord.
Qed.
