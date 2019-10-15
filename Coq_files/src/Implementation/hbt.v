(* ********** Imports ********** *)
Require Import Hbt.Paraphernalia.paraphernalia.
Require Export Hbt.Paraphernalia.paraphernalia.

(* ********** Section 1: Different AVL tree type definitions  ********** *)

(* Coq formalization of polymorphic ordinary binary tree implementation *)
Inductive ordinary_binary_tree (A : Type) : Type :=
| OLeaf : ordinary_binary_tree A
| ONode : ordinary_binary_tree A -> A -> ordinary_binary_tree A.

(* Coq formalization of polymorphic AVL tree type *) 
Inductive heightened_binary_tree (A : Type) : Type := 
  HNode : nat -> binary_tree A -> heightened_binary_tree A 
with binary_tree (A : Type) : Type :=
     | Leaf : binary_tree A
     | Node : triple A -> binary_tree A 
with triple (A : Type) : Type :=
     | Triple : heightened_binary_tree A -> A -> heightened_binary_tree A -> triple A.

(* We need define an induction principle for mutually inductive types; this is done as 
 * follows: *)
Scheme heightened_binary_tree_induction := Induction for heightened_binary_tree Sort Prop
  with binary_tree_induction := Induction for binary_tree Sort Prop
  with triple_induction := Induction for triple Sort Prop.

Combined Scheme heightened_binary_tree_mutual_induction
         from heightened_binary_tree_induction,binary_tree_induction,triple_induction.

(* See: https://coq.inria.fr/refman/user-extensions/proof-schemes.html *) 
 
Check heightened_binary_tree_mutual_induction.

(* This property requires that the height stored in each node of an AVL Tree is
 *  accurate *)

(* ********** Section 3: The invariant properties of AVL trees ********** *)

(* ***** 3.1: Soundness ***** *)

(* Recursive helper functions to traverse the different structures
 * Note that we might need to use a compare function instead of =n=. *)
Fixpoint traverse_to_check_soundness_hbt
         (A : Type)
         (hbt : heightened_binary_tree A) : option nat :=
  match hbt with
  | HNode h bt =>
    match traverse_to_check_soundness_bt A bt with
    | None =>
      None
    | Some h' =>
      if h' =n= h
      then Some h
      else None
    end
  end
with traverse_to_check_soundness_bt
       (A : Type)
       (bt : binary_tree A) : option nat :=
       match bt with
       | Leaf =>
         Some 0
       | Node t =>
         traverse_to_check_soundness_t A t
       end
with traverse_to_check_soundness_t
       (A : Type)
       (t : triple A) : option nat :=
       match t with
       | Triple hbt1 _ hbt2 =>
         match traverse_to_check_soundness_hbt A hbt1 with
         | None =>
           None
         | Some h1 =>
           match traverse_to_check_soundness_hbt A hbt2 with
           | None =>
             None
           | Some h2 =>
             Some (1 + max h1 h2)
           end
         end
       end.

(* Unfold lemmas for traverse_to_check_soundness_hbt, traverse_to_check_soundness_bt, and traverse_to_check_soundness_t *)
Lemma unfold_traverse_to_check_soundness_hbt:
  forall (A : Type)
         (h : nat)
         (bt : binary_tree A),
    traverse_to_check_soundness_hbt A (HNode A h bt) =
    match traverse_to_check_soundness_bt A bt with
    | None =>
      None
    | Some h' =>
      if h' =n= h
      then Some h
      else None
    end.
Proof.
  unfold_tactic traverse_to_check_soundness_hbt.
Qed.

Lemma unfold_traverse_to_check_soundness_bt_leaf:
  forall (A : Type),
    traverse_to_check_soundness_bt A (Leaf A) = Some 0.
Proof.
    unfold_tactic traverse_to_check_soundness_bt.
Qed.

Lemma unfold_traverse_to_check_soundness_bt_node:
  forall (A : Type)
         (t : triple A),
    traverse_to_check_soundness_bt A (Node A t) = traverse_to_check_soundness_t A t.
Proof.
  unfold_tactic traverse_to_check_soundness_bt.
Qed.

Lemma unfold_traverse_to_check_soundness_t:
  forall (A : Type)
         (hbt1 hbt2 : heightened_binary_tree A)
         (e : A),
    traverse_to_check_soundness_t A (Triple A hbt1 e hbt2) =
    match traverse_to_check_soundness_hbt A hbt1 with
    | None =>
      None
    | Some h1 =>
      match traverse_to_check_soundness_hbt A hbt2 with
      | None =>
        None
      | Some h2 =>
        Some (1 + max h1 h2)
      end
    end.
Proof.
  unfold_tactic traverse_to_check_soundness_t.
Qed.

(* Function to test soundness of a heightened_binary_tree *)
Definition is_sound_hbt (A : Type) (hbt : heightened_binary_tree A) :=
  match traverse_to_check_soundness_hbt A hbt with
  | None =>
    false
  | Some _ =>
    true
  end.

(* ***** *)

(* ***** 3.2: Balancedness ***** *)

(* This property requires that for every node in the tree, the heights of its 
 * subtrees differ by at most 1 *)

(* Unit tests for differ_by_one *)
Definition test_differ_by_one (cand : nat -> nat -> bool) : bool :=
  (cand 3 4 =b= true)
  &&
  (cand 4 6 =b= false)
  &&
  (cand 3 2 =b= true)
  &&
  (cand 8 2 =b= false).
                  
(* Helper function to check if two heights differ by 1 *) 
Definition differ_by_one (h1 h2 : nat) : bool :=
   (h1 =n= h2 + 1) || (h2 =n= h1 + 1) || (h2 =n= h1).
  
Compute (test_differ_by_one differ_by_one).
 
(* Recursive helper function to traverse binary tree to check for balanced *)
Fixpoint traverse_to_check_balanced_hbt
         (A : Type) (hbt : heightened_binary_tree A) : option nat :=
  match hbt with
  | HNode _ bt =>
    traverse_to_check_balanced_bt A bt
  end
with traverse_to_check_balanced_bt
       (A : Type) (bt : binary_tree A) : option nat :=
       match bt with
       | Leaf =>
         Some 0
       | Node t =>
         traverse_to_check_balanced_t A t
       end
with traverse_to_check_balanced_t
       (A : Type) (t : triple A) : option nat :=
       match t with
       | Triple hbt1 _ hbt2 =>
         match traverse_to_check_balanced_hbt A hbt1 with
         | None =>
           None
         | Some h1 =>
           match traverse_to_check_balanced_hbt A hbt2 with
           | None =>
             None
           | Some h2 =>
             if differ_by_one h1 h2
             then Some (1 + max h1 h2)
             else None
           end
         end
       end.

(* Unfold lemmas for traverse_to_check_balanced_hbt, traverse_to_check_balanced_bt, and
 * traverse_to_check_balanced_t *)
Lemma unfold_traverse_to_check_balanced_hbt:
  forall (A : Type)
         (h : nat)
         (bt : binary_tree A),
    traverse_to_check_balanced_hbt A (HNode A h bt) = traverse_to_check_balanced_bt A bt.
Proof.          
  unfold_tactic traverse_to_check_balanced_hbt.
Qed.

Lemma unfold_traverse_to_check_balanced_bt_leaf:
  forall (A : Type),
    traverse_to_check_balanced_bt A (Leaf A) = Some 0.
Proof.
    unfold_tactic traverse_to_check_balanced_bt.
Qed.

Lemma unfold_traverse_to_check_balanced_bt_node:
  forall (A : Type)
         (t : triple A),
    traverse_to_check_balanced_bt A (Node A t) = traverse_to_check_balanced_t A t.
Proof.
  unfold_tactic traverse_to_check_balanced_bt.
Qed.

Lemma unfold_traverse_to_check_balanced_t:
  forall (A : Type)
         (hbt1 hbt2 : heightened_binary_tree A)
         (e : A),
    traverse_to_check_balanced_t A (Triple A hbt1 e hbt2) =
    match traverse_to_check_balanced_hbt A hbt1 with
    | None =>
      None
    | Some h1 =>
      match traverse_to_check_balanced_hbt A hbt2 with
      | None =>
        None
      | Some h2 =>
        if differ_by_one h1 h2
        then Some (1 + max h1 h2)
        else None
      end
    end.
Proof.
  unfold_tactic traverse_to_check_balanced_t.
Qed.

(* Function to test balanced of a heightened_binary_tree *)
Definition is_balanced_hbt (A : Type) (hbt : heightened_binary_tree A) :=
  match traverse_to_check_balanced_hbt A hbt with
  | None =>
    false
  | Some h =>
    true
  end.

(* ***** *)

(* ***** 3.3: In-orderedness ***** *)


Fixpoint traverse_to_check_ordered_hbt
         (A : Type)
         (hbt : heightened_binary_tree A)
         (compare : A -> A -> element_comparison) : triple_option (A * A) :=
  match hbt with
  | HNode h bt =>
    traverse_to_check_ordered_bt A bt compare
  end
with traverse_to_check_ordered_bt
       (A : Type)
       (bt : binary_tree A)
       (compare : A -> A -> element_comparison) : triple_option (A * A) :=
       match bt with
       | Leaf =>
         TNone (A * A)
       | Node t =>
         traverse_to_check_ordered_t A t compare
       end
with traverse_to_check_ordered_t
       (A : Type)
       (t : triple A)
       (compare : A -> A -> element_comparison) : triple_option (A * A) :=
       match t with
       | Triple hbt1 e hbt2 =>
         match traverse_to_check_ordered_hbt A hbt1 compare with
         (* hbt1 is unordered *)
         | TError =>
           TError (A * A)
         (* hbt1 is a leaf *)
         | TNone =>
           match traverse_to_check_ordered_hbt A hbt2 compare with
           (* hbt2 is unordered *)
           | TError =>
             TError (A * A)
           (* hbt2 is a leaf *)
           | TNone =>
             TSome (A * A) (e, e)
           (*  hbt2 is an ordered heightened_binary_tree *)
           | TSome (min2, max2) =>
             match compare e min2 with
             | Lt =>
               TSome (A * A) (e, max2)
             | Eq =>
               TError (A * A)
             | Gt =>
               TError (A * A)
             end
           end
         (* hbt1 is an ordered heightened_binary_tree *)
         | TSome (min1, max1) =>
           match compare max1 e with
           | Lt =>
             match traverse_to_check_ordered_hbt A hbt2 compare with
             (* hbt2 is unordered *)
             | TError =>
               TError (A * A)
             (* hbt2 is a leaf *)
             | TNone =>
               TSome (A * A) (min1, e)
             (* hbt2 is an ordered heightened_binary_tree *)
             | TSome (min2, max2) =>
               match compare e min2 with
               | Lt =>
                 TSome (A * A) (min1, max2)
               | Eq =>
                 TError (A * A)
               | Gt =>
                 TError (A * A)
               end
             end
           | Eq =>
             TError (A * A)
           | Gt =>
             TError (A * A)
           end
         end
       end.

(* Unfold lemmas for the helper functions *)
Lemma unfold_traverse_to_check_ordered_hbt:
  forall (A : Type)
         (h : nat)
         (bt : binary_tree A)
         (compare : A -> A -> element_comparison),
    traverse_to_check_ordered_hbt A (HNode A h bt) compare =
    traverse_to_check_ordered_bt A bt compare. 
Proof.
  unfold_tactic traverse_to_check_ordered_hbt.
Qed.             

Lemma unfold_traverse_to_check_ordered_bt_leaf:
  forall (A : Type)
         (compare : A -> A -> element_comparison),
    traverse_to_check_ordered_bt A (Leaf A) compare =
    TNone (A * A).
Proof.
  unfold_tactic traverse_to_check_ordered_bt.
Qed.             

Lemma unfold_traverse_to_check_ordered_bt_node:
  forall (A : Type)
         (t : triple A) 
         (compare : A -> A -> element_comparison),
    traverse_to_check_ordered_bt A (Node A t) compare =
    traverse_to_check_ordered_t A t compare.
Proof.
  unfold_tactic traverse_to_check_ordered_t.
Qed.             
       
Lemma unfold_traverse_to_check_ordered_t: 
  forall (A : Type)
         (hbt1 : heightened_binary_tree A)
         (e : A)
         (hbt2 : heightened_binary_tree A)
         (compare : A -> A -> element_comparison),
    traverse_to_check_ordered_t A (Triple A hbt1 e hbt2) compare =
    match traverse_to_check_ordered_hbt A hbt1 compare with
    | TError => TError (A * A)
    | TNone =>
      match traverse_to_check_ordered_hbt A hbt2 compare with
      | TError => TError (A * A)
      | TNone => TSome (A * A) (e, e)
      | TSome (min2, max2) =>
        match compare e min2 with
        | Lt => TSome (A * A) (e, max2)
        | Eq => TError (A * A)
        | Gt => TError (A * A)
        end
      end
    | TSome (min1, max1) =>
      match compare max1 e with
      | Lt =>
        match traverse_to_check_ordered_hbt A hbt2 compare with
        | TError => TError (A * A)
        | TNone => TSome (A * A) (min1, e)
        | TSome (min2, max2) =>
          match compare e min2 with
          | Lt => TSome (A * A) (min1, max2)
          | Eq => TError (A * A)
          | Gt => TError (A * A)
          end
        end
      | Eq => TError (A * A)
      | Gt => TError (A * A)
      end
    end.
Proof.
  unfold_tactic traverse_to_check_ordered_t.
Qed.

(* Function to check if a heightened_binary_tree is ordered *)
Definition is_ordered_hbt
           (A : Type)
           (hbt : heightened_binary_tree A)
           (compare : A -> A -> element_comparison) : bool :=
  match traverse_to_check_ordered_hbt A hbt compare with
  | TError =>
    false
  | _ =>
    true
  end.

(* ********** Section 4 : The lookup operation in AVL trees ********** *)

(* ***** Section 4.1: Implementations of occurs for both AVL trees type ***** *) 

(* Function to traverse hbt and check if an element occurs *)
Fixpoint occurs_hbt
         (A : Type)
         (compare : A -> A -> element_comparison)
         (e : A)
         (hbt : heightened_binary_tree A) : bool :=
  match hbt with
  | HNode h bt =>
    occurs_bt A compare e bt
  end
with occurs_bt
       (A : Type)
       (compare : A -> A -> element_comparison)
       (e : A)
       (bt : binary_tree A) : bool :=
       match bt with
       | Leaf =>
         false
       | Node t =>
         occurs_t A compare e t
       end
with occurs_t
       (A : Type)
       (compare : A -> A -> element_comparison)
       (e : A)
       (t : triple A) : bool :=
       match t with
       | Triple hbt1 e' hbt2 =>
         match compare e e' with
         | Lt =>
           occurs_hbt A compare e hbt1
         | Eq =>
           true
         | Gt =>
           occurs_hbt A compare e hbt2
         end
       end.

(* Unfold lemmas for occurs_hbt, occurs_bt, occurs_t *)
Lemma unfold_occurs_hbt:
  forall (A : Type)
         (compare : A -> A -> element_comparison)
         (e : A)
         (h : nat)
         (bt : binary_tree A),
    occurs_hbt A compare e (HNode A h bt) = occurs_bt A compare e bt.
Proof.
  unfold_tactic occurs_hbt.
Qed.

Lemma unfold_occurs_bt_leaf: 
  forall (A : Type)
         (compare : A -> A -> element_comparison)
         (e : A),
    occurs_bt A compare e (Leaf A) = false.
Proof.
  unfold_tactic occurs_bt.
Qed.

Lemma unfold_occurs_bt_node:
  forall (A : Type)
         (compare : A -> A -> element_comparison)
         (e : A)
         (t : triple A),
    occurs_bt A compare e (Node A t) = occurs_t A compare e t.
Proof.  
  unfold_tactic occurs_bt.
Qed.

Lemma unfold_occurs_t:
  forall (A : Type)
         (compare : A -> A -> element_comparison)
         (e e' : A)
         (hbt1 hbt2 : heightened_binary_tree A),
    occurs_t A compare e (Triple A hbt1 e' hbt2) =
    match compare e e' with
    | Lt =>
      occurs_hbt A compare e hbt1
    | Eq =>
      true
    | Gt =>
      occurs_hbt A compare e hbt2
    end.
Proof.      
  unfold_tactic occurs_t.
Qed.

(* ********** Section 5: The insert operation on trees ********** *)

(* ***** Section 5.1: Tests  ***** *)

(* Helper function to check the equality of lists *) 
Fixpoint equal_lists
         (A : Type)
         (compare : A -> A -> element_comparison)
         (xs ys : list A) : bool :=
  match xs with
  | nil =>
    match ys with
    | nil =>
      true
    | _ =>
      false
    end
  | x :: xs' =>
    match ys with
    | nil =>
      false
    | y :: ys' =>
      match compare x y with
      | Eq =>
        equal_lists A compare xs' ys'
      | _ =>
        false
      end
    end
  end.

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


(* Function to check equality of heightened_binary_tree s *)
Definition equal_hbt
         (A : Type)
         (compare : A -> A -> element_comparison)
         (hbt1 hbt2 : heightened_binary_tree A) : bool := 
  equal_lists A compare (hbt_to_list A hbt1) (hbt_to_list A hbt2).

(* Function to insert a list of values into a heightened_binary_tree *)
Fixpoint insert_list
         (A : Type)
         (insert : forall (A' : Type),
             (A' -> A' -> element_comparison)
             -> A'
             -> heightened_binary_tree A'
             -> heightened_binary_tree A')
         (compare : A -> A -> element_comparison)
         (xs : list A)
         (hbt : heightened_binary_tree A) :=
  match xs with
  | nil =>
    hbt
  | x :: xs' =>
    insert_list A insert compare xs' (insert A compare x hbt)
  end.

(* Function to generate values between 1 and n *)
Fixpoint atoi (n : nat) :=
  match n with
  | 0 =>
    nil
  | S n' =>
    (S n') :: (atoi n')
  end.

(* Function to generate values between n and 1 *)
Fixpoint traverse (n : nat) (acc : list nat) :=
  match n with
  | 0 =>
    acc
  | S n' =>
    traverse n' ((S n') :: acc)
  end.

Definition iota (n : nat) :=
  traverse n nil.

(* Sample heightened_binary_tree s for testing *)
Definition hbt_empty := HNode nat 0 (Leaf nat).

Definition hbt_1 :=
  HNode nat 2 (Node nat (Triple nat
                            (HNode nat 0 (Leaf nat))
                            1
                            (HNode nat 1 (Node nat (Triple nat
                                                       (HNode nat 0 (Leaf nat))
                                                       2
                                                       (HNode nat 0 (Leaf nat))))))).

Definition test_insert_hbt
           (candidate : forall (A' : Type),
               (A' -> A' -> element_comparison)
               -> A'
               -> heightened_binary_tree A'
               -> heightened_binary_tree A') :=
  (is_sound_hbt
     nat
     (candidate nat compare_int 1 (candidate nat compare_int 2 hbt_empty)))
    && (is_balanced_hbt
          nat 
          (candidate nat compare_int 1 (candidate nat compare_int 2 hbt_empty)))
    && (is_ordered_hbt
          nat
          (candidate nat compare_int 1 (candidate nat compare_int 2 hbt_empty))
          compare_int)
    && (is_sound_hbt
          nat
          (candidate nat compare_int 2 (candidate nat compare_int 1 hbt_empty)))
    && (is_balanced_hbt
          nat
          (candidate nat compare_int 2 (candidate nat compare_int 1 hbt_empty)))
    && (is_ordered_hbt
          nat
          (candidate nat compare_int 2 (candidate nat compare_int 1 hbt_empty))
          compare_int)
    && (equal_hbt
          nat
          compare_int
          (candidate nat compare_int 1 (candidate nat compare_int 2 hbt_empty))
          (candidate nat compare_int 2 (candidate nat compare_int 1 hbt_empty)))
    && (is_sound_hbt
          nat
          (candidate nat compare_int 15 hbt_1))
    && (is_balanced_hbt
          nat
          (candidate nat compare_int 15 hbt_1))
    && (is_ordered_hbt
          nat
          (candidate nat compare_int 15 hbt_1)
          compare_int)
    && (is_sound_hbt
          nat
          (insert_list nat candidate compare_int (atoi 50) hbt_empty))
    && (is_ordered_hbt
          nat
          (insert_list nat candidate compare_int (atoi 50) hbt_empty)
          compare_int)
    && (is_balanced_hbt
          nat
          (insert_list nat candidate compare_int (atoi 50) hbt_empty))
    && (is_sound_hbt
          nat
          (insert_list nat candidate compare_int (iota 50) hbt_empty))
    && (is_ordered_hbt
          nat
          (insert_list nat candidate compare_int (iota 50) hbt_empty)
          compare_int)
    && (is_balanced_hbt
          nat
          (insert_list nat candidate compare_int (iota 50) hbt_empty)).

(* ***** *)

(* ***** Section 5.2: Implementation of rotation and insert functions *) 

(* Implementing rotate right *)

Definition rotate_right_bt
           (A : Type)
           (bt1 : binary_tree A)
           (e : A)
           (h2 : nat)
           (bt2 : binary_tree A) :=
  match bt1 with
  | Leaf =>
    None
  | Node (Triple (HNode h11 bt11) e1 (HNode h12 bt12)) =>
    if h11 + 1 =n= h12
    then 
      match bt12 with
      | Leaf =>
        None
      | Node (Triple (HNode h121 bt121) e12 (HNode h122 bt122)) => 
        Some (HNode A
                    (1 + max (1 + max h11 h121) (1 + max h122 h2))
                    (Node A (Triple A
                                    (HNode A
                                           (1 + max h11 h121)
                                           (Node A (Triple A
                                                           (HNode A h11 bt11)
                                                           e1
                                                           (HNode A h121 bt121))))
                                    e12
                                    (HNode A
                                           (1 + max h122 h2)
                                           (Node A (Triple A
                                                           (HNode A h122 bt122)
                                                           e
                                                           (HNode A h2 bt2)))))))
      end
    else
      if h12 + 1 =n= h11
      then Some (HNode A
                       (1 + max h11 (1 + max h12 h2))
                       (Node A (Triple A
                                       (HNode A h11 bt11)
                                       e1
                                       (HNode A
                                              (1 + max h12 h2)
                                              (Node A (Triple A
                                                              (HNode A h12 bt12)
                                                              e
                                                              (HNode A h2 bt2)))))))
                (* impossible case *)
      else None
  end.
           
Definition rotate_right_hbt
         (A : Type)
         (hbt1 : heightened_binary_tree A)
         (e : A)
         (hbt2 : heightened_binary_tree A) :=
  match hbt1 with
  | HNode _ bt1 =>
    match hbt2 with
    | HNode h2 bt2 =>
      rotate_right_bt A bt1 e h2 bt2
    end
  end.

Definition rotate_left_bt
           (A : Type)
           (h1 : nat)
           (bt1 : binary_tree A)
           (e : A)
           (bt2 : binary_tree A) :=
  match bt2 with
  | Leaf =>
    None
  | Node (Triple (HNode h21 bt21) e2 (HNode h22 bt22)) =>
    if h22 + 1 =n= h21
    then
      match bt21 with
      | Leaf =>
        None
      | Node (Triple (HNode h211 bt211) e21 (HNode h212 bt212)) =>
        Some (HNode A
                    (1 + max (1 + max h1 h211) (1 + max h212 h22))
                    (Node A (Triple A
                                    (HNode A
                                           (1 + max h1 h211)
                                           (Node A (Triple A
                                                           (HNode A h1 bt1)
                                                           e
                                                           (HNode A h211 bt211))))
                                    e21
                                    (HNode A
                                           (1 + max h212 h22)
                                           (Node A (Triple A
                                                           (HNode A h212 bt212)
                                                           e2
                                                           (HNode A h22 bt22)))))))
      end
    else
      if h21 + 1 =n= h22
      then Some (HNode A (1 + max (1 + max h1 h21) h22)
                       (Node A (Triple A
                                       (HNode A
                                              (1 + max h1 h21)
                                              (Node A (Triple A
                                                              (HNode A h1 bt1)
                                                              e
                                                              (HNode A h21 bt21))))
                                       e2
                                       (HNode A h22 bt22))))
                (* impossible case *)
      else None
  end.

Definition rotate_left_hbt
         (A : Type)
         (hbt1 : heightened_binary_tree A)
         (e : A)
         (hbt2 : heightened_binary_tree A) :=
  match hbt1 with
  | HNode h1 bt1 =>
    match hbt2 with
    | HNode _ bt2 =>
      rotate_left_bt A h1 bt1 e bt2
    end
  end.

Definition project_height_hbt
           (A : Type)
           (hbt : heightened_binary_tree A) : nat :=
  match hbt with
  | HNode h _ => h
  end.

Definition project_bt_hbt
           (A : Type)
           (hbt : heightened_binary_tree A) : binary_tree A :=
  match hbt with
  | HNode _ bt => bt
  end.
           

Definition project_height_bt
           (A : Type)
           (bt : binary_tree A) :=
  match bt with
  | Leaf =>
    0
  | Node (Triple hbt1 _ hbt2) =>
    1 + max (project_height_hbt A hbt1) (project_height_hbt A hbt2)
  end.

Definition project_height_t
           (A : Type)
           (t : triple A) :=
  match t with
  | Triple hbt1 _ hbt2 =>
    1 + max (project_height_hbt A hbt1) (project_height_hbt A hbt2)
  end.

Fixpoint insert_hbt_helper
         (A : Type)
         (compare : A -> A -> element_comparison)
         (x : A) 
         (hbt : heightened_binary_tree A) :=
  match hbt with
  | HNode h bt =>
    insert_bt_helper A compare x h bt
  end
with insert_bt_helper
       (A : Type)
       (compare : A -> A -> element_comparison)
       (x : A)
       (h_hbt : nat)
       (bt : binary_tree A) :=
       match bt with
       | Leaf =>
         Some (HNode A
                     1
                     (Node A (Triple A
                                     (HNode A 0 (Leaf A))
                                     x 
                                     (HNode A 0 (Leaf A)))))
       | Node t =>
         insert_t_helper A compare x h_hbt t
       end
with insert_t_helper
       (A : Type)
       (compare : A -> A -> element_comparison)
       (x : A)
       (h_hbt : nat)
       (t : triple A) :=
       match t with
       | Triple hbt1 e hbt2 =>
         match compare x e with
         | Lt =>
           match insert_hbt_helper A compare x hbt1 with
           | None =>
             None 
           | Some (HNode h1' bt1') =>
             match compare_int (h1' - (project_height_hbt A hbt2)) 2 with
             | Lt =>
               Some (HNode A
                           (1 + max h1' (project_height_hbt A hbt2))
                           (Node A (Triple A (HNode A h1' bt1') e hbt2)))
             | Eq =>
               rotate_right_hbt A (HNode A h1' bt1') e hbt2
             | Gt =>
               None 
             end
           end
         | Eq =>
           None
         | Gt =>
           match insert_hbt_helper A compare x hbt2 with 
           | None =>
             None 
           | Some (HNode h2' bt2') =>
             match compare_int (h2' - (project_height_hbt A hbt1)) 2 with
             | Lt =>
               Some (HNode A
                           (1 + max (project_height_hbt A hbt1) h2')
                           (Node A (Triple A hbt1 e (HNode A h2' bt2'))))
             | Eq =>
               rotate_left_hbt A hbt1 e (HNode A h2' bt2')
             | Gt =>
               None
             end
           end
         end
       end.

Check (insert_bt_helper).
(* Unfold lemmas *)
Lemma  unfold_insert_hbt_helper:
  forall (A : Type)
         (compare : A -> A -> element_comparison)
         (x : A)
         (h : nat)
         (bt : binary_tree A),
    insert_hbt_helper A compare x (HNode A h bt) = insert_bt_helper A compare x h bt.
Proof.
  unfold_tactic insert_hbt_helper.
Qed.

Lemma unfold_insert_bt_helper_leaf:
  forall (A : Type)
         (compare : A -> A -> element_comparison)
         (x : A)
         (h_hbt : nat),
    insert_bt_helper A compare x h_hbt (Leaf A) =
    Some (HNode A
                1
                (Node A (Triple A
                                (HNode A 0 (Leaf A))
                                x 
                                (HNode A 0 (Leaf A))))).
Proof.
  unfold_tactic insert_bt_helper.
Qed.

Lemma unfold_insert_bt_helper_node:
  forall (A : Type)
         (compare : A -> A -> element_comparison)
         (x : A)
         (h_hbt : nat) 
         (t : triple A),
    insert_bt_helper A compare x h_hbt (Node A t) =
    insert_t_helper A compare x h_hbt t.
Proof.    
  unfold_tactic insert_bt_helper.
Qed.

Lemma unfold_insert_t_helper:
  forall (A : Type)
         (compare : A -> A -> element_comparison)
         (x : A)
         (h_hbt : nat) 
         (hbt1 : heightened_binary_tree A)
         (e : A)
         (hbt2 : heightened_binary_tree A),
    insert_t_helper A compare x h_hbt (Triple A hbt1 e hbt2) =
    match compare x e with
    | Lt =>
      match insert_hbt_helper A compare x hbt1 with
      | None =>
        None 
      | Some (HNode h1' bt1') =>
        match compare_int (h1' - (project_height_hbt A hbt2)) 2 with
        | Lt =>
          Some (HNode A
                      (1 + max h1' (project_height_hbt A hbt2))
                      (Node A (Triple A (HNode A h1' bt1') e hbt2)))
        | Eq =>
          rotate_right_hbt A (HNode A h1' bt1') e hbt2
        | Gt =>
          None 
        end
      end
    | Eq =>
      None
    | Gt =>
      match insert_hbt_helper A compare x hbt2 with 
      | None =>
        None 
      | Some (HNode h2' bt2') =>
        match compare_int (h2' - (project_height_hbt A hbt1)) 2 with
        | Lt =>
          Some (HNode A
                      (1 + max (project_height_hbt A hbt1) h2')
                      (Node A (Triple A hbt1 e (HNode A h2' bt2'))))
        | Eq =>
          rotate_left_hbt A hbt1 e (HNode A h2' bt2')
        | Gt =>
          None
        end
      end
    end.
Proof.
  intros.
  unfold insert_t_helper.
  reflexivity.
Qed.

Definition insert_hbt
         (A : Type)
         (compare : A -> A -> element_comparison)
         (x : A) 
         (hbt : heightened_binary_tree A) :=
  match insert_hbt_helper A compare x hbt with
  | None =>
    hbt
  | Some hbt' =>
    hbt'
  end.
 
Compute (test_insert_hbt insert_hbt).
(* The tests work! *)

(* ********** 6: Deletion operation on AVL trees ********** *)

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
           match compare_int (project_height_hbt A hbt1) (h2' + 2) with
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
      match compare_int (project_height_hbt A hbt1) (h2' + 2) with
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
           match compare_int (project_height_hbt A hbt2) (h1' + 2) with
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
      match compare_int (project_height_hbt A hbt2) (h1' + 2) with
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
  
Definition delete_is_succesful opt_hbt1 hbt1_del_res :=
  match opt_hbt1 with
  | None =>
    false
  | Some hbt1 =>
    equal_hbt nat compare_int hbt1 hbt1_del_res
  end.

Definition test_delete_hbt_helper candidate :=
  let b0 :=
      delete_is_succesful (candidate nat compare_int 10 t_del_leaf) t_del_leaf in
  let b1 :=
      delete_is_succesful (candidate nat compare_int 3 t_del3) t_del3_r in
  let b2 :=
      delete_is_succesful (candidate nat compare_int 3 t_del3') t_del3'_r in
  let b3 :=
      delete_is_succesful (candidate nat compare_int 3 t_del1) t_del1_r in
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
             match compare_int ((project_height_hbt A hbt2) - h1') 2 with
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
           if ((project_height_hbt A hbt1) - (project_height_hbt A hbt2) =n= 1)
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
               if ((project_height_hbt A hbt2) - (project_height_hbt A hbt1) =n= 1)
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
             match compare_int (h2' - (project_height_hbt A hbt1)) 2 with
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
             match compare_int ((project_height_hbt A hbt2) - h1') 2 with
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
           if ((project_height_hbt A hbt1) - (project_height_hbt A hbt2) =n= 1)
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
               if ((project_height_hbt A hbt2) - (project_height_hbt A hbt1) =n= 1)
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
             match compare_int (h2' - (project_height_hbt A hbt1)) 2 with
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

