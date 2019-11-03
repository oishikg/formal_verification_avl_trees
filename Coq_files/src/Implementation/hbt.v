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
  | HNode _ h bt =>
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
       | Leaf _ =>
         Some 0
       | Node _ t =>
         traverse_to_check_soundness_t A t
       end
with traverse_to_check_soundness_t
       (A : Type)
       (t : triple A) : option nat :=
       match t with
       | Triple _ hbt1 _ hbt2 =>
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
  | HNode _ _ bt =>
    traverse_to_check_balanced_bt A bt
  end
with traverse_to_check_balanced_bt
       (A : Type) (bt : binary_tree A) : option nat :=
       match bt with
       | Leaf _ =>
         Some 0
       | Node _ t =>
         traverse_to_check_balanced_t A t
       end
with traverse_to_check_balanced_t
       (A : Type) (t : triple A) : option nat :=
       match t with
       | Triple _ hbt1 _ hbt2 =>
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

Inductive triple_option (A : Type) : Type := 
| TError : triple_option A
| TNone : triple_option A
| TSome : A -> triple_option A.

Lemma tsome_x_equal_tsome_y:
  forall (A : Type)
         (x y : A),
    TSome A x = TSome A y <-> x = y.
Proof.
  intros; split.
  intro.
  inversion H; reflexivity.
  intro.
  rewrite -> H; reflexivity.
Qed.



Fixpoint traverse_to_check_ordered_hbt
         (A : Type)
         (hbt : heightened_binary_tree A)
         (compare : A -> A -> element_comparison) : triple_option (A * A) :=
  match hbt with
  | HNode _ h bt =>
    traverse_to_check_ordered_bt A bt compare
  end
with traverse_to_check_ordered_bt
       (A : Type)
       (bt : binary_tree A)
       (compare : A -> A -> element_comparison) : triple_option (A * A) :=
       match bt with
       | Leaf _ =>
         TNone (A * A)
       | Node _ t =>
         traverse_to_check_ordered_t A t compare
       end
with traverse_to_check_ordered_t
       (A : Type)
       (t : triple A)
       (compare : A -> A -> element_comparison) : triple_option (A * A) :=
       match t with
       | Triple _ hbt1 e hbt2 =>
         match traverse_to_check_ordered_hbt A hbt1 compare with
         (* hbt1 is unordered *)
         | TError _ =>
           TError (A * A)
         (* hbt1 is a leaf *)
         | TNone _ =>
           match traverse_to_check_ordered_hbt A hbt2 compare with
           (* hbt2 is unordered *)
           | TError _ =>
             TError (A * A)
           (* hbt2 is a leaf *)
           | TNone _ =>
             TSome (A * A) (e, e)
           (*  hbt2 is an ordered heightened_binary_tree *)
           | TSome _ (min2, max2) =>
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
         | TSome _ (min1, max1) =>
           match compare max1 e with
           | Lt =>
             match traverse_to_check_ordered_hbt A hbt2 compare with
             (* hbt2 is unordered *)
             | TError _ =>
               TError (A * A)
             (* hbt2 is a leaf *)
             | TNone _ =>
               TSome (A * A) (min1, e)
             (* hbt2 is an ordered heightened_binary_tree *)
             | TSome _ (min2, max2) =>
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
    | TError _ => TError (A * A)
    | TNone _ =>
      match traverse_to_check_ordered_hbt A hbt2 compare with
      | TError _ => TError (A * A)
      | TNone _ => TSome (A * A) (e, e)
      | TSome _ (min2, max2) =>
        match compare e min2 with
        | Lt => TSome (A * A) (e, max2)
        | Eq => TError (A * A)
        | Gt => TError (A * A)
        end
      end
    | TSome _ (min1, max1) =>
      match compare max1 e with
      | Lt =>
        match traverse_to_check_ordered_hbt A hbt2 compare with
        | TError _ => TError (A * A)
        | TNone _ => TSome (A * A) (min1, e)
        | TSome _ (min2, max2) =>
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
  | TError _ =>
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
  | HNode _ h bt =>
    occurs_bt A compare e bt
  end
with occurs_bt
       (A : Type)
       (compare : A -> A -> element_comparison)
       (e : A)
       (bt : binary_tree A) : bool :=
       match bt with
       | Leaf _ =>
         false
       | Node _ t =>
         occurs_t A compare e t
       end
with occurs_t
       (A : Type)
       (compare : A -> A -> element_comparison)
       (e : A)
       (t : triple A) : bool :=
       match t with
       | Triple _ hbt1 e' hbt2 =>
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
    | HNode _ _ bt =>
      bt_to_list A bt
    end
with bt_to_list (A : Type) (bt : binary_tree A) : list A :=
       match bt with
       | Leaf _ =>
         nil
       | Node _ t =>
         t_to_list A t
       end
with t_to_list (A : Type) (t : triple A) : list A :=
       match t with
       | Triple _ hbt1 e hbt2 =>
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
  | Leaf _ =>
    None
  | Node _ (Triple _ (HNode _ h11 bt11) e1 (HNode _ h12 bt12)) =>
    if h11 + 1 =n= h12
    then 
      match bt12 with
      | Leaf _ =>
        None
      | Node _ (Triple _ (HNode _ h121 bt121) e12 (HNode _ h122 bt122)) => 
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
      if (h12 + 1 =n= h11) || (h12 =n= h11)
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
  | HNode _ _ bt1 =>
    match hbt2 with
    | HNode _ h2 bt2 =>
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
  | Leaf _ =>
    None
  | Node _ (Triple _ (HNode _ h21 bt21) e2 (HNode _ h22 bt22)) =>
    if h22 + 1 =n= h21
    then
      match bt21 with
      | Leaf _ =>
        None
      | Node _ (Triple _ (HNode _ h211 bt211) e21 (HNode _ h212 bt212)) =>
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
      if (h21 + 1 =n= h22) || (h21 =n= h22)
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
  | HNode _ h1 bt1 =>
    match hbt2 with
    | HNode _ _ bt2 =>
      rotate_left_bt A h1 bt1 e bt2
    end
  end.

Definition project_height_hbt
           (A : Type)
           (hbt : heightened_binary_tree A) : nat :=
  match hbt with
  | HNode _ h _ => h
  end.

Definition project_bt_hbt
           (A : Type)
           (hbt : heightened_binary_tree A) : binary_tree A :=
  match hbt with
  | HNode _ _ bt => bt
  end.
           

Definition project_height_bt
           (A : Type)
           (bt : binary_tree A) :=
  match bt with
  | Leaf _ =>
    0
  | Node _ (Triple _ hbt1 _ hbt2) =>
    1 + max (project_height_hbt A hbt1) (project_height_hbt A hbt2)
  end.

Definition project_height_t
           (A : Type)
           (t : triple A) :=
  match t with
  | Triple _ hbt1 _ hbt2 =>
    1 + max (project_height_hbt A hbt1) (project_height_hbt A hbt2)
  end.

Fixpoint insert_hbt_helper
         (A : Type)
         (compare : A -> A -> element_comparison)
         (x : A) 
         (hbt : heightened_binary_tree A) :=
  match hbt with
  | HNode _ h bt =>
    insert_bt_helper A compare x h bt
  end
with insert_bt_helper
       (A : Type)
       (compare : A -> A -> element_comparison)
       (x : A)
       (h_hbt : nat)
       (bt : binary_tree A) :=
       match bt with
       | Leaf _ =>
         Some (HNode A
                     1
                     (Node A (Triple A
                                     (HNode A 0 (Leaf A))
                                     x 
                                     (HNode A 0 (Leaf A)))))
       | Node _ t =>
         insert_t_helper A compare x h_hbt t
       end
with insert_t_helper
       (A : Type)
       (compare : A -> A -> element_comparison)
       (x : A)
       (h_hbt : nat)
       (t : triple A) :=
       match t with
       | Triple _ hbt1 e hbt2 =>
         match compare x e with
         | Lt =>
           match insert_hbt_helper A compare x hbt1 with
           | None =>
             None 
           | Some (HNode _ h1' bt1') =>
             (* if (h1' =n= project_height_hbt A hbt1) *)
             (*    || (h1' =n= 1 + (project_height_hbt A hbt1)) *)
             (* then *)
             match compare_int h1' (2 + (project_height_hbt A hbt2)) with
             | Lt =>
               Some (HNode A
                           (1 + max h1' (project_height_hbt A hbt2))
                           (Node A (Triple A (HNode A h1' bt1') e hbt2)))
             | Eq =>
               rotate_right_hbt A (HNode A h1' bt1') e hbt2
             | Gt =>
               None 
             end
               (* else *)
               (*   None *)
           end
         | Eq =>
           None
         | Gt =>
           match insert_hbt_helper A compare x hbt2 with 
           | None =>
             None 
           | Some (HNode _ h2' bt2') =>
             (* if (h2' =n= project_height_hbt A hbt2) *)
             (*    || (h2' =n= 1 + (project_height_hbt A hbt2)) *)
             (* then *)
             match compare_int h2' (2 + (project_height_hbt A hbt1)) with
             | Lt =>
               Some (HNode A
                           (1 + max (project_height_hbt A hbt1) h2')
                           (Node A (Triple A hbt1 e (HNode A h2' bt2'))))
             | Eq =>
               rotate_left_hbt A hbt1 e (HNode A h2' bt2')
             | Gt =>
               None
             end
               (* else *)
               (*   None *)
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
      | Some (HNode _ h1' bt1') =>
        match compare_int h1' (2 + (project_height_hbt A hbt2)) with
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
      | Some (HNode _ h2' bt2') =>
        match compare_int h2' (2 + (project_height_hbt A hbt1)) with
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

