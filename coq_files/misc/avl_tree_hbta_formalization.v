(* Formalization of Professor Danvy's formalization of AVL Trees 
 * in Coq; refer to the implementation in week-02b_balanced-binary-trees.ml *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Oishik Ganguly <oishik.ganguly@u.yale-nus.edu.sg> *)


(* ********** *)

(* Paraphernalia: *)
 
Ltac unfold_tactic name := intros; unfold name; (* fold name; *) reflexivity.

Require Import Arith Bool List. 

(* Equality of natural numbers *)
Notation "A =n= B" :=
  (beq_nat A B) (at level 70, right associativity).

(* Equality of boolean values *) 
Notation "A =b= B" :=
  (eqb A B) (at level 70, right associativity).

(* Function to check if the first argument is less than the second argument *)
Fixpoint ltb (n m : nat) : bool :=
  match n with
  | 0    =>
    match m with
    | 0   =>
      false
    | S _ =>
      true
    end
  | S n' =>
    match m with
    | 0    =>
      false
    | S m' =>
      ltb n' m'
    end
  end.

(* Unit tests for ltb *)
Definition test_ltb (candidate : nat -> nat -> bool) :=
  (candidate 3 4 =b= true)
    &&
    (candidate 5 7 =b= true)
    &&
    (candidate 13 32 =b= true)
    &&
    (candidate 5 2 =b= false)
    &&
    (candidate 90 32 =b= false).
    
Compute (test_ltb ltb).

(* Notation for "less than" *) 
Notation "A <n B" := (ltb A B) (at level 70, right associativity).

(* Function to check if the first argument is greater than the second argument *)
Fixpoint gtb (n m : nat) : bool :=
  match n with
  | 0    =>
    false
  | S n' =>
    match m with
    | 0    =>
      true
    | S m' =>
      gtb n' m'
    end
  end.

(* Unit tests for ltb *)
Definition test_gtb (candidate : nat -> nat -> bool) :=
  (candidate 3 4 =b= false)
    &&
    (candidate 5 7 =b= false)
    &&
    (candidate 13 32 =b= false)
    &&
    (candidate 5 2 =b= true)
    &&
    (candidate 90 32 =b= true).

Compute (test_gtb gtb).

(* Notation for "greater than" *) 
Notation "A n> B" := (gtb A B) (at level 70, right associativity).

(* Paraphernalia for comparison: *)
Inductive comparison :=
| Lt : comparison
| Eq : comparison
| Gt : comparison.

Definition compare_int (i j : nat) : comparison := 
  if i <n j then Lt else if i =n= j then Eq else Gt. 


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

(* Coq formalization of alternative polymorphic AVL tree type *)
Inductive heightened_binary_tree_alternative (A : Type) : Type :=
  | ALeaf : heightened_binary_tree_alternative A
  | ANode : nat -> heightened_binary_tree_alternative A -> A -> heightened_binary_tree_alternative A -> heightened_binary_tree_alternative A. 

Check (heightened_binary_tree_alternative_ind).

(* Recursive function to convert a heightened_binary_tree to an 
 * alternative_heightened_binary_tree *)
Fixpoint hbt_to_hbta
         (A : Type)
         (hbt : heightened_binary_tree A) : heightened_binary_tree_alternative A :=
  match hbt with
  | HNode h bt =>
    bt_to_hbta A h bt
  end
with bt_to_hbta
       (A : Type)
       (h : nat)
       (bt : binary_tree A) : heightened_binary_tree_alternative A :=
       match bt with
       | Leaf =>
         ALeaf A
       | Node t =>
         t_to_hbta A h t
       end
with t_to_hbta
       (A : Type)
       (h : nat)
       (t : triple A) : heightened_binary_tree_alternative A :=
       match t with
       | Triple hbt1 e hbt2 =>
         ANode A h (hbt_to_hbta A hbt1) e (hbt_to_hbta A hbt2)
       end.

(* Unfold lemmas for hbt_to_hbta, bt_to_hbta, and t_to_hbta *)
Lemma unfold_hbt_to_hbta:
  forall (A : Type)
         (h : nat)
         (bt : binary_tree A),
    hbt_to_hbta A (HNode A h bt) = bt_to_hbta A h bt.
Proof.
  unfold_tactic hbt_to_hbta.
Qed.

Lemma unfold_bt_to_hbta_leaf:
  forall (A : Type)
         (h : nat),
    bt_to_hbta A h (Leaf A) = (ALeaf A).
Proof.         
  unfold_tactic bt_to_hbta.
Qed.

Lemma unfold_bt_to_hbta_node:
  forall (A : Type)
         (h : nat)
         (t : triple A),
    bt_to_hbta A h (Node A t) = t_to_hbta A h t.
Proof.  
  unfold_tactic bt_to_hbta.
Qed.
  
Lemma unfold_t_to_hbta:
  forall (A : Type)
         (h : nat)
         (hbt1 hbt2 : heightened_binary_tree A)
         (e : A),
    t_to_hbta A h (Triple A hbt1 e hbt2) =
    ANode A h (hbt_to_hbta A hbt1) e (hbt_to_hbta A hbt2).
Proof.  
  unfold_tactic t_to_hbta.
Qed.

(* Recursive function to convert a heightened_binary_tree_alternative to an 
 * heightened_binary_tree *)
Fixpoint hbta_to_hbt (A : Type) (hbta : heightened_binary_tree_alternative A) : heightened_binary_tree A :=
  match hbta with
  | ALeaf => HNode A 0 (Leaf A)
  | ANode h hbta1 e hbta2 =>
    HNode A h (Node A (Triple A (hbta_to_hbt A hbta1) e (hbta_to_hbt A hbta2)))
  end. 

(* Unfold lemmas for hbta_to_hbt *)
Lemma unfold_hbta_to_hbt_leaf :
  forall (A : Type),
    hbta_to_hbt A (ALeaf A) = HNode A 0 (Leaf A).
Proof.
  unfold_tactic hbta_to_hbt.
Qed. 

Lemma unfold_hbta_to_hbt_node :
  forall (h : nat)
         (A : Type)
         (hbta1 : heightened_binary_tree_alternative A)
         (e : A)
         (hbta2 : heightened_binary_tree_alternative A),
    hbta_to_hbt A (ANode A h hbta1 e hbta2) =
    HNode A h (Node A (Triple A (hbta_to_hbt A hbta1) e (hbta_to_hbt A hbta2))).
Proof.                      
  unfold_tactic hbta_to_hbt.
Qed.                        

(* Note that, excluding heightened_binary_tree s which are leaves with non-zero 
 * height, the two types heightened_binary_tree and heightened_binary_tree_alternative
 * are isomorphic. This allows us to define analogous functions *)

(* Function that, given a function that acts on heightened_binary_tree s, 
 * returns the analogues function for heightened_binary_tree_alternative *)
Definition hbta_analogue
           (A : Type)
           (f_hbt : heightened_binary_tree A -> heightened_binary_tree A) :
  (heightened_binary_tree_alternative A -> heightened_binary_tree_alternative A) :=
  fun hbta => hbt_to_hbta A (f_hbt (hbta_to_hbt A hbta)).

(* Function that, given a function that acts on heightened_binary_tree_alternative s
 * returns the analogues function for heightened_binary_tree s *)
Definition hbt_analogue
           (A : Type)
           (f_hbta : heightened_binary_tree_alternative A ->
                     heightened_binary_tree_alternative A):
  (heightened_binary_tree A -> heightened_binary_tree A) :=
  fun hbt => hbta_to_hbt A (f_hbta (hbt_to_hbta A hbt)).

(* Unfortunately, hbt_to_hbta must consider in its domain all heightened_binary_tree s
 * that are leaves with non-zero height; these trees are unsound and should obviously
 * not be considered in the domain. heightened_binary_tree_alternative however, does
 * not contain such invalid values, since the leaves have no height. Thus, 
 * hbt_to_hbta is a partial function. We will return to this issue when we need to 
 * alternate between types. 
 * Two possible solutions: 
   (i) Write a propostion that constrains the domain of heightened_binary_tree s
   (ii) Redefine the type 
 * For now, we only prove one side on the theorem. *) 

(* hbta_to_hbt and hbta_to_hbt are isomorphic *)
Proposition isomorphic1 :
  forall (A : Type) 
         (hbta : heightened_binary_tree_alternative A),
    hbt_to_hbta A (hbta_to_hbt A hbta) = hbta.
Proof. 
  intros A hbta. 
  induction hbta as [ | h hbta1 IH_hbta1 e hbta2 IH_hbta2].

  (* Base case *)
  Check (unfold_hbta_to_hbt_leaf A).
  rewrite -> (unfold_hbta_to_hbt_leaf A).
  Check (unfold_hbt_to_hbta).
  rewrite -> (unfold_hbt_to_hbta A 0 (Leaf A)).
  Check (unfold_bt_to_hbta_leaf).
  rewrite -> (unfold_bt_to_hbta_leaf A 0).
  reflexivity.

  (* Inductive case *)
  Check (unfold_hbta_to_hbt_node h A hbta1 e hbta2). 
  rewrite -> (unfold_hbta_to_hbt_node h A hbta1 e hbta2).
  Check (unfold_hbt_to_hbta).
  rewrite -> (unfold_hbt_to_hbta
                A
                h
                (Node A (Triple A (hbta_to_hbt A hbta1) e (hbta_to_hbt A hbta2)))).
  Check (unfold_bt_to_hbta_node).
  rewrite -> (unfold_bt_to_hbta_node
                A
                h
                (Triple A (hbta_to_hbt A hbta1) e (hbta_to_hbt A hbta2))).
  Check (unfold_t_to_hbta).
  rewrite -> (unfold_t_to_hbta A h (hbta_to_hbt A hbta1) (hbta_to_hbt A hbta2)).
  rewrite -> IH_hbta1.
  rewrite -> IH_hbta2.
  reflexivity.
Qed.

(* write isomoprhic2 *) 
         

(* ********** Section 3: The invariant properties of AVL trees ********** *)

(* ***** 3.1: Soundness ***** *)

(* This property requires that the height stored in each node of an AVL Tree is
 *  accurate *) 

(* Recursive helper functions to traverse the different structures
 * Note that we might need to use a compare function instead of =n=. *)

(* Recursive helper function to traverse a heightened_binary_tree_alternative *)
Fixpoint traverse_to_check_soundness_hbta (A : Type) (hbta : heightened_binary_tree_alternative A) : option nat :=
  match hbta with
  | ALeaf =>
    Some 0
  | ANode h hbta1 e hbta2 =>
     match traverse_to_check_soundness_hbta A hbta1 with
     | None =>
        None
     | Some h1 =>
        match traverse_to_check_soundness_hbta A hbta2 with
        | None =>
           None
        | Some h2 =>
           if h =n= 1 + max h1 h2
           then Some h
           else None
        end
     end
  end.

(* Unfold lemmas for traverse_to_check_soundness_hbta *)
Lemma unfold_traverse_to_check_soundness_hbta_leaf :
  forall (A : Type),
    traverse_to_check_soundness_hbta A (ALeaf A) = Some 0.
Proof.
  unfold_tactic traverse_to_check_soundness_hbta.
Qed.    

Lemma unfold_traverse_to_check_soundness_hbta_node:
  forall (A: Type)
         (h : nat)
         (e : A) 
         (hbta1 hbta2 : heightened_binary_tree_alternative A),
    traverse_to_check_soundness_hbta A (ANode A h hbta1 e hbta2) = 
     match traverse_to_check_soundness_hbta A hbta1 with
     | None =>
        None
     | Some h1 =>
        match traverse_to_check_soundness_hbta A hbta2 with
        | None =>
           None
        | Some h2 =>
           if h =n= 1 + max h1 h2
           then Some h
           else None
        end
     end.
Proof.
  unfold_tactic traverse_to_check_soundness_hbta.
Qed.

(* Function to test the soundness of a heightened_binary_tree_alternative *)
Definition is_sound_hbta
           (A : Type) (hbta : heightened_binary_tree_alternative A) : bool := 
  match traverse_to_check_soundness_hbta A hbta with
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
 
(* Recursive helper function to traverse heightened_binary_tree_alternative to check
 * if balanced *)
Fixpoint traverse_to_check_balanced_hbta
         (A : Type) (hbta : heightened_binary_tree_alternative A) : option nat :=
  match hbta with
  | ALeaf =>
    Some 0
  | ANode h hbta1 e hbta2 =>
    match traverse_to_check_balanced_hbta A hbta1 with
    | None =>
      None
    | Some h1' =>
      match traverse_to_check_balanced_hbta A hbta2 with
      | None =>
        None
      | Some h2' =>
        if differ_by_one h1' h2'
        then Some (1 + max h1' h2')
        else None
      end
    end
  end.

(* Unfold lemmas for traverse_to_check_balanced_hbta *)
Lemma unfold_traverse_to_check_balanced_hbta_leaf:
  forall (A : Type),
    traverse_to_check_balanced_hbta A (ALeaf A) = Some 0.
Proof.
  unfold_tactic traverse_to_check_balanced_hbta.
Qed.

Lemma unfold_traverse_to_check_balanced_hbta_node:
  forall (A : Type)
         (h : nat)
         (e : A)
         (hbta1 hbta2 : heightened_binary_tree_alternative A),
    traverse_to_check_balanced_hbta A (ANode A h hbta1 e hbta2) =
    match traverse_to_check_balanced_hbta A hbta1 with
    | None =>
      None
    | Some h1' =>
      match traverse_to_check_balanced_hbta A hbta2 with
      | None =>
        None
      | Some h2' =>
        if differ_by_one h1' h2'
        then Some (1 + max h1' h2')
        else None
      end
    end.
Proof.
  unfold_tactic traverse_to_check_balanced_hbta.
Qed.

(* Function to test balanced of a heightened_binary_tree_alternative *)
Definition is_balanced_hbta
           (A : Type)
           (hbta : heightened_binary_tree_alternative A) : bool := 
  match traverse_to_check_balanced_hbta A hbta with
  | Some _ =>
    true
  | None =>
    false
  end.

(* ***** *)

(* ***** 3.3: In-orderedness ***** *)

(* This property requires that the payloads of the tree traversed depth-first 
 * left to right are in-order (i.e., ascending or descending)  *)

(* Our strategy to check for in-orderedness will involve flattening trees into 
 * lists; we do so as follows: *)

(* Function to map a heightened_binary_tree_alternative into the in-order
 * list of its elements *)
Fixpoint flatten_hbta
           (A : Type) (hbta : heightened_binary_tree_alternative A) : list A := 
  match hbta with
  | ALeaf =>
    nil
  | ANode _ hbta1 e hbta2 =>
    (flatten_hbta A hbta1) ++ (e :: (flatten_hbta A hbta2))
  end.

(* Unfold lemmas for flatten_hbta_helper *)
Lemma unfold_flatten_hbta_helper_leaf:
  forall (A : Type),
    flatten_hbta A (ALeaf A) = nil.
Proof.
  unfold_tactic flatten_hbta.
Qed. 

Lemma unfold_flatten_hbta_helper_node:
  forall (A : Type)
         (h : nat)
         (hbta1 hbta2 : heightened_binary_tree_alternative A)
         (e : A),
    flatten_hbta A (ANode A h hbta1 e hbta2) =
    (flatten_hbta A hbta1) ++ (e :: (flatten_hbta A hbta2)).
Proof.
  unfold_tactic flatten_hbta.
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
         (es' : list A)
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

(* Function to check whether heightened_binary_tree_alternative is in order *)
Definition is_ordered_hbta (A : Type)
           (hbta : heightened_binary_tree_alternative A)
           (compare : A -> A -> comparison) : bool :=
  is_ordered_list A (flatten_hbta A hbta) compare.

(* ***** *)

(* ***** Section 3.4.1: Independence of soundness and balancedness ***** *)

Definition hbta_sound_but_unbalanced
           (A : Type) (a : A) : heightened_binary_tree_alternative A :=
  ANode A 3
        (ALeaf A)
        a
        (ANode A 2
               (ALeaf A)
               a
               (ANode A 1
                      (ALeaf A)
                      a
                      (ALeaf A))).

Definition hbta_unsound_but_balanced
           (A : Type) (a : A) : heightened_binary_tree_alternative A :=
  ANode A 3
        (ALeaf A)
        a
        (ALeaf A).

Proposition independence_of_soundness_and_balancedness_hbta:
  forall (A : Type)
         (a : A),
    (exists hbta : heightened_binary_tree_alternative A,
        (is_sound_hbta A hbta = true) /\ (is_balanced_hbta A hbta = false))
    /\
    (exists hbta : heightened_binary_tree_alternative A,
        (is_sound_hbta A hbta = false) /\ (is_balanced_hbta A hbta = true)). 
Proof.
  intros A a.
  split. 

  (* ***** Existence of hbta that is sound but not balanced ***** *)
  - exists (hbta_sound_but_unbalanced A a).
    split.

    (* Show that counter-example is sound *)
    unfold is_sound_hbta.
    unfold hbta_sound_but_unbalanced.
    Check (unfold_traverse_to_check_soundness_hbta_node
             A 3 a (ALeaf A) (ANode A 2
                                    (ALeaf A)
                                    a
                                    (ANode A 1
                                           (ALeaf A)
                                           a
                                           (ALeaf A)))).
    (* Apply unfold lemmas until hbta structure is completely unfolded *) 
    rewrite -> (unfold_traverse_to_check_soundness_hbta_node
                  A 3 a (ALeaf A) (ANode A 2
                                         (ALeaf A)
                                         a
                                         (ANode A 1
                                                (ALeaf A)
                                                a
                                                (ALeaf A)))).
    rewrite -> (unfold_traverse_to_check_soundness_hbta_leaf A).
    rewrite -> (unfold_traverse_to_check_soundness_hbta_node
                  A 2 a (ALeaf A) (ANode A 1
                                         (ALeaf A)
                                         a
                                         (ALeaf A))).
    rewrite -> (unfold_traverse_to_check_soundness_hbta_leaf A). 
    rewrite -> (unfold_traverse_to_check_soundness_hbta_node
                  A 1 a (ALeaf A) (ALeaf A)).
    rewrite -> (unfold_traverse_to_check_soundness_hbta_leaf A).
    (* Unfold remaining functions in order of computation *)
    unfold max at 1.
    Search (_ + 0 = _).
    rewrite -> (plus_0_r 1).
    unfold beq_nat at 1.
    unfold max at 1.
    rewrite -> (plus_Sn_m 0 1).
    rewrite -> (plus_0_l 1).
    unfold beq_nat at 1.
    unfold max at 1.
    rewrite -> (plus_Sn_m 0 2).
    rewrite -> (plus_0_l 2).
    unfold beq_nat at 1.
    reflexivity.

    (* Show that counter example is unbalanced *)
    unfold is_balanced_hbta.
    unfold hbta_sound_but_unbalanced.
    (* Apply unfold lemmas until hbta structure is completely unfolded *) 
    rewrite -> (unfold_traverse_to_check_balanced_hbta_node
                  A 3 a (ALeaf A) (ANode A 2
                                         (ALeaf A)
                                         a
                                         (ANode A 1
                                                (ALeaf A)
                                                a
                                                (ALeaf A)))).
    rewrite -> (unfold_traverse_to_check_balanced_hbta_leaf A).
    rewrite -> (unfold_traverse_to_check_balanced_hbta_node
                  A 2 a (ALeaf A) (ANode A 1
                                         (ALeaf A)
                                         a
                                         (ALeaf A))).
    rewrite -> (unfold_traverse_to_check_balanced_hbta_leaf A).
    rewrite -> (unfold_traverse_to_check_balanced_hbta_node
                  A 1 a (ALeaf A) (ALeaf A)).
    rewrite -> (unfold_traverse_to_check_balanced_hbta_leaf A).
    (* Unfold the remaining functions in order of computation *)
    unfold differ_by_one at 1.
    rewrite -> (plus_0_l 1).    
    unfold beq_nat at 1 2 3.
    unfold orb at 1 2.
    unfold differ_by_one at 1.
    unfold max.    
    rewrite -> (plus_0_l 1).
    rewrite -> (plus_0_r 1).
    rewrite -> (plus_Sn_m 0 1).
    rewrite -> (plus_0_l 1).
    unfold beq_nat at 1 2 3.
    unfold orb at 1 2.
    unfold differ_by_one.
    rewrite -> (plus_Sn_m 1 1).
    rewrite -> (plus_Sn_m 0 1).
    rewrite -> (plus_0_l 1).
    unfold beq_nat at 1 2 3.
    unfold orb at 1 2.
    reflexivity. 

  (* ***** Existence of hbta that is not sound but balanced ***** *)
  - exists (hbta_unsound_but_balanced A a).
    split. 

    (* Show that the counter-example is unsound *)
    unfold hbta_unsound_but_balanced.
    unfold is_sound_hbta.
    (* Apply unfold lemmas until the structure is completely unfolded *)
    rewrite ->
            (unfold_traverse_to_check_soundness_hbta_node
               A 3 a (ALeaf A) (ALeaf A)).
    rewrite -> unfold_traverse_to_check_soundness_hbta_leaf.
    (* Unfold the remaining functions *)
    unfold max.
    rewrite -> (plus_0_r 1).
    unfold beq_nat.
    reflexivity.

    (* Show that counter-example is balanced *)
    unfold hbta_unsound_but_balanced.
    unfold is_balanced_hbta.
    (* Use unfold lemmas to unfold the structure *)
    rewrite ->
            (unfold_traverse_to_check_balanced_hbta_node
               A 3 a (ALeaf A) (ALeaf A)).
    rewrite -> (unfold_traverse_to_check_balanced_hbta_leaf A).
    (* Unfold the remaining functions *)
    unfold differ_by_one.
    rewrite -> (plus_0_l 1).
    unfold beq_nat.
    unfold orb.
    reflexivity.
Qed.

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

Definition hbta_sound_but_unordered
           (A : Type) (a1 a2 : A) : heightened_binary_tree_alternative A :=
  ANode A 2
        (ALeaf A)
        a2
        (ANode A 1
               (ALeaf A)
               a1
               (ALeaf A)).

Definition hbta_unsound_but_ordered
           (A : Type) (a1 : A) : heightened_binary_tree_alternative A :=
  ANode A 3
        (ALeaf A)
        a1
        (ALeaf A).

Proposition independence_of_soundness_and_orderedness_hbta:
    forall (A : Type),
    (exists (f : A -> A -> comparison)
            (a1 a2 : A),
            f a2 a1 = Gt) -> 
    (exists (hbta : heightened_binary_tree_alternative A)
            (cmp : A -> A -> comparison),
        (is_sound_hbta A hbta = true) /\ (is_ordered_hbta A hbta cmp = false))
    /\
    (exists (hbta : heightened_binary_tree_alternative A)
            (cmp : A -> A -> comparison),
        (is_sound_hbta A hbta = false) /\ (is_ordered_hbta A hbta cmp = true)).
Proof.
  intros A [f [a1 [a2 H_f]]].
  split.

  (* ***** Existence of hbt that is sound but unordered ***** *)
  - exists (hbta_sound_but_unordered A a1 a2). 
    exists f.
    split. 

    (* Show that counter-example is sound *)
    unfold hbta_sound_but_unordered.
    unfold is_sound_hbta.
    rewrite ->
            (unfold_traverse_to_check_soundness_hbta_node
               A 2 a2
               (ALeaf A)
               (ANode A 1 (ALeaf A) a1 (ALeaf A))).
    rewrite -> (unfold_traverse_to_check_soundness_hbta_leaf A).
    rewrite ->
            (unfold_traverse_to_check_soundness_hbta_node
               A 1 a1
               (ALeaf A)
               (ALeaf A)).
    rewrite -> (unfold_traverse_to_check_soundness_hbta_leaf A).
    (* Now unfold the remaining functions in order of computation *)
    unfold beq_nat at 1. 
    unfold max at 1.
    Search (_ + 0 = _).
    rewrite -> (plus_0_r 1).
    unfold max at 1.
    rewrite -> (plus_Sn_m 0 1).
    rewrite -> (plus_0_l 1).
    unfold beq_nat at 1.
    reflexivity.

    (* Show that counter-example is unbalanced *)
    unfold hbta_sound_but_unordered.
    unfold is_ordered_hbta.
    unfold is_ordered_list.
    unfold flatten_hbta.
    (* Flatten the counter-example into a list by unfolding *)
    rewrite ->
            (unfold_flatten_hbta_helper_node
               A nil 2
               (ALeaf A) (ANode A 1 (ALeaf A) a1 (ALeaf A))
               a2).
    rewrite ->
            (unfold_flatten_hbta_helper_leaf
               A
               (a2 :: flatten_hbta_helper A (ANode A 1 (ALeaf A) a1 (ALeaf A)) nil)).
    rewrite ->
            (unfold_flatten_hbta_helper_node
               A nil 1
               (ALeaf A) (ALeaf A)
               a1).
    rewrite ->
            (unfold_flatten_hbta_helper_leaf
               A
               (a1 :: flatten_hbta_helper A (ALeaf A) nil)).
    rewrite ->
            (unfold_flatten_hbta_helper_leaf
               A
               nil).
    rewrite ->
            (unfold_is_ordered_cons_cons
               A a2 a1 nil f).
    rewrite -> H_f.
    reflexivity.

  (* ***** Existence of hbta that is unsound but ordered ***** *)
  - exists (hbta_unsound_but_ordered A a1).
    exists f.
    split.

    (* Show that the counter-example is unsound *)
    unfold hbta_unsound_but_ordered.
    unfold is_sound_hbta.
    rewrite ->
            (unfold_traverse_to_check_soundness_hbta_node
               A 3 a1 (ALeaf A) (ALeaf A)).
    rewrite -> (unfold_traverse_to_check_soundness_hbta_leaf A).
    unfold max at 1.
    rewrite -> (plus_0_r 1).
    unfold beq_nat at 1.
    reflexivity.

    (* Show that the counter-example is ordered *)
    unfold hbta_unsound_but_ordered.
    unfold is_ordered_hbta.
    unfold is_ordered_list.
    unfold flatten_hbta.
    rewrite ->
            (unfold_flatten_hbta_helper_node
               A nil 3 (ALeaf A) (ALeaf A) a1).
    rewrite -> (unfold_flatten_hbta_helper_leaf A nil).
    rewrite ->
            (unfold_flatten_hbta_helper_leaf
               A (a1 :: nil)).
    rewrite ->
            (unfold_is_ordered_cons_nil
               A a1 nil f).
    reflexivity.
Qed.

(* Sanity check: the independence of soundness and orderedness holds for integers *)
Proposition independence_of_soundness_and_orderedness_hbta_nat: 
    (exists (hbta : heightened_binary_tree_alternative nat)
            (cmp : nat -> nat -> comparison),
        (is_sound_hbta nat hbta = true) /\ (is_ordered_hbta nat hbta cmp = false))
    /\
    (exists (hbta : heightened_binary_tree_alternative nat)
            (cmp : nat -> nat -> comparison),
        (is_sound_hbta nat hbta = false) /\ (is_ordered_hbta nat hbta cmp = true)).
Proof.
  Check (independence_of_soundness_and_orderedness_hbta nat).
  apply (independence_of_soundness_and_orderedness_hbta nat).
  exists compare_int.
  exists 1.
  exists 2.
  unfold compare_int.
  unfold ltb.
  unfold beq_nat.
  reflexivity.
Qed.

(* ***** *)

(* ***** Section 3.4.3: Independence of balancedness and orderedness  ***** *)

(* Tackle this section after clarifying with professor Danvy if the notion of an 
 * ordering has been correctly captured *) 

(* ***** *)

(* ********** *)

(* ********** Section 4 : The lookup operation in AVL trees ********** *)

(* ***** Section 4.1: Implementations of occurs for both AVL trees type ***** *) 

(* Function to recursively traverse heightened_binary_tree_alternative and check if 
 * a given element occurs *)
Fixpoint occurs_hbta
         (A : Type)
         (compare : A -> A -> comparison)
         (e : A)
         (hbta : heightened_binary_tree_alternative A) :=
  match hbta with
  | ALeaf =>
    false
  | ANode _ hbta1 e' hbta2 =>
    match compare e e' with
    | Lt =>
      occurs_hbta A compare e hbta1
    | Eq =>
      true
    | Gt =>
      occurs_hbta A compare e hbta2
    end
  end.

(* Unfold lemmeas for occurs_hbta *)
Lemma unfold_occurs_hbta_leaf:
  forall (A : Type)
         (cmp : A -> A -> comparison)
         (e : A),
    occurs_hbta A cmp e (ALeaf A) = false.
Proof.
  unfold_tactic occurs_hbta.
Qed. 

Lemma unfold_occurs_hbta_node:
  forall (A : Type)
         (compare : A -> A -> comparison)
         (e e' : A)
         (h : nat)
         (hbta1 hbta2 : heightened_binary_tree_alternative A),
    occurs_hbta A compare e (ANode A h hbta1 e' hbta2) =
    match compare e e' with
    | Lt =>
      occurs_hbta A compare e hbta1
    | Eq =>
      true
    | Gt =>
      occurs_hbta A compare e hbta2
    end.
Proof.
  unfold_tactic occurs_hbta.
Qed.

(* ***** Section 4.2: Formal specification and associated theorems for lookup ***** *)









