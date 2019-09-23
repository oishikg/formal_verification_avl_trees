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

(* Unfold lemmas for ltb *)
Lemma unfold_ltb_0_0:
  ltb 0 0 = false.
Proof.
  unfold_tactic ltb.
Qed.

Lemma unfold_ltb_0_Sm:
  forall (m : nat),
    ltb 0 (S m) = true.
Proof.
  unfold_tactic ltb.
Qed.

Lemma unfold_ltb_Sn_0:
  forall (n : nat),
    ltb (S n) 0 = false.
Proof.        
  unfold_tactic ltb.
Qed.

Lemma unfold_ltb_Sn_Sm:
  forall (n m : nat),
    ltb (S n) (S m) = ltb n m.
Proof.    
  unfold_tactic ltb.
Qed.

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

(* Capturing transitivity of comparison functions *)
Axiom transitivity_of_comparisons:
  forall (A : Type)
         (x y z : A)
         (compare : A -> A -> comparison)
         (r : comparison), 
    compare x y = r ->
    compare y z = r ->
    compare x z = r.

Definition compare_int (i j : nat) : comparison := 
  if i <n j then Lt else if i =n= j then Eq else Gt.

(* A custom option type to handle three possible output values *)
Inductive triple_option (A : Type) : Type := 
| TError : triple_option A
| TNone : triple_option A
| TSome : A -> triple_option A.


Axiom tsome_x_equal_tsome_y:
  forall (A : Type)
         (x y : A),
    TSome A x = TSome A y <-> x = y.

Axiom pairwise_equality:
  forall (A : Type)
         (x1 x2 y1 y2 : A),
    (x1, x2) = (y1, y2) <-> x1 = y1 /\ x2 = y2.

Axiom some_x_equal_some_y:
  forall (A : Type)
         (x y : A),
    Some x = Some y <-> x = y.

Lemma diff_equal_0_implies_equal:
  forall (x y : nat),
    x - y = 0 -> x = y.
Proof.
Admitted.
(* figure this out *)

Lemma diff_equal_1_implies_greater_by_1:
  forall (x y : nat),
    x - y = 1 -> x = y + 1.
Proof.
Admitted.

Lemma or_implication:
  forall (A B C : Prop),
    ((A \/ B) -> C) -> ((A -> C) /\ (B -> C)).
Proof. 
  intros A B C H_abc.
  split.
  - intro H_a.
    apply H_abc.
    Search (_ \/ _).
    Check (or_introl).
    apply (or_introl).
    exact H_a.
  - intro H_b.
    apply H_abc.
    apply (or_intror).
    exact H_b.
Qed.

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


         

(* ********** *)



(* ********** Section 3: The invariant properties of AVL trees ********** *)

(* ***** 3.1: Soundness ***** *)

(* This property requires that the height stored in each node of an AVL Tree is
 *  accurate *) 

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
         (compare : A -> A -> comparison) : triple_option (A * A) :=
  match hbt with
  | HNode h bt =>
    traverse_to_check_ordered_bt A bt compare
  end
with traverse_to_check_ordered_bt
       (A : Type)
       (bt : binary_tree A)
       (compare : A -> A -> comparison) : triple_option (A * A) :=
       match bt with
       | Leaf =>
         TNone (A * A)
       | Node t =>
         traverse_to_check_ordered_t A t compare
       end
with traverse_to_check_ordered_t
       (A : Type)
       (t : triple A)
       (compare : A -> A -> comparison) : triple_option (A * A) :=
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
         (compare : A -> A -> comparison),
    traverse_to_check_ordered_hbt A (HNode A h bt) compare =
    traverse_to_check_ordered_bt A bt compare. 
Proof.
  unfold_tactic traverse_to_check_ordered_hbt.
Qed.             

Lemma unfold_traverse_to_check_ordered_bt_leaf:
  forall (A : Type)
         (compare : A -> A -> comparison),
    traverse_to_check_ordered_bt A (Leaf A) compare =
    TNone (A * A).
Proof.
  unfold_tactic traverse_to_check_ordered_bt.
Qed.             

Lemma unfold_traverse_to_check_ordered_bt_node:
  forall (A : Type)
         (t : triple A) 
         (compare : A -> A -> comparison),
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
         (compare : A -> A -> comparison),
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
           (compare : A -> A -> comparison) : bool :=
  match traverse_to_check_ordered_hbt A hbt compare with
  | TError =>
    false
  | _ =>
    true
  end.
                  

(* ***** *)

(* ********** *)

(* ********** Section 4 : The lookup operation in AVL trees ********** *)

(* ***** Section 4.1: Implementations of occurs for both AVL trees type ***** *) 

(* Function to traverse hbt and check if an element occurs *)
Fixpoint occurs_hbt
         (A : Type)
         (compare : A -> A -> comparison)
         (e : A)
         (hbt : heightened_binary_tree A) : bool :=
  match hbt with
  | HNode h bt =>
    occurs_bt A compare e bt
  end
with occurs_bt
       (A : Type)
       (compare : A -> A -> comparison)
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
       (compare : A -> A -> comparison)
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
         (compare : A -> A -> comparison)
         (e : A)
         (h : nat)
         (bt : binary_tree A),
    occurs_hbt A compare e (HNode A h bt) = occurs_bt A compare e bt.
Proof.
  unfold_tactic occurs_hbt.
Qed.

Lemma unfold_occurs_bt_leaf: 
  forall (A : Type)
         (compare : A -> A -> comparison)
         (e : A),
    occurs_bt A compare e (Leaf A) = false.
Proof.
  unfold_tactic occurs_bt.
Qed.

Lemma unfold_occurs_bt_node:
  forall (A : Type)
         (compare : A -> A -> comparison)
         (e : A)
         (t : triple A),
    occurs_bt A compare e (Node A t) = occurs_t A compare e t.
Proof.  
  unfold_tactic occurs_bt.
Qed.

Lemma unfold_occurs_t:
  forall (A : Type)
         (compare : A -> A -> comparison)
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


(* ***** Section 4.2: Formal specification and associated theorems for lookup ***** *)

(* The specification *)
Definition specification_of_occurs_hbt
           (A : Type)
           (compare : A -> A -> comparison)
           (occ_hbt : forall (A' : Type),
               (A' -> A' -> comparison)
               -> A'
               -> heightened_binary_tree A'
               -> bool) :=
  forall (e : A)
         (h : nat) 
         (bt : binary_tree A),
  exists (occ_bt : forall (A' : Type),
             (A' -> A' -> comparison) -> A' -> binary_tree A' -> bool),
    occ_hbt A compare e (HNode A h bt) = occ_bt A compare e bt.

Definition specification_of_occurs_bt 
           (A : Type)
           (compare : A -> A -> comparison)
           (occ_bt : forall (A' : Type),
               (A' -> A' -> comparison)
               -> A'
               -> binary_tree A'
               -> bool) :=
  (forall (e : A),
      occ_bt A compare e (Leaf A) = false)
  /\
  (forall (e : A)
          (t : triple A),
      exists (occ_t : forall (A' : Type),
                 (A' -> A' -> comparison) -> A' -> triple A' -> bool),
        occ_bt A compare e (Node A t) = occ_t A compare e t).

Definition specification_of_occurs_t
           (A : Type)
           (compare : A -> A -> comparison)
           (occ_t : forall (A' : Type),
               (A' -> A' -> comparison)
               -> A'
               -> triple A'
               -> bool) :=
  forall (e e' : A)
         (hbt1 hbt2 : heightened_binary_tree A),
    exists (occ_hbt : forall (A' : Type),
               (A' -> A' -> comparison)
               -> A'
               -> heightened_binary_tree A'
               -> bool),
      occ_t A compare e (Triple A hbt1 e' hbt2) =
      match compare e e' with
      | Lt =>
        occ_hbt A compare e hbt1
      | Eq =>
        true
      | Gt =>
        occ_hbt A compare e hbt2
      end.
                
(* Theorem for the soundness of the specification *)
Theorem there_is_only_one_occurs:
  forall (A : Type)
         (compare : A -> A -> comparison), 
    (forall (hbt : heightened_binary_tree A)
            (e : A)
            (occ_hbt1 occ_hbt2 : forall (A' : Type),
                (A' -> A' -> comparison)
                -> A'
                -> heightened_binary_tree A'
                -> bool),
        specification_of_occurs_hbt A compare occ_hbt1 ->
        specification_of_occurs_hbt A compare occ_hbt2 ->
        occ_hbt1 A compare e hbt = occ_hbt2 A compare e hbt)
    /\
    (forall (bt : binary_tree A)
            (e : A)
            (occ_bt1 occ_bt2 : forall (A' : Type),
                (A' -> A' -> comparison)
                -> A'
                -> binary_tree A'
                -> bool),
        specification_of_occurs_bt A compare occ_bt1 ->
        specification_of_occurs_bt A compare occ_bt2 ->
        occ_bt1 A compare e bt = occ_bt2 A compare e bt)
    /\
    (forall (t : triple A)
            (e : A)
            (occ_t1 occ_t2 : forall (A' : Type),
                (A' -> A' -> comparison)
                -> A'
                -> triple A'
                -> bool),
        specification_of_occurs_t A compare occ_t1 ->
        specification_of_occurs_t A compare occ_t2 ->
        occ_t1 A compare e t = occ_t2 A compare e t).
Proof. 
  intros A compare.
  apply heightened_binary_tree_mutual_induction.
  - intros h bt bt_ind_hyp.
    intros e occ_hbt1 occ_hbt2 spec_hbt1 spec_hbt2.
    unfold specification_of_occurs_hbt in spec_hbt1.
    unfold specification_of_occurs_hbt in spec_hbt2.
    destruct (spec_hbt1 e h bt) as [occ_bt_hyp1 hyp1].
    destruct (spec_hbt2 e h bt) as [occ_bt_hyp2 hyp2].
    rewrite -> hyp1.
    rewrite -> hyp2.
    apply (bt_ind_hyp e occ_bt_hyp1 occ_bt_hyp2).
Abort. 
  
    

(* Theorem to show that occurs_hbt, occurs_bt, and occurs_t meet their respective 
 * specifications *) 
Theorem occurs_implementation_satisfies_its_specification:
  forall (A : Type)
         (compare : A -> A -> comparison),
  (specification_of_occurs_hbt A compare occurs_hbt)
  /\
  (specification_of_occurs_bt A compare occurs_bt)
  /\
  (specification_of_occurs_t A compare occurs_t).
Proof.    
  intros A compare.
  split. 

  - unfold specification_of_occurs_hbt.
    intros e h bt.
    exists occurs_bt.
    reflexivity.

  - split.
    unfold specification_of_occurs_bt.
    split.
    intro e.
    rewrite -> (unfold_occurs_bt_leaf A compare e).
    reflexivity.
    intros e t.
    exists occurs_t.
    Check (unfold_occurs_bt_node).
    rewrite -> (unfold_occurs_bt_node A compare e t).
    reflexivity.

    unfold specification_of_occurs_t.
    intros e e' hbt1 hbt2.
    exists occurs_hbt.
    Check (unfold_occurs_t).
    rewrite -> (unfold_occurs_t A compare e e' hbt1 hbt2).
    reflexivity.
Qed.

(* Finish the heightened_binary_tree_alternative proofs later *)


(* ********** Section 5: The insert operation on trees ********** *)

(* ***** Section 5.1: Tests  ***** *)

(* Helper function to check the equality of lists *) 
Fixpoint equal_lists
         (A : Type)
         (compare : A -> A -> comparison)
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
         (compare : A -> A -> comparison)
         (hbt1 hbt2 : heightened_binary_tree A) : bool := 
  equal_lists A compare (hbt_to_list A hbt1) (hbt_to_list A hbt2).

(* Function to insert a list of values into a heightened_binary_tree *)
Fixpoint insert_list
         (A : Type)
         (insert : forall (A' : Type),
             (A' -> A' -> comparison)
             -> A'
             -> heightened_binary_tree A'
             -> heightened_binary_tree A')
         (compare : A -> A -> comparison)
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
               (A' -> A' -> comparison)
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

Definition foo x := 
  match x =n= 3 with
  | true => Some 4
  | false => None
  end.
 



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
         (compare : A -> A -> comparison)
         (x : A) 
         (hbt : heightened_binary_tree A) :=
  match hbt with
  | HNode h bt =>
    insert_bt_helper A compare x h bt
  end
with insert_bt_helper
       (A : Type)
       (compare : A -> A -> comparison)
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
       (compare : A -> A -> comparison)
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
         (compare : A -> A -> comparison)
         (x : A)
         (h : nat)
         (bt : binary_tree A),
    insert_hbt_helper A compare x (HNode A h bt) = insert_bt_helper A compare x h bt.
Proof.
  unfold_tactic insert_hbt_helper.
Qed.

Lemma unfold_insert_bt_helper_leaf:
  forall (A : Type)
         (compare : A -> A -> comparison)
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
         (compare : A -> A -> comparison)
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
         (compare : A -> A -> comparison)
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
  unfold_tactic insert_t_helper.
Qed.

Definition insert_hbt
         (A : Type)
         (compare : A -> A -> comparison)
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

(* ***** Section 5.3: The specifications  ***** *)

Definition specification_of_insert_hbt_helper
           (A : Type)
           (compare : A -> A -> comparison)
           (x : A)
           (insert_hbt_helper : forall (A' : Type),
               (A' -> A' -> comparison)
               -> A'
               -> heightened_binary_tree A'
               -> option (heightened_binary_tree A')) :=
  forall (hbt hbt' : heightened_binary_tree A),
    is_sound_hbt A hbt = true ->
    is_balanced_hbt A hbt = true ->
    is_ordered_hbt A hbt compare = true -> 
    insert_hbt_helper A compare x hbt = Some hbt' ->
    (is_sound_hbt A hbt' = true)
    /\ 
    (is_balanced_hbt A hbt' = true)
    /\
    (is_ordered_hbt A hbt' compare = true).


Definition specification_of_insert_bt_helper 
           (A : Type)
           (compare : A -> A -> comparison)
           (x : A)
           (insert_bt_helper : forall (A' : Type),
               (A' -> A' -> comparison)
               -> A'
               -> nat
               -> binary_tree A'
               -> option (heightened_binary_tree A')) :=
  forall (bt : binary_tree A)
         (h_hbt : nat)
         (hbt' : heightened_binary_tree A),
    is_sound_hbt A (HNode A h_hbt bt) = true ->
    is_balanced_hbt A (HNode A h_hbt bt) = true ->
    is_ordered_hbt A (HNode A h_hbt bt) compare = true ->
    insert_bt_helper A compare x h_hbt bt = Some hbt' ->
    (is_sound_hbt A hbt' = true)
    /\
    (is_balanced_hbt A hbt' = true)
    /\
    (is_ordered_hbt A hbt' compare = true).

Definition specification_of_insert_t_helper
           (A : Type)
           (compare : A -> A -> comparison)
           (x : A)
           (insert_t_helper : forall (A' : Type),
               (A' -> A' -> comparison)
               -> A'
               -> nat
               -> triple A'
               -> option (heightened_binary_tree A')) :=
  forall (t : triple A)
         (h_hbt : nat)
         (hbt' : heightened_binary_tree A),
    is_sound_hbt A (HNode A h_hbt (Node A t)) = true ->
    is_balanced_hbt A (HNode A h_hbt (Node A t)) = true ->
    is_ordered_hbt A (HNode A h_hbt (Node A t)) compare = true ->
    insert_t_helper A compare x h_hbt t = Some hbt' ->
    (is_sound_hbt A hbt' = true)
    /\
    (is_balanced_hbt A hbt' = true)
    /\
    (is_ordered_hbt A hbt' compare = true).

(* ***** *)

(* ***** Section 5.4: Lemmas concerning soundness ***** *)

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
  case (h_ret =n= h) as [ | ] eqn : C_equal_heights.
  Check (beq_nat_true).
  apply (beq_nat_true h_ret h) in C_equal_heights.
  rewrite <- C_equal_heights in H.
  exact H.

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
  unfold is_sound_hbt.
  rewrite ->
          (unfold_traverse_to_check_soundness_hbt
             A
             h_hbt
             (Node A (Triple A hbt1 e hbt2))).
  rewrite ->
          (unfold_traverse_to_check_soundness_bt_node
             A
             (Triple A hbt1 e hbt2)).
  rewrite -> (unfold_traverse_to_check_soundness_t A hbt1 hbt2 e).
  unfold is_sound_hbt in H_hbt1.

  case (traverse_to_check_soundness_hbt A hbt1) as [h1_ret | ] eqn : C_check_hbt1.
  case (traverse_to_check_soundness_hbt A hbt2) as [h2_ret | ] eqn : C_check_hbt2.
  (* the proof shouldn't be too hard from here on; return to this later *)
Admitted.

(* ***** *)

(* ***** Section 5.5: Balancedness lemmas ***** *)

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
  (* same structure as above, write later *)
Admitted.

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
  case (h_ret =n= h_given) as [ | ] eqn : C_equal_heights.
  apply (beq_nat_true h_ret h_given) in C_equal_heights.  
  apply (some_x_equal_some_y nat h_given h) in H_traverse_sound.
  exact H_traverse_sound.

  discriminate.

  discriminate.
Qed.

(* Essential lemma to related height differences between 2 trees and the 
 * differ_by_one defintion *)  
Lemma relating_compare_int_and_differ_by_one:
  forall (ha hb : nat),
    ((compare_int (ha - hb) 2 = Lt)
    \/
    (compare_int (hb - ha) 2 = Lt))
    ->
    differ_by_one ha hb = true.
Proof.
  intros ha hb [H_ab | H_ba].
  
  - unfold compare_int in H_ab.
    case (ha - hb) as [ | hd] eqn : C_height_diff.
    
    + unfold differ_by_one.
      apply (diff_equal_0_implies_equal ha hb) in C_height_diff.
      rewrite -> C_height_diff.
      Check (beq_nat_refl hb).
      rewrite <- (beq_nat_refl hb).
      Check (orb_true_r ((hb =n= hb + 1) || (hb =n= hb + 1))).
      exact (orb_true_r ((hb =n= hb + 1) || (hb =n= hb + 1))).
    
    + case hd as [ | hd'] eqn : C_height_diff_succ.
      unfold differ_by_one.
      Check (diff_equal_1_implies_greater_by_1).
      apply (diff_equal_1_implies_greater_by_1 ha hb) in C_height_diff.
      rewrite -> C_height_diff.
      rewrite <- (beq_nat_refl (hb + 1)).
      Search (true || _ = _).
      exact (orb_true_l ((hb =n= hb + 1 + 1) || (hb =n= hb + 1))).
      
      rewrite -> (unfold_ltb_Sn_Sm (S hd') 1) in H_ab.
      rewrite -> (unfold_ltb_Sn_Sm hd' 0) in H_ab.
      case hd' as [ | hd''].
      rewrite -> (unfold_ltb_0_0) in H_ab.
      unfold beq_nat in H_ab.
      discriminate.

      rewrite -> (unfold_ltb_Sn_0 hd'') in H_ab.
      unfold beq_nat in H_ab.
      discriminate.
      
  - unfold compare_int in H_ba.
    case (hb - ha) as [ | hd] eqn : C_height_diff.
    
    + unfold differ_by_one.
      apply (diff_equal_0_implies_equal hb ha) in C_height_diff.
      rewrite -> C_height_diff.
      rewrite <- (beq_nat_refl ha).
      Check (orb_true_r ((hb =n= ha + 1) || (ha =n= ha + 1))).
      exact (orb_true_r ((ha =n= ha + 1) || (ha =n= ha + 1))).
    
    + case hd as [ | hd'] eqn : C_height_diff_succ.
      unfold differ_by_one.
      Check (diff_equal_1_implies_greater_by_1).
      apply (diff_equal_1_implies_greater_by_1 hb ha) in C_height_diff.
      rewrite -> C_height_diff.
      rewrite <- (beq_nat_refl (ha + 1)).
      Search (true || _ = _).
      rewrite -> (orb_true_r (ha =n= ha + 1 + 1)).
      rewrite -> (orb_true_l (ha + 1 =n= ha)).
      reflexivity.
      
      rewrite -> (unfold_ltb_Sn_Sm (S hd') 1) in H_ba.
      rewrite -> (unfold_ltb_Sn_Sm hd' 0) in H_ba.
      case hd' as [ | hd''].
      rewrite -> (unfold_ltb_0_0) in H_ba.
      unfold beq_nat in H_ba.
      discriminate.

      rewrite -> (unfold_ltb_Sn_0 hd'') in H_ba.
      unfold beq_nat in H_ba.
      discriminate.
Qed.

(* The most important lemma for balancedness: it provides the conditions for which
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
      ((compare_int ((project_height_hbt A hbt1) - (project_height_hbt A hbt2))
                   2 = Lt)
      \/
      (compare_int ((project_height_hbt A hbt2) - (project_height_hbt A hbt1))
                   2 = Lt)) ->
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

(* ***** *)

(* ***** Section 5.6: Lemmas for orderedness ***** *)
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
Admitted.

Lemma insertion_implies_leaf: 
  forall (A : Type)
         (compare : A -> A -> comparison)
         (hbt : heightened_binary_tree A)
         (hbt' : heightened_binary_tree A)
         (x min' max' : A),
    insert_hbt_helper A compare x hbt = Some hbt' ->
    traverse_to_check_ordered_hbt A hbt' compare = TSome (A * A) (min', max') ->
    traverse_to_check_ordered_hbt A hbt compare = TNone (A * A) ->
    min' = x /\ max' = x.
Proof.
  intros A compare hbt hbt' x min' max' H_insert H_hbt' H_hbt.

  induction hbt as [h bt].
  
  assert (H_form_of_bt: bt = (Leaf A)).
  rewrite -> (unfold_traverse_to_check_ordered_hbt A h bt compare) in H_hbt.
  case bt as [ | t] eqn : C_bt.
  reflexivity.
  rewrite -> (unfold_traverse_to_check_ordered_bt_node A t compare) in H_hbt.
  case t as [hbt1 e hbt2].
  rewrite -> (unfold_traverse_to_check_ordered_t A hbt1 e hbt2 compare) in H_hbt. 
  case (traverse_to_check_ordered_hbt A hbt1 compare) as [ | | (min1, max1)] eqn : C_ord_hbt1.
  discriminate.
  case (traverse_to_check_ordered_hbt A hbt2 compare) as [ | | (min2, max2)] eqn : C_ord_hbt2.
  discriminate.
  discriminate.
  case (compare e min2) as [ | | ] eqn : C_comp_e_min2.
  discriminate.
  discriminate.
  discriminate.
  case (compare max1 e) as [ | | ] eqn : C_comp_e_min1.
  case (traverse_to_check_ordered_hbt A hbt2 compare) as [ | | (min2, max2)] eqn : C_ord_hbt2.
  discriminate.
  discriminate.
  case (compare e min2) as [ | | ] eqn : C_comp_e_min2.
  discriminate.
  discriminate.
  discriminate.
  discriminate.
  discriminate.

  rewrite -> H_form_of_bt in H_insert.
  rewrite -> (unfold_insert_hbt_helper A compare x h (Leaf A)) in H_insert.
  rewrite -> (unfold_insert_bt_helper_leaf A compare x h) in H_insert.
  rewrite ->  some_x_equal_some_y in H_insert.
  rewrite <- H_insert in H_hbt'.
  rewrite ->
          (unfold_traverse_to_check_ordered_hbt
             A
             1
             (Node A (Triple A (HNode A 0 (Leaf A)) x (HNode A 0 (Leaf A))))
             compare) in H_hbt'.
  rewrite ->
          (unfold_traverse_to_check_ordered_bt_node
             A
             (Triple A (HNode A 0 (Leaf A)) x (HNode A 0 (Leaf A)))) in H_hbt'.
  rewrite ->
          (unfold_traverse_to_check_ordered_t
             A
             (HNode A 0 (Leaf A))
             x
             (HNode A 0 (Leaf A))) in H_hbt'.
  rewrite -> (unfold_traverse_to_check_ordered_hbt A 0 (Leaf A) compare) in H_hbt'.
  rewrite -> (unfold_traverse_to_check_ordered_bt_leaf A compare) in H_hbt'.
  rewrite -> (tsome_x_equal_tsome_y (A * A) (x, x) (min', max')) in H_hbt'.
  apply (pairwise_equality A x x min' max') in H_hbt'.
  destruct H_hbt' as [G1 G2].
  split.

  rewrite -> G1.
  reflexivity.
  
  rewrite -> G2.
  reflexivity.
Qed.



Lemma insertion_impossible_case:
  forall (A : Type)
         (compare : A -> A -> comparison)
         (x : A) 
         (hbt0 : heightened_binary_tree A)
         (hbt'' : heightened_binary_tree A),
    insert_hbt_helper A compare x hbt0 = Some hbt'' ->
    traverse_to_check_ordered_hbt A hbt'' compare <> TNone (A * A).
Proof.                                                                    
    intros A compare x  hbt0 hbt'' H_ins.
    unfold not.
    induction hbt'' as [h'' bt''].
    rewrite -> (unfold_traverse_to_check_ordered_hbt A h'' bt'' compare).
    case bt'' as [ | t''].
    
    induction hbt0 as [h0 bt0].
    rewrite -> (unfold_insert_hbt_helper A compare x h0 bt0) in H_ins.
    case bt0 as [ | t0].
    rewrite -> (unfold_insert_bt_helper_leaf A compare) in H_ins.
    discriminate.
    induction t0 as [ hbt01 e0 hbt02].
    rewrite -> (unfold_insert_bt_helper_node A compare x h0 (Triple A hbt01 e0 hbt02))
      in H_ins.
    rewrite -> (unfold_insert_t_helper A compare x h0 hbt01 e0 hbt02) in H_ins.
    case (compare x e0) as [ | | ] eqn : C_comp_x_e0.
    case (insert_hbt_helper A compare x hbt01) as [ hbt01_ret | ]  eqn : C_ins_hbt01.
    induction hbt01_ret as [h01_ret bt_01_ret].
    case (compare_int (h01_ret - project_height_hbt A hbt02) 2)
         as [ | | ] eqn : C_h_diff.
    rewrite -> (some_x_equal_some_y
                  (heightened_binary_tree A)
                  (HNode A (1 + max h01_ret (project_height_hbt A hbt02))
                         (Node A (Triple A (HNode A h01_ret bt_01_ret) e0 hbt02)))
                  (HNode A h'' (Leaf A))) in H_ins.
    discriminate.
    unfold rotate_right_hbt in H_ins.
    induction hbt02 as [h02 bt02]. 
    unfold rotate_right_bt in H_ins.
    case (bt_01_ret) as [ t01 | ].
    discriminate.
    induction t as [ hbt011 e01 hbt012].
    induction hbt011 as [h011 bt011].
    induction hbt012 as [h012 bt012].
    case (h011 + 1 =n= h012) as [ | ].
    case bt012 as [ | t012].
    discriminate.
    induction t012 as [ hbt0121 e012 hbt0122 ].
    induction hbt0121 as [ h0121 bt0121 ].
    induction hbt0122 as [ h0122 bt0122 ].
    rewrite -> some_x_equal_some_y in H_ins.
    discriminate.
    case (h012 + 1 =n= h011) as [ | ].
    rewrite -> some_x_equal_some_y in H_ins.
    discriminate.
    discriminate.
    discriminate.
    discriminate.
    discriminate.
    
    case (insert_hbt_helper A compare x hbt02) as [hbt02_ret | ].
    induction hbt02_ret as [h02_ret bt02_ret].
    case (compare_int (h02_ret - project_height_hbt A hbt01) 2) as [ | | ].
    rewrite -> some_x_equal_some_y in H_ins.
    discriminate.
    unfold rotate_left_hbt in H_ins.
    induction hbt01 as [h01 bt01].
    unfold rotate_left_bt in H_ins.
    case bt02_ret as [ | t02].
    discriminate.
    induction t02 as [hbt021 e2 hbt022].
    induction hbt021 as [h021 bt021].
    induction hbt022 as [h022 bt022].
    case (h022 + 1 =n= h021) as [ | ].
    case bt021 as [ | t021 ].
    discriminate.
    induction t021 as [hbt0211 e21 hbt0212].
    induction hbt0211 as [h0211 bt0211].
    induction hbt0212 as [h0212 bt0212].
    rewrite -> some_x_equal_some_y in H_ins.
    discriminate.
    case (h021 + 1 =n= h022) as [ | ].
    rewrite -> some_x_equal_some_y in H_ins.
    discriminate.
    discriminate.
    discriminate.
    discriminate.

    intro H_check_ord.
    rewrite -> (unfold_traverse_to_check_ordered_bt_node A t'' compare)
      in H_check_ord.
    induction t'' as [hbt1'' e hbt2''].
    rewrite -> (unfold_traverse_to_check_ordered_t A hbt1'' e hbt2'' compare)
      in H_check_ord.
    case (traverse_to_check_ordered_hbt A hbt1'' compare) as [ | | (min1, max1)].
    discriminate.
    case (traverse_to_check_ordered_hbt A hbt2'' compare) as [ | | (min2, max2)].
    discriminate.
    discriminate.
    case (compare e min2) as [ | | ].
    discriminate.
    discriminate.
    discriminate.
    case (compare max1 e) as [ | | ].
    case (traverse_to_check_ordered_hbt A hbt2'' compare) as [ | | (min2, max2)].
    discriminate.
    discriminate.
    case (compare e min2) as [ | | ].
    discriminate.
    discriminate.
    discriminate.
    discriminate.
    discriminate.
Qed.

Lemma insertion_impossible_case_implies_true:
  forall (A : Type)
         (hbt hbt' : heightened_binary_tree A)
         (compare : A -> A -> comparison)
         (x : A)
         (P : Prop),
    insert_hbt_helper A compare x hbt = Some hbt' ->
    traverse_to_check_ordered_hbt A hbt' compare = TNone (A * A) ->
    P.
Proof.
  intros A hbt hbt' compare x P H_insertion H_traverse.
  induction hbt' as [h' bt'].
  assert (H_impossible_case : 
            traverse_to_check_ordered_hbt A (HNode A h' bt')  compare <>
            TNone (A * A)).
    exact (insertion_impossible_case
             A
             compare x hbt (HNode A h' bt')
             H_insertion).
    unfold not in H_impossible_case.
    assert (H_false : False).
    exact (H_impossible_case H_traverse).
    exact (False_ind
             P
             H_false).
Qed.
    
Lemma rotate_left_1:
  forall (A : Type)
         (compare : A -> A -> comparison)
         (h11' h121' h122' h2 h1' h12': nat)
         (bt11' bt121' bt122' bt2 : binary_tree A)
         (e1 e12 e t_min' t_max' : A), 
         traverse_to_check_ordered_hbt
         A
         (HNode A
                (1 + max (1 + max h11' h121') (1 + max h122' h2))
                (Node A
                      (Triple A
                              (HNode A (1 + max h11' h121')
                                     (Node A (Triple A
                                                     (HNode A h11' bt11')
                                                     e1
                                                     (HNode A h121' bt121'))))
                              e12
                              (HNode A (1 + max h122' h2)
                                     (Node A (Triple A
                                                     (HNode A h122' bt122')
                                                     e
                                                     (HNode A h2 bt2)))))))
         compare =
         TSome (A * A) (t_min', t_max') ->
         exists t_max'', 
         traverse_to_check_ordered_hbt
           A
           (HNode A h1'
                  (Node A
                        (Triple A (HNode A h11' bt11') e1
                                (HNode A h12'
                                       (Node A
                                             (Triple A
                                                     (HNode A h121' bt121')
                                                     e12
                                                     (HNode A h122' bt122')))))))
           compare = TSome (A * A) (t_min', t_max'').
Proof.
  intros. 

  Ltac quick_unfold :=
    rewrite -> (unfold_traverse_to_check_ordered_hbt);
    rewrite -> (unfold_traverse_to_check_ordered_bt_node);
    rewrite -> (unfold_traverse_to_check_ordered_t).
  quick_unfold.
  - do 2 (rewrite -> (unfold_traverse_to_check_ordered_hbt) in H;
          rewrite -> (unfold_traverse_to_check_ordered_bt_node) in H;
          rewrite -> (unfold_traverse_to_check_ordered_t) in H).
  case (traverse_to_check_ordered_hbt A (HNode A h11' bt11') compare)
    as [ | | (min11', max11')] eqn : C_check_ord_hbt11'.
  
  discriminate.

  case (traverse_to_check_ordered_hbt A (HNode A h121' bt121') compare)
    as [ | | (min121', max121')] eqn : C_check_ord_hbt121'.

  discriminate.
  case (compare e1 e12) as [ | | ] eqn : C_comp_e1_e12.
  rewrite -> (unfold_traverse_to_check_ordered_hbt) in H.
  rewrite -> (unfold_traverse_to_check_ordered_bt_node) in H.
  rewrite -> (unfold_traverse_to_check_ordered_t) in H.
  case (traverse_to_check_ordered_hbt A (HNode A h122' bt122') compare)
    as [ | | (min122', max122')] eqn : C_check_ord_hbt122'.
  discriminate.
  case (traverse_to_check_ordered_hbt A (HNode A h2 bt2) compare)
    as [ | | (min2, max2)] eqn : C_check_ord_hbt2.
  discriminate.
  case (compare e12 e) as [ | | ] eqn : C_comp_e12_e. 

  quick_unfold.
  rewrite -> C_check_ord_hbt121'.
  rewrite -> C_check_ord_hbt122'.  
  rewrite -> C_comp_e1_e12.
  exists e12.
  rewrite -> tsome_x_equal_tsome_y in H.
  rewrite ->  pairwise_equality in H.
  destruct H as [H_e1 _].
  rewrite <- H_e1.
  reflexivity.

  discriminate.

  discriminate.

  case (compare e min2) as [ | | ] eqn : C_comp_e_min2.
  case (compare e12 e) as [ | | ] eqn : C_comp_e12_e.
  rewrite -> (unfold_traverse_to_check_ordered_hbt); 
  rewrite -> (unfold_traverse_to_check_ordered_bt_node);
  rewrite -> (unfold_traverse_to_check_ordered_t).
  rewrite -> C_check_ord_hbt121'.
  rewrite -> C_check_ord_hbt122'.
  rewrite -> C_comp_e1_e12.
  exists e12.
  rewrite -> tsome_x_equal_tsome_y in H.
  rewrite ->  pairwise_equality in H.
  destruct H as [H_e1 _].
  rewrite <- H_e1.
  reflexivity.

  discriminate.

  discriminate.

  discriminate.

  discriminate.

  case (compare max122' e) as [ | | ] eqn : C_comp_max122'_e.
  case (traverse_to_check_ordered_hbt A (HNode A h2 bt2) compare) as
      [ | | (min2, max2)] eqn : C_check_ord_hbt2.
  discriminate.

  case (compare e12 min122') as [ | | ] eqn : C_comp_e12_min122'.
  rewrite -> (unfold_traverse_to_check_ordered_hbt); 
  rewrite -> (unfold_traverse_to_check_ordered_bt_node);
  rewrite -> (unfold_traverse_to_check_ordered_t).
  rewrite -> C_check_ord_hbt121'.
  rewrite -> C_check_ord_hbt122'.
  rewrite -> C_comp_e12_min122'.
  rewrite -> C_comp_e1_e12.
  exists max122'.
  rewrite -> tsome_x_equal_tsome_y in H;
  rewrite ->  pairwise_equality in H;
  destruct H as [H_e1 _];
  rewrite <- H_e1;
  reflexivity.

  discriminate.

  discriminate.

  case (compare e min2) as [ | | ] eqn : C_comp_e_min2.
  case (compare e12 min122') as [ | | ] eqn : C_comp_e12_min122'.
  quick_unfold.
  rewrite -> C_check_ord_hbt121'.
  rewrite -> C_check_ord_hbt122'.
  rewrite -> C_comp_e12_min122'.
  rewrite -> C_comp_e1_e12.
  exists max122'.
  rewrite -> tsome_x_equal_tsome_y in H;
  rewrite ->  pairwise_equality in H;
  destruct H as [H_e1 _];
  rewrite <- H_e1;
  reflexivity.

  discriminate.

  discriminate.

  discriminate.

  discriminate.

  discriminate.

  discriminate.

  discriminate.

  discriminate.


  rewrite -> (unfold_traverse_to_check_ordered_hbt); 
  rewrite -> (unfold_traverse_to_check_ordered_bt_node);
  rewrite -> (unfold_traverse_to_check_ordered_t).
  rewrite -> C_check_ord_hbt121'.
  rewrite -> (unfold_traverse_to_check_ordered_hbt) in H. 
  rewrite -> (unfold_traverse_to_check_ordered_bt_node) in H.
  rewrite -> (unfold_traverse_to_check_ordered_t) in H.
  case (traverse_to_check_ordered_hbt A (HNode A h122' bt122') compare)
       as [ | | (min122', max122')] eqn : C_check_ord_hbt122'.
  case (compare e1 min121') as [ | | ] eqn : C_comp_e1_min121.
  case (compare max121' e12) as [ | | ] eqn : C_comp_max121'_e12.
  discriminate.

  discriminate.

  discriminate.
    
  discriminate.
  
  discriminate.

   case (compare e1 min121') as [ | | ] eqn : C_comp_e1_min121'.
   case (traverse_to_check_ordered_hbt A (HNode A h2 bt2) compare)
     as [ | | (min2, max2)] eqn : C_comp_min2_max2.
   case (compare max121' e12) as [ | | ] eqn : C_comp_max121'_e12.
  discriminate.

  discriminate.

  discriminate.

  case (compare max121' e12) as [ | | ] eqn : C_comp_max121'_e12.
  case (compare e12 e) as [ | | ] eqn : C_comp_e12_e.
  rewrite -> C_comp_e1_min121'.
  exists e12.
  rewrite -> tsome_x_equal_tsome_y in H;
  rewrite ->  pairwise_equality in H;
  destruct H as [H_e1 _];
  rewrite <- H_e1;
  reflexivity.

  discriminate.

  discriminate.

  discriminate.

  discriminate.

  case (compare max121' e12) as [ | | ] eqn : C_comp_max121'_e12.
  case (compare e min2) as [ | | ] eqn : C_comp_e_min2.
  case (compare e12 e) as [ | | ] eqn : C_comp_e12_e.
  rewrite -> C_comp_e1_min121'.
  exists e12.
  rewrite -> tsome_x_equal_tsome_y in H;
  rewrite ->  pairwise_equality in H;
  destruct H as [H_e1 _];
  rewrite <- H_e1;
  reflexivity.

  discriminate.

  discriminate.

  discriminate.

  discriminate.
  
  discriminate.

  discriminate.

  discriminate.

  discriminate.

  case (compare e1 min121') as [ | | ] eqn : C_comp_e1_min121'.
  case (compare max121' e12) as [ | | ] eqn : C_comp_max121'_e12.
  case (compare max122' e) as [ | | ] eqn : C_comp_max122'_e.
  case (traverse_to_check_ordered_hbt A (HNode A h2 bt2) compare) as
      [ | | (min2, max2)] eqn : C_check_ord_hbt2.
  
  discriminate.
  
  case (compare e12 min122') as [ | | ] eqn : C_comp_e12_min122'.
  rewrite -> C_comp_e1_min121'.
  exists max122'.
  rewrite -> tsome_x_equal_tsome_y in H;
  rewrite ->  pairwise_equality in H;
  destruct H as [H_e1 _];
  rewrite <- H_e1;
  reflexivity.

  discriminate.
  
  discriminate.

  case (compare e min2) as [ | | ] eqn : C_comp_e_min2.
  case (compare e12 min122') as [ | | ] eqn : C_comp_e12_min122'.
  rewrite -> C_comp_e1_min121'.
  exists max122'.
    rewrite -> tsome_x_equal_tsome_y in H;
  rewrite ->  pairwise_equality in H;
  destruct H as [H_e1 _];
  rewrite <- H_e1;
  reflexivity.

  discriminate.
  
  discriminate.

  discriminate.

  discriminate.
  
  discriminate.

  discriminate.

  discriminate.
  
  discriminate.

  discriminate.
 
  discriminate.
  (* this proof is exploding in size! *)
Admitted.



Lemma insertion_implies_node:
  forall (A : Type)
         (compare : A -> A -> comparison),
    (forall (hbt : heightened_binary_tree A)
            (hbt' : heightened_binary_tree A)
            (x min min' max max' : A),
        insert_hbt_helper A compare x hbt = Some hbt' ->
        traverse_to_check_ordered_hbt A hbt' compare = TSome (A * A) (min', max') ->
        traverse_to_check_ordered_hbt A hbt compare = TSome (A * A) (min, max) ->
        (max' = x \/ max' = max) /\ (min' = x \/ min' = min))
    /\
    (forall (bt : binary_tree A)
            (h : nat)
            (hbt' : heightened_binary_tree A)
            (x min min' max max' : A),
        insert_bt_helper A compare x h bt = Some hbt' ->
        traverse_to_check_ordered_hbt A hbt' compare = TSome (A * A) (min', max') ->
        traverse_to_check_ordered_bt A bt compare = TSome (A * A) (min, max) ->
        (max' = x \/ max' = max) /\ (min' = x \/ min' = min))
    /\
    (forall (t : triple A)
            (h : nat)
            (hbt' : heightened_binary_tree A)
            (x min min' max max' : A),
        insert_t_helper A compare x h t = Some hbt' ->
        traverse_to_check_ordered_hbt A hbt' compare = TSome (A * A) (min', max') ->
        traverse_to_check_ordered_t A t compare = TSome (A * A) (min, max) ->
        (max' = x \/ max' = max) /\ (min' = x \/ min' = min)).
Proof.    
  intros A compare.
  apply heightened_binary_tree_mutual_induction.

  (* proof for hbt, with bt as inductive hypothesis *)
  intros h bt H_ind_bt hbt' x min min' max max' H_insert_hbt H_ord_hbt' H_ord_hbt.
  rewrite -> (unfold_insert_hbt_helper A compare x h bt) in H_insert_hbt.
  rewrite -> (unfold_traverse_to_check_ordered_hbt A h bt compare) in H_ord_hbt.
  Check (H_ind_bt h hbt' x min min' max max' H_insert_hbt H_ord_hbt' H_ord_hbt).
  exact (H_ind_bt h hbt' x min min' max max' H_insert_hbt H_ord_hbt' H_ord_hbt).

  (* a leaf provides a vacuous case *)
  intros h  hbt' x min min' max max' H_insert_hbt H_ord_hbt' H_ord_hbt.
  rewrite -> (unfold_traverse_to_check_ordered_bt_leaf A compare) in H_ord_hbt.
  discriminate.

  (* proof for node, with t as inductive hypothesis *)
  intros t H_ind_t h hbt' x min min' max max' H_insert_bt H_ord_hbt' H_ord_bt.
  rewrite -> (unfold_insert_bt_helper_node A compare x h t) in H_insert_bt.
  rewrite -> (unfold_traverse_to_check_ordered_bt_node A t compare) in H_ord_bt.
  Check (H_ind_t h hbt' x min min' max max' H_insert_bt H_ord_hbt' H_ord_bt).
  exact (H_ind_t h hbt' x min min' max max' H_insert_bt H_ord_hbt' H_ord_bt).

  (* proof for t, with inductive hypotheses for hbt1 and hbt2 *)
  intros hbt1 H_hbt1 e hbt2 H_hbt2 h hbt' x t_min t_min' t_max t_max'
         H_insert_hbt H_ord_hbt' H_ord_t. 
  
  (* the long and arduous journey into the insert function *)
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
          exact (insertion_implies_leaf
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
          exact (insertion_implies_leaf
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
    case (h11' + 1 =n= h12') as [ | ] eqn : C_h11'_h12'.

    (* h11' + 1 = h12' *)
    + case bt12' as [ | t12'].

      discriminate.

      induction t12' as [hbt121' e12 hbt122'].
      induction hbt121' as [h121' bt121'].
      induction hbt122' as [h122' bt122'].
      rewrite -> some_x_equal_some_y in H_insert_hbt. 
      rewrite <- H_insert_hbt in H_ord_hbt'.  

      assert (H_hbt_ret_original:
                exists t_max'', 
                  traverse_to_check_ordered_hbt
                    A
                    (HNode A h1'
                           (Node A
                                 (Triple A (HNode A h11' bt11') e1
                                         (HNode A h12'
                                                (Node A
                                                      (Triple A
                                                              (HNode A h121' bt121')
                                                              e12
                                                              (HNode A h122' bt122')))))))
                    compare = TSome (A * A) (t_min', t_max'')).
      exact (rotate_left_1 A
                           compare 
                           h11' h121' h122' h2 h1' h12'
                           bt11' bt121' bt122' bt2 
                           e1 e12 e t_min' t_max' H_ord_hbt').


      (* unfold traverse_to_check_ordered as much as possible *)  
      do 2 (rewrite -> (unfold_traverse_to_check_ordered_hbt) in H_ord_hbt';
            rewrite -> (unfold_traverse_to_check_ordered_bt_node) in H_ord_hbt';
            rewrite -> (unfold_traverse_to_check_ordered_t) in H_ord_hbt').
      case (traverse_to_check_ordered_hbt A (HNode A h11' bt11') compare)
           as [ | | (min11', max11')] eqn : C_check_ord_hbt11'.
      discriminate.
      case (traverse_to_check_ordered_hbt A (HNode A h121' bt121') compare)
           as [ | | (min121', max121')] eqn : C_check_ord_hbt121'.
      discriminate.
      case (compare e1 e12) as [ | | ] eqn : C_comp_e1_e12.
      rewrite -> (unfold_traverse_to_check_ordered_hbt) in H_ord_hbt';
        rewrite -> (unfold_traverse_to_check_ordered_bt_node) in H_ord_hbt';
        rewrite -> (unfold_traverse_to_check_ordered_t) in H_ord_hbt'.
      case (traverse_to_check_ordered_hbt A (HNode A h122' bt122') compare)
           as [ | | (min122', max122')] eqn : C_check_ord_hbt122.
      discriminate.
      case (traverse_to_check_ordered_hbt A (HNode A h2 bt2) compare)
        as [ | | (min2, max2)] eqn : C_check_ord_hbt2.
      discriminate.
      case (compare e12 e) as [ | | ] eqn : C_comp_e12_e.
(* this proof is going out of hand *)
Abort.



(* ***** *)
  
(* ***** 
        SECTION 5.7: The main theorem: implementations meet their specifications
 * *****)


Lemma the_helper_functions_meet_their_specifications:
  forall (A : Type)
         (compare : A -> A -> comparison)
         (x : A),
    (specification_of_insert_hbt_helper A compare x insert_hbt_helper)
    /\
    (specification_of_insert_bt_helper A compare x insert_bt_helper)
    /\
    (specification_of_insert_t_helper A compare x insert_t_helper).
Proof.
  intros A compare x.
  unfold specification_of_insert_hbt_helper.
  unfold specification_of_insert_bt_helper.
  unfold specification_of_insert_t_helper.
  apply heightened_binary_tree_mutual_induction.

  Focus 4.
    (* Specification for t holds, given hbt as inductive case *)
  {
    intros hbt1 H_hbt1_inductive_assumption
           e
           hbt2 H_hbt2_inductive_assumption
           h_hbt hbt'
           H_sound_t_init H_bal_t_init H_ord_t_init H_insert_t.
    Check (unfold_insert_t_helper).
    rewrite -> (unfold_insert_t_helper A compare x h_hbt hbt1 e hbt2)
      in H_insert_t.
    case (compare x e) as [ | | ] eqn : C_comp.

    (* Element to be inserted is Lt current element considered *)
    -  Check (unfold_insert_hbt_helper).
      case (insert_hbt_helper A compare x hbt1) as [hbt_ret | ] eqn : C_insert_hbt1.

      (* The element is succesfully inserted *)
       + induction hbt_ret as [h_ret bt_ret].
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
           
           (* Before working on the particular subgoals, assert some essential 
            * hypotheses *)
           destruct (triple_sound_implies_hbts_sound
                       A h_hbt hbt1 e hbt2 H_sound_t_init) as [H_hbt1_is_sound _].
           destruct (triple_balanced_implies_hbts_balanced
                       A h_hbt hbt1 e hbt2 H_bal_t_init) as [H_hbt1_is_balanced _].
           destruct (triple_ordered_implies_hbts_ordered
                       A compare h_hbt hbt1 e hbt2 H_ord_t_init)
             as [H_hbt1_is_ordered _].
           assert (P_some_eq : Some (HNode A h_ret bt_ret) =
                               Some (HNode A h_ret bt_ret)).
           reflexivity. 

           split.
           (* The resultant tree is sound *)
           {
             destruct (triple_sound_implies_hbts_sound
                         A h_hbt hbt1 e hbt2 H_sound_t_init) as [_ H_hbt2_is_sound].
             destruct (H_hbt1_inductive_assumption (HNode A h_ret bt_ret)
                                                   H_hbt1_is_sound
                                                   H_hbt1_is_balanced
                                                   H_hbt1_is_ordered
                                                   P_some_eq) as
                 [H_hbt_ret_is_sound [_ _]].
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

           split.

           (* The resultant tree is balanced *)
           {
             destruct (triple_balanced_implies_hbts_balanced
                         A h_hbt hbt1 e hbt2 H_bal_t_init)
               as [_ H_hbt2_is_balanced].
             destruct (triple_sound_implies_hbts_sound
                         A h_hbt hbt1 e hbt2 H_sound_t_init)
               as [_ H_hbt2_is_sound].
             destruct (H_hbt1_inductive_assumption (HNode A h_ret bt_ret)
                                                   H_hbt1_is_sound
                                                   H_hbt1_is_balanced
                                                   H_hbt1_is_ordered
                                                   P_some_eq) as
                 [_ [H_hbt_ret_is_balanced _]].
             destruct (H_hbt1_inductive_assumption (HNode A h_ret bt_ret)
                                                   H_hbt1_is_sound
                                                   H_hbt1_is_balanced
                                                   H_hbt1_is_ordered
                                                   P_some_eq) as
                 [H_hbt_ret_is_sound [_ _]].
             assert (H_hbts_balanced_triple_balanced_with_da:
                       compare_int (project_height_hbt A (HNode A h_ret bt_ret) -
                                    project_height_hbt A hbt2) 2 = Lt
                       \/
                       compare_int (project_height_hbt A hbt2 -
                                    project_height_hbt A (HNode A h_ret bt_ret)) 2 =
                       Lt ->
                       is_balanced_hbt
                         A
                         (HNode A (1 + max h_ret (project_height_hbt A hbt2))
                                (Node A (Triple A (HNode A h_ret bt_ret) e hbt2))) =
                       true).
             exact (hbts_balanced_implies_triple_balanced_weak
                      A
                      (1 + max h_ret (project_height_hbt A hbt2))
                      (HNode A h_ret bt_ret)
                      e
                      hbt2
                      H_hbt_ret_is_balanced
                      H_hbt2_is_balanced
                      H_hbt_ret_is_sound
                      H_hbt2_is_sound).
             destruct (or_implication
                         (compare_int
                            (project_height_hbt A (HNode A h_ret bt_ret) -
                             project_height_hbt A hbt2) 2 = Lt)
                         (compare_int
                            (project_height_hbt A hbt2 -
                             project_height_hbt A (HNode A h_ret bt_ret)) 2 = Lt)
                         (is_balanced_hbt
                            A
                            (HNode A (1 + max h_ret (project_height_hbt A hbt2))
                                   (Node A (Triple A (HNode A h_ret bt_ret) e hbt2)))
                          = true)
                         H_hbts_balanced_triple_balanced_with_da)
               as [H_we_need_12  H_we_need_21].
             exact (H_we_need_12 C_height_diff).
           }
           
           (* The resultant tree is ordered *)
           {
             unfold is_ordered_hbt in H_ord_t_init. 
             destruct (H_hbt1_inductive_assumption
                         (HNode A h_ret bt_ret)
                         H_hbt1_is_sound
                         H_hbt1_is_balanced
                         H_hbt1_is_ordered
                         P_some_eq) as [_ [_ H_hbt_ret_is_ordered]].
             destruct (triple_ordered_implies_hbts_ordered
                         A compare h_hbt hbt1 e hbt2 H_ord_t_init)
               as [_ H_hbt2_is_ordered].
             unfold is_ordered_hbt.
             rewrite ->
                     (unfold_traverse_to_check_ordered_hbt
                        A
                        (1 + max h_ret (project_height_hbt A hbt2))
                        (Node A (Triple A (HNode A h_ret bt_ret) e hbt2))).
             rewrite ->
                     (unfold_traverse_to_check_ordered_bt_node
                        A
                        (Triple A (HNode A h_ret bt_ret) e hbt2)).
             rewrite ->
                     (unfold_traverse_to_check_ordered_t
                        A
                        (HNode A h_ret bt_ret)
                        e
                        hbt2).
             unfold is_ordered_hbt in H_hbt_ret_is_ordered.
             unfold is_ordered_hbt in H_hbt2_is_ordered. 
             case (traverse_to_check_ordered_hbt A (HNode A h_ret bt_ret) compare)
               as [ | | (min_ret, max_ret)] eqn : C_traverse_ord_hbt_ret.
             
             (* the returned tree is unorderd : vacuous case *)
             discriminate.
             case (traverse_to_check_ordered_hbt A hbt2 compare)
               as [ | | (min2, max2)] eqn : C_traverse_ord_hbt2.
             discriminate.

             (* the returned tree is a leaf *)
             reflexivity. 
             rewrite ->
                     (unfold_traverse_to_check_ordered_hbt
                        A
                        h_hbt
                        (Node A (Triple A hbt1 e hbt2))) in H_ord_t_init.
             rewrite ->
                     (unfold_traverse_to_check_ordered_bt_node
                        A
                        (Triple A hbt1 e hbt2)) in H_ord_t_init.
             rewrite ->
                     (unfold_traverse_to_check_ordered_t
                        A
                        hbt1
                        e
                        hbt2) in H_ord_t_init.
             case (traverse_to_check_ordered_hbt A hbt1 compare)
                  as [ | | (max1, min1)] eqn : C_traverse_ord_hbt1.
             discriminate.
             rewrite -> C_traverse_ord_hbt2 in H_ord_t_init.
             case (compare e min2) as [ | | ] eqn : C_comp_e_min2.
             reflexivity.
             discriminate.
             discriminate.
             case (compare min1 e) as [ | | ] eqn : C_comp_e_min1.
             rewrite -> C_traverse_ord_hbt2 in H_ord_t_init.
             case (compare e min2) as [ | | ] eqn : C_comp_e_min2.
             reflexivity.
             discriminate.
             discriminate.
             discriminate.
             discriminate.

             (* we need some lemma that related the max value in the 
              * returned sub tree with e; see
              * the lemma insert_implies_node above *)
Abort.


  (* (* Specification for hbt holds, given bt as inductive case *) *)
  (* { *)
  (*   intros h bt H_bt_inductive_assumption hbt' H_sound_hbt_init  *)
  (*          H_bal_hbt_init H_ord_hbt_init H_insert_hbt. *)
  (*   split. *)
  (*   Check (H_bt_inductive_assumption h hbt' H_sound_hbt_init H_bal_hbt_init H_ord_hbt_init H_insert_hbt). *)
  (*   destruct (H_bt_inductive_assumption h hbt' H_sound_hbt_init H_bal_hbt_init H_ord_hbt_init H_insert_hbt) as [H_sound _]. *)
  (*   exact H_sound. *)

  (*   split. *)
  (*   destruct (H_bt_inductive_assumption h hbt' H_sound_hbt_init H_bal_hbt_init H_ord_hbt_init H_insert_hbt) as [_ [H_bal _]]. *)
  (*   exact H_bal. *)
    
  (*   destruct (H_bt_inductive_assumption h hbt' H_sound_hbt_init H_bal_hbt_init H_ord_hbt_init H_insert_hbt) as [_ [_ H_ord]]. *)
  (*   exact H_ord. *)
  (* } *)

  
  (* (* Specification for bt leaf constructor holds *) *)
  (* { *)
  (*   intros h_hbt hbt' H_sound_bt_init H_bal_bt_init H_ord_bt_init H_insert_bt. *)
  (*   rewrite -> (unfold_insert_bt_helper_leaf A compare x) *)
  (*     in H_insert_bt. *)
  (*   rewrite  *)
  (*           (some_x_equal_some_y *)
  (*              (heightened_binary_tree A) *)
  (*                  (HNode A 1 *)
  (*                     (Node A *)
  (*                           (Triple A  *)
  (*                                   (HNode A 0 (Leaf A)) x  *)
  (*                                   (HNode A 0 (Leaf A))))) *)
  (*                             hbt' *)
  (*           ) in H_insert_bt. *)
  (*   rewrite <- H_insert_bt. *)
     
  (*   (* prove soundness *) *)
  (*   - split. *)
  (*     unfold is_sound_hbt. *)
  (*     Check (unfold_traverse_to_check_soundness_hbt). *)
  (*     rewrite -> *)
  (*             (unfold_traverse_to_check_soundness_hbt *)
  (*                A *)
  (*                1 *)
  (*                (Node A (Triple A (HNode A 0 (Leaf A)) x (HNode A 0 (Leaf A))))). *)
  (*     Check (unfold_traverse_to_check_soundness_bt_node). *)
  (*     rewrite -> *)
  (*             (unfold_traverse_to_check_soundness_bt_node *)
  (*                A *)
  (*                (Triple A (HNode A 0 (Leaf A)) x (HNode A 0 (Leaf A)))). *)
  (*     Check (unfold_traverse_to_check_soundness_t). *)
  (*     rewrite -> *)
  (*             (unfold_traverse_to_check_soundness_t *)
  (*                A *)
  (*                (HNode A 0 (Leaf A)) *)
  (*                (HNode A 0 (Leaf A)) *)
  (*                x). *)
  (*     rewrite -> *)
  (*             (unfold_traverse_to_check_soundness_hbt *)
  (*                A *)
  (*                0 *)
  (*                (Leaf A)). *)
  (*     Check (unfold_traverse_to_check_soundness_bt_leaf). *)
  (*     rewrite -> (unfold_traverse_to_check_soundness_bt_leaf A).  *)
  (*     unfold beq_nat at 1. *)
  (*     unfold beq_nat at 1.     *)
  (*     unfold max at 1. *)
  (*     Search (_ + 0 = _). *)
  (*     rewrite -> (plus_0_r 1) at 1. *)
  (*     unfold beq_nat at 1. *)
  (*     reflexivity. *)

  (*     split. *)
      
  (*     (* prove balancedness *) *)
  (*     + unfold is_balanced_hbt. *)
  (*       Check (unfold_traverse_to_check_balanced_hbt). *)
  (*       rewrite -> *)
  (*               (unfold_traverse_to_check_balanced_hbt *)
  (*                  A *)
  (*                  1 *)
  (*                  (Node A (Triple A (HNode A 0 (Leaf A)) x (HNode A 0 (Leaf A))))). *)
  (*       Check (unfold_traverse_to_check_balanced_bt_node). *)
  (*       rewrite -> *)
  (*               (unfold_traverse_to_check_balanced_bt_node *)
  (*                  A *)
  (*                  (Triple A (HNode A 0 (Leaf A)) x (HNode A 0 (Leaf A)))). *)
  (*       Check (unfold_traverse_to_check_balanced_t). *)
  (*       rewrite -> *)
  (*               (unfold_traverse_to_check_balanced_t *)
  (*                  A *)
  (*                  (HNode A 0 (Leaf A)) *)
  (*                  (HNode A 0 (Leaf A)) *)
  (*                  x). *)
  (*       rewrite -> *)
  (*               (unfold_traverse_to_check_balanced_hbt *)
  (*                  A *)
  (*                  0 *)
  (*                  (Leaf A)). *)
  (*       rewrite -> (unfold_traverse_to_check_balanced_bt_leaf A).  *)
  (*       unfold differ_by_one. *)
  (*       rewrite -> (plus_0_l 1). *)
  (*       unfold beq_nat. *)
  (*       unfold max. *)
  (*       rewrite -> (plus_0_r 1). *)
  (*       (* why does the boolean statement not evaluate here? *) *)
  (*       reflexivity. *)

  (*   (* show orderedness *) *)
  (*     + unfold is_ordered_hbt. *)
  (*       unfold is_ordered_list. *)
  (*       Check (unfold_hbt_to_list). *)
  (*       rewrite -> *)
  (*               (unfold_hbt_to_list *)
  (*                  A *)
  (*                  1 *)
  (*                  (Node A (Triple A (HNode A 0 (Leaf A)) x (HNode A 0 (Leaf A))))). *)
  (*       Check (unfold_bt_to_list_node). *)
  (*       rewrite -> *)
  (*               (unfold_bt_to_list_node *)
  (*                  A *)
  (*                  (Triple A (HNode A 0 (Leaf A)) x (HNode A 0 (Leaf A)))). *)
  (*       Check (unfold_t_to_list). *)
  (*       rewrite -> *)
  (*               (unfold_t_to_list *)
  (*                  A *)
  (*                  (HNode A 0 (Leaf A)) *)
  (*                  (HNode A 0 (Leaf A)) *)
  (*                  x). *)
  (*       rewrite -> *)
  (*               (unfold_hbt_to_list *)
  (*                  A *)
  (*                  0 *)
  (*                  (Leaf A)). *)
  (*       rewrite -> (unfold_bt_to_list_leaf A). *)
  (*       Search (nil ++ _ = _). *)
  (*       rewrite -> (app_nil_l (x :: nil)). *)
  (*       unfold is_ordered_cons. *)
  (*       reflexivity. *)
  (* } *)
  
  (* (* Specification for bt with node constructor holds, given t as inductive case *) *)
  (* {  *)
  (*   intros t H_t_inductive_assumption h_hbt hbt' H_sound_bt_init *)
  (*          H_bal_bt_init H_ord_bt_init H_insert_bt. *)
  (*   exact (H_t_inductive_assumption h_hbt hbt' H_sound_bt_init H_bal_bt_init *)
  (*                                   H_ord_bt_init H_insert_bt). *)
  (* } *)


    

  (* } *)


        

Definition specifiction_of_insert_hbt
           (A : Type)
           (compare : A -> A -> comparison)
           (x : A)
           (insert_hbt : forall (A' : Type),
               (A' -> A' -> comparison)
               -> A'
               -> heightened_binary_tree A'
               -> heightened_binary_tree A') :=
  forall (hbt : heightened_binary_tree A),
    (is_sound_hbt A hbt = true) ->
    (is_balanced_hbt A hbt = true) ->
    (is_ordered_hbt A hbt compare = true) -> 
    (is_sound_hbt A (insert_hbt A compare x hbt) = true)
    /\
    (is_balanced_hbt A (insert_hbt A compare x hbt) = true)
    /\
    (is_ordered_hbt A (insert_hbt A compare x hbt) compare = true).


Theorem insert_hbt_satisfies_its_specification: 
  forall (A : Type)
         (compare : A -> A -> comparison)
         (x : A),
    specifiction_of_insert_hbt A compare x insert_hbt.
Proof.          
  intros A compare.  
  unfold specifiction_of_insert_hbt.
  intros x hbt H_sound_init H_bal_init H_order_init.
  unfold insert_hbt.
  (* destruct (the_helper_functions_meet_their_specifications A compare x) as [H_hbt [_ _]]. *)
  
  unfold specification_of_insert_hbt_helper in H_hbt.
  case (insert_hbt_helper A compare x hbt) as [ hbt' | ] eqn : C.
  apply (H_hbt hbt hbt').
  exact C.

  split.
  exact H_sound_init.
  split.
  exact H_bal_init.
  exact H_order_init.
Qed.







         




