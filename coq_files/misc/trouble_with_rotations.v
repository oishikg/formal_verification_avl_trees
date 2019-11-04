(* Question about rotations *)

(* 14th Oct, 2019 *)

(* ********** Paraphernalia ********** *)
Require Import Arith Bool List.

Inductive heightened_binary_tree (A : Type) : Type := 
  HNode : nat -> binary_tree A -> heightened_binary_tree A 
with binary_tree (A : Type) : Type :=
     | Leaf : binary_tree A
     | Node : triple A -> binary_tree A 
with triple (A : Type) : Type :=
     | Triple : heightened_binary_tree A -> A -> heightened_binary_tree A -> triple A.

Ltac unfold_tactic name := intros; unfold name; (* fold name; *) reflexivity.

(* Equality of natural numbers *)
Notation "A =n= B" :=
  (beq_nat A B) (at level 70, right associativity).

(* Equality of boolean values *) 
Notation "A =b= B" :=
  (eqb A B) (at level 70, right associativity).

(* ********** Implementation of rotations ********** *)

(* This is the implementation I am currently using: it consider the 3 finite cases, which are
 * the only ones which should occur if hbt1 is balanced; in all other cases, we would usually
 * raise an exception in OCaml. Since there are no exceptions in Coq, I have been using the
 * option type instead. *)
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

(* The alternative would be as follows: *)
Definition rotate_right_bt_alt
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
      Some (HNode A
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
  end.

(* To prove theorems involving rotate_right_bt_alt, we would naturally have to first prove 
 * some lemma that enumerates the 3 possibile equations involving h11 and h12 (assuming that
 * hbt1 is balanced). Then, when working on the else case, we would use this lemma to obtain
 * the following as a hypothesis: h11 = h12 || h12 + 1 = h11 *)

(* My question the following: which approach is preferable? 
 *
 * (i) The one where the code itself captures the notion that the tree passed to it should
 * be balanced, and therefore considers only the 3 cases (this is what the first
 * implementation does)
 * 
 * OR
 *
 * (ii) The alternative approach, where the code is only correct if the input tree is balanced
 * (and therefore requires the lemma I mention *)




