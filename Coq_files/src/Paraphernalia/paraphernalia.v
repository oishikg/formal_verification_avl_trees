Ltac unfold_tactic name := intros; unfold name; (* fold name; *) reflexivity.

Require Import Arith Bool List.

Require Export Arith Bool List.

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
Inductive element_comparison :=
| Lt : element_comparison
| Eq : element_comparison
| Gt : element_comparison.

(* Capturing transitivity of comparison functions *)
Axiom transitivity_of_comparisons:
  forall (A : Type)
         (x y z : A)
         (compare : A -> A -> element_comparison)
         (r : element_comparison), 
    compare x y = r ->
    compare y z = r ->
    compare x z = r.

Axiom relating_lt_gt:
  forall (A : Type)
         (x y : A)
         (compare : A -> A -> element_comparison),
    compare x y = Lt <-> compare y x = Gt. 

Definition compare_int (i j : nat) : element_comparison := 
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