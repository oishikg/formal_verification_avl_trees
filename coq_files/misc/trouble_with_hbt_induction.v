(* Fri Sep 24 2019 *)

(* Paraphernalia: *)
 
Ltac unfold_tactic name := intros; unfold name; (* fold name; *) reflexivity.

Require Import Arith Bool List. 

(* Equality of natural numbers *)
Notation "A =n= B" :=
  (beq_nat A B) (at level 70, right associativity).

(* Equality of boolean values *) 
Notation "A =b= B" :=
  (eqb A B) (at level 70, right associativity).

(* Coq formalization of polymorphic AVL tree type *) 
Inductive heightened_binary_tree (A : Type) : Type :=
  HNode : nat -> binary_tree A -> heightened_binary_tree A 
with binary_tree (A : Type) : Type :=
     | Leaf : binary_tree A
     | Node : triple A -> binary_tree A 
with triple (A : Type) : Type :=
     | Triple : heightened_binary_tree A -> A -> heightened_binary_tree A -> triple A.

(* Now we check the induction principle that is defined by coq *)
Check (heightened_binary_tree_ind).

(* The result is as follows: 

 heightened_binary_tree_ind : forall (A : Type) (P : heightened_binary_tree A -> Prop),
       (forall (n : nat) (b : binary_tree A), P (HNode A n b)) ->
       forall h : heightened_binary_tree A, P h 

*)

(* The issue is, the induction principle does not make any reference to th subtrees of h,
 * because the subtrees are wrapped by two layers of constructors (namely, those of 
 * the binary_tree type, and that of the triple type. However, all of our inductive proofs
 * involving this type require inductive hypotheses on the subtrees. Thus we proceed to 
 * define our own induction principle as follows: *) 


(* Defining an induction principle for heightened_binary_tree *)
Lemma hbt_induction_principle:
  forall (A : Type)
         (P : heightened_binary_tree A -> Prop),
    (forall (h : nat),
        P (HNode A h (Leaf A))) ->
    (forall (h : nat)
            (hbt1 : heightened_binary_tree A)
            (e : A)
            (hbt2 : heightened_binary_tree A),
        P hbt1 -> P hbt2 -> P (HNode A h (Node A (Triple A hbt1 e hbt2)))) ->
    forall (hbt : heightened_binary_tree A),
      P hbt.  
Proof.
  intros A P H_leaf H_node hbt.
  induction hbt as [h bt].
  induction bt as [| tr].
  exact (H_leaf h).
  induction tr as [hbt1 e hbt2].
  
  apply (H_node h hbt1 e hbt2).
  (* And now our subgoals are exactly the goals we wanted to prove! *)
Abort.

(* Question: How should we prove this induction principle? *)
