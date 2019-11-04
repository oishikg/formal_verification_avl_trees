(* for_oishik_continued.v *)
(* Singapore, Sat 24 Aug 2019 *)
(* was: *)
(* Singapore, Fri 23 Aug 2019 *)

(* ********** *)

Require Import List.

Check List.length.

(*
length
     : forall A : Type, list A -> nat
*)

Lemma giving_it_a_try :
  forall (A : Type)
         (a : A), (* <- guarantees that the type is not empty *)
    exists xs : list A,
      List.length xs = 1.
Proof.
  intros A a.
  exists (a :: nil).
  unfold length.
  reflexivity.
Qed.

(* ********** *)

(* more generally: *)

Lemma unneeded_quantification :
  forall (A : Type)
         (P : Type -> Prop),
    P A <-> (forall (a : A), P A).
Proof.
  intros A P.
  split.

  - intros H_PA H_A.
    exact H_PA.

  - intros H_impl.
    apply H_impl.
Abort.

(* The issue is not about the possible emptiness of the quantified type,
   it is a logical one:

     1 focused subgoal
     (unfocused: 0), subgoal 1 (ID 10)
       
       A : Type
       P : Type -> Prop
       ============================
       (A -> P A) -> P A

   Here, A could be False (which implies anything),
   and therefore the implication (A -> P A) does not imply P A.

   There is something silly here because the quantified variable is not used.
*)

Lemma more_silliness :
  forall (A : Type),
    True <-> (forall (a : A), True).
Proof.
  intro A.
  split.

  - intros H_True _.
    exact H_True.

  - intros _.
    reflexivity.
Qed.

Lemma even_more_silliness :
  forall (A : Type)
         (B : Prop),
    B <-> (forall (a : A), B).
Proof.
  (* Why is the forall treated as A -> B *) 
  intros A B.
  split.

  - intros H_B _.
    exact H_B.

  - intros H_AB.
    Abort. 
(*     reflexivity. *)
    (* Qed. *)

Lemma foo_bar :
  forall (A : Type)
         (a : A)
         (P : A -> A -> Prop),
    forall x : A, P a x. 
         
    





(* Conclusion:
   witness unneeded_quantification,
   what I suggested is to weaken your lemma
   (weakened in the sense that A -> B
   is a weaker version of B,
   since it requires A to hold in order for B to hold).

   Reference:
     https://en.wikipedia.org/wiki/Structural_rule
*)

(* ********** *)

(* end of for_oishik_continued.v *)
