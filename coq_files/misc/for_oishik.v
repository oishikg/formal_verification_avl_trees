(* for_oishik.v *)
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

(* end of for_oishik.v *)
