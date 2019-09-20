(* hbt_induction.v *)
(* Singapore, Fri 06 Sep 2019 *)

(* ********** *)

Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.

(* ********** *)

Inductive heightened_binary_tree (A : Set) : Set :=
  HNode : nat -> binary_tree A -> heightened_binary_tree A 
with binary_tree (A : Set) : Set :=
     | Leaf : binary_tree A
     | Node : triple A -> binary_tree A 
with triple (A : Set) : Set :=
     | Triple : heightened_binary_tree A -> A -> heightened_binary_tree A -> triple A.

(* This is the induction principle we want: *)

Lemma the_guy :
  forall (A : Set)
         (HBT : heightened_binary_tree A -> Prop)
         (BT : binary_tree A -> Prop)
         (T : triple A -> Prop),
       (forall (h : nat) (bt : binary_tree A),
           BT bt -> HBT (HNode A h bt)) ->
       BT (Leaf A) -> 
       (forall t : triple A,
           T t -> BT (Node A t)) ->
       (forall hbt1 : heightened_binary_tree A,
           HBT hbt1 ->
           forall (e : A)
                  (hbt2 : heightened_binary_tree A),
             HBT hbt2 ->
             T (Triple A hbt1 e hbt2)) ->
       (forall hbt : heightened_binary_tree A,
           HBT hbt)
       /\
       (forall bt : binary_tree A,
           BT bt)
       /\
       (forall t : triple A,
           T t).
Proof.
Admitted.

(* To wit: *)

Fixpoint mirror_heightened_binary_tree (A : Set) (hbt : heightened_binary_tree A) :=
  match hbt with
  | HNode h bt =>
    HNode A h (mirror_binary_tree A bt)
  end
with mirror_binary_tree (A : Set) (bt : binary_tree A) : binary_tree A :=
       match bt with
       | Leaf => 
         Leaf A
       | Node t =>
         Node A (mirror_triple A t)
       end
with mirror_triple (A : Set) (t : triple A) : triple A :=
       match t with
       | Triple hbt1 e hbt2 =>
         Triple A (mirror_heightened_binary_tree A hbt2) e (mirror_heightened_binary_tree A hbt1)
       end.

(* ***** *)

Lemma fold_unfold_mirror_heightened_binary_tree_HNode :
  forall (A : Set)
         (h : nat)
         (bt : binary_tree A),
    mirror_heightened_binary_tree A (HNode A h bt) =
    HNode A h (mirror_binary_tree A bt).
Proof.
  intros.
  unfold mirror_heightened_binary_tree.
  (* fold mirror_heightened_binary_tree. *)  
  reflexivity.
  fold_unfold_tactic mirror_heightened_binary_tree.
Qed.

Lemma fold_unfold_mirror_binary_tree_Leaf :
  forall A : Set,
    mirror_binary_tree A (Leaf A) =
    Leaf A.
Proof.
  fold_unfold_tactic mirror_binary_tree.
Qed.

Lemma fold_unfold_mirror_binary_tree_Node :
  forall (A : Set)
         (t : triple A),
    mirror_binary_tree A (Node A t) =
    Node A (mirror_triple A t).
Proof.
  fold_unfold_tactic mirror_binary_tree.
Qed.

Lemma fold_unfold_mirror_triple_Triple :
  forall (A : Set)
         (hbt1 : heightened_binary_tree A)
         (e : A)
         (hbt2 : heightened_binary_tree A),
    mirror_triple A (Triple A hbt1 e hbt2) =
    Triple A (mirror_heightened_binary_tree A hbt2) e (mirror_heightened_binary_tree A hbt1).
Proof.
  fold_unfold_tactic mirror_triple.
Qed.

(* ***** *)

Proposition mirroring_is_involutory :
  forall (A : Set),
    (forall hbt : heightened_binary_tree A,
        mirror_heightened_binary_tree A (mirror_heightened_binary_tree A hbt) = hbt)
    /\
    (forall bt : binary_tree A,
        mirror_binary_tree A (mirror_binary_tree A bt) = bt)
    /\
    (forall t : triple A,
        mirror_triple A (mirror_triple A t) = t).
Proof.
  intros A.
  apply the_guy.

  - intros h bt H_bt.
    rewrite -> fold_unfold_mirror_heightened_binary_tree_HNode.
    rewrite -> fold_unfold_mirror_heightened_binary_tree_HNode.
    rewrite -> H_bt.
    reflexivity.

  - rewrite -> fold_unfold_mirror_binary_tree_Leaf.
    reflexivity.

  - intros t H_t.
    rewrite -> fold_unfold_mirror_binary_tree_Node.
    rewrite -> fold_unfold_mirror_binary_tree_Node.
    rewrite -> H_t.
    reflexivity.

  - intros hbt1 H_hbt1 e hbt2 H_hbt2.
    rewrite -> fold_unfold_mirror_triple_Triple.
    rewrite -> fold_unfold_mirror_triple_Triple.
    rewrite -> H_hbt1.
    rewrite -> H_hbt2.
    reflexivity.
Qed.

(* ********** *)

(* And now for the Coq magic described at
     https://coq.inria.fr/refman/user-extensions/proof-schemes.html
*)

Scheme heightened_binary_tree_induction := Induction for heightened_binary_tree Sort Prop
  with binary_tree_induction := Induction for binary_tree Sort Prop
  with triple_induction := Induction for triple Sort Prop.

Combined Scheme heightened_binary_tree_mutual_induction from heightened_binary_tree_induction,binary_tree_induction,triple_induction.

Check heightened_binary_tree_mutual_induction.

(* ...which is the guy we want. *)

(* And indeed: *)

Proposition mirroring_is_involutory' :
  forall (A : Set),
    (forall hbt : heightened_binary_tree A,
        mirror_heightened_binary_tree A (mirror_heightened_binary_tree A hbt) = hbt)
    /\
    (forall bt : binary_tree A,
        mirror_binary_tree A (mirror_binary_tree A bt) = bt)
    /\
    (forall t : triple A,
        mirror_triple A (mirror_triple A t) = t).
Proof.
  intros A.
  apply heightened_binary_tree_mutual_induction.

  - intros h bt H_bt.
    rewrite -> fold_unfold_mirror_heightened_binary_tree_HNode.
    rewrite -> fold_unfold_mirror_heightened_binary_tree_HNode.
    rewrite -> H_bt.
    reflexivity.

  - rewrite -> fold_unfold_mirror_binary_tree_Leaf.
    reflexivity.

  - intros t H_t.
    rewrite -> fold_unfold_mirror_binary_tree_Node.
    rewrite -> fold_unfold_mirror_binary_tree_Node.
    rewrite -> H_t.
    reflexivity.

  - intros hbt1 H_hbt1 e hbt2 H_hbt2.
    rewrite -> fold_unfold_mirror_triple_Triple.
    rewrite -> fold_unfold_mirror_triple_Triple.
    rewrite -> H_hbt1.
    rewrite -> H_hbt2.
    reflexivity.
Qed.

(* ********** *)

(* end of hbt_induction.v *)
