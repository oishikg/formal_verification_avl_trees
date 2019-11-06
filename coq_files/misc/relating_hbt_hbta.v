(* Coq formalization of alternative polymorphic AVL tree type *)
Inductive heightened_binary_tree_alternative (A : Type) : Type :=
  | ALeaf : heightened_binary_tree_alternative A
  | ANode : nat -> heightened_binary_tree_alternative A -> A -> heightened_binary_tree_alternative A -> heightened_binary_tree_alternative A. 

Check (heightened_binary_tree_alternative_ind).

(* Recursive function to convert a heightened_binary_tree to an 
 * alternative_heightenels_binary_tree *)
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

