Require Import Arith Bool List.
Require Export Arith Bool List.

(* ********** = and < operations ********** *)

Ltac unfold_tactic name := intros; unfold name; (* fold name; *) reflexivity.

(* Equality of natural numbers *)
Notation "A =n= B" :=
  (beq_nat A B) (at level 70, right associativity).

Lemma unfold_beq_nat_Sn_Sm:
  forall (n m : nat),
    beq_nat (S n) (S m) = beq_nat n m.
Proof.
  unfold_tactic beq_nat.
Qed.

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

(* Notation for "less than" *) 
Notation "A <n B" := (ltb A B) (at level 70, right associativity).

(* ********** *)

(* ********** Datatype for data comparison ********** *)

(* Paraphernalia for comparison: *)
Inductive element_comparison :=
| Lt : element_comparison
| Eq : element_comparison
| Gt : element_comparison.


Axiom relating_lt_gt:
  forall (A : Type)
         (x y : A)
         (compare : A -> A -> element_comparison),
    compare x y = Lt <-> compare y x = Gt.


Definition compare_int (i j : nat) : element_comparison := 
  if i <n j then Lt else if i =n= j then Eq else Gt.


(* ********** ********** *)
Lemma pairwise_equality:
  forall (A : Type)
         (x1 x2 y1 y2 : A),
    (x1, x2) = (y1, y2) <-> x1 = y1 /\ x2 = y2.
Proof.
  intros; split.
  intro.
  inversion H; split; reflexivity; reflexivity.
  intro.
  destruct H.
  rewrite -> H; rewrite -> H0; reflexivity.
Qed.  

Lemma some_x_equal_some_y:
  forall (A : Type)
         (x y : A),
    Some x = Some y <-> x = y.
Proof.
  intros; split.
  intro.
  inversion H; reflexivity.
  intro.
  rewrite -> H; reflexivity.
Qed.

(* ********** *)

(* ********** Lemmas for Max.max ********** *)

Lemma max_cases:
  forall (a b : nat),
    max a b = a \/ max a b = b.
Proof.
  intros.
  intros.
  case (le_ge_dec a b) as [ | ].
  - Search (max _ _ = _).
    right.
    exact (max_r a b l).
    
  - Search (max _ _ = _).
    
    assert (H: b <= a).
    auto.

    left.
    exact (max_l a b H).
Qed.    

Lemma unfold_max_Sn_Sm:
  forall (n m : nat),
    max (S n) (S m) = S (max n m).
Proof.
  unfold_tactic max.
Qed.

Lemma H_max_S:
  forall (a : nat),
    max (a + 1) a = a + 1.
Proof.                      
  intros.
  induction a as [ | a' IH_a'].
  rewrite -> plus_0_l.
  unfold max.
  reflexivity.
  
  Search (max _ _ = _).
  rewrite -> (plus_comm (S a') 1).
  Search (S _ = _).
  rewrite <- plus_n_Sm.
  rewrite -> unfold_max_Sn_Sm.
  rewrite -> plus_comm in IH_a'.
  rewrite -> IH_a'.
  reflexivity.
Qed.


(* ********** *)

(* ********** Lemmas for operations on Peano nat numbers ********** *)

Lemma succ_eq:
  forall (a b : nat),
    S a = S b -> a = b.
Proof.
  intros; inversion H; reflexivity.
Qed.

Lemma ltb_false_case:
  forall (a x : nat),
    (a + x <n a + x) = false.
Proof.
  intros.
  induction a as [ | a' IH_a'].

  Focus 2.
  Search (S _ + _ = _).
  rewrite -> plus_Sn_m.
  rewrite -> unfold_ltb_Sn_Sm.
  exact IH_a'.

  rewrite -> plus_0_l.
  induction x as [ | x' IH_x'].
  unfold ltb.
  reflexivity.

  rewrite -> unfold_ltb_Sn_Sm.
  exact IH_x'.
Qed.


Lemma add_to_both_sides:
  forall (x y z : nat),
    x = y -> x + z = y + z.
  intros.
  induction z as [ | z' IH_z'].
  rewrite -> plus_0_r.
  rewrite -> plus_0_r.
  exact H.

  rewrite <- plus_n_Sm.
  rewrite <- plus_n_Sm.
  rewrite -> IH_z'.
  reflexivity.
Qed.

Lemma minus_Sn_0:
  forall (n : nat),
    S n - 0 = S n.
Proof.
  unfold_tactic minus.
Qed.

Lemma minus_Sn_Sm:
  forall (n m : nat),
    S n - S m = n - m.
Proof.
  unfold_tactic minus.
Qed.

Lemma minus_n_0:
  forall (n : nat),
    n - 0 = n.
Proof.
  intros.
  case n as [ | n'].

  unfold minus.
  reflexivity.

  rewrite -> minus_Sn_0.
  reflexivity.
Qed.



Lemma prop_to_bool_helper:
  forall (a : nat),
    a = a -> ((a =n= a) = true).
Proof.
  intros.
  induction a as [ | a' IH_a].
  unfold beq_nat.
  reflexivity.
  
  rewrite -> unfold_beq_nat_Sn_Sm. 
  apply IH_a.
  exact (succ_eq a' a' H).
Qed.  

Lemma prop_to_bool:
  forall (a b : nat),
    a = b -> ((a =n= b) = true).
Proof.
  intros.
  induction a as [ | a' IH_a].
  case b as [ | b'].
  unfold beq_nat.
  reflexivity.
  discriminate.

  case b as [ | b'].
  discriminate.
  rewrite -> H.
  rewrite -> unfold_beq_nat_Sn_Sm.
  
  assert (H_trivial: b' = b').
  reflexivity.
  exact (prop_to_bool_helper b' H_trivial).
Qed.

