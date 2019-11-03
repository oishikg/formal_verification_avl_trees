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


(* ********** *)

(* ********** Lemmas for operations on Peano nat numbers ********** *)

Lemma succ_eq:
  forall (a b : nat),
    S a = S b -> a = b.
Proof.
  intros; inversion H; reflexivity.
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


(* ********** Defining an ordering ********** *)

(* Type alias for the predefined inductive type compairson *)
Inductive element_comparison :=
| Lt : element_comparison
| Eq : element_comparison
| Gt : element_comparison.

(* Predicate to check if a compare function returns an Lt or Eq constructor; 
 * we use this to define a total order *)
Definition leq (ce : element_comparison) : bool :=
  match ce with
  | Lt =>
    true
  | Eq =>
    true
  | Gt =>
    false
  end.

Axiom relating_Eq_eq:
  forall (A : Type)
         (a b : A)
         (compare : A -> A -> element_comparison),
  compare a b = Eq <-> a = b.

(* See: https://en.wikipedia.org/wiki/Total_order *)

(* A compare function is anti-symmetric if it meets the following definition *)
Definition anti_symmetry 
           (A : Type)
           (a b : A)
           (compare : A -> A -> element_comparison) :=
    leq (compare a b) = true -> 
    leq (compare b a) = true ->
    compare a b = Eq.

(* A compare function is transitive if it meets the following definition *)
Definition transitivity 
           (A : Type)
           (a b c : A)
           (compare : A -> A -> element_comparison) :=
    leq (compare a b) = true -> 
    leq (compare b c) = true ->
    leq (compare a c) = true.

(* A compare function has the connexity property if it meets the following
 * definition *)
Definition connexity 
           (A : Type)
           (a b : A)
           (compare : A -> A -> element_comparison) := 
  leq (compare a b) = true 
  \/
  leq (compare b a) = true.

(* For a compare function of type A -> A -> element_comparison to define a total 
 * order on A, it should meet the following specification: *)
Definition specification_of_compare_defining_total_order
           (A : Type)
           (compare : A -> A -> element_comparison) :=
  forall (a b c : A),
    anti_symmetry A a b compare
    /\
    transitivity A a b c compare
    /\
    connexity A a b compare.

(* Now we derive the property of reflexivity for a compare function that defines 
 * a total order on a set A *)
Lemma reflexivity_total_order:
  forall (A : Type)
         (x : A)
         (compare : A -> A -> element_comparison),
    specification_of_compare_defining_total_order A compare -> 
    leq (compare x x) = true.
Proof.
  intros.
  unfold specification_of_compare_defining_total_order in H.
  destruct (H x x x) as [_ [_ H_conn]].
  unfold connexity in H_conn.
  destruct H_conn.
  exact H0.
  exact H0.
Qed.

(* An important lemma that relates the Gt and Lt constructor values *)
Lemma relating_Lt_Gt_total_order:
  forall (A : Type)
         (a b : A)
         (compare : A -> A -> element_comparison),
    specification_of_compare_defining_total_order A compare ->
    (compare a b = Lt <-> compare b a = Gt).
Proof.
  intros.
  
  assert (H_duplicate: specification_of_compare_defining_total_order A compare).
  exact H. 
  
  split.
  
  - intro.
    unfold specification_of_compare_defining_total_order in H.
    destruct (H a b b) as [H_anti_symm [H_trans H_conn]].
    unfold connexity in H_conn.
    rewrite -> H0 in H_conn.
    case (compare b a) as [ | | ] eqn : C_comp_ba.

    + unfold anti_symmetry in H_anti_symm.
      rewrite -> C_comp_ba in H_anti_symm.
      rewrite -> H0 in H_anti_symm.
      destruct H_conn.
      apply H_anti_symm in H1.
      discriminate.
      exact H1.
      apply H_anti_symm in H1.
      discriminate.
      exact H1.

    + unfold anti_symmetry in H_anti_symm.
      rewrite -> H0 in H_anti_symm.
      rewrite -> C_comp_ba in H_anti_symm.
      unfold leq in H_anti_symm.

      assert (H_trivial: true = true).
      reflexivity.

      apply H_anti_symm in H_trivial.
      discriminate.
      reflexivity.

    + reflexivity.

  - intro.
    unfold specification_of_compare_defining_total_order in H.
    destruct (H a b b) as [H_anti_symm [H_trans H_conn]].
    unfold connexity in H_conn.
    rewrite -> H0 in H_conn.
    case (compare a b) as [ | | ] eqn : C_comp_ba.

    + reflexivity.

    + destruct H_conn.

      * Check (relating_Eq_eq).
        destruct (relating_Eq_eq A a b compare).
        apply H2 in C_comp_ba.
        rewrite -> C_comp_ba in H0.
        
        Check (reflexivity_total_order A b compare H).
        assert (H_refl: leq (compare b b) = true).
        exact (reflexivity_total_order A b compare H).

        rewrite -> H0 in H_refl.
        unfold leq in H_refl.
        discriminate.

      * unfold leq in H1.
        discriminate.

    + unfold leq in H_conn.
      destruct H_conn.
      discriminate.
      discriminate.
Qed.




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

Lemma beq_nat_symm:
  forall (x y : nat),
    (x =n= y) = (y =n= x).
Proof.
  intros.
  
  case (x =n= y) as [ | ] eqn : C_xy.

  - apply beq_nat_true in C_xy.
    case (y =n= x) as [ | ] eqn : C_yx.
    reflexivity.

    apply beq_nat_false in C_yx.
    rewrite -> C_xy in C_yx.
    unfold not in C_yx.

    assert (H_trivial: y = y).
    reflexivity.

    apply C_yx in H_trivial.
    apply False_ind.

    exact H_trivial.

  - apply beq_nat_false in C_xy.
    unfold not in C_xy.
    case (y =n= x) as [ | ] eqn : C_yx.
    apply beq_nat_true in C_yx.
    symmetry in C_yx.
    apply C_xy in C_yx.
    apply False_ind.
    exact C_yx.
    reflexivity.
Qed.

Lemma disjunction_to_prop:
  forall (b1 b2 : bool),
    (b1 || b2 = true) -> (b1 = true) \/ (b2 = true).
Proof.
  intros.
  case b1 as [ | ].
  case b2 as [ | ].
  apply or_intror.
  reflexivity.
  apply or_introl.
  reflexivity.
  apply or_intror.
  Search (false || _ = _).
  rewrite -> (orb_false_l b2) in H.
  exact H.
Qed.

Lemma trivial_equality:
  forall (A : Type)
         (v : A),
    v = v.
Proof.
  intros; reflexivity.
Qed.

