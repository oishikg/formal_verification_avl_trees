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
           (compare : A -> A -> element_comparison) :=           
  forall (a b : A),
    leq (compare a b) = true -> 
    leq (compare b a) = true ->
    compare a b = Eq.

(* A compare function is transitive if it meets the following definition *)
Definition transitivity 
           (A : Type)
           (compare : A -> A -> element_comparison) :=
  forall (a b c : A),
    leq (compare a b) = true -> 
    leq (compare b c) = true ->
    leq (compare a c) = true.

(* A compare function has the connexity property if it meets the following
 * definition *)
Definition connexity 
           (A : Type)
           (compare : A -> A -> element_comparison) :=
  forall (a b : A),
    (leq (compare a b) = true)
    \/
    (leq (compare b a) = true).

(* For a compare function of type A -> A -> element_comparison to define a total 
 * order on A, it should meet the following specification: *)
Definition specification_of_compare_defining_total_order
           (A : Type)
           (compare : A -> A -> element_comparison) :=
  anti_symmetry A compare 
  /\
  transitivity A compare 
  /\
  connexity A compare.

(* Now we derive the property of reflexivity for a compare function that defines 
 * a total order on a set A *)
Lemma reflexivity_total_order:
  forall (A : Type)
         (compare : A -> A -> element_comparison)
         (x : A), 
    specification_of_compare_defining_total_order A compare -> 
    leq (compare x x) = true.
Proof.
  intros.
  unfold specification_of_compare_defining_total_order in H.
  destruct H as [_ [_ H_conn]].
  unfold connexity in H_conn.
  destruct (H_conn x x).
  exact H.
  exact H.
Qed.

(* An important lemma that relates the Gt and Lt constructor values *)
Lemma relating_Lt_Gt_total_order:
  forall (A : Type)
         (compare : A -> A -> element_comparison)
         (a b : A),
    specification_of_compare_defining_total_order A compare ->
    (compare a b = Lt <-> compare b a = Gt).
Proof.
  intros.
  
  assert (H_duplicate: specification_of_compare_defining_total_order A compare).
  exact H.

  unfold specification_of_compare_defining_total_order in H.
  destruct H as [H_anti_symm [H_trans H_conn]].
  
  unfold connexity in H_conn.
  assert (H_conn_quantified: leq (compare a b) = true \/ leq (compare b a) = true).
  exact (H_conn a b).

  unfold anti_symmetry in H_anti_symm.
  assert (H_anti_symm_quantified:
            leq (compare a b) = true -> leq (compare b a) = true ->
            compare a b = Eq).
  exact (H_anti_symm a b).
  
  split.
  
  - intro.
    rewrite -> H in H_conn_quantified.
    case (compare b a) as [ | | ] eqn : C_comp_ba.

    + (* rewrite -> C_comp_ba in H_anti_symm_quantified. *)
      rewrite -> H in H_anti_symm_quantified.
      destruct H_conn_quantified.
      apply H_anti_symm_quantified in H0.
      discriminate.
      exact H0.
      apply H_anti_symm_quantified in H0.
      discriminate.
      exact H0.

    + rewrite -> H in H_anti_symm_quantified.
      unfold leq in H_anti_symm_quantified.

      assert (H_trivial: true = true).
      reflexivity.

      apply H_anti_symm_quantified in H_trivial.
      discriminate.
      reflexivity.

    + reflexivity.

  - intro.
    rewrite -> H in H_conn_quantified.
    case (compare a b) as [ | | ] eqn : C_comp_ab.

    + reflexivity.

    + destruct H_conn_quantified.

      * Check (relating_Eq_eq).
        destruct (relating_Eq_eq A a b compare).
        apply H1 in C_comp_ab.
        rewrite -> C_comp_ab in H.
        
        Check (reflexivity_total_order A compare).
        assert (H_refl: leq (compare b b) = true).
        exact (reflexivity_total_order A compare b H_duplicate).
        
        rewrite -> H in H_refl.
        unfold leq in H_refl.
        discriminate.

      * unfold leq in H0.
        discriminate.

    + unfold leq in H_conn_quantified.
      destruct H_conn_quantified.
      discriminate.
      discriminate.
Qed.

(* Defining a comparison function for integers *) 
Definition compare_int (i j : nat) : element_comparison := 
  if i <? j then Lt else if i =n= j then Eq else Gt.

(* Theorem to show that compare_int meets the ordering specification *)
Theorem compare_int_defines_a_total_order:
  specification_of_compare_defining_total_order nat compare_int.
Proof.
  unfold specification_of_compare_defining_total_order.
  intros.
  split.

  - unfold anti_symmetry.
    intros.
    unfold compare_int in H.
    unfold compare_int in H0.
    case (a <? b) as [ | ] eqn : C_a_lt_b.

    + case (b <? a) as [ | ] eqn : C_b_lt_a.

      * Search (Nat.ltb).
        destruct (Nat.ltb_lt a b) as [H_ltb_lt_ab _].
        apply H_ltb_lt_ab in C_a_lt_b.
        destruct (Nat.ltb_lt b a) as [H_ltb_lt_ba _].
        apply H_ltb_lt_ba in C_b_lt_a.

        assert (H_impossible: a < a).
        exact (Nat.lt_trans a b a C_a_lt_b C_b_lt_a).

        destruct (Nat.ltb_lt a a) as [_ H_ltb_lt_aa].
        apply H_ltb_lt_aa in H_impossible.

        Search (Nat.ltb).
        assert (H_contradictory: (a <? a) = false).
        exact (Nat.ltb_irrefl a).
        
        rewrite -> H_contradictory in H_impossible.
        discriminate.

      * case (b =n= a) as [ | ] eqn : C_b_eq_a.
        apply beq_nat_true in C_b_eq_a.
        rewrite C_b_eq_a in C_a_lt_b.

        assert (H_contradictory: (a <? a) = false).
        exact (Nat.ltb_irrefl a).

        rewrite -> H_contradictory in C_a_lt_b.
        discriminate.

        unfold leq in H0. 
        discriminate.

    + case (a =n= b) as [ | ] eqn : C_a_eq_b.
      apply beq_nat_true in C_a_eq_b.
      destruct (relating_Eq_eq nat a b compare_int).
      apply H2 in C_a_eq_b.
      exact C_a_eq_b.

      unfold leq in H.
      discriminate.

  - split.

    + unfold transitivity.
      intros.
      unfold compare_int in H.
      unfold compare_int in H0.      

      case (a <? b) as [ | ] eqn : C_a_lt_b.

      * case (b <? c) as [ | ] eqn : C_b_lt_c.

        {
          destruct (Nat.ltb_lt a b).
          apply H1 in C_a_lt_b.

          destruct (Nat.ltb_lt b c).
          apply H3 in C_b_lt_c.

          assert (H_a_lt_c_prop: a < c).
          exact (Nat.lt_trans a b c C_a_lt_b C_b_lt_c).

          destruct (Nat.ltb_lt a c).
          apply H6 in H_a_lt_c_prop.

          unfold compare_int.
          rewrite -> H_a_lt_c_prop.
          unfold leq.
          reflexivity.
        }

        {
          case (b =n= c) as [ | ] eqn : C_b_eq_c.
          apply beq_nat_true in C_b_eq_c.
          rewrite -> C_b_eq_c in C_a_lt_b.
          unfold compare_int.
          rewrite -> C_a_lt_b.
          unfold leq.
          reflexivity.

          unfold leq in H0.
          discriminate.
        }

      * case (a =n= b) as [ | ] eqn : C_a_eq_b.

        apply beq_nat_true in C_a_eq_b.
        rewrite <- C_a_eq_b in H0.
        case (a <? c) as [ | ] eqn : C_a_lt_c.

        {
          unfold compare_int.
          rewrite -> C_a_lt_c.
          unfold leq.
          reflexivity.
        }

        {
          case (a =n= c) as [ | ] eqn : C_a_eq_c.
          unfold compare_int.
          rewrite -> C_a_lt_c.
          rewrite -> C_a_eq_c.
          unfold leq.
          reflexivity.

          unfold leq in H0.
          discriminate.
        }
        
        unfold leq in H.
        discriminate.

    + unfold connexity.
      intros.
      unfold compare_int.

      case (a <? b) as [ | ] eqn : C_a_lt_b.

      * unfold leq.

        assert (H_trivial: true = true).
        reflexivity.
        left.
        exact H_trivial.

      * case (a =n= b) as [ | ] eqn : C_a_eq_b.
        left.
        unfold leq.
        reflexivity.

        right.
        case (b <? a) as [ | ] eqn : C_b_lt_a.
        unfold leq.
        reflexivity.

        Search (_ <? _).
        destruct (Nat.ltb_ge a b).
        apply H in C_a_lt_b.

        destruct (Nat.ltb_ge b a).
        apply H1 in C_b_lt_a.

        Search (_ <= _).
        Check (Nat.le_antisymm a b C_b_lt_a C_a_lt_b).
        rewrite (Nat.le_antisymm a b C_b_lt_a C_a_lt_b) in C_a_eq_b.
        Search (_ =n= _).
        rewrite -> (Nat.eqb_refl b) in C_a_eq_b.
        discriminate.
Qed.

(* ********** *)


(* ********** Equality of pairs and option types ********** *)

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


(* ********** Reflections ********** *)

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

(* ********** *)
