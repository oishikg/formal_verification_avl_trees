(* ********** Original implementation ********** *)

module Original_Hbt =
  struct
    (* Type defintion for AVL trees *)
    type 'a heightened_binary_tree = int * 'a binary_tree
    and 'a triple = 'a heightened_binary_tree * 'a * 'a heightened_binary_tree
    and 'a binary_tree = Leaf
                       | Node of 'a triple

    (* Empty hbt *)
    let hbt_empty = (0, Leaf)

    (* Paraphernalia for comparison: *)
    type comparison =
      | Lt
      | Eq
      | Gt

    (* The comparison function for integers: *)
    let compare_int i j =
      if i < j then Lt else if i = j then Eq else Gt;;

    (* Lookup function *)
    let occurs_hbt (compare : 'a -> 'a -> comparison)
               (e : 'a)
               (hbt : 'a heightened_binary_tree) : bool = 
      let rec traverse_to_check_occurs_bt bt =
        match bt with
        | Leaf ->
           false
        | Node ((_, bt1), e', (_, bt2)) ->
           match compare e e' with
           | Lt ->
              traverse_to_check_occurs_bt bt1
           | Gt ->
              traverse_to_check_occurs_bt bt2
           | Eq ->
              true
      in
      match hbt with
      | (_, Leaf) ->
         false
      | (_, bt) ->
         traverse_to_check_occurs_bt bt

    (* Testing whether two heights differ by at most one: *)
    let same_same h1 h2 =
      abs (h1 - h2) <= 1;;

    (* Exceptions *)
    exception Imbalanced;;

    exception Unsatisfied_assumption;;

    exception Bail_out;;

    (* Rotations *)
    let rotate_right ((_, bt1) as hbt1) e ((h2, bt2) as hbt2) =
      match bt1 with
      | Leaf ->
         raise Unsatisfied_assumption
      | Node (((h11, bt11) as hbt11), e1, ((h12, bt12) as hbt12)) ->
         if h11 + 1 = h12
         then match bt12 with
              | Leaf ->
                 raise Unsatisfied_assumption
              | Node (((h121, bt121) as hbt121), e12, ((h122, bt122) as hbt122)) ->
                 let new_h1 = 1 + max h11 h121
                 and new_h2 = 1 + max h122 h2
                 in (1 + max new_h1 new_h2,
                     Node ((new_h1,
                            Node (hbt11,
                                  e1,
                                  hbt121)),
                           e12,
                           (new_h2,
                            Node (hbt122,
                                  e,
                                  hbt2))))
         else let new_h2 = 1 + max h12 h2
              in (1 + max h11 new_h2,
                  Node (hbt11,
                        e1,
                        (new_h2,
                         Node (hbt12,
                               e,
                               hbt2))));;


    let rotate_left ((h1, bt1) as hbt1) e ((_, bt2) as hbt2) =
      match bt2 with
      | Leaf ->
         raise Unsatisfied_assumption
      | Node (((h21, bt21) as hbt21), e2, ((h22, bt22) as hbt22)) ->
         if h21 = h22 + 1
         then match bt21 with
              | Leaf ->
                 raise Unsatisfied_assumption
              | Node (((h211, bt211) as hbt211), e21, ((h212, bt212) as hbt212)) ->
                 let new_h1 = 1 + max h1 h211
                 and new_h2 = 1 + max h212 h22
                 in (1 + max new_h1 new_h2,
                     Node ((new_h1,
                            Node (hbt1,
                                  e,
                                  hbt211)),
                           e21,
                           (new_h2,
                            Node (hbt212,
                                  e2,
                                  hbt22))))
         else let new_h1 = 1 + max h1 h21
              in (1 + max new_h1 h22,
                  Node ((new_h1,
                         Node (hbt1,
                               e,
                               hbt21)),
                        e2,
                        hbt22));;


    (* Implementation of insertion *)

    let insert compare x (hbt : 'a heightened_binary_tree) =
      let rec climb_hbt (h, bt) =
        climb_bt h bt
      and climb_bt h bt =
        match bt with
        | Leaf ->
           (1, Node ((0, Leaf), x, (0, Leaf)))
        | Node (((h1, bt1) as hbt1), e, ((h2, bt2) as hbt2)) ->
           if h = 1 + max h1 h2 && same_same h1 h2 (* sanity check *)
           then match compare x e with
                | Lt ->
                   let ((h1', bt1') as hbt1') = climb_bt h1 bt1
                   in if h1' - h2 = 2
                      then rotate_right hbt1' e hbt2
                      else (1 + max h1' h2, Node (hbt1', e, hbt2))
                | Eq ->
                   raise Bail_out
                | Gt ->
                   let ((h2', bt2') as hbt2') = climb_bt h2 bt2
                   in if h2' - h1 = 2
                      then rotate_left hbt1 e hbt2'
                      else (1 + max h1 h2', Node (hbt1, e, hbt2'))
           else raise Imbalanced
      in try climb_hbt hbt
         with
         | Bail_out ->
            hbt;;
  end
;;

(* ********** *)

(* ********** Certified implementation using Peano numbers ********** *)

(* Module with certified heightened binary tree code *)
module Certified_Hbt_Peano =
  struct
    
    type bool =
      | True
      | False

    type nat =
      | O
      | S of nat

    type 'a option =
      | Some of 'a
      | None

    (** val add : nat -> nat -> nat **)
    let rec add n m =
      match n with
      | O -> m
      | S p -> S (add p m)

    (** val max : nat -> nat -> nat **)
    let rec max n m =
      match n with
      | O -> m
      | S n' -> (match m with
                 | O -> n
                 | S m' -> S (max n' m'))

    module Nat =
      struct
        (** val eqb : nat -> nat -> bool **)
        let rec eqb n m =
          match n with
          | O -> (match m with
                  | O -> True
                  | S _ -> False)
          | S n' -> (match m with
                     | O -> False
                     | S m' -> eqb n' m')

        (** val leb : nat -> nat -> bool **)
        let rec leb n m =
          match n with
          | O -> True
          | S n' -> (match m with
                     | O -> False
                     | S m' -> leb n' m')

        (** val ltb : nat -> nat -> bool **)
        let ltb n m =
          leb (S n) m
      end

    type element_comparison =
      | Lt
      | Eq
      | Gt

    (** val compare_int : nat -> nat -> element_comparison **)
    let compare_int i j =
      match Nat.ltb i j with
      | True -> Lt
      | False -> (match Nat.eqb i j with
                  | True -> Eq
                  | False -> Gt)

    type 'a heightened_binary_tree =
      | HNode of nat * 'a binary_tree
    and 'a binary_tree =
      | Leaf
      | Node of 'a triple
    and 'a triple =
      | Triple of 'a heightened_binary_tree * 'a * 'a heightened_binary_tree

    (** val hbt_empty : nat heightened_binary_tree **)
    let hbt_empty =
      HNode (O, Leaf)

    (** val occurs_hbt :
    ('a1 -> 'a1 -> element_comparison) -> 'a1 -> 'a1 heightened_binary_tree -> bool **)
    let rec occurs_hbt compare e = function
      | HNode (_, bt) -> occurs_bt compare e bt
    (** val occurs_bt : ('a1 -> 'a1 -> element_comparison) -> 'a1 -> 'a1 binary_tree -> bool **)
    and occurs_bt compare e = function
      | Leaf -> False
      | Node t -> occurs_t compare e t
    (** val occurs_t : ('a1 -> 'a1 -> element_comparison) -> 'a1 -> 'a1 triple -> bool **)
    and occurs_t compare e = function
      | Triple (hbt1, e', hbt2) ->
         (match compare e e' with
          | Lt -> occurs_hbt compare e hbt1
          | Eq -> True
          | Gt -> occurs_hbt compare e hbt2)
            

    (** val rotate_right_bt :
    'a1 binary_tree -> 'a1 -> nat -> 'a1 binary_tree -> 'a1 heightened_binary_tree option **)
    let rotate_right_bt bt1 e h2 bt2 =
      match bt1 with
      | Leaf -> None
      | Node t ->
         let Triple (h, e1, h0) = t in
         let HNode (h11, bt11) = h in
         let HNode (h12, bt12) = h0 in
         (match Nat.eqb (add h11 (S O)) h12 with
          | True ->
             (match bt12 with
              | Leaf -> None
              | Node t0 ->
                 let Triple (h1, e12, h3) = t0 in
                 let HNode (h121, bt121) = h1 in
                 let HNode (h122, bt122) = h3 in
                 Some (HNode ((add (S O) (max (add (S O) (max h11 h121)) (add (S O) (max h122 h2)))),
                              (Node (Triple ((HNode ((add (S O) (max h11 h121)), (Node (Triple ((HNode (h11, bt11)),
                                                                                                e1, (HNode (h121, bt121))))))), e12, (HNode ((add (S O) (max h122 h2)), (Node (Triple
                                                                                                                                                                                 ((HNode (h122, bt122)), e, (HNode (h2, bt2)))))))))))))
          | False ->
             (match match Nat.eqb (add h12 (S O)) h11 with
                    | True -> True
                    | False -> Nat.eqb h12 h11 with
              | True ->
                 Some (HNode ((add (S O) (max h11 (add (S O) (max h12 h2)))), (Node (Triple ((HNode
                                                                                                (h11, bt11)), e1, (HNode ((add (S O) (max h12 h2)), (Node (Triple ((HNode (h12,
                                                                                                                                                                           bt12)), e, (HNode (h2, bt2))))))))))))
              | False -> None))

    (** val rotate_right_hbt :
    'a1 heightened_binary_tree -> 'a1 -> 'a1 heightened_binary_tree -> 'a1 heightened_binary_tree
    option **)
    let rotate_right_hbt hbt1 e hbt2 =
      let HNode (_, bt1) = hbt1 in let HNode (h2, bt2) = hbt2 in rotate_right_bt bt1 e h2 bt2

    (** val rotate_left_bt :
    nat -> 'a1 binary_tree -> 'a1 -> 'a1 binary_tree -> 'a1 heightened_binary_tree option **)
    let rotate_left_bt h1 bt1 e = function
      | Leaf -> None
      | Node t ->
         let Triple (h, e2, h0) = t in
         let HNode (h21, bt21) = h in
         let HNode (h22, bt22) = h0 in
         (match Nat.eqb (add h22 (S O)) h21 with
          | True ->
             (match bt21 with
              | Leaf -> None
              | Node t0 ->
                 let Triple (h2, e21, h3) = t0 in
                 let HNode (h211, bt211) = h2 in
                 let HNode (h212, bt212) = h3 in
                 Some (HNode ((add (S O) (max (add (S O) (max h1 h211)) (add (S O) (max h212 h22)))),
                              (Node (Triple ((HNode ((add (S O) (max h1 h211)), (Node (Triple ((HNode (h1, bt1)), e,
                                                                                               (HNode (h211, bt211))))))), e21, (HNode ((add (S O) (max h212 h22)), (Node (Triple
                                                                                                                                                                             ((HNode (h212, bt212)), e2, (HNode (h22, bt22)))))))))))))
          | False ->
             (match match Nat.eqb (add h21 (S O)) h22 with
                    | True -> True
                    | False -> Nat.eqb h21 h22 with
              | True ->
                 Some (HNode ((add (S O) (max (add (S O) (max h1 h21)) h22)), (Node (Triple ((HNode
                                                                                                ((add (S O) (max h1 h21)), (Node (Triple ((HNode (h1, bt1)), e, (HNode (h21,
                                                                                                                                                                        bt21))))))), e2, (HNode (h22, bt22)))))))
              | False -> None))

    (** val rotate_left_hbt :
    'a1 heightened_binary_tree -> 'a1 -> 'a1 heightened_binary_tree -> 'a1 heightened_binary_tree
    option **)
    let rotate_left_hbt hbt1 e hbt2 =
      let HNode (h1, bt1) = hbt1 in let HNode (_, bt2) = hbt2 in rotate_left_bt h1 bt1 e bt2

    (** val project_height_hbt : 'a1 heightened_binary_tree -> nat **)
    let project_height_hbt = function
      | HNode (h, _) -> h

    (** val insert_hbt_helper :
    ('a1 -> 'a1 -> element_comparison) -> 'a1 -> 'a1 heightened_binary_tree -> 'a1
    heightened_binary_tree option **)
    let rec insert_hbt_helper compare x = function
      | HNode (h, bt) -> insert_bt_helper compare x h bt
    (** val insert_bt_helper :
    ('a1 -> 'a1 -> element_comparison) -> 'a1 -> nat -> 'a1 binary_tree -> 'a1
    heightened_binary_tree option **)
    and insert_bt_helper compare x h_hbt = function
      | Leaf -> Some (HNode ((S O), (Node (Triple ((HNode (O, Leaf)), x, (HNode (O, Leaf)))))))
      | Node t -> insert_t_helper compare x h_hbt t
    (** val insert_t_helper :
    ('a1 -> 'a1 -> element_comparison) -> 'a1 -> nat -> 'a1 triple -> 'a1 heightened_binary_tree
    option **)
    and insert_t_helper compare x _ = function
      | Triple (hbt1, e, hbt2) ->
         (match compare x e with
          | Lt ->
             (match insert_hbt_helper compare x hbt1 with
              | Some h ->
                 let HNode (h1', bt1') = h in
                 (match compare_int h1' (add (S (S O)) (project_height_hbt hbt2)) with
                  | Lt ->
                     Some (HNode ((add (S O) (max h1' (project_height_hbt hbt2))), (Node (Triple ((HNode
                                                                                                     (h1', bt1')), e, hbt2)))))
                  | Eq -> rotate_right_hbt (HNode (h1', bt1')) e hbt2
                  | Gt -> None)
              | None -> None)
          | Eq -> None
          | Gt ->
             (match insert_hbt_helper compare x hbt2 with
              | Some h ->
                 let HNode (h2', bt2') = h in
                 (match compare_int h2' (add (S (S O)) (project_height_hbt hbt1)) with
                  | Lt ->
                     Some (HNode ((add (S O) (max (project_height_hbt hbt1) h2')), (Node (Triple (hbt1, e,
                                                                                                  (HNode (h2', bt2')))))))
                  | Eq -> rotate_left_hbt hbt1 e (HNode (h2', bt2'))
                  | Gt -> None)
              | None -> None))

    (** val insert_hbt :
    ('a1 -> 'a1 -> element_comparison) -> 'a1 -> 'a1 heightened_binary_tree -> 'a1
    heightened_binary_tree **)
    let insert_hbt compare x hbt =
      match insert_hbt_helper compare x hbt with
      | Some hbt' -> hbt'
      | None -> hbt
  end
;;

(* ********** *)

(* ********** Certified implementation using OCaml Int ********** *)

module Certified_Hbt_Int =
  struct
    type element_comparison =
      | Lt
      | Eq
      | Gt

    let compare_int i j =
      if i < j then Lt else if i = j then Eq else Gt;;

    type 'a heightened_binary_tree =
      | HNode of int * 'a binary_tree
    and 'a binary_tree =
      | Leaf
      | Node of 'a triple
    and 'a triple =
      | Triple of 'a heightened_binary_tree * 'a * 'a heightened_binary_tree

    (** val hbt_empty : nat heightened_binary_tree **)
    let hbt_empty =
      HNode (0, Leaf)

    (** val occurs_hbt :
    ('a1 -> 'a1 -> element_comparison) -> 'a1 -> 'a1 heightened_binary_tree -> bool **)
    let rec occurs_hbt compare e = function
      | HNode (_, bt) -> occurs_bt compare e bt
    (** val occurs_bt : ('a1 -> 'a1 -> element_comparison) -> 'a1 -> 'a1 binary_tree -> bool **)
    and occurs_bt compare e = function
      | Leaf -> false
      | Node t -> occurs_t compare e t
    (** val occurs_t : ('a1 -> 'a1 -> element_comparison) -> 'a1 -> 'a1 triple -> bool **)
    and occurs_t compare e = function
      | Triple (hbt1, e', hbt2) ->
         (match compare e e' with
          | Lt -> occurs_hbt compare e hbt1
          | Eq -> true
          | Gt -> occurs_hbt compare e hbt2)
            

    (** val rotate_right_bt :
    'a1 binary_tree -> 'a1 -> nat -> 'a1 binary_tree -> 'a1 heightened_binary_tree option **)
    let rotate_right_bt bt1 e h2 bt2 =
      match bt1 with
      | Leaf -> None
      | Node t ->
         let Triple (h, e1, h0) = t in
         let HNode (h11, bt11) = h in
         let HNode (h12, bt12) = h0 in
         (match succ h11 = h12 with
          | true ->
             (match bt12 with
              | Leaf -> None
              | Node t0 ->
                 let Triple (h1, e12, h3) = t0 in
                 let HNode (h121, bt121) = h1 in
                 let HNode (h122, bt122) = h3 in
                 Some (HNode ((succ (max (succ (max h11 h121)) (succ (max h122 h2)))),
                              (Node (Triple ((HNode ((succ (max h11 h121)), (Node (Triple ((HNode (h11, bt11)),
                                                                                                e1, (HNode (h121, bt121))))))), e12, (HNode ((succ (max h122 h2)), (Node (Triple
                                                                                                                                                                                 ((HNode (h122, bt122)), e, (HNode (h2, bt2)))))))))))))
          | false ->
             (match match succ h12 = h11 with
                    | true -> true
                    | false -> h12 = h11 with
              | true ->
                 Some (HNode ((succ (max h11 (succ (max h12 h2)))), (Node (Triple ((HNode
                                                                                                (h11, bt11)), e1, (HNode ((succ (max h12 h2)), (Node (Triple ((HNode (h12,
                                                                                                                                                                           bt12)), e, (HNode (h2, bt2))))))))))))
              | false -> None))

    (** val rotate_right_hbt :
    'a1 heightened_binary_tree -> 'a1 -> 'a1 heightened_binary_tree -> 'a1 heightened_binary_tree
    option **)
    let rotate_right_hbt hbt1 e hbt2 =
      let HNode (_, bt1) = hbt1 in let HNode (h2, bt2) = hbt2 in rotate_right_bt bt1 e h2 bt2

    (** val rotate_left_bt :
    nat -> 'a1 binary_tree -> 'a1 -> 'a1 binary_tree -> 'a1 heightened_binary_tree option **)
    let rotate_left_bt h1 bt1 e = function
      | Leaf -> None
      | Node t ->
         let Triple (h, e2, h0) = t in
         let HNode (h21, bt21) = h in
         let HNode (h22, bt22) = h0 in
         (match succ h22 = h21 with
          | true ->
             (match bt21 with
              | Leaf -> None
              | Node t0 ->
                 let Triple (h2, e21, h3) = t0 in
                 let HNode (h211, bt211) = h2 in
                 let HNode (h212, bt212) = h3 in
                 Some (HNode ((succ (max (succ (max h1 h211)) (succ (max h212 h22)))),
                              (Node (Triple ((HNode ((succ (max h1 h211)), (Node (Triple ((HNode (h1, bt1)), e,
                                                                                               (HNode (h211, bt211))))))), e21, (HNode ((succ (max h212 h22)), (Node (Triple
                                                                                                                                                                             ((HNode (h212, bt212)), e2, (HNode (h22, bt22)))))))))))))
          | false ->
             (match match succ h21 = h22 with
                    | true -> true
                    | false -> h21 = h22 with
              | true ->
                 Some (HNode ((succ (max (succ (max h1 h21)) h22)), (Node (Triple ((HNode
                                                                                                ((succ (max h1 h21)), (Node (Triple ((HNode (h1, bt1)), e, (HNode (h21,
                                                                                                                                                                        bt21))))))), e2, (HNode (h22, bt22)))))))
              | false -> None))

    (** val rotate_left_hbt :
    'a1 heightened_binary_tree -> 'a1 -> 'a1 heightened_binary_tree -> 'a1 heightened_binary_tree
    option **)
    let rotate_left_hbt hbt1 e hbt2 =
      let HNode (h1, bt1) = hbt1 in let HNode (_, bt2) = hbt2 in rotate_left_bt h1 bt1 e bt2

    (** val project_height_hbt : 'a1 heightened_binary_tree -> nat **)
    let project_height_hbt = function
      | HNode (h, _) -> h

    (** val insert_hbt_helper :
    ('a1 -> 'a1 -> element_comparison) -> 'a1 -> 'a1 heightened_binary_tree -> 'a1
    heightened_binary_tree option **)
    let rec insert_hbt_helper compare x = function
      | HNode (h, bt) -> insert_bt_helper compare x h bt
    (** val insert_bt_helper :
    ('a1 -> 'a1 -> element_comparison) -> 'a1 -> nat -> 'a1 binary_tree -> 'a1
    heightened_binary_tree option **)
    and insert_bt_helper compare x h_hbt = function
      | Leaf -> Some (HNode (1, (Node (Triple ((HNode (0, Leaf)), x, (HNode (0, Leaf)))))))
      | Node t -> insert_t_helper compare x h_hbt t
    (** val insert_t_helper :
    ('a1 -> 'a1 -> element_comparison) -> 'a1 -> nat -> 'a1 triple -> 'a1 heightened_binary_tree
    option **)
    and insert_t_helper compare x _ = function
      | Triple (hbt1, e, hbt2) ->
         (match compare x e with
          | Lt ->
             (match insert_hbt_helper compare x hbt1 with
              | Some h ->
                 let HNode (h1', bt1') = h in
                 (match compare_int h1' (2 + (project_height_hbt hbt2)) with
                  | Lt ->
                     Some (HNode ((succ (max h1' (project_height_hbt hbt2))), (Node (Triple ((HNode
                                                                                                     (h1', bt1')), e, hbt2)))))
                  | Eq -> rotate_right_hbt (HNode (h1', bt1')) e hbt2
                  | Gt -> None)
              | None -> None)
          | Eq -> None
          | Gt ->
             (match insert_hbt_helper compare x hbt2 with
              | Some h ->
                 let HNode (h2', bt2') = h in
                 (match compare_int h2' (2 + (project_height_hbt hbt1)) with
                  | Lt ->
                     Some (HNode ((succ (max (project_height_hbt hbt1) h2')), (Node (Triple (hbt1, e,
                                                                                                  (HNode (h2', bt2')))))))
                  | Eq -> rotate_left_hbt hbt1 e (HNode (h2', bt2'))
                  | Gt -> None)
              | None -> None))

    (** val insert_hbt :
    ('a1 -> 'a1 -> element_comparison) -> 'a1 -> 'a1 heightened_binary_tree -> 'a1
    heightened_binary_tree **)
    let insert_hbt compare x hbt =
      match insert_hbt_helper compare x hbt with
      | Some hbt' -> hbt'
      | None -> hbt
  end
;;

(* ********** *)

(* ********** Paraphernalia ********** *)

(* Introducing a type that captures the abstract syntax tree of expressions in 
 * binary operations that are both associative and commutative; taken from 
 * Professor Danvy's YSC3203 midterm project *)

type name = string ;;

type exp = Ide of name | BinOp of exp * exp ;;

(* Module to generate unique variables *)
module Gensym =
  struct
    let counter = ref 1

    let reset () =
      counter := 1

    let gensym p =
      let s = string_of_int (!counter)
      in counter := succ (!counter);
         p ^ s
  end;;

(* Testing paraphernalia for equality modulo associative and commutativity *)
module Tests =
  struct 
    let random_char () =
      let i = Random.int 26
      in char_of_int (97 + i)

    let random_singleton_string () =
      String.make 1 (random_char ())

    let random_Char () =
      let i = Random.int 26
      in char_of_int (65 + i)

    let random_singleton_String () =
      String.make 1 (random_Char ())

    (* Random expression generator with unique variables *)
    let generate_random_exp depth =
      let rec visit n =
        if n = 0
        then Ide (Gensym.gensym (random_singleton_String ()))
        else match Random.int 3 with
             | 0 ->
                Ide (Gensym.gensym (random_singleton_String ()))
             | _ ->
                BinOp (visit (pred n), visit (pred n))
      in Gensym.reset ();
         visit depth

    (* Function to randomly modify an expression such that the expression and modified
     * expression are equal modulo commutativity *)
    let randomize_exp_modulo_commutativity e_init =
      let rec visit e = 
        match e with
        | Ide x ->
           e
        | BinOp (t1, t2) ->
           if Random.bool ()
           then BinOp (visit t1, visit t2)
           else BinOp (visit t2, visit t1)
      in visit e_init

    (* Function to randomly modify an expression such that the expression and 
     * modified  expression are equal modulo commutativity *)
    exception Impossible_Case

    let randomize_exp_modulo_associativity e_init =
      let rec rotate_right e11 e12 e2 = BinOp (e11, (BinOp (e12, e2)))
      and rotate_left e1 e21 e22 = BinOp (BinOp (e1, e21), e22)
      and randomize_rotated_exp e =
        match e with
        | Ide _ ->
           raise Impossible_Case
        | BinOp (e1', e2') ->
           begin
             match Random.int 3 with
             | 0 ->
                BinOp (e1', traverse_exp e2')
             | 1 ->
                BinOp (traverse_exp e1', e2')
             | _ ->
                BinOp (e1', e2')
           end
      and traverse_exp e =
        match e with
        | Ide _ ->
           e
        | BinOp (Ide _, Ide _) ->
           e
        | BinOp (BinOp (e11, e12), Ide x) ->
           randomize_rotated_exp (rotate_right e11 e12 (Ide x))
        | BinOp (Ide x, BinOp (e21, e22)) ->
           randomize_rotated_exp (rotate_left (Ide x) e21 e22)
        | BinOp (BinOp (e11, e12), BinOp (e21, e22)) ->
           begin
             match Random.int 2 with
             | 0 ->
                randomize_rotated_exp (rotate_right e11 e12 (BinOp (e21, e22)))
             | _ ->
                randomize_rotated_exp (rotate_left (BinOp (e11, e12)) e21 e22)
           end
      in traverse_exp e_init

    (* Function to randomly modify an expression using both 
     * randomize_exp_modulo_associativity and randomize_exp_modulo_commutativity *)
    let randomize_exp_modulo_assoc_comm e =
      randomize_exp_modulo_associativity (randomize_exp_modulo_commutativity e)

    (* Function which _messes up_ a term, that is, modifies a term such that it
     * is _not_ equal to the original term modulo commutativity *)
    let mess_up_exp_modulo_assoc_comm e_init =
      let rec visit_exp e =
        match e with
        | Ide x ->
           Ide (Gensym.gensym "something completely different")
        | BinOp (e1, e2) ->
           match Random.int 6 with
           | 0 ->
              BinOp (Ide (random_singleton_string ()), visit_exp e2)
           | 1 ->
              BinOp (visit_exp e1, Ide (random_singleton_string ()))
           | 2 | 3 ->
              BinOp (visit_exp e1, e2)
           | _ ->
              BinOp (e1, visit_exp e2)
      in Gensym.reset ();
         visit_exp e_init

    (* Function to generate a pair of equal expressions, given a depth *)
    let generate_pair_equal_modulo_assoc_comm depth = 
      let e = generate_random_exp depth in
      let e' = randomize_exp_modulo_assoc_comm e
      in (e, e')
    
    (* Function to generate a pair of unequal expressions, given a depth *)
    let generate_pair_not_equal_modulo_assoc_comm depth =
      let e = generate_random_exp depth in
      let e' = mess_up_exp_modulo_assoc_comm e
      in (e, e')

    (* Implementation of a loop *)
    let rec loop f n =
      match n with
      | 0 ->
         true
      | n ->
         (f ()) && (loop f (pred n)) 
  end
  
(* Function to map OCaml's in-built compare function to 
 * Original_Hbt.element_comparison *)
let compare_to_comparison a b =
  match compare a b with
  | -1 ->
     Original_Hbt.Lt
  | 0 ->
     Original_Hbt.Eq
  | _ ->
     Original_Hbt.Gt
;;
    
(* Function to map OCaml's in-built compare function to 
 * Certified_Hbt_Peano.element_comparison *)
let compare_to_element_comparison_peano a b =
  match compare a b with
  | -1 ->
     Certified_Hbt_Peano.Lt
  | 0 ->
     Certified_Hbt_Peano.Eq
  | _ ->
     Certified_Hbt_Peano.Gt
;;

(* Function to map OCaml's in-built compare function to 
 * Certified_Hbt_Int.element_comparison *)
let compare_to_element_comparison_int a b =
  match compare a b with
  | -1 ->
     Certified_Hbt_Int.Lt
  | 0 ->
     Certified_Hbt_Int.Eq
  | _ ->
     Certified_Hbt_Int.Gt
;;

(* Lazy list type *)
type 'a lazy_list =
  | LNil
  | LCons of 'a * (unit -> 'a lazy_list);;

let force f = f () ;;

(* Function to check if two lazy lists are equal *) 
let lazy_lists_equal (lxs_init : name lazy_list) (lys_init : name lazy_list) =
  let rec walk lxs lys = 
    match lxs with
    | LNil ->
       begin
         match lys with
         | LNil ->
            true
         | _    ->
            false
       end
    | LCons (lx, fxs') ->
       begin
         match lys with
         | LNil ->
            false
         | LCons (ly, fys') ->
            if lx = ly
            then walk (force fxs') (force fys')
            else false 
       end
  in walk lxs_init lys_init
;;

(* ********** *)

(* ********** Equality modulo associativity and commutativity ********** *)

(* Define tests for predicate using Tests module *)
let test_eq_assoc_comm candidate n =
  let f = (fun () ->
      let depth = Random.int 20
      in let (e, e_eq) = Tests.generate_pair_equal_modulo_assoc_comm depth
         and (e1, e1_neq) = Tests.generate_pair_not_equal_modulo_assoc_comm depth
         in (candidate e e_eq = true) && (candidate e1 e1_neq = false))
  in Tests.loop f n
;;    
  
(* Traverse the expression and insert each variables into a self-balancing binary 
 * tree using the certified insertion function *)

(* Predicate to check equality modulo associativity and commutativity using the 
 * original OCaml AVL tree implementation *)
let eq_assoc_comm_original_hbt e1 e2 =
  let rec traverse_exp e acc = 
    match e with
    | Ide n ->
       Original_Hbt.insert compare_to_comparison n acc
    | BinOp (e1, e2) ->
       traverse_exp e1 (traverse_exp e2 acc)
  and flatten_to_ll hbt acc = 
    match hbt with
    |  (_, Original_Hbt.Leaf) ->
       acc
    |  (_, Original_Hbt.Node (hbt1, e, hbt2)) ->
       flatten_to_ll hbt1 (LCons (e, (fun () -> flatten_to_ll hbt2 acc)))
  in let hbt1 = traverse_exp e1 Original_Hbt.hbt_empty
     and hbt2 = traverse_exp e2 Original_Hbt.hbt_empty
     in let ll1 = flatten_to_ll hbt1 LNil
        and ll2 = flatten_to_ll hbt2 LNil
in lazy_lists_equal ll1 ll2
;;

let _ = assert (test_eq_assoc_comm eq_assoc_comm_original_hbt 1000) ;;

(* Predicate to check equality modulo associativity and commutativity using the 
 * certified and extracted OCaml AVL tree implementation using Peano numbers *)
let eq_assoc_comm_certified_hbt_peano e1 e2 =
  let rec traverse_exp e acc = 
    match e with
    | Ide n ->
       Certified_Hbt_Peano.insert_hbt compare_to_element_comparison_peano n acc
    | BinOp (e1, e2) ->
       traverse_exp e1 (traverse_exp e2 acc)
  and flatten_to_ll hbt acc = 
    match hbt with
    | Certified_Hbt_Peano.HNode (_, Certified_Hbt_Peano.Leaf) ->
       acc
    | Certified_Hbt_Peano.HNode (_, Certified_Hbt_Peano.Node
                                (Certified_Hbt_Peano.Triple (hbt1, e, hbt2))) ->
       flatten_to_ll hbt1 (LCons (e, (fun () -> flatten_to_ll hbt2 acc)))
  in let hbt1 = traverse_exp e1 Certified_Hbt_Peano.hbt_empty
     and hbt2 = traverse_exp e2 Certified_Hbt_Peano.hbt_empty
     in let ll1 = flatten_to_ll hbt1 LNil
        and ll2 = flatten_to_ll hbt2 LNil
        in lazy_lists_equal ll1 ll2
;;

let _ = assert (test_eq_assoc_comm eq_assoc_comm_certified_hbt_peano 1000) ;;

(* Predicate to check equality modulo associativity and commutativity using the 
 * certified and extracted OCaml AVL tree implementation using Peano numbers *)
let eq_assoc_comm_certified_hbt_int e1 e2 =
  let rec traverse_exp e acc = 
    match e with
    | Ide n ->
       Certified_Hbt_Int.insert_hbt compare_to_element_comparison_int n acc
    | BinOp (e1, e2) ->
       traverse_exp e1 (traverse_exp e2 acc)
  and flatten_to_ll hbt acc = 
    match hbt with
    | Certified_Hbt_Int.HNode (_, Certified_Hbt_Int.Leaf) ->
       acc
    | Certified_Hbt_Int.HNode (_, Certified_Hbt_Int.Node
                                (Certified_Hbt_Int.Triple (hbt1, e, hbt2))) ->
       flatten_to_ll hbt1 (LCons (e, (fun () -> flatten_to_ll hbt2 acc)))
  in let hbt1 = traverse_exp e1 Certified_Hbt_Int.hbt_empty
     and hbt2 = traverse_exp e2 Certified_Hbt_Int.hbt_empty
     in let ll1 = flatten_to_ll hbt1 LNil
        and ll2 = flatten_to_ll hbt2 LNil
        in lazy_lists_equal ll1 ll2
;;

let _ = assert (test_eq_assoc_comm eq_assoc_comm_certified_hbt_int 1000) ;;

(* ********** *)

(* ********** Benchmarking the predicates ********** *)

(* Record type to store performance info *)
type performance_info =
  { t_org        : float;
    t_cert_peano : float;
    t_cert_int   : float;
  }
;;

(* Function to record duration *)
let duration p (x, x') exp =
  let t_init = Sys.time () in
  let bv = p x x' in
  assert (bv = exp);
  let t_fin = Sys.time ()
  in t_fin -. t_init
;;

(* Function to compare predicate performances and return the average time taken *)
let compare_eq_assoc_comm_predicates n_init =
  let rec iterate n r =
    match n with
    | 0 ->
       let nf = float_of_int n_init
       in { t_org = (r.t_org /. nf);
            t_cert_peano = (r.t_cert_peano /. nf);
            t_cert_int = (r.t_cert_int /. nf);            
          }
    | _ -> 
       let depth = Random.int 30
       in let p_eq = Tests.generate_pair_equal_modulo_assoc_comm depth
          and p_neq = Tests.generate_pair_not_equal_modulo_assoc_comm depth in
          let t_org' = (duration eq_assoc_comm_original_hbt p_eq true)
                       +. (duration eq_assoc_comm_original_hbt p_neq false)
          and t_cert_peano' = (duration eq_assoc_comm_certified_hbt_peano p_eq true)
                              +. (duration eq_assoc_comm_certified_hbt_peano p_neq
                                    false) 
          and t_cert_int' = (duration eq_assoc_comm_certified_hbt_int p_eq true)
                              +. (duration eq_assoc_comm_certified_hbt_int p_neq
                                    false) in
          let r' = { t_org = r.t_org +. t_org';
                     t_cert_peano = r.t_cert_peano +. t_cert_peano';
                     t_cert_int = r.t_cert_int +. t_cert_int';
                   }
          in iterate (n - 1) r'
  in iterate n_init {t_org = 0.0; t_cert_peano = 0.0; t_cert_int = 0.0;}
;;

(*
# compare_eq_assoc_comm_predicates 1000000 ;;
- : performance_info =
{t_org = 0.000735804128000012; t_cert_peano = 0.00176464631200033023;
 t_cert_int = 0.000780153733999675611}
# 
*)
