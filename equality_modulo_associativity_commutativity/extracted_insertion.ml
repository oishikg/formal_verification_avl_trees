(* ********** The original heightened binary_tree implementaion ********** *)


module Original_Hbt =
  struct
    (* Type defintion for AVL trees *)

    type 'a heightened_binary_tree = int * 'a binary_tree
    and 'a triple = 'a heightened_binary_tree * 'a * 'a heightened_binary_tree
    and 'a binary_tree = Leaf
                       | Node of 'a triple
    ;;

    (* Empty hbt *)
    let hbt_empty = (0, Leaf)
    ;;

    (* Paraphernalia for comparison: *)

    type comparison =
      | Lt
      | Eq
      | Gt
    ;;

    (* The comparison function for integers: *)

    let compare_int i j =
      if i < j then Lt else if i = j then Eq else Gt;;

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

(* ********** Module with certified heightened binary tree code ********** *)
module Certified_Hbt =
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

let compare_int_certified a b =
  if a < b
  then Certified_Hbt.Lt
  else
    if a = b
    then Certified_Hbt.Eq
    else Certified_Hbt.Gt
;;
                  
           
let a0 = Certified_Hbt.insert_hbt compare_int_certified 2 Certified_Hbt.hbt_empty ;;

let a1 = Certified_Hbt.insert_hbt compare_int_certified 3 a0 ;;

let a2 = Certified_Hbt.insert_hbt compare_int_certified 4 a1 ;;

let a3 = Certified_Hbt.insert_hbt compare_int_certified 5 a2 ;;


(* ********** Equality modulo associativity and commutativity ********** *)

(* Introducing a type that captures the abstract syntax tree of expressions in 
 * binary operations that are both associative and commutative; taken from 
 * Professor Danvy's YSC3203 midterm project *)

type name = string ;;

type exp = Ide of name | BinOp of exp * exp ;;

(* Testing paraphernalia for equality modulo associative and commutativity *)

module Tests =
  struct 
    let random_char () =
      let i = Random.int 26
      in char_of_int (97 + i);;

    let random_singleton_string () =
      String.make 1 (random_char ());;

    let random_Char () =
      let i = Random.int 26
      in char_of_int (65 + i);;

    let random_singleton_String () =
      String.make 1 (random_Char ());;

    (* Random expression generator *)

    let generate_random_exp depth =
      let rec visit n =
        if n = 0
        then Ide (random_singleton_String ())
        else match Random.int 3 with
             | 0 ->
                Ide (random_singleton_string ())
             | _ ->
                BinOp (visit (pred n), visit (pred n))
      in visit depth;;    

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
      in visit e_init;;


    (* Function to randomly modify an expression such that the expression and 
     * modified  expression are equal modulo commutativity *)

    exception Impossible_Case ;;

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
    ;;

    (* Function to randomly modify an expression using both 
     * randomize_exp_modulo_associativity and randomize_exp_modulo_commutativity *)

    let randomize_exp_modulo_assoc_comm e =
      randomize_exp_modulo_associativity (randomize_exp_modulo_commutativity e)
    ;;

    (* Function which _messes up_ a term, that is, modifies a term such that it
     * is _not_ equal to the original term modulo commutativity *)

    let mess_up_exp_modulo_assoc_comm e_init =
      let rec visit_exp e =
        match e with
        | Ide x ->
           Ide "something completely different"
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
      in visit_exp e_init
    ;;

    (* Function to generate a pair of equal expressions, given a depth *)
    
    let generate_pair_equal_modulo_assoc_comm depth = 
      let e = generate_random_exp depth in
      let e' = randomize_exp_modulo_assoc_comm e
      in (e, e')
    ;;
    
    (* Function to generate a pair of equal expressions, given a depth *)

    let generate_pair_not_equal_modulo_assoc_comm depth =
      let e = generate_random_exp depth in
      let e' = mess_up_exp_modulo_assoc_comm e
      in (e, e')
    ;;


  end
  
             

(* Checking for equality modulo associativity and commutativity between two 
 * expressions boils down to checking if the two expressions have exactly the same
 * elements. *)

(* The naive predicate: 
 * Flatten both expressions into lists, and then sorting the lists *)

let flatten_exp e_init =
  let rec traverse_exp e acc = 
    match e with
    | Ide n ->
       n :: acc
    | BinOp (e1, e2) ->
       traverse_exp e1 (traverse_exp e2 acc)
  in traverse_exp e_init []
;;

let eq_assoc_comm_naive e1 e2 =
  List.sort compare (flatten_exp e1) = List.sort compare (flatten_exp e2)
;;
  
(* Alternative approach: 
 * Traverse the expression and insert each Ide 

