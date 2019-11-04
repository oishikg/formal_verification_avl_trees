

(* Type defintion for AVL trees *)

type 'a heightened_binary_tree = int * 'a binary_tree
 and 'a triple = 'a heightened_binary_tree * 'a * 'a heightened_binary_tree
 and 'a binary_tree = Leaf
                    | Node of 'a triple
;;

(* Paraphernalia for comparison: *)

type comparison =
  | Lt
  | Eq
  | Gt;;

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
