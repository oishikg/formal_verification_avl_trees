
(* OCaml Implementation of AVL trees *) 
(* Senior Thesis *)
(* Oishik Ganguly <oishik.ganguly@u.yale-nus.edu.sg> *) 
(* Acknowledgements: Much of the code in this file belong to Professor Olivier Danvy, who 
 * wrote it as part of his course Introduction to Data Structures and Algorithms (YSC2229),
 *  Sem2, 2017-2018 *)

(* ********** Paraphernalia ********** *)

exception Not_implemented_yet;;
  
(* when false: error messages are issued *)
(* when  true: error messages are not issued *)
let silent = ref false;;

(* Short cut: *)
exception Bail_out;;

(* ********** *)

(* ********** Implementation of AVL tree data type ********** *)
  
(* Professor Danvy's implementation of the data type *)
type 'a heightened_binary_tree = int * 'a binary_tree
 and 'a triple = 'a heightened_binary_tree * 'a * 'a heightened_binary_tree
 and 'a binary_tree = Leaf
                    | Node of 'a triple
;;
 
(* An alternative data type implementation *)
type 'a heightened_binary_tree_alternative =
  ALeaf
| ANode of int * 'a heightened_binary_tree_alternative * 'a *
            'a heightened_binary_tree_alternative
;;
  
         
(* let rec height (hbta : 'a heightened_binary_tree_alternative) : int = *)
(*   match hbta with *)
(*   | ALeaf -> 0 *)
(*   | ANode (h, hbt1, e, hbt2) -> *)
(*      max (height hbt1) (height hbt2) + 1 *)
(* ;; *)

(* let _ = assert (test_height height) ;; *)

(* function to convert heightened_binary_tree to heightened_binary_tree_alternative *)
let rec  hbt_to_hbta (hbt : 'a heightened_binary_tree) =
  match hbt with
  | (_, Leaf) -> ALeaf
  | (h, Node (hbt1, e, hbt2)) ->
     let hbta1 = hbt_to_hbta hbt1
     and hbta2 = hbt_to_hbta hbt2 in
     ANode (h, hbta1, e, hbta2)
;;
                            
(*function to convert heightened_binary_tree_alternative to heightened_binary_tree*)     
let hbta_to_hbt (hbta : 'a heightened_binary_tree_alternative) =
  match hbta with
  | ALeaf -> (0, Leaf)
  | ANode (h, hbta1, e, hbta2) -> (h, Node (hbta_to_hbt hbta1, e, hbta_to_hbt hbta2))
;;

(* Function that, given a function that acts on heightened_binary_tree s, 
 * returns the analogues function for heightened_binary_tree_alternative *)
let hbta_analogue (f_hbt : 'a heightened_binary_tree -> 'a heightened_binary_tree) :
      ('a heightened_binary_tree_alternative ->
       'a heightened_binary_tree_alternative) =
  fun hbta -> hbt_to_hbta (f_hbt (hbta_to_hbt hbta))
;;

(* Function that, given a function that acts on heightened_binary_tree_alternative s
 * returns the analogues function for heightened_binary_tree s *)
let hbt_analogue (f_hbta : 'a heightened_binary_tree_alternative ->
                           'a heightened_binary_tree_alternative) :
      ('a heightened_binary_tree ->
       'a heightened_binary_tree) =
  fun hbt -> hbta_to_hbt (f_hbta (hbt_to_hbta hbt))
;;

(* ********** *) 

(* ********** heightened_binary_tree implementations for testing ********** **)

(* heightened_binary_tree s that are sound, ordered, and balanced (no errors) *) 
let hbt_0 = (0, Leaf)
;;

let hbt_1 =
  (2, 
   Node ((0, 
          Leaf), 
         1, 
         (1, 
          Node ((0, 
                 Leaf), 
                2, 
                (0, 
                 Leaf)))))
;;

let hbt_2 =
  (3, 
         Node ((2, 
                Node ((0, 
                       Leaf), 
                      1, 
                      (1, 
                       Node ((0, 
                              Leaf), 
                             2, 
                             (0, 
                              Leaf))))), 
               3, 
               (0, 
                Leaf)))
;;

let hbt_3 =
  (3, 
         Node ((2, 
                Node ((0, 
                       Leaf), 
                      1, 
                      (1, 
                       Node ((0, 
                              Leaf), 
                             2, 
                             (0, 
                              Leaf))))), 
               3, 
               (2, 
                Node ((0,
                       Leaf),
                      4,
                      (1, Node
                            ((0,
                              Leaf),
                             5,
                             (0,
                              Leaf)))))
              )
  )
;;

let hbt_4 =
  (4,
   Node  ((3,
           Node
            ((1, Node
                      ((0,
                        Leaf),
                       1,
                       (0,
                        Leaf))) ,
                3,
                (2, Node
                      ((1, Node
                             ((0,
                               Leaf),
                              4,
                              (0,
                               Leaf))),
                       5,
                       (1, Node
                             ((0,
                               Leaf),
                              6,
                              (0,
                               Leaf))))))),
         7,
         (3, Node
               ((2, Node
                      ((0,
                        Leaf),
                       8,
                       (1, Node
                             ((0,
                               Leaf),
                              9,
                              (0,
                               Leaf))))),
                10,
                (2, Node
                      ((0,
                        Leaf),
                       11,
                       (1, Node
                             ((0,
                               Leaf),
                              13,
                               (0,
                                Leaf)))))))))
;;

let hbt_5=
  (2, Node
        ( (1,
           Node
             (
               (0, Leaf),
               5,
               (0, Leaf))),
          10,
          (1, Node (
                  (0, Leaf),
                  11,
                  (0, Leaf)))))
;;

(* Heightened binary trees with errors in them *) 

(* Unbalanced (height errors) *) 
let hbt_with_height_error_0 =
  (4, 
         Node ((2, 
                Node ((0, 
                       Leaf), 
                      1, 
                      (1, 
                       Node ((0, 
                              Leaf), 
                             2, 
                             (0, 
                              Leaf))))), 
               3, 
               (2, 
                Node ((0,
                       Leaf),
                      4,
                      (1, Node
                            ((0,
                              Leaf),
                             5,
                             (0,
                              Leaf)))))
              )
  )
;;

let hbt_with_height_error_1 =
  (4, 
         Node ((2, 
                Node ((0, 
                       Leaf), 
                      1, 
                      (1, 
                       Node ((0, 
                              Leaf), 
                             2, 
                             (0, 
                              Leaf))))), 
               3, 
               (2, 
                Node ((1,
                       Leaf),
                      4,
                      (1, Node
                            ((0,
                              Leaf),
                             5,
                             (0,
                              Leaf)))))
              )
  )
;;

let hbt_with_height_error_2 = 
  (4,
   Node  ((3,
           Node
            ((1, Node
                      ((0,
                        Leaf),
                       1,
                       (0,
                        Leaf))) ,
                3,
                (1, Node
                      ((1, Node
                             ((0,
                               Leaf),
                              4,
                              (0,
                               Leaf))),
                       5,
                       (1, Node
                             ((0,
                               Leaf),
                              6,
                              (0,
                               Leaf))))))),
         7,
         (3, Node
               ((2, Node
                      ((0,
                        Leaf),
                       8,
                       (1, Node
                             ((0,
                               Leaf),
                              9,
                              (0,
                               Leaf))))),
                10,
                (2, Node
                      ((0,
                        Leaf),
                       11,
                       (1, Node
                             ((0,
                               Leaf),
                              13,
                               (0,
                                Leaf)))))))))
;;


(* Balancing error, i.e., the trees are unbalanced *)
let unbalanced_hbt_0 =
  (5, Node
        ((0, Leaf),
         1,
         (4, Node
               ((0, Leaf),
                2,
                (3, Node
                      ((0, Leaf),
                       3,
                       (2, Node
                             ((0, Leaf),
                              4,
                              (1, Node
                                    ((0, Leaf),
                                     5,
                                     (0, Leaf)))))))))))
;;

let unbalanced_hbt_1 =
  (4, Node
        ((3, Node
               ((2, Node
                      ((1, Node
                             ((0, Leaf),
                              1,
                              (0, Leaf))),
                       2,
                       (0, Leaf))),
                3,
                (0, Leaf))),
         4,
         (0, Leaf)))
;;

let unbalanced_hbt_2 =
  (4, Node
        ((1, Node
               ((0, Leaf),
                3,
                (0, Leaf))),
         10,
         (3, Node
               ((0, Leaf),
                15,
                (2, Node
                      ((0, Leaf),
                       16,
                       (1, Node
                             ((0, Leaf),
                              22,
                              (0, Leaf)))))))))
;;

let unbalanced_hbt_3 =
  (5, Node
        ((4, Node
               ((0, Leaf),
                11,
                (3, Node
                      ((0, Leaf),
                       12,
                       (2, Node
                             ((0, Leaf),
                              13,
                              (1, Node
                                    ((0, Leaf),
                                     14,
                                     (0, Leaf))))))))), 
         16,
         (4, Node
               ((2, Node
                      ((1, Node
                             ((0, Leaf),
                              17,
                              (0, Leaf))),
                       18,
                       (0, Leaf))),
                20,
                (3, Node
                      ((0, Leaf),
                       21,
                       (2, Node
                             ((0, Leaf),
                              22,
                              (1, Node
                                    ((0, Leaf),
                                     23,
                                     (0, Leaf)))))))))))
;;

(* Unordered binary trees *)
let unordered_hbt_0 =
  (2, Node
        ((1, Node
               ((0, Leaf),
                13,
                (0, Leaf))),
         10,
         (1, Node
               ((0, Leaf),
                12,
                (0, Leaf)))))
;;

let unordered_hbt_1 =
  (3, Node
        ((2, Node
               ((0, Leaf),
                11,
                (1, Node
                      ((0, Leaf),
                       13,
                       (0, Leaf))))),
         12,
         (1, Node
               ((0, Leaf),
                15,
                (0, Leaf)))))
;;

let unordered_hbt_2 =
  (4, Node
        ((2, Node
               ((1, Node
                      ((0, Leaf),
                       7,
                       (0, Leaf))),
                8,
                (0, Leaf))),
         9,
         (3, Node
               ((2, Node
                      ((1, Node
                             ((0, Leaf),
                              6,
                              (0, Leaf))),
                       10,
                       (0, Leaf))),
                12,
                (1, Node
                      ((0, Leaf),
                       14,
                       (0, Leaf)))))))
;;

(* ********** *)


(* ********** Unparsing paraphernalia (useful for tracing): ********** *)

let show_int n =
  if n < 0
  then "(" ^ string_of_int n ^ ")"
  else string_of_int n;;

let show_bool b =
  if b
  then "true"
  else "false";;

let show_heightened_binary_tree show_yourself (hbt : 'a heightened_binary_tree) =
  let rec show_heightened_binary_tree (h, bt) =
    "(" ^ show_int h ^ ", " ^ show_binary_tree bt ^ ")"
  and show_binary_tree bt =
    match bt with
    | Leaf ->
       "Leaf"
    | Node (hbt1, e, hbt2) ->
       "Node (" ^ show_heightened_binary_tree hbt1 ^ ", " ^ show_yourself e ^ ", " ^ show_heightened_binary_tree hbt2 ^ ")"
  in show_heightened_binary_tree hbt;;

let show_binary_tree show_yourself (bt : 'a binary_tree) =
  let rec show_heightened_binary_tree (h, bt) =
    "(" ^ show_int h ^ ", " ^ show_binary_tree bt ^ ")"
  and show_binary_tree bt =
    match bt with
    | Leaf ->
       "Leaf"
    | Node (hbt1, e, hbt2) ->
       "Node (" ^ show_heightened_binary_tree hbt1 ^ ", " ^ show_yourself e ^ ", " ^ show_heightened_binary_tree hbt2 ^ ")"
  in show_binary_tree bt;;



(* A pretty-printing function (useful for visualization): *)
let pp_heightened_binary_tree show_yourself (hbt : 'a heightened_binary_tree) =
  let rec show_heightened_binary_tree (h, bt) prefix =
    "(" ^ show_int h ^ ", \n " ^ prefix ^ show_binary_tree bt (prefix ^ " ") ^ ")"
  and show_binary_tree bt prefix =
    match bt with
    | Leaf ->
       "Leaf"
    | Node (hbt1, e, hbt2) ->
       "Node (" ^ show_heightened_binary_tree hbt1 (prefix ^ "      ") ^ ", \n" ^ prefix ^ "      " ^ show_yourself e ^ ", \n" ^ prefix ^ "      " ^ show_heightened_binary_tree hbt2 (prefix ^ "      ")^ ")"
  in Printf.printf "%s\n" (show_heightened_binary_tree hbt "");;

(* ********** *)

(* ********** Invariant Properties of AVL Trees ********** *)

(* ***** Soundness ***** *) 

(* This property requires that the height stored in each node of an AVL Tree
 *  is accurate *) 

(* Unit tests for is_sound_hbt *)
let test_is_sound_hbt (cand : 'a heightened_binary_tree -> bool) : bool =
  let t0 = (cand hbt_0 = true)
  and t1 = (cand hbt_1 = true)
  and t2 = (cand hbt_2 = true)
  and t3 = (cand hbt_5 = true)
  and t4 = (cand hbt_with_height_error_0 = false)
  and t5 = (cand hbt_with_height_error_1 = false)
  and t6 = (cand hbt_with_height_error_2 = false)
  in (t0 && t1 && t2 && t3 && t4 && t5 && t6)
;;
  


(* Function to test if a heightened_binary_tree is sound *) 
let is_sound_hbt ((h_init, bt_init) : 'a heightened_binary_tree) : bool =
  (* Helper function to traverse an 'a binary_tree *) 
  let rec traverse_to_check_soundness_bt (bt : 'a binary_tree) : int option =
    match bt with
    | Leaf ->
       Some 0 
    | Node ((h1, bt1), e, (h2, bt2)) ->
       match traverse_to_check_soundness_bt bt1 with
       | None ->
          None
       | Some h1' ->
          if h1' = h1
          then
            match traverse_to_check_soundness_bt bt2 with
            | None -> None
            | Some h2' ->
               if h2' = h2
               then Some (1 + max h1 h2)
               else None 
          else None
  in match traverse_to_check_soundness_bt bt_init with
     | None ->
        false
     | Some h ->
        h = h_init
;;

let _ =  assert (test_is_sound_hbt is_sound_hbt) ;;

(* Unit tests for is_sound_hbta *)
let test_is_sound_hbta (cand : 'a heightened_binary_tree_alternative -> bool) : bool =
  let t0 = (cand (hbt_to_hbta hbt_0) = true)
  and t1 = (cand (hbt_to_hbta hbt_1) = true)
  and t2 = (cand (hbt_to_hbta hbt_2) = true)
  and t3 = (cand (hbt_to_hbta hbt_5) = true)
  and t4 = (cand (hbt_to_hbta hbt_with_height_error_0) = false)
  and t5 = (cand (hbt_to_hbta hbt_with_height_error_1) = false)
  and t6 = (cand (hbt_to_hbta hbt_with_height_error_2) = false)
  in (t0 && t1 && t2 && t3 && t4 && t5 && t6)
;;

;;

(* Function to test if a heightened_binary_tree_alternative is sound *)
let is_sound_hbta (hbta : 'a heightened_binary_tree_alternative) : bool =
  (* Helper function to traverse heightened_binary_tree_alternative *)
  let rec traverse_to_check_soundness_hbta (hbta : 'a heightened_binary_tree_alternative) : int option =
    match hbta with
    | ALeaf ->
       Some 0
    | ANode (h, hbta1, _, hbta2) ->
       match traverse_to_check_soundness_hbta hbta1 with
       | None ->
          None
       | Some h1 ->
          match traverse_to_check_soundness_hbta hbta2 with
          | None ->
             None
          | Some h2 ->
             if h = 1 + max h1 h2
             then Some h
             else None
  in match traverse_to_check_soundness_hbta hbta with
     | None ->
        false
     | Some _ ->
        true 
;;

let _ =  assert (test_is_sound_hbta is_sound_hbta);;

(* ***** *)

(* ***** Balancedness ***** *) 

(* This property requires that for every node in the tree, the heights of its 
 * subtrees differ by at most 1 *)
  
(* Helper function to check if two heights differ by 1 *) 
let differ_by_one h1 h2 =
  abs (h1 - h2) <= 1;;

(* Traced version thereof: *)
let traced_differ_by_one h1 h2 =
  Printf.printf "differ_by_one %s %s ->\n" (show_int h1) (show_int h2);
  let result = abs (h1 - h2) <= 1
  in Printf.printf "differ_by_one %s %s <- %s\n" (show_int h1) (show_int h2) (show_bool result);
     result;;

(* Unit tests for is_balanced_hbt *)
let test_is_balanced_hbt (cand : 'a heightened_binary_tree -> bool)  =
  let t0 = (cand hbt_0 = true)
  and t1 = (cand hbt_3 = true)
  and t2 = (cand hbt_5 = true)
  and t3 = (cand unbalanced_hbt_0 = false)
  and t4 = (cand unbalanced_hbt_2 = false)
  and t5 = (cand unbalanced_hbt_3 = false)
  in (t0 && t1 && t2 && t3 && t4 && t5)
;;
  
(* Function to check if a heightened_binary_tree is balanced *)
let is_balanced_hbt ((_, bt_init) : 'a heightened_binary_tree) : bool =
  (* Helper function to traverse a binary_tree to check soundness *) 
  let rec traverse_to_check_balanced_bt (bt : 'a binary_tree) : int option =
    match bt with
    | Leaf ->
       Some 0 
    | Node ((_, bt1), e, (_, bt2)) ->
       match traverse_to_check_balanced_bt bt1 with
       | None ->
          None
       | Some h1' ->
          match traverse_to_check_balanced_bt bt2 with
          | None ->
             None
          | Some h2' ->
             if differ_by_one h1' h2'
             then Some (1 + max h1' h2')
             else None 
  in  match traverse_to_check_balanced_bt bt_init with
      | None ->
         false
      | Some _ ->
         true
;;

let _ = assert (test_is_balanced_hbt is_balanced_hbt);;

(* Unit tests for is_balanced_hbta *)
let test_is_balanced_hbta (cand : 'a heightened_binary_tree_alternative -> bool)  =
  let t0 = (cand (hbt_to_hbta hbt_0) = true)
  and t1 = (cand (hbt_to_hbta hbt_3) = true)
  and t2 = (cand (hbt_to_hbta hbt_5) = true)
  and t3 = (cand (hbt_to_hbta unbalanced_hbt_0) = false)
  and t4 = (cand (hbt_to_hbta unbalanced_hbt_2) = false)
  and t5 = (cand (hbt_to_hbta unbalanced_hbt_3) = false)
  in (t0 && t1 && t2 && t3 && t4 && t5)
;;

(* Function to check whether heightened_binary_tree_alternative is balanced *)
let is_balanced_hbta (hbta : 'a heightened_binary_tree_alternative) : bool =
  (* Helper function to traverse heightened_binary_tree_alternative to check for 
   * balancedness *)
  let rec traverse_to_check_balanced_hbta (hbta : 'a heightened_binary_tree_alternative) : int option =
    match hbta with
    | ALeaf ->
       Some 0
    | ANode (h, hbta1, _, hbta2) ->
       match traverse_to_check_balanced_hbta hbta1 with
       | None ->
          None
       | Some h1' ->
          match traverse_to_check_balanced_hbta hbta2 with
          | None ->
             None
          | Some h2' ->
             if differ_by_one h1' h2'
             then Some (1 + max h1' h2') 
             else None
  in match traverse_to_check_balanced_hbta hbta with
     | None ->
        false
     | Some _ ->
        true 
;;

let _ = assert (test_is_balanced_hbta is_balanced_hbta);;

(* ***** *)

(* ***** In-orderedness ***** *) 

(* This property requires that the payloads of the tree traversed depth-first 
 * left to right are in-order (i.e., ascending or descending)  *)

(* Our strategy to check for in-orderedness will involve flattening trees into 
 * lists; we do so as follows: *)

(* Helper function to flatten a binary tree *) 
let rec flatten_binary_tree (bt : 'a binary_tree) (es : 'a list) : 'a list = 
    match bt with
    | Leaf ->
       es
    | Node ((_, bt1), e, (_, bt2)) ->
       flatten_binary_tree bt1 (e :: flatten_binary_tree bt2 es)
;;
  
(* Function to map a heightened_binary_tree into the in-order list of its elements *)
let hbt_to_list ((h, bt) : 'a heightened_binary_tree) : 'a list =
  flatten_binary_tree bt [];;

(* Function to map a heightened_binary_tree_alternative into the in-order
 * list of its elements *)
let hbta_to_list (hbta_init : 'a heightened_binary_tree_alternative) : 'a list =
  let rec flatten_hbta_helper hbta es =
    match hbta with
    | ALeaf ->
       es 
    | ANode (_, hbta1, e, hbta2) ->
       flatten_hbta_helper hbta1 (e :: (flatten_hbta_helper hbta2 es))
  in flatten_hbta_helper hbta_init []
;;

(* We will also need some way of comparing the elements of a list. The assumption is
 * that the elements of the list have some order defined on them. With this 
 * assumption, we formalize the idea of comparing the elements by introducing a 
 * comparison function for the type. This function takes two elements of the type, 
 * and maps to an enum type constructed by the possible inequalities: *)

(* Paraphernalia for comparison: *)
type comparison =
  | Lt
  | Eq
  | Gt;;

(* The comparison function for integers: *)
let compare_int i j =
  if i < j then Lt else if i = j then Eq else Gt;;

(* Unit tests for is_ordered_list *)
let test_is_ordered_list (cand : 'a list 
                                 -> ('a -> 'a -> comparison)
                                 -> bool) =
  let t0 = (cand [0 ; 1 ; 2 ; 3 ; 4] compare_int = true)
  and t1 = (cand [1 ; 3 ; 5 ; 7 ; 9] compare_int = true)
  and t2 = (cand [2 ; 5 ; 3 ; 2 ; 13] compare_int = false)
  and t3 = (cand [2 ; 5 ; 7 ; 9 ; 8] compare_int = false)
  in (t0 && t1 && t2 && t3)
;;

(* Helper function to check if a list with at least one element is ordered *)
let rec is_ordered_cons (e : 'a)
                        (es' : 'a list)
                        (compare : 'a -> 'a -> comparison) : bool =
  match es' with
  | []         ->
     true
  | e' :: es'' ->
     match compare e e' with
     | Lt ->
       is_ordered_cons e' es'' compare
     | _  ->
        false
;;

(* Function to check if a list is ordered *)
let is_ordered_list (es : 'a list)
                    (compare : 'a -> 'a -> comparison) : bool =
  match es with
  | []       ->
     true
  | e :: es' ->
     is_ordered_cons e es' compare
;;

let _ = assert (test_is_ordered_list is_ordered_list);;

(* Unit tests for is_ordered_hbt *)
let test_is_ordered_hbt (cand : int heightened_binary_tree ->
                                (int -> int -> comparison) -> bool) : bool = 
  let t0 = (cand hbt_0 compare_int = true)
  and t1 = (cand hbt_1 compare_int = true)
  and t2 = (cand hbt_2 compare_int = true)
  and t3 = (cand hbt_5 compare_int = true)
  and t4 = (cand unordered_hbt_0 compare_int = false)
  and t5 = (cand unordered_hbt_1 compare_int = false)
  and t6 = (cand unordered_hbt_2 compare_int = false)
  in (t0 && t1 && t2 && t3 && t4 && t5 && t6)
;;

(* Function to check whether heightened_binary_tree is in order *)
let is_ordered_hbt (hbt : 'a heightened_binary_tree)
                   (compare : 'a -> 'a -> comparison) : bool =
  is_ordered_list (hbt_to_list hbt) compare
;;

let _ = assert (test_is_ordered_hbt is_ordered_hbt);;


(* let is_ordered_listless show_yourself compare (hbt : 'a heightened_binary_tree) = *)
(*   raise Not_implemented_yet;; *)


(* let () = assert (test_is_ordered is_ordered_listless);; *)

(* Consider implementing listless version if time permits *)

(* Unit tests for is_ordered_hbta *)
let test_is_ordered_hbta (cand : int heightened_binary_tree_alternative ->
                                (int -> int -> comparison) -> bool) = 
  let t0 = (cand (hbt_to_hbta hbt_0) compare_int = true)
  and t1 = (cand (hbt_to_hbta hbt_1) compare_int = true)
  and t2 = (cand (hbt_to_hbta hbt_2) compare_int = true)
  and t3 = (cand (hbt_to_hbta hbt_5) compare_int = true)
  and t4 = (cand (hbt_to_hbta unordered_hbt_0) compare_int = false)
  and t5 = (cand (hbt_to_hbta unordered_hbt_1) compare_int = false)
  and t6 = (cand (hbt_to_hbta unordered_hbt_2) compare_int = false)
  in (t0 && t1 && t2 && t3 && t4 && t5 && t6)
;;

(* Function to check whether heightened_binary_tree_alternative is in order *)
let is_ordered_hbta (hbta : 'a heightened_binary_tree_alternative)
                    (compare : 'a -> 'a -> comparison) : bool =
  is_ordered_list (hbta_to_list hbta) compare
;;

let _ = assert (test_is_ordered_hbta is_ordered_hbta);;

(* ********** *)

(*
The three independent properties of AVL trees: 
(i) Soundness: The notion that the height of each sub-tree is correct. 
(ii) Balancedness: The notion that for each node, the height difference between 
its sub-trees is at most 1. 
(iii) In-orderedness: The notion that the payloads of the tree are in-order (hahah 
self-referential defintion. Use the one in the proposal).  

See the coq file for a formalization of this notion 
*)

(* ********** *)

(* ********** *)

(* Comparing two heightened binary trees eagerly for equality: *)

let equal_heightened_binary_tree compare ((h1, _) as hbt1 : 'a heightened_binary_tree) ((h2, _) as hbt2 : 'a heightened_binary_tree) =
  let rec traverse e1s e2s =
    match e1s with
    | [] ->
       (match e2s with
        | [] ->
           true
        | e2 :: e2s' ->
           false)
    | e1 :: e1s' ->
       (match e2s with
        | [] ->
           false
        | e2 :: e2s' ->
           (match compare e1 e2 with
            | Eq ->
               traverse e1s' e2s'
            | _ ->
               false))
  in h1 = h2 && traverse (hbt_to_list hbt1) (hbt_to_list hbt2);;

(* ********** *)

(* Comparing two heightened binary trees lazily for equality: *)

let lazy_equal_heightened_binary_tree compare ((h1, _) as hbt1 : 'a heightened_binary_tree) ((h2, _) as hbt2 : 'a heightened_binary_tree) =
  let rec traverse le1s le2s =
    match le1s with
    | Lazy_nil ->
       (match le2s with
        | Lazy_nil ->
           true
        | Lazy_cons (e2, thunk2) ->
           false)
    | Lazy_cons (e1, thunk1) ->
       (match le2s with
        | Lazy_nil ->
           false
        | Lazy_cons (e2, thunk2) ->
           (match compare e1 e2 with
            | Eq ->
               traverse (force thunk1) (force thunk2)
            | _ ->
               false))
  in h1 = h2 && traverse (hbt_to_lazy_list hbt1) (hbt_to_lazy_list hbt2);;

(* ********** *)

(* Testing whether an element occurs in a heightened binary tree:
*)
let test_occurs candidate =
     (candidate compare_int 10 (obt_to_hbt OLeaf)
      = false)
  && (candidate compare_int 10 (obt_to_hbt (ONode (OLeaf,
                                                   10,
                                                   OLeaf)))
      = true)
  && (candidate compare_int 10 (obt_to_hbt (ONode (OLeaf,
                                                   20,
                                                   OLeaf)))
      = false)
  && (candidate compare_int 2 hbt_1 = true)
  && (candidate compare_int 20 hbt_3 = false)
  && (candidate compare_int 9 hbt_4 = true)
  && (candidate compare_int 11 hbt_5 = true)
  && (candidate compare_int 32 hbt_5 = false)
;;
(* etc. *);;

(* Exercise 6:
   extend this unit-test function with more unit tests.
*)

let occurs compare e (hbt : 'a heightened_binary_tree) =
  let rec visit es =
    match es with
    | [] ->
       false
    | e' :: es' ->
       (match compare e e' with
        | Eq ->
           true
        | _ ->
           visit es')
  in visit (hbt_to_list hbt);;

let () = assert (test_occurs occurs);;

(* Exercise 7:
   implement a listless version of occurs,
   i.e., a version that does not construct an intermediary list.
*)

let occurs_listless compare e (hbt : 'a heightened_binary_tree) =
  let rec traverse bt =
    match bt with
    | Leaf -> false
    | Node ((_, bt1), e', (_, bt2)) ->
       match compare e e' with
       | Lt -> traverse bt1
       | Gt -> traverse bt2
       | Eq -> true
  in
  match hbt with
  | (_, Leaf) -> false
  | (_, bt) -> traverse bt
;;


let () = assert (test_occurs occurs_listless);;


(* Solution for Exercise 7: *)

let occurs_listless compare e (hbt : 'a heightened_binary_tree) =
  let rec climb_hbt (h, t) =
    climb_bt t
  and climb_bt t =
    match t with
    | Leaf ->
       false
    | Node (hbt1, e', hbt2) ->
       (match compare e e' with
        | Lt ->
           climb_hbt hbt1
        | Eq ->
           true
        | Gt ->
           climb_hbt hbt2)
  in climb_hbt hbt;;

let () = assert (test_occurs occurs_listless);;

(* Exercise D:
   justify why occurs_listless, when applied to an ordered and balanced tree,
   returns a Boolean,
   and does so in logarithmically many recursive calls
   wrt. the number of nodes in the given tree.
   (Huh, try not to paraphrase the code...)

Because at each recursive call, the sub-tree in which the search is conducted gets halved. 
*)

(* ********** *)

(* Inserting an element in a heightened binary tree:
*)

let hbt_empty = obt_to_hbt OLeaf;;

let test_insert_int candidate =
  (is_sound    show_int
               (candidate show_int compare_int 1 (candidate show_int compare_int 2 hbt_empty)))
  && (is_balanced show_int
                  (candidate show_int compare_int 1 (candidate show_int compare_int 2 hbt_empty)))
  && (is_ordered  show_int
                  compare_int
                  (candidate show_int compare_int 1 (candidate show_int compare_int 2 hbt_empty)))
  &&
    (is_sound    show_int
                 (candidate show_int compare_int 2 (candidate show_int compare_int 1 hbt_empty)))
  && (is_balanced show_int
                  (candidate show_int compare_int 2 (candidate show_int compare_int 1 hbt_empty)))
  && (is_ordered  show_int
                  compare_int
                  (candidate show_int compare_int 2 (candidate show_int compare_int 1 hbt_empty)))
  &&
    (lazy_equal_heightened_binary_tree compare_int
                                       (candidate show_int compare_int 1 (candidate show_int compare_int 2 hbt_empty))
                                       (candidate show_int compare_int 2 (candidate show_int compare_int 1 hbt_empty)))
  && (is_sound show_int  (candidate show_int compare_int 15 hbt_1))
  && (is_balanced show_int  (candidate show_int compare_int 15 hbt_1))
  && (is_ordered  show_int compare_int (candidate show_int compare_int 15 hbt_1))
;;



      




  
(* The following naive function might return an imbalanced tree:
*)

let insert_first_shot show_yourself compare e (hbt : 'a heightened_binary_tree) =
  let rec climb_hbt (h, bt) =
    climb_bt bt
  and climb_bt bt =
    match bt with
    | Leaf ->
       (1, Node ((0, Leaf), e, (0, Leaf)))
    | Node (((h1, bt1) as hbt1), e', ((h2, bt2) as hbt2)) ->
       (match compare e e' with
        | Lt ->
           let ((h1', bt1') as hbt1') = climb_hbt hbt1
           in (1 + max h1' h2, Node (hbt1', e', hbt2))
        | Eq ->
           raise Bail_out
        | Gt ->
           let ((h2', bt2') as hbt2') = climb_hbt hbt2
           in (1 + max h1 h2', Node (hbt1, e', hbt2')))
  in try climb_hbt hbt
     with
     | Bail_out ->
        hbt;;

let () = assert (test_insert_int insert_first_shot);;

(*
   # pp_heightened_binary_tree show_int hbt_empty;;
   (0, 
    Leaf)
   - : unit = ()
   # pp_heightened_binary_tree show_int (insert_first_shot compare_int 1 hbt_empty);;
   (1, 
    Node ((0, 
           Leaf), 
          1, 
          (0, 
           Leaf)))
   - : unit = ()
   # pp_heightened_binary_tree show_int (insert_first_shot compare_int 2 (insert_first_shot compare_int 1 hbt_empty));;
   (2, 
    Node ((0, 
           Leaf), 
          1, 
          (1, 
           Node ((0, 
                  Leaf), 
                 2, 
                 (0, 
                  Leaf)))))
   - : unit = ()
   # 
*)

(* Exercise 8:
   massively expand this unit-test function with more unit tests.
   Your measure of success is that insert_first_shot should fail to pass it: we have done so,
   and the unit test fails to pass. 
*)

(* function to insert a list of values into a binary tree *)
let insert_list insert show_yourself compare xs_init (hbt_init : 'a heightened_binary_tree) =
  let rec visit xs hbt =
    match xs with
    | [] ->
       hbt
    | x :: xs' ->
       visit xs' (insert show_yourself compare x hbt)
  in visit xs_init hbt_init;;

(* function to merge lists *)
let rec merge_lists xs ys =
  match xs with
  | [] ->
     ys
  | x :: xs' ->
     x :: (match ys with
           | [] ->
              xs'
           | y :: ys' ->
              y :: (merge_lists xs' ys'));;

(* returns an int list with values between 1 and n_init*)
let atoi n_init =
  (* atoi : int -> int list *)
  let rec countdown n =
    if n = 0
    then []
    else let n' = n - 1
         in n' :: countdown n'
  in if n_init >= 0
     then countdown n_init
     else raise (Failure "atoi");;

(* returns an int list with values between n_init and 1 *)
let iota n_init =
  (* atoi : int -> int list *)
  let rec visit n a =
    match n with
    | 0 ->
       a
    | _ ->
       let n' = n - 1
       in visit n' (n' :: a)
  in if n_init >= 0
     then visit n_init []
     else raise (Failure "iota");;

(*
   # iota 50;;
   - : int list =
   [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20;
    21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31; 32; 33; 34; 35; 36; 37; 38; 39;
    40; 41; 42; 43; 44; 45; 46; 47; 48; 49]
   # let hbt50 = insert_list insert show_int compare_int (iota 50) hbt_empty;;
   val hbt50 : int heightened_binary_tree =
     ...
   # is_ordered show_int compare_int hbt50;;
   - : bool = true
   # is_balanced show_int hbt50;;
   - : bool = true
   # let hbt50' = insert_list insert show_int compare_int (atoi 50) hbt_empty;;
   val hbt50' : int heightened_binary_tree =
     ...
   # is_ordered show_int compare_int hbt50';;
   - : bool = true
   # is_balanced show_int hbt50';;
   - : bool = true
   # let hbt100 = insert_list insert show_int compare_int (merge_lists (atoi 50) (List.map (fun n -> n+1) (iota 50))) hbt_empty;;
   val hbt100 : int heightened_binary_tree =
     ...
   # is_ordered show_int compare_int hbt100;;
   - : bool = true
   # is_balanced show_int hbt100;;
   - : bool = true
   # let hbt100' = insert_list insert show_int compare_int (merge_lists (List.map (fun n -> n+1) (iota 50)) (atoi 50)) hbt_empty;;
   val hbt100' : int heightened_binary_tree =
     ...
   # is_ordered show_int compare_int hbt100';;
   - : bool = true
   # is_balanced show_int hbt100';;
   - : bool = true
   # let hbt90 = insert_list insert show_int compare_int (merge_lists (atoi 50) (List.map (fun n -> n+40) (iota 50))) hbt_empty;;
   val hbt90 : int heightened_binary_tree =
     ...
   # let hbt90' = insert_list insert show_int compare_int (merge_lists (List.map (fun n -> n+40) (iota 50)) (atoi 50)) hbt_empty;;
   val hbt90' : int heightened_binary_tree =
     ...
   # is_ordered show_int compare_int hbt90;;
   - : bool = true
   # is_ordered show_int compare_int hbt90';;
   - : bool = true
   # is_balanced show_int hbt90;;
   - : bool = true
   # is_balanced show_int hbt90';;
   - : bool = true
   # 
*)

(* Exercise 9:
   think about a version of insert that yields a balanced tree
   and therefore that passes the unit test.
*)

exception Imbalanced;;

exception Unsatisfied_assumption;;

let rotate_right show_yourself ((_, bt1) as hbt1) e ((h2, bt2) as hbt2) =
  match bt1 with
  | Leaf ->
     let () = Printf.printf "rotate_right outer impossible case: %s\n"
                            (show_heightened_binary_tree show_yourself hbt1)
     in raise Unsatisfied_assumption
  | Node (((h11, bt11) as hbt11), e1, ((h12, bt12) as hbt12)) ->
     if h11 + 1 = h12
     then match bt12 with
          | Leaf ->
             let () = Printf.printf "rotate_right inner impossible case: %s\n"
                                    (show_heightened_binary_tree show_yourself hbt12)
             in raise Unsatisfied_assumption
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

(* Exercise E:
   justify why rotate_right, when applied to the triple from a balanced tree,
   returns a balanced tree.
   (Huh, try not to paraphrase the code...)
*)

let rotate_left show_yourself ((h1, bt1) as hbt1) e ((_, bt2) as hbt2) =
  match bt2 with
  | Leaf ->
     let () = Printf.printf "rotate_left outer impossible case: %s\n"
                            (show_heightened_binary_tree show_yourself hbt2)
     in raise Unsatisfied_assumption
  | Node (((h21, bt21) as hbt21), e2, ((h22, bt22) as hbt22)) ->
     if h21 = h22 + 1
     then match bt21 with
          | Leaf ->
             let () = Printf.printf "rotate_left inner impossible case: %s\n"
                                    (show_heightened_binary_tree show_yourself hbt21)
             in raise Unsatisfied_assumption
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

(* Exercise F:
   justify why rotate_left, when applied to the triple from a balanced tree,
   returns a balanced tree.
   (Huh, try not to paraphrase the code...)
*)

let insert show_yourself compare x (hbt : 'a heightened_binary_tree) =
  let rec climb_hbt (h, bt) =
    climb_bt h bt
  and climb_bt h bt =
    match bt with
    | Leaf ->
       (1, Node ((0, Leaf), x, (0, Leaf)))
    | Node (((h1, bt1) as hbt1), e, ((h2, bt2) as hbt2)) ->
       if h = 1 + max h1 h2 && differ_by_one h1 h2 (* sanity check *)
       then match compare x e with
            | Lt ->
               let ((h1', bt1') as hbt1') = climb_bt h1 bt1
               in if h1' - h2 = 2
                  then rotate_right show_yourself hbt1' e hbt2
                  else (1 + max h1' h2, Node (hbt1', e, hbt2))
            | Eq ->
               raise Bail_out
            | Gt ->
               let ((h2', bt2') as hbt2') = climb_bt h2 bt2
               in if h2' - h1 = 2
                  then rotate_left show_yourself hbt1 e hbt2'
                  else (1 + max h1 h2', Node (hbt1, e, hbt2'))
       else let () = Printf.printf "insert %s in imbalanced given subtree: %s\n"
                                   (show_yourself x)
                                   (show_heightened_binary_tree show_yourself (h, bt))
            in raise Imbalanced
  in try climb_hbt hbt
     with
     | Bail_out ->
        hbt;;

(* Exercise G:
   justify why insert, when applied to an element and a balanced tree,
   returns a ordered and balanced tree containing this element,
   and does so in logarithmically many recursive calls
   wrt. the number of nodes in the given tree.
   (Huh, try not to paraphrase the code...)
*)

let () = assert (test_insert_int insert);;

(* Exercise 10:
   we want more useful information out of the unit-test function than a Boolean.
   Suggestions?
*)

(* ********** *)

(* Exercise H:
   implement an OCaml function factor_rightmost that,
   given a triple from a balanced tree, returns a pair
     (hbt, e)
   where e is the rightmost element in the triple
   and hbt is balanced,
   and does so in logarithmically many recursive calls
   wrt. the number of nodes in the given tree.
   Justify your implementation.
   (Huh, try not to paraphrase the code...)
 *)



let test_factor_rightmost_int candidate =
     (candidate show_int compare_int ((0, Leaf), 10, (0, Leaf))
      (* originally from:   (1, Node ((0, Leaf), 10, (0, Leaf))) *)
      = ((0, Leaf), 10))
  && (candidate show_int compare_int ((0, Leaf), 10, (1, Node ((0, Leaf), 20, (0, Leaf))))
      (* originally from:   (2, Node ((0, Leaf), 10, (1, Node ((0, Leaf), 20, (0, Leaf))))) *)
      = ((1, Node ((0, Leaf), 10, (0, Leaf))), 20))
  && (candidate show_int compare_int ((1, Node ((0, Leaf), 5, (0, Leaf))), 10, (1, Node ((0, Leaf), 20, (0, Leaf))))
      (* originally from:   (2, Node ((1, Node ((0, Leaf), 5, (0, Leaf))), 10, (1, Node ((0, Leaf), 20, (0, Leaf))))) *)
      = ((2, Node ((1, Node ((0, Leaf), 5, (0, Leaf))), 10, (0, Leaf))), 20))
  && (candidate show_int compare_int
                (
                  (2,
                   Node
                     ((1,
                       Node
                         ((0, Leaf),
                          2,
                          (0, Leaf))),
                      3,
                      (1,
                       Node
                         ((0, Leaf),
                          4,
                          (0, Leaf))))),
                  5,
                  (1,
                   Node
                     ((0, Leaf),
                      10,
                      (0, Leaf)))
                )
      = (
        (3,
         Node
           ((1,
             Node
               ((0, Leaf),
                2,
                (0, Leaf))),
            3,
            (2,
             Node
               ((1,
                 Node
                   ((0, Leaf),
                    4,
                    (0, Leaf))),
                5,
                (0, Leaf))))),
        10)
     )
   
  (* etc. *);;

let factor_rightmost show_yourself compare (t : 'a triple) =
  let rec traverse t =
    match t with
    (* this is the base case for a triple; we wish to delete this node *)
    | (hbt1, e, (0, Leaf)) ->
       (hbt1, e)
    | (((h1, bt1) as hbt1), e, (h2, Node ((hbt21, e2, hbt22) as t2))) ->
       begin
         match traverse t2 with
         | (((h2', bt2')as hbt2'), e') ->
            (* check to see if the deletion leads to an imbalance; note that the tree can
             * only be left-imbalanced*)
            if h1 - h2' = 2
            then
              let new_hbt = rotate_right show_yourself (hbt1) e (hbt2')
              in (new_hbt, e')
            else
              (* if it is the case that there is no imbalance *)
              let new_hbt = (1 + max h1 h2', Node (hbt1, e, hbt2'))
              in (new_hbt, e')
       end
    | _ -> let () = Printf.printf "factor_rightmost impossible case:"
           in raise Unsatisfied_assumption

  in
  traverse t
;;
       
       
let () = assert (test_factor_rightmost_int factor_rightmost);;


(* ********** *)

(* Exercise I:
   implement an OCaml function factor_leftmost that,
   given a triple from a balanced tree, returns a pair
     (e, hbt)
   where e is the leftmost element in the triple
   and hbt is balanced,
   and does so in logarithmically many recursive calls
   wrt. the number of nodes in the given tree.
   Justify your implementation.
   (Huh, try not to paraphrase the code...)
*)

let test_factor_leftmost_int candidate =
  (* write these unit tests *)
  (candidate show_int compare_int ((0, Leaf), 10, (0, Leaf)) =
     (10, (0, Leaf)))
  && (candidate show_int compare_int
                ((0, Leaf),
                 10,
                 (1,
                  Node
                    ((0, Leaf),
                     20,
                     (0, Leaf)))) =
        (10,
          (1,
           Node
             ((0, Leaf),
              20,
              (0, Leaf)))))
  && (candidate show_int compare_int
                ((1,
                  Node
                    ((0, Leaf),
                     3,
                     (0, Leaf))),
                 10,
                 (2,
                  Node
                    ((1,
                      Node
                           ((0, Leaf),
                            12,
                            (0, Leaf))),
                     15,
                     (1,
                      Node
                        ((0, Leaf),
                         17,
                         (0, Leaf)))))) =
        (3, (3,
          Node
            ((2,
              Node
                ((0, Leaf),
                 10,
                 (1,
                  Node
                    ((0, Leaf),
                     12,
                     (0, Leaf))))),
             15,
             (1,
              Node
                ((0, Leaf),
                 17,
                 (0, Leaf)))))))

;;

let factor_leftmost show_yourself compare (t : 'a triple) =
  let rec traverse t =
    match t with
    | ((0, Leaf), e, hbt2) ->
       (e, hbt2)
    | ((h1, Node ((hbt11, e1, hbt12) as t)), e, ((h2, bt2) as hbt2)) ->
       begin
         match traverse t with
         | (e', ((h1', bt1') as hbt1')) ->
            (* check for imbalance *)
            if h2 - h1' = 2
            then
              let new_hbt = rotate_left show_yourself (hbt1') e (hbt2)
              in (e', new_hbt)
            else
              let new_hbt = (1 + max h1' h2, Node (hbt1', e, hbt2))
              in (e', new_hbt)
       end
    | _ ->
       let () = Printf.printf "factor_rightmost impossible case:"
       in raise Unsatisfied_assumption
  in
  traverse t
;;



let () = assert (test_factor_leftmost_int factor_leftmost);;


(* ********** *)

let rec all_truep bs =
  match bs with
  | [] ->
     true
  | b :: bs' ->
     b && all_truep bs';;

let test_delete_int candidate =
  (all_truep (List.map (is_ordered show_int compare_int) (List.map (fun i -> (candidate show_int compare_int (Random.int 200) (candidate show_int compare_int (Random.int 200) (insert_list insert show_int compare_int (merge_lists (atoi 100) (List.map (fun i -> i + 88) (iota 100))) hbt_empty)))) (iota 200))))
  &&
 -   (all_truep (List.map (is_balanced show_int) (List.map (fun i -> (candidate show_int compare_int (Random.int 200) (candidate show_int compare_int (Random.int 200) (insert_list insert show_int compare_int (merge_lists (atoi 100) (List.map (fun i -> i + 88) (iota 100))) hbt_empty)))) (iota 200))))
;;

;;
(* Exercise J:
   expand this unit-test function with more unit tests,
   and justify your tests.
*)

let delete show_yourself compare x (hbt : 'a heightened_binary_tree) =
  let rec climb_hbt (h, bt) =
    climb_bt h bt
  and climb_bt h bt =
    match bt with
    | Leaf ->
       raise Bail_out
    | Node (((h1, bt1) as hbt1), e, ((h2, bt2) as hbt2)) ->
       if h = 1 + max h1 h2 && differ_by_one h1 h2 (* sanity check *)
       then match compare x e with
            | Lt ->
               let ((h1', t1') as hbt1') = climb_bt h1 bt1
               in if h2 - h1' = 2
                  then rotate_left show_yourself hbt1' e hbt2
                  else (1 + max h1' h2, Node (hbt1', e, hbt2))
            | Eq ->
               (match h1 - h2 with
                | -1 ->
                   (match bt2 with
                    | Leaf ->
                       let () = Printf.printf "delete Eq impossible case 2: %s\n"
                                              (show_heightened_binary_tree show_yourself hbt2)
                       in raise Unsatisfied_assumption
                    | Node t2 ->
                       let (e2', ((h2', bt2') as hbt2')) = factor_leftmost show_yourself compare t2
                       in (1 + max h1 h2', Node (hbt1, e2', hbt2')))
                | 1 ->
                   (match bt1 with
                    | Leaf ->
                       let () = Printf.printf "delete Eq impossible case 1: %s\n"
                                              (show_heightened_binary_tree show_yourself hbt1)
                       in raise Unsatisfied_assumption
                    | Node t1 ->
                       let (((h1', bt1') as hbt1'), e1') = factor_rightmost show_yourself compare t1
                       in (1 + max h1' h2, Node (hbt1', e1', hbt2)))
                | _ -> (* i.e., 0 since "differ_by_one h1 h2" evaluated to true *)
                   if Random.bool ()
                   then (match bt1 with
                         | Leaf ->
                            (0, Leaf)
                         | Node t1 ->
                            let (((h1', bt1') as hbt1'), e1') = factor_rightmost show_yourself compare t1
                            in (1 + max h1' h2, Node (hbt1', e1', hbt2)))
                   else (match bt2 with
                         | Leaf ->
                            (0, Leaf)
                         | Node t2 ->
                            let (e2', ((h2', bt2') as hbt2')) = factor_leftmost show_yourself compare t2
                            in (1 + max h1 h2', Node (hbt1, e2', hbt2'))))
            | Gt ->
               let ((h2', t2') as hbt2') = climb_bt h2 bt2
               in if h1 - h2' = 2
                  then rotate_right show_yourself hbt1 e hbt2'
                  else (1 + max h1 h2', Node (hbt1, e, hbt2'))
       else let () = Printf.printf "delete %s in imbalanced given subtree: %s\n"
                                   (show_yourself x)
                                   (show_heightened_binary_tree show_yourself (h, bt))
            in raise Imbalanced
  in try climb_hbt hbt
     with
     | Bail_out ->
        hbt;;


let () = assert (test_delete_int delete);;


(* Exercise K:
   justify why delete, when applied to an element and a balanced tree,
   returns a ordered and balanced tree that does not contain this element,
   and does so in logarithmically many recursive calls
   wrt. the number of nodes in the given tree.
   (Huh, try not to paraphrase the code...)
*)

(* ********** *)

(* end of week-02b_balanced-binary-trees.ml *)

"week-02b_balanced-binary-trees.ml"
