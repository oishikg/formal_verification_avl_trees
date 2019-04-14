
(* week-02b_balanced-binary-trees.ml *)
(* Introduction to Data Structures and Algorithms (YSC2229), Sem2, 2017-2018 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of Fri 26 Jan 2018 *)

(* ********** *)

exception Not_implemented_yet;;

(* ********** *)

(* when false: error messages are issued *)
(* when  true: error messages are not issued *)

let silent = ref false;;

(* ********** *)

(* Short cut: *)

exception Bail_out;;

(* ********** *)

(* A data type for ordinary polymorphic binary trees: *)

type 'a ordinary_binary_tree = OLeaf
                             | ONode of 'a ordinary_binary_tree * 'a * 'a ordinary_binary_tree;;

(* ********** *)

(* A data type for polymorphic binary trees indexed with their height: *)
  
type 'a heightened_binary_tree = int * 'a binary_tree
 and 'a triple = 'a heightened_binary_tree * 'a * 'a heightened_binary_tree
 and 'a binary_tree = Leaf
                    | Node of 'a triple;;


(* An alternative data type implementation *)
  
type 'a heightened_binary_tree_alternative =
  | 


(* ********** *)

(* From ordinary binary tree to heightened binary tree: *)

(* Exercise 0:
   implement a function that maps an ordinary binary tree
   to the corresponding heightened binary tree.
 *)


let test_obt_to_hbt candidate =
     (candidate OLeaf
      = (0,
         Leaf))
  && (candidate (ONode (OLeaf,
                        1,
                        ONode (OLeaf,
                               2,
                               OLeaf)))
      = (2, 
         Node ((0, 
                Leaf), 
               1, 
               (1, 
                Node ((0, 
                       Leaf), 
                      2, 
                      (0, 
                       Leaf))))))
  && (candidate (ONode (ONode (OLeaf,
                               1,
                               ONode (OLeaf,
                                      2,
                                      OLeaf)),
                        3,
                        OLeaf))
      = (3, 
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
                Leaf))))
  (* etc. *);;

(* Solution for Exercise 0: *)

let obt_to_hbt obt_init =
  let rec traverse obt =
    match obt with
    | OLeaf ->
       (0, Leaf)
    | ONode (obt1, e, obt2) ->
       let (h1, bt1) as hbt1 = traverse obt1
       and (h2, bt2) as hbt2 = traverse obt2
       in (1 + max h1 h2, Node (hbt1, e, hbt2))
  in traverse obt_init;;

let () = assert (test_obt_to_hbt obt_to_hbt);;

(* ********** *)

(* Added by Oishik Ganguly *)
(* Heightened Binary Trees for testing *)

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




(* heightened binary trees with errors in them *)

(* height errors *)

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

(* balancing error, i.e., the trees are unbalanced *)
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

(* unordered binary trees *)
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
n         (3, Node
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


(* Unparsing paraphernalia (useful for tracing): *)

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

(* ********** *)

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

(* Exercise 1:
   implement a function that checks that the heights,
   in a given heightened binary tree, are accurate.
*)

(* Solution for Exercise 1, using an option type: *)

let is_sound' show_yourself (hbt_init : 'a heightened_binary_tree) =
  let rec climb_hbt ((h, bt) as hbt) =
    match climb_bt bt with
    | None ->
       None
    | Some h' ->
       if h' = h
       then Some h
       else let () = if !silent
                     then ()
                     else Printf.printf "is_sound': %s and %s\n"
                                        (show_int h')
                                        (show_heightened_binary_tree show_yourself hbt)
            in None
  and climb_bt bt =
    match bt with
    | Leaf ->
       Some 0
    | Node (hbt1, e, hbt2) ->
       (match climb_hbt hbt1 with
        | None ->
           None
        | Some h1 ->
           (match climb_hbt hbt2 with
            | None ->
               None
            | Some h2 ->
               Some (1 + max h1 h2)))
  in match climb_hbt hbt_init with
     | None ->
        false
     | Some _ ->
         true;;

(* Solution for Exercise 1, using the exception Bail_out: *)

let is_sound show_yourself (hbt_init : 'a heightened_binary_tree) =
  let rec climb_hbt ((h, bt) as hbt) =
    let h' = climb_bt bt
    in if h' = h
       then h
       else let () = if !silent
                     then ()
                     else Printf.printf "is_sound: %s and %s\n"
                                        (show_int h')
                                        (show_heightened_binary_tree show_yourself hbt)
            in raise Bail_out
  and climb_bt bt =
    match bt with
    | Leaf ->
       0
    | Node (hbt1, e, hbt2) ->
       let h1 = climb_hbt hbt1
       and h2 = climb_hbt hbt2
       in 1 + max h1 h2
  in try let _ = climb_hbt hbt_init
         in true
     with
     | Bail_out ->
        false;;

(* ********** *)

(* Flattening a binary tree into a list: *)

let flatten_binary_tree bt =
  let rec visit bt es =
    match bt with
    | Leaf ->
       es
    | Node ((_, bt1), e, (_, bt2)) ->
       visit bt1 (e :: visit bt2 es)
  in visit bt [];;

(* Mapping a heightened binary tree into the in-order list of its elements: *)

let hbt_to_list ((h, bt) : 'a heightened_binary_tree) =
  flatten_binary_tree bt;;

(* ********** *)

(* Flattening a binary tree into a lazy list: *)

type 'a lazy_list =
  | Lazy_nil
  | Lazy_cons of 'a * (unit -> 'a lazy_list);;

let force thunk =
  thunk ();;

let lazy_flatten_binary_tree bt =
  let rec visit bt thunk =
    match bt with
    | Leaf ->
       force thunk
    | Node ((_, bt1), e, (_, bt2)) ->
       visit bt1 (fun () -> Lazy_cons (e, fun () -> visit bt2 thunk))
  in visit bt (fun () -> Lazy_nil);;

(* Mapping a heightened binary tree into the in-order lazy list of its elements: *)

let hbt_to_lazy_list ((h, bt) : 'a heightened_binary_tree) =
  lazy_flatten_binary_tree bt;;

(* ********** *)

(* Paraphernalia for comparison: *)

type comparison =
  | Lt
  | Eq
  | Gt;;

(* The comparison function for integers: *)

let compare_int i j =
  if i < j then Lt else if i = j then Eq else Gt;;

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

(* Testing whether two heights differ by at most one: *)

let same_same h1 h2 =
  abs (h1 - h2) <= 1;;

(* Traced version thereof: *)

let traced_same_same h1 h2 =
  Printf.printf "same_same %s %s ->\n" (show_int h1) (show_int h2);
  let result = abs (h1 - h2) <= 1
  in Printf.printf "same_same %s %s <- %s\n" (show_int h1) (show_int h2) (show_bool result);
     result;;

(* ********** *)

(* Testing whether a heightened binary tree is balanced,
   i.e., for each of its nodes,
   the height of its subtrees differ by at most one:
*)

let test_is_balanced candidate =
     (candidate show_int (obt_to_hbt OLeaf)
      = true)
  && (candidate show_int (obt_to_hbt (ONode (OLeaf,
                                             1,
                                             ONode (OLeaf,
                                                    2,
                                                    OLeaf))))
      = true)
  && (candidate show_int (obt_to_hbt (ONode (OLeaf,
                                             1,
                                             ONode (OLeaf,
                                                    2,
                                                    ONode (OLeaf,
                                                           3,
                                                           OLeaf)))))
      = false)
  (* etc. *);;

(* Exercise 2:
   extend this unit-test function with more unit tests.
*)

let is_balanced show_yourself (hbt_init : 'a heightened_binary_tree) =
  let rec climb_hbt (h, bt) =
    climb_bt bt
  and climb_bt bt =
    match bt with
    | Leaf ->
       0
    | Node (hbt1, e, hbt2) ->
       let h1 = climb_hbt hbt1
       and h2 = climb_hbt hbt2
       in if same_same h1 h2
          then 1 + max h1 h2
          else let () = if !silent
                        then ()
                        else Printf.printf "is_balanced: %s\n"
                                           (show_binary_tree show_yourself bt)
               in raise Bail_out
  in try let _ = climb_hbt hbt_init
         in true
     with
     | Bail_out ->
        false;;

let () = assert (test_is_balanced is_balanced);;

(* Exercise 3:
   write a version of is_balanced that uses an option type
   instead of an exception.
*)

let is_balanced' show_yourself (hbt_init : 'a heightened_binary_tree) =
  raise Not_implemented_yet;;

(*
let () = assert (test_is_balanced is_balanced');;
*)

(* Solution for Exercise 3: *)

let is_balanced' show_yourself (hbt_init : 'a heightened_binary_tree) =
  let rec climb_hbt (h, bt) =
    climb_bt bt
  and climb_bt bt =
    match bt with
    | Leaf ->
       Some 0
    | Node (hbt1, e, hbt2) ->
       (match climb_hbt hbt1 with
        | None ->
            None
        | Some h1 ->
           (match climb_hbt hbt2 with
            | None ->
               None
            | Some h2 ->
               if same_same h1 h2
               then Some (1 + max h1 h2)
               else None))
  in match climb_hbt hbt_init with
     | None ->
        false
     | Some _ ->
        true;;

let () = assert (test_is_balanced is_balanced');;

(* ********** *)

(* Testing whether a heightened binary tree is ordered,
   i.e., the in-order list of its payloads is increasing:
*)

let test_is_ordered candidate =
     (candidate show_int compare_int (obt_to_hbt OLeaf)
      = true)
     && (candidate show_int compare_int (obt_to_hbt (ONode (OLeaf,
                                                            1,
                                                            OLeaf)))
      = true)
  && (candidate show_int compare_int (obt_to_hbt (ONode (ONode (OLeaf,
                                                                0,
                                                                OLeaf),
                                                         1,
                                                         OLeaf)))
      = true)
  && (candidate show_int compare_int (obt_to_hbt (ONode (ONode (OLeaf,
                                                                0,
                                                                OLeaf),
                                                         1,
                                                         ONode (OLeaf,
                                                                2,
                                                                OLeaf))))
      = true)
  && (candidate show_int compare_int (obt_to_hbt (ONode (ONode (OLeaf,
                                                                0,
                                                                OLeaf),
                                                         0,
                                                         ONode (OLeaf,
                                                                2,
                                                                OLeaf))))
      = false)
  && (candidate show_int compare_int (obt_to_hbt (ONode (ONode (OLeaf,
                                                                0,
                                                                OLeaf),
                                                         2,
                                                         ONode (OLeaf,
                                                                1,
                                                                OLeaf))))
      = false)
  (* etc. *);;

(* Exercise 4:
   extend this unit-test function with more unit tests.
*)

let is_ordered show_yourself compare (hbt : 'a heightened_binary_tree) =
  match hbt_to_list hbt with
  | [] ->
     true
  | e_init :: es_init ->
     let rec visit e es =
       match es with
       | [] ->
          true
       | e' :: es' ->
          (match compare e e' with
           | Lt ->
              visit e' es'
           | _ ->
              false)
     in visit e_init es_init;;

let () = assert (test_is_ordered is_ordered);;

(* Exercise 5:
   implement a listless version of is_ordered,
   i.e., a version that does not construct an intermediary list.
*)

let is_ordered_listless show_yourself compare (hbt : 'a heightened_binary_tree) =
  raise Not_implemented_yet;;

(*
let () = assert (test_is_ordered is_ordered_listless);;
*)

(* Solution for Exercise 5: *)

let is_ordered_listless show_yourself compare (hbt : 'a heightened_binary_tree) =
  let rec climb_hbt (h, t) =
    climb_bt h t
  and climb_bt h t =
    match t with
    | Leaf ->
       None
    | Node (((h1, bt1) as hbt1), e, ((h2, bt2) as hbt2)) ->
       if h = 1 + max h1 h2 && same_same h1 h2 (* sanity check *)
       then let r1 = climb_hbt hbt1
            and r2 = climb_hbt hbt2
            in match r1 with
               | None ->
                  (match r2 with
                   | None ->
                      Some (e, e)
                   | Some (min2, max2) ->
                      (match compare e min2 with
                       | Lt ->
                          Some (e, max2)
                       | _ ->
                          let () = if !silent
                                   then ()
                                   else Printf.printf "is_ordered: %s\n"
                                                      (show_binary_tree show_yourself t)
                          in raise Bail_out))
               | Some (min1, max1) ->
                  (match compare max1 e with
                   | Lt ->
                      (match r2 with
                       | None ->
                          Some (min1, e)
                       | Some (min2, max2) ->
                          (match compare e min2 with
                           | Lt ->
                              Some (min1, max2)
                           | _ ->
                              let () = if !silent
                                       then ()
                                       else Printf.printf "is_ordered: %s\n"
                                                          (show_binary_tree show_yourself t)
                              in raise Bail_out))
                   | _ ->
                      let () = if !silent
                               then ()
                               else Printf.printf "is_ordered: %s\n"
                                                  (show_binary_tree show_yourself t)
                      in raise Bail_out)
       else let () = Printf.printf "imbalanced given subtree in is_ordered_listless: %s\n"
                                   (show_heightened_binary_tree show_yourself (h, bt))
            in raise Imbalanced
  in try (match climb_hbt hbt with
          | None ->
             true
          | Some (min, max) ->
             true)
     with
     | Bail_out ->
        false;;

(* ********** *)

(*
The three independent properties of AVL trees: 
(i) Soundness: The notion that the height of each sub-tree is correct. 
(ii) Balancedness: The notion that for each node, the height difference between its sub-trees
is at most 1. 
(iii) In-orderedness: The notion that the payloads of the tree are in-order (hahah 
self-referential defintion. Use the one in the proposal).  


*)
(* Exercise A1:
   given a value hbt of type
     int heightened_binary_tree
   such that evaluating
     is_sound hbt
   yields true, does evaluating
     is_balanced hbt
   always yields true?

   If yes, justify why.

   If no, exhibit a counter-example.

Ans.  No. The tree may be sound, i.e., the heights of each sub-tree may be correct, but the
tree may nonetheless be unbalanced (e.g. when for some node, the left sub-tree has height 2
and the right sub-tree has height 4
*)

(* Exercise A2:
   given a value hbt of type
     int heightened_binary_tree
   such that evaluating
     is_balanced hbt
   yields true, does evaluating
     is_sound hbt
   always yields true?

   If yes, justify why.

   If no, exhibit a counter-example.

Ans. No. This is because the height values stored at each node may be incorrect. 
*)

(* ********** *)

(* Exercise B1:
   given a value hbt of type
     int heightened_binary_tree
   such that evaluating
     is_ordered hbt
   yields true, does evaluating
     is_balanced hbt
   always yields true?

   If yes, justify why.

   If no, exhibit a counter-example.
Ans. No. A tree may be in order but unbalanced. E.g.
 1
/ \
   2
  / \
*)

(* Exercise B2:
   given a value hbt of type
     int heightened_binary_tree
   such that evaluating
     is_balanced hbt
   yields true, does evaluating
     is_ordered hbt
   always yields true?

   If yes, justify why.

   If no, exhibit a counter-example.
Ans. No. A tree may be balanced, but nonethless not be in-order. E.g.
    10
   /  \
  14   3
*)

(* ********** *)

(* Exercise C1:
   given a value hbt of type
     int heightened_binary_tree
   such that evaluating
     is_sound hbt
   yields true, does evaluating
     is_ordered hbt
   always yields true?

   If yes, justify why.

   If no, exhibit a counter-example.
No, because the payloads themselves have nothing to do with the heights and may not be 
in-order. 
*)

(* Exercise C2:
   given a value hbt of type
     int heightened_binary_tree
   such that evaluating
     is_ordered hbt
   yields true, does evaluating
     is_sound hbt
   always yields true?

   If yes, justify why.

   If no, exhibit a counter-example.
Same explanation as above. 
*)

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
       if h = 1 + max h1 h2 && same_same h1 h2 (* sanity check *)
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
       if h = 1 + max h1 h2 && same_same h1 h2 (* sanity check *)
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
                | _ -> (* i.e., 0 since "same_same h1 h2" evaluated to true *)
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
