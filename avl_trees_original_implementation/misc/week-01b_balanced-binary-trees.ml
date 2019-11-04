(* week-01b_balanced-binary-trees.ml *)
(* Introduction to Data Structures and Algorithms (YSC2229), Sem2, 2017-2018 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of Sat 20 Jan 2018 *)
(* with no spurious uses of flatten *)
(* was: *)
(* Version of Fri 19 Jan 2018 *)

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

(* A data type for ordinary polymorphic binary tree; payload in the nodes *)

type 'a ordinary_binary_tree = OLeaf
                             | ONode of 'a ordinary_binary_tree * 'a * 'a ordinary_binary_tree;;

(* ********** *)

(* A data type for polymorphic binary trees indexed with their height: *)

type 'a heightened_binary_tree = int * 'a binary_tree
 and 'a triple = 'a heightened_binary_tree * 'a * 'a heightened_binary_tree
 and 'a binary_tree = Leaf
                    | Node of 'a triple;;

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

(* Oishik's solution *)  
let obt_to_hbt' obt_init =
  let rec traverse_obt obt =
    match obt with
    | OLeaf -> (0, Leaf)
    | ONode (l_obt, n, r_obt) ->
       (* traverse the right and left obts and convert them to hbt *)
       let l_hbt = traverse_obt l_obt in
       let r_hbt = traverse_obt r_obt in
       (* retrieve the heights of the sub-trees to compute the height of the 
        * present one *)
       match r_hbt, l_hbt with
       | (h_r, _) , (h_l, _) ->
          if h_r > h_l
          then (h_r + 1, Node (l_hbt, n, r_hbt))
          else (h_l + 1, Node (l_hbt, n, r_hbt))
  in traverse_obt (obt_init)
;;
  
let () = assert (test_obt_to_hbt obt_to_hbt');;
  


(* Professor Danvy's solution *)  
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


(* code to test to the pretty printing functions *)

let show_integer e = string_of_int e
;;
  pp_heightened_binary_tree show_integer hbt_0
;;
  pp_heightened_binary_tree show_integer hbt_1
;;
  pp_heightened_binary_tree show_integer hbt_4
;;
      

(* ********** *)

(* Exercise 1:
   implement a function that checks that the heights,
   in a given heightened binary tree, are accurate.
*)

(* oishik' solution using option types (naive implementation) *)

let is_sound'' (hbt_init : 'a heightened_binary_tree) =
  let rec traverse_hbt hbt =
    match hbt with
    | (h, Leaf) ->
       if h = 0
       then Some (h, Leaf)
       else None
    (* retrieve heights of left and right subtrees; check if the max of these
     * values + 1 is equal to h or not*)
    | (h, Node (hbt_1, e, hbt_2)) ->
       match traverse_hbt hbt_1 with
       | None -> None
       | Some (h_1, _) ->
          match traverse_hbt hbt_2 with
          | None -> None
          | Some (h_2, _) ->
             if max h_1 h_2 + 1 = h
             then Some (h, Node (hbt_1, e, hbt_2))
             else None
  in
  match traverse_hbt hbt_init with
  | None -> false
  | Some (_, _) -> true
;;

(* quick and dirty test for this function *)

(* unit tests for is_sound *)

let test_is_sound candidate =
  (candidate hbt_0 = true)
  &&
    (candidate hbt_2 = true)
  &&
    (candidate hbt_3 = true)
  &&
    (candidate hbt_4 = true)
  &&
    (candidate hbt_with_height_error_0 = false)
  &&
    (candidate hbt_with_height_error_1 = false)
  &&
    (candidate hbt_with_height_error_2 = false)
;;

let () = assert (test_is_sound is_sound'')
;;
  
(* Professor Danvy's solution for Exercise 1, using an option type: *)

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
                     else Printf.printf "is_sound: %s and %s\n"
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

(* oishik's solution for heightened binary trees using an accumulator*)
let flatten_binary_tree hbt_init =
  let rec traverse_bt (h, bt) acc = 
    match bt with
    | Leaf ->
       acc
    | Node (hbt_1 , e , hbt_2) ->
       traverse_bt hbt_1 (e :: (traverse_bt hbt_2 acc))
  in
  traverse_bt hbt_init []
;;

(* quick and dirty tests *)
  flatten_binary_tree hbt_2;;
  flatten_binary_tree hbt_3;;
    flatten_binary_tree hbt_4;;

(* Professor Danvy's solution *)

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

hbt_to_list hbt_2;;  

(* ********** *)

(* Flattening a binary tree into a lazy list: *)

type 'a lazy_list =
  | Lazy_nil
  | Lazy_cons of 'a * (unit -> 'a lazy_list);;

let force thunk =
  thunk ();;

(* oishik's solution *)
let lazy_flatten_binary_tree' bt_init =
  let rec traverse_bt bt acc =
    match bt with
    | Leaf ->
       acc
    | Node ((_, bt_1) , e , (_, bt_2)) ->
       traverse_bt bt_1
                   (Lazy_cons (e,
                               (fun () -> traverse_bt bt_2 acc)))
  in
  traverse_bt bt_init Lazy_nil
;;


let hbt_to_lazy_list' ((h, bt) : 'a heightened_binary_tree) =
  lazy_flatten_binary_tree' bt
;;

(* quick and dirty test *)

let (Lazy_cons (y, lazy_ys)) = hbt_to_lazy_list' hbt_2;;
  force lazy_ys;;

  (* unit tests for hbt_to_lazy_list *)


let test_hbt_to_lazy_list_helper candidate hbt xs =
  let lazy_xs = candidate hbt
  in 
  let rec traverse_lazy_list lazy_ys ys =
    match lazy_ys, ys with
    | Lazy_nil, [] ->
       true
    | Lazy_cons (y, lazy_ys'), x::xs' ->
       if y = x
       then traverse_lazy_list (force lazy_ys') xs'
       else false
    | _, _ -> false
  in
  traverse_lazy_list lazy_xs xs
;;

let test_hbt_to_lazy_list candidate =
  (test_hbt_to_lazy_list_helper candidate hbt_0 [])
  &&
    (test_hbt_to_lazy_list_helper candidate hbt_1 [1; 2])
  &&
    (test_hbt_to_lazy_list_helper candidate hbt_2 [1; 2; 3])
  &&
    (test_hbt_to_lazy_list_helper candidate hbt_3 [1; 2; 3; 4; 5])
  &&
    (test_hbt_to_lazy_list_helper candidate hbt_4
                                  [1; 3; 4; 5; 6; 7; 8; 9; 10; 11; 13])
;;
  
let () = assert (test_hbt_to_lazy_list hbt_to_lazy_list');;


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

let () = assert (test_hbt_to_lazy_list hbt_to_lazy_list);;

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

(* Oishik's solution involving only traversing the trees *)

let equal_heightened_binary_tree'
      compare
      ((h1, bt1_init) as hbt1 : 'a heightened_binary_tree)
      ((h2, bt2_init) as hbt2 : 'a heightened_binary_tree) =
  let rec traverse_bts bt_1 bt_2 =
    match bt_1, bt_2 with
    | Leaf, Leaf -> true
    | Node ((h_11, bt_11), e_1, (h_12, bt_12)),
      Node ((h_21, bt_21), e_2, (h_22, bt_22)) ->
       match compare e_1 e_2 with
       | Eq ->
          if (h_11 = h_21) && (h_12 = h_22)
          then (traverse_bts bt_11 bt_21) &&
                 (traverse_bts bt_12 bt_22)
          else false
       | _ -> false
  in
  if h1 = h2
  then traverse_bts bt1_init bt2_init
  else false
;;

(* quick and dirty test *)
  equal_heightened_binary_tree' compare_int hbt_2 hbt_2;;
  equal_heightened_binary_tree' compare_int hbt_3 hbt_3;;

  (* unit tests *)
let test_equal_heightened_binary_tree candidate compare =
  candidate compare hbt_1 hbt_1 = true
  &&
    candidate compare hbt_3 hbt_3 = true
  &&
    candidate compare hbt_4 hbt_4 = true
  &&
    candidate compare hbt_3 hbt_4 = false
  &&
    candidate compare hbt_2 hbt_1 = false
;;

let () = assert (test_equal_heightened_binary_tree
                   equal_heightened_binary_tree'
                   compare_int);;


(* Professor Danvy's solution involving converting the trees to a list
first *)

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

let () = assert (test_equal_heightened_binary_tree
                   equal_heightened_binary_tree
                   compare_int);;


(* ********** *)

(* Comparing two heightened binary trees lazily for equality: *)

(* oishik's solution *)

let lazy_equal_heightened_binary_tree'
      compare
      ((h1, _) as hbt1 : 'a heightened_binary_tree)
      ((h2, _) as hbt2 : 'a heightened_binary_tree) =
  let rec traverse_lazy_lists x1s x2s =
    match x1s, x2s with
    | Lazy_nil, Lazy_nil -> true
    | Lazy_cons (x1, x1s'), Lazy_cons (x2, x2s') ->
       begin
       match compare x1 x2 with
       | Eq ->
          traverse_lazy_lists (force x1s') (force x2s')
       | _ -> false
       end
    | _ -> false 
  in
  if h1 = h2
  then traverse_lazy_lists
         (hbt_to_lazy_list hbt1)
         (hbt_to_lazy_list hbt2)
  else false
;;
    
(* unit tests *)

let test_lazy_equal_heightened_binary_tree candidate compare =
  candidate compare hbt_1 hbt_1 = true
  &&
    candidate compare hbt_3 hbt_3 = true
  &&
    candidate compare hbt_4 hbt_4 = true
  &&
    candidate compare hbt_3 hbt_4 = false
  &&
    candidate compare hbt_2 hbt_1 = false
;;

let () = assert (test_lazy_equal_heightened_binary_tree
                   lazy_equal_heightened_binary_tree'
                   compare_int);;

(* Professor Danvy's solution *)

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
  
let () = assert (test_lazy_equal_heightened_binary_tree
                   lazy_equal_heightened_binary_tree
                   compare_int);;


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
(* to expand  the unit tests, we add more binary tree examples to the section at
 * the top *)
  
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
  && (candidate show_int hbt_2 = true)
  && (candidate show_int hbt_4 = true)
  && (candidate unbalanced_hbt_0 = false)
  && (candidate unbalanced_hbt_1 = false)
  && (candidate unbalanced_hbt_3 = false)
;;
                                   
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

let is_balanced' show_yourself ((h, bt_init) : 'a heightened_binary_tree) =
  let rec traverse (bt : 'a binary_tree) =
    match bt with
    | Leaf -> Some 0
    | Node ((_, bt_1), e, (_, bt_2)) ->
       (* check if the left sub-tree is balanced *)
       match traverse bt_1 with
       | Some h1->
          (* check if the right sub-tree is balanced *)
          begin
            match traverse bt_2 with
            | Some h2 ->
               (* if both are balanced, compare their current heights *)
               if same_same h1 h2
               then Some (max h1 h2 + 1)
               else None
            | None -> None
          end
       | None -> None
  in
  match traverse bt_init with
  | Some _ -> true
  | None -> false
;;

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
  && (candidate show_int compare_int hbt_3 = true)
  && (candidate show_int compare_int hbt_4 = true)
  && (candidate show_int compare_int hbt_5 = true)
  && (candidate show_int compare_int unordered_hbt_0 = false)
  && (candidate show_int compare_int unordered_hbt_1 = false)
  && (candidate show_int compare_int unordered_hbt_2 = false)
;;

(* Exercise 4:
n   extend this unit-test function with more unit tests.
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
             (* what if e = e'? are we assuming that there are no equalities in 
              * AVL tree payloads *)
           | Lt ->
              visit e' es'
           | _ ->
              false)
     in visit e_init es_init;;

let () = assert (test_is_ordered is_ordered);;

(* Exercise 5:
   implement a listless version of is_ordered.
*)
  
let is_ordered_listless_inefficient show_yourself compare (hbt : 'a heightened_binary_tree) =
  let rec largest_payload bt =
    match bt with
    | Leaf -> None
    | Node (_, e, (0, Leaf)) -> Some e 
    | Node (_ , e, (_, bt2)) ->
       largest_payload bt2
                       
  and smallest_payload bt =
    match bt with
    | Leaf -> None
    | Node ((0,Leaf), e, _) -> Some e 
    | Node ((_, bt1), e, _) ->
       smallest_payload bt1

  and traverse_tree bt =
    match bt with
    | Leaf -> Some true
    | Node ((_, bt1), e, (_, bt2)) ->
       (* traverse the right sub-tree first and check for in-orderness *)
       match traverse_tree bt2 with
       | None -> None
       | Some _ ->
          (* now check if the smallest value of the right sub-tree is greater than e *)
          match smallest_payload bt2 with
          (* implies that the right sub-tree is a leaf; move on to left sub-tree *)
          | None ->
             begin
               (* if this is so, traverse the left sub-tree, checking for in-orderness *)
               match traverse_tree bt1 with
               | None -> None
               | Some _ ->
                  (* if the left sub-tree is in-order, all there is left to check is 
                   * if the largest payload value in the left-subtree is smaller than the 
                   * current expression *)
                  match largest_payload bt1 with
                  (* implies that the left sub-tree is a leaf *)
                  | None -> Some true
                  | Some e'' ->
                     match compare e'' e with
                     | Lt -> Some true
                     | _ -> None
             end
          | Some e' ->
             (* Printf.printf "%s \n" (show_yourself e'); *)
             match compare e' e with
             | Gt ->
                begin
                  (* if this is so, traverse the left sub-tree, checking for in-orderness *)
                  match traverse_tree bt1 with
                  | None -> None
                  | Some _ ->
                     (* if the left sub-tree is in-order, all there is left to check is 
                      * if the largest payload value in the left-subtree is smaller than the 
                      * current expression *)
                     match largest_payload bt1 with
                     (* implies that the left sub-tree is a leaf *)
                     | None -> Some true
                     | Some e'' ->
                        match compare e'' e with
                        | Lt -> Some true
                        | _ -> None
                end
             | _ -> None
  in
  match hbt with
  | (_, Leaf) -> true
  | (_, bt) ->
     match traverse_tree bt with
     | None -> false
     | Some _ -> true
        
;;


let () = assert (test_is_ordered is_ordered_listless_inefficient);;

(* await Danvy's email on how to do this more efficiently; come back to this later *) 


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
   implement a listless version of occurs.
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


(* ********** *)

(* Inserting an element in a heightened binary tree:
*)

let hbt_empty = obt_to_hbt OLeaf;;

let test_insert candidate =
     (is_sound show_int (candidate compare_int 1 (candidate compare_int 2 hbt_empty)))
  && (is_balanced show_int (candidate compare_int 1 (candidate compare_int 2 hbt_empty)))
  && (is_sound show_int (candidate compare_int 2 (candidate compare_int 1 hbt_empty)))
  && (is_balanced show_int (candidate compare_int 2 (candidate compare_int 1 hbt_empty)))
  && (lazy_equal_heightened_binary_tree compare_int
                                        (candidate compare_int 1 (candidate compare_int 2 hbt_empty))
                                        (candidate compare_int 2 (candidate compare_int 1 hbt_empty)))
  (* etc. *);;

(* The following naive function might return an imbalanced tree:
*)

let insert_first_shot compare e (hbt : 'a heightened_binary_tree) =
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

let () = assert (test_insert insert_first_shot);;

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
   massively expand the unit test function with more unit tests.
   Your measure of success is that insert_first_shot should fail to pass it.
*)

(* Exercise 9:
   think about a version of insert that yields a balanced tree
   and therefore that passes the unit test.
 *)

(* this would involve rotations; see next file *)

(* Exercise 10:
   we want more useful information out of the unit-test function than a Boolean.
   Suggestions?
*)

(* ********** *)

(* end of week-01b_balanced-binary-trees.ml *)

"week-01b_balanced-binary-trees.ml"
