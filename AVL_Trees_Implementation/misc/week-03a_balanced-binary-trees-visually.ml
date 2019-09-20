(* week-03a_balanced-binary-trees-visually.ml *)
(* Introduction to Data Structures and Algorithms (YSC2229), Sem2, 2017-2018 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of Tue 30 Jan 2018 *)

(* ********** *)
(*
(* A data type for polymorphic binary trees indexed with their height: *)

type 'a heightened_binary_tree = int * 'a binary_tree
 and 'a triple = 'a heightened_binary_tree * 'a * 'a heightened_binary_tree
 and 'a binary_tree = Leaf
                    | Node of 'a triple;;

let show_int n =
  if n < 0
  then "(" ^ string_of_int n ^ ")"
  else string_of_int n;;
*)
(* ********** *)

(* Two more succinct displaying functions (useful for visualization): *)

let display_heightened_binary_tree show_yourself (hbt : 'a heightened_binary_tree) =
  let rec show_heightened_binary_tree (h, bt) prefix =
    show_binary_tree h bt prefix
  and show_binary_tree h bt prefix =
    match bt with
    | Leaf ->
       ""
    | Node (hbt1, e, hbt2) ->
       show_heightened_binary_tree hbt2 (prefix ^ "  ") (* ^ "\n" *)
       ^
       prefix ^ "(" ^ show_yourself e ^ ", " ^ show_int h ^ ")\n"
       ^
       show_heightened_binary_tree hbt1 (prefix ^ "  ")
  in Printf.printf "%s" (show_heightened_binary_tree hbt "");;

let display_heightened_binary_tree' show_yourself (hbt : 'a heightened_binary_tree) =
  let rec show_heightened_binary_tree (h, bt) prefix =
    show_binary_tree h bt prefix
  and show_binary_tree h bt prefix =
    match bt with
    | Leaf ->
       ""
    | Node (hbt1, e, hbt2) ->
       show_heightened_binary_tree hbt2 (prefix ^ " |") (* ^ "\n" *)
       ^
       prefix ^ " /\n"
       ^
       prefix ^ "(" ^ show_yourself e ^ ", " ^ show_int h ^ ")\n"
       ^
       prefix ^ " \\\n"
       ^
       show_heightened_binary_tree hbt1 (prefix ^ " |")
  in Printf.printf "%s" (show_heightened_binary_tree hbt "");;

(* ********** *)

(* Example:
   tilt your head to the left
   and you will see the binary tree as you draw it.
*)

(*
   # display_heightened_binary_tree' show_int (insert_list insert show_int compare_int (List.map (fun i -> i + 100) (iota 10)) hbt_empty);;
    | | | /
    | | |(109, 1)
    | | | \
    | | /
    | |(108, 2)
    | | \
    | /
    |(107, 3)
    | \
    | | | /
    | | |(106, 1)
    | | | \
    | | /
    | |(105, 2)
    | | \
    | | | /
    | | |(104, 1)
    | | | \
    /
   (103, 4)
    \
    | | /
    | |(102, 1)
    | | \
    | /
    |(101, 2)
    | \
    | | /
    | |(100, 1)
    | | \
   - : unit = ()
   # 
*)

(* More succinctly: *)

(*
   # display_heightened_binary_tree show_int (insert_list insert show_int compare_int (List.map (fun i -> i + 100) (iota 10)) hbt_empty);;
         (109, 1)
       (108, 2)
     (107, 3)
         (106, 1)
       (105, 2)
         (104, 1)
   (103, 4)
       (102, 1)
     (101, 2)
       (100, 1)
   - : unit = ()
   # 
*)

(* ********** *)

let fetch_triple (h, bt) =
  match bt with
  | Leaf ->
     raise (Failure "fetch_triple")
  | Node t ->
     t;;

(* ********** *)

(* Example: rotating a tree to the left. *)

(*
   # let x = insert_list insert_first_shot show_int compare_int [100; 200; 300] hbt_empty;;
   val x : int heightened_binary_tree =
     (3,
      Node
       ((0, Leaf), 100,
        (2, Node ((0, Leaf), 200, (1, Node ((0, Leaf), 300, (0, Leaf)))))))
   # display_heightened_binary_tree show_int x;;
       (300, 1)
     (200, 2)
   (100, 3)
   - : unit = ()
   # let (hbt1, e, hbt2) = fetch_triple x in display_heightened_binary_tree show_int (rotate_left show_int hbt1 e hbt2);;
     (300, 1)
   (200, 2)
     (100, 1)
   - : unit = ()
   # let (hbt1, e, hbt2) = fetch_triple x in let (hbt1', e', hbt2') = fetch_triple (rotate_left show_int hbt1 e hbt2) in display_heightened_binary_tree show_int (rotate_left show_int hbt1' e' hbt2');;
   (300, 3)
     (200, 2)
       (100, 1)
   - : unit = ()
   # 
*)

(* ********** *)

(* Example: rotating a tree to the right. *)

(*
   # let y = insert_list insert_first_shot show_int compare_int [300; 200; 100] hbt_empty;;
   val y : int heightened_binary_tree =
     (3,
      Node
       ((2, Node ((1, Node ((0, Leaf), 100, (0, Leaf))), 200, (0, Leaf))), 300,
        (0, Leaf)))
   # display_heightened_binary_tree show_int y;;
   (300, 3)
     (200, 2)
       (100, 1)
   - : unit = ()
   # let (hbt1, e, hbt2) = fetch_triple y in display_heightened_binary_tree show_int (rotate_right show_int hbt1 e hbt2);;
     (300, 1)
   (200, 2)
     (100, 1)
   - : unit = ()
   # let (hbt1, e, hbt2) = fetch_triple y in let (hbt1', e', hbt2') = fetch_triple (rotate_right show_int hbt1 e hbt2) in display_heightened_binary_tree show_int (rotate_right show_int hbt1' e' hbt2');;
       (300, 1)
     (200, 2)
   (100, 3)
   - : unit = ()
   # 
*)

(* ********** *)

(* end of week-03a_balanced-binary-trees-visually.ml *)

"week-03a_balanced-binary-trees-visually.ml"
