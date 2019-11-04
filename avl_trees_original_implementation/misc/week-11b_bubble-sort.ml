(* week-11b_bubble-sort.ml *)
(* Introduction to Data Structures and Algorithms (YSC2229), Sem2, 2017-2018 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of Thu 29 Mar 2018 *)

(* ********** *)

(* https://en.wikipedia.org/wiki/Bubble_sort *)

(* ********** *)

type comparison =
  | Lt
  | Eq
  | Gt;;

let compare_int i j =
  if i < j then Lt else if i = j then Eq else Gt;;

let is_increasing compare xs =
  let length_of_xs = Array.length xs
  in if length_of_xs = 0
     then true
     else let rec visit x i =
            if i = length_of_xs
            then true
            else let x' = Array.get xs i
                 in match compare x x' with
                    | Lt ->
                       visit x' (i + 1)
                    | Eq ->
                       visit x' (i + 1)
                    | Gt ->
                       false
          in visit (Array.get xs 0) 1;;

(* ********** *)

let test_sort_int size candidate name_of_candidate =
  let rec loop counter =
    if counter < 0
    then true
    else let ns = Array.init counter (fun i -> Random.int 1000 - Random.int 1000)
         in let ns_allegedly_sorted = candidate ns
            in if is_increasing compare_int ns_allegedly_sorted
               then loop (counter - 1)
               else (Printf.printf "%s failed on\n%s\n%s\n"
                                   name_of_candidate
                                   (show_array show_int ns)
                                   (show_array show_int ns_allegedly_sorted);
                     false)
  in if size < 0
     then raise (Failure "test_sort_int needs a non-negative integer")
     else loop size;;

let test_sort_int_sorted size candidate name_of_candidate =
  let rec loop counter =
    if counter < 0
    then true
    else let ns = Array.init counter (fun i -> i)
         in let ns_allegedly_sorted = candidate ns
            in if is_increasing compare_int ns_allegedly_sorted
               then loop (counter - 1)
               else (Printf.printf "%s failed on\n%s\n%s\n"
                                   name_of_candidate
                                   (show_array show_int ns)
                                   (show_array show_int ns_allegedly_sorted);
                     false)
  in if size < 0
     then raise (Failure "test_sort_int needs a non-negative integer")
     else loop size;;

(* ********** *)

let bubble_sort compare show_yourself xs =
  let length_of_xs = Array.length xs
  in let rec bubble_up i xs_i b =
       let j = i + 1
       in if j = length_of_xs
          then b
          else let xs_j = Array.get xs j
               in match compare xs_i xs_j with
                  | Lt ->
                     bubble_up j xs_j b
                  | Eq ->
                     bubble_up j xs_j b
                  | Gt ->
                     (Array.set xs i xs_j;
                      Array.set xs j xs_i;
                      bubble_up j xs_i false)
     in if length_of_xs = 0
        then xs
        else let rec again () =
               if bubble_up 0 (Array.get xs 0) true
               then xs
               else again ()
             in again();;

let bubble_sort_int = bubble_sort compare_int show_int;;

let () = assert (test_sort_int 100 bubble_sort_int "bubble_sort_int");;

(* ********** *)

let time thunk message =
  let time = Sys.time ()
  in (thunk ();
      Printf.sprintf "Elapsed time: %f seconds -- %s" (Sys.time() -. time) message);;

(* ********** *)

let test_int size =
  let ns = Array.init size (fun i -> Random.int 1000 - Random.int 1000)
  in let time_merge_OCaml = 
       time (fun () ->
              Array.sort (fun i j -> if i < j then ~-1 else if i = j then 0 else 1) ns)
            "OCaml"
     and time_bubble_sort =
       time (fun () ->
              bubble_sort_int ns)
            "bubble sort"
     in (time_merge_OCaml, time_bubble_sort);;

(* ********** *)

(* Exercise:

   Explain why the bubble-sort function above
   is faster than OCaml's resident sort function
   according to this testing function.
*)

(* ********** *)

(* end of week-11b_bubble-sort.ml *)

"week-11b_bubble-sort.ml"
