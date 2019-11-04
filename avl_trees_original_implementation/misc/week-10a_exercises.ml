(* week-10a_exercises.ml *)
(* Introduction to Data Structures and Algorithms (YSC2229), Sem2, 2017-2018 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of Wed 21 Mar 2018 *)

(* ********** *)

(* Exercise 1a:

   Program an OCaml function that,
   given a non-empty array of size n that contains integers between 0 and n,
   all distinct, computes the missing one.

   For example, if n = 1,

   - applying your function to [|0|] yields 1
   - applying your function to [|1|] yields 0

   and if n = 2,

   - applying your function to [|0; 1|] yields 2
   - applying your function to [|0; 2|] yields 1
   - applying your function to [|1; 2|] yields 0

   What is the complexity of your function in time and in space?
*)

(* Exercise 1b:

   Exercise 1b is the same as Exercise 1a,
   except that the given non-empty array of size n is immutable,
   i.e., cannot be overwritten.
   (If your solution for Exercise 1a doesn't overwrite the given array,
   then it qualifies as a solution for Exercise 1b.)
*)

(* ********** *)

(* Exercise 2:

   Reminder: given a function of type 'a -> 'b and a list of elements of type 'a,
   List.map applies the given function to each of the given elements
   and construct a list of the results, in the same order as in the given list.
   Example: evaluating
     List.map string_of_int [1; 2; 3]
   yields
     ["1"; "2"; "3"]

   You are being asked
   - to optimize the following definition of foo,
   - to test your optimized definition, and
   - to explain as well as justify your optimization.
*)

let make_odd_number n =
  2 * n + 1;;

let foo xs =
  List.map make_odd_number (List.map (fun x -> x mod 3) xs);;

(* ********** *)

(* Exercise 3:

   The goal of this exercise is to implement an OCaml function
   that, given a list of lists of integers and a list of integers,
   computes whether the given list occurs in the given list of lists.

   (a) Implement a naive OCaml function that traverses the list of lists.

       Estimate, in time and in space, the complexity of your OCaml function.

   (b) Write a unit-test function that uses your naive function as a baseline.

   Example: if the given list of lists is
     [[1; 1; 2]; [2; 1]; [2; 1; 3]; [1; 1; 3; 4]]
   then here is an OCaml function that does the job without backtracking.

     fun ns ->
       match ns with
       | [] ->
          false
       | 1 :: ns' ->
          (match ns' with
           | [] ->
              false
           | 1 :: ns'' ->
              (match ns'' with
                | [] ->
                   false
                | 2 :: ns''' ->
                   (match ns''' ->
                    | [] ->
                       true
                    | _ ->
                       false)
                | 3 ->
                   (match ns''' with
                    | [] ->
                       false
                    | 4 :: ns'''' ->
                       (match ns'''' with
                        | [] ->
                           true
                        | _ ->
                           false)
                    | _ ->
                       false)
                 | _ ->
                    false)
           | _ ->
              false)
       | 2 :: ns' ->
          (match ns' with
           | [] ->
              false
           | 1 :: ns'' ->
              (match ns'' with
               | [] ->
                  true
               | 3 :: ns''' ->
                  (match ns''' with
                   | [] ->
                      true
                   | _ ->
                      false)
               | _ ->
                  false)
           | _ ->
              false)
       | _ ->
          false

   Pictorially:

                 *
                /
               2
              /
         .-1-.-3-.-4-*
        /
       1
      /
     +
      \
       2 
        \     
         .-1-*-3-*
  
   Each of the paths from the root + to a leaf * enumerates
   the elements of each of the lists:
     1 :: 1 :: 2 :: []
     1 :: 1 :: 3 :: 4 :: []
     2 :: 1 :: []
     2 :: 1 :: 3 :: []

   (c) implement an OCaml data type that accounts for the tree just above.

   (d) implement an OCaml function that maps a given list of lists
       into the corresponding tree.

       Estimate, in time and in space, the complexity of your OCaml function.

   (e) implement an OCaml function that, given a list and such a tree,
       computes whether this given list occurs in the list of lists
       represented by this tree.

       Estimate, in time and in space, the complexity of your OCaml function.

   (f) compose your OCaml function from (d) and your OCaml function from (e)
       and verify that the resulting function satisfies the unit test of (b).
*)

(* ********** *)

(* end of week-10a_exercises.ml *)

"week-10a_exercises.ml"
