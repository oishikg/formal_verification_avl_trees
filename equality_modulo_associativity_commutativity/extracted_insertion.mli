
type bool =
| True
| False

type nat =
| O
| S of nat

type 'a option =
| Some of 'a
| None

val add : nat -> nat -> nat

val max : nat -> nat -> nat

module Nat :
 sig
  val eqb : nat -> nat -> bool

  val leb : nat -> nat -> bool

  val ltb : nat -> nat -> bool
 end

type element_comparison =
| Lt
| Eq
| Gt

val compare_int : nat -> nat -> element_comparison

type 'a heightened_binary_tree =
| HNode of nat * 'a binary_tree
and 'a binary_tree =
| Leaf
| Node of 'a triple
and 'a triple =
| Triple of 'a heightened_binary_tree * 'a * 'a heightened_binary_tree

val rotate_right_bt :
  'a1 binary_tree -> 'a1 -> nat -> 'a1 binary_tree -> 'a1 heightened_binary_tree option

val rotate_right_hbt :
  'a1 heightened_binary_tree -> 'a1 -> 'a1 heightened_binary_tree -> 'a1 heightened_binary_tree
  option

val rotate_left_bt :
  nat -> 'a1 binary_tree -> 'a1 -> 'a1 binary_tree -> 'a1 heightened_binary_tree option

val rotate_left_hbt :
  'a1 heightened_binary_tree -> 'a1 -> 'a1 heightened_binary_tree -> 'a1 heightened_binary_tree
  option

val project_height_hbt : 'a1 heightened_binary_tree -> nat

val insert_hbt_helper :
  ('a1 -> 'a1 -> element_comparison) -> 'a1 -> 'a1 heightened_binary_tree -> 'a1
  heightened_binary_tree option

val insert_bt_helper :
  ('a1 -> 'a1 -> element_comparison) -> 'a1 -> nat -> 'a1 binary_tree -> 'a1
  heightened_binary_tree option

val insert_t_helper :
  ('a1 -> 'a1 -> element_comparison) -> 'a1 -> nat -> 'a1 triple -> 'a1 heightened_binary_tree
  option

val insert_hbt :
  ('a1 -> 'a1 -> element_comparison) -> 'a1 -> 'a1 heightened_binary_tree -> 'a1
  heightened_binary_tree
