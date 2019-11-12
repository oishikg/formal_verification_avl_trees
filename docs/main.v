
(** This page contains the documentation for the Coq proofs written to verify our implementations of the <<lookup>> and <<insertion>> operations on AVL Trees. To view the code corresponding to the implementation, see #<a href = https://github.com/oishikg/formal_verification_avl_trees>the github page </a>#. To get a sense of how the proofs proceed, it is recommended that the libraries in the project be viewed in the following order: *)

(** * #<a href = "https://oishikg.github.io/formal_verification_avl_trees/Paraphernalia/paraphernalia.html"> paraphernalia </a># *)

(** This library contains general lemmas used across the project. The notion of an ordering comparison function is defined in this library. *)

(** * #<a href = "https://oishikg.github.io/formal_verification_avl_trees/Implementation/hbt.html"> hbt </a># *)

(** This library contains the Gallina implementation of the insertion and lookup functions, and the predicates for soundness, balancedness, and orderedness.It also contains unfold lemmas for the functions, which are key to algebraically reasoning about our programs. **)

(** * #<a href = "https://oishikg.github.io/formal_verification_avl_trees/Theorems/theorems.html"> theorems </a># *)

(** This library contains the specifications for the insertion and lookup functions, the statement of theorems claiming that the implementations meet these specifications, and the proofs for these theorems. The proof for <<lookup>> is trivial, while fairly complex for <<insertion>>. The latter proof is constructed with the help of 3 key lemmas which are discussed in the next section *)

(** * Lemmas *)

(** The 3 key lemmas used to show the correctness of the insertion implementation were:

- Insertion preserves the soundness invariant
- Insertion preserves the balancedness invariant
- Insertion preserves the orderedness invariant *)

(** ** #<a href = "https://oishikg.github.io/formal_verification_avl_trees/Lemmas/Sound/sound.html"> sound  </a># *)

(** This library contains lemmas concerning the soundness property. *)

(** ** #<a href = "https://oishikg.github.io/formal_verification_avl_trees/Lemmas/Balanced/balanced.html"> balanced </a># *)

(** This library contains lemmas concerning the balancedness property. *)

(** ** #<a href = "https://oishikg.github.io/formal_verification_avl_trees/Lemmas/Ordered/Main/ordered_main.html"> ordered_main </a># *)

(** This library contains the most importatnt lemmas for the orderedness property, including: 
- The lemma to relate the inserted element to a payload in terms of an ordering
- The lemmas to show that rotations preserve order
- The lemma to show that insertion preserves orderedness *)

(** The library builds on helper lemmas defined in #<a href = "https://oishikg.github.io/formal_verification_avl_trees/Lemmas/Ordered/Helper/ordered_helper.html"> ordered_helper </a># *)
