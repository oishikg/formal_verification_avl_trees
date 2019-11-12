# Formally Verifying the Correctness of an OCaml AVL Tree Implementation

This project aims to formally verify the correctness of an OCaml based AVL tree implementation using the `Coq` proof assistant. It contains:
- A`Gallina` implementation of AVL trees 
- Specifications for the lookup and insert operations on AVL trees
- Theorems to prove the specifications 
- Lemmas to aid in the above theorems 
- An application of the certified insertion function: checking for equality of expressions modulo associativity and commutativity 

## Getting started

### Prerequisites

- `OCaml`  4.2 >= 
- `coqc` version 8.9: 
  - We required the latest version to `Extract` our certified code. 
  - Check the version of you coq compiler with the `coqc --version` terminal command. 
  - If the version is less than 8.9, there may be issues with some of the standard library lemmas, which have been relocated to different modules in comparison to older versions. 
  - In case of issues, update `coqc` using `opam`. Instructions may be found  [here](https://coq.inria.fr/opam-using.html).

### Installing 

Download/clone the repository and run the following commands in the `Coq_files/src` directory:

- `coq_makefile -f _CoqProject -o Makefile`: To autogenerate the required make file using the information specified in the `_CoqProject` file.
- `make`: To build the project. 

## The Proofs and Application

###`coq_files/src`:

There are four folders in `coq_files/src` corresponding to four different parts of the project:
- `/Paraphernalia`: Contains `paraphernalia.v` with the basic axioms and lemmas required to build
  and write proofs.
- `/Implementation`: Contains `hbt.v`, which in turn contains the `Gallina` implementation of the
  AVL tree implementation.
- `/Theorems`: Contains `theorems.v` with the specifications for the AVL tree lookup and insertion operations, theorems claiming that the implementations of these operations meet the specifications, and the proofs for
  them. 
- `/Lemmas`: This folder contains three more folders in turn:
  - `/Lemmas/Sound`: This folder contains the `sound.v` file with lemmas concerning soundness of our AVL tree implementation. 
  - `/Lemmas/Balanced`: This folder contains the `balanced.v` filed with lemmas concerning the balancedness of our AVL tree implementation
  - `/Lemmas/Ordered`: This folder in turn contains two more folders:
    - `/Lemmas/Ordered/Helper`: This contains the file `ordered_helper.v` with 'helper' lemmas related to the orderedness of our AVL tree implementation. These lemmas are used to prove the main orderedness lemmas.
    - `/Lemmas/Ordered/Main`: This contains the file `ordered_main.v` with the main lemmas for orderedness.

###`equality_modulo_associativity_commutativity`

- This section contains an application of AVL trees: checking whether two expressions of binary operators (e.g. `+`, `x`, `++` , etc.) are equal modulo associativity and commutativity. 
- We benchmark the performance of three AVL tree implementations:
  - The original OCaml implementation contained in the`Original_Hbt` module.
  - The certified and extracted implementation contained in the `Certified_Hbt_Peano` module.
  - The certified and extracted implementation with the Peano numbers ADT replaced with the OCaml integer data type. 

## Author

- Oishik Ganguly 