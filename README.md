# Formally Verifying the Correctness of an OCaml AVL Tree Implementation

This project aims to formally verify the correctness of an OCaml based AVL tree implementation
using the `Coq` proof assistant. It contains:
- Professor Olivier Danvy's implementation of AVL trees (in `AVL_Trees_Implementation`). 
- The corresponding `Gallina` implementation of AVL trees (in `Coq_files/src`).
- Specifications for the lookup, insert, and deleting operations (in `Coq_files/src`).
- Theorems to prove the specifications (in `Coq_files/src`).
- Lemmas to aid in the above theorems (in `Coq_files/src`).

## Getting started

### Prerequisites

- `OCaml` 4.2
- The Coq Proof Assistant, version 8.4pl4 

### Installing 

Download/clone the repository and run the following commands in the `Coq_files/src` directory:

- `make Makefile.Coq`: To autogenerate the required make file using the information specified in
the `_CoqProject` file.
- `make`: To build the project. 

## Structure of `Coq_files/src`: 
There are four folders in `Coq_files/src` corresponding to four different parts of the project:
- `Paraphernalia`: Contains `paraphernalia.v` with the basic axioms and lemmas required to build
and write proofs.
- `Implementation`: Contains `hbt.v`, which in turn contains the `Gallina` implementation of the
AVL tree implementation.
- `Theorems`: Contains `theorems.c` with the specifications for the AVL tree operations, theorems
claiming that the implementations of these operations meet the specifications, and the proofs for
them. 
- `Lemmas`: Contains `sound_and_balanced.v` and `ordered.v` which contain lemmas required to
prove the above theorems. 

## Author

- Oishik Ganguly 