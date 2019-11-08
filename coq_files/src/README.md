# Formally Verifying the Correctness of an OCaml AVL Tree Implementation

This project aims to formally verify the correctness of an OCaml based AVL tree implementation using the `Coq` proof assistant. It contains:
- The a `Gallina` implementation of AVL trees 
- Specifications for the lookup and insert operations on AVL trees
- Theorems to prove the specifications 
- Lemmas to aid in the above theorems 

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

- `make Makefile.Coq`: To autogenerate the required make file using the information specified in the `_CoqProject` file.
- `make`: To build the project. 

## Structure of `Coq_files/src`: 
There are four folders in `Coq_files/src` corresponding to four different parts of the project:
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

## How to Read This Project

Owing to the large size of the project, the `.v` files may be hard to read by themselves, owing to the length of the proofs. Thus, each `.v` file is accompanied by a corresponding `.html` and `.css` file to view the statement of the lemmas and the corresponding documentation in a more readable format. 

Work is currently ongoing to unite all the documentation files into one unfied documentation resource. 

The recommended order in which the Coq files should be viewed is as follows: 

1.  `Paraphernalia/paraphernalia.v` : to get a sense of some of the lemmas used across the project. The notion of an ordering comparison function is defined in this file. 
2. `Implementation/hbt.v`: to view the Gallina implementation of the insertion and lookup functions, and the predicates for soundness, balancedness, and orderedness. This file also contains the unfold lemmas. 
3. `Theorems/theorems.v`: to view the specifications for the insertion and lookup functions, the statement of theorems claiming that our implementations in `hbt.v` do meet these specifications, and the proofs for these theorems. 
4. `Lemmas/*`: to view the different lemmas used for soundness, balancedness, and orderedness. It is recommended that one see `sound.v` first, followed by `balanced.v`, and finally `ordered_main.v`. `ordered_helper.v` contains disparate helper lemmas, which should be referred to with reference to one of the main orderedness lemmas. 

## Author

- Oishik Ganguly 