# Named Arguments as Intersections, Optional Arguments as Unions (Artifact)

This repository contains the Coq formalization of the elaboration from Uᴀᴇɴᴀ to λᵢᵤ. The source calculus Uᴀᴇɴᴀ supports first-class named and optional arguments, and the target calculus λᵢᵤ features intersection and union types.

## Build Instructions

The proofs are continuously tested against Coq 8.17 - 8.20. The easiest way to install a specific version of Coq is via [opam](https://opam.ocaml.org/doc/Install.html):

```
$ opam pin add coq 8.20.0
coq is now pinned to version 8.20.0
......
```

After installing Coq, you can build the proofs using `make`:

```
$ make
coq_makefile -f _CoqProject -o CoqMakefile
make -f CoqMakefile
COQDEP VFILES
COQC theories/Definitions.v
COQC theories/Soundness.v
```

## Proof Correspondence

| Definition / Theorem             | Paper       | Coq File        | Coq Name              |
| -------------------------------- | ----------- | --------------- | --------------------- |
| Syntax of λᵢᵤ                    | Section 4.1 | `Definitions.v` | `Inductive typ/exp`   |
| Subtyping of λᵢᵤ                 | Fig. 3      | `Definitions.v` | `Inductive sub`       |
| Subtyping reflexivity            | Theorem 1   | `Soundness.v`   | `Theorem sub_refl`    |
| Subtyping transitivity           | Theorem 2   | `Soundness.v`   | `Theorem sub_trans`   |
| Typing of λᵢᵤ                    | Fig. 4      | `Definitions.v` | `Inductive typing`    |
| Syntax of Uᴀᴇɴᴀ                  | Section 4.2 | `Definitions.v` | `Inductive styp/sexp` |
| Elaboration                      | Fig. 5      | `Definitions.v` | `Inductive elab`      |
| Named parameter elaboration      | Fig. 5      | `Definitions.v` | `Inductive pelab`     |
| Call site rewriting              | Fig. 6      | `Definitions.v` | `Inductive pmatch`    |
| Successful lookup                | Appendix D  | `Definitions.v` | `Inductive lookup`    |
| Failed lookup                    | Appendix D  | `Definitions.v` | `Inductive lookdown`  |
| Soundness of call site rewriting | Theorem 5   | `Soundness.v`   | `Lemma pmatch_sound`  |
| Soundness of elaboration         | Theorem 6   | `Soundness.v`   | `Theorem elab_sound`  |

