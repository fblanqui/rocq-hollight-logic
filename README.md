This repository contains a [Rocq](https://coq.inria.fr/) library that is an automatic translation of the [HOL-Light](https://github.com/jrh13/hol-light) library on [Logic](https://github.com/jrh13/hol-light/blob/master/Logic/make.ml), obtained with [hol2dk](https://github.com/Deducteam/hol2dk) and [lambdapi](https://github.com/Deducteam/lambdapi), with HOL-Light types and functions mapped to idiomatic types and functions in Rocq.

Remark: The translated theorems are provided as axioms in order to have a fast Require because the proofs currently extracted from HOL-Light can be very big (several Gb) and not very informative for they are low level (the translation is done at the kernel level, not at the source level). If you are skeptical, you can however generate and check them again by using the script [reproduce](https://github.com/Deducteam/rocq-hollight-logic/blob/main/reproduce). It however takes more than 2 hours with 32 processors Intel Core i9-13950HX and 64 Gb RAM. If every thing works well, the proofs will be in the directory `tmp/output`.

**Installation using [opam](https://opam.ocaml.org/)**

```
opam repo add rocq-released https://rocq-prover.org/opam/released
opam install rocq-hollight-logic
```

**Usage in a Rocq file**

```
Require Import HOLLight_Logic.theorems.
```
