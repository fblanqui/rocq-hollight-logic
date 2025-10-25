This repository contains a [Rocq](https://coq.inria.fr/) library that is an automatic translation of the [HOL-Light](https://github.com/jrh13/hol-light) library on [Logic](https://github.com/jrh13/hol-light/blob/master/Logic), obtained with [hol2dk](https://github.com/Deducteam/hol2dk) and [lambdapi](https://github.com/Deducteam/lambdapi), with HOL-Light types and functions mapped to idiomatic types and functions in Rocq.

Remark: The translated theorems are provided as axioms in order to have a fast Require because the proofs currently extracted from HOL-Light can be very big (several Gb) and not very informative for they are low level (the translation is done at the kernel level, not at the source level). If you are skeptical, you can however generate and check them again by using the script [reproduce](https://github.com/Deducteam/rocq-hollight-logic/blob/main/reproduce). It however takes more than 2 hours and 11 minutes with 32 processors Intel Core i9-13950HX and 64 Gb RAM. If every thing works well, the proofs will be in the directory `tmp/output`.

**Contents**

For an overview of the goals and contents of this library, one can read the README and make.ml files in the [Logic](https://github.com/jrh13/hol-light/blob/master/Logic) library. More precisions are available in John Harrison's publications detailed in the README, as well as in the structure of each file (thanks to proper section naming).

Some key types and definitions in this library, all available as idomatic Rocq objects (note that some are defined in the rocq-hollight-logic-unif library):
- two (inductive) types for first order terms and formulae, over a fixed countable signature (functions and predicates labelled by N for all possible arities) or subsets of this signature, 
- Basic definitions including free/bound variables, term interpretations and formula realization in a model, semantic implication and equivalence, substitution in terms and formulae, and more.
- Conversion to prenex form and skollemization of formulae
- Propositional logic
- Canonical models
- Unification algorithm
- Resolution (with a lot of variants)
- Given clause algorithm (two variants)
- Provability in equational logic
- First order term rewriting
- Lexicographic path ordering

The available theorems include:
- A lot of properties of each definition, as correctness-checking is one of the main goal of the library
- Upward Löwenheim-Skolem (thm_MODEL_DUPLICATE)
- Downard Löwenheim-Skolem* (thm_LS, thm_COMPACT_LS_NORM)
- Compactness* (thm_COMPACT_PROP, thm_COMPACT_LS, thm_COMPACT_LS_NORM)
- Uniformity/Skolem-Gödel-Herbrand (thm_UNIFORMITY)
- Herbrand (thm_HERBRAND_THEOREM)
- Completeness of resolution* (thm_RESOLUTION_COMPLETE, thm_LINEAR_RESOLUTION_COMPLETE, thm_SOS_RESOLUTION_COMPLETE, thm_POSRESOLUTION_COMPLETE, thm_SEMRESOLUTION_COMPLETE, thm_GBACKCHAIN_MINIMAL, thm_IBACKCHAIN_MINIMAL)
- Birkhoff's theorem (thm_EQLOGIC_COMPLETE, thm_EQLOGIC_SOUND)
- Well-foundedness of the lexicographic path ordering over a finite signature (thm_LPO_WF)
(*) Compactness in propositionnal logic, LS+Compactness in regular FOL and in FOL with equality (over normal structures), completeness of each variant of resolution.


**Installation using [opam](https://opam.ocaml.org/)**

```
opam repo add rocq-released https://rocq-prover.org/opam/released
opam install rocq-hollight-logic
```

**Usage in a Rocq file**

```
Require Import HOLLight_Logic.theorems.
```

**
