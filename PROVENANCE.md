# Provenance

This repository is a standalone Lean 4 formalization of Dana Scott's 1980
Oxford lectures, published May 1981 as PRG-19 *Lectures on a Mathematical
Theory of Computation*. It is not a thin wrapper and not a reimplementation
of an independent formalization.

Dana Scott did not participate in, review, or endorse this formalization.
The formalization was produced by Lars Warren Ericson without input from
Scott. The source monograph is cited as literature only and is not licensed
under this repository's Apache-2.0 terms (see `NOTICE`).

Cross-presentation equivalence theorems for Scott's 1972 / 1980 / 1982
material live in
[`catskillsresearch/scott_models`](https://github.com/catskillsresearch/scott_models).
**This repository is submitted to Palomar on its own**, for the 1981
lectures alone, following the same Challenge / Solution pattern as
[`catskillsresearch/cardb`](https://github.com/catskillsresearch/cardb)
and
[`catskillsresearch/scott1972`](https://github.com/catskillsresearch/scott1972).

The compared Palomar claim is **the first sentence of Scott's unlettered
Theorem 8.8**: every countable neighbourhood system `D` embeds as a
subdomain of the universal domain `U` (`D ⊴ U`). The other two sentences
of 8.8 are proved in the library (`theorem_8_8_b`, `theorem_8_8_c`) and
are not Comparator targets. The Lectures I–VIII development lives in
`Scott1980/Neighborhood/*`; Exercise 8.17 Part 2 is a documented deferral.

Palomar reviews and, if registered, preserves a pinned commit of *this*
repository.
