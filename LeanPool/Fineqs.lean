/-
Copyright (c) 2026 Stefan Barańczuk, Aristotle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Barańczuk, Aristotle
-/

import LeanPool.Fineqs.Main

/-!
# FinEqs: Reducing the number of equations defining a subset of n-space over a finite field

Source: arxiv:1906.11174
Authors: Stefan Barańczuk, Aristotle
Status: verified
Main declarations: `theorem_1`, `prop_1`, `corollary_2`, `corollary_3`, `remark_example`,
`matrix_rank_lemma`, `card_projectivization_minus_point`
Tags: number-theory, finite-fields, algebraic-geometry
MSC: 14G15, 11T06

## Mathematical overview

This project formalizes the paper "Reducing the number of equations defining a subset
of the n-space over a finite field" by Stefan Barańczuk
([arXiv:1906.11174](https://arxiv.org/abs/1906.11174)). The formalization was
performed with the software Aristotle by Harmonic.

## Main results

- `theorem_1`: Any set of functions on a set X of size at most
  `(q^(n+1) - q) / (q - 1)` can be reduced to n functions with the same zero set.
- `prop_1`: The bound on the size of X in Theorem 1 is sharp.
- `corollary_2`: Theorem 1 applied to affine space.
- `corollary_3`: Theorem 1 applied to projective space.
- `remark_example`: For the specific case of coordinate functions, n - 1 equations
  are not enough.

## Helper lemmas

- `matrix_rank_lemma`: Factorization of a matrix into a rank-n matrix and another matrix.
- `card_projectivization_minus_point`: Cardinality of projective space minus a point.
-/
