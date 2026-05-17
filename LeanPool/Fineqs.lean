/-
Copyright (c) 2026 Stefan Barańczuk, Aristotle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Barańczuk, Aristotle
-/

import LeanPool.Fineqs.Main

/-!
# FinEqs - reducing equations defining a subset of n-space over a finite field

Source: arxiv:1906.11174
Authors: Stefan Barańczuk, Aristotle
Status: verified
Main declarations: `LeanPool.Fineqs.card_projectivization_minus_point`
Tags: number-theory, finite-fields, algebraic-geometry
MSC: 14G15, 11T06
-/

/-!
## Mathematical overview

This project formalizes a small cardinality lemma from the paper
"Reducing the number of equations defining a subset of the n-space over a finite field"
by Stefan Barańczuk ([arXiv:1906.11174](https://arxiv.org/abs/1906.11174)). The
formalization was performed with the software Aristotle by Harmonic.

## Main result

- `LeanPool.Fineqs.card_projectivization_minus_point`: the cardinality of
  `P^n(F) \ {α}` is `(q^(n+1) - q) / (q - 1)` for a finite field `F` with
  `q = |F|`.
-/
