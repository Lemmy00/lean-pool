/-
Copyright (c) 2026 Óscar Álvarez Sánchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Óscar Álvarez Sánchez
-/

import LeanPool.DemazureOperatorsLean.Demazure
import LeanPool.DemazureOperatorsLean.DemazureAux
import LeanPool.DemazureOperatorsLean.DemazureRelations
import LeanPool.DemazureOperatorsLean.DemazureAuxRelations

/-!
# Demazure Operators and Lean

Source: I. N. Bernstein, I. M. Gelfand, and S. I. Gelfand,
  "Schubert cells, and the cohomology of the spaces G/P", Russian
  Mathematical Surveys 28:3 (1973), for divided-difference/Demazure operator
  relations; formalization source: url:https://github.com/bolito2/DemazureOperatorsLean
Authors: Óscar Álvarez Sánchez
Status: verified
Main declarations: `Demazure.Dem`, `Demazure.demazure_commutes_adjacent`
Tags: algebraic-combinatorics, demazure-operators, polynomials, representation-theory
MSC: 05E05, 13P10, 20F55
-/
