/-
Copyright (c) 2026 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/

import LeanPool.Monlib4.LinearAlgebra
import LeanPool.Monlib4.Other
import LeanPool.Monlib4.Preq
import LeanPool.Monlib4.RepTheory

/-!
# Monlib4 matrix algebra automorphisms

Source: url:https://github.com/themathqueen/monlib4
Authors: Monica Omar
Status: verified
Main declarations: `Matrix.aut_mat_inner`, `Matrix.aut_mat_inner_trace_preserving`,
  `Matrix.automorphism_matrix_inner`
Tags: linear-algebra, matrices, operator-algebras, representation-theory
MSC: 15A69, 16W20
-/

/-!
## Mathematical overview

A core theorem-bearing subset of `monlib4` — a Lean 4 formalization of
non-commutative graph theory. The full upstream library builds quantum-graph
and quantum-set theory on substantial matrix / inner-product-space
infrastructure.

This vendored subset now includes the upstream matrix-algebra automorphism
theorem: every automorphism of a finite matrix algebra over a field is inner,
implemented by conjugation with an invertible matrix (`Matrix.aut_mat_inner` and
`Matrix.aut_mat_inner'`).  As a corollary, such automorphisms preserve trace
(`Matrix.aut_mat_inner_trace_preserving`).

The supporting imported infrastructure includes a `Matrix.reshape` linear
equivalence between `Mₙₓₘ(R)` and `Rⁿˣᵐ`, the entrywise conjugate
`Matrix.conj` with the `ᴴᵀ` notation, the projection `directSumFromTo` between
summands of a dependent direct sum, basic spectrum commutativity
(`isUnit_comm`, `spectrum.comm`), and helper lemmas for finite sums,
ites/dites, `RCLike`-valued order relations, and base-`b+1` divisibility tests.

## Provenance

Imported from <https://github.com/themathqueen/monlib4> (originally Lean
`v4.21.0-rc3`) and ported to Lean Pool's `v4.30.0-rc2` / Mathlib `v4.30.0-rc2`.
The successor of <https://github.com/themathqueen/monlib> (the Lean 3 version).
The bulk of the upstream library is not yet vendored — see the import-PR
description for the porting status of individual modules.
-/
