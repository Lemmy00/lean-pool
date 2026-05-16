/-
Copyright (c) 2026 Andrej Bauer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrej Bauer
-/

import LeanPool.PartialCombinatoryAlgebras.Basic
import LeanPool.PartialCombinatoryAlgebras.PartialCombinatoryAlgebra
import LeanPool.PartialCombinatoryAlgebras.CombinatoryAlgebra
import LeanPool.PartialCombinatoryAlgebras.Programming
import LeanPool.PartialCombinatoryAlgebras.FreeCombinatoryAlgebra
import LeanPool.PartialCombinatoryAlgebras.GraphModel

/-!
# Partial Combinatory Algebras

Source: url:https://github.com/andrejbauer/partial-combinatory-algebras
Authors: Andrej Bauer
Status: verified
Main declarations: `LeanPool.PartialCombinatoryAlgebras.PCA`
Tags: combinatory-algebra, lambda-calculus, computability
MSC: 03B40, 03D75
-/

/-!
## Mathematical overview

A *partial combinatory algebra* (PCA) is a set `A` equipped with a partial binary
operation `· : A → A ⇀ A` together with distinguished combinators `K` and `S`
satisfying the usual equations
`K · a · b = a` and `S · a · b · c = (a · c) · (b · c)`.
Such a structure is enough to model untyped λ-calculus and witnesses
Turing-completeness in an algebraic form.

This formalisation develops the basic theory:

- `LeanPool.PartialCombinatoryAlgebras.PCA` — the class of partial combinatory algebras,
  together with the inductive type of formal `Expr`essions, combinatory abstraction
  `abstr`, and the `[pca: …]` / `≪ x ≫ …` macros that recover λ-style notation.
- `LeanPool.PartialCombinatoryAlgebras.CA` — total combinatory algebras, with a canonical
  partial-application instance promoting every `CA` to a `PCA`.
- Programming with PCAs: the identity combinator `I`, pairing and projections
  (`pair`, `fst`, `snd`), booleans and the conditional (`tru`, `fal`, `ite`),
  fixed-point combinators (`X`, `Z`, `W`, `Y`), Curry numerals (`numeral n`,
  `succ`, `pred`, `iszero`) and primitive recursion `primrec`.
- `LeanPool.PartialCombinatoryAlgebras.FreeCA` — the free total combinatory algebra,
  built as a quotient of formal expressions by the equational theory of `K` and `S`.
- `LeanPool.PartialCombinatoryAlgebras.GraphModel` — the *graph model*: given a section
  -retraction `List α → α` (a `Listing` instance), the powerset `Set α` carries a
  combinatory algebra structure via `K`, `S`, and Scott-continuous function graphs.

## Provenance

Imported from <https://github.com/andrejbauer/partial-combinatory-algebras>; a Lean 4
model project for Andrej Bauer's 2024 course "Formalized mathematics and proof
assistants" at the University of Ljubljana. Ported from Lean v4.15.0-rc1 to Lean
Pool's v4.30.0-rc2. The upstream `FirstKleeneAlgebra.lean`, which is incomplete in
the source (contains `sorry` placeholders for the S-combinator construction via
Gödel numbers of partial recursive functions), is not vendored. Equation lemmas for
the Curry-numeral predecessor (`eq_pred`, `eq_pred_succ`) and primitive recursion
(`eq_primrec`, `eq_primrec_zero`, `eq_primrec_succ`) are also omitted in this port.
-/
