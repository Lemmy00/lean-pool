/-
Copyright (c) 2026 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/

import Mathlib.Algebra.Algebra.Equiv
import LeanPool.Monlib4.LinearAlgebra.Matrix.Reshape
import LeanPool.Monlib4.Preq.StarAlgEquiv

/-!
# Linear equivalence conjugation compatibility

Mathlib's `LinearEquiv.conjAlgEquiv` is the current version of the upstream
`LinearEquiv.innerConj` construction used by the Monlib4 `IncludeBlock` slice.
-/

namespace LinearEquiv

/-- Conjugate endomorphism algebras along a linear equivalence. -/
def innerConj {R E F : Type*} [CommSemiring R] [AddCommMonoid E] [AddCommMonoid F]
    [Module R E] [Module R F] (e : E ≃ₗ[R] F) :
    Module.End R E ≃ₐ[R] Module.End R F :=
  e.conjAlgEquiv R

theorem innerConj_apply {R E F : Type*} [CommSemiring R] [AddCommMonoid E]
    [AddCommMonoid F] [Module R E] [Module R F] (e : E ≃ₗ[R] F)
    (f : Module.End R E) :
    e.innerConj f = e.toLinearMap ∘ₗ f ∘ₗ e.symm.toLinearMap :=
  rfl

end LinearEquiv
