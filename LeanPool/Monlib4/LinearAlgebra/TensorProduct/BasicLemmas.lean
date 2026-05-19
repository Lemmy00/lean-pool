/-
Copyright (c) 2026 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/

import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Tensor product compatibility

The tensor-product helper lemmas needed by the `IncludeBlock` slice are now in
Mathlib, including `TensorProduct.ext_threefold'`.  This module preserves the
upstream import path while re-exporting those Mathlib declarations.
-/

namespace TensorProduct

/-- Linear maps out of a tensor product are equal iff they agree on pure tensors. -/
theorem ext_iff' {R M N P : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] [AddCommMonoid P] [Module R P]
    {g h : M ⊗[R] N →ₗ[R] P} :
    g = h ↔ ∀ x y, g (x ⊗ₜ[R] y) = h (x ⊗ₜ[R] y) :=
  ⟨fun hxy x y => by rw [hxy], fun hxy => TensorProduct.ext' hxy⟩

end TensorProduct
