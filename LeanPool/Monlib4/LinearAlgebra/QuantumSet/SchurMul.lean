/-
Copyright (c) 2024 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/

import LeanPool.Monlib4.LinearAlgebra.QuantumSet.Basic
import Mathlib.RingTheory.Coalgebra.Basic

/-!
# Schur Product Operator

This file ports the definition of the upstream `Monlib.LinearAlgebra.QuantumSet.SchurMul`
operator.  The deeper upstream Schur-product theorem stack depends on the finite-dimensional
Hilbert-algebra coalgebra instance and tensor-product infrastructure that are not yet recovered
in the current monlib4 slice.
-/

open scoped TensorProduct BigOperators

local notation "m" x => LinearMap.mul' ℂ x
local notation x " ⊗ₘ " y => TensorProduct.map x y

open Coalgebra

/-- Schur product `x •ₛ y := m ∘ (x ⊗ y) ∘ comul`. -/
@[simps]
noncomputable def schurMul {B C : Type*}
    [AddCommMonoid B] [NonUnitalNonAssocSemiring C]
    [Module ℂ B] [Module ℂ C] [CoalgebraStruct ℂ B]
    [SMulCommClass ℂ C C] [IsScalarTower ℂ C C] :
    (B →ₗ[ℂ] C) →ₗ[ℂ] (B →ₗ[ℂ] C) →ₗ[ℂ] (B →ₗ[ℂ] C) where
  toFun x :=
    { toFun := fun y => (m C) ∘ₗ (x ⊗ₘ y) ∘ₗ comul
      map_add' := fun _ _ => by
        simp only [TensorProduct.map_add_right, LinearMap.add_comp, LinearMap.comp_add]
      map_smul' := fun _ _ => by
        simp only [TensorProduct.map_smul_right, LinearMap.smul_comp, LinearMap.comp_smul,
          RingHom.id_apply] }
  map_add' x y := by
    simp only [TensorProduct.map_add_left, LinearMap.add_comp, LinearMap.comp_add,
      LinearMap.ext_iff, LinearMap.add_apply, LinearMap.coe_mk]
    intro _ _
    rfl
  map_smul' r x := by
    simp only [TensorProduct.map_smul_left, LinearMap.smul_comp, LinearMap.comp_smul,
      LinearMap.ext_iff, LinearMap.smul_apply, LinearMap.coe_mk, RingHom.id_apply]
    intro _ _
    rfl

@[inherit_doc schurMul]
notation3:80 (name := schurMulNotation) x:81 " •ₛ " y:80 => schurMul x y
