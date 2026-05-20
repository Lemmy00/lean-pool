/-
Copyright (c) 2024 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/

import LeanPool.Monlib4.LinearAlgebra.QuantumSet.Basic
import Mathlib.RingTheory.Coalgebra.Basic
import Mathlib.RingTheory.Coalgebra.Hom

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

theorem nonUnitalAlgHom_comp_mul {R A B : Type*} [CommSemiring R] [Semiring A]
    [Semiring B] [Algebra R A] [Algebra R B] (f : A →ₙₐ[R] B) :
    (LinearMapClass.linearMap f) ∘ₗ LinearMap.mul' R A =
      (LinearMap.mul' R B) ∘ₗ
        ((LinearMapClass.linearMap f) ⊗ₘ (LinearMapClass.linearMap f)) := by
  rw [TensorProduct.ext_iff']
  intro a b
  simp only [LinearMap.comp_apply, LinearMap.mul'_apply, TensorProduct.map_tmul]
  exact NonUnitalAlgHom.map_mul f a b

theorem algHom_comp_mul {R A B : Type*} [CommSemiring R] [Semiring A]
    [Semiring B] [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) :
    f.toLinearMap ∘ₗ LinearMap.mul' R A =
      (LinearMap.mul' R B) ∘ₗ (f.toLinearMap ⊗ₘ f.toLinearMap) :=
  by simpa using nonUnitalAlgHom_comp_mul f.toNonUnitalAlgHom

attribute [local instance] Algebra.ofIsScalarTowerSmulCommClass

variable {A B : Type*}
  [NormedAddCommGroupOfRing A] [NormedAddCommGroupOfRing B]
  [InnerProductSpace ℂ A] [InnerProductSpace ℂ B]
  [SMulCommClass ℂ A A] [SMulCommClass ℂ B B]
  [IsScalarTower ℂ A A] [IsScalarTower ℂ B B]
  [FiniteDimensional ℂ A] [FiniteDimensional ℂ B]

theorem comul_comp_nonUnitalAlgHom_adjoint (f : A →ₙₐ[ℂ] B) :
    Coalgebra.comul ∘ₗ LinearMap.adjoint (LinearMapClass.linearMap f) =
      ((LinearMap.adjoint (LinearMapClass.linearMap f)) ⊗ₘ
        (LinearMap.adjoint (LinearMapClass.linearMap f))) ∘ₗ Coalgebra.comul := by
  simp_rw [Coalgebra.comul_eq_mul_adjoint, ← TensorProduct.map_adjoint,
    ← LinearMap.adjoint_comp, nonUnitalAlgHom_comp_mul f]

theorem comul_comp_algHom_adjoint (f : A →ₐ[ℂ] B) :
    Coalgebra.comul ∘ₗ LinearMap.adjoint f.toLinearMap =
      ((LinearMap.adjoint f.toLinearMap) ⊗ₘ (LinearMap.adjoint f.toLinearMap)) ∘ₗ
        Coalgebra.comul := by
  simpa using comul_comp_nonUnitalAlgHom_adjoint f.toNonUnitalAlgHom

theorem schurMul_nonUnitalAlgHom_comp_coalgHom {C D : Type*}
    [Semiring C] [Semiring D]
    [Module ℂ C] [Module ℂ D]
    [SMulCommClass ℂ C C] [SMulCommClass ℂ D D]
    [IsScalarTower ℂ C C] [IsScalarTower ℂ D D]
    (g : C →ₙₐ[ℂ] D) (f : A →ₗc[ℂ] B) (x y : B →ₗ[ℂ] C) :
    ((LinearMapClass.linearMap g) ∘ₗ x ∘ₗ f.toLinearMap) •ₛ
        ((LinearMapClass.linearMap g) ∘ₗ y ∘ₗ f.toLinearMap) =
      (LinearMapClass.linearMap g) ∘ₗ (x •ₛ y) ∘ₗ f.toLinearMap := by
  simp_rw [schurMul_apply_apply, ← LinearMap.comp_assoc, nonUnitalAlgHom_comp_mul,
    LinearMap.comp_assoc, ← f.map_comp_comul]
  congr 1
  simp_rw [← LinearMap.comp_assoc]
  congr 1
  simp_rw [TensorProduct.map_comp]

theorem schurMul_algHom_comp_coalgHom {C D : Type*}
    [Semiring C] [Semiring D]
    [Module ℂ C] [Module ℂ D]
    [SMulCommClass ℂ C C] [SMulCommClass ℂ D D]
    [IsScalarTower ℂ C C] [IsScalarTower ℂ D D]
    (g : C →ₐ[ℂ] D) (f : A →ₗc[ℂ] B) (x y : B →ₗ[ℂ] C) :
    (g.toLinearMap ∘ₗ x ∘ₗ f.toLinearMap) •ₛ (g.toLinearMap ∘ₗ y ∘ₗ f.toLinearMap) =
      g.toLinearMap ∘ₗ (x •ₛ y) ∘ₗ f.toLinearMap := by
  simpa using schurMul_nonUnitalAlgHom_comp_coalgHom g.toNonUnitalAlgHom f x y

theorem schurMul_nonUnitalAlgHom_comp_nonUnitalAlgHom_adjoint {C D : Type*}
    [Semiring C] [Semiring D]
    [Module ℂ C] [Module ℂ D]
    [SMulCommClass ℂ C C] [SMulCommClass ℂ D D]
    [IsScalarTower ℂ C C] [IsScalarTower ℂ D D]
    (g : C →ₙₐ[ℂ] D) (f : B →ₙₐ[ℂ] A) (x y : B →ₗ[ℂ] C) :
    ((LinearMapClass.linearMap g) ∘ₗ x ∘ₗ
        (LinearMap.adjoint (LinearMapClass.linearMap f))) •ₛ
      ((LinearMapClass.linearMap g) ∘ₗ y ∘ₗ
        (LinearMap.adjoint (LinearMapClass.linearMap f))) =
      (LinearMapClass.linearMap g) ∘ₗ (x •ₛ y) ∘ₗ
        LinearMap.adjoint (LinearMapClass.linearMap f) := by
  simp_rw [schurMul_apply_apply, ← LinearMap.comp_assoc, nonUnitalAlgHom_comp_mul,
    LinearMap.comp_assoc, comul_comp_nonUnitalAlgHom_adjoint]
  congr 1
  simp_rw [← LinearMap.comp_assoc]
  congr 1
  simp_rw [TensorProduct.map_comp]

theorem schurMul_algHom_comp_algHom_adjoint {C D : Type*}
    [Semiring C] [Semiring D]
    [Module ℂ C] [Module ℂ D]
    [SMulCommClass ℂ C C] [SMulCommClass ℂ D D]
    [IsScalarTower ℂ C C] [IsScalarTower ℂ D D]
    (g : C →ₐ[ℂ] D) (f : B →ₐ[ℂ] A) (x y : B →ₗ[ℂ] C) :
    (g.toLinearMap ∘ₗ x ∘ₗ LinearMap.adjoint f.toLinearMap) •ₛ
        (g.toLinearMap ∘ₗ y ∘ₗ LinearMap.adjoint f.toLinearMap) =
      g.toLinearMap ∘ₗ (x •ₛ y) ∘ₗ LinearMap.adjoint f.toLinearMap := by
  simpa using schurMul_nonUnitalAlgHom_comp_nonUnitalAlgHom_adjoint
    g.toNonUnitalAlgHom f.toNonUnitalAlgHom x y
