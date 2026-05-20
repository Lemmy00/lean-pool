/-
Copyright (c) 2024 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.Ring
import LeanPool.Monlib4.LinearAlgebra.Coalgebra.FiniteDimensional

/-!
# Quantum Sets

This file ports the structural core of upstream `Monlib.LinearAlgebra.QuantumSet.Basic`:
star algebras with modular automorphisms, inner-product algebras, quantum sets,
the base quantum set on `ℂ`, basic modular inner-product identities, and the
coalgebra comultiplication on `ℂ`.

The coalgebra, `Psi`/`Upsilon`, and Schur-product layers of the upstream file
still depend on older normed-ring scaffolding and large heartbeat overrides, so
they are intentionally not included here.
-/

/-- A star algebra over `ℂ` equipped with a real-parameter modular automorphism group. -/
class starAlgebra (A : Type _) extends
    Ring A, Algebra ℂ A, StarRing A, StarModule ℂ A where
  /-- The modular automorphism `σ_r` as an algebra equivalence. -/
  modAut : Π _ : ℝ, A ≃ₐ[ℂ] A
  /-- The modular automorphisms compose additively in the real parameter. -/
  modAut_trans : ∀ r s, (modAut r).trans (modAut s) = modAut (r + s)
  /-- Star changes the sign of the modular parameter. -/
  modAut_star : ∀ r x, star (modAut r x) = modAut (-r) (star x)

attribute [instance] starAlgebra.toRing
attribute [instance] starAlgebra.toAlgebra
attribute [instance] starAlgebra.toStarRing
attribute [instance] starAlgebra.toStarModule
attribute [simp] starAlgebra.modAut_trans
attribute [simp] starAlgebra.modAut_star
export starAlgebra (modAut)

theorem starAlgebra.modAut_zero {A : Type*} [hA : starAlgebra A] :
    hA.modAut 0 = 1 := by
  ext x
  have := hA.modAut_trans 0 1
  rw [zero_add, AlgEquiv.ext_iff] at this
  specialize this x
  apply_fun (modAut 1).symm at this
  simp only [AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply] at this
  exact this

@[simp]
theorem starAlgebra.modAut_apply_modAut {A : Type*} [ha : starAlgebra A]
    (t r : ℝ) (a : A) :
    ha.modAut t (ha.modAut r a) = ha.modAut (t + r) a := by
  rw [← AlgEquiv.trans_apply, starAlgebra.modAut_trans, add_comm]

@[simp]
theorem starAlgebra.modAut_symm {A : Type*} [ha : starAlgebra A] (r : ℝ) :
    (ha.modAut r).symm = ha.modAut (-r) := by
  ext
  apply_fun (ha.modAut r) using AlgEquiv.injective _
  simp only [AlgEquiv.apply_symm_apply, modAut_apply_modAut, add_neg_cancel, ha.modAut_zero]
  rfl

attribute [simp] starAlgebra.modAut_zero

/-- A star algebra whose underlying complex module is an inner-product space. -/
class InnerProductAlgebra (A : Type*) [starAlgebra A]
    extends NormedAddCommGroup A, InnerProductSpace ℂ A

open scoped InnerProductSpace
open scoped TensorProduct

/-- A finite-dimensional quantum set with a modular automorphism and fixed orthonormal basis. -/
class QuantumSet (A : Type _) [ha : starAlgebra A]
    extends InnerProductAlgebra A where
  /-- The modular automorphism is symmetric for the quantum-set inner product. -/
  modAut_isSymmetric : ∀ r x y, ⟪ha.modAut r x, y⟫_ℂ = ⟪x, ha.modAut r y⟫_ℂ
  /-- The modular exponent used in the KMS identities. -/
  k : ℝ
  inner_star_left : ∀ x y z : A, ⟪x * y, z⟫_ℂ = ⟪y, ha.modAut (-k) (star x) * z⟫_ℂ
  inner_conj_left : ∀ x y z : A, ⟪x * y, z⟫_ℂ = ⟪x, z * ha.modAut (-k-1) (star y)⟫_ℂ
  /-- The index type of the fixed orthonormal basis. -/
  n : Type*
  /-- The fixed basis index type is finite. -/
  n_isFintype : Fintype n
  /-- The fixed basis index type has decidable equality. -/
  n_isDecidableEq : DecidableEq n
  /-- A fixed orthonormal basis of the quantum set. -/
  onb : OrthonormalBasis n ℂ A

attribute [instance] QuantumSet.toInnerProductAlgebra
attribute [reducible, instance] QuantumSet.n_isFintype
attribute [reducible, instance] QuantumSet.n_isDecidableEq
attribute [simp] QuantumSet.inner_star_left
attribute [simp] QuantumSet.modAut_isSymmetric

export QuantumSet (n onb k)

variable {A : Type*} [ha : _root_.starAlgebra A]

/-- The fixed basis index type of a quantum set is finite. -/
instance n_isFinite [QuantumSet A] : Finite (n A) := by
  infer_instance

alias QuantumSet.modAut_apply_modAut := starAlgebra.modAut_apply_modAut

lemma QuantumSet.inner_conj [QuantumSet A] (a b : A) :
    ⟪a, b⟫_ℂ = ⟪star b, ha.modAut (-(2 * k A) - 1) (star a)⟫_ℂ :=
calc
  ⟪a, b⟫_ℂ = ⟪1 * a, b⟫_ℂ := by rw [one_mul]
  _ = ⟪1, b * ha.modAut (-k A - 1) (star a)⟫_ℂ := by rw [inner_conj_left]
  _ = starRingEnd ℂ ⟪b * ha.modAut (-k A - 1) (star a), 1⟫_ℂ := by
    rw [inner_conj_symm]
  _ = starRingEnd ℂ ⟪ha.modAut (-k A - 1) (star a), ha.modAut (-k A) (star b)⟫_ℂ := by
    rw [inner_star_left, mul_one]
  _ = ⟪star b, ha.modAut (-(2 * k A) - 1) (star a)⟫_ℂ := by
    rw [inner_conj_symm, modAut_isSymmetric, modAut_apply_modAut]
    ring_nf

lemma QuantumSet.inner_conj' [QuantumSet A] (a b : A) :
    ⟪a, b⟫_ℂ = ⟪ha.modAut (-(2 * k A) - 1) (star b), star a⟫_ℂ := by
  rw [inner_conj, modAut_isSymmetric]

lemma QuantumSet.inner_modAut_right_conj [QuantumSet A] (a b : A) :
    ⟪a, ha.modAut (-k A) (star b)⟫_ℂ =
      ⟪b, ha.modAut (-k A - 1) (star a)⟫_ℂ := by
  nth_rw 1 [← one_mul a]
  rw [inner_conj_left, ← inner_star_left, mul_one]

lemma QuantumSet.inner_conj'' [QuantumSet A] (a b : A) :
    ⟪a, b⟫_ℂ =
      ⟪ha.modAut ((-(2 * k A) - 1) / 2) (star b),
        ha.modAut ((-(2 * k A) - 1) / 2) (star a)⟫_ℂ :=
calc
  ⟪a, b⟫_ℂ = ⟪ha.modAut (-(2 * k A) - 1) (star b), star a⟫_ℂ := by
    rw [inner_conj']
  _ = ⟪ha.modAut ((-(2 * k A) - 1) / 2)
        (ha.modAut ((-(2 * k A) - 1) / 2) (star b)), star a⟫_ℂ := by
    rw [modAut_apply_modAut]
    norm_num
  _ = ⟪ha.modAut ((-(2 * k A) - 1) / 2) (star b),
        ha.modAut ((-(2 * k A) - 1) / 2) (star a)⟫_ℂ := by
    rw [modAut_isSymmetric]

section Complex

noncomputable instance Complex.starAlgebra : starAlgebra ℂ where
  modAut _ := 1
  modAut_trans _ _ := rfl
  modAut_star _ _ := rfl

noncomputable instance : InnerProductAlgebra ℂ where

noncomputable instance Complex.quantumSet : QuantumSet ℂ where
  modAut_isSymmetric _ _ _ := rfl
  k := 0
  inner_star_left _ _ _ := by
    simp_rw [RCLike.inner_apply, modAut, RCLike.star_def, AlgEquiv.one_apply, mul_comm, map_mul]
    ring
  inner_conj_left x y z := by
    simp_rw [RCLike.inner_apply, modAut, map_mul, RCLike.star_def, AlgEquiv.one_apply, mul_comm z]
    rw [mul_assoc, mul_comm]
  n := Unit
  n_isFintype := inferInstance
  n_isDecidableEq := inferInstance
  onb := OrthonormalBasis.singleton Unit ℂ

@[simp]
theorem QuantumSet.complex_modAut :
    Complex.starAlgebra.modAut = 1 :=
rfl

theorem QuantumSet.complex_comul :
    (Coalgebra.comul : ℂ →ₗ[ℂ] ℂ ⊗[ℂ] ℂ) = (TensorProduct.lid ℂ ℂ).symm.toLinearMap := by
  ext
  rw [TensorProduct.inner_ext_iff']
  intro a b
  simp

end Complex
