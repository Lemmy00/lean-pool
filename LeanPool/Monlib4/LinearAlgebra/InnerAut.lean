/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/

import LeanPool.Monlib4.LinearAlgebra.MySpec
import LeanPool.Monlib4.RepTheory.AutMat
import Mathlib.Algebra.Star.Pi
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Inner Automorphisms

This file ports the upstream monlib4 unitary inner-automorphism interface.  In
current Mathlib the general star-algebra automorphism by unitary conjugation is
available as `Unitary.conjStarAlgAut`; the declarations here keep monlib4's
names for the matrix-algebra specialization and its trace, spectrum, and
Hermitian-preservation lemmas.
-/

section

variable {n 𝕜 : Type _} [Fintype n] [Field 𝕜] [StarRing 𝕜]

@[simp]
theorem StarAlgEquiv.trace_preserving (f : Matrix n n 𝕜 ≃⋆ₐ[𝕜] Matrix n n 𝕜)
    (x : Matrix n n 𝕜) : (f x).trace = x.trace := by
  classical
  exact Matrix.aut_mat_inner_trace_preserving f.toAlgEquiv x

end

namespace unitary

/-- The star-algebra automorphism given by conjugation with a unitary element. -/
abbrev innerAutStarAlg (K : Type _) {R : Type _} [Semiring R] [StarMul R]
    [SMul K R] [IsScalarTower K R R] [SMulCommClass K R R] (a : unitary R) :
    R ≃⋆ₐ[K] R :=
  Unitary.conjStarAlgAut K R a

theorem innerAutStarAlg_apply {K R : Type _} [Semiring R] [StarMul R]
    [SMul K R] [IsScalarTower K R R] [SMulCommClass K R R] (U : unitary R) (x : R) :
    innerAutStarAlg K U x = U * x * (star U : unitary R) :=
  rfl

theorem innerAutStarAlg_apply' {K R : Type _} [Semiring R] [StarMul R]
    [SMul K R] [IsScalarTower K R R] [SMulCommClass K R R] (U : unitary R) (x : R) :
    innerAutStarAlg K U x = U * x * (U⁻¹ : unitary R) := by
  rfl

theorem innerAutStarAlg_apply'' {K R : Type _} [Semiring R] [StarMul R]
    [SMul K R] [IsScalarTower K R R] [SMulCommClass K R R] (U : unitary R) (x : R) :
    innerAutStarAlg K U x = U * x * star (U : R) :=
  rfl

theorem innerAutStarAlg_symm_apply {K R : Type _} [Semiring R] [StarMul R]
    [SMul K R] [IsScalarTower K R R] [SMulCommClass K R R] (U : unitary R) (x : R) :
    (innerAutStarAlg K U).symm x = (star U : unitary R) * x * U :=
  rfl

theorem innerAutStarAlg_symm_apply' {K R : Type _} [Semiring R] [StarMul R]
    [SMul K R] [IsScalarTower K R R] [SMulCommClass K R R] (U : unitary R) (x : R) :
    (innerAutStarAlg K U).symm x = (U⁻¹ : unitary R) * x * U := by
  rfl

theorem innerAutStarAlg_symm_apply'' {K R : Type _} [Semiring R] [StarMul R]
    [SMul K R] [IsScalarTower K R R] [SMulCommClass K R R] (U : unitary R) (x : R) :
    (innerAutStarAlg K U).symm x = star (U : R) * x * U :=
  rfl

theorem innerAutStarAlg_symm {K R : Type _} [Semiring R] [StarMul R]
    [SMul K R] [IsScalarTower K R R] [SMulCommClass K R R] (U : unitary R) :
    (innerAutStarAlg K U).symm = innerAutStarAlg K (star U) :=
  Unitary.conjStarAlgAut_symm U

theorem innerAutStarAlg_symm' {K R : Type _} [Semiring R] [StarMul R]
    [SMul K R] [IsScalarTower K R R] [SMulCommClass K R R] (U : unitary R) :
    (innerAutStarAlg K U).symm = innerAutStarAlg K U⁻¹ := by
  rw [innerAutStarAlg_symm]
  rfl

instance (R : Type*) [Monoid R] [StarMul R] :
    CoeTC (unitary R) R :=
  ⟨fun x => x⟩

theorem pi_mem {k : Type _} {s : k → Type _} [∀ i, Semiring (s i)]
    [∀ i, StarMul (s i)] (U : Π i, unitary (s i)) :
    (fun i => (U i : s i)) ∈ unitary (∀ i, s i) := by
  rw [Unitary.mem_iff]
  simp only [Pi.mul_def, Pi.star_apply, Unitary.coe_star_mul_self]
  simp only [← Unitary.coe_star, Unitary.coe_mul_star_self, and_self]
  rfl

/-- Build a unitary element of a dependent function type from pointwise unitaries. -/
@[inline]
abbrev pi {k : Type _} {s : k → Type _} [∀ i, Semiring (s i)]
    [∀ i, StarMul (s i)] (U : ∀ i, unitary (s i)) :
    unitary (∀ i, s i) :=
  ⟨fun i => U i, pi_mem U⟩

theorem pi_apply {k : Type _} {s : k → Type _} [∀ i, Semiring (s i)]
    [∀ i, StarMul (s i)] (U : ∀ i, unitary (s i)) {i : k} :
    (pi U : ∀ i, s i) i = U i :=
  rfl

end unitary

namespace Matrix

variable {n 𝕜 : Type _} [Fintype n]

section

variable [Field 𝕜] [StarRing 𝕜]

theorem _root_.Matrix.unitaryGroup.coe_hMul_star_self [DecidableEq n]
    (a : Matrix.unitaryGroup n 𝕜) :
    (HMul.hMul a (star a) : Matrix n n 𝕜) = (1 : Matrix n n 𝕜) := by
  simp only [Unitary.mul_star_self]
  rfl

theorem _root_.Matrix.unitaryGroup.star_coe_eq_coe_star [DecidableEq n]
    (U : unitaryGroup n 𝕜) :
    (star (U : unitaryGroup n 𝕜) : Matrix n n 𝕜) = (star U : unitaryGroup n 𝕜) :=
  rfl

/-- The star-algebra automorphism `x ↦ U * x * U⁻¹`. -/
@[inline]
abbrev innerAutStarAlg [DecidableEq n] (a : unitaryGroup n 𝕜) :
    Matrix n n 𝕜 ≃⋆ₐ[𝕜] Matrix n n 𝕜 :=
  unitary.innerAutStarAlg 𝕜 a

open scoped Matrix

theorem innerAutStarAlg_apply [DecidableEq n] (U : unitaryGroup n 𝕜) (x : Matrix n n 𝕜) :
    innerAutStarAlg U x = U * x * (star U : unitaryGroup n 𝕜) :=
  rfl

theorem innerAutStarAlg_apply' [DecidableEq n] (U : unitaryGroup n 𝕜) (x : Matrix n n 𝕜) :
    innerAutStarAlg U x = U * x * (U⁻¹ : unitaryGroup n 𝕜) :=
  rfl

theorem innerAutStarAlg_symm_apply [DecidableEq n] (U : unitaryGroup n 𝕜)
    (x : Matrix n n 𝕜) :
    (innerAutStarAlg U).symm x = (star U : unitaryGroup n 𝕜) * x * U :=
  rfl

theorem innerAutStarAlg_symm_apply' [DecidableEq n] (U : unitaryGroup n 𝕜)
    (x : Matrix n n 𝕜) :
    (innerAutStarAlg U).symm x = (U⁻¹ : unitaryGroup n 𝕜) * x * U :=
  rfl

theorem innerAutStarAlg_symm [DecidableEq n] (U : unitaryGroup n 𝕜) :
    (innerAutStarAlg U).symm = innerAutStarAlg U⁻¹ :=
  unitary.innerAutStarAlg_symm' U

/-- The unitary inner automorphism as a linear map. -/
abbrev innerAut [DecidableEq n] (U : unitaryGroup n 𝕜) :
    Matrix n n 𝕜 →ₗ[𝕜] Matrix n n 𝕜 :=
  (innerAutStarAlg U).toAlgEquiv.toLinearMap

@[simp]
theorem innerAut_coe [DecidableEq n] (U : unitaryGroup n 𝕜) :
    ⇑(innerAut U) = innerAutStarAlg U :=
  rfl

theorem innerAut_inv_coe [DecidableEq n] (U : unitaryGroup n 𝕜) :
    ⇑(innerAut U⁻¹) = (innerAutStarAlg U).symm := by
  simp_rw [innerAutStarAlg_symm]
  rfl

theorem innerAut_apply [DecidableEq n] (U : unitaryGroup n 𝕜) (x : Matrix n n 𝕜) :
    innerAut U x = U * x * (U⁻¹ : unitaryGroup n 𝕜) :=
  rfl

theorem innerAut_apply' [DecidableEq n] (U : unitaryGroup n 𝕜) (x : Matrix n n 𝕜) :
    innerAut U x = U * x * (star U : unitaryGroup n 𝕜) :=
  rfl

theorem innerAut_inv_apply [DecidableEq n] (U : unitaryGroup n 𝕜) (x : Matrix n n 𝕜) :
    innerAut U⁻¹ x = (U⁻¹ : unitaryGroup n 𝕜) * x * U := by
  simp only [innerAut_apply, inv_inv _]

theorem innerAut_star_apply [DecidableEq n] (U : unitaryGroup n 𝕜) (x : Matrix n n 𝕜) :
    innerAut (star U) x = (star U : unitaryGroup n 𝕜) * x * U := by
  simp_rw [innerAut_apply', star_star]

theorem innerAut_conjTranspose [DecidableEq n] (U : unitaryGroup n 𝕜)
    (x : Matrix n n 𝕜) :
    (innerAut U x)ᴴ = innerAut U xᴴ := by
  simpa only [innerAut_coe] using (map_star (innerAutStarAlg U) x).symm

theorem innerAut_comp_innerAut [DecidableEq n] (U₁ U₂ : unitaryGroup n 𝕜) :
    innerAut U₁ ∘ₗ innerAut U₂ = innerAut (U₁ * U₂) := by
  simp_rw [LinearMap.ext_iff, LinearMap.comp_apply, innerAut_apply, UnitaryGroup.inv_apply,
    UnitaryGroup.mul_apply, Matrix.star_mul, Matrix.mul_assoc, forall_true_iff]

theorem innerAut_apply_innerAut [DecidableEq n] (U₁ U₂ : unitaryGroup n 𝕜)
    (x : Matrix n n 𝕜) :
    innerAut U₁ (innerAut U₂ x) = innerAut (U₁ * U₂) x := by
  rw [← innerAut_comp_innerAut, LinearMap.comp_apply]

theorem innerAut_eq_iff [DecidableEq n] (U : unitaryGroup n 𝕜) (x y : Matrix n n 𝕜) :
    innerAut U x = y ↔ x = innerAut U⁻¹ y := by
  rw [innerAut_coe, innerAut_inv_coe]
  exact (innerAutStarAlg U).toEquiv.apply_eq_iff_eq_symm_apply

theorem _root_.Matrix.unitaryGroup.toLinearEquiv_apply [DecidableEq n] (U : unitaryGroup n 𝕜)
    (x : n → 𝕜) :
    (UnitaryGroup.toLinearEquiv U) x = (↑(U : unitaryGroup n 𝕜) : Matrix n n 𝕜).mulVec x :=
  rfl

theorem _root_.Matrix.unitaryGroup.toLinearEquiv_eq [DecidableEq n]
    (U : unitaryGroup n 𝕜) (x : n → 𝕜) :
    (UnitaryGroup.toLinearEquiv U) x = (UnitaryGroup.toLin' U) x :=
  rfl

theorem _root_.Matrix.unitaryGroup.toLin'_apply [DecidableEq n] (U : unitaryGroup n 𝕜)
    (x : n → 𝕜) :
    (UnitaryGroup.toLin' U) x = (↑(U : unitaryGroup n 𝕜) : Matrix n n 𝕜).mulVec x :=
  rfl

theorem _root_.Matrix.unitaryGroup.toLin'_eq [DecidableEq n] (U : unitaryGroup n 𝕜)
    (x : n → 𝕜) :
    (UnitaryGroup.toLin' U) x = (toLin' U) x :=
  rfl

omit [StarRing 𝕜] in
theorem toLinAlgEquiv'_apply' [DecidableEq n] (x : Matrix n n 𝕜) :
    toLinAlgEquiv' x =
      (toLin' : Matrix n n 𝕜 ≃ₗ[𝕜] (n → 𝕜) →ₗ[𝕜] (n → 𝕜)) x :=
  rfl

/-- The spectrum of `U * x * U⁻¹` is the spectrum of `x`. -/
theorem _root_.Matrix.innerAut.spectrum_eq [DecidableEq n] (U : unitaryGroup n 𝕜)
    (x : Matrix n n 𝕜) :
    spectrum 𝕜 (toLin' (innerAut U x)) = spectrum 𝕜 (toLin' x) := by
  simp_rw [← toLinAlgEquiv'_apply', AlgEquiv.spectrum_eq, innerAut_coe,
    AlgEquiv.spectrum_eq]

theorem innerAut_one [DecidableEq n] : innerAut (1 : unitaryGroup n 𝕜) = 1 := by
  simp_rw [LinearMap.ext_iff, innerAut_apply, UnitaryGroup.inv_apply, UnitaryGroup.one_apply,
    star_one, Matrix.mul_one, Matrix.one_mul, Module.End.one_apply, forall_true_iff]

theorem innerAut_comp_innerAut_inv [DecidableEq n] (U : unitaryGroup n 𝕜) :
    innerAut U ∘ₗ innerAut U⁻¹ = 1 := by
  rw [LinearMap.ext_iff]
  intro x
  rw [LinearMap.comp_apply, innerAut_coe, innerAut_inv_coe, StarAlgEquiv.apply_symm_apply]
  rfl

theorem innerAut_apply_innerAut_inv [DecidableEq n] (U₁ U₂ : unitaryGroup n 𝕜)
    (x : Matrix n n 𝕜) :
    innerAut U₁ (innerAut U₂⁻¹ x) = innerAut (U₁ * U₂⁻¹) x := by
  rw [innerAut_apply_innerAut]

theorem innerAut_apply_innerAut_inv_self [DecidableEq n] (U : unitaryGroup n 𝕜)
    (x : Matrix n n 𝕜) :
    innerAut U (innerAut U⁻¹ x) = x := by
  rw [innerAut_apply_innerAut_inv, mul_inv_cancel, innerAut_one, Module.End.one_apply]

theorem innerAut_inv_apply_innerAut_self [DecidableEq n] (U : unitaryGroup n 𝕜)
    (x : Matrix n n 𝕜) :
    innerAut U⁻¹ (innerAut U x) = x := by
  rw [innerAut_inv_coe, innerAut_coe]
  exact StarAlgEquiv.symm_apply_apply _ _

theorem innerAut_apply_zero [DecidableEq n] (U : unitaryGroup n 𝕜) :
    innerAut U 0 = 0 :=
  map_zero _

theorem innerAut_conj_spectrum_eq [DecidableEq n] (U : unitaryGroup n 𝕜)
    (x : Matrix n n 𝕜 →ₗ[𝕜] Matrix n n 𝕜) :
    spectrum 𝕜 (innerAut U⁻¹ ∘ₗ x ∘ₗ innerAut U) = spectrum 𝕜 x := by
  rw [spectrum.comm, LinearMap.comp_assoc, innerAut_comp_innerAut_inv, LinearMap.comp_one]

theorem innerAut_apply_one [DecidableEq n] (U : unitaryGroup n 𝕜) :
    innerAut U 1 = 1 := by
  rw [innerAut_coe, _root_.map_one]

theorem innerAutStarAlg_apply_eq_innerAut_apply [DecidableEq n] (U : unitaryGroup n 𝕜)
    (x : Matrix n n 𝕜) : innerAutStarAlg U x = innerAut U x :=
  rfl

theorem _root_.Matrix.innerAut.map_mul [DecidableEq n] (U : unitaryGroup n 𝕜)
    (x y : Matrix n n 𝕜) :
    innerAut U (x * y) = innerAut U x * innerAut U y := by
  rw [innerAut_coe, _root_.map_mul (innerAutStarAlg U)]

theorem _root_.Matrix.innerAut.map_star [DecidableEq n] (U : unitaryGroup n 𝕜)
    (x : Matrix n n 𝕜) :
    star (innerAut U x) = innerAut U (star x) :=
  innerAut_conjTranspose _ _

theorem innerAut_inv_eq_star [DecidableEq n] {x : unitaryGroup n 𝕜} :
    innerAut x⁻¹ = innerAut (star x) :=
  rfl

theorem _root_.Matrix.unitaryGroup.coe_inv [DecidableEq n] (U : unitaryGroup n 𝕜) :
    ⇑(U⁻¹ : unitaryGroup n 𝕜) = ((U : Matrix n n 𝕜)⁻¹ : Matrix n n 𝕜) := by
  symm
  apply inv_eq_left_inv
  simp_rw [UnitaryGroup.inv_apply, UnitaryGroup.star_mul_self]

theorem _root_.Matrix.innerAut.map_inv [DecidableEq n] (U : unitaryGroup n 𝕜)
    (x : Matrix n n 𝕜) :
    (innerAut U x)⁻¹ = innerAut U x⁻¹ := by
  simp_rw [innerAut_apply, Matrix.mul_inv_rev, ← unitaryGroup.coe_inv, inv_inv, Matrix.mul_assoc]

/-- The trace of `U * x * U⁻¹` is the trace of `x`. -/
theorem innerAut_apply_trace_eq [DecidableEq n] (U : unitaryGroup n 𝕜)
    (x : Matrix n n 𝕜) :
    (innerAut U x).trace = x.trace := by
  rw [innerAut_coe, StarAlgEquiv.trace_preserving]

variable [DecidableEq n]

theorem exists_innerAut_iff_exists_innerAut_inv {P : Matrix n n 𝕜 → Prop}
    (x : Matrix n n 𝕜) :
    (∃ U : unitaryGroup n 𝕜, P (innerAut U x)) ↔
      ∃ U : unitaryGroup n 𝕜, P (innerAut U⁻¹ x) := by
  constructor <;> rintro ⟨U, hU⟩ <;> use U⁻¹
  simp_rw [inv_inv]
  exact hU

theorem _root_.Matrix.innerAut.is_injective (U : unitaryGroup n 𝕜) :
    Function.Injective (innerAut U) := by
  intro u v huv
  rw [← innerAut_inv_apply_innerAut_self U u, huv, innerAut_inv_apply_innerAut_self]

/-- A matrix is Hermitian iff its image under a unitary inner automorphism is Hermitian. -/
theorem innerAut_isHermitian_iff (U : unitaryGroup n 𝕜) (x : Matrix n n 𝕜) :
    x.IsHermitian ↔ (innerAut U x).IsHermitian := by
  simp_rw [IsHermitian, innerAut_conjTranspose,
    Function.Injective.eq_iff (innerAut.is_injective U)]

end

end Matrix
