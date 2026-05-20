/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/

import LeanPool.Monlib4.LinearAlgebra.MySpec
import LeanPool.Monlib4.RepTheory.AutMat
import Mathlib.Algebra.Star.Pi
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.Matrix.Order
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

theorem _root_.Matrix.unitaryGroup.injective_hMul (U : unitaryGroup n 𝕜) (x y : Matrix n n 𝕜) :
    x = y ↔ x * (U : Matrix n n 𝕜) = y * (U : Matrix n n 𝕜) := by
  constructor
  · intro h
    rw [h]
  · intro h
    have h' := congrArg (fun z : Matrix n n 𝕜 => z * (U⁻¹ : unitaryGroup n 𝕜)) h
    simpa [Matrix.mul_assoc, UnitaryGroup.inv_apply] using h'

end

section Positivity

variable [RCLike 𝕜] [DecidableEq n]

open scoped ComplexOrder MatrixOrder

/-- A unitary inner automorphism preserves positive semidefinite matrices. -/
theorem _root_.Matrix.innerAut_posSemidef_iff (U : unitaryGroup n 𝕜) {a : Matrix n n 𝕜} :
    (innerAut U a).PosSemidef ↔ a.PosSemidef := by
  constructor
  · intro h
    rw [← Matrix.nonneg_iff_posSemidef] at h ⊢
    rcases CStarAlgebra.nonneg_iff_eq_star_mul_self.mp h with ⟨b, hb⟩
    rw [← innerAut_inv_apply_innerAut_self U a, hb, Matrix.innerAut.map_mul]
    rw [← Matrix.innerAut.map_star]
    exact CStarAlgebra.nonneg_iff_eq_star_mul_self.mpr ⟨innerAut U⁻¹ b, rfl⟩
  · intro h
    rw [← Matrix.nonneg_iff_posSemidef] at h ⊢
    rcases CStarAlgebra.nonneg_iff_eq_star_mul_self.mp h with ⟨b, hb⟩
    rw [hb, Matrix.innerAut.map_mul]
    rw [← Matrix.innerAut.map_star]
    exact CStarAlgebra.nonneg_iff_eq_star_mul_self.mpr ⟨innerAut U b, rfl⟩

theorem _root_.Matrix.posSemidef_innerAut {a : Matrix n n 𝕜} (ha : a.PosSemidef)
    (U : unitaryGroup n 𝕜) :
    (innerAut U a).PosSemidef :=
  (innerAut_posSemidef_iff U).mpr ha

theorem _root_.Matrix.innerAut_isUnit_iff (U : unitaryGroup n 𝕜) {x : Matrix n n 𝕜} :
    IsUnit (innerAut U x) ↔ IsUnit x := by
  simpa [innerAut_coe] using (isUnit_map_iff (innerAutStarAlg U).toAlgEquiv.toMulEquiv x)

/-- A unitary inner automorphism preserves positive definite matrices. -/
theorem _root_.Matrix.innerAut_posDef_iff (U : unitaryGroup n 𝕜) {x : Matrix n n 𝕜} :
    (innerAut U x).PosDef ↔ x.PosDef := by
  constructor
  · intro h
    exact ((innerAut_posSemidef_iff U).mp h.posSemidef).posDef_iff_isUnit.mpr
      ((innerAut_isUnit_iff U).mp h.isUnit)
  · intro h
    exact ((innerAut_posSemidef_iff U).mpr h.posSemidef).posDef_iff_isUnit.mpr
      ((innerAut_isUnit_iff U).mpr h.isUnit)

theorem _root_.Matrix.posDef_innerAut {a : Matrix n n 𝕜} (ha : a.PosDef)
    (U : unitaryGroup n 𝕜) :
    (innerAut U a).PosDef :=
  (innerAut_posDef_iff U).mpr ha

open scoped BigOperators

/-- Every star-algebra equivalence of `Mₙ` is implemented by a unitary conjugation. -/
theorem _root_.StarAlgEquiv.of_matrix_is_inner
    (f : Matrix n n 𝕜 ≃⋆ₐ[𝕜] Matrix n n 𝕜) :
    ∃ U : unitaryGroup n 𝕜, innerAutStarAlg U = f := by
  by_cases h : IsEmpty n
  · haveI := h
    use 1
    ext a
    have : a = 0 := by simp only [eq_iff_true_of_subsingleton]
    simp_rw [this, map_zero]
  rw [not_isEmpty_iff] at h
  haveI := h
  let f' := f.toAlgEquiv
  obtain ⟨y', hy⟩ := aut_mat_inner f'
  let y := LinearMap.toMatrix' (y'.toLinearMap)
  let yinv := LinearMap.toMatrix' y'.symm.toLinearMap
  have Hy : y * yinv = 1 ∧ yinv * y = 1 := by
    simp_rw [y, yinv, ← LinearMap.toMatrix'_comp,
      LinearEquiv.comp_coe, LinearEquiv.symm_trans_self, LinearEquiv.self_trans_symm,
      LinearEquiv.refl_toLinearMap, LinearMap.toMatrix'_id, and_self_iff]
  have H : y⁻¹ = yinv := inv_eq_left_inv Hy.2
  have hf' : ∀ x : Matrix n n 𝕜, f' x = y * x * y⁻¹ := by
    intro x
    simp_rw [hy, Algebra.autInner_apply, H]
    rfl
  have hf : ∀ x : Matrix n n 𝕜, f x = y * x * y⁻¹ := by
    intro x
    rw [← hf']
    rfl
  have hstar : ∀ x : Matrix n n 𝕜, (f x)ᴴ = f xᴴ :=
    fun _ => (map_star f _).symm
  simp_rw [hf, conjTranspose_mul, conjTranspose_nonsing_inv] at hstar
  have hcomm_aux : ∀ x : Matrix n n 𝕜, yᴴ * y * xᴴ * y⁻¹ = xᴴ * yᴴ := by
    intro x
    simp_rw [Matrix.mul_assoc, ← Matrix.mul_assoc y, ← hstar, ← Matrix.mul_assoc, ←
      conjTranspose_nonsing_inv, ← conjTranspose_mul, H, Hy.2, Matrix.mul_one]
  have hcomm_star : ∀ x : Matrix n n 𝕜, Commute xᴴ (yᴴ * y) := by
    intro x
    simp_rw [Commute, SemiconjBy, ← Matrix.mul_assoc, ← hcomm_aux, Matrix.mul_assoc, H,
      Hy.2, Matrix.mul_one]
  have hcomm : ∀ x : Matrix n n 𝕜, Commute x (yᴴ * y) := by
    intro x
    specialize hcomm_star xᴴ
    simp_rw [conjTranspose_conjTranspose] at hcomm_star
    exact hcomm_star
  obtain ⟨α, hα⟩ := commutes_with_all_iff.mp hcomm
  have hpos_semidef : (yᴴ * y).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self y
  have hy_unit : IsUnit y := ⟨⟨y, yinv, Hy.1, Hy.2⟩, rfl⟩
  have hunit_yhy : IsUnit (yᴴ * y) := by
    simpa [star_eq_conjTranspose] using (isUnit_star.mpr hy_unit).mul hy_unit
  have hpos_def := hpos_semidef.posDef_iff_isUnit.mpr hunit_yhy
  have hα_re : α = RCLike.re α := by
    have hdiag := IsHermitian.coe_re_diag hpos_semidef.1
    simp_rw [hα, diag_smul, diag_one, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one] at hdiag
    have hone_ne_zero : (1 : n → 𝕜) ≠ 0 := by
      simp_rw [ne_eq, funext_iff, Pi.one_apply, Pi.zero_apply, one_ne_zero]
      simp only [Classical.not_forall, not_false_iff, exists_const]
    have hsmul : (RCLike.re α : 𝕜) • (1 : n → 𝕜) = α • 1 := by
      rw [← hdiag]
      ext1
      simp only [Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
    rw [(smul_left_injective _ hone_ne_zero).eq_iff] at hsmul
    rw [hsmul]
  have hdiag_pos : (diagonal fun _ : n => α).PosDef := by
    rw [← Matrix.smul_one_eq_diagonal α, ← hα]
    exact hpos_def
  have hpositive : 0 < RCLike.re α := by
    have hαpos : 0 < α := (Matrix.posDef_diagonal_iff.mp hdiag_pos) h.some
    rw [hα_re, RCLike.ofReal_pos] at hαpos
    exact hαpos
  have hunitary :
      (((RCLike.re α : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : 𝕜) • y ∈ unitaryGroup n 𝕜 := by
    rw [mem_unitaryGroup_iff', star_eq_conjTranspose]
    simp_rw [conjTranspose_smul, RCLike.star_def, Matrix.smul_mul, Matrix.mul_smul,
      RCLike.conj_ofReal, smul_smul, ← RCLike.ofReal_mul]
    rw [← Real.rpow_add hpositive, hα, hα_re, smul_smul, ← RCLike.ofReal_mul,
      RCLike.ofReal_re, ← Real.rpow_add_one (NeZero.of_pos hpositive).out]
    norm_num
  let U : unitaryGroup n 𝕜 := ⟨_, hunitary⟩
  have hU : (U : Matrix n n 𝕜) =
      (((RCLike.re α : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : 𝕜) • y := rfl
  have hU_inv :
      ((((RCLike.re α : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : 𝕜) • y)⁻¹ =
        ((U⁻¹ : _) : Matrix n n 𝕜) := by
    apply inv_eq_left_inv
    rw [← hU, UnitaryGroup.inv_apply, UnitaryGroup.star_mul_self]
  have hscalar_inv :
      ((((RCLike.re α : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : 𝕜) • y)⁻¹ =
        (((RCLike.re α : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : 𝕜)⁻¹ • y⁻¹ := by
    apply inv_eq_left_inv
    simp_rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [inv_mul_cancel₀, one_smul, H, Hy.2]
    · simp_rw [ne_eq, RCLike.ofReal_eq_zero, Real.rpow_eq_zero_iff_of_nonneg (le_of_lt hpositive),
        (NeZero.of_pos hpositive).out, false_and]
      exact not_false
  use U
  ext1 x
  simp_rw [innerAutStarAlg_apply_eq_innerAut_apply, innerAut_apply, ← hU_inv, hscalar_inv, hf,
    hU, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← RCLike.ofReal_inv, ←
    RCLike.ofReal_mul, ← Real.rpow_neg_one, ← Real.rpow_mul (le_of_lt hpositive),
    ← Real.rpow_add hpositive]
  norm_num

/-- A unitary matrix implementing a star-algebra equivalence of full matrix algebras. -/
noncomputable def _root_.StarAlgEquiv.of_matrix_unitary
    (f : Matrix n n 𝕜 ≃⋆ₐ[𝕜] Matrix n n 𝕜) : unitaryGroup n 𝕜 := by
  choose U _ using f.of_matrix_is_inner
  exact U

lemma _root_.StarAlgEquiv.eq_innerAut
    (f : Matrix n n 𝕜 ≃⋆ₐ[𝕜] Matrix n n 𝕜) :
    innerAutStarAlg f.of_matrix_unitary = f := by
  rw [StarAlgEquiv.of_matrix_unitary]
  generalize_proofs
  expose_names
  exact pf_1

/-- Spectral theorem in Monlib's inner-automorphism notation. -/
theorem _root_.Matrix.IsHermitian.spectral_theorem'' {x : Matrix n n 𝕜}
    (hx : x.IsHermitian) :
    x = innerAut hx.eigenvectorUnitary (diagonal (RCLike.ofReal ∘ hx.eigenvalues)) := by
  simpa [innerAut, innerAutStarAlg] using hx.spectral_theorem

end Positivity

variable [Field 𝕜] [StarRing 𝕜] [DecidableEq n]

theorem _root_.Matrix.innerAutStarAlg_equiv_toLinearMap (U : unitaryGroup n 𝕜) :
    (innerAutStarAlg U).toAlgEquiv.toLinearMap = innerAut U :=
  rfl

theorem _root_.Matrix.innerAutStarAlg_equiv_symm_toLinearMap (U : unitaryGroup n 𝕜) :
    (innerAutStarAlg U).symm.toAlgEquiv.toLinearMap = innerAut U⁻¹ := by
  ext1
  simp only [innerAut_apply, inv_inv]
  rw [UnitaryGroup.inv_apply]
  rfl

theorem _root_.Matrix.innerAut_comp_inj (U : Matrix.unitaryGroup n 𝕜)
    (S T : Matrix n n 𝕜 →ₗ[𝕜] Matrix n n 𝕜) :
    S = T ↔ innerAut U ∘ₗ S = innerAut U ∘ₗ T := by
  simp_rw [LinearMap.ext_iff, LinearMap.comp_apply, innerAut_eq_iff,
    innerAut_inv_apply_innerAut_self]

theorem _root_.Matrix.innerAut_inj_comp (U : unitaryGroup n 𝕜)
    (S T : Matrix n n 𝕜 →ₗ[𝕜] Matrix n n 𝕜) :
    S = T ↔ S ∘ₗ innerAut U = T ∘ₗ innerAut U := by
  refine ⟨fun h => by rw [h], fun h => ?_⟩
  simp_rw [LinearMap.ext_iff, LinearMap.comp_apply] at h ⊢
  intro x
  nth_rw 1 [← innerAut_apply_innerAut_inv_self U x]
  rw [h, innerAut_apply_innerAut_inv_self]

end Matrix
