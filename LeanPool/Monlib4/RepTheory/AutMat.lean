/-
Copyright (c) 2026 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.Trace
import LeanPool.Monlib4.LinearAlgebra.Matrix.Basic
import LeanPool.Monlib4.LinearAlgebra.Matrix.Cast

/-!
# Inner automorphisms of matrix algebras

This file ports the upstream monlib4 theorem that every automorphism of a
finite, nontrivial matrix algebra over a field is inner.  The downstream
corollaries package the implementing matrix as a linear equivalence or as an
element of the general linear group.
-/

open scoped BigOperators Matrix

variable {n R 𝕜 : Type _} [Field 𝕜] [Fintype n]

local notation "M" n => Matrix n n 𝕜
local notation "Mₙ" n => Matrix n n R

namespace Matrix

private def matT [Semiring R] (f : (Mₙ n) →ₗ[R] Mₙ n)
    (y z : n → R) : (n → R) →ₗ[R] n → R where
  toFun x := (f (vecMulVec x y)).mulVec z
  map_add' w p := by
    simp_rw [vecMulVec_eq (Fin 1), replicateCol_add w p,
      Matrix.add_mul, map_add, add_mulVec]
  map_smul' w r := by
    simp_rw [vecMulVec_eq (Fin 1), RingHom.id_apply,
      replicateCol_smul, smul_mul, LinearMap.map_smul, smul_mulVec_assoc]

private theorem matT_apply [Semiring R] (f : (Mₙ n) →ₗ[R] Mₙ n)
    (y z r : n → R) :
    matT f y z r = (f (vecMulVec r y)).mulVec z :=
  rfl

/-- Every automorphism of a finite nontrivial matrix algebra is inner. -/
theorem automorphism_matrix_inner [Field R] [DecidableEq n] [Nonempty n]
    (f : (Mₙ n) ≃ₐ[R] Mₙ n) :
    ∃ T : Mₙ n,
      (∀ a : Mₙ n, f a * T = T * a) ∧
        Function.Bijective (Matrix.toLin' T) := by
  have exists_vector : ∃ u : n → R, u ≠ 0 := ⟨1, one_ne_zero⟩
  have exists_vector' := exists_vector
  obtain ⟨u, hu⟩ := exists_vector
  obtain ⟨y, hy⟩ := exists_vector'
  have f_ne_zero_iff :
      f (vecMulVec u y) ≠ 0 ↔ vecMulVec u y ≠ 0 := by
    rw [not_iff_not]
    exact
      ⟨fun hzero =>
        (injective_iff_map_eq_zero f).mp f.bijective.1 _ hzero,
        fun hzero => by rw [hzero, map_zero]⟩
  have exists_z : ∃ z : n → R, (f (vecMulVec u y)) *ᵥ z ≠ 0 := by
    simp_rw [ne_eq, ← Classical.not_forall]
    suffices ¬f (vecMulVec u y) = 0 by
      simp_rw [mulVec_eq, zero_mulVec] at this
      exact this
    rw [← ne_eq, f_ne_zero_iff]
    exact vecMulVec_ne_zero hu hy
  obtain ⟨z, hz⟩ := exists_z
  let T := matT f.toLinearMap y z
  use LinearMap.toMatrix' T
  have commute :
      ∀ a : Mₙ n, f a * LinearMap.toMatrix' T =
        LinearMap.toMatrix' T * a := by
    simp_rw [mulVec_eq]
    intro A x
    symm
    calc
      (LinearMap.toMatrix' T * A) *ᵥ x = T (A *ᵥ x) := by
        ext
        rw [← mulVec_mulVec, LinearMap.toMatrix'_mulVec]
      _ = (f (vecMulVec (A *ᵥ x) y)) *ᵥ z := by
        rw [matT_apply, AlgEquiv.toLinearMap_apply]
      _ = (f (A * vecMulVec x y)) *ᵥ z := by
        simp_rw [vecMulVec_eq (Fin 1), replicateCol_mulVec, ← Matrix.mul_assoc]
      _ = (f A * f (vecMulVec x y)) *ᵥ z := by
        simp_rw [_root_.map_mul]
      _ = (f A) *ᵥ T x := by
        simp_rw [← mulVec_mulVec, ← AlgEquiv.toLinearMap_apply,
          ← matT_apply _ y z]
        rfl
      _ = (f A * LinearMap.toMatrix' T) *ᵥ x := by
        simp_rw [← mulVec_mulVec, ← toLin'_apply (LinearMap.toMatrix' T),
          toLin'_toMatrix']
  refine ⟨commute, ?_⟩
  simp_rw [Matrix.toLin'_toMatrix']
  suffices Function.Surjective T by
    exact ⟨LinearMap.injective_iff_surjective.mpr this, this⟩
  intro w
  have hTu : T u ≠ 0 := by
    rw [matT_apply _ y z]
    exact hz
  have exists_dual : ∃ d : n → R, T u ⬝ᵥ d = 1 := by
    rw [← vec_ne_zero] at hTu
    obtain ⟨q, hq⟩ := hTu
    use Pi.single q (T u q)⁻¹
    rw [dotProduct_single, mul_inv_cancel₀ hq]
  have exists_preimage : ∃ B : Mₙ n, (f B) *ᵥ T u = w := by
    obtain ⟨d, hd⟩ := exists_dual
    obtain ⟨B, hB⟩ := f.bijective.2 (vecMulVec w d)
    use B
    rw [hB, vecMulVec_eq (Fin 1), ← mulVec_mulVec]
    suffices replicateRow (Fin 1) d *ᵥ T u = 1 by
      ext
      simp_rw [this, mulVec, dotProduct, replicateCol_apply,
        Pi.one_apply, mul_one, Finset.sum_const, nsmul_eq_mul]
      simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
        Finset.card_singleton, Nat.cast_one, one_mul]
    ext
    simp_rw [mulVec, Pi.one_apply, ← hd, dotProduct, replicateRow_apply,
      mul_comm]
  obtain ⟨B, hB⟩ := exists_preimage
  use (toLin' B) u
  rw [← toLin'_toMatrix' T]
  simp_rw [toLin'_apply, mulVec_mulVec, ← commute, ← mulVec_mulVec,
    ← toLin'_apply (LinearMap.toMatrix' T), toLin'_toMatrix']
  exact hB

private def gMat [DecidableEq n] (a : M n) (b : (n → 𝕜) → n → 𝕜)
    (hb : Function.LeftInverse b (toLin' a) ∧
      Function.RightInverse b (toLin' a)) :
    (n → 𝕜) ≃ₗ[𝕜] n → 𝕜 where
  toFun x := (toLin' a) x
  map_add' := a.toLin'.map_add'
  map_smul' := a.toLin'.map_smul'
  invFun := b
  left_inv := hb.1
  right_inv := hb.2

private theorem gMat_apply [DecidableEq n] (a : M n)
    (b : (n → 𝕜) → n → 𝕜)
    (hb : Function.LeftInverse b (toLin' a) ∧
      Function.RightInverse b (toLin' a)) (x : n → 𝕜) :
    gMat a b hb x = (toLin' a) x :=
  rfl

/-- Version of `automorphism_matrix_inner` using a linear equivalence. -/
theorem automorphism_matrix_inner'' [DecidableEq n] [Nonempty n]
    (f : (M n) ≃ₐ[𝕜] M n) :
    ∃ T : (n → 𝕜) ≃ₗ[𝕜] n → 𝕜,
      ∀ a : M n,
        f a = LinearMap.toMatrix' T * a * LinearMap.toMatrix' T.symm := by
  obtain ⟨T, hT⟩ := automorphism_matrix_inner f
  obtain ⟨r, hr⟩ := Function.bijective_iff_has_inverse.mp hT.2
  let g := gMat T r hr
  use g
  intro a
  have hg : g.toLinearMap = toLin' T := by
    ext
    simp_rw [LinearMap.coe_comp, LinearEquiv.coe_toLinearMap,
      LinearMap.coe_single, Function.comp_apply, Matrix.toLin'_apply,
      Matrix.mulVec_single, g, gMat_apply T r hr, Matrix.toLin'_apply,
      Matrix.mulVec_single]
  rw [hg, LinearMap.toMatrix'_toLin', ← hT.1,
    ← LinearMap.toMatrix'_toLin' T, Matrix.mul_assoc, ← hg]
  symm
  calc
    f a * (LinearMap.toMatrix' g * LinearMap.toMatrix' g.symm) =
        f a * LinearMap.toMatrix' (g.symm.trans g) := by
      simp_rw [← LinearEquiv.comp_coe, LinearMap.toMatrix'_comp]
    _ = f a := by
      simp_rw [LinearEquiv.symm_trans_self, LinearEquiv.refl_toLinearMap,
        LinearMap.toMatrix'_id, Matrix.mul_one]

/-- Inner automorphism by conjugation with an invertible algebra element. -/
def Algebra.autInner {R E : Type _} [CommSemiring R] [Semiring E]
    [Algebra R E] (x : E) [Invertible x] : E ≃ₐ[R] E where
  toFun y := x * y * ⅟ x
  invFun y := ⅟ x * y * x
  left_inv _ := by
    simp_rw [← mul_assoc, invOf_mul_self, one_mul, invOf_mul_cancel_right]
  right_inv _ := by
    simp_rw [← mul_assoc, mul_invOf_self, one_mul, mul_invOf_cancel_right]
  map_add' _ _ := by
    simp_rw [mul_add, add_mul]
  commutes' r := by
    simp_rw [Algebra.algebraMap_eq_smul_one, mul_smul_one,
      smul_mul_assoc, mul_invOf_self]
  map_mul' _ _ := by
    simp_rw [mul_assoc, invOf_mul_cancel_left]

theorem Algebra.autInner_apply {R E : Type _} [CommSemiring R] [Semiring E]
    [Algebra R E] (x : E) [Invertible x] (y : E) :
    (Algebra.autInner x : E ≃ₐ[R] E) y = x * y * ⅟ x :=
  rfl

private theorem automorphism_matrix_inner''' [DecidableEq n] [Nonempty n]
    (f : (M n) ≃ₐ[𝕜] M n) :
    ∃ T : (n → 𝕜) ≃ₗ[𝕜] n → 𝕜,
      f =
        @Algebra.autInner 𝕜 (M n) _ _ _
          (LinearMap.toMatrix' (T : (n → 𝕜) →ₗ[𝕜] n → 𝕜))
          T.toInvertibleMatrix := by
  obtain ⟨T, hT⟩ := automorphism_matrix_inner'' f
  use T
  ext
  simp_rw [Algebra.autInner_apply, hT]
  rfl

/-- Any automorphism of a finite matrix algebra is implemented by conjugation. -/
theorem aut_mat_inner [DecidableEq n] (f : (M n) ≃ₐ[𝕜] M n) :
    ∃ T : (n → 𝕜) ≃ₗ[𝕜] n → 𝕜,
      f =
        @Algebra.autInner 𝕜 (M n) _ _ _
          (LinearMap.toMatrix' (T : (n → 𝕜) →ₗ[𝕜] n → 𝕜))
          T.toInvertibleMatrix := by
  rcases em (Nonempty n) with hn | hn
  · exact automorphism_matrix_inner''' f
  · use 1
    ext _ i _
    simp only [not_nonempty_iff, isEmpty_iff] at hn
    exact False.elim (hn i)

/-- Any automorphism of a finite matrix algebra is conjugation by `GL n 𝕜`. -/
theorem aut_mat_inner' [DecidableEq n] (f : (M n) ≃ₐ[𝕜] M n) :
    ∃ T : GL n 𝕜,
      f = @Algebra.autInner 𝕜 (M n) _ _ _ (T : M n) (Units.invertible T) := by
  obtain ⟨T, hT⟩ := aut_mat_inner f
  let T' : M n := LinearMap.toMatrix' T
  have hT' : T' = LinearMap.toMatrix' T := rfl
  let Tinv : M n := LinearMap.toMatrix' T.symm
  have hTinv : Tinv = LinearMap.toMatrix' T.symm := rfl
  refine ⟨⟨T', Tinv, ?_, ?_⟩, by congr⟩
  · simp only [hT', hTinv, ← LinearMap.toMatrix'_mul,
      Module.End.mul_eq_comp, LinearEquiv.comp_coe,
      LinearEquiv.symm_trans_self, LinearEquiv.refl_toLinearMap,
      LinearMap.toMatrix'_id]
  · simp only [hT', hTinv, ← LinearMap.toMatrix'_mul,
      Module.End.mul_eq_comp, LinearEquiv.comp_coe,
      LinearEquiv.self_trans_symm, LinearEquiv.refl_toLinearMap,
      LinearMap.toMatrix'_id]

/-- Automorphisms of finite matrix algebras preserve trace. -/
theorem aut_mat_inner_trace_preserving [DecidableEq n]
    (f : (M n) ≃ₐ[𝕜] M n) (x : M n) :
    (f x).trace = x.trace := by
  obtain ⟨T, rfl⟩ := aut_mat_inner' f
  rw [Algebra.autInner_apply]
  calc
    (T * x * ⅟ (T : M n)).trace = (⅟ (T : M n) * (T * x)).trace := by
      rw [trace_mul_comm]
    _ = ((⅟ (T : M n) * T) * x).trace := by
      rw [Matrix.mul_assoc]
    _ = x.trace := by
      rw [invOf_mul_self, Matrix.one_mul]

alias AlgEquiv.apply_matrix_trace := aut_mat_inner_trace_preserving

end Matrix
