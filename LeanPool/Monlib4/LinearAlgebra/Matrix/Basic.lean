/-
Copyright (c) 2026 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.TensorProduct.Matrix

/-!
# Matrix basics

Basic matrix lemmas used by the monlib4 automorphism-of-matrix-algebras
formalization.
-/

namespace Matrix

open scoped BigOperators Matrix Kronecker

theorem mulVec_stdBasis {R m n : Type _} [Semiring R] [Fintype n]
    (a : Matrix m n R) (i : m) (j : n) :
    (a.mulVec (Pi.basisFun R n j)) i = a i j := by
  classical
  simp_rw [mulVec, dotProduct, Pi.basisFun_apply, Pi.single_apply,
    mul_boole, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem mulVec_eq {R m n : Type _} [CommSemiring R] [Fintype n]
    (a b : Matrix m n R) :
    a = b ↔ ∀ c : n → R, a.mulVec c = b.mulVec c := by
  refine ⟨fun h c => by rw [h], fun h => ?_⟩
  ext i j
  rw [← mulVec_stdBasis a i j, ← mulVec_stdBasis b i j, h _]

/-- A vector is nonzero iff at least one entry is nonzero. -/
theorem vec_ne_zero {R n : Type _} [Semiring R] (a : n → R) :
    (∃ i, a i ≠ 0) ↔ a ≠ 0 := by
  simp_rw [ne_eq, ← Classical.not_forall]
  constructor
  · intro h hzero
    simp_rw [hzero, Pi.zero_apply, imp_true_iff, not_true] at h
  · intro h hentries
    apply h
    ext x
    rw [Pi.zero_apply]
    exact hentries x

theorem smul_mulVec_assoc {R m n : Type _} [Semiring R] [Fintype n]
    (r : R) (x : Matrix m n R) (y : n → R) :
    (r • x) *ᵥ y = r • (x *ᵥ y) := by
  ext i
  simp [mulVec, dotProduct, Finset.mul_sum, mul_assoc]

/-- Expand a square matrix indexed by a product as a sum of Kronecker products of matrix units. -/
theorem kmul_representation {R n₁ n₂ : Type _} [Fintype n₁] [Fintype n₂]
    [DecidableEq n₁] [DecidableEq n₂] [Semiring R]
    (x : Matrix (n₁ × n₂) (n₁ × n₂) R) :
    x =
      ∑ i : n₁, ∑ j : n₁, ∑ k : n₂, ∑ l : n₂,
        x (i, k) (j, l) • Matrix.single i j (1 : R) ⊗ₖ Matrix.single k l (1 : R) := by
  simp_rw [← Matrix.ext_iff, Matrix.sum_apply, Matrix.smul_apply, Matrix.kroneckerMap,
    Matrix.single, Matrix.of_apply, ite_mul, MulZeroClass.zero_mul, one_mul, smul_ite,
    smul_zero, ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Prod.mk.eta, smul_eq_mul, mul_one, forall₂_true_iff]

end Matrix

/-- A linear equivalence of `R^n` gives an invertible matrix. -/
@[reducible]
def LinearEquiv.toInvertibleMatrix {n R : Type _} [CommSemiring R]
    [Fintype n] [DecidableEq n] (x : (n → R) ≃ₗ[R] n → R) :
    Invertible (LinearMap.toMatrix' (x : (n → R) →ₗ[R] n → R)) := by
  refine Invertible.mk
    (LinearMap.toMatrix' (x.symm : (n → R) →ₗ[R] n → R)) ?_ ?_
  · simp only [← LinearMap.toMatrix'_mul, Module.End.mul_eq_comp,
      LinearEquiv.comp_coe, LinearEquiv.self_trans_symm,
      LinearEquiv.refl_toLinearMap, LinearMap.toMatrix'_id]
  · simp only [← LinearMap.toMatrix'_mul, Module.End.mul_eq_comp,
      LinearEquiv.comp_coe, LinearEquiv.symm_trans_self,
      LinearEquiv.refl_toLinearMap, LinearMap.toMatrix'_id]
