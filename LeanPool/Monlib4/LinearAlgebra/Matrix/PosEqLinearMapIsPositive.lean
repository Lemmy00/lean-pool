/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import LeanPool.Monlib4.LinearAlgebra.End
import LeanPool.Monlib4.LinearAlgebra.Ips.Pos
import LeanPool.Monlib4.LinearAlgebra.Ips.RankOne
import LeanPool.Monlib4.LinearAlgebra.Matrix.Basic
import LeanPool.Monlib4.Preq.Ites
import LeanPool.Monlib4.Preq.RCLikeLe

/-!
# Positivity of matrices and linear maps

Compatibility wrappers for the part of Monlib's matrix-positive API now covered by Mathlib.
-/

namespace Matrix

variable {𝕜 m n : Type*} [RCLike 𝕜]
  [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

open scoped ComplexConjugate

/-- The adjoint of the linear map associated to a matrix is the map associated to its conjugate
transpose. -/
theorem conjTranspose_eq_adjoint (A : Matrix m n 𝕜) :
    A.conjTranspose.toEuclideanLin = LinearMap.adjoint A.toEuclideanLin :=
  Matrix.toEuclideanLin_conjTranspose_eq_adjoint A

end Matrix

variable {n 𝕜 : Type*} [RCLike 𝕜]

open Matrix
open scoped Matrix ComplexOrder

alias Matrix.posSemidef_star_mul_self := Matrix.posSemidef_conjTranspose_mul_self
alias Matrix.posSemidef_mul_star_self := Matrix.posSemidef_self_mul_conjTranspose

open scoped InnerProductSpace

theorem Matrix.posSemidef_eq_linearMap_positive' [Fintype n] [DecidableEq n]
    (x : Matrix n n 𝕜) :
    x.PosSemidef ↔ x.toEuclideanLin.IsPositive' := by
  rw [LinearMap.isPositive'_iff_isPositive]
  exact Matrix.isPositive_toEuclideanLin_iff.symm

local notation "⟪" x "," y "⟫_𝕜" => @inner 𝕜 _ _ x y

open scoped BigOperators

theorem Matrix.dotProduct_eq_inner {n : Type*} [Fintype n] (x y : n → 𝕜) :
    dotProduct (star x) y = ∑ i : n, ⟪x i, y i⟫_𝕜 := by
  simp [dotProduct, RCLike.inner_apply, mul_comm]

theorem Matrix.isHermitian_self_hMul_conjTranspose {m n : Type*} [Fintype m]
    (A : Matrix m n 𝕜) :
    (Aᴴ * A).IsHermitian :=
  Matrix.isHermitian_conjTranspose_mul_self A

theorem Matrix.trace_star [Fintype n] {A : Matrix n n 𝕜} : star A.trace = Aᴴ.trace := by
  rw [Matrix.trace_conjTranspose]

/-- A positive definite matrix is invertible. -/
@[reducible]
noncomputable def Matrix.PosDef.invertible [Fintype n] [DecidableEq n] {Q : Matrix n n 𝕜}
    (hQ : Q.PosDef) :
    Invertible Q :=
  hQ.isUnit.invertible

theorem Matrix.posSemidef_iff_vecMulVec [Finite n] {x : Matrix n n 𝕜} :
    x.PosSemidef ↔
      ∃ (m : ℕ) (v : Fin m → EuclideanSpace 𝕜 n),
        x = ∑ i : Fin m, vecMulVec (v i : n → 𝕜) (star (v i : n → 𝕜)) := by
  constructor
  · intro h
    rcases (Matrix.posSemidef_iff_eq_sum_vecMulVec (𝕜 := 𝕜) (M := x)).mp h with
      ⟨m, v, hv⟩
    exact ⟨m, fun i => WithLp.toLp 2 (v i), by simpa using hv⟩
  · rintro ⟨m, v, hv⟩
    apply (Matrix.posSemidef_iff_eq_sum_vecMulVec (𝕜 := 𝕜) (M := x)).mpr
    exact ⟨m, fun i => (v i : n → 𝕜), by simpa using hv⟩

theorem vecMulVec_posSemidef [Finite n] (x : n → 𝕜) :
    (vecMulVec x (star x)).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star x

/-- The identity is a positive definite matrix. -/
theorem Matrix.posDefOne [DecidableEq n] : (1 : Matrix n n 𝕜).PosDef :=
  Matrix.PosDef.one

alias Matrix.PosDef.pos_eigenvalues := Matrix.PosDef.eigenvalues_pos

theorem Matrix.PosDef.trace_ne_zero [Fintype n] [Nonempty n]
    {x : Matrix n n 𝕜} (hx : x.PosDef) :
    x.trace ≠ 0 := by
  exact ne_of_gt hx.trace_pos

theorem single.sum_eq_one [Fintype n] [DecidableEq n] (a : 𝕜) :
    ∑ k : n, single k k a = a • 1 := by
  rw [Matrix.one_eq_sum_std_matrix]
  simp_rw [Finset.smul_sum, Matrix.smul_single, smul_eq_mul, mul_one]

theorem single_hMul [Fintype n] [DecidableEq n] (i j k l : n) (a b : 𝕜) :
    single i j a * single k l b =
      ite (j = k) (1 : 𝕜) (0 : 𝕜) • single i l (a * b) := by
  ext p q
  rw [Matrix.single.hMul_stdBasisMatrix i p j k l q a b]
  by_cases hip : i = p <;> by_cases hjk : j = k <;> by_cases hlq : l = q <;>
    simp [Matrix.smul_apply, Matrix.single, smul_eq_mul, hip, hjk, hlq]

theorem Matrix.smul_single' {n R : Type*} [CommSemiring R] [DecidableEq n] (i j : n)
    (c : R) :
    single i j c = c • single i j 1 := by
  rw [smul_single, smul_eq_mul, mul_one]

theorem Matrix.trace_iff' [Fintype n] (x : Matrix n n 𝕜) : x.trace = ∑ i : n, x i i :=
  rfl

theorem Matrix.single.trace [Fintype n] [DecidableEq n] (i j : n) (a : 𝕜) :
    (single i j a).trace = ite (i = j) a 0 := by
  by_cases h : i = j
  · subst h
    simp [Matrix.trace_single_eq_same]
  · simp [Matrix.trace_single_eq_of_ne i j a h, h]

theorem Matrix.single_eq {R n m : Type*} [Semiring R] [DecidableEq n] [DecidableEq m]
    (i : n) (j : m) (a : R) :
    single i j a = fun i' j' => ite (i = i' ∧ j = j') a 0 :=
  rfl

theorem vecMulVec_eq_zero_iff (x : n → 𝕜) : vecMulVec x (star x) = 0 ↔ x = 0 := by
  constructor
  · intro h
    by_contra hx
    exact Matrix.vecMulVec_ne_zero hx (by simpa using hx) h
  · intro h
    simp [h]

lemma norm_ite {α : Type*} [Norm α] (P : Prop) [Decidable P] (a b : α) :
    ‖(ite P a b : α)‖ = (ite P ‖a‖ ‖b‖) := by
  split_ifs <;> rfl

theorem Matrix.PosSemidef.diagonal_iff [DecidableEq n] (x : n → 𝕜) :
    (diagonal x).PosSemidef ↔ ∀ i, 0 ≤ x i :=
  Matrix.posSemidef_diagonal_iff

theorem Matrix.PosDef.diagonal_iff [DecidableEq n] (x : n → 𝕜) :
    (diagonal x).PosDef ↔ ∀ i, 0 < x i :=
  Matrix.posDef_diagonal_iff
