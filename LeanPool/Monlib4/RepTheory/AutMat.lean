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
import LeanPool.Monlib4.LinearAlgebra.Matrix.PiMat
import LeanPool.Monlib4.LinearAlgebra.LmulRmul
import LeanPool.Monlib4.Preq.Set

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

namespace Algebra

/-- Inner automorphism by conjugation with an invertible algebra element. -/
def autInner {R E : Type _} [CommSemiring R] [Semiring E]
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

theorem autInner_apply {R E : Type _} [CommSemiring R] [Semiring E]
    [Algebra R E] (x : E) [Invertible x] (y : E) :
    (autInner x : E ≃ₐ[R] E) y = x * y * ⅟ x :=
  rfl

end Algebra

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

namespace Algebra

/-- Root-name compatibility wrapper for upstream monlib4 inner automorphisms. -/
abbrev autInner {R E : Type _} [CommSemiring R] [Semiring E]
    [Algebra R E] (x : E) [Invertible x] : E ≃ₐ[R] E :=
  Matrix.Algebra.autInner x

theorem autInner_apply {R E : Type _} [CommSemiring R] [Semiring E]
    [Algebra R E] (x : E) [Invertible x] (y : E) :
    (autInner x : E ≃ₐ[R] E) y = x * y * ⅟ x :=
  rfl

theorem autInner_symm_apply {R E : Type _} [CommSemiring R] [Semiring E]
    [Algebra R E] (x : E) [Invertible x] (y : E) :
    (autInner x : E ≃ₐ[R] E).symm y = ⅟ x * y * x :=
  rfl

theorem coe_autInner_eq_rmul_comp_lmul {R E : Type _} [CommSemiring R]
    [Semiring E] [Algebra R E] (x : E) [Invertible x] :
    (Algebra.autInner x : E ≃ₐ[R] E) =
      (_root_.lmul x : E →ₗ[R] E) ∘ (_root_.rmul (⅟ x) : E →ₗ[R] E) := by
  ext a
  simp only [autInner_apply, _root_.lmul_apply, _root_.rmul_apply,
    Function.comp_apply, mul_assoc]

theorem coe_autInner_symm_eq_rmul_comp_lmul {R E : Type _} [CommSemiring R]
    [Semiring E] [Algebra R E] (x : E) [Invertible x] :
    (Algebra.autInner x : E ≃ₐ[R] E).symm =
      (_root_.lmul (⅟ x) : E →ₗ[R] E) ∘ (_root_.rmul x : E →ₗ[R] E) := by
  ext a
  simp only [autInner_symm_apply, _root_.lmul_apply, _root_.rmul_apply,
    Function.comp_apply, mul_assoc]

end Algebra

theorem lmul_comp_rmul_eq_mulLeftRight {R E : Type _} [CommSemiring R]
    [NonUnitalSemiring E] [Module R E] [SMulCommClass R E E] [IsScalarTower R E E]
    (a b : E) :
    (_root_.lmul a : E →ₗ[R] E) ∘ₗ (_root_.rmul b : E →ₗ[R] E) =
      LinearMap.mulLeftRight R (a, b) := by
  ext _
  simp only [LinearMap.mulLeftRight_apply, _root_.lmul_apply, _root_.rmul_apply,
    LinearMap.comp_apply, mul_assoc]

theorem lmul_comp_rmul_eq_coe_mulLeftRight {R E : Type _} [CommSemiring R]
    [NonUnitalSemiring E] [Module R E] [SMulCommClass R E E] [IsScalarTower R E E]
    (a b : E) :
    (_root_.lmul a : E →ₗ[R] E) ∘ (_root_.rmul b : E →ₗ[R] E) =
      LinearMap.mulLeftRight R (a, b) := by
  rw [← lmul_comp_rmul_eq_mulLeftRight]
  rfl

namespace Algebra

theorem autInner_hMul_autInner {R E : Type _} [CommSemiring R] [Semiring E]
    [Algebra R E] (x y : E) [hx : Invertible x] [hy : Invertible y] :
    (Algebra.autInner x : E ≃ₐ[R] E) * Algebra.autInner y =
      @Algebra.autInner _ _ _ _ _ (x * y) (hx.mul hy) := by
  ext
  simp_rw [AlgEquiv.mul_apply, Algebra.autInner_apply, invOf_mul, mul_assoc]

end Algebra

namespace AlgEquiv

/-- An algebra automorphism is inner if it is conjugation by an invertible element. -/
def IsInner {R E : Type*} [CommSemiring R] [Semiring E]
    [Algebra R E] (f : E ≃ₐ[R] E) : Prop :=
  ∃ (a : E) (_ : Invertible a), f = Algebra.autInner a

/-- Product of algebra equivalences, acting componentwise on a product algebra. -/
@[simps]
def prod_map {K R₁ R₂ R₃ R₄ : Type*} [CommSemiring K]
    [Semiring R₁] [Semiring R₂] [Semiring R₃] [Semiring R₄]
    [Algebra K R₁] [Algebra K R₂] [Algebra K R₃] [Algebra K R₄]
    (f : R₁ ≃ₐ[K] R₂) (g : R₃ ≃ₐ[K] R₄) :
    (R₁ × R₃) ≃ₐ[K] (R₂ × R₄) where
  toFun := Prod.map f g
  invFun := Prod.map f.symm g.symm
  left_inv := fun x => by aesop
  right_inv := fun x => by aesop
  map_add' := fun x y => by aesop
  map_mul' := fun x y => by aesop
  commutes' := fun r => by aesop

/-- Dependent-function algebra equivalence induced by pointwise algebra equivalences. -/
@[simps]
def Pi {K ι : Type*} [CommSemiring K] {R : ι → Type*}
    [∀ i, Semiring (R i)] [∀ i, Algebra K (R i)]
    (f : Π i, R i ≃ₐ[K] R i) :
    (Π i, R i) ≃ₐ[K] (Π i, R i) where
  toFun := fun x i => f i (x i)
  invFun := fun x i => (f i).symm (x i)
  left_inv := fun x => funext fun i => (f i).left_inv (x i)
  right_inv := fun x => funext fun i => (f i).right_inv (x i)
  map_add' := fun x y => funext fun i => _root_.map_add _ (x i) (y i)
  map_mul' := fun x y => funext fun i => _root_.map_mul _ (x i) (y i)
  commutes' := fun r => funext fun i => (f i).commutes r

end AlgEquiv

instance Prod.invertible_fst {R₁ R₂ : Type*} [Semiring R₁] [Semiring R₂]
    {a : R₁ × R₂} [ha : Invertible a] :
    Invertible a.1 := by
  use (⅟ a).1
  on_goal 1 => have := ha.invOf_mul_self
  on_goal 2 => have := ha.mul_invOf_self
  all_goals
    rw [Prod.mul_def, Prod.mk_eq_one] at this
    simp_rw [this]

instance Prod.invertible_snd {R₁ R₂ : Type*} [Semiring R₁] [Semiring R₂]
    {a : R₁ × R₂} [ha : Invertible a] :
    Invertible a.2 := by
  use (⅟ a).2
  on_goal 1 => have := ha.invOf_mul_self
  on_goal 2 => have := ha.mul_invOf_self
  all_goals
    rw [Prod.mul_def, Prod.mk_eq_one] at this
    simp_rw [this]

instance Prod.invertible {R₁ R₂ : Type*} [Semiring R₁] [Semiring R₂]
    {a : R₁} {b : R₂} [ha : Invertible a] [hb : Invertible b] :
    Invertible (a, b) :=
  ⟨(⅟ a, ⅟ b), by simp, by simp⟩

instance Pi.invertible_i {ι : Type*} {R : ι → Type*} [∀ i, Semiring (R i)]
    {a : ∀ i, R i} [ha : Invertible a] (i : ι) :
    Invertible (a i) := by
  use (⅟ a) i
  on_goal 1 => have := ha.invOf_mul_self
  on_goal 2 => have := ha.mul_invOf_self
  all_goals
    rw [Pi.mul_def, funext_iff] at this
    simp_rw [this]
    rfl

instance Pi.invertible {ι : Type*} {R : ι → Type*} [∀ i, Semiring (R i)]
    {a : ∀ i, R i} [ha : ∀ i, Invertible (a i)] :
    Invertible a :=
  ⟨fun i => ⅟ (a i), by simp_rw [mul_def, invOf_mul_self]; rfl,
    by simp_rw [mul_def, mul_invOf_self]; rfl⟩

namespace AlgEquiv

theorem prod_isInner_iff_prod_map {K R₁ R₂ : Type*} [CommSemiring K]
    [Semiring R₁] [Semiring R₂] [Algebra K R₁] [Algebra K R₂]
    (f : (R₁ × R₂) ≃ₐ[K] (R₁ × R₂)) :
    AlgEquiv.IsInner f ↔
      ∃ (a : R₁) (_ha : Invertible a) (b : R₂) (_hb : Invertible b),
        f = AlgEquiv.prod_map (Algebra.autInner a) (Algebra.autInner b) := by
  constructor
  · rintro ⟨a, _ha, h⟩
    use a.1, by infer_instance, a.2, by infer_instance
    exact h
  · rintro ⟨a, _ha, b, _hb, h⟩
    use (a, b), by infer_instance
    exact h

theorem pi_isInner_iff_pi_map {K ι : Type*} {R : ι → Type*} [CommSemiring K]
    [∀ i, Semiring (R i)] [∀ i, Algebra K (R i)]
    (f : (∀ i, R i) ≃ₐ[K] (∀ i, R i)) :
    AlgEquiv.IsInner f ↔
      ∃ (a : ∀ i, R i) (_ha : ∀ i, Invertible (a i)),
        f = AlgEquiv.Pi (fun i => Algebra.autInner (a i)) := by
  constructor <;>
    exact fun ⟨a, _ha, h⟩ => ⟨(fun i => a i), by infer_instance, by rw [h]; rfl⟩

theorem pi_isInner_iff_pi_map' {K ι : Type*} {n : ι → Type*} [CommSemiring K]
    [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)]
    (f : PiMat K ι n ≃ₐ[K] PiMat K ι n) :
    AlgEquiv.IsInner f ↔
      ∃ (a : PiMat K ι n) (_ : ∀ i, Invertible (a i)),
        f = AlgEquiv.Pi (fun i => Algebra.autInner (a i)) :=
  AlgEquiv.pi_isInner_iff_pi_map _

end AlgEquiv

/-- A matrix that commutes with every matrix is scalar. -/
theorem Matrix.commutes_with_all_iff {R n : Type _} [CommSemiring R] [Fintype n]
    [DecidableEq n] {x : Matrix n n R} :
    (∀ y : Matrix n n R, Commute y x) ↔ ∃ α : R, x = α • 1 := by
  simp_rw [Commute, SemiconjBy]
  constructor
  · intro h
    by_cases h' : x = 0
    · exact ⟨0, by rw [h', zero_smul]⟩
    simp_rw [← eq_zero, Classical.not_forall] at h'
    obtain ⟨i, _, _⟩ := h'
    have : x = diagonal x.diag := by
      ext k l
      specialize h (single l k 1)
      simp_rw [← Matrix.ext_iff, mul_apply, single, of_apply, boole_mul, mul_boole, ite_and,
        Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ,
        if_true] at h
      specialize h k k
      simp_rw [diagonal, of_apply, Matrix.diag]
      simp_rw [if_true, @eq_comm _ l k] at h
      exact h.symm
    have this1 : ∀ k l : n, x k k = x l l := by
      intro k l
      specialize h (single k l 1)
      simp_rw [← Matrix.ext_iff, mul_apply, single, of_apply, boole_mul, mul_boole, ite_and,
        Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ,
        if_true] at h
      specialize h k l
      simp_rw [if_true] at h
      exact h.symm
    use x i i
    ext k l
    simp_rw [Matrix.smul_apply, one_apply, smul_ite, smul_zero, smul_eq_mul, mul_one]
    nth_rw 1 [this]
    simp_rw [diagonal, diag, of_apply, this1 i k]
  · rintro ⟨α, rfl⟩ y
    simp_rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]

lemma Matrix.center {R n : Type*} [CommSemiring R] [Fintype n] [DecidableEq n] :
    Set.center (Matrix n n R) = Submodule.span R {(1 : Matrix n n R)} := by
  ext x
  rw [Semigroup.mem_center_iff]
  have := @Matrix.commutes_with_all_iff _ _ _ _ _ x
  simp_rw [Commute, SemiconjBy] at this
  rw [this]
  simp [Submodule.mem_span_singleton, eq_comm]

lemma Matrix.prod_center {R n m : Type*} [CommSemiring R] [Fintype n] [Fintype m]
    [DecidableEq n] [DecidableEq m] :
    Set.center (Matrix n n R × Matrix m m R) =
      (Submodule.span R {((1 : Matrix n n R), (0 : Matrix m m R)), (0, 1)}) := by
  simp_rw [Set.center_prod, Matrix.center]
  ext x
  simp only [Set.mem_prod, SetLike.mem_coe, Submodule.mem_span_pair,
    Submodule.mem_span_singleton, Prod.smul_mk, smul_zero, Prod.mk_add_mk, zero_add,
    add_zero]
  nth_rw 3 [← Prod.eta x]
  simp_rw [Prod.ext_iff, exists_and_left, exists_and_right]

lemma Matrix.pi_center {R ι : Type*} [CommSemiring R] {n : ι → Type*}
    [∀ i, Fintype (n i)] :
    Set.center (∀ i : ι, Matrix (n i) (n i) R) =
      { x | ∀ i, x i ∈ Set.center (Matrix (n i) (n i) R) } := by
  classical
  simp_rw [Set.center_pi, Matrix.center]
  ext x
  simp only [Set.mem_pi, Set.mem_univ, SetLike.mem_coe, forall_true_left]
  simp only [Submodule.mem_span_singleton]
  rfl

lemma PiMat.center {R ι : Type*} [CommSemiring R] {n : ι → Type*}
    [∀ i, Fintype (n i)] :
    Set.center (PiMat R ι n) =
      { x | ∀ i, x i ∈ Set.center (Matrix (n i) (n i) R) } :=
  Matrix.pi_center

omit [Fintype n] in
private theorem matrix.one_ne_zero {R : Type _} [Semiring R] [One R] [Zero R]
    [NeZero (1 : R)] [DecidableEq n] [hn : Nonempty n] :
    (1 : Matrix n n R) ≠ 0 := by
  simp_rw [ne_eq, ← Matrix.eq_zero, Matrix.one_apply, ite_eq_right_iff, _root_.one_ne_zero,
    imp_false, Classical.not_forall, Classical.not_not]
  exact ⟨hn.some, hn.some, rfl⟩

theorem Matrix.commutes_with_all_iff_of_ne_zero [DecidableEq n] [Nonempty n]
    {x : Matrix n n 𝕜} (hx : x ≠ 0) :
    (∀ y : Matrix n n 𝕜, Commute y x) ↔ ∃! α : 𝕜ˣ, x = (α : 𝕜) • 1 := by
  simp_rw [Matrix.commutes_with_all_iff]
  refine ⟨fun h => ?_, fun ⟨α, hα, _⟩ => ⟨α, hα⟩⟩
  obtain ⟨α, hα⟩ := h
  have : α ≠ 0 := by
    intro this
    rw [this, zero_smul] at hα
    contradiction
  refine ⟨Units.mk0 α this, hα, fun y hy => ?_⟩
  simp only at hy
  rw [hα, ← sub_eq_zero, ← sub_smul, smul_eq_zero, sub_eq_zero] at hy
  simp_rw [matrix.one_ne_zero, or_false] at hy
  simp_rw [Units.mk0, hy, Units.mk_val]

theorem Matrix.one_ne_zero_iff {𝕜 n : Type*} [DecidableEq n]
    [Zero 𝕜] [One 𝕜] [NeZero (1 : 𝕜)] :
    (1 : Matrix n n 𝕜) ≠ (0 : Matrix n n 𝕜) ↔ Nonempty n := by
  simp_rw [ne_eq, ← Matrix.ext_iff, one_apply, zero_apply, not_forall]
  constructor
  · rintro ⟨x, _, _⟩
    use x
  · intro h
    obtain ⟨i⟩ := h
    use i, i
    simp only [↓reduceIte, one_ne_zero, not_false_iff]

theorem Matrix.one_eq_zero_iff {𝕜 n : Type*} [DecidableEq n]
    [Zero 𝕜] [One 𝕜] [NeZero (1 : 𝕜)] :
    (1 : Matrix n n 𝕜) = (0 : Matrix n n 𝕜) ↔ IsEmpty n := by
  rw [← not_nonempty_iff, ← @one_ne_zero_iff 𝕜 n, not_ne_iff]

theorem Fin.fintwo_of_neZero {i : Fin 2} (hi : i ≠ 0) : i = 1 := by
  revert i
  rw [Fin.forall_fin_two]
  simp only [Fin.isValue, ne_eq, not_true_eq_false, _root_.zero_ne_one, imp_self,
    one_ne_zero, not_false_eq_true, and_self]

/-- Split a nonempty finite dependent product of matrix algebras into its head and tail. -/
def matrixPiFin_algEquiv_PiFinTwo {𝕜 : Type*} [CommSemiring 𝕜]
    {k : ℕ} {n : Fin (k + 1) → Type*}
    [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)] :
    (Π i : Fin (k + 1), Mat 𝕜 (n i)) ≃ₐ[𝕜]
      (Mat 𝕜 (n ⟨0, Nat.zero_lt_succ k⟩) ×
        (Π j : Fin k, Mat 𝕜 (n j.succ))) where
  toFun x := (x 0, fun j => x j.succ)
  invFun x i := if h : i = 0 then by
    rw [h]
    exact x.1
  else by
    rw [← Fin.succ_pred i h]
    exact x.2 (Fin.pred i h)
  left_inv x := by
    refine funext ?h
    simp_rw [Fin.forall_fin_succ]
    simp only [↓reduceDIte, eq_mpr_eq_cast, cast_eq]
    simp only [true_and]
    aesop
  right_inv _ := by rfl
  map_add' _ _ := by rfl
  map_mul' _ _ := by rfl
  commutes' _ := by rfl

theorem matrixPiFin_algEquiv_PiFinTwo_apply {𝕜 : Type*} [CommSemiring 𝕜]
    {k : ℕ} {n : Fin (k + 1) → Type*}
    [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)]
    (x : Π i : Fin (k + 1), Mat 𝕜 (n i)) :
    matrixPiFin_algEquiv_PiFinTwo x = (x 0, fun j : Fin k => x j.succ) :=
  rfl

theorem matrixPiFin_algEquiv_PiFinTwo_symm_apply {𝕜 : Type*} [CommSemiring 𝕜]
    {k : ℕ} {n : Fin (k + 1) → Type*}
    [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)]
    (x : Mat 𝕜 (n 0) × (Π j : Fin k, Mat 𝕜 (n j.succ))) (i : Fin (k + 1)) :
    matrixPiFin_algEquiv_PiFinTwo.symm x i =
      if h : i = 0 then fun a b => x.1 (by rw [← h]; exact a) (by rw [← h]; exact b)
      else by
        rw [← Fin.succ_pred i h]
        exact x.2 (Fin.pred i h) := by
  revert i
  simp_rw [Fin.forall_fin_succ]
  simp only [↓reduceDIte, eq_mpr_eq_cast, cast_eq]
  aesop

/-- Identify a two-term dependent product of matrix algebras with a binary product. -/
def matrixPiFinTwo_algEquiv_prod {𝕜 : Type*} [CommSemiring 𝕜]
    {n : Fin 2 → Type*} [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)] :
    (Π i : Fin 2, Mat 𝕜 (n i)) ≃ₐ[𝕜]
      (Mat 𝕜 (n 0) × Mat 𝕜 (n 1)) where
  toFun x := (x 0, x 1)
  invFun x i := if h : i = 0 then by
    rw [h]
    exact x.1
  else by
    rw [Fin.fintwo_of_neZero h]
    exact x.2
  left_inv x := by
    refine funext ?h
    simp_rw [Fin.forall_fin_two]
    simp only [↓reduceDIte, eq_mpr_eq_cast, cast_eq, Fin.isValue, one_ne_zero, and_self]
  right_inv x := by ext <;> rfl
  map_add' _ _ := by
    simp_rw [Prod.add_def]
    rfl
  map_mul' _ _ := by
    simp_rw [Prod.mul_def]
    rfl
  commutes' _ := by
    simp_rw [Algebra.algebraMap_eq_smul_one, Prod.smul_def]
    rfl

@[simp]
theorem matrixPiFinTwo_algEquiv_prod_apply {𝕜 : Type*} [CommSemiring 𝕜]
    {n : Fin 2 → Type*} [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)]
    (x : Π i : Fin 2, Mat 𝕜 (n i)) :
    matrixPiFinTwo_algEquiv_prod x = (x 0, x 1) :=
  rfl

@[simp]
theorem matrixPiFinTwo_algEquiv_prod_symm_apply {𝕜 : Type*} [CommSemiring 𝕜]
    {n : Fin 2 → Type*} [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)]
    (x : Mat 𝕜 (n 0) × Mat 𝕜 (n 1)) (i : Fin 2) :
    matrixPiFinTwo_algEquiv_prod.symm x i =
      if h : i = 0 then fun a b =>
        x.1 (by rw [← h]; exact a) (by rw [← h]; exact b)
      else fun a b => x.2 (by rw [← Fin.fintwo_of_neZero h]; exact a)
        (by rw [← Fin.fintwo_of_neZero h]; exact b) := by
  revert i
  simp_rw [Fin.forall_fin_two]
  simp only [↓reduceDIte, eq_mpr_eq_cast, cast_eq]
  aesop
