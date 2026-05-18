/-
Copyright (c) 2026 FredRaj3. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FredRaj3
-/
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.HasLaw

/-!
# Semicircle Distributions over `ℝ`

We define the real-valued Wigner semicircle distribution.

## Main definitions

* `semicirclePDFReal`: the function
  `μ v x ↦ (1 / (2 * π * v)) * √(4 * v - (x - μ) ^ 2)`,
  the probability density function of the semicircle distribution with mean `μ`
  and variance `v` (when `v ≠ 0`).
* `semicirclePDF`: the `ℝ≥0∞`-valued pdf,
  `semicirclePDF μ v x = ENNReal.ofReal (semicirclePDFReal μ v x)`.
* `semicircleReal`: the semicircle measure on `ℝ`, parametrized by mean `μ` and
  variance `v`. If `v = 0`, this is `Measure.dirac μ`; otherwise it is the
  measure with density `semicirclePDF μ v` against the Lebesgue measure.
-/

open scoped ENNReal NNReal Real

open MeasureTheory Set

namespace LeanPool.SemicircleLaw

/-- Probability density function of the semicircle distribution with mean `μ` and variance `v`.
Note that the square root of a negative number is defined to be zero. -/
noncomputable
def semicirclePDFReal (μ : ℝ) (v : ℝ≥0) (x : ℝ) : ℝ :=
  1 / (2 * π * v) * √(4 * v - (x - μ) ^ 2)

lemma semicirclePDFReal_def (μ : ℝ) (v : ℝ≥0) :
    semicirclePDFReal μ v =
      fun x ↦ 1 / (2 * π * v) * √(4 * v - (x - μ) ^ 2) := rfl

@[simp]
lemma semicirclePDFReal_zero_var (m : ℝ) : semicirclePDFReal m 0 = 0 := by
  ext x
  simp [semicirclePDFReal]

/-- The semicircle pdf is nonnegative. -/
lemma semicirclePDFReal_nonneg (μ : ℝ) (v : ℝ≥0) (x : ℝ) : 0 ≤ semicirclePDFReal μ v x := by
  rw [semicirclePDFReal]
  positivity

/-- The semicircle pdf is continuous. -/
lemma continuous_semicirclePDFReal (μ : ℝ) (v : ℝ≥0) :
    Continuous (semicirclePDFReal μ v) := by
  rw [semicirclePDFReal_def]
  fun_prop

/-- The semicircle pdf is measurable. -/
@[fun_prop]
lemma measurable_semicirclePDFReal (μ : ℝ) (v : ℝ≥0) :
    Measurable (semicirclePDFReal μ v) :=
  (continuous_semicirclePDFReal μ v).measurable

/-- The semicircle pdf is strongly measurable. -/
@[fun_prop]
lemma stronglyMeasurable_semicirclePDFReal (μ : ℝ) (v : ℝ≥0) :
    StronglyMeasurable (semicirclePDFReal μ v) :=
  (measurable_semicirclePDFReal μ v).stronglyMeasurable

/-- The support of the semicircle pdf is contained in `[μ - 2√v, μ + 2√v]`. -/
lemma support_semicirclePDFReal_subset (μ : ℝ) (v : ℝ≥0) :
    Function.support (semicirclePDFReal μ v) ⊆ Icc (μ - 2 * √v) (μ + 2 * √v) := by
  intro x hx
  by_contra hxI
  apply hx
  unfold semicirclePDFReal
  have h_abs : 2 * √v ≤ |x - μ| := by
    rcases not_and_or.mp (mt mem_Icc.mpr hxI) with h | h
    · push Not at h
      have : 2 * √v ≤ μ - x := by linarith
      have h2 : 0 ≤ μ - x := by
        have : (0 : ℝ) ≤ √v := Real.sqrt_nonneg _
        linarith
      rw [show |x - μ| = μ - x by rw [abs_sub_comm]; exact abs_of_nonneg h2]
      exact this
    · push Not at h
      have : 2 * √v ≤ x - μ := by linarith
      have h2 : 0 ≤ x - μ := by
        have : (0 : ℝ) ≤ √v := Real.sqrt_nonneg _
        linarith
      rw [abs_of_nonneg h2]
      exact this
  have h_sq : 4 * (v : ℝ) ≤ (x - μ) ^ 2 := by
    have h_sq_abs : (2 * √v) ^ 2 ≤ |x - μ| ^ 2 :=
      pow_le_pow_left₀ (by positivity) h_abs 2
    rw [mul_pow, Real.sq_sqrt (NNReal.coe_nonneg v), sq_abs] at h_sq_abs
    linarith
  have h_nonpos : 4 * (v : ℝ) - (x - μ) ^ 2 ≤ 0 := by linarith
  rw [Real.sqrt_eq_zero_of_nonpos h_nonpos, mul_zero]

/-- The semicircle pdf is integrable. -/
@[fun_prop]
lemma integrable_semicirclePDFReal (μ : ℝ) (v : ℝ≥0) :
    Integrable (semicirclePDFReal μ v) := by
  have h_cont : Continuous (semicirclePDFReal μ v) := continuous_semicirclePDFReal μ v
  have h_compact : IsCompact (Icc (μ - 2 * √v) (μ + 2 * √v)) := isCompact_Icc
  have h_int_on : IntegrableOn (semicirclePDFReal μ v) (Icc (μ - 2 * √v) (μ + 2 * √v)) :=
    h_cont.continuousOn.integrableOn_compact h_compact
  exact (integrableOn_iff_integrable_of_support_subset
    (support_semicirclePDFReal_subset μ v)).mp h_int_on

lemma sqrt_semicircle_affine (v : ℝ≥0) {y : ℝ} (hy : y ∈ Icc (-1 : ℝ) 1) :
    √(4 * (v : ℝ) - (2 * √(v : ℝ) * y) ^ 2) =
      2 * √(v : ℝ) * √(1 - y ^ 2) := by
  have hv_nonneg : 0 ≤ (v : ℝ) := NNReal.coe_nonneg v
  have hy_abs : |y| ≤ 1 := abs_le.mpr ⟨by linarith [hy.1], hy.2⟩
  have hy_sq : y ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one y).2 hy_abs
  calc
    √(4 * (v : ℝ) - (2 * √(v : ℝ) * y) ^ 2)
        = √((4 * (v : ℝ)) * (1 - y ^ 2)) := by
          congr 1
          nlinarith [Real.sq_sqrt hv_nonneg]
    _ = √(4 * (v : ℝ)) * √(1 - y ^ 2) := by
          rw [Real.sqrt_mul (mul_nonneg (by norm_num) hv_nonneg) (1 - y ^ 2)]
    _ = 2 * √(v : ℝ) * √(1 - y ^ 2) := by
          rw [Real.sqrt_mul (by norm_num : 0 ≤ (4 : ℝ)) (v : ℝ)]
          have h_sqrt_four : √(4 : ℝ) = 2 := by
            rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
            norm_num
          rw [h_sqrt_four]

/-- The unnormalized semicircle kernel has integral `2 * π * v` over its support interval. -/
lemma integral_sqrt_semicircle_interval (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    ∫ x in μ - 2 * √(v : ℝ)..μ + 2 * √(v : ℝ),
      √(4 * (v : ℝ) - (x - μ) ^ 2) = 2 * π * (v : ℝ) := by
  let c : ℝ := 2 * √(v : ℝ)
  have hv_pos : 0 < (v : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  have hv_nonneg : 0 ≤ (v : ℝ) := hv_pos.le
  have hc_pos : 0 < c := by
    dsimp [c]
    positivity
  have h_change :=
    intervalIntegral.smul_integral_comp_mul_add
      (f := fun x ↦ √(4 * (v : ℝ) - (x - μ) ^ 2)) (a := (-1 : ℝ)) (b := 1)
      (c := c) (d := μ)
  calc
    ∫ x in μ - 2 * √(v : ℝ)..μ + 2 * √(v : ℝ),
      √(4 * (v : ℝ) - (x - μ) ^ 2)
        = c * ∫ y in (-1 : ℝ)..1, √(4 * (v : ℝ) - (c * y + μ - μ) ^ 2) := by
          simpa [c, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm]
            using h_change.symm
    _ = c * ∫ y in (-1 : ℝ)..1, c * √(1 - y ^ 2) := by
          congr 1
          apply intervalIntegral.integral_congr
          intro y hy
          have hy' : y ∈ Icc (-1 : ℝ) 1 := by simpa using hy
          simp [c, sqrt_semicircle_affine v hy']
    _ = c * (c * ∫ y in (-1 : ℝ)..1, √(1 - y ^ 2)) := by
          rw [intervalIntegral.integral_const_mul]
    _ = 2 * π * (v : ℝ) := by
          rw [integral_sqrt_one_sub_sq]
          dsimp [c]
          calc
            2 * √(v : ℝ) * (2 * √(v : ℝ) * (π / 2)) =
                2 * π * (√(v : ℝ)) ^ 2 := by ring
            _ = 2 * π * (v : ℝ) := by rw [Real.sq_sqrt hv_nonneg]

/-- The semicircle distribution pdf integrates to 1 when the variance is nonzero. -/
lemma integral_semicirclePDFReal_eq_one (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    ∫ x, semicirclePDFReal μ v x = 1 := by
  have hv_pos : 0 < (v : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  have h_support :
      ∫ x in Icc (μ - 2 * √(v : ℝ)) (μ + 2 * √(v : ℝ)), semicirclePDFReal μ v x
        = ∫ x, semicirclePDFReal μ v x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx ↦ by
        by_contra h
        exact hx (support_semicirclePDFReal_subset μ v h))
  have h_interval :
      ∫ x in Icc (μ - 2 * √(v : ℝ)) (μ + 2 * √(v : ℝ)),
          √(4 * (v : ℝ) - (x - μ) ^ 2)
        = ∫ x in μ - 2 * √(v : ℝ)..μ + 2 * √(v : ℝ),
          √(4 * (v : ℝ) - (x - μ) ^ 2) := by
    have hle : μ - 2 * √(v : ℝ) ≤ μ + 2 * √(v : ℝ) := by
      linarith [Real.sqrt_nonneg (v : ℝ)]
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle]
  rw [← h_support]
  simp only [semicirclePDFReal]
  rw [integral_const_mul, h_interval, integral_sqrt_semicircle_interval μ hv]
  field_simp [(show (v : ℝ) ≠ 0 by positivity), Real.pi_ne_zero]

/-- The semicircle distribution pdf has total mass 1 when the variance is nonzero. -/
lemma lintegral_semicirclePDFReal_eq_one (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    ∫⁻ x, ENNReal.ofReal (semicirclePDFReal μ v x) = 1 := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_semicirclePDFReal μ v)
    (ae_of_all _ (semicirclePDFReal_nonneg μ v))]
  rw [integral_semicirclePDFReal_eq_one μ hv, ENNReal.ofReal_one]

/-- The `ℝ≥0∞`-valued pdf of a semicircle distribution on `ℝ` with mean `μ` and variance `v`. -/
noncomputable
def semicirclePDF (μ : ℝ) (v : ℝ≥0) (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (semicirclePDFReal μ v x)

lemma semicirclePDF_def (μ : ℝ) (v : ℝ≥0) :
    semicirclePDF μ v = fun x ↦ ENNReal.ofReal (semicirclePDFReal μ v x) := rfl

@[simp]
lemma semicirclePDF_zero_var (μ : ℝ) : semicirclePDF μ 0 = 0 := by
  ext
  simp [semicirclePDF]

@[simp]
lemma toReal_semicirclePDF {μ : ℝ} {v : ℝ≥0} (x : ℝ) :
    (semicirclePDF μ v x).toReal = semicirclePDFReal μ v x := by
  rw [semicirclePDF, ENNReal.toReal_ofReal (semicirclePDFReal_nonneg μ v x)]

lemma semicirclePDF_lt_top {μ : ℝ} {v : ℝ≥0} {x : ℝ} : semicirclePDF μ v x < ∞ := by
  simp [semicirclePDF]

lemma semicirclePDF_ne_top {μ : ℝ} {v : ℝ≥0} {x : ℝ} : semicirclePDF μ v x ≠ ∞ :=
  semicirclePDF_lt_top.ne

@[measurability, fun_prop]
lemma measurable_semicirclePDF (μ : ℝ) (v : ℝ≥0) : Measurable (semicirclePDF μ v) :=
  (measurable_semicirclePDFReal _ _).ennreal_ofReal

@[simp]
lemma lintegral_semicirclePDF_eq_one (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    ∫⁻ x, semicirclePDF μ v x = 1 :=
  lintegral_semicirclePDFReal_eq_one μ hv

/-- A semicircle distribution on `ℝ` with mean `μ` and variance `v`. -/
noncomputable
def semicircleReal (μ : ℝ) (v : ℝ≥0) : Measure ℝ :=
  if v = 0 then Measure.dirac μ else volume.withDensity (semicirclePDF μ v)

lemma semicircleReal_of_var_ne_zero (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    semicircleReal μ v = volume.withDensity (semicirclePDF μ v) := if_neg hv

@[simp]
lemma semicircleReal_zero_var (μ : ℝ) : semicircleReal μ 0 = Measure.dirac μ := if_pos rfl

instance instIsProbabilityMeasureSemicircleReal (μ : ℝ) (v : ℝ≥0) :
    IsProbabilityMeasure (semicircleReal μ v) where
  measure_univ := by by_cases h : v = 0 <;> simp [semicircleReal_of_var_ne_zero, h]

/-- The semicircle pdf vanishes outside the support `[μ - 2√v, μ + 2√v]`. -/
lemma semicirclePDFReal_eq_zero_of_notMem (μ : ℝ) (v : ℝ≥0) {x : ℝ}
    (hx : x ∉ Icc (μ - 2 * √v) (μ + 2 * √v)) :
    semicirclePDFReal μ v x = 0 := by
  by_contra h
  exact hx (support_semicirclePDFReal_subset μ v h)

/-- Translating the input translates the mean in the opposite direction. -/
lemma semicirclePDFReal_sub {μ : ℝ} {v : ℝ≥0} (x y : ℝ) :
    semicirclePDFReal μ v (x - y) = semicirclePDFReal (μ + y) v x := by
  simp only [semicirclePDFReal]
  rw [sub_add_eq_sub_sub_swap]

/-- Translating the input translates the mean in the opposite direction. -/
lemma semicirclePDFReal_add {μ : ℝ} {v : ℝ≥0} (x y : ℝ) :
    semicirclePDFReal μ v (x + y) = semicirclePDFReal (μ - y) v x := by
  rw [sub_eq_add_neg, ← semicirclePDFReal_sub, sub_eq_add_neg, neg_neg]

/-- Scaling the input rescales both the mean and variance parameters of the density. -/
lemma semicirclePDFReal_inv_mul {μ : ℝ} {v : ℝ≥0} {c : ℝ} (hc : c ≠ 0) (x : ℝ) :
    semicirclePDFReal μ v (c⁻¹ * x)
      = |c| * semicirclePDFReal (c * μ) (.mk (c ^ 2) (sq_nonneg _) * v) x := by
  rw [semicirclePDFReal, semicirclePDFReal]
  simp only [one_div, NNReal.coe_mul, NNReal.coe_mk]
  have h_arg :
      c⁻¹ * x - μ = c⁻¹ * (x - c * μ) := by
    rw [mul_sub, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  have h_sqrt₁ :
      √(4 * (v : ℝ) - (c⁻¹ * x - μ) ^ 2)
        = √(4 * (v : ℝ) - (c⁻¹) ^ 2 * (x - c * μ) ^ 2) := by
    rw [h_arg]
    ring_nf
  have h_sqrt₂ :
      √(4 * (v : ℝ) - (c⁻¹) ^ 2 * (x - c * μ) ^ 2)
        = |c⁻¹| * √(4 * (c ^ 2 * v) - (x - c * μ) ^ 2) := by
    have h_factor :
        4 * (v : ℝ) - (c⁻¹) ^ 2 * (x - c * μ) ^ 2
          = (c⁻¹) ^ 2 * (4 * (c ^ 2 * v) - (x - c * μ) ^ 2) := by
      field_simp [hc]
    rw [h_factor, ← sq_abs, Real.sqrt_mul (sq_nonneg _) _, Real.sqrt_sq (abs_nonneg _)]
  rw [h_sqrt₁, h_sqrt₂]
  have h_abs_inv : |c⁻¹| = |c|⁻¹ := abs_inv c
  rw [h_abs_inv]
  field_simp [hc, abs_ne_zero.mpr hc]
  rw [sq_abs]

/-- Scaling the input rescales both the mean and variance parameters of the density. -/
lemma semicirclePDFReal_mul {μ : ℝ} {v : ℝ≥0} {c : ℝ} (hc : c ≠ 0) (x : ℝ) :
    semicirclePDFReal μ v (c * x)
      = |c⁻¹| * semicirclePDFReal (c⁻¹ * μ)
          (.mk ((c ^ 2)⁻¹) (inv_nonneg.mpr (sq_nonneg _)) * v) x := by
  conv_lhs => rw [← inv_inv c, semicirclePDFReal_inv_mul (inv_ne_zero hc)]
  simp

/-- The `ℝ≥0∞`-valued semicircle density is nonnegative. -/
lemma semicirclePDF_nonneg (μ : ℝ) (v : ℝ≥0) (x : ℝ) : 0 ≤ semicirclePDF μ v x := by
  simp [semicirclePDF]

/-- The support of the `ℝ≥0∞`-valued semicircle density is contained in its support interval. -/
lemma support_semicirclePDF_subset (μ : ℝ) (v : ℝ≥0) :
    Function.support (semicirclePDF μ v) ⊆ Icc (μ - 2 * √v) (μ + 2 * √v) := by
  intro x hx
  exact support_semicirclePDFReal_subset μ v fun hzero ↦ hx (by simp [semicirclePDF, hzero])

/-- The `ℝ≥0∞`-valued semicircle density vanishes outside its support interval. -/
lemma semicirclePDF_eq_zero_of_notMem (μ : ℝ) (v : ℝ≥0) {x : ℝ}
    (hx : x ∉ Icc (μ - 2 * √v) (μ + 2 * √v)) :
    semicirclePDF μ v x = 0 := by
  simp [semicirclePDF, semicirclePDFReal_eq_zero_of_notMem μ v hx]

/-- The semicircle measure has no atoms when the variance is nonzero. -/
lemma noAtoms_semicircleReal {μ : ℝ} {v : ℝ≥0} (hv : v ≠ 0) :
    NoAtoms (semicircleReal μ v) := by
  rw [semicircleReal_of_var_ne_zero μ hv]; infer_instance

/-- The semicircle measure of a set is the set integral of the density when `v ≠ 0`. -/
lemma semicircleReal_apply (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (s : Set ℝ) :
    semicircleReal μ v s = ∫⁻ x in s, semicirclePDF μ v x := by
  rw [semicircleReal_of_var_ne_zero _ hv, withDensity_apply' _ s]

/-- The semicircle measure of a set as a real integral of the density when `v ≠ 0`. -/
lemma semicircleReal_apply_eq_integral (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (s : Set ℝ) :
    semicircleReal μ v s = ENNReal.ofReal (∫ x in s, semicirclePDFReal μ v x) := by
  rw [semicircleReal_apply _ hv s, ofReal_integral_eq_lintegral_ofReal]
  · rfl
  · exact (integrable_semicirclePDFReal _ _).restrict
  · exact ae_of_all _ (semicirclePDFReal_nonneg _ _)

/-- The semicircle measure is absolutely continuous with respect to the Lebesgue measure
when the variance is nonzero. -/
lemma semicircleReal_absolutelyContinuous (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    semicircleReal μ v ≪ (volume : Measure ℝ) := by
  rw [semicircleReal_of_var_ne_zero μ hv]
  exact withDensity_absolutelyContinuous _ _

/-- The Radon-Nikodym derivative of the semicircle measure with respect to the Lebesgue
measure equals the pdf almost everywhere when the variance is nonzero. -/
lemma rnDeriv_semicircleReal (μ : ℝ) (v : ℝ≥0) :
    (semicircleReal μ v).rnDeriv volume =ᵐ[volume] semicirclePDF μ v := by
  by_cases hv : v = 0
  · simp only [hv, semicircleReal_zero_var, semicirclePDF_zero_var]
    refine (Measure.eq_rnDeriv measurable_zero (mutuallySingular_dirac μ volume) ?_).symm
    rw [withDensity_zero, add_zero]
  · rw [semicircleReal_of_var_ne_zero μ hv]
    exact Measure.rnDeriv_withDensity _ (measurable_semicirclePDF μ v)

/-- Integrating against a non-degenerate semicircle measure is integrating against its density. -/
lemma integral_semicircleReal_eq_integral_smul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {μ : ℝ} {v : ℝ≥0} {f : ℝ → E} (hv : v ≠ 0) :
    ∫ x, f x ∂semicircleReal μ v = ∫ x, semicirclePDFReal μ v x • f x := by
  simp [semicircleReal, hv,
    integral_withDensity_eq_integral_toReal_smul (measurable_semicirclePDF _ _)
      (ae_of_all _ fun _ ↦ semicirclePDF_lt_top)]

variable {μ : ℝ} {v : ℝ≥0}

lemma _root_.MeasurableEmbedding.semicircleReal_comap_apply (hv : v ≠ 0)
    {f : ℝ → ℝ} (hf : MeasurableEmbedding f) {f' : ℝ → ℝ}
    (h_deriv : ∀ x, HasDerivAt f (f' x) x) {s : Set ℝ} (hs : MeasurableSet s) :
    (semicircleReal μ v).comap f s
      = ENNReal.ofReal (∫ x in s, |f' x| * semicirclePDFReal μ v (f x)) := by
  rw [semicircleReal_of_var_ne_zero _ hv, semicirclePDF_def]
  exact hf.withDensity_ofReal_comap_apply_eq_integral_abs_deriv_mul' hs h_deriv
    (ae_of_all _ (semicirclePDFReal_nonneg _ _)) (integrable_semicirclePDFReal _ _)

lemma _root_.MeasurableEquiv.semicircleReal_map_symm_apply (hv : v ≠ 0) (f : ℝ ≃ᵐ ℝ)
    {f' : ℝ → ℝ} (h_deriv : ∀ x, HasDerivAt f (f' x) x) {s : Set ℝ}
    (hs : MeasurableSet s) :
    (semicircleReal μ v).map f.symm s
      = ENNReal.ofReal (∫ x in s, |f' x| * semicirclePDFReal μ v (f x)) := by
  rw [semicircleReal_of_var_ne_zero _ hv, semicirclePDF_def]
  exact f.withDensity_ofReal_map_symm_apply_eq_integral_abs_deriv_mul' hs h_deriv
    (ae_of_all _ (semicirclePDFReal_nonneg _ _)) (integrable_semicirclePDFReal _ _)

/-- The map of a semicircle distribution by addition of a constant is semicircular. -/
lemma semicircleReal_map_add_const (y : ℝ) :
    (semicircleReal μ v).map (· + y) = semicircleReal (μ + y) v := by
  by_cases hv : v = 0
  · simp [hv, semicircleReal_zero_var]
  let e : ℝ ≃ᵐ ℝ := (Homeomorph.addRight y).symm.toMeasurableEquiv
  have he' : ∀ x, HasDerivAt e ((fun _ ↦ 1) x) x := fun _ ↦ (hasDerivAt_id _).sub_const y
  change (semicircleReal μ v).map e.symm = semicircleReal (μ + y) v
  ext s hs
  rw [MeasurableEquiv.semicircleReal_map_symm_apply hv e he' hs]
  simp only [abs_one, one_mul]
  rw [semicircleReal_apply_eq_integral _ hv s]
  simp [e, semicirclePDFReal_sub _ y, Homeomorph.addRight, ← sub_eq_add_neg]

/-- The map of a semicircle distribution by addition of a constant is semicircular. -/
lemma semicircleReal_map_const_add (y : ℝ) :
    (semicircleReal μ v).map (y + ·) = semicircleReal (μ + y) v := by
  simp_rw [add_comm y]
  exact semicircleReal_map_add_const y

/-- The map of a semicircle distribution by multiplication by a constant is semicircular. -/
lemma semicircleReal_map_const_mul (c : ℝ) :
    (semicircleReal μ v).map (c * ·) =
      semicircleReal (c * μ) (.mk (c ^ 2) (sq_nonneg _) * v) := by
  by_cases hv : v = 0
  · simp [hv, mul_zero, semicircleReal_zero_var]
  by_cases hc : c = 0
  · simp [hc, zero_mul]
  let e : ℝ ≃ᵐ ℝ := (Homeomorph.mulLeft₀ c hc).symm.toMeasurableEquiv
  have he' : ∀ x, HasDerivAt e ((fun _ ↦ c⁻¹) x) x := by
    suffices ∀ x, HasDerivAt (fun x ↦ c⁻¹ * x) (c⁻¹ * 1) x by
      rwa [mul_one] at this
    exact fun _ ↦ HasDerivAt.const_mul _ (hasDerivAt_id _)
  change (semicircleReal μ v).map e.symm =
    semicircleReal (c * μ) (.mk (c ^ 2) (sq_nonneg _) * v)
  ext s hs
  rw [MeasurableEquiv.semicircleReal_map_symm_apply hv e he' hs,
    semicircleReal_apply_eq_integral _ _ s]
  swap
  · simp only [ne_eq, mul_eq_zero, hv, or_false]
    rw [← NNReal.coe_inj]
    simp [hc]
  simp only [e, Homeomorph.mulLeft₀, Equiv.mulLeft₀_symm_apply,
    Homeomorph.toMeasurableEquiv_coe, Homeomorph.homeomorph_mk_coe_symm,
    semicirclePDFReal_inv_mul hc]
  congr with x
  suffices |c⁻¹| * |c| = 1 by rw [← mul_assoc, this, one_mul]
  rw [abs_inv, inv_mul_cancel₀]
  rwa [ne_eq, abs_eq_zero]

/-- The map of a semicircle distribution by multiplication by a constant is semicircular. -/
lemma semicircleReal_map_mul_const (c : ℝ) :
    (semicircleReal μ v).map (· * c) =
      semicircleReal (c * μ) (.mk (c ^ 2) (sq_nonneg _) * v) := by
  simp_rw [mul_comm _ c]
  exact semicircleReal_map_const_mul c

lemma semicircleReal_map_neg :
    (semicircleReal μ v).map (fun x ↦ -x) = semicircleReal (-μ) v := by
  simpa using semicircleReal_map_const_mul (μ := μ) (v := v) (-1)

/-- The map of a semicircle distribution by division by a constant is semicircular. -/
lemma semicircleReal_map_div_const (c : ℝ) :
    (semicircleReal μ v).map (· / c) =
      semicircleReal (μ / c) (v / .mk (c ^ 2) (sq_nonneg _)) := by
  simp_rw [div_eq_mul_inv]
  convert semicircleReal_map_mul_const (μ := μ) (v := v) c⁻¹ using 2 <;> rw [mul_comm]
  ext
  simp

lemma semicircleReal_map_sub_const (y : ℝ) :
    (semicircleReal μ v).map (· - y) = semicircleReal (μ - y) v := by
  simp_rw [sub_eq_add_neg, semicircleReal_map_add_const]

lemma semicircleReal_map_const_sub (y : ℝ) :
    (semicircleReal μ v).map (y - ·) = semicircleReal (y - μ) v := by
  simp_rw [sub_eq_add_neg]
  have : (fun x ↦ y + -x) = (fun x ↦ y + x) ∘ fun x ↦ -x := by ext; simp
  rw [this, ← Measure.map_map (by fun_prop) (by fun_prop), semicircleReal_map_neg,
    semicircleReal_map_const_add, add_comm]

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : Ω → ℝ}

/-- If `X` has semicircular law with mean `μ` and variance `v`, then `X + y` has
semicircular law with mean `μ + y` and variance `v`. -/
lemma semicircleReal_add_const (hX : ProbabilityTheory.HasLaw X (semicircleReal μ v) P)
    (y : ℝ) :
    ProbabilityTheory.HasLaw (fun ω ↦ X ω + y) (semicircleReal (μ + y) v) P :=
  ProbabilityTheory.HasLaw.comp ⟨by fun_prop, semicircleReal_map_add_const y⟩ hX

/-- If `X` has semicircular law with mean `μ` and variance `v`, then `y + X` has
semicircular law with mean `μ + y` and variance `v`. -/
lemma semicircleReal_const_add (hX : ProbabilityTheory.HasLaw X (semicircleReal μ v) P)
    (y : ℝ) :
    ProbabilityTheory.HasLaw (fun ω ↦ y + X ω) (semicircleReal (μ + y) v) P :=
  ProbabilityTheory.HasLaw.comp ⟨by fun_prop, semicircleReal_map_const_add y⟩ hX

/-- If `X` has semicircular law with mean `μ` and variance `v`, then `X - y` has
semicircular law with mean `μ - y` and variance `v`. -/
lemma semicircleReal_sub_const (hX : ProbabilityTheory.HasLaw X (semicircleReal μ v) P)
    (y : ℝ) :
    ProbabilityTheory.HasLaw (fun ω ↦ X ω - y) (semicircleReal (μ - y) v) P :=
  ProbabilityTheory.HasLaw.comp ⟨by fun_prop, semicircleReal_map_sub_const y⟩ hX

/-- If `X` has semicircular law with mean `μ` and variance `v`, then `c * X` has
semicircular law with mean `c * μ` and variance `c ^ 2 * v`. -/
lemma semicircleReal_const_mul (hX : ProbabilityTheory.HasLaw X (semicircleReal μ v) P)
    (c : ℝ) :
    ProbabilityTheory.HasLaw (fun ω ↦ c * X ω)
      (semicircleReal (c * μ) (.mk (c ^ 2) (sq_nonneg _) * v)) P :=
  ProbabilityTheory.HasLaw.comp ⟨by fun_prop, semicircleReal_map_const_mul c⟩ hX

/-- If `X` has semicircular law with mean `μ` and variance `v`, then `X * c` has
semicircular law with mean `c * μ` and variance `c ^ 2 * v`. -/
lemma semicircleReal_mul_const (hX : ProbabilityTheory.HasLaw X (semicircleReal μ v) P)
    (c : ℝ) :
    ProbabilityTheory.HasLaw (fun ω ↦ X ω * c)
      (semicircleReal (c * μ) (.mk (c ^ 2) (sq_nonneg _) * v)) P :=
  ProbabilityTheory.HasLaw.comp ⟨by fun_prop, semicircleReal_map_mul_const c⟩ hX

lemma semicircleReal_neg (hX : ProbabilityTheory.HasLaw X (semicircleReal μ v) P) :
    ProbabilityTheory.HasLaw (-X) (semicircleReal (-μ) v) P := by
  rw [Pi.neg_def, ← Function.comp_def]
  exact ProbabilityTheory.HasLaw.comp ⟨by fun_prop, semicircleReal_map_neg⟩ hX

/-- If `X` has semicircular law with mean `μ` and variance `v`, then `X / c` has
semicircular law with mean `μ / c` and variance `v / c ^ 2`. -/
lemma semicircleReal_div_const (hX : ProbabilityTheory.HasLaw X (semicircleReal μ v) P)
    (c : ℝ) :
    ProbabilityTheory.HasLaw (fun ω ↦ X ω / c)
      (semicircleReal (μ / c) (v / .mk (c ^ 2) (sq_nonneg _))) P :=
  ProbabilityTheory.HasLaw.comp ⟨by fun_prop, semicircleReal_map_div_const c⟩ hX

lemma semicircleReal_const_sub (hX : ProbabilityTheory.HasLaw X (semicircleReal μ v) P)
    (y : ℝ) :
    ProbabilityTheory.HasLaw (fun ω ↦ y - X ω) (semicircleReal (y - μ) v) P :=
  ProbabilityTheory.HasLaw.comp ⟨by fun_prop, semicircleReal_map_const_sub y⟩ hX

variable {μ : ℝ} {v : ℝ≥0}

/-- The identity is almost surely bounded under a semicircle distribution. -/
lemma ae_abs_id_le_semicircleReal :
    ∀ᵐ x ∂semicircleReal μ v, |id x| ≤ |μ| + 2 * √(v : ℝ) := by
  by_cases hv : v = 0
  · simp [hv, semicircleReal_zero_var]
  rw [semicircleReal_of_var_ne_zero μ hv]
  rw [ae_withDensity_iff (measurable_semicirclePDF μ v)]
  filter_upwards [] with x hx
  have hxI := support_semicirclePDF_subset μ v hx
  have hx_abs_sub : |x - μ| ≤ 2 * √(v : ℝ) := by
    rw [abs_sub_le_iff]
    constructor <;> linarith [hxI.1, hxI.2]
  calc
    |id x| = |x| := rfl
    _ = |(x - μ) + μ| := by ring_nf
    _ ≤ |x - μ| + |μ| := abs_add_le _ _
    _ ≤ 2 * √(v : ℝ) + |μ| := by linarith
    _ = |μ| + 2 * √(v : ℝ) := by ring

/-- All finite moments of a real semicircle distribution are finite. -/
lemma memLp_id_semicircleReal (p : ℝ≥0) : MemLp id p (semicircleReal μ v) := by
  have htop : MemLp id ∞ (semicircleReal μ v) :=
    memLp_top_of_bound (by fun_prop) (|μ| + 2 * √(v : ℝ)) ae_abs_id_le_semicircleReal
  exact htop.mono_exponent (by simp)

/-- All finite moments of a real semicircle distribution are finite. -/
lemma memLp_id_semicircleReal' (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp id p (semicircleReal μ v) := by
  lift p to ℝ≥0 using hp
  exact memLp_id_semicircleReal p

end LeanPool.SemicircleLaw
