/-
Copyright (c) 2026 FredRaj3. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FredRaj3
-/
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.WithDensity

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

/-- A semicircle distribution on `ℝ` with mean `μ` and variance `v`. -/
noncomputable
def semicircleReal (μ : ℝ) (v : ℝ≥0) : Measure ℝ :=
  if v = 0 then Measure.dirac μ else volume.withDensity (semicirclePDF μ v)

lemma semicircleReal_of_var_ne_zero (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    semicircleReal μ v = volume.withDensity (semicirclePDF μ v) := if_neg hv

@[simp]
lemma semicircleReal_zero_var (μ : ℝ) : semicircleReal μ 0 = Measure.dirac μ := if_pos rfl

/-- The semicircle pdf vanishes outside the support `[μ - 2√v, μ + 2√v]`. -/
lemma semicirclePDFReal_eq_zero_of_notMem (μ : ℝ) (v : ℝ≥0) {x : ℝ}
    (hx : x ∉ Icc (μ - 2 * √v) (μ + 2 * √v)) :
    semicirclePDFReal μ v x = 0 := by
  by_contra h
  exact hx (support_semicirclePDFReal_subset μ v h)

/-- The semicircle measure has no atoms when the variance is nonzero. -/
lemma noAtoms_semicircleReal {μ : ℝ} {v : ℝ≥0} (hv : v ≠ 0) :
    NoAtoms (semicircleReal μ v) := by
  rw [semicircleReal_of_var_ne_zero μ hv]; infer_instance

/-- The semicircle measure is absolutely continuous with respect to the Lebesgue measure
when the variance is nonzero. -/
lemma semicircleReal_absolutelyContinuous (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    semicircleReal μ v ≪ (volume : Measure ℝ) := by
  rw [semicircleReal_of_var_ne_zero μ hv]
  exact withDensity_absolutelyContinuous _ _

/-- The Radon-Nikodym derivative of the semicircle measure with respect to the Lebesgue
measure equals the pdf almost everywhere when the variance is nonzero. -/
lemma rnDeriv_semicircleReal (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    (semicircleReal μ v).rnDeriv volume =ᵐ[volume] semicirclePDF μ v := by
  rw [semicircleReal_of_var_ne_zero μ hv]
  exact Measure.rnDeriv_withDensity _ (measurable_semicirclePDF μ v)

end LeanPool.SemicircleLaw
