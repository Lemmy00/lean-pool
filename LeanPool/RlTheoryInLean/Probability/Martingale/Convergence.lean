/-
Copyright (c) 2026 Shangtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shangtong Zhang
-/
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.Probability.Martingale.Upcrossing
import Mathlib.Probability.Martingale.Convergence
import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

open TopologicalSpace Filter MeasureTheory.Filtration Finset NNReal
open scoped MeasureTheory ProbabilityTheory Topology

namespace MeasureTheory

variable {Ω : Type*} [m₀ : MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {ℱ : Filtration ℕ m₀}
variable {f : ℕ → Ω → ℝ}

omit [IsProbabilityMeasure μ] in
theorem ae_summable_of_summable_integral
  {f : ℕ → Ω → ℝ}
  (hf : ∀ i, Integrable (f i) μ)
  (hfm : ∀ i, Measurable (f i))
  (hfnonneg : ∀ n, 0 ≤ᵐ[μ] f n)
  (hfsum : Summable (fun n => ∫ ω, f n ω ∂μ)) :
  ∀ᵐ ω ∂μ, Summable (fun n => f n ω) := by
  let g := fun n ω => ENNReal.ofReal (f n ω)
  have hg : ∀ n, AEMeasurable (g n) μ := fun n =>
    ENNReal.measurable_ofReal.comp_aemeasurable (hf n).aemeasurable
  have hlt : ∀ᵐ ω ∂μ, ∑' n, g n ω < ⊤ := by
    let g' : ℕ → ℝ≥0 := fun n => (∫ ω, f n ω ∂μ).toNNReal
    refine ae_lt_top (Measurable.ennreal_tsum fun n =>
      ENNReal.measurable_ofReal.comp (hfm n)) ?_
    rw [lintegral_tsum hg]
    have hsumg' : Summable g' := hfsum.toNNReal
    have hne := ENNReal.tsum_coe_ne_top_iff_summable.mpr hsumg'
    by_contra h
    refine hne ?_
    refine Eq.symm (h.symm.trans (tsum_congr fun n => ?_))
    simp only [g, g']
    rw [integral_eq_lintegral_of_nonneg_ae (hfnonneg n) (hf n).aestronglyMeasurable,
      ENNReal.ofNNReal_toNNReal,
      ENNReal.ofReal_toReal (ne_top_of_lt (hf n).lintegral_lt_top)]
  apply Eventually.mono (hlt.and (ae_all_iff.mpr hfnonneg))
  intro ω hω
  simp only [g] at hω
  refine ⟨(∑' n, ENNReal.ofReal (f n ω)).toReal, ?_⟩
  refine (hasSum_iff_tendsto_nat_of_nonneg hω.2 _).mpr ?_
  have htendsto := ENNReal.tendsto_nat_tsum fun n => ENNReal.ofReal (f n ω)
  refine (Tendsto.congr ?_) ((ENNReal.tendsto_toReal hω.1.ne_top).comp htendsto)
  intro n
  simp only [Function.comp_apply]
  rw [ENNReal.toReal_sum (fun i _ => ENNReal.ofReal_ne_top)]
  exact sum_congr rfl fun i _ => ENNReal.toReal_ofReal (hω.2 i)


lemma Submartingale.uniform_bdd_l1_of_uniform_bdd_above
  (hf : Submartingale f ℱ μ)
  (hbdd : ∃ R : ℝ, ∀ n, μ[(f n)⁺] ≤ R)
  : ∃ R : ℝ≥0, ∀ n, eLpNorm (f n) 1 μ ≤ R := by
  obtain ⟨hAdapted, hNondec, hInt⟩ := hf
  obtain ⟨R, hbdd⟩ := hbdd
  have hμfn : ∀ n, μ[(f n)⁻] = μ[(f n)⁺] - μ[f n] := by
    intro n
    rw [show ((f n)⁻ : Ω → ℝ) = fun ω => max (-(f n ω)) 0 from rfl,
      show ((f n)⁺ : Ω → ℝ) = fun ω => max (f n ω) 0 from rfl,
      ← integral_sub (Integrable.pos_part (hInt n)) (hInt n)]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    obtain h | h := le_total (f n ω) 0
    · simp only [max_eq_right h, max_eq_left (neg_nonneg.2 h)]; ring
    · simp only [max_eq_left h, max_eq_right (neg_nonpos.2 h)]; ring
  have hle : ∀ n, μ[f 0] ≤ μ[f n] := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      have hmono := hNondec n (n + 1) n.le_succ
      have hle := integral_mono_ae (hInt n) integrable_condExp hmono
      rw [integral_condExp] at hle
      exact ih.trans hle
  have hnegbdd : ∀ n, μ[(f n)⁻] ≤ R - μ[f 0] := fun n => by
    linarith [hμfn n, hle n, hbdd n]
  have habs : ∀ n, μ[fun ω => |f n ω|] ≤ 2 * R - μ[f 0] := by
    intro n
    have hcongr : (fun ω => |f n ω|) =ᵐ[μ] fun ω => max (f n ω) 0 + max (-(f n ω)) 0 :=
      Eventually.of_forall fun ω => (posPart_add_negPart (f n ω)).symm
    rw [integral_congr_ae hcongr, integral_add (Integrable.pos_part (hInt n))
      (Integrable.neg_part (hInt n)),
      show (fun ω => max (f n ω) 0) = ((f n)⁺ : Ω → ℝ) from rfl,
      show (fun ω => max (-(f n ω)) 0) = ((f n)⁻ : Ω → ℝ) from rfl]
    linarith [hbdd n, hμfn n, hle n]
  let R' := |2 * R - μ[f 0]|
  have hR'nonneg : (0 : ℝ) ≤ R' := abs_nonneg _
  have habs' : ∀ n, μ[fun ω => |f n ω|] ≤ R' :=
    fun n => (habs n).trans (le_abs_self (2 * R - μ[f 0]))
  refine ⟨⟨R', hR'nonneg⟩, fun n => ?_⟩
  rw [eLpNorm_one_eq_lintegral_enorm]
  have hfm : AEStronglyMeasurable (f n) μ := (hInt n).aemeasurable.aestronglyMeasurable
  have hltop : ∫⁻ x, ‖f n x‖ₑ ∂μ ≠ ⊤ := (hInt n).hasFiniteIntegral.lt_top.ne
  have h := habs' n
  rw [integral_congr_ae (Eventually.of_forall fun x => (Real.norm_eq_abs (f n x)).symm),
    integral_norm_eq_lintegral_enorm hfm] at h
  have h := ENNReal.ofReal_le_ofReal h
  rw [ENNReal.ofReal_toReal hltop, ENNReal.ofReal_eq_coe_nnreal hR'nonneg] at h
  exact h

lemma sum_cancel_consecutive {α : Type*} [AddCommGroup α] {f : ℕ → α} {m n : ℕ} (hmn : m ≤ n) :
  ∑ i ∈ Ico m n, (f (i + 1) - f i) = f n - f m :=
  Finset.sum_Ico_sub f hmn

theorem ae_tendsto_zero_of_almost_supermartingale
    (hAdapt : Adapted ℱ f)
    (hfm : ∀ n, Measurable (f n))
    (hfInt : ∀ n, Integrable (f n) μ)
    (hfnonneg : ∀ n, 0 ≤ᵐ[μ] f n)
    {T : ℕ → ℝ}
    (hTpos : ∀ n, 0 < T n)
    {hTsum : Tendsto (fun n => ∑ k ∈ range n, T k) atTop atTop}
    {hTsqsum : Summable (fun n => (T n) ^ 2)}
    (hAlmostSupermartingale :
      ∃ C ≥ 0, ∀ n, μ[f (n + 1) | ℱ n] ≤ᵐ[μ] (fun ω => (1 - T n) * f n ω + C * T n ^ 2)) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 0) := by
    obtain ⟨C, hC, hAlmostSupermartingale⟩ := hAlmostSupermartingale

    let tail := fun n => ∑' k, (T (k + n)) ^ 2
    let g := fun n (_ : Ω) => C * tail n
    have htailnonneg : ∀ m, 0 ≤ tail m := fun m => tsum_nonneg fun k => sq_nonneg (T (k + m))
    have hgInt : ∀ n, Integrable (g n) μ := fun _ => integrable_const _
    let W := -f - g
    have hWeq : ∀ n ω, W n ω = -(f n ω) - C * tail n := fun _ _ => rfl
    have hWInt : ∀ n, Integrable (W n) μ := fun n => ((hfInt n).neg).sub (hgInt n)
    have hWm : ∀ n, @StronglyMeasurable _ _ _ (ℱ n) (W n) := fun n =>
      ((hAdapt n).stronglyMeasurable.neg).sub (stronglyMeasurable_const)
    have htail : ∀ n, tail n = T n ^ 2 + tail (n + 1) := by
      intro n
      have hsumm : Summable (fun k => T (k + n) ^ 2) := (_root_.summable_nat_add_iff n).mpr hTsqsum
      have hsplit := hsumm.tsum_eq_zero_add
      simp only [zero_add] at hsplit
      have hcongr : (∑' k, T (k + 1 + n) ^ 2) = tail (n + 1) :=
        tsum_congr fun k => by congr 2; omega
      change (∑' k, T (k + n) ^ 2) = T n ^ 2 + tail (n + 1)
      rw [hsplit, hcongr]
    have hW : ∀ n, W n + T n • f n ≤ᶠ[ae μ] μ[W (n + 1)|ℱ n] := by
      intro n
      have hcond : (μ[W (n + 1)|ℱ n] : Ω → ℝ) =ᵐ[μ]
          fun ω => -(μ[f (n + 1)|ℱ n] ω) - C * tail (n + 1) := by
        refine (condExp_sub (hfInt (n + 1)).neg (hgInt (n + 1)) _).trans ?_
        refine EventuallyEq.sub (condExp_neg _ _) ?_
        exact Eventually.of_forall fun ω => congrFun (condExp_const (μ := μ) (ℱ.le' n) _) ω
      refine EventuallyLE.trans_eq ?_ hcond.symm
      apply Eventually.mono ((hAlmostSupermartingale n).and (hfnonneg n))
      intro ω hω
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hω ⊢
      rw [hWeq, htail n]
      nlinarith [hω.1, hω.2, hC, htailnonneg (n + 1), mul_nonneg hC (htailnonneg (n + 1))]
    have hWsub : Submartingale W ℱ μ := by
      refine ⟨fun n => ((hAdapt n).stronglyMeasurable.neg).sub stronglyMeasurable_const,
        fun i => ?_, hWInt⟩
      refine Nat.le_induction ?_ ?_
      · exact (condExp_of_aestronglyMeasurable' _ (hWm i).aestronglyMeasurable (hWInt i)).symm.le
      · intro n hn hin
        have hstep : W n ≤ᶠ[ae μ] μ[W (n + 1)|ℱ n] := by
          apply Eventually.mono ((hW n).and (hfnonneg n))
          intro ω hω
          have h1 := hω.1
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1
          exact le_of_add_le_of_nonneg_left h1 (mul_nonneg (hTpos n).le hω.2)
        have hmono := condExp_mono (m := ℱ i) (hWInt n) integrable_condExp hstep
        exact (hin.trans hmono).trans_eq (condExp_condExp (μ := μ) (W (n + 1)) ℱ hn)
    have hWnonpos : ∀ n, μ[(W n)⁺] ≤ 0 := by
      intro n
      have hle : (W n)⁺ ≤ᵐ[μ] 0 := by
        apply Eventually.mono (hfnonneg n)
        intro ω hω
        simp only [Pi.posPart_apply, Pi.zero_apply] at hω ⊢
        refine posPart_nonpos.mpr ?_
        rw [hWeq]
        nlinarith [hω, htailnonneg n, mul_nonneg hC (htailnonneg n)]
      calc μ[(W n)⁺] ≤ ∫ _, (0 : ℝ) ∂μ :=
            integral_mono_ae (Integrable.pos_part (hWInt n)) (integrable_const 0) hle
        _ = 0 := integral_zero _ _

    obtain ⟨R, hR⟩ := hWsub.uniform_bdd_l1_of_uniform_bdd_above ⟨0, hWnonpos⟩
    have hWtendsto := hWsub.exists_ae_tendsto_of_bdd hR
    have hftendsto : ∀ᵐ ω ∂μ, ∃ c, Tendsto (fun n => f n ω) atTop (𝓝 c) := by
      apply Eventually.mono hWtendsto
      intro ω hω
      obtain ⟨c, hc⟩ := hω
      simp [W, g] at hc
      refine ⟨-c, ?_⟩
      have : Tendsto tail atTop (𝓝 0) := by
        unfold tail
        apply Tendsto.congr
        intro n
        have := Summable.sum_add_tsum_nat_add n hTsqsum
        have := eq_sub_of_add_eq' this
        exact this.symm
        have := hTsqsum.tendsto_sum_tsum_nat
        have := this.const_sub (b := ∑' (i : ℕ), T i ^ 2)
        simp at this
        exact this
      have := (hc.add (this.const_mul C)).neg
      unfold tail at this
      simp at this
      exact this

    have : Summable (fun n => μ[T n • f n]) := by
      set g := fun n => μ[T n • f n]
      have hg : ∀ n, 0 ≤ g n := by
        intro n
        apply integral_nonneg_of_ae
        apply Eventually.mono (hfnonneg n)
        intro ω hω
        simp at hω ⊢
        apply mul_nonneg
        exact (hTpos n).le
        exact hω
      have hgub : ∀ n, μ[T n • f n] ≤ μ[W (n + 1)] - μ[W n] := by
        intro n
        have := integral_mono_ae ?_ ?_ (hW n)
        simp at this
        rw [integral_condExp _, integral_add] at this
        simp
        linarith
        exact hWInt n
        exact (hfInt n).const_mul (T n)
        exact (hWInt n).add ((hfInt n).const_mul (T n))
        apply integrable_condExp
      have : ∃ l, Tendsto (fun n ↦ ∑ i ∈ range n, g i) atTop (𝓝 l) := by
        have hmono : Monotone fun n => ∑ i ∈ range n, g i := by
          intro m n hmn
          apply sum_mono_set_of_nonneg
          exact hg
          simp
          exact hmn
        apply Or.resolve_left
        apply tendsto_atTop_of_monotone hmono
        by_contra hcontra
        have := (tendsto_atTop_atTop_iff_of_monotone hmono).mp hcontra
        apply absurd this
        push Not
        refine ⟨R + |μ[W 0]| + 1, ?hub⟩
        case hub =>
          intro n
          simp [g]
          apply lt_of_le_of_lt
          apply sum_le_sum
          intro i hi
          exact hgub i
          have : range n = Ico 0 n := by simp
          rw [this]
          rw [sum_cancel_consecutive (f := fun n => ∫ ω, W n ω ∂μ) (by simp)]
          have := hR n
          simp [eLpNorm_one_eq_lintegral_enorm] at this
          apply lt_of_le_of_lt
          case hbc.b => exact R + |μ[W 0]|
          apply le_of_abs_le
          rw [sub_eq_add_neg]
          grw [abs_add_le]
          rw [abs_neg]
          simp
          rw [←Real.norm_eq_abs]
          grw [norm_integral_le_lintegral_norm]
          apply ENNReal.toReal_le_coe_of_le_coe
          simp
          grw [lintegral_ofReal_le_lintegral_enorm]
          simp [this]
          simp
      refine ⟨this.choose, ?hc⟩
      case hc =>
        apply (hasSum_iff_tendsto_nat_of_nonneg ?_ _).mpr
        exact this.choose_spec
        exact hg

    have := ae_summable_of_summable_integral ?_ ?_ ?_ this
    apply Eventually.mono ((this.and hftendsto).and (ae_all_iff.mpr hfnonneg))
    intro ω hω
    simp at hω
    obtain ⟨c, hc⟩ := hω.1.2
    have : 0 = c := by
      by_contra h
      have : 0 ≤ c := by
        apply le_of_tendsto_of_tendsto' (f := 0) _ hc
        intro n
        simp
        exact hω.2 n
        apply tendsto_const_nhds
      have hcpos : 0 < c := by apply lt_of_le_of_ne this h
      set ε := c / 2 with hε
      have := Metric.tendsto_atTop.mp hc ε (by simp [ε, hcpos])
      obtain ⟨n₀, hn₀⟩ := this
      have hflb : ∀ n ≥ n₀, ε < f n ω := by
        intro n hn
        have h := hn₀ n hn
        simp [dist] at h
        unfold ε at h ⊢
        have := le_abs_self (c - f n ω)
        rw [←abs_neg, neg_sub] at this
        linarith
      apply absurd hω.1.1
      apply (not_summable_iff_tendsto_nat_atTop_of_nonneg ?_).mpr
      apply (tendsto_add_atTop_iff_nat n₀).mp

      have := hTsum.atTop_mul_const (r := ε) (by linarith)
      have := (tendsto_add_atTop_iff_nat n₀).mpr this
      have := tendsto_atTop_add_const_right atTop
        (∑ k ∈ range n₀, T k * f k ω - ∑ k ∈ range n₀, T k * ε) this
      apply tendsto_atTop_mono' atTop ?_ this
      apply Filter.eventually_atTop.mpr
      refine ⟨n₀, ?hN⟩
      case hN =>
        intro n hn
        simp
        rw [sum_mul]
        simp_rw [range_eq_Ico]
        have := Ico_union_Ico_eq_Ico
          (a := 0) (b := n₀) (c := n + n₀) (by simp) (by simp)
        simp_rw [←this]
        rw [sum_union, sum_union]
        nth_rw 2 [add_comm]
        rw [add_add_sub_cancel]
        rw [add_comm]
        apply add_le_add
        rfl
        apply sum_le_sum
        intro i hi
        apply mul_le_mul_of_nonneg_left
        apply le_of_lt
        apply hflb i
        simp [mem_Ico.mp hi]
        apply le_of_lt
        apply hTpos
        apply Ico_disjoint_Ico_consecutive
        apply Ico_disjoint_Ico_consecutive
      intro n
      apply mul_nonneg
      apply le_of_lt
      apply hTpos
      apply hω.2
    simp [←this] at hc
    exact hc

    intro n
    apply Integrable.smul
    exact hfInt n
    intro n
    apply Measurable.const_mul
    exact hfm n
    intro n
    apply Eventually.mono (hfnonneg n)
    intro ω hω
    simp at hω ⊢
    apply mul_nonneg
    exact (hTpos n).le
    exact hω

end MeasureTheory
