/-
Copyright (c) 2026 M1ngXU. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Max Obreiter, Tobias Steinbrecher, Robert Foerster
-/

import LeanPool.PLAcceleratedNesterovLean.MorseBott.Defs
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Tubular Neighborhood Projection — Definitions and Helpers

Core definitions (`optimalityEqn`, `IsTubularNeighborhoodOfSubmanifold`,
`tubularProj`) and basic helper lemmas for the nearest-point projection.
-/

open Filter Topology Metric NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

namespace PLAcceleratedNesterovLean

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

-- ════════════════════════════════════════════════════════════════════════════
-- § Optimality equation (needed in structure definition)
-- ════════════════════════════════════════════════════════════════════════════

/-- The first-order optimality equation for the nearest-point problem.

Given a submanifold chart `(V, φ, δ)` at `m ∈ S`, the nearest point
on `S` to a query point `y = m + r` is `p = m + v + φ(v)` where
`y − p ⊥ T_pS`. We encode this as:

  `F(r, v) = V.orthogonalProjectionOnto(r − v − φ(v))
            + (fderiv ℝ φ v).adjoint (V⊥.orthogonalProjectionOnto(r − v − φ(v)))` -/
noncomputable def optimalityEqn
    {V : Submodule ℝ E} (φ : V → V.orthogonal) (_m : E)
    : E × V → V :=
  let _anchor := _m
  fun ⟨r, v⟩ =>
    let residual := r - (v : E) - (φ v : E)
    V.orthogonalProjectionOnto residual +
      (fderiv ℝ φ v).adjoint (V.orthogonal.orthogonalProjectionOnto
        (show E from residual))

-- ════════════════════════════════════════════════════════════════════════════
-- § Definition
-- ════════════════════════════════════════════════════════════════════════════

/-- A tubular neighborhood of a C² submanifold `S` in a
    finite-dimensional inner product space.

    Bundles:
    - `U` is open with `S ⊆ U`
    - Every point in `U` has a unique nearest point in `S`
    - `S` is a C² submanifold (locally a C² graph over a subspace)

    `S` is automatically closed relative to `U` (from `uniqueProj`);
    see `mem_of_mem_closure_in_U`. -/
structure IsTubularNeighborhoodOfSubmanifold (S U : Set E) : Prop where
  isOpen : IsOpen U
  subset : S ⊆ U
  uniqueProj : ∀ x ∈ U, ∃! p, p ∈ S ∧ dist x p = Metric.infDist x S
  -- C² submanifold: at each point m ∈ S, there exists a decomposition
  -- E = V ⊕ V⊥ where V is the tangent space, and S is locally the graph
  -- of a C² function φ : V → V⊥ with φ(0) = 0, Dφ(0) = 0.
  -- The normal space is allowed to be trivial, covering the full-dimensional
  -- edge case.
  submanifold_chart : ∀ m ∈ S, ∃ (V : Submodule ℝ E)
    (φ : V → V.orthogonal) (δ : ℝ),
    0 < δ ∧
    ContDiff ℝ 2 φ ∧
    φ 0 = 0 ∧
    fderiv ℝ φ 0 = 0 ∧
    (∀ x ∈ Metric.ball m δ,
      x ∈ S ↔ ∃ v : V, x = m + (v : E) + (φ v : E))

-- ════════════════════════════════════════════════════════════════════════════
-- § Projection map
-- ════════════════════════════════════════════════════════════════════════════

/-- The nearest-point projection: for `x ∈ U` pick the unique closest point
    in `S`; for `x ∉ U` pick an arbitrary element of `S`. -/
def tubularProj {S U : Set E} (hTN : IsTubularNeighborhoodOfSubmanifold S U)
    (hne : S.Nonempty) (x : E) : E :=
  if hx : x ∈ U then
    (hTN.uniqueProj x hx).choose
  else
    hne.some

-- ════════════════════════════════════════════════════════════════════════════
-- § Helper lemmas
-- ════════════════════════════════════════════════════════════════════════════

omit [FiniteDimensional ℝ E] in
private lemma tubularProj_eq_choose {S U : Set E}
    (hTN : IsTubularNeighborhoodOfSubmanifold S U) (hne : S.Nonempty)
    (x : E) (hx : x ∈ U) :
    tubularProj hTN hne x = (hTN.uniqueProj x hx).choose := by
  simp only [tubularProj, and_imp, dif_pos hx]

omit [FiniteDimensional ℝ E] in
lemma tubularProj_mem {S U : Set E}
    (hTN : IsTubularNeighborhoodOfSubmanifold S U) (hne : S.Nonempty)
    (x : E) (hx : x ∈ U) :
    tubularProj hTN hne x ∈ S ∧ dist x (tubularProj hTN hne x) = Metric.infDist x S := by
  rw [tubularProj_eq_choose hTN hne x hx]
  exact (hTN.uniqueProj x hx).choose_spec.1

omit [FiniteDimensional ℝ E] in
lemma tubularProj_unique {S U : Set E}
    (hTN : IsTubularNeighborhoodOfSubmanifold S U) (hne : S.Nonempty)
    (x : E) (hx : x ∈ U) (y : E) (hy : y ∈ S ∧ dist x y = Metric.infDist x S) :
    y = tubularProj hTN hne x := by
  rw [tubularProj_eq_choose hTN hne x hx]
  exact (hTN.uniqueProj x hx).choose_spec.2 y hy

omit [FiniteDimensional ℝ E] in
lemma tubularProj_fixes_S {S U : Set E}
    (hTN : IsTubularNeighborhoodOfSubmanifold S U) (hne : S.Nonempty)
    (x : E) (hx : x ∈ S) :
    tubularProj hTN hne x = x := by
  have hx_U : x ∈ U := hTN.subset hx
  exact (tubularProj_unique hTN hne x hx_U x
    ⟨hx, by rw [dist_self, Metric.infDist_zero_of_mem hx]⟩).symm

omit [FiniteDimensional ℝ E] in
/-- If `f` is differentiable at `x`, `f(x) = x`, and `f(x + tv) = x` for all
    small `t > 0`, then `fderiv ℝ f x v = 0`.

    From `HasFDerivAt`: `‖f(x+h) - x - L(h)‖ ≤ (ε/‖v‖)·‖h‖` for `‖h‖ < δ`.
    Setting `h = tv` with fiber constancy `f(x+tv) = x`:
    `t·‖L(v)‖ ≤ (ε/‖v‖)·t·‖v‖ = t·ε`, so `‖L(v)‖ ≤ ε`.
    Since `ε > 0` is arbitrary, `L(v) = 0`. -/
lemma fderiv_eq_zero_of_const_on_ray {f : E → E} {x v : E}
    (hf : DifferentiableAt ℝ f x)
    (hfx : f x = x)
    (hconst : ∀ t : ℝ, 0 < t → t ≤ 1 → f (x + t • v) = x) :
    fderiv ℝ f x v = 0 := by
  by_cases hv : v = 0
  · simp only [hv, map_zero]
  set L := fderiv ℝ f x
  have hfda : HasFDerivAt f L x := hf.hasFDerivAt
  rw [hasFDerivAt_iff_isLittleO_nhds_zero] at hfda
  have hv_pos : (0 : ℝ) < ‖v‖ := norm_pos_iff.mpr hv
  refine norm_le_zero_iff.mp (le_of_forall_gt_imp_ge_of_dense fun ε hε => ?_)
  obtain ⟨δ, hδ_pos, hball⟩ := Metric.eventually_nhds_iff.mp (hfda.def (div_pos hε hv_pos))
  set t := min 1 (δ / (2 * ‖v‖))
  have ht_pos : 0 < t := lt_min one_pos (div_pos hδ_pos (mul_pos two_pos hv_pos))
  have ht_in : dist (t • v) 0 < δ := by
    rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos ht_pos]
    calc t * ‖v‖ ≤ (δ / (2 * ‖v‖)) * ‖v‖ :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) hv_pos.le
         _ = δ / 2 := by field_simp
         _ < δ := half_lt_self hδ_pos
  have hbound := hball ht_in
  rw [hconst t ht_pos (min_le_left _ _), hfx, sub_self, zero_sub, norm_neg,
      map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos ht_pos,
      norm_smul, Real.norm_eq_abs, abs_of_pos ht_pos] at hbound
  have hrhs : ε / ‖v‖ * (t * ‖v‖) = t * ε := by field_simp
  rw [hrhs] at hbound
  exact le_of_mul_le_mul_left hbound ht_pos

omit [FiniteDimensional ℝ E] in
/-- Local version: constancy on a short initial segment `(0, t₀]` suffices. -/
lemma fderiv_eq_zero_of_const_on_ray_local {f : E → E} {x v : E}
    (hf : DifferentiableAt ℝ f x)
    (hfx : f x = x)
    {t₀ : ℝ} (ht₀ : 0 < t₀)
    (hconst : ∀ t : ℝ, 0 < t → t ≤ t₀ → f (x + t • v) = x) :
    fderiv ℝ f x v = 0 := by
  by_cases hv : v = 0
  · simp only [hv, map_zero]
  set L := fderiv ℝ f x
  have hfda : HasFDerivAt f L x := hf.hasFDerivAt
  rw [hasFDerivAt_iff_isLittleO_nhds_zero] at hfda
  have hv_pos : (0 : ℝ) < ‖v‖ := norm_pos_iff.mpr hv
  refine norm_le_zero_iff.mp (le_of_forall_gt_imp_ge_of_dense fun ε hε => ?_)
  obtain ⟨δ, hδ_pos, hball⟩ := Metric.eventually_nhds_iff.mp (hfda.def (div_pos hε hv_pos))
  set t := min t₀ (δ / (2 * ‖v‖))
  have ht_pos : 0 < t := lt_min ht₀ (div_pos hδ_pos (mul_pos two_pos hv_pos))
  have ht_in : dist (t • v) 0 < δ := by
    rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos ht_pos]
    calc t * ‖v‖ ≤ (δ / (2 * ‖v‖)) * ‖v‖ :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) hv_pos.le
         _ = δ / 2 := by field_simp
         _ < δ := half_lt_self hδ_pos
  have hbound := hball ht_in
  rw [hconst t ht_pos (min_le_left _ _), hfx, sub_self, zero_sub, norm_neg,
      map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos ht_pos,
      norm_smul, Real.norm_eq_abs, abs_of_pos ht_pos] at hbound
  have hrhs : ε / ‖v‖ * (t * ‖v‖) = t * ε := by field_simp
  rw [hrhs] at hbound
  exact le_of_mul_le_mul_left hbound ht_pos

omit [FiniteDimensional ℝ E] in
/-- π is constant along the fiber segment `[(1-t)·πx + t·x]` for `t ∈ [0,1]`.
    Combines star-shapedness (Prop 5), distance realization (Prop 6), and
    uniqueness of nearest point. -/
lemma tubularProj_const_on_fiber {S U : Set E}
    (hTN : IsTubularNeighborhoodOfSubmanifold S U) (hne : S.Nonempty)
    (x : E) (hx : x ∈ U) (t : ℝ) (_ht : t ∈ Set.Icc (0 : ℝ) 1)
    (h_in_U : (1 - t) • tubularProj hTN hne x + t • x ∈ U)
    (h_realizes : ‖(1 - t) • tubularProj hTN hne x + t • x - tubularProj hTN hne x‖
                  = Metric.infDist ((1 - t) • tubularProj hTN hne x + t • x) S) :
    tubularProj hTN hne ((1 - t) • tubularProj hTN hne x + t • x) =
      tubularProj hTN hne x := by
  set y := (1 - t) • tubularProj hTN hne x + t • x
  set πx := tubularProj hTN hne x
  have hπS : πx ∈ S := (tubularProj_mem hTN hne x hx).1
  exact (tubularProj_unique hTN hne y h_in_U πx
    ⟨hπS, by rw [dist_eq_norm]; exact h_realizes⟩).symm


omit [FiniteDimensional ℝ E] in
/-- The fiber segment from πx to x realizes the infDist at every point.
    Extracted from the Property 6 proof for reuse in Property 7. -/
lemma tubularProj_fiber_realizes_infDist {S U : Set E}
    (hTN : IsTubularNeighborhoodOfSubmanifold S U) (hne : S.Nonempty)
    (x : E) (hx : x ∈ U) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖(1 - t) • tubularProj hTN hne x + t • x - tubularProj hTN hne x‖ =
    Metric.infDist ((1 - t) • tubularProj hTN hne x + t • x) S := by
  obtain ⟨h0, h1⟩ := ht
  set πx := tubularProj hTN hne x
  have hπS := (tubularProj_mem hTN hne x hx).1
  have hπdist := (tubularProj_mem hTN hne x hx).2
  have hy_sub : (1 - t) • πx + t • x - πx = t • (x - πx) := by
    rw [sub_smul, one_smul, smul_sub]; abel
  have hy_norm : ‖(1 - t) • πx + t • x - πx‖ = t * ‖x - πx‖ := by
    rw [hy_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg h0]
  have hx_sub_y : x - ((1 - t) • πx + t • x) = (1 - t) • (x - πx) := by
    simp only [smul_sub, sub_smul, one_smul]; abel
  have hdist_xy : dist x ((1 - t) • πx + t • x) = (1 - t) * ‖x - πx‖ := by
    rw [dist_eq_norm, hx_sub_y, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr h1)]
  have hdist_xπ : dist x πx = ‖x - πx‖ := dist_eq_norm x πx
  apply le_antisymm
  · rw [hy_norm, Metric.le_infDist hne]
    intro m hm
    have h_near : ‖x - πx‖ ≤ dist x m := by
      rw [← hdist_xπ, hπdist]; exact Metric.infDist_le_dist_of_mem hm
    have h_tri : dist x m ≤ dist x ((1 - t) • πx + t • x) +
        dist ((1 - t) • πx + t • x) m := dist_triangle _ _ _
    rw [hdist_xy] at h_tri
    linarith
  · calc Metric.infDist ((1 - t) • πx + t • x) S
        ≤ dist ((1 - t) • πx + t • x) πx := Metric.infDist_le_dist_of_mem hπS
      _ = ‖(1 - t) • πx + t • x - πx‖ := dist_eq_norm _ _

omit [FiniteDimensional ℝ E] in
/-- U is open. -/
lemma U_isOpen {S U : Set E}
    (hTN : IsTubularNeighborhoodOfSubmanifold S U) : IsOpen U :=
  hTN.isOpen

namespace IsTubularNeighborhoodOfSubmanifold

omit [FiniteDimensional ℝ E] in
/-- `S` is closed relative to `U`: any limit point of `S` that lies in `U` belongs to `S`.
    Proof: `infDist(x, S) = 0` and `uniqueProj` gives a point of `S` at distance 0. -/
lemma mem_of_mem_closure_in_U {S U : Set E}
    (hTN : IsTubularNeighborhoodOfSubmanifold S U)
    {x : E} (hxU : x ∈ U) (hx_cl : x ∈ closure S) : x ∈ S := by
  obtain ⟨p, ⟨hpS, hpdist⟩, _⟩ := hTN.uniqueProj x hxU
  suffices dist x p = 0 by rwa [dist_eq_zero.mp this]
  rw [hpdist]
  by_contra h
  have hpos : 0 < Metric.infDist x S :=
    lt_of_le_of_ne Metric.infDist_nonneg (Ne.symm h)
  obtain ⟨y, hyS, hxy⟩ := Metric.mem_closure_iff.mp hx_cl _ hpos
  exact absurd hxy (not_lt.mpr (Metric.infDist_le_dist_of_mem hyS))

omit [FiniteDimensional ℝ E] in
/-- `S ∩ C` is closed whenever `C` is closed and `C ⊆ U`.
    Follows from `S` being closed relative to `U`. -/
lemma isClosed_inter_closed {S U : Set E}
    (hTN : IsTubularNeighborhoodOfSubmanifold S U)
    {C : Set E} (hC_closed : IsClosed C) (hC_sub : C ⊆ U) :
    IsClosed (S ∩ C) := by
  apply isClosed_of_closure_subset
  intro x hx
  have hxC : x ∈ C := by
    have h1 : x ∈ closure C := closure_mono Set.inter_subset_right hx
    rw [hC_closed.closure_eq] at h1; exact h1
  exact ⟨hTN.mem_of_mem_closure_in_U (hC_sub hxC)
    (closure_mono Set.inter_subset_left hx), hxC⟩

omit [FiniteDimensional ℝ E] in
/-- `S ∩ closedBall(m, r)` is compact when `closedBall(m, r) ⊆ U`
    (in a proper metric space). -/
lemma isCompact_inter_closedBall {S U : Set E}
    (hTN : IsTubularNeighborhoodOfSubmanifold S U) [ProperSpace E]
    {m : E} {r : ℝ} (hr : Metric.closedBall m r ⊆ U) :
    IsCompact (S ∩ Metric.closedBall m r) :=
  (isCompact_closedBall m r).of_isClosed_subset
    (hTN.isClosed_inter_closed Metric.isClosed_closedBall hr)
    Set.inter_subset_right

end IsTubularNeighborhoodOfSubmanifold

omit [FiniteDimensional ℝ E] in
/-- The projection is continuous at every point of `S`.
    Since `U` is open, for `m ∈ S ⊆ U`, nearby points are in `U` and
    `dist(π(x), m) ≤ 2·dist(x, m)`. -/
lemma tubularProj_continuousAt_of_mem {S U : Set E}
    (hTN : IsTubularNeighborhoodOfSubmanifold S U) (hne : S.Nonempty)
    {m : E} (hm : m ∈ S) :
    ContinuousAt (tubularProj hTN hne) m := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  have hm_U := hTN.subset hm
  obtain ⟨δ, hδ_pos, hδ_sub⟩ := Metric.isOpen_iff.mp hTN.isOpen m hm_U
  have hπ_m := tubularProj_fixes_S hTN hne m hm
  refine ⟨min (ε / 2) δ, lt_min (half_pos hε) hδ_pos, fun x hx => ?_⟩
  have hxU : x ∈ U :=
    hδ_sub (Metric.mem_ball.mpr (lt_of_lt_of_le hx (min_le_right _ _)))
  have hπ_dist : dist (tubularProj hTN hne x) x = Metric.infDist x S := by
    rw [dist_comm]; exact (tubularProj_mem hTN hne x hxU).2
  calc dist (tubularProj hTN hne x) (tubularProj hTN hne m)
      = dist (tubularProj hTN hne x) m := by rw [hπ_m]
    _ ≤ dist (tubularProj hTN hne x) x + dist x m := dist_triangle _ _ _
    _ = Metric.infDist x S + dist x m := by rw [hπ_dist]
    _ ≤ dist x m + dist x m := by gcongr; exact Metric.infDist_le_dist_of_mem hm
    _ = 2 * dist x m := by ring
    _ < 2 * (ε / 2) := by linarith [lt_of_lt_of_le hx (min_le_left _ _)]
    _ = ε := by ring

end PLAcceleratedNesterovLean
