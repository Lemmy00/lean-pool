/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/

import LeanPool.Polytopes.Polytope


variable {E  : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
open Pointwise

/-
Let 𝑋 be a closed convex subset of ℝ^𝑑. Then:
• 𝑋 is a 𝑉-polytope if it is the convex hull of a finite point set.
• 𝑋 is an 𝐻-polytope if it is the intersection of finitely many half spaces.

Theorem : Every 𝑉-polytope is an 𝐻-polytope, and every compact 𝐻-polytope is a 𝑉-polytope.
-/

-- As a ball around x is convex, it must contain a segment with x in its interior
lemma hxSegBallInterSeg : ∀ (x1 x2 : E) (ε : ℝ),
  x ∈ openSegment ℝ x1 x2 ∧ ¬ (x1 = x ∧ x2 = x) → 0 < ε →
  ∃ x1' x2', x ∈ openSegment ℝ x1' x2' ∧
  segment ℝ x1' x2' ⊆ openSegment ℝ x1 x2 ∩ Metric.ball x ε ∧ ¬ (x1' = x ∧ x2' = x) := by
  rintro x1 x2 ε ⟨ hxseg, hne ⟩ hε
  push_neg at hne
  have hxseg' := hxseg
  rw [openSegment_eq_image', Set.mem_image] at hxseg
  rcases hxseg with ⟨ t, ht, htt ⟩
  let v := x2 - x1
  let t1 := (-(min t (ε/norm v)/2))
  let t2 := ((min (1-t) (ε/norm v))/2)
  use t1 • v + x
  use t2 • v + x

  have hx12 : x1 ≠ x2 := by
    intro h
    rw [←h, openSegment_same] at hxseg'
    exact (h.symm ▸ hne) (Set.eq_of_mem_singleton hxseg').symm (Set.eq_of_mem_singleton hxseg').symm

  have ht1pos: 0 < min t (ε / ‖x2 - x1‖) := lt_min ht.1 <| div_pos hε <| norm_sub_pos_iff.mpr (Ne.symm hx12)

  have ht2pos: 0 < min (1 - t) (ε / ‖x2 - x1‖) :=
    lt_min (by linarith [ht.2]) <| div_pos hε <| norm_sub_pos_iff.mpr (Ne.symm hx12)

  have ht1 : t1 < 0 := neg_lt_zero.mpr <| half_pos ht1pos
  have ht2 : 0 < t2 := half_pos ht2pos
  have ht12 : 0 < t2 - t1 := sub_pos.mpr <| lt_trans ht1 ht2

  constructor
  · -- x in the segment
    rw [openSegment_eq_image', Set.mem_image]
    refine ⟨ (-t1/(t2 - t1)), ?_, ?_ ⟩
    ·
      constructor
      · -- 1.
        rw [div_pos_iff]
        left
        exact ⟨ neg_pos_of_neg ht1, ht12 ⟩
      · -- 2.
        rw [div_lt_one_iff]
        left
        exact ⟨ ht12, neg_lt_sub_iff_lt_add.mpr <| lt_add_of_le_of_pos (le_refl _) ht2 ⟩
      done
    ·
      rw [smul_sub (-t1 / (t2 - t1)), smul_add (-t1 / (t2 - t1)), smul_smul, smul_add, smul_smul,
        add_sub_add_comm, sub_self, add_zero, ←sub_smul, ←mul_sub, div_mul_cancel _ ?_, add_comm,
        ← add_assoc, ← add_smul, neg_add_self, zero_smul, zero_add]
      exact Ne.symm (ne_of_lt ht12)


  -- intersection of convex is convex
  -- convex of 1d is segment

  constructor
  · -- 1. main proof
    rw [Set.subset_inter_iff]
    constructor
    · -- 1. smaller segment is in the segment
      have := @convex_openSegment ℝ _ _ _ _ x1 x2
      rw [convex_iff_segment_subset] at this
      apply this <;> clear this <;> rw [←htt] <;>
      rw [@add_comm _ _ x1, ←add_assoc, ← add_smul, @add_comm _ _ _ t, openSegment_eq_image']
      · -- 1. first bound of the smaller segment is in the segment (boring ineq manipulation)
        exact ⟨ t + t1,
          ⟨ lt_of_le_of_lt' (by linarith [min_le_left t (ε/norm v)] : t -t/2 ≤ t -(min t (ε /norm v)/2))
            (by linarith [ht.1]), lt_trans (add_lt_of_neg_right t ht1) ht.2 ⟩,
          by unfold_let v; simp only [ge_iff_le]; rw [add_comm, @add_comm _ _ t t1, sub_eq_neg_add] ⟩
      · -- 2. second bound of the smaller segment is in the segment
        refine ⟨ t + t2,
          ⟨ lt_trans ht.1 (by linarith [ht2pos] : t < t + (min (1 - t) (ε / ‖x2 - x1‖) / 2)), ?_ ⟩,
          by simp only [ge_iff_le] ;rw [add_comm] ⟩
        exact lt_of_lt_of_le' (by linarith [ht.2]) (by linarith [min_le_left (1 - t) ((ε / ‖x2 - x1‖))]
          : t + min (1 - t) (ε / ‖x2 - x1‖) / 2 ≤ t + ((1 - t) / 2))
      done
    · -- 2. smaller segment is in the ball
      clear ht hxseg' hne -- ⊢ segment ℝ (t1 • v + x) (t2 • v + x) ⊆ Metric.ball x ε
      rw [← half_lt_self_iff] at hε -- ⊢ segment ℝ (t1 • v + x) (t2 • v + x) ⊆ Metric.ball x ε
      apply (convex_iff_segment_subset.mp <| convex_ball x ε ) <;> -- ⊢ t1 • v + x ∈ Metric.ball x ε
      rw [Metric.mem_ball] <;> -- ⊢ dist (t1 • v + x) x < ε
      norm_num <;> unfold_let -- ⊢ ‖(min t (ε / ‖x2 - x1‖) / 2) • (x2 - x1)‖ < ε
      simp
      all_goals {
        rw [norm_smul, -- ⊢ ‖min t (ε / ‖x2 - x1‖) / 2‖ * ‖x2 - x1‖ < ε
        Real.norm_eq_abs, -- ⊢ |min t (ε / ‖x2 - x1‖) / 2| * ‖x2 - x1‖ < ε
        abs_of_pos (by linarith), -- ⊢ min t (ε / ‖x2 - x1‖) / 2 * ‖x2 - x1‖ < ε
        ← min_div_div_right (by linarith), -- ⊢ min (t / 2) (ε / ‖x2 - x1‖ / 2) * ‖x2 - x1‖ < ε
        Monotone.map_min fun _ _ => (mul_le_mul_right (norm_sub_pos_iff.mpr (Ne.symm hx12))).mpr] -- ⊢ min (t / 2 * ‖x2 - x1‖) (ε / ‖x2 - x1‖ / 2 * ‖x2 - x1‖) < ε
        apply min_lt_of_right_lt ; -- ⊢ ε / ‖x2 - x1‖ / 2 * ‖x2 - x1‖ < ε
        rw [@div_mul_comm _ _ _ 2, -- ⊢ ‖x2 - x1‖ / 2 * (ε / ‖x2 - x1‖) < ε
        mul_comm, -- ⊢ ε / ‖x2 - x1‖ * (‖x2 - x1‖ / 2) < ε
        div_mul_div_cancel _ (Ne.symm (ne_of_lt (norm_sub_pos_iff.mpr (Ne.symm hx12))))] ; -- ⊢ ε / 2 < ε
        exact hε
      }
    done
  · -- 2. the smaller segment is not a singleton
    push_neg
    intro h1
    rcases (em (x1 = x)) with (rfl | hx1x)
    <;> norm_num
    <;> intro h
    <;> rw [sub_eq_zero] at h
    <;> rcases h with h | rfl
    exact (ne_of_lt ht2) h.symm
    simp at hne
    exact (ne_of_lt ht2) h.symm
    simp at hx12
    done
  done


def Hpolytope.I (H_ : Set (Halfspace E)) (x : E) : Set (Halfspace E) :=
  { Hi_ ∈ H_ | x ∈ (frontier <| SetLike.coe Hi_) }

lemma Hpolytope.I_mem {H_ : Set (Halfspace E)} (x : E) :
  ∀ Hi_, Hi_ ∈ Hpolytope.I H_ x ↔ Hi_ ∈ H_ ∧ x ∈ (frontier <| SetLike.coe Hi_) := by
  rintro Hi_
  unfold I
  rw [Set.mem_setOf]
  done

lemma Hpolytope.I_sub {H_ : Set (Halfspace E)} (x : E) :
  Hpolytope.I H_ x ⊆ H_ := by
  unfold Hpolytope.I
  simp only [Set.sep_subset]
  done

lemma ExtremePointsofHpolytope {H_ : Set (Halfspace E)} (hH_ : H_.Finite) :
  ∀ x ∈ Hpolytope hH_, x ∈ Set.extremePoints ℝ (Hpolytope hH_) ↔
  ⋂₀ ((frontier <| SetLike.coe ·) '' Hpolytope.I H_ x) = {x} := by
  rintro x hxH
  constructor
  · -- 1.
    intro hxEx
    rw [Set.eq_singleton_iff_unique_mem]
    refine ⟨ fun HiS ⟨ Hi_, hHi_, h ⟩ => h ▸ hHi_.2, ?_ ⟩

    contrapose! hxEx
    rcases hxEx with ⟨ y, hy, hyx ⟩

    -- some useful results
    have hxyy : x ∈ openSegment ℝ ((2:ℝ) • x - y) y := by
      clear hyx hy hxH hH_
      rw [openSegment_eq_image, Set.mem_image]
      refine ⟨ 1/2, by norm_num, ?_ ⟩
      rw [(by norm_num : (1:ℝ) - 1 / 2 = 1 / 2), smul_sub, sub_add_cancel, smul_smul,
        div_mul_cancel _ (by linarith), one_smul]
      done

    -- v is in halfspaces not in I by being inside a suitably small ball around x
    have hmemballmemIc : ∃ ε, ε > 0 ∧ ∀ v, v ∈ Metric.ball x ε → ∀ Hi_,
      Hi_ ∈ H_ \ Hpolytope.I H_ x → v ∈ SetLike.coe Hi_ := by
      -- For all Hi ∉ I x, x is in the interior of Hi then we can fit a ball around x within Hi
      have hball : ∃ ε, ε > 0 ∧ Metric.ball x ε ⊆
        ⋂₀ ((interior <| SetLike.coe ·) '' (H_ \ Hpolytope.I H_ x)) := by
        unfold Hpolytope at hxH
        have hxIcinterior : x ∈ ⋂₀ ((interior <| SetLike.coe ·) '' (H_ \ Hpolytope.I H_ x)) := by
          rintro HiS ⟨ Hi_, hHi_, rfl ⟩
          rw [Set.mem_diff, Hpolytope.I_mem, IsClosed.frontier_eq <| Halfspace_closed Hi_,
            Set.mem_diff] at hHi_
          push_neg at hHi_
          exact hHi_.2 hHi_.1 <| hxH Hi_ ⟨ Hi_, hHi_.1, rfl ⟩

        have hIcinteriorOpen : IsOpen (⋂₀ ((interior <| SetLike.coe ·) '' (H_ \ Hpolytope.I H_ x))) := by
          apply Set.Finite.isOpen_sInter (Set.Finite.image _ (Set.Finite.diff hH_ _))
          exact fun _ ⟨ Hi_, _, h ⟩ => h ▸ isOpen_interior

        rw [Metric.isOpen_iff] at hIcinteriorOpen
        exact hIcinteriorOpen x hxIcinterior

      rcases hball with ⟨ ε, hε, hball ⟩
      refine ⟨ ε, hε, fun v hv Hi_ hHi_ => ?_ ⟩
      apply interior_subset
      exact (Set.mem_sInter.mp <| hball hv) (interior <| SetLike.coe Hi_) ⟨ Hi_, hHi_, rfl ⟩

    -- v is in halfspaces in I by being in the segment
    have hmemsegmemI : ∀ v, v ∈ segment ℝ ((2:ℝ) • x - y) y →
      ∀ Hi_, Hi_ ∈ Hpolytope.I H_ x → v ∈ SetLike.coe Hi_ := by
      rintro v hv Hi_ hHi_
      -- x & y are in the hyperplane
      rw [Set.mem_sInter] at hy
      specialize hy (frontier <| SetLike.coe Hi_) ⟨ Hi_, hHi_, rfl ⟩
      have hHi_2 := hHi_.2
      rw [frontierHalfspace_Hyperplane] at hy hHi_2

      -- v ∈ segment ℝ ((2:ℝ) • x - y) y ⊆ frontier Hi_ ⊆ Hi_
      apply IsClosed.frontier_subset <| Halfspace_closed Hi_
      rw [frontierHalfspace_Hyperplane]
      apply Set.mem_of_mem_of_subset hv
      apply (convex_iff_segment_subset.mp <| Hyperplane_convex Hi_) _ hy

      -- segment is in the hyperplane as hyperplane is closed under affine combination
      have h21 : Finset.sum Finset.univ ![(2:ℝ), -1] = 1 := by
        rw [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
        linarith
        done

      have h2x_y := Hyperplane_affineClosed Hi_ ![x, y] (by
        rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty];
        exact Set.union_subset (Set.singleton_subset_iff.mpr hHi_2) (Set.singleton_subset_iff.mpr hy))
        ![2, -1] h21

      rw [Finset.affineCombination_eq_linear_combination _ _ _ h21, Fin.sum_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, neg_one_smul, ← sub_eq_add_neg] at h2x_y
      exact h2x_y

    rw [mem_extremePoints]
    push_neg
    rintro hxH'
    rcases hmemballmemIc with ⟨ ε, hε, hmemballmemIc ⟩
    rcases hxSegBallInterSeg ((2:ℝ) • x - y) y ε ⟨ hxyy, fun h => hyx h.2 ⟩ hε with
      ⟨ x1, x2, hmem, hsub, hne ⟩
    push_neg at hne ; clear hxH' hε hyx hy hxH hxyy
    unfold Hpolytope

    refine ⟨ x1, ?_, x2, ?_, ⟨ hmem, hne ⟩ ⟩ <;> clear hmem hne <;>
    rw [Set.mem_sInter] <;>
    intro Hi_s hHi_s <;>
    rw [Set.mem_image] at hHi_s <;>
    rcases hHi_s with ⟨ Hi_, hHi_, rfl ⟩

    · -- x1 ∈ Hpolytope hH_
      specialize hsub (left_mem_segment ℝ x1 x2)
      rcases (em (Hi_ ∈ Hpolytope.I H_ x)) with (hinI | hninI)
      ·
        apply hmemsegmemI x1 ?_ Hi_ hinI
        apply openSegment_subset_segment
        exact Set.mem_of_mem_inter_left hsub
      ·
        have : Hi_ ∈ H_ \ Hpolytope.I H_ x := by
          rw [Set.mem_diff]
          exact ⟨ hHi_, hninI ⟩
        exact hmemballmemIc x1 (Set.mem_of_mem_inter_right hsub) Hi_ this
      done
    · -- x2 ∈ Hpolytope hH_
      specialize hsub (right_mem_segment ℝ x1 x2)
      rcases (em (Hi_ ∈ Hpolytope.I H_ x)) with (hinI | hninI)
      ·
        apply hmemsegmemI x2 ?_ Hi_ hinI
        apply openSegment_subset_segment
        exact Set.mem_of_mem_inter_left hsub
      ·
        have : Hi_ ∈ H_ \ Hpolytope.I H_ x := by
          rw [Set.mem_diff]
          exact ⟨ hHi_, hninI ⟩
        exact hmemballmemIc x2 (Set.mem_of_mem_inter_right hsub) Hi_ this
    done

  · -- 2.
    intro hinterx
    rw [mem_extremePoints]
    refine ⟨ hxH, λ x1 hx1 x2 hx2 hx => ?_ ⟩

    have : segment ℝ x1 x2 ⊆ {x} → x1 = x ∧ x2 = x := by
      rw [Set.Nonempty.subset_singleton_iff (Set.nonempty_of_mem (left_mem_segment ℝ x1 x2)),
        Set.eq_singleton_iff_unique_mem]
      exact fun hseg => ⟨ hseg.2 x1 (left_mem_segment ℝ x1 x2),
        hseg.2 x2 (right_mem_segment ℝ x1 x2) ⟩
    apply this; clear this

    rw [← hinterx, Set.subset_sInter_iff]
    rintro HiS ⟨ Hi_, hHi_, rfl ⟩
    simp only

    have hfxα : Hi_.f.1 x = Hi_.α := by
      have : x ∈ {x} := by
        exact Set.mem_singleton x
      rw [← hinterx, Set.mem_sInter] at this
      specialize this (frontier <| SetLike.coe Hi_) ⟨ Hi_, hHi_, rfl ⟩
      rw [frontierHalfspace_Hyperplane, Set.mem_setOf] at this
      exact this
    clear hinterx hxH

    -- unpacking the fact that x1, x2 are in Hpolytope
    rw [mem_Hpolytope] at hx1 hx2
    specialize hx1 Hi_ hHi_.1
    specialize hx2 Hi_ hHi_.1
    clear hHi_ hH_ H_

    -- Frontier of a halfspace is convex
    rw [frontierHalfspace_Hyperplane]
    have := Hyperplane_convex Hi_
    rw [convex_iff_segment_subset] at this
    apply this <;>
    clear this <;>
    rw [Set.mem_setOf] <;>
    by_contra h <;>
    -- Since dual is linear map, if there is one end with less than α, with equal to α at some point in the middle (at x),
    -- then the other end must be greater than α, contradition!
    push_neg at h <;>
    have hlt := lt_of_le_of_ne (by assumption) h <;>
    clear h
    · -- If Hi_.f x1 < Hi_.α, then Hi_.f x2 > Hi_.α
      rw [openSegment_eq_image', Set.mem_image] at hx
      rcases hx with ⟨ t, ht, rfl ⟩
      rw [Hi_.f.1.map_add, Hi_.f.1.map_smul] at hfxα

      have : Hi_.f.1 x1 + t • Hi_.f.1 (x2 - x1) + (1-t) • Hi_.f.1 (x2 - x1) > Hi_.α := by
        rw [hfxα, gt_iff_lt]
        exact lt_add_of_le_of_pos (by linarith) <|
          (smul_pos_iff_of_pos_left (by linarith [ht.2])).mpr <|
          (smul_pos_iff_of_pos_left ht.1).mp <| pos_of_lt_add_right <| hfxα.symm ▸ hlt

      rw [add_assoc, ← add_smul, add_sub, add_comm t 1, add_sub_cancel, one_smul, ← Hi_.f.1.map_add, add_comm, sub_add_cancel] at this
      linarith
      done
    · -- If Hi_.f x2 < Hi_.α, then Hi_.f x1 > Hi_.α
      rw [openSegment_symm, openSegment_eq_image', Set.mem_image] at hx
      rcases hx with ⟨ t, ht, rfl ⟩
      rw [Hi_.f.1.map_add, Hi_.f.1.map_smul] at hfxα

      have : Hi_.f.1 x2 + t • Hi_.f.1 (x1 - x2) + (1-t) • Hi_.f.1 (x1 - x2) > Hi_.α := by
        rw [hfxα, gt_iff_lt]
        exact lt_add_of_le_of_pos (by linarith) <|
          (smul_pos_iff_of_pos_left (by linarith [ht.2])).mpr <|
          (smul_pos_iff_of_pos_left ht.1).mp <| pos_of_lt_add_right <| hfxα.symm ▸ hlt

      rw [add_assoc, ← add_smul, add_sub, add_comm t 1, add_sub_cancel, one_smul,
        ← Hi_.f.1.map_add, add_comm, sub_add_cancel] at this
      linarith
      done
  done


lemma DualOfVpolytope_compactHpolytope [FiniteDimensional ℝ E] {S : Set E} (hS : S.Finite)
  (hS0 : 0 ∈ interior (Vpolytope hS))
  : ∃ (H_ : Set (Halfspace E)) (hH_ : H_.Finite),
  Hpolytope hH_ = polarDual (Vpolytope hS) ∧ IsCompact (Hpolytope hH_):= by
  -- Last statment follows from polarDual_origin
  suffices hHeqVdual : ∃ (H_ : Set (Halfspace E)) (hH_ : H_.Finite),
    Hpolytope hH_ = polarDual (Vpolytope hS) from by
    rcases hHeqVdual with ⟨H_, hH_, hHeqVdual⟩
    refine ⟨ H_, hH_, hHeqVdual, ?_ ⟩
    exact hHeqVdual ▸ (polarDual_compact_if (Closed_Vpolytope hS) (Convex_Vpolytope hS) hS0)

  -- main proof
  use pointDual '' (Subtype.val ⁻¹' (S \ {0}))
  use (by
    apply Set.Finite.image
    apply Set.Finite.preimage _ _
    apply Set.injOn_of_injective
    exact Subtype.val_injective
    exact Set.Finite.diff hS {0}
    done)
  apply subset_antisymm
  · -- hard direction
    -- take x from Hpolytope of nonzero elements of S
    intro x hx
    -- Special treatment for x = 0
    cases' (em (x = 0)) with h h
    ·
      rw [h]
      exact polarDual_origin (Vpolytope hS)

    rw [mem_Hpolytope] at hx
    rw [mem_polarDual]
    intro p hp


    /-
      Magic: Since inner product is commutative over ℝ,
      DON'T imagine as x in each of the dual halfspaces of each s in S,
      instead, imagine S sitting inside the dual halfspace of x.
      halfspaces are convex hence Vpolytope of S sits inside the halfspace. QED
    -/
    let x' := (⟨ x, h ⟩ : { p : E // p ≠ 0 })
    have hx' : ↑x' = x := rfl
    rw [← hx', real_inner_comm, ←mem_pointDual]

    suffices h : S ⊆ SetLike.coe (pointDual x') from by
      apply convexHull_min h <| Halfspace_convex (pointDual x')
      exact hp

    -- Since x is in dual halfspace of each s in S, s is in dual halfspace of x
    intro s hs
    cases' (em (s = 0)) with h h
    ·
      exact h ▸ pointDual_origin x'

    specialize hx (pointDual ⟨ s, h ⟩) (Set.mem_image_of_mem _ ?_)
    ·
      rw [Set.mem_preimage, Subtype.coe_mk, Set.mem_diff]
      exact ⟨ hs, h ⟩

    rw [← Halfspace_mem, mem_pointDual, Subtype.coe_mk] at hx
    rw [mem_pointDual, Subtype.coe_mk, real_inner_comm]
    exact hx
    done

  · -- easy direction, simply need to show it is set intersection of a smaller set
    apply Set.sInter_subset_sInter
    apply Set.image_subset
    apply Set.image_subset
    rw [Set.preimage_subset_preimage_iff]
    apply subset_trans (by simp)  <| subset_convexHull _ _
    rw [Subtype.range_coe_subtype]
    intro x hx
    rw [Set.mem_diff, Set.mem_singleton_iff] at hx
    rw [Set.mem_setOf]
    exact hx.2
  done

lemma Vpolytope_of_Hpolytope : ∀ {H_ : Set (Halfspace E)} (hH_ : H_.Finite),
  IsCompact (Hpolytope hH_) →
  ∃ (S : Set E) (hS : S.Finite), Hpolytope hH_ = Vpolytope hS := by
  intro H_ hH_ hHcpt

  have hExHFinite : ((Hpolytope hH_).extremePoints ℝ).Finite := by
    have := ExtremePointsofHpolytope hH_

    let f := fun T : Set (Halfspace E) => ⋂₀ ((frontier <| SetLike.coe · ) '' T)
    let g : E ↪ Set E :=
      ⟨ fun x : E => Set.singleton x, Set.singleton_injective ⟩

    -- power set of H_ is finite
    rcases Set.Finite.exists_finset_coe hH_ with ⟨ Hfin, hHfin ⟩
    let PHfin := Hfin.powerset
    let PH := Finset.toSet '' PHfin.toSet
    have hPH : PH.Finite := PHfin.finite_toSet.image _

    -- f '' (power set of H_) is finite
    have hfPH : (f '' PH).Finite := hPH.image f

    -- g '' (Set.extremePoints ℝ (Hpolytope hH_)) ⊆ f '' (power set of H_) hence finite
    have hgfPH : g '' ((Hpolytope hH_).extremePoints ℝ) ⊆ f '' PH := by
      intro Sx hSx
      rcases hSx with ⟨ x, hx, rfl ⟩
      change {x} ∈ f '' PH
      rw [PH.mem_image]
      refine ⟨ Hpolytope.I H_ x, ?_, ?_ ⟩
      · -- x ∈ Hpolytope hH_
        rw [Set.mem_image]
        rcases (hH_.subset (Hpolytope.I_sub x)).exists_finset_coe  with ⟨ Ifin, hIfin ⟩
        refine ⟨ Ifin, ?_, hIfin ⟩
        rw [Finset.mem_coe, Finset.mem_powerset, ← Finset.coe_subset, hHfin, hIfin]
        exact Hpolytope.I_sub x
      · -- sInter of I H_ x is {x}
        rw [← ExtremePointsofHpolytope hH_ x (extremePoints_subset hx)]
        exact hx
      done

    have hgExFin : Set.Finite <| g '' (Set.extremePoints ℝ (Hpolytope hH_)) := Set.Finite.subset hfPH hgfPH

    -- Since g is embedding, Set.extremePoints ℝ (Hpolytope hH_) is finite
    have := hgExFin.preimage_embedding g
    rw [Function.Injective.preimage_image] at this
    exact this
    exact g.2
    done

  have : closure (convexHull ℝ ((Hpolytope hH_).extremePoints ℝ)) = Hpolytope hH_ :=
    closure_convexHull_extremePoints hHcpt (Convex_Hpolytope hH_)
  rw [← this, IsClosed.closure_eq]

  use (Hpolytope hH_).extremePoints ℝ
  use hExHFinite
  rfl

  exact Closed_Vpolytope hExHFinite
  done

theorem Hpolytope_of_Vpolytope_subsingleton [FiniteDimensional ℝ E] [Nontrivial E] {S : Set E}
  (hS : S.Finite) (hStrivial : Set.Subsingleton S):
    ∃ (H_ : Set (Halfspace E)) (hH_ : H_.Finite), Hpolytope hH_ = Vpolytope hS := by
  cases' hStrivial.eq_empty_or_singleton with hSempty hSsingleton
  ·
    rw [Vpolytope, hSempty, convexHull_empty]
    exact empty_Hpolytope
  ·
    rcases hSsingleton with ⟨ x, hx ⟩
    rcases @origin_Hpolytope E _ _ _ _ with ⟨ H_, hH_Fin, hH_ ⟩
    refine ⟨ Halfspace_translation x '' H_, hH_Fin.image (Halfspace_translation x), ?_ ⟩
    rw [Vpolytope, hx, convexHull_singleton, Hpolytope_translation hH_Fin, hH_, Set.singleton_add_singleton, zero_add]
  done

lemma Hpolytope_of_Vpolytope_0interior [FiniteDimensional ℝ E] {S : Set E} (hS : S.Finite)
  (hV0 : 0 ∈ interior (Vpolytope hS)):
  ∃ (H_ : Set (Halfspace E)) (hH_ : H_.Finite), Hpolytope hH_ = Vpolytope hS := by
  rcases DualOfVpolytope_compactHpolytope hS hV0 with ⟨ H_, hH_, hH_eq, hH_cpt ⟩
  rcases Vpolytope_of_Hpolytope hH_ hH_cpt with ⟨ S', hS', hS'eq ⟩
  have : 0 ∈ interior (Vpolytope hS') := by
    rw [←hS'eq, hH_eq, compact_polarDual_iff (Closed_Vpolytope hS)]
    exact Compact_Vpolytope hS
  rcases DualOfVpolytope_compactHpolytope hS' this with ⟨ H_', hH_', hH_'eq, _ ⟩
  refine ⟨ H_', hH_', ?_ ⟩
  rw [hH_'eq, ←hS'eq, hH_eq, doublePolarDual_self (Closed_Vpolytope hS) (Convex_Vpolytope hS) (interior_subset hV0)]
  done

lemma translationHomeo (x : E) : E ≃ₜ E where
  toFun := (· + x)
  invFun := (· + -x)
  left_inv := fun y => by simp
  right_inv := fun y => by simp
  continuous_toFun := by continuity
  continuous_invFun := by continuity

lemma translationHomeo.toFun.def (x : E) :
  ↑(translationHomeo x) = (· + x) := by
  unfold translationHomeo
  simp
  done

lemma Hpolytope_of_Vpolytope_interior [FiniteDimensional ℝ E] {S : Set E} (hS : S.Finite)
  (hVinteriorNonempty : (interior (Vpolytope hS)).Nonempty):
  ∃ (H_ : Set (Halfspace E)) (hH_ : H_.Finite), Hpolytope hH_ = Vpolytope hS := by
  let S' := S + {-hVinteriorNonempty.some}
  have hS' : S'.Finite := by exact (hS.translation (-hVinteriorNonempty.some))

  have : 0 ∈ interior (Vpolytope hS') := by
    rw [Vpolytope_translation hS, Set.add_singleton, ]
    have := @Homeomorph.image_interior _ _ _ _ (translationHomeo (-hVinteriorNonempty.some)) (Vpolytope hS)
    rw [translationHomeo.toFun.def] at this
    rw [← this]; clear this
    rw [← Set.add_singleton, Set.mem_translation, zero_sub,  neg_neg]
    exact hVinteriorNonempty.some_mem
    done

  rcases Hpolytope_of_Vpolytope_0interior hS' this with ⟨ H_', hH_', hH_'eq ⟩
  let H_ := (Halfspace_translation hVinteriorNonempty.some) '' H_'
  have hH_ : H_.Finite := hH_'.image _

  refine ⟨ H_, hH_, ?_ ⟩
  ext x
  rw [Hpolytope_translation, hH_'eq, Vpolytope_translation hS, ← Set.sub_eq_neg_add,
    Set.neg_add_cancel_right' hVinteriorNonempty.some]
  done

variable {E P : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [PseudoMetricSpace P] [NormedAddTorsor E P] [FiniteDimensional ℝ E]


lemma Vpolytope_of_Vpolytope_inter_cutSpace_fin {S : Set E} (hS : S.Finite) (hVinterior : Set.Nonempty (interior (Vpolytope hS)))
  {H_ : Set (Halfspace E)} (hH_ : H_.Finite) :
  ∃ (S' : Set E) (hS' : S'.Finite), Vpolytope hS' = Vpolytope hS ∩ Hpolytope hH_ := by
  rcases Hpolytope_of_Vpolytope_interior _ hVinterior with ⟨ H_', hH_', hHV ⟩
  have hH_inter := inter_Hpolytope H_' H_ hH_' hH_
  have : IsCompact (Vpolytope hS ∩ Hpolytope hH_) := (Compact_Vpolytope hS).inter_right (Closed_cutSpace H_)
  rw [← hHV, ← hH_inter] at this
  rcases Vpolytope_of_Hpolytope (hH_'.union hH_) this with ⟨ S', hS', hSV ⟩
  exact ⟨ S', hS', by rw [← hSV, ← hHV, ← hH_inter] ⟩
  done

lemma InDown_eq_DownIn {p : AffineSubspace ℝ P} [Nonempty { x // x ∈ p }] {S : Set P} (x : p):
  (AffineIsometryEquiv.VSubconst ℝ x) '' ((@Subtype.val P (fun x => x ∈ p)) ⁻¹' S) =
  (@Subtype.val E fun x => x ∈ p.direction) ⁻¹' (S -ᵥ ({x.1} : Set P)) := by
  ext y
  simp only [AffineIsometryEquiv.coe_VSubconst, Set.vsub_singleton, Set.mem_image, Set.mem_preimage,
    Set.mem_image, Subtype.exists, exists_and_left]
  constructor
  ·
    rintro ⟨ v, hvmemS, ⟨ hvmemp, rfl ⟩ ⟩
    refine ⟨ v, hvmemS, ?_ ⟩
    simp only [hvmemS, AffineSubspace.coe_vsub]
  ·
    rintro ⟨ v, hvmemS, h ⟩
    have := y.2
    rw [← h, AffineSubspace.vsub_right_mem_direction_iff_mem x.2] at this
    exact ⟨ v, hvmemS, this, Subtype.val_injective ((AffineSubspace.coe_vsub _ _ x) ▸ h) ⟩
  done


lemma Nonempty_iff_Nonempty_interior_in_direction {S : Set E}{s : E} (hs : s ∈ S) (hS : Nonempty S) :
    (interior ((@AffineIsometryEquiv.VSubconst ℝ (affineSpan ℝ S).direction (affineSpan ℝ S) _ _ _ _ (AffineSubspace.toNormedAddTorsor (affineSpan ℝ (S))) ⟨ s, by apply subset_affineSpan; exact hs ⟩ ) ''
      ((@Subtype.val E fun x => x ∈ (affineSpan ℝ S)) ⁻¹' ((convexHull ℝ) S)))).Nonempty := by
  rw [Set.nonempty_coe_sort, ← @convexHull_nonempty_iff ℝ, ← intrinsicInterior_nonempty (convex_convexHull ℝ S),
    intrinsicInterior, Set.image_nonempty, affineSpan_convexHull] at hS
  rw [← AffineIsometryEquiv.coe_toHomeomorph, ← Homeomorph.image_interior, Set.image_nonempty]
  exact hS


theorem MainTheoremOfPolytopes [FiniteDimensional ℝ E] [Nontrivial E] :
  (∀ (S : Set E) (hS : S.Finite),
    ∃ (H_ : Set (Halfspace E)) (hH_ : H_.Finite),
    Hpolytope hH_ = Vpolytope hS) ∧
  ∀ {H_ : Set (Halfspace E)} (hH_ : H_.Finite),
    IsCompact (Hpolytope hH_) →
    ∃ (S : Set E) (hS : S.Finite), Hpolytope hH_ = Vpolytope hS := by
  constructor
  · -- 1.
    intro S hS
    /-
    1. ConvexHull always have an intrinsic interior
    2. Any AffineSubspaces are intersections of hyperplanes
    3. Any hyperplane is an intersection of two Halfspaces
    4. Take union of the set of Halfspaces for Hpolytope in the affineSpan and for the affineSpan
    -/
    cases' em (S.Nontrivial) with hSnontrivial hStrivial
    · -- S is nontrivial
      -- Instance set up
      have := Set.nontrivial_coe_sort.mpr hSnontrivial
      have hSnonempty := hSnontrivial.nonempty
      have := Set.nonempty_coe_sort.mpr hSnonempty

      rcases hSnontrivial.nonempty with ⟨ s, hs ⟩
      have hsaff : s ∈ affineSpan ℝ S := by apply subset_affineSpan; exact hs
      let SpanS := affineSpan ℝ S
      let s' : SpanS := ⟨ s, hsaff ⟩

      rcases (Nonempty_iff_Nonempty_interior_in_direction hs this) with ⟨ x, hx ⟩

      have : ∃ S', S'.Finite ∧ convexHull ℝ S' = (AffineIsometryEquiv.VSubconst ℝ s') '' ((@Subtype.val E fun x => x ∈ SpanS) ⁻¹' ((convexHull ℝ) S : Set E)) := by
        rw [InDown_eq_DownIn, ← @convexHull_singleton ℝ, Set.vsub_eq_sub, ← convexHull_sub,
          ← Submodule.coeSubtype]
        refine ⟨ Subtype.val ⁻¹' (S - {s}), ?_, ?_ ⟩
        ·
          apply Set.Finite.preimage (Set.injOn_of_injective Subtype.val_injective _)
          rw [Set.sub_singleton]
          exact hS.image _
        ·
          rw [← Submodule.coeSubtype, ← LinearMap.coe_toAffineMap, ← AffineMap.preimage_convexHull]
          all_goals (try rw [AffineMap.toFun_eq_coe])
          all_goals rw [LinearMap.coe_toAffineMap, Submodule.coeSubtype]
          exact Subtype.val_injective

          rw [Subtype.range_coe_subtype]
          exact AffineSubspace.direction_subset_subset (subset_affineSpan ℝ S)
            (subset_trans (Set.singleton_subset_iff.mpr hs) (subset_affineSpan ℝ S))
        done


      rcases this with ⟨ S', hS'Fin, hS'eq ⟩
      rw [← hS'eq] at hx
      have hS' : (interior (Vpolytope hS'Fin)).Nonempty := Set.nonempty_of_mem hx

      rcases @Hpolytope_of_Vpolytope_interior SpanS.direction _ _ _ _ _ hS'Fin hS' with ⟨ H_''1, hH''1, hHV ⟩

      let H_'1 : Set (Halfspace E) := (Halfspace.val SpanS.direction) '' H_''1
      have hH_'1 : H_'1.Finite := Set.Finite.image _ hH''1

      rcases Submodule_cutspace SpanS.direction with ⟨ H_'2, hH_'2, hH_'2Span' ⟩
      have hH_'2Span: Hpolytope hH_'2 = SpanS.direction := hH_'2Span'.symm; clear hH_'2Span'

      let H_' : Set (Halfspace E) := Halfspace_translation s '' (H_'1 ∪ H_'2)
      have hH_' : H_'.Finite := Set.Finite.image _ (Set.Finite.union hH_'1 hH_'2)
      have hH_'12 := inter_Hpolytope H_'1 H_'2 hH_'1 hH_'2

      have : Nontrivial SpanS.direction := by
        apply AffineSubspace.direction_nontrivial_of_nontrivial
        exact affineSpan_nontrivial ℝ (Set.nontrivial_coe_sort.mpr hSnontrivial)

      refine ⟨ H_', hH_', ?_ ⟩
      rw [Hpolytope_translation, hH_'12, hH_'2Span, Hpolytope, ← Set.Nonempty.sInter_inter_comm, Set.image_image,
        Set.image_image, @Set.image_congr' _ _ _ _ (H_''1) (Halfspace.val_eq' SpanS.direction),
        ← Set.image_image, Set.sInter_image, ← Set.Nonempty.image_sInter ?_ (Subtype.val_injective)]
      change Subtype.val '' Hpolytope hH''1 + {s} = Vpolytope hS
      rw [hHV, Vpolytope, hS'eq]
      change Subtype.val '' ((AffineIsometryEquiv.toHomeomorph (AffineIsometryEquiv.VSubconst ℝ s')) '' (Subtype.val ⁻¹' (convexHull ℝ) S)) + {s} = Vpolytope hS
      rw [AffineIsometryEquiv.coe_toHomeomorph]

      rw [InDown_eq_DownIn, Set.vsub_eq_sub]
      change ((↑) : SpanS.direction → E) '' (((↑) : SpanS.direction → E) ⁻¹' ((convexHull ℝ) S - {s})) + {s} = Vpolytope hS
      rw [Subtype.image_preimage_coe, Set.inter_eq_self_of_subset_right ?_, Set.neg_add_cancel_right', Vpolytope]
      exact AffineSubspace.direction_subset_subset (convexHull_subset_affineSpan S)
              (subset_trans (Set.singleton_subset_iff.mpr hs) (subset_affineSpan ℝ S))

      -- In case Span of S has dim = 0
      all_goals (apply Set.Nonempty.image)
      all_goals (try (change Set.Nonempty (Halfspace.val (AffineSubspace.direction SpanS) '' H_''1)))
      all_goals (try apply Set.Nonempty.image)
      all_goals (by_contra h)
      all_goals (rw [Set.not_nonempty_iff_eq_empty] at h)
      all_goals (rw [Hpolytope, h, Set.image_empty, Set.sInter_empty] at hHV)
      all_goals (exact IsCompact.ne_univ (Compact_Vpolytope hS'Fin) hHV.symm)
      done

    · -- S is trivial
      rw [Set.not_nontrivial_iff] at hStrivial
      exact Hpolytope_of_Vpolytope_subsingleton _ hStrivial
  · -- 2.
    exact Vpolytope_of_Hpolytope
  done
