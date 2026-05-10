/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import LeanPool.FormalLearningTheory.Complexity.Generalization.Core

universe u v


section FinBlockInfrastructure

open Equiv in
/-- Extract block j from a flat array of k*m elements, using finProdFinEquiv. -/
def block_extract {α : Type*} (k m : ℕ) (S : Fin (k * m) → α) (j : Fin k) : Fin m → α :=
  fun i => S (finProdFinEquiv (j, i))

/-- Boolean majority vote: returns true iff strictly more than half the votes are true. -/
def majority_vote (k : ℕ) (votes : Fin k → Bool) : Bool :=
  decide (2 * (Finset.univ.filter (fun j => votes j = true)).card > k)

/-- Block index sets are disjoint for distinct blocks. -/
lemma block_extract_disjoint (k m : ℕ) (j₁ j₂ : Fin k) (hne : j₁ ≠ j₂) :
    Disjoint
      (Finset.image (fun i : Fin m => finProdFinEquiv (j₁, i)) Finset.univ)
      (Finset.image (fun i : Fin m => finProdFinEquiv (j₂, i)) Finset.univ) := by
  rw [Finset.disjoint_iff_ne]
  intro a ha b hb
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at ha hb
  obtain ⟨i₁, rfl⟩ := ha
  obtain ⟨i₂, rfl⟩ := hb
  intro heq
  exact hne (congr_arg Prod.fst (finProdFinEquiv.injective heq))

/-- Block extraction is measurable: extracting block j from a pi-type is measurable. -/
lemma block_extract_measurable {X : Type*} [MeasurableSpace X]
    (k m : ℕ) (j : Fin k) :
    Measurable (fun (ω : Fin (k * m) → X) => block_extract k m ω j) := by
  exact measurable_pi_lambda _ (fun i => measurable_pi_apply _)

/-- Block extractions are independent under the product measure.
    Key infrastructure for boosting (D4) and probability amplification. -/
lemma iIndepFun_block_extract {X : Type*} [MeasurableSpace X]
    (k m : ℕ) (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D] :
    ProbabilityTheory.iIndepFun (β := fun _ : Fin k => Fin m → X)
      (fun (j : Fin k) (ω : Fin (k * m) → X) => block_extract k m ω j)
      (MeasureTheory.Measure.pi (fun _ : Fin (k * m) => D)) := by
  open MeasureTheory MeasureTheory.Measure ProbabilityTheory Equiv in
  -- The currying MeasurableEquiv: Fin(k*m) → X  ≃ᵐ  Fin k → (Fin m → X)
  set pcl := MeasurableEquiv.piCongrLeft (fun _ : Fin k × Fin m => X) finProdFinEquiv.symm
  set cur := MeasurableEquiv.curry (Fin k) (Fin m) X
  set e : (Fin (k * m) → X) ≃ᵐ (Fin k → Fin m → X) := pcl.trans cur
  -- block_extract = e pointwise
  have he : ∀ j ω, block_extract k m ω j = e ω j := by
    intro j ω; ext i
    simp only [block_extract, e, MeasurableEquiv.trans_apply, pcl, cur]
    simp [MeasurableEquiv.piCongrLeft, piCongrLeft_apply, MeasurableEquiv.curry,
      Function.curry]
  -- Rewrite goal to use e
  simp_rw [he]
  -- Now goal: iIndepFun (fun j ω => e ω j) (Measure.pi (fun _ => D))
  -- Apply the map characterization
  set μ := Measure.pi (fun _ : Fin (k * m) => D)
  -- AEMeasurable: each component is measurable
  have hmeas : ∀ j : Fin k, AEMeasurable (fun ω => e ω j) μ :=
    fun j => ((measurable_pi_apply j).comp e.measurable).aemeasurable
  rw [iIndepFun_iff_map_fun_eq_pi_map hmeas]
  -- Goal: μ.map (fun ω j => e ω j) = Measure.pi (fun j => μ.map (fun ω => e ω j))
  -- LHS: μ.map (fun ω j => e ω j) = μ.map e
  have hlhs : (fun (ω : Fin (k * m) → X) (j : Fin k) => e ω j) = e := by
    ext ω j; rfl
  rw [hlhs]
  -- Define the nested product measure
  set D' : Fin k → Measure (Fin m → X) := fun _ => Measure.pi (fun _ : Fin m => D)
  -- Step 1: μ.map pcl preserves measure
  have hpcl : MeasurePreserving pcl μ (Measure.pi (fun _ : Fin k × Fin m => D)) :=
    measurePreserving_piCongrLeft (fun _ : Fin k × Fin m => D) finProdFinEquiv.symm
  -- Step 2: (flat on Fin k × Fin m).map cur = nested product
  have hcur : (Measure.pi (fun _ : Fin k × Fin m => D)).map cur = Measure.pi D' := by
    have h1 : Measure.pi (fun _ : Fin k × Fin m => D) =
        infinitePi (fun _ : Fin k × Fin m => D) :=
      (infinitePi_eq_pi (μ := fun _ : Fin k × Fin m => D)).symm
    rw [h1]
    have h3 : D' = fun _ : Fin k => infinitePi (fun _ : Fin m => D) := by
      funext; exact (infinitePi_eq_pi (μ := fun _ : Fin m => D)).symm
    have h2 : Measure.pi D' = infinitePi D' :=
      (infinitePi_eq_pi (μ := D')).symm
    rw [h2, h3]
    exact infinitePi_map_curry (fun _ : Fin k => fun _ : Fin m => D)
  -- Step 3: μ.map e = Measure.pi D'
  have hmap_e : μ.map e = Measure.pi D' := by
    have : (e : (Fin (k * m) → X) → (Fin k → Fin m → X)) = cur ∘ pcl := rfl
    rw [this, ← map_map cur.measurable pcl.measurable, hpcl.map_eq, hcur]
  rw [hmap_e]
  -- RHS: Measure.pi (fun j => μ.map (fun ω => e ω j))
  -- Each marginal: μ.map (fun ω => e ω j) = D' j
  congr 1
  ext j : 1
  -- μ.map (fun ω => e ω j) = j-th marginal of μ.map e = D' j
  have hcomp : (fun ω => e ω j) = (fun f => f j) ∘ (e : (Fin (k * m) → X) → _) := rfl
  rw [hcomp, ← map_map (measurable_pi_apply j) e.measurable, hmap_e]
  exact ((measurePreserving_eval D' j).map_eq).symm

end FinBlockInfrastructure

section PACTheoremHelpers
/-- Shattering lifting: if T is shattered by C and f : ↥T → Bool, then
    there exists c ∈ C that agrees with f on all of T. -/
theorem shatters_realize {X : Type u} {C : ConceptClass X Bool} {T : Finset X}
    (hT : Shatters X C T) (f : ↥T → Bool) :
    ∃ c ∈ C, ∀ x : ↥T, c (x : X) = f x :=
  hT f

/-- Key counting lemma: for any h : ↥T → Bool on a shattered set T with |T| ≥ 2,
    there exists c ∈ C with #{x ∈ T | c x ≠ h x} > |T|/4.
    Lifts exists_many_disagreements through shattering. -/
theorem shatters_hard_labeling {X : Type u} {C : ConceptClass X Bool} {T : Finset X}
    (hT : Shatters X C T) (h : ↥T → Bool) (hcard : 2 ≤ T.card) :
    ∃ c ∈ C, T.card <
      4 * (Finset.univ.filter fun x : ↥T => c (x : X) ≠ h x).card := by
  classical
  have hcard' : 2 ≤ Fintype.card ↥T := by rwa [Fintype.card_coe]
  obtain ⟨f, hf⟩ := exists_many_disagreements h hcard'
  obtain ⟨c, hcC, hcf⟩ := shatters_realize hT f
  refine ⟨c, hcC, ?_⟩
  convert hf using 2
  · exact (Fintype.card_coe T).symm
  · congr 1; ext x; simp [hcf x]

/-- NFL per-sample lemma for shattered sets: for ANY fixed sample xs and
    ANY hypothesis h, there exists c ∈ C agreeing with h on sample points
    but with high error (> 1 / 4) on the shattered set T.
    Uses the counting argument on unseen points via disagreement_sum_eq. -/
theorem nfl_per_sample_shattered {X : Type u} {C : ConceptClass X Bool}
    {T : Finset X} (hT : Shatters X C T) {m : ℕ} (hTcard : 2 * m < T.card)
    (xs : Fin m → X) (h : X → Bool) :
    ∃ c ∈ C, (∀ i : Fin m, xs i ∈ T → c (xs i) = h (xs i)) ∧
      T.card < 4 * (T.filter fun x => c x ≠ h x).card := by
  classical
  -- Define adversarial labeling: agree with h on seen points, disagree on unseen
  let f : ↥T → Bool := fun ⟨x, _⟩ =>
    if x ∈ Set.range xs then h x else !h x
  -- Shattering gives c ∈ C realizing f
  obtain ⟨c, hcC, hcf⟩ := hT f
  refine ⟨c, hcC, ?_, ?_⟩
  · -- c agrees with h on sample points that are in T
    intro i hi
    have hcfi : c (xs i) = f ⟨xs i, hi⟩ := hcf ⟨xs i, hi⟩
    simp only [f, Set.mem_range_self, ↓reduceIte] at hcfi
    exact hcfi
  · -- c disagrees with h on all unseen points of T
    -- So the disagreement count ≥ |T \ range(xs)| ≥ T.card - m > T.card/2
    -- First: every unseen point in T has c x ≠ h x
    have hunseen : ∀ x ∈ T, x ∉ Set.range xs → c x ≠ h x := by
      intro x hxT hxns
      have hcfx : c x = f ⟨x, hxT⟩ := hcf ⟨x, hxT⟩
      simp only [f, hxns, ↓reduceIte] at hcfx
      rw [hcfx]; cases h x <;> decide
    -- The disagreement filter contains T \ image of xs
    -- Let seen = T.filter (· ∈ range xs)
    set disagree := T.filter (fun x => c x ≠ h x) with hdisagree_def
    -- T \ (Finset.image xs Finset.univ) ⊆ disagree
    have hsub : T \ Finset.image xs Finset.univ ⊆ disagree := by
      intro x hx
      simp only [Finset.mem_sdiff, Finset.mem_image, Finset.mem_univ, true_and] at hx
      simp only [hdisagree_def, Finset.mem_filter]
      exact ⟨hx.1, hunseen x hx.1 (by
        intro ⟨i, hi⟩; exact hx.2 ⟨i, hi⟩)⟩
    -- |T \ image xs| ≥ T.card - m
    have hsdiff_card : T.card - m ≤ (T \ Finset.image xs Finset.univ).card := by
      have himg_le : (Finset.image xs Finset.univ).card ≤ m := by
        calc (Finset.image xs Finset.univ).card
            ≤ Fintype.card (Fin m) := Finset.card_image_le
          _ = m := Fintype.card_fin m
      -- |T \ S| + |T ∩ S| = |T| (Finset.card_sdiff_add_card_inter)
      have hkey := Finset.card_sdiff_add_card_inter T (Finset.image xs Finset.univ)
      -- |T ∩ S| ≤ |S| ≤ m
      have hinter_le : (T ∩ Finset.image xs Finset.univ).card ≤ m :=
        le_trans (Finset.card_le_card Finset.inter_subset_right) himg_le
      omega
    -- Combine: disagree.card ≥ T.card - m
    have hdisagree_ge : T.card - m ≤ disagree.card :=
      le_trans hsdiff_card (Finset.card_le_card hsub)
    -- Since 2m < T.card: T.card - m > T.card / 2, so 4*(T.card - m) > 2*T.card > T.card
    -- More precisely: T.card < 4 * (T.card - m) ≤ 4 * disagree.card
    calc T.card < 4 * (T.card - m) := by omega
      _ ≤ 4 * disagree.card := by omega
/-- If VCDim = ⊤, then C is not PAC learnable.
    Proof: for any learner L with sample function mf, pick ε = 1 / 4, δ = 1 / 4.
    Let m = mf(1 / 4, 1 / 4). Since VCDim = ⊤, ∃ shattered set S with |S| ≥ 2m.
    Put D = uniform on S. For random labeling, any m-sample learner
    has expected error ≥ 1 / 4 on unseen points.
    This is the core of pac_imp_vcdim_finite (contrapositive direction). -/
theorem vcdim_infinite_not_pac (X : Type u) [MeasurableSpace X]
    -- proof-size-limit-ok: ported formal learning theory proof.
    [MeasurableSingletonClass X]
    (C : ConceptClass X Bool) (hinf : VCDim X C = ⊤) :
    ¬ PACLearnable X C := by
  -- Assume PACLearnable for contradiction
  intro ⟨L, mf, hpac⟩
  -- Step 1: VCDim = ⊤ → for any n, ∃ shattered T with |T| > n
  have hvcdim_unbounded : ∀ b : WithTop ℕ, b < ⊤ → ∃ T, ∃ _ : Shatters X C T,
      b < (T.card : WithTop ℕ) := by
    have := (iSup₂_eq_top
      (fun (T : Finset X) (_ : Shatters X C T) => (T.card : WithTop ℕ))).mp
    rw [VCDim] at hinf
    exact this hinf
  -- Step 2: Fix ε = 1 / 4, δ = 1 / 4, m = mf(1 / 4)(1 / 4)
  set m := mf (1 / 4 : ℝ) (1 / 4 : ℝ) with hm_def
  -- Step 3: Get shattered T with |T| > 2m
  obtain ⟨T, hTshat, hTcard⟩ := hvcdim_unbounded (2 * m) (WithTop.coe_lt_top _)
  -- hTcard : (2 * ↑m : WithTop ℕ) < (T.card : WithTop ℕ)
  have hTcard_nat : 2 * m < T.card := by exact_mod_cast hTcard
  -- Step 4: From PAC guarantee, L works for ε=1 / 4, δ=1 / 4
  have hpac14 := hpac (1 / 4 : ℝ) (1 / 4 : ℝ) (by norm_num) (by norm_num)
  -- Step 5: T is nonempty (|T| > 2m ≥ 0)
  have hTne : T.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h; simp [h] at hTcard_nat
  -- Step 6: Derive contradiction.
  -- We need: ∃ D (prob measure on X), ∃ c ∈ C, PAC guarantee fails.
  -- hpac14 says: ∀ D prob, ∀ c ∈ C, Pr[err ≤ 1 / 4] ≥ 3 / 4.
  -- We construct D and find c ∈ C where Pr[err ≤ 1 / 4] < 3 / 4.
  suffices ∃ (D : MeasureTheory.Measure X), MeasureTheory.IsProbabilityMeasure D ∧
      ∃ c ∈ C,
        MeasureTheory.Measure.pi (fun _ : Fin m => D)
          { xs : Fin m → X |
            D { x | L.learn (fun i => (xs i, c (xs i))) x ≠ c x }
              ≤ ENNReal.ofReal (1 / 4 : ℝ) }
          < ENNReal.ofReal (1 - 1 / 4 : ℝ) by
    obtain ⟨D, hDprob, c, hcC, hfail⟩ := this
    exact not_le.mpr hfail (hpac14 D hDprob c hcC)
  -- Construct D = uniform on ↥T pushed to X via Subtype.val
  classical
  letI msT : MeasurableSpace ↥T := ⊤
  haveI : @MeasurableSingletonClass ↥T ⊤ :=
    ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  have hTne_type : Nonempty ↥T := hTne.coe_sort
  have hTpos : 0 < Fintype.card ↥T := by rw [Fintype.card_coe]; omega
  let D_sub := @uniformMeasure ↥T ⊤ _ hTne_type
  have hD_sub_prob : @MeasureTheory.IsProbabilityMeasure ↥T ⊤ D_sub :=
    @uniformMeasure_isProbability ↥T ⊤ _ ⟨fun _ => trivial⟩ hTne_type hTpos
  have hval_meas : @Measurable ↥T X ⊤ _ Subtype.val :=
    fun _ _ => MeasurableSpace.measurableSet_top
  let D := @MeasureTheory.Measure.map ↥T X ⊤ _ Subtype.val D_sub
  have hDprob : MeasureTheory.IsProbabilityMeasure D := by
    constructor
    show D Set.univ = 1
    simp only [D, MeasureTheory.Measure.map_apply hval_meas MeasurableSet.univ]
    have : Subtype.val ⁻¹' (Set.univ : Set X) = (Set.univ : Set ↥T) := Set.preimage_univ
    rw [this]; exact hD_sub_prob.measure_univ
  refine ⟨D, hDprob, ?_⟩
  -- Double-counting + measure bridge (see analysis in pac_lower_bound_core).
  -- For each f : ↥T → Bool, shattering gives c_f ∈ C with c_f|_T = f.
  -- For fixed xs, group f's by f|_{range(xs)}. Within each group (same training data),
  -- h₀ is fixed. Pair f_unseen with !f_unseen: disagree sum = |unseen| ≥ d-m > d/2,
  -- so at most one per pair has ≤ d/4 disagreements. Per group ≤ 2^{u-1}, total ≤ 2^{d-1}.
  -- Pigeonhole over f: ∃ f₀ with #{xs : error(c_{f₀}) ≤ 1 / 4} ≤ d^m/2.
  -- Measure bridge: Pr = count/d^m ≤ 1 / 2 < 3 / 4.
  --
  -- Factor into two sorry'd substeps:
  -- (A) Combinatorial: ∃ f₀ : ↥T → Bool, counting bound on good xs.
  -- (B) Measure bridge: counting → Measure.pi.
  set d := T.card with hd_def
  have h2m_lt_d : 2 * m < d := hTcard_nat
  have hd_pos : 0 < d := by omega
  -- Substep A: combinatorial double-counting + pigeonhole
  -- Apply nfl_counting_core. It uses `classical` for Fintype instances, which
  -- may differ from the outer Fintype. Since all Fintype instances on a given type
  -- give the same cardinalities and univ, we use Subsingleton to reconcile.
  obtain ⟨f₀, c₀, hc₀C, hc₀f, hcount⟩ := nfl_counting_core hTshat hTcard_nat L
  -- Substep B (measure bridge):
  -- Convert: 2 · #{good xs on ↥T} ≤ card(Fin m → ↥T)
  -- to: Measure.pi D {xs : Fin m → X | D-error ≤ 1 / 4} ≤ 1 / 2 < 3 / 4.
  refine ⟨c₀, hc₀C, ?_⟩
  -- Substep B: measure bridge from counting bound to Measure.pi probability bound.
  -- B1: Subtype.val : ↥T → X is a MeasurableEmbedding.
  have hT_meas : MeasurableSet (T : Set X) := T.measurableSet
  have hval_emb : @MeasurableEmbedding ↥T X ⊤ _ Subtype.val := {
    injective := Subtype.val_injective
    measurable := hval_meas
    measurableSet_image' := fun {s} _ => by
      exact Set.Finite.measurableSet (Set.Finite.subset T.finite_toSet
        (fun x hx => by obtain ⟨⟨y, hy⟩, _, rfl⟩ := hx; exact Finset.mem_coe.mpr hy)) }
  -- B2: D S = D_sub(val⁻¹' S) for all sets S.
  have hD_val : ∀ S : Set X, D S = D_sub (Subtype.val ⁻¹' S) :=
    fun S => hval_emb.map_apply D_sub S
  -- B3: valProd and MeasurableEmbedding.
  let valProd : (Fin m → ↥T) → (Fin m → X) := fun xs i => (xs i).val
  have hvalProd_emb : @MeasurableEmbedding (Fin m → ↥T) (Fin m → X)
      (@MeasurableSpace.pi (Fin m) (fun _ => ↥T) (fun _ => ⊤))
      MeasurableSpace.pi valProd := {
    injective := fun a b hab => funext fun i => Subtype.val_injective (congr_fun hab i)
    measurable := by
      rw [@measurable_pi_iff]
      intro i
      exact hval_meas.comp (@measurable_pi_apply (Fin m) (fun _ => ↥T)
        (fun _ => (⊤ : MeasurableSpace ↥T)) i)
    measurableSet_image' := fun {s} _ =>
      (Set.toFinite s |>.image valProd).measurableSet }
  -- B4: Measure.pi D = (Measure.pi D_sub).map valProd via pi_map_pi.
  -- We use pi_map_pi:
  -- (Measure.pi μ).map (fun x i => f i (x i)) = Measure.pi (fun i => (μ i).map (f i))
  -- with μ = fun _ => D_sub, f = fun _ => Subtype.val, so
  -- (Measure.pi D_sub).map valProd = Measure.pi (fun _ => D_sub.map val) = Measure.pi (fun _ => D).
  have hpi_map : MeasureTheory.Measure.pi (fun _ : Fin m => D) =
      (@MeasureTheory.Measure.pi (Fin m) (fun _ => ↥T) _ (fun _ => ⊤)
        (fun _ => D_sub)).map valProd := by
    -- Work with the explicit discrete measurable space on ↥T
    letI : ∀ (_ : Fin m), MeasureTheory.SigmaFinite
        (@MeasureTheory.Measure.map ↥T X ⊤ _ Subtype.val D_sub) := fun _ => by
      change MeasureTheory.SigmaFinite D; exact inferInstance
    -- pi_map_pi applied to μ i = D_sub on (↥T, ⊤), f i = Subtype.val
    conv_lhs =>
      rw [show (fun (_ : Fin m) => D) =
        fun (_ : Fin m) => @MeasureTheory.Measure.map ↥T X ⊤ _ Subtype.val D_sub from rfl]
    symm
    -- pi_map_pi: (Measure.pi μ).map (fun x i => f i (x i)) = Measure.pi (fun i => (μ i).map (f i))
    -- @pi_map_pi args: ι, [Fintype ι], X, Y, mX, μ, [∀ i, MS (Y i)], f, [hμ SigmaFinite], hf
    have key := @MeasureTheory.Measure.pi_map_pi (Fin m) inferInstance
      (fun _ => ↥T) (fun _ => X) (fun _ => (⊤ : MeasurableSpace ↥T))
      (fun _ => D_sub) inferInstance (fun _ => @Subtype.val X (· ∈ T))
      inferInstance (fun _ => hval_meas.aemeasurable)
    -- convert resolves the beta-reduction mismatch.
    convert key using 1
  -- B5: Measure.pi D S = Measure.pi D_sub (valProd⁻¹' S) for all S.
  have hpi_val : ∀ S : Set (Fin m → X),
      MeasureTheory.Measure.pi (fun _ : Fin m => D) S =
      @MeasureTheory.Measure.pi (Fin m) (fun _ => ↥T) _ (fun _ => ⊤)
        (fun _ => D_sub) (valProd ⁻¹' S) := fun S => by
    rw [hpi_map]; exact hvalProd_emb.map_apply _ S
  -- B6: Define good set and counting set.
  set good_X : Set (Fin m → X) := { xs |
    D { x | L.learn (fun i => (xs i, c₀ (xs i))) x ≠ c₀ x }
      ≤ ENNReal.ofReal (1 / 4 : ℝ) } with good_X_def
  set count_finset := Finset.univ.filter fun xs : Fin m → ↥T =>
    (Finset.univ.filter fun t : ↥T =>
      c₀ ((↑t : X)) ≠
        L.learn (fun i => ((↑(xs i) : X), c₀ (↑(xs i)))) (↑t)).card * 4
    ≤ d with count_finset_def
  -- B7: Preimage equivalence.
  have hpre_eq : valProd ⁻¹' good_X = (↑count_finset : Set (Fin m → ↥T)) := by
    ext xs_T
    simp only [Set.mem_preimage, good_X_def, Set.mem_setOf_eq, valProd,
      count_finset_def, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
    set h_val := L.learn (fun i => ((↑(xs_T i) : X), c₀ (↑(xs_T i))))
    -- D {error} = D_sub {error on T}
    have herr : D { x | h_val x ≠ c₀ x } =
        D_sub { t : ↥T | c₀ (↑t) ≠ h_val (↑t) } := by
      rw [hD_val]; congr 1; ext ⟨t, _⟩; exact ne_comm
    -- D_sub {P} = |{P}| / d (uniform measure)
    have hunif : D_sub { t : ↥T | c₀ (↑t) ≠ h_val (↑t) } =
        ((Finset.univ.filter fun t : ↥T => c₀ (↑t) ≠ h_val (↑t)).card : ENNReal) /
          (d : ENNReal) := by
      simp only [D_sub, uniformMeasure, MeasureTheory.Measure.smul_apply, smul_eq_mul]
      rw [@MeasureTheory.Measure.count_apply_finite' ↥T ⊤ _
        (Set.toFinite _) MeasurableSpace.measurableSet_top]
      simp only [Fintype.card_coe, one_div, ne_eq, Set.Finite.toFinset_setOf,
        Finset.univ_eq_attach]
      rw [ENNReal.div_eq_inv_mul]
    rw [herr, hunif]
    -- k / d ≤ ofReal(1 / 4) ↔ k * 4 ≤ d for natural numbers
    set k := (Finset.univ.filter fun t : ↥T => c₀ (↑t) ≠ h_val (↑t)).card
    have hd_ne : (d : ENNReal) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hd_nt : (d : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top d
    constructor
    · -- k/d ≤ 1 / 4 → k*4 ≤ d
      intro hle
      rw [ENNReal.div_le_iff hd_ne hd_nt] at hle
      rw [show ENNReal.ofReal (1 / 4 : ℝ) = (4 : ENNReal)⁻¹ from by
        rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ) < 4)]
        norm_num, mul_comm] at hle
      have h4 : (k : ENNReal) * 4 ≤ (d : ENNReal) :=
        calc (k : ENNReal) * 4
            ≤ (d : ENNReal) * (4 : ENNReal)⁻¹ * 4 := mul_le_mul_left hle 4
          _ = (d : ENNReal) := by
              rw [mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), mul_one]
      exact_mod_cast h4
    · -- k*4 ≤ d → k/d ≤ 1 / 4
      intro hle
      rw [ENNReal.div_le_iff hd_ne hd_nt]
      rw [show ENNReal.ofReal (1 / 4 : ℝ) = (4 : ENNReal)⁻¹ from by
        rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ) < 4)]
        norm_num, mul_comm]
      have hk4 : (k : ENNReal) * 4 ≤ (d : ENNReal) := by exact_mod_cast hle
      calc (k : ENNReal) = (k : ENNReal) * 4 * (4 : ENNReal)⁻¹ := by
              rw [mul_assoc, mul_comm 4 (4 : ENNReal)⁻¹,
                  ENNReal.inv_mul_cancel (by norm_num) (by norm_num), mul_one]
            _ ≤ (d : ENNReal) * (4 : ENNReal)⁻¹ := mul_le_mul_left hk4 _
  -- B8: Main bound.
  rw [show ENNReal.ofReal (1 - 1 / 4 : ℝ) = ENNReal.ofReal (3 / 4 : ℝ) from by norm_num]
  have hgoal_eq : MeasureTheory.Measure.pi (fun _ : Fin m => D) good_X =
      @MeasureTheory.Measure.pi (Fin m) (fun _ => ↥T) _ (fun _ => ⊤)
        (fun _ => D_sub) (↑count_finset) := by
    rw [hpi_val good_X, hpre_eq]
  -- B9: Bound Measure.pi D_sub ↑count_finset ≤ 1 / 2 using hcount.
  -- Product of uniform measures on d-element type gives uniform on d^m-element product.
  -- μ(count_finset) = |count_finset| / d^m ≤ 1 / 2.
  have hpi_sub_bound : @MeasureTheory.Measure.pi (Fin m) (fun _ => ↥T) _ (fun _ => ⊤)
      (fun _ => D_sub) (↑count_finset) ≤ ENNReal.ofReal (1 / 2 : ℝ) := by
    set μ_pi := @MeasureTheory.Measure.pi (Fin m) (fun _ => ↥T) _ (fun _ => ⊤)
      (fun _ => D_sub) with hμ_pi_def
    -- Key instances for the discrete product type
    haveI inst_msc_pi : @MeasurableSingletonClass (Fin m → ↥T)
        (@MeasurableSpace.pi (Fin m) (fun _ => ↥T) (fun _ => ⊤)) :=
      @Pi.instMeasurableSingletonClass (Fin m) (fun _ => ↥T) (fun _ => ⊤)
        inferInstance (fun _ => ⟨fun _ => MeasurableSpace.measurableSet_top⟩)
    haveI : @MeasureTheory.IsFiniteMeasure ↥T ⊤ D_sub := by
      constructor; rw [hD_sub_prob.measure_univ]; exact ENNReal.one_lt_top
    haveI : @MeasureTheory.SigmaFinite ↥T ⊤ D_sub :=
      @MeasureTheory.IsFiniteMeasure.toSigmaFinite ↥T ⊤ D_sub inferInstance
    -- D_sub {t} = 1/d for all t : ↥T (uniform measure singleton)
    have hD_sub_singleton : ∀ t : ↥T, D_sub {t} = 1 / (d : ENNReal) := by
      intro t
      simp only [D_sub, uniformMeasure, MeasureTheory.Measure.smul_apply, smul_eq_mul]
      rw [@MeasureTheory.Measure.count_apply_finite' ↥T ⊤ _
        (Set.toFinite _) MeasurableSpace.measurableSet_top]
      simp [Set.Finite.toFinset, Fintype.card_coe, hd_def]
    -- μ_pi {xs} = (1/d)^m via pi_singleton
    have hpi_singleton : ∀ xs : Fin m → ↥T,
        μ_pi {xs} = (1 / (d : ENNReal)) ^ m := by
      intro xs
      rw [hμ_pi_def, @MeasureTheory.Measure.pi_singleton]
      simp only [hD_sub_singleton, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    -- μ_pi(count_finset) = ∑ xs ∈ count_finset, μ_pi {xs} = card * (1/d)^m
    have hsum_eq : μ_pi (↑count_finset) = ∑ xs ∈ count_finset, μ_pi {xs} :=
      (@MeasureTheory.sum_measure_singleton (Fin m → ↥T)
        (@MeasurableSpace.pi (Fin m) (fun _ => ↥T) (fun _ => ⊤)) μ_pi
        count_finset inst_msc_pi).symm
    rw [hsum_eq]
    simp only [hpi_singleton, Finset.sum_const, nsmul_eq_mul]
    -- card * (1/d)^m ≤ ofReal(1 / 2) from hcount: 2 * card ≤ d^m
    have hcard_prod : Fintype.card (Fin m → ↥T) = d ^ m := by
      rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe, hd_def]
    rw [hcard_prod] at hcount
    have hd_pow_pos : 0 < d ^ m := Nat.pos_of_ne_zero (by positivity)
    have hd_ne : (d : ENNReal) ^ m ≠ 0 := by positivity
    have hd_ne_top : (d : ENNReal) ^ m ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top d)
    -- Rewrite card • (1/d)^m as card / d^m
    rw [show (count_finset.card : ENNReal) * (1 / (d : ENNReal)) ^ m =
        (count_finset.card : ENNReal) / (d : ENNReal) ^ m from by
      rw [one_div, ← ENNReal.inv_pow, div_eq_mul_inv]]
    -- card / d^m ≤ ofReal(1 / 2). Use div_le_iff: card / d^m ≤ c iff card ≤ c * d^m.
    rw [ENNReal.div_le_iff hd_ne hd_ne_top]
    -- Goal: (card : ENNReal) ≤ ofReal(1 / 2) * (d : ENNReal)^m
    -- ofReal(1 / 2) * d^m = d^m / 2. Need card ≤ d^m / 2.
    -- From 2 * card ≤ d^m: card * 2 ≤ d^m, so card ≤ d^m * (1 / 2) = ofReal(1 / 2) * d^m.
    -- Use le_div_iff_mul_le to reduce to card * 2 ≤ d^m:
    -- card ≤ ofReal(1 / 2) * d^m iff card * 2 ≤ d^m * ... no, let me be direct.
    -- ofReal(1 / 2) * d^m >= card iff 2 * card <= 2 * (ofReal(1 / 2) * d^m) = d^m.
    -- Direct cast: h_ennreal: 2 * card ≤ d^m (ENNReal) from hcount.
    have h_ennreal : (2 * count_finset.card : ENNReal) ≤ (d : ENNReal) ^ m := by
      rw [show (d : ENNReal) ^ m = ((d ^ m : ℕ) : ENNReal) from by push_cast; rfl]
      exact_mod_cast hcount
    -- card ≤ ofReal(1 / 2) * d^m follows from 2*card ≤ d^m by dividing by 2.
    -- ofReal(1 / 2) = 2⁻¹
    calc (count_finset.card : ENNReal)
        = (count_finset.card : ENNReal) * 1 := (mul_one _).symm
      _ = (count_finset.card : ENNReal) * (2 * (2 : ENNReal)⁻¹) := by
          rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
      _ = (count_finset.card : ENNReal) * 2 * (2 : ENNReal)⁻¹ := by ring
      _ = (2 * count_finset.card : ENNReal) * (2 : ENNReal)⁻¹ := by ring
      _ ≤ (d : ENNReal) ^ m * (2 : ENNReal)⁻¹ :=
          mul_le_mul_left h_ennreal _
      _ = ENNReal.ofReal (1 / 2 : ℝ) * (d : ENNReal) ^ m := by
          rw [show ENNReal.ofReal (1 / 2 : ℝ) = (2 : ENNReal)⁻¹ from by
            rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ) < 2)]; norm_num]
          ring
  calc MeasureTheory.Measure.pi (fun _ : Fin m => D) good_X
      = @MeasureTheory.Measure.pi (Fin m) (fun _ => ↥T) _ (fun _ => ⊤)
          (fun _ => D_sub) (↑count_finset) := hgoal_eq
    _ ≤ ENNReal.ofReal (1 / 2 : ℝ) := hpi_sub_bound
    _ < ENNReal.ofReal (3 / 4 : ℝ) := by
        exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by norm_num) |>.mpr (by norm_num)

end PACTheoremHelpers

/-- Drift rate: how fast the target concept changes over time. -/
abbrev DriftRate := ℝ
