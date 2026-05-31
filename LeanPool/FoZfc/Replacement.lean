/-
Copyright (c) 2026 Tetsuya Ishiu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Ishiu
-/

import Init.Data.Fin.Basic
import LeanPool.FoZfc.Basic
import LeanPool.FoZfc.Tostring
import LeanPool.FoZfc.FixedSnoc
import LeanPool.FoZfc.BoundedFormulaOps
import LeanPool.FoZfc.Axioms

/-!
# The Replacement Axiom

## Main Definitions

- A `FirstOrder.ZFC.RelByFormula` defines the relation defined by a formula.
- A `FirstOrder.ZFC.intIsFunctFormula` defines a formula for ϕ describes
  a function. A `FirstOrder.ZFC.EntIsFunctFormula` defines ϕ describes
  a function externally.
- A `FirstOrder.ZFC.intIsImage` defines the formula for fv 1 is the image of
  the function defined by ϕ of fv 0.
- A `FirstOrder.ZFC.ModelReplacement` is a class of models of Set Theory
  with the replacement schema.
- A `FirstOrder.ZFC.ModelZF` is a class of models of ZF.

## Main Statements

- Various "realize" theorems are proved.

-/

open FirstOrder
open FirstOrder.Language
open FirstOrder.Language.BoundedFormula

open ReplaceFV
open ZFC
open FixedSnoc

universe u v

namespace FirstOrder.ZFC

variable {V : Type u}

/-- Make a formula for ϕ describes a function. -/
def intIsFunctFormula {n : ℕ} (ϕ : LZFC.BoundedFormula ℕ n) :
    LZFC.BoundedFormula ℕ n :=
  let ϕ' := liftAt 3 n ϕ
  let tsN1 := makeTsN ![bv'' n, bv'' (n+1)]
  let tsN2 := makeTsN ![bv'' n, bv'' (n+2)]
  (∀'∀'∀'(BoundedFormula.replaceFV ϕ' tsN1 ⟹
  BoundedFormula.replaceFV ϕ' tsN2 ⟹ bv'' (n+1) =' bv'' (n+2)))

/-- Find the (k+1)-ary relation defined by a formula. -/
def RelByFormula [ModelSets V] {n : ℕ} (s : ℕ → V) (xs : Fin n → V)
    (ϕ : LZFC.BoundedFormula ℕ n) {k : ℕ} (xs1 : Fin (k + 1) → V) : Prop :=
  ϕ.Realize (replaceInitialValues s xs1) xs

/-- Dexcribe ϕ describes a function. -/
def ExtIsFunctFormula [ModelSets V] {n : ℕ} (s : ℕ → V) (xs : Fin n → V)
    (ϕ : LZFC.BoundedFormula ℕ n) : Prop :=
  let R : (Fin 2 → V) → Prop := RelByFormula s xs ϕ
  ∀ (x : V) (y₁ : V) (y₂ : V), (R ![x, y₁] → R ![x, y₂] → y₁ = y₂)

/-- The realization of `intIsFunctFormula ϕ` matches `ExtIsFunctFormula ϕ`. -/
theorem realize_is_funct_formula [ModelSets V] {n : ℕ} (s : ℕ → V)
    (xs : Fin n → V) (ϕ : LZFC.BoundedFormula ℕ n) :
    (intIsFunctFormula ϕ).Realize s xs ↔ ExtIsFunctFormula s xs ϕ := by
  unfold intIsFunctFormula ExtIsFunctFormula RelByFormula
  simp [realize_liftAt']

/-- Make a formula for fv 1 is the image of fv 0 under the relation defined by ϕ. -/
def intIsImage {n : ℕ} (ϕ : LZFC.BoundedFormula ℕ n) :
    LZFC.BoundedFormula ℕ n := (∀'(bv'' n ∈' fv (n+1) 1 ⇔
    ∃'((bv'' (n+1)) ∈' fv' 0 ∧' (BoundedFormula.replaceFV (liftAt 2 n ϕ)
    (makeTsN ![bv'' (n+1), bv'' n])))))

/-- Describe b is the image of a under the relation defined by ϕ. -/
def ExtIsImage [ModelSets V] {n : ℕ} (s : ℕ → V) (xs : Fin n → V)
    (ϕ : LZFC.BoundedFormula ℕ n) (a b : V) := ∀ (y : V),
  (y ∈ b ↔ ∃ (x : V), x ∈ a ∧ ϕ.Realize (replaceInitialValues s ![x, y]) xs)

/-- `replaceInitialValues` composed with a larger replacement collapses. -/
@[simp]
theorem replaceInitialValues_replaceInitialValues {n m : ℕ} {h : n ≤ m}
    {s : ℕ → V} {xs1 : Fin (n + 1) → V} {xs2 : Fin (m + 1) → V} :
    replaceInitialValues (replaceInitialValues s xs1) xs2 =
    replaceInitialValues s xs2 := by
  funext k
  unfold replaceInitialValues
  by_cases h_k_le_m : k < m + 1
  · rw [if_pos h_k_le_m]
    rw [if_pos h_k_le_m]
  · have h_k_gt_n : ¬ (k < n + 1) := by omega
    rw [if_neg h_k_le_m]
    rw [if_neg h_k_gt_n]
    rw [if_neg h_k_le_m]

@[simp]
theorem realize_is_image [ModelSets V] {n : ℕ} (s : ℕ → V) (xs : Fin n → V)
    (ϕ : LZFC.BoundedFormula ℕ n) (a b : V) : (intIsImage ϕ).Realize
    (replaceInitialValues s ![a, b]) xs ↔ ExtIsImage s xs ϕ a b := by
  unfold intIsImage ExtIsImage
  simp [realize_liftAt']

/-- Model with the Replacement schema. -/
class ModelReplacement (V : Type u) extends ModelSets V where
  /-- The model satisfies the replacement schema. -/
  replacement_schema : ∀ {n : ℕ} (s : ℕ → V) (xs : Fin n → V)
    (ϕ : LZFC.BoundedFormula ℕ n), (intIsFunctFormula ϕ ⟹
    ∀'∃'(BoundedFormula.replaceFV (liftAt 2 n (intIsImage ϕ))
    (makeTsN ![bv'' n, bv'' (n+1)]))).Realize s xs

/-- The Replacement described externally. -/
theorem ext_replacement [ModelReplacement V] {n : ℕ} (s : ℕ → V)
    (xs : Fin n → V) (ϕ : LZFC.BoundedFormula ℕ n) :
    ExtIsFunctFormula s xs ϕ → ∀ (a : V), ∃ (b : V),
    ExtIsImage s xs ϕ a b := by
  intro h0 a
  have h_intIsFunctFormula : (intIsFunctFormula ϕ).Realize s xs := by
    apply (realize_is_funct_formula s xs ϕ).mpr h0
  obtain ⟨b, h_b⟩ := realize_ex.mp ((ModelReplacement.replacement_schema
    s xs ϕ) h_intIsFunctFormula a)
  rw [snoc_conv, snoc_conv] at h_b
  use b
  rw [BoundedFormula.realize_replaceFV, realize_liftAt'] at h_b
  · simpa using h_b
  · omega
  · omega

/-- Model with pairing and replacement. -/
class ModelPR (V : Type u) extends ModelPairing V, ModelReplacement V

/-- The image of `intIsSingleton` exists as a witness to replacement. -/
theorem ext_test [ModelPR V] (s : ℕ → V) (xs : Fin 0 → V) (a : V) :
    ∃ (b : V), ExtIsImage s xs intIsSingleton a b := by
  have h1 : ExtIsFunctFormula s xs intIsSingleton := by
    intro x y₁ y₂
    unfold RelByFormula
    simp only [realize_is_singleton, replaceInitialValues_2_0, replaceInitialValues_2_1]
    exact ext_singleton_unique
  obtain ⟨b, hb⟩ := ext_replacement s xs intIsSingleton h1 a
  exact ⟨b, hb⟩

/-- The image of `intIsSingleton` exists as a witness to replacement, internally. -/
theorem int_test [ModelPR V] (s : ℕ → V) (xs : Fin 0 → V) :
    (∀'∃'((intIsImage intIsSingleton).liftAndReplaceFV 2 0
    ![bv'' 0, bv'' 1])).Realize s xs := by
  suffices h : ∀ (a : V), ∃ (b : V), ExtIsImage s xs intIsSingleton a b by
    suffices h' :
        ∀ (a : V), ∃ (b : V),
          ExtIsImage s (fixedSnoc (fixedSnoc xs a) b ∘ fun i => i.addNat 2)
            intIsSingleton a b by
      simpa [realize_liftAt'] using h'
    intro a
    obtain ⟨b, hb⟩ := h a
    refine ⟨b, ?_⟩
    have hxs : (fixedSnoc (fixedSnoc xs a) b ∘ fun i : Fin 0 => i.addNat 2) = xs := by
      funext i
      exact Fin.elim0 i
    simpa [hxs] using hb
  intro a
  exact ext_test s xs a

/-- Model of ZF: all the standard axioms together. -/
class ModelZF (V : Type u) extends ModelEmptyset V, ModelPairing V,
    ModelUnion V, ModelPowerset V, ModelInfinity V, ModelRegularity V,
    ModelComprehension V, ModelReplacement V

end FirstOrder.ZFC
