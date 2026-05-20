/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/

import Mathlib.Data.Complex.Basic
import LeanPool.Monlib4.LinearAlgebra.Matrix.PiMat
import LeanPool.Monlib4.Preq.Set
import LeanPool.Monlib4.RepTheory.AutMat

/-!
# Two-Term PiMat Equivalences

This file restores the first upstream `Monlib.QuantumGraph.PiMatFinTwo` layer:
algebra equivalences between binary products of matrix algebras and `PiMat`
families indexed by `Fin 2`, plus the inner-automorphism transport lemmas that
do not depend on the later quantum-graph projection theory.
-/

open scoped Matrix

/-- Identify a binary product of matrix algebras with a `Fin 2`-indexed `PiMat`. -/
def MatProd_algEquiv_PiMat (n' : Fin 2 → Type*) [Π i, Fintype (n' i)]
    [Π i, DecidableEq (n' i)] :
    (Matrix (n' 0) (n' 0) ℂ × Matrix (n' 1) (n' 1) ℂ) ≃ₐ[ℂ]
      PiMat ℂ (Fin 2) n' :=
  matrixPiFinTwo_algEquiv_prod.symm

/-- Swap the two index types in a `Fin 2`-indexed family. -/
abbrev PiFinTwo.swap (n' : Fin 2 → Type*) : Fin 2 → Type _ :=
  fun i => if i = 0 then n' 1 else n' 0

instance {n' : Fin 2 → Type*} [Π i, Fintype (n' i)] :
    Π i, Fintype ((PiFinTwo.swap n') i) :=
  fun i => by
    by_cases h : i = 0
    · rw [PiFinTwo.swap, if_pos h]
      exact inferInstanceAs (Fintype (n' 1))
    · rw [PiFinTwo.swap, if_neg h]
      exact inferInstanceAs (Fintype (n' 0))

instance {n' : Fin 2 → Type*} [Π i, DecidableEq (n' i)] :
    Π i, DecidableEq ((PiFinTwo.swap n') i) :=
  fun i => by
    by_cases h : i = 0
    · rw [PiFinTwo.swap, if_pos h]
      exact inferInstanceAs (DecidableEq (n' 1))
    · rw [PiFinTwo.swap, if_neg h]
      exact inferInstanceAs (DecidableEq (n' 0))

/-- Identify the swapped binary product with the swapped `Fin 2`-indexed `PiMat`. -/
def MatProd_algEquiv_PiMat_swap (n' : Fin 2 → Type*) [Π i, Fintype (n' i)]
    [Π i, DecidableEq (n' i)] :
    (Matrix (n' 1) (n' 1) ℂ × Matrix (n' 0) (n' 0) ℂ) ≃ₐ[ℂ]
      PiMat ℂ (Fin 2) (PiFinTwo.swap n') :=
  MatProd_algEquiv_PiMat (PiFinTwo.swap n')

namespace Prod

/-- Algebra equivalence swapping the two factors of a product algebra. -/
@[simps]
def swap_algEquiv (α β : Type*) [Semiring α] [Semiring β] [Algebra ℂ α] [Algebra ℂ β] :
    (α × β) ≃ₐ[ℂ] (β × α) where
  toFun x := x.swap
  invFun x := x.swap
  left_inv _ := by simp
  right_inv _ := by simp
  map_add' _ _ := by simp
  map_mul' _ _ := by simp
  commutes' _ := by simp

end Prod

/-- Swap the two components of a `Fin 2`-indexed `PiMat` as an algebra equivalence. -/
def PiMat_finTwo_swapAlgEquiv {n' : Fin 2 → Type*} [Π i, Fintype (n' i)]
    [Π i, DecidableEq (n' i)] :
    PiMat ℂ (Fin 2) n' ≃ₐ[ℂ] PiMat ℂ (Fin 2) (PiFinTwo.swap n') :=
  (MatProd_algEquiv_PiMat n').symm.trans
    ((Prod.swap_algEquiv _ _).trans (MatProd_algEquiv_PiMat_swap n'))

theorem PiMat_finTwo_swapAlgEquiv_apply {n' : Fin 2 → Type*}
    [Π i, Fintype (n' i)] [Π i, DecidableEq (n' i)]
    (x : Matrix (n' 0) (n' 0) ℂ) (y : Matrix (n' 1) (n' 1) ℂ) :
    PiMat_finTwo_swapAlgEquiv (MatProd_algEquiv_PiMat n' (x, y)) =
      MatProd_algEquiv_PiMat _ (y, x) :=
  rfl

theorem AlgEquiv.prod_map_inner_of {K R₁ R₂ : Type*} [CommSemiring K]
    [Semiring R₁] [Semiring R₂] [Algebra K R₁] [Algebra K R₂]
    {f : R₁ ≃ₐ[K] R₁} (hf : f.IsInner) {g : R₂ ≃ₐ[K] R₂} (hg : g.IsInner) :
    (f.prod_map g).IsInner := by
  rw [AlgEquiv.prod_isInner_iff_prod_map]
  obtain ⟨U, hU, rfl⟩ := hf
  obtain ⟨V, hV, rfl⟩ := hg
  exact ⟨U, hU, V, hV, rfl⟩
