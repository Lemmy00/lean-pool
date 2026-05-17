/-
Copyright (c) 2026 Stefan Barańczuk, Aristotle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Barańczuk, Aristotle
-/

import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.Data.Set.Card
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

/-!
# FinEqs main file

Vendored from `nasqret/fineqs`. See `LeanPool/Fineqs.lean` for the project overview.
-/

namespace LeanPool.Fineqs

open scoped BigOperators

/-- The zero set of a set of functions `X → F`. -/
def ZeroSet {X F : Type*} [Zero F] (S : Set (X → F)) : Set X :=
  {x | ∀ f ∈ S, f x = 0}

/-- For a submodule `L` of a finite-dimensional `F`-vector space `V` of dimension
`finrank F L + n`, there is a linear map from `V` to `Fin n → F` with kernel exactly `L`. -/
private lemma exists_linearMap_of_ker {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [Module.Finite F V] (n : ℕ) (L : Submodule F V)
    (hV : Module.finrank F V = Module.finrank F L + n) :
    ∃ M : V →ₗ[F] (Fin n → F), LinearMap.ker M = L := by
  have hquot : Module.finrank F (V ⧸ L) = n := by
    have h := Submodule.finrank_quotient_add_finrank L
    omega
  classical
  have hrank : Module.finrank F (V ⧸ L) = Module.finrank F (Fin n → F) := by
    rw [hquot, Module.finrank_fin_fun]
  let e : (V ⧸ L) ≃ₗ[F] (Fin n → F) := LinearEquiv.ofFinrankEq _ _ hrank
  refine ⟨e.toLinearMap.comp L.mkQ, ?_⟩
  rw [LinearMap.ker_comp]
  have he : LinearMap.ker e.toLinearMap = ⊥ := e.ker
  rw [he, Submodule.comap_bot, Submodule.ker_mkQ]

variable {F : Type*} [Field F] [Fintype F]

/--
Cardinality of projective space minus a point: `|P^n(F) \ {α}| = (q^{n+1} - q) / (q - 1)`.
-/
lemma card_projectivization_minus_point (n : ℕ) (α : Projectivization F (Fin (n + 1) → F)) :
    Nat.card {x : Projectivization F (Fin (n + 1) → F) // x ≠ α} =
    (Fintype.card F ^ (n + 1) - Fintype.card F) / (Fintype.card F - 1) := by
  classical
  haveI : Fintype (Projectivization F (Fin (n + 1) → F)) := Fintype.ofFinite _
  haveI : Nonempty (Projectivization F (Fin (n + 1) → F)) := ⟨α⟩
  haveI : Fintype {x : Projectivization F (Fin (n + 1) → F) // x ≠ α} := Subtype.fintype _
  haveI : Fintype {x : Projectivization F (Fin (n + 1) → F) // x = α} := Subtype.fintype _
  rw [Nat.card_eq_fintype_card,
    Fintype.card_subtype_compl (p := (· = α)),
    Fintype.card_subtype_eq α]
  have hcardV := Projectivization.card' F (Fin (n + 1) → F)
  simp only [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin] at hcardV
  have hq : 2 ≤ Fintype.card F := Fintype.one_lt_card
  have hP : 1 ≤ Fintype.card (Projectivization F (Fin (n + 1) → F)) :=
    Fintype.card_pos
  set q := Fintype.card F
  set P := Fintype.card (Projectivization F (Fin (n + 1) → F))
  have hqsub : 0 < q - 1 := by omega
  -- Show: q^(n+1) - q = (q - 1) * (P - 1).
  have hPq : P * (q - 1) = q ^ (n + 1) - 1 := by omega
  have h_eq : q ^ (n + 1) - q = (P - 1) * (q - 1) := by
    rw [Nat.sub_mul, one_mul]; omega
  have hdvd : (q - 1) ∣ (q ^ (n + 1) - q) := ⟨P - 1, by rw [mul_comm]; exact h_eq⟩
  rw [eq_comm, Nat.div_eq_iff_eq_mul_left hqsub hdvd]
  exact h_eq

end LeanPool.Fineqs
