/-
Copyright (c) 2023 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/

import LeanPool.Monlib4.LinearAlgebra.IsReal
import LeanPool.Monlib4.LinearAlgebra.QuantumSet.SchurMul

/-!
# Quantum Graphs

This file ports the core upstream quantum-graph predicates: Schur projections, quantum graphs,
and real quantum graphs.  Since the current Lean Pool monlib4 slice does not yet recover
upstream's quantum-set coalgebra instance, the declarations carry explicit `CoalgebraStruct`
assumptions.
-/

variable {A B : Type*} [starAlgebra A] [starAlgebra B] [QuantumSet A] [QuantumSet B]
  [CoalgebraStruct ℂ A] [CoalgebraStruct ℂ B]

/-- A Schur-idempotent star-preserving linear map. -/
class schurProjection (f : A →ₗ[ℂ] B) : Prop where
  isIdempotentElem : f •ₛ f = f
  isReal : LinearMap.IsReal f

/-- A quantum graph is an idempotent for the Schur product. -/
class QuantumGraph (A : Type*) [starAlgebra A] [QuantumSet A] [CoalgebraStruct ℂ A]
    (f : A →ₗ[ℂ] A) : Prop where
  isIdempotentElem : f •ₛ f = f

theorem quantumGraph_iff {A : Type*} [starAlgebra A] [QuantumSet A] [CoalgebraStruct ℂ A]
    {f : A →ₗ[ℂ] A} :
    QuantumGraph A f ↔ f •ₛ f = f :=
  ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩

/-- A quantum graph whose underlying linear map is star-preserving. -/
class QuantumGraph.IsReal {A : Type*} [starAlgebra A] [QuantumSet A] [CoalgebraStruct ℂ A]
    {f : A →ₗ[ℂ] A} (_h : QuantumGraph A f) : Prop where
  isReal : LinearMap.IsReal f

/-- A real quantum graph packages Schur idempotence and star preservation. -/
class QuantumGraph.Real (A : Type*) [starAlgebra A] [QuantumSet A] [CoalgebraStruct ℂ A]
    (f : A →ₗ[ℂ] A) : Prop where
  isIdempotentElem : f •ₛ f = f
  isReal : LinearMap.IsReal f

theorem QuantumGraph.real_iff {A : Type*} [starAlgebra A] [QuantumSet A]
    [CoalgebraStruct ℂ A] {f : A →ₗ[ℂ] A} :
    QuantumGraph.Real A f ↔ f •ₛ f = f ∧ LinearMap.IsReal f :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

theorem quantumGraphReal_iff_schurProjection {A : Type*} [starAlgebra A] [QuantumSet A]
    [CoalgebraStruct ℂ A] {f : A →ₗ[ℂ] A} :
    QuantumGraph.Real A f ↔ schurProjection f :=
  ⟨fun h => ⟨h.isIdempotentElem, h.isReal⟩,
    fun h => ⟨h.isIdempotentElem, h.isReal⟩⟩

theorem QuantumGraph.Real.toQuantumGraph {A : Type*} [starAlgebra A] [QuantumSet A]
    [CoalgebraStruct ℂ A] {f : A →ₗ[ℂ] A} (h : QuantumGraph.Real A f) :
    QuantumGraph A f :=
  ⟨h.isIdempotentElem⟩
