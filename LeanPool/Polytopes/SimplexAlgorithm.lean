/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/

import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Data.Vector.Basic
import Mathlib.Data.PNat.Basic

namespace Polytopes

/-- A linear program with `p` constraints in `d` variables over an ordered field `R`. -/
structure LinearProgram (p d : ℕ+) (R : Type*)
    [Field R] [LinearOrder R] [IsStrictOrderedRing R] where
  /-- Whether the objective is to be minimized (otherwise maximized). -/
  minimize : Bool := true
  /-- The coefficient vector of the linear objective function. -/
  objectiveVector : (Fin d) → R
  /-- The constraint coefficient matrix. -/
  constraints : Matrix (Fin p) (Fin d) R
  /-- The right-hand side vector of the constraints. -/
  constraintRhs : (Fin p) → R
  /-- Each constraint row is nonzero. -/
  constraintsNonzero : ∀ i, constraints i ≠ 0

namespace LinearProgram

/-- A simplex tableau with `n+1` rows and `m` columns over an ordered field `R`. -/
@[ext]
structure Tableau (n m : ℕ+) (R : Type*) [Field R] [LinearOrder R] [IsStrictOrderedRing R] where
  /-- The body of the tableau. -/
  A : Matrix (Fin (n + 1)) (Fin m) R
  /-- The right-hand side of each row, carrying a lexicographic tie-breaking pair. -/
  Rhs : (Fin (n + 1)) → (Fin 2 → R)
  /-- The index of the basic variable for each row. -/
  basic : (Fin (n + 1) → Fin m)

/-- The result of running the simplex algorithm on a linear program `lp`. -/
structure result {p d : ℕ+} {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (lp : LinearProgram p d R) where
  /-- The basic variable assignment of the returned vertex. -/
  basic : Fin (p + 1) → Fin (p + d + 1) := 0
  /-- The optimal value paired with the optimal vertex, if the program is feasible and bounded. -/
  value_vertex : Option (List.Vector ((Fin 2 → R)) (d + 1))
  /-- The optimal value of the objective function. -/
  value : Option ((Fin 2 → R)) := value_vertex >>= (·.head)
  /-- The optimal value adjusted for the optimization direction. -/
  score : Option ((Fin 2 → R)) := if lp.minimize then value else value.map (-·)
  /-- The optimal vertex. -/
  vertex : Option (List.Vector ((Fin 2 → R)) (d + 1 - 1)) := value_vertex >>= (·.tail)
  /-- The optimal value is the head of `value_vertex`. -/
  hValue : value = value_vertex >>= (·.head) := by rfl
  /-- The optimal vertex is the tail of `value_vertex`. -/
  hVertex : vertex = value_vertex >>= (·.tail) := by rfl

namespace result

/-- The failure result, returned when the linear program is infeasible or unbounded. -/
def fail {p d : ℕ+} {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (lp : LinearProgram p d R) : result lp :=
  { value_vertex := none }

end result

/-- Whether the origin is a feasible point of the linear program `lp`. -/
def origin_feasible {p d : ℕ+} {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (lp : LinearProgram p d R) : Bool :=
  (List.Vector.ofFn lp.constraintRhs).toList.all (0 ≤ ·)

namespace Tableau

/-- Perform a single pivot of the tableau `T` on the entry `(pivot_row, pivot_col)`. -/
def pivoting {n m : ℕ+} {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (T : Tableau n m R) (pivot_row : Fin (n + 1)) (pivot_col : Fin m) : Tableau n m R :=
  let v := (T.A pivot_row pivot_col)⁻¹ • T.A pivot_row
  let r := (T.A pivot_row pivot_col)⁻¹ • T.Rhs pivot_row
  ⟨ fun j => if j = pivot_row then v else (- T.A j pivot_col) • v + T.A j,
    fun j => if j = pivot_row then r else (- T.A j pivot_col) • r + T.Rhs j,
    Function.update T.basic pivot_row pivot_col⟩

/-- Read off the optimal result of `lp` from a terminal tableau `T`. -/
def «return» {n p d : ℕ+} {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (lp : LinearProgram p d R) (T : Tableau n (p + d + 1) R) : lp.result := by
  let f : Fin (n + 1) → (Fin _ → (Fin 2 → R)) := fun i => Pi.single (T.basic i) (T.Rhs i)
  let f1 : Fin (p + d + 1) → (Fin 2 → R) := Finset.univ.sum f
  let f2 : Fin (d + 1) → (Fin 2 → R) := fun i =>
    if i = 0 then f1 0 else f1 ⟨i + p, by omega⟩
  let vertex := List.Vector.ofFn f2
  exact { basic := fun i => T.basic (Fin.ofNat (n + 1) i), value_vertex := some vertex }

end Tableau

variable {p d : ℕ+} {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- Build the phase-2 simplex tableau of `lp`.

The slack variables occupy the first `p+1` columns of the tableau and the first row holds the
objective function. -/
def phase2_tableau (lp : LinearProgram p d R) : Tableau p (p + d + 1) R := by
  let AwithObjective : Matrix (Fin (p + 1)) (Fin d) R :=
    fun i => if h : i = 0 then
      if lp.minimize then -lp.objectiveVector else lp.objectiveVector
    else
      lp.constraints (i.pred h)
  let A : Matrix (Fin (p + 1)) (Fin (p + d + 1)) R := by
    apply Matrix.transpose
    apply (Equiv.vectorEquivFin (Fin (p + 1) → R) _).1
    let v1 := List.Vector.ofFn (1 : Matrix (Fin (p + 1)) (Fin (p + 1)) R)
    let v2 := List.Vector.ofFn (AwithObjective.transpose : (Fin d) → (Fin (p + 1)) → R)
    refine ⟨ v1.1 ++ v2.1, ?_⟩
    simp only [List.length_append, v1.2, v2.2]
    omega
  exact ⟨ A, (fun i => if h : i = 0 then 0 else
    fun j => if j = 0 then lp.constraintRhs (i.pred h) else 0),
    fun i => Fin.castLE (by simp only [PNat.add_coe, PNat.one_coe]; omega) i ⟩

end LinearProgram

end Polytopes
