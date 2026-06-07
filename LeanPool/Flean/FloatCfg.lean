/-
Copyright (c) 2026 Joseph McKinsey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph McKinsey
-/
import Mathlib.Data.Rat.Defs

structure FloatCfg where
  (prec : ℕ) (emin emax : ℤ)
  emin_lt_emax : emin < emax
  prec_pos : 0 < prec


inductive RoundingMode where
  | nearest
  | down
  | up
  | tozero
  | toinf

class Rounding where
  mode : RoundingMode
