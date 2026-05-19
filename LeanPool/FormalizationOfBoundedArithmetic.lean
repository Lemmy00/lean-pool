/-
Copyright (c) 2026 ruplet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ruplet
-/

import LeanPool.FormalizationOfBoundedArithmetic.Algebra
import LeanPool.FormalizationOfBoundedArithmetic.AxiomSchemes
import LeanPool.FormalizationOfBoundedArithmetic.BasicSingleSorted
import LeanPool.FormalizationOfBoundedArithmetic.Complexity
import LeanPool.FormalizationOfBoundedArithmetic.DisplayedVariables
import LeanPool.FormalizationOfBoundedArithmetic.IDelta0
import LeanPool.FormalizationOfBoundedArithmetic.IOPEN
import LeanPool.FormalizationOfBoundedArithmetic.IsEnum
import LeanPool.FormalizationOfBoundedArithmetic.LanguagePeano
import LeanPool.FormalizationOfBoundedArithmetic.LanguageZambella
import LeanPool.FormalizationOfBoundedArithmetic.MathlibSimps
import LeanPool.FormalizationOfBoundedArithmetic.Order
import LeanPool.FormalizationOfBoundedArithmetic.Register
import LeanPool.FormalizationOfBoundedArithmetic.Semantics
import LeanPool.FormalizationOfBoundedArithmetic.SimpRules
import LeanPool.FormalizationOfBoundedArithmetic.Syntax
import LeanPool.FormalizationOfBoundedArithmetic.V0
import LeanPool.FormalizationOfBoundedArithmetic.V0StrAddAssoc
import LeanPool.FormalizationOfBoundedArithmetic.V0StrAddComm
import LeanPool.FormalizationOfBoundedArithmetic.V0StrSuccAssoc

/-!
# Formalization of bounded arithmetic

Source: url:https://github.com/ruplet/formalization-of-bounded-arithmetic
Authors: ruplet
Status: verified
Main declarations: `IOPENModel.add_assoc`, `V0Model.ind_of_comp`, `str_add_assoc`, `str_succ_assoc`
Tags: logic, bounded-arithmetic, model-theory, computational-complexity
MSC: 03F30, 03D15
-/
