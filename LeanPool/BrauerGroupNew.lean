/-
Copyright (c) 2026 Yunzhou Xie and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Yichen Feng, Jujian Zhang, Yael Dillies
-/

import LeanPool.BrauerGroupNew.CentralSimple
import LeanPool.BrauerGroupNew.Centralizer
import LeanPool.BrauerGroupNew.ExtendScalar
import LeanPool.BrauerGroupNew.FieldCat
import LeanPool.BrauerGroupNew.LemmasAboutSimpleRing
import LeanPool.BrauerGroupNew.MatrixCenterEquiv
import LeanPool.BrauerGroupNew.MatrixEquivTensor
import LeanPool.BrauerGroupNew.TwoSidedIdeal
import LeanPool.BrauerGroupNew.Wedderburn
import LeanPool.BrauerGroupNew.Mathlib
import LeanPool.BrauerGroupNew.Subfield

/-!
# Brauer Group Core

Source: Philippe Gille and Tamás Szamuely, "Central Simple Algebras and
  Galois Cohomology", 2nd ed., Cambridge Studies in Advanced Mathematics 165,
  Cambridge University Press, 2017, for central simple algebras and Brauer
  group structure; formalization source:
  url:https://github.com/Whysoserioushah/BrauerGroup_new
Authors: Yunzhou Xie, Yichen Feng, Jujian Zhang, Yael Dillies
Status: verified
Main declarations: `Wedderburn_Artin`, `IsCentralSimple.TensorProduct.simple`, `CSA_implies_CSA`
Tags: algebra, ring-theory, central-simple-algebras, brauer-groups
MSC: 16K20, 16K50, 16S35
-/
