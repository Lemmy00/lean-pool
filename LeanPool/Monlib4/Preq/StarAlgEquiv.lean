/-
Copyright (c) 2026 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/

import Mathlib.Algebra.Star.StarAlgHom

/-!
# Star algebra equivalence compatibility

Mathlib now provides most of the upstream `StarAlgEquiv` API.  This file keeps
the small compatibility lemma still used by the imported Monlib4 slice.
-/

namespace StarAlgEquiv

theorem symm_apply_eq {R A B : Type*} [Add A] [Add B] [Mul A] [Mul B]
    [SMul R A] [SMul R B] [Star A] [Star B] (f : A ≃⋆ₐ[R] B)
    {x : A} {y : B} :
    f.symm y = x ↔ y = f x :=
  EquivLike.inv_apply_eq (e := f)

end StarAlgEquiv
