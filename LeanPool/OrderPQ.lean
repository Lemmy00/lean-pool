/-
Copyright (c) 2026 Scott Harper, Peiran Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Harper, Peiran Wu
-/
import LeanPool.OrderPQ.IsCyclic
import LeanPool.OrderPQ.MonoidHom
import LeanPool.OrderPQ.MulZMod
import LeanPool.OrderPQ.PrimeOrder
import LeanPool.OrderPQ.SemidirectProduct
import LeanPool.OrderPQ.TorsionBy

/-!
# Auxiliary infrastructure for groups of order p * q

Source: url:https://github.com/wupr/order-p-q
Authors: Scott Harper, Peiran Wu
Status: verified
Main declarations: `IsCyclic.of_card_eq_prime`
Tags: group-theory, finite-groups, semidirect-products
MSC: 20D20, 20E22, 20D60
-/

/-!
## Provenance and scope

The full classification of groups of order `p * q` lives in `Basic.lean` and `Main.lean`
upstream; the main `nonempty_mulEquiv_mulZMod_prime_semidirectProduct_mulZMod_prime` proof
in `Basic.lean` does not survive the Lean / Mathlib bump in this import session and was
omitted. What remains is the supporting infrastructure (cyclic-group helpers, semidirect
product results, `MulZMod` and prime-order lemmas) on which a future re-import can build.
-/
