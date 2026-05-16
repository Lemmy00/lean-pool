/-
Copyright (c) 2026 Scott Harper, Peiran Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Harper, Peiran Wu
-/
import LeanPool.OrderPQ.Main

/-!
# Classification of groups of order p * q

Source: url:https://github.com/wupr/order-p-q
Authors: Scott Harper, Peiran Wu
Status: verified
Main declarations: `LeanPool.OrderPQ.exists_card_eq_prime_mul_prime_and_not_isCyclic_iff`, `LeanPool.OrderPQ.nonempty_mulEquiv_of_card_eq_prime_mul_prime_of_not_isCyclic`
Tags: group-theory, finite-groups, semidirect-products
MSC: 20D20, 20E22, 20D60
-/

/-!
## Mathematical overview

For prime numbers `p` and `q`, this project classifies the groups of order `p * q`:

* A noncyclic group of order `p * q` exists iff `p = q`, `p ∣ q - 1`, or `q ∣ p - 1`.
* All noncyclic groups of order `p * q` are mutually isomorphic.
* When `p < q` and `G` is noncyclic of order `p * q`, then `G` is a semidirect product
  `MulZMod q ⋊[φ] MulZMod p` for some (in fact, any) nontrivial homomorphism `φ`.
* When `p = q` and `G` is noncyclic of order `p * q = p ^ 2`, then `G` is the direct product
  `MulZMod p × MulZMod p`.

Auxiliary developments include key properties of semidirect products of groups (including a
recognition criterion for internal semidirect products), order-of-element and Sylow-theoretic
lemmas used to organise the case analysis, and a uniqueness-up-to-isomorphism result for cyclic
subgroups of the same finite order in a cyclic group.

## Provenance

Imported from <https://github.com/wupr/order-p-q>. Ported from Mathlib `v4.15.0` to Lean Pool's
`v4.30.0-rc2`.
-/
