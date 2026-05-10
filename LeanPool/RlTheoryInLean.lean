/-
Copyright (c) 2026 Shangtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shangtong Zhang
-/

import LeanPool.RlTheoryInLean.Analysis
import LeanPool.RlTheoryInLean.Data
import LeanPool.RlTheoryInLean.Defs
import LeanPool.RlTheoryInLean.MeasureTheory
import LeanPool.RlTheoryInLean.Order
import LeanPool.RlTheoryInLean.Probability
import LeanPool.RlTheoryInLean.StochasticApproximation

/-!
# RL Theory in Lean

Source: arxiv:2511.03618
Authors: Shangtong Zhang
Status: verified
Main declarations: `StochasticMatrix.stationary_distribution_exists`
Tags: probability, reinforcement-learning, stochastic-matrices
MSC: 62L20, 60J10
-/

/-!
## Provenance

Imported from <https://github.com/ShangtongZhang/rl-theory-in-lean> (MIT-licensed
upstream; relicensed into Lean Pool under Apache 2.0 with the upstream author's
copyright preserved). Accompanies the paper *Towards Formalizing Reinforcement
Learning Theory* (arXiv:2511.03618). Ported from Lean `v4.28.0-rc1` to Lean Pool's
`v4.30.0-rc2`. This Lean Pool import keeps the warning-clean core infrastructure.

## Mathematical overview

The project mirrors Mathlib's directory layout and develops stochastic
row-stochastic matrices, Doeblin minorization and geometric mixing for finite
chains, finite Markov-chain kernels and trajectory measures, measure/kernel helper
lemmas, and discrete Gronwall inequalities used in stochastic approximation.
-/
