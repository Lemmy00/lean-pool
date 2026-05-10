/-
Copyright (c) 2026 Shangtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shangtong Zhang
-/
import LeanPool.RlTheoryInLean.Algorithm
import LeanPool.RlTheoryInLean.Analysis
import LeanPool.RlTheoryInLean.Basic
import LeanPool.RlTheoryInLean.Data
import LeanPool.RlTheoryInLean.Defs
import LeanPool.RlTheoryInLean.MarkovDecisionProcess
import LeanPool.RlTheoryInLean.MeasureTheory
import LeanPool.RlTheoryInLean.Order
import LeanPool.RlTheoryInLean.Probability
import LeanPool.RlTheoryInLean.StochasticApproximation

/-!
# RL Theory in Lean

Source: arxiv:2511.03618
Authors: Shangtong Zhang
Status: verified
Main declarations: `ReinforcementLearning.LinearTD.ae_tendsto_of_linearTD_iid`
Tags: probability, reinforcement-learning, stochastic-approximation
MSC: 62L20, 60J10
-/

/-!
## Provenance

Imported from <https://github.com/ShangtongZhang/rl-theory-in-lean> (MIT-licensed
upstream; relicensed into Lean Pool under Apache 2.0 with the upstream author's
copyright preserved). Accompanies the paper *Towards Formalizing Reinforcement
Learning Theory* (arXiv:2511.03618). Ported from Lean `v4.28.0-rc1` to Lean Pool's
`v4.30.0-rc2`. Upstream contains no `sorry`s.

## Mathematical overview

The project mirrors Mathlib's directory layout and develops, among other things:
finite Markov reward / decision processes, stochastic (row-)stochastic matrices and
their Doeblin minorization and mixing, the Ionescu–Tulcea trajectory measure of a
Markov chain, the Robbins–Siegmund almost-supermartingale convergence theorem, a
general stochastic-approximation framework (martingale-difference, i.i.d. and
Markov noise, inverse-polynomial step sizes), and almost-sure convergence of linear
temporal-difference learning and of Q-learning.
-/
