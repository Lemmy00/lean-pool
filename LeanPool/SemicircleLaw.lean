/-
Copyright (c) 2026 FredRaj3. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FredRaj3
-/

import LeanPool.SemicircleLaw.SemicircleDistribution

/-!
# Wigner Semicircle Distribution

Source: url:https://github.com/FredRaj3/SemicircleLaw
Authors: FredRaj3
Status: verified
Main declarations: `LeanPool.SemicircleLaw.semicircleReal`
Tags: probability, random-matrix-theory, distributions
MSC: 60B20, 60E05
-/

/-!
## Mathematical overview

The Wigner semicircle distribution is the limiting spectral distribution of a
Wigner random matrix, scaled by `1 / √n`. It is supported on `[-2√v, 2√v]`,
where `v` is the variance, with density

  `f(x) = 1 / (2 π v) · √(4 v - (x - μ) ^ 2)`

for `x ∈ [μ - 2√v, μ + 2√v]`. The semicircle law is Theorem 2.3 in Todd Kemp's
Random Matrix Theory notes.

## Main results

- `LeanPool.SemicircleLaw.semicirclePDFReal` — the real-valued probability
  density function of the semicircle distribution.
- `LeanPool.SemicircleLaw.semicirclePDF` — the `ℝ≥0∞`-valued pdf.
- `LeanPool.SemicircleLaw.semicircleReal` — the semicircle measure on `ℝ`,
  parametrized by mean `μ` and variance `v`.
-/
