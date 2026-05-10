# Import guard failure

The wrapper found forbidden Lean tokens in added LeanPool lines:

- `LeanPool/RlTheoryInLean/Algorithm/LinearTD.lean:   -- ∑ i, P s i * (∑ ...) where the inner sum is over x s (constant in i) = ∑ ...`
- `LeanPool/RlTheoryInLean/StochasticApproximation/LpSpace.lean:     -- When p = 2, the constant is (d^((2-2)/2))^(1/2) = (d^0)^(1/2) = 1^(1/2) = 1`
- `LeanPool/RlTheoryInLean/StochasticApproximation/MarkovSamples.lean:            -- The constant a = |P^k s - μ s| doesn't depend on s', factor it out`

Remove these escape hatches or diagnostics before merging.
