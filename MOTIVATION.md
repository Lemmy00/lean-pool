<img width="1586" height="661" alt="image" src="https://github.com/user-attachments/assets/ea9dde0c-73a0-41bf-8efd-3e75d888e8fc" />

Lean Pool sits between [`mathlib`](https://github.com/leanprover-community/mathlib4) and [`merely-true`](https://github.com/merely-true/merely-true), preserving Lean 4 formalizations that don't fit mathlib's scope. 
Instead of mathlib's high-quality human review, Lean Pool relies on deterministic linters and LLM judgment, so it can grow faster while staying sorry-free, and pinned to the latest Mathlib. 
Lean Pool depends on Mathlib.
Lean Pool serves several purposes:

1. One-off formalizations get maintained, and can be depended upon.
2. Some of AI-slop PRs to mathlib get redirected to Lean Pool, where the strict CI and LLM review filter them out.
3. An appropriate target to PR medium-quality large-scale AI (and manual) formalization projects.

Lean Pool only accepts serious finished `sorry`-free and `axiom`-free projects in an attempt to ensure higher quality.

In the future Lean Pool or something similar may become a large mathematical library that can be grown quickly, like arXiv for informal mathematics.
The design decision to make it a monorepo as opposed to e.g. Lean Reservoir is intentional - math is interconnected, and several projects from Lean Pool may be needed at the same Lean version, without namespace clashes.
