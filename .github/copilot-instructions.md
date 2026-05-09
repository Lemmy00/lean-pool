# Copilot review instructions

This repository runs two LLM reviewers on pull requests:

1. **GitHub Copilot's automatic code review** (you).
2. **A custom workflow** that calls `gpt-5.4-mini` against the rules in
   [`./REVIEW_RULES.md`](./REVIEW_RULES.md).

Both reviewers should apply the same standards. Read [`./REVIEW_RULES.md`](./REVIEW_RULES.md)
in full before reviewing; the summary below is for convenience only.

## What to review

Lean Pool curates **completed, self-contained formalization projects of real
mathematics, physics, computer science, or similarly serious formal subjects
at the graduate or research level**. Single lemmas, golfing PRs,
infrastructure-only PRs, and incremental API tweaks do **not** belong, even
when they compile cleanly.

When reviewing a PR, focus on the judgement calls only an LLM can make:

- **S1 Significance** — graduate/research level, anchored in a paper /
  textbook / problem statement.
- **S2 Self-containment** — PR ends at a coherent landmark.
- **S3 Project card** — new top-level projects must include a Lean module
  docstring (`/-! ... -/`) at the top of their entry-point file describing
  what was formalized, source, authors, and status.
- **S4 Statement matches description** — formal Lean theorem matches its
  informal claim (no missing hypotheses, no quantifier swaps, etc.).
- **S5 Verbose proofs** — flag clearly golfable proofs (repeated `have`s,
  one-line tactic where term-mode is used, `simp` chains that collapse).
- **S6 Redundancy** — trivial reformulations, possible mathlib duplicates,
  declarations that exist only to be inlined.
- **S7 Pointless infrastructure** — types/instances/wrappers with no use in
  the PR's main results.

## What NOT to review

The following are caught by separate linters in CI; **do not** flag them:

- Presence of `sorry` / `admit` / new `axiom`.
- File headers, copyright, license, authorship metadata.
- File-size or proof-size limits.
- `set_option maxHeartbeats` overrides.
- Naming conventions (`camelCase` vs `snake_case`).
- Bare `simp` vs `simp only`.
- `decide` / `native_decide` justification comments.
- Presence of docstrings on public declarations.

## Style

- Comment only when a specific rule above is violated.
- Cite the file and line where you can.
- Suggest a concrete fix, not just a complaint.
- When uncertain, say nothing.
- Do not rewrite proofs in full; suggest direction.
- Do not comment on commit messages, PR titles, or PR descriptions beyond
  verifying that S3's project card requirement is met for new top-level
  projects.

When in doubt, defer to [`./REVIEW_RULES.md`](./REVIEW_RULES.md).
