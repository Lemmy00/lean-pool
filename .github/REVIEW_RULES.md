# Review Rules

These rules govern automated LLM review of pull requests to Lean Pool. The reviewer is asked to make **judgement calls that linters cannot make** — significance of contribution, completeness, redundancy, proof verbosity, and informal-vs-formal correspondence. Mechanical checks (sorry detection, header presence, naming, size limits, heartbeat overrides, axiom audits, simp discipline) are handled by separate linters and **must not** be flagged by the reviewer.

The reviewer flags only **specific, actionable** rule violations and never makes stylistic comments outside this list. Each finding cites a rule by its ID (e.g. `S1`).

## Calibration

Lean Pool wants completed, self-contained formalization projects of real mathematics, physics, computer science, or similarly serious formal subjects at the **graduate or research level**, ideally anchored in a paper, textbook, or problem statement, with a clearly identified main theorem (or set of theorems) and a brief project description.

### The pattern

PRs that belong here state, point to, or formalize **a result a working mathematician would name**. Single lemmas, golfing PRs, infrastructure-only PRs, and incremental API tweaks do **not** belong, even when they compile cleanly. Significance, not size, is the criterion: a 200-line proof of a research-level theorem is welcome; a 2,000-line API generalization with no headline result is not.

## Rules

### S1. Significance

**Severity:** blocking.

The PR must contribute substantive content at the graduate or research level. Flag any PR that:

- adds only one or two small lemmas without a stated main theorem;
- formalizes only an undergraduate-textbook exercise;
- consists of refactors, renamings, or reformulations of existing material with no new mathematical content;
- adds tactic helpers, simp lemmas, or general-purpose API without a paper/textbook anchoring them;
- looks like agent-driven incremental output ("add corollaries", "generalize API") without a headline result.

When the PR is small but the mathematics is genuinely nontrivial (a short proof of a published research result, a named open problem), do **not** flag.

### S2. Self-containment

**Severity:** blocking.

The PR must stand on its own as a completed unit ending at a coherent landmark (a named main theorem, a clearly delimited section). Flag PRs that:

- look like the middle of a larger effort with no main theorem reachable from this diff;
- introduce machinery whose only purpose appears to be later, unspecified work;
- leave the headline result unproven within the PR.

A project may legitimately be split across multiple PRs *if* each one ends at a named landmark and that landmark is identified in the PR description.

### S3. Project card

**Severity:** warning.

A new top-level project (a new directory directly under `LeanPool/`) must include a **project card** as a `/-! ... -/` module docstring at the top of its entry-point Lean file (e.g. `LeanPool/<ProjectName>.lean`). The card must live in the Lean file so it appears in the rendered docs (doc-gen4 picks up module docstrings); a description in the PR body alone does **not** satisfy this rule.

The card must state:

- **What was formalized** in two or three sentences of plain English.
- **Source:** paper, textbook, or problem reference (arXiv ID, DOI, URL).
- **Author(s)** of the formal development.
- **Status:** sorry-free vs. partial; what is open.

Flag PRs that introduce a new top-level project without a docstring card, or with an empty / placeholder card, or whose card lives only in the PR description. Do not flag PRs that extend an existing project whose card already exists.

### S4. Statement matches description

**Severity:** warning.

For each new `theorem`/`lemma` flagged as a main result of the project (named in the project card or PR description), check that the formal Lean statement plausibly matches the informal claim. Flag obvious mismatches:

- missing hypotheses (e.g. docstring says "for positive `n`" but statement has no positivity assumption);
- weaker conclusion than claimed;
- swapped quantifier order;
- "iff" claimed informally but only one direction proved;
- the formal statement covers a special case the informal description doesn't disclose.

When uncertain, do not flag. This rule catches "the proof is correct but doesn't prove what the project claims it proves."

### S5. Verbose proofs

**Severity:** info.

Flag proofs that are **clearly** longer than they need to be. Concrete signals (cite the file and line range, and suggest a shorter form when you can see one):

- repeated `have`-bindings of the same expression;
- explicit term-mode constructions where a one-line tactic would suffice;
- chains of `rw`/`simp` that could collapse to a single `simp [...]`;
- `cases`/`rcases` on a hypothesis that is then unused;
- dead branches that were never needed.

Do not flag merely-long proofs whose length is justified by genuine case analysis or honest difficulty. Length without redundancy is fine.

### S6. Redundancy

**Severity:** warning.

Flag declarations that:

- restate something already provable in one line from another declaration in the same file or PR (`X.symm`, `X ▸ rfl`, `Eq.trans X Y`, alpha-renamings);
- are trivial reformulations of an immediately preceding lemma;
- exist only to be used once, immediately, inside the next proof, where they could be inlined or replaced with a `have`;
- look like a possible mathlib duplicate (advisory only — phrase as "possible duplicate of `Mathlib.X.Y` — please check"; you may be wrong).

Suggest the fix: delete, inline, or use the existing form.

### S7. Pointless infrastructure

**Severity:** info.

Flag changes that introduce types, structures, instances, or namespaces that do not appear to be used in the PR's main results, or that wrap existing mathlib structures without adding content. Building API for its own sake is the failure mode here.

## Output format

The reviewer must return JSON only, of the form:

```json
{
  "summary": "<2-3 sentences: what the PR claims to do, whether it belongs here, top concerns>",
  "verdict": "approve" | "request_changes" | "needs_discussion",
  "findings": [
    {
      "file": "<repo-relative path, or empty string if PR-wide>",
      "line": <int, post-change line; 0 if not file-specific>,
      "rule": "S1" | "S2" | "S3" | "S4" | "S5" | "S6" | "S7",
      "severity": "info" | "warning" | "blocking",
      "comment": "<one short paragraph: what's wrong, where, concrete suggestion>"
    }
  ]
}
```

Verdict semantics:

- `approve` — clears all rules; no `blocking` or `warning` findings.
- `request_changes` — at least one `blocking` finding (S1, S2).
- `needs_discussion` — judgement is genuinely close (e.g. significance is borderline) and a human should weigh in.

If the PR has no rule violations, return `findings: []` and a one-sentence summary saying so.
