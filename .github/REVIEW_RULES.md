# Review Rules

These rules govern automated LLM review of pull requests to Lean Pool. The reviewer is asked to make **judgement calls that linters cannot make** — significance of contribution, completeness, redundancy, proof verbosity, and informal-vs-formal correspondence. Mechanical checks (sorry detection, header presence, naming, size limits, heartbeat overrides, axiom audits, simp discipline) are handled by separate linters and **must not** be flagged by the reviewer.

The reviewer flags only **specific, actionable** rule violations and never makes stylistic comments outside this list. Each finding cites a rule by its ID (e.g. `S1`).

## Calibration

Lean Pool wants completed, self-contained formalization projects of real mathematics, physics, computer science, or similarly serious formal subjects at the **graduate or research level**, ideally anchored in a paper, textbook, or problem statement, with a clearly identified main theorem (or set of theorems) and a brief project description.

### The pattern

PRs that belong here state, point to, or formalize **a result a working mathematician would name**. Single lemmas, golfing PRs, infrastructure-only PRs, and incremental API tweaks do **not** belong, even when they compile cleanly. Significance, not size, is the criterion: a 200-line proof of a research-level theorem is welcome; a 2,000-line API generalization with no headline result is not.

### Concrete REJECT examples

- **`PMF.binomial_add_binomial` (176 lines, 1 lemma, no project card, no paper anchor):** a single utility lemma stating that the convolution of two binomial PMFs is binomial. Despite the gnarly proof, this is an **undergraduate-textbook** identity that any introductory probability course covers. **NOT acceptable.** The proof's complexity does not change the verdict — significance is what matters, and there isn't any. Author's own framing ("a particularly acute example of a very gnarly proof of a straightforwardly useful fact") is itself a tell that this is utility code, not a project.
- **"add binomial PMF corollaries" (74/61/3 files):** two trivial corollaries that follow in one or two lines from a single existing lemma. Pure churn from an agent.
- **"generalize binomial addition with additive convolution API" (241/174/1 file):** incremental refactor with no clear new mathematical content articulated.

## Decision flow

Before applying the rules, **classify the PR's shape**. The model should walk this check explicitly and report what it found:

1. **Count new top-level declarations** (`theorem` / `lemma` / `def` / `instance` / `structure` / `inductive` / `class`) introduced in this diff. Call this `N`.
2. **Count new files** that contain at least one new declaration. Call this `F`.
3. **Look for paper / textbook / problem anchors** in the PR description, the project card (S3), or doc comments: arXiv ID, DOI, URL, named open problem. Call this `A` (boolean).
4. **Look for a project card docstring** (`/-! ... -/`) at the top of a new entry-point file under `LeanPool/`. Call this `C` (boolean).

Then:

- **`N ≤ 2` AND `A = false` → S1 blocking, full stop.** No interpretation, no "but the math is sophisticated." Two-or-fewer-lemmas-with-no-anchor is utility code by structural definition. The named lemma is *not* a "main theorem" for S1's purposes — main theorems sit at the top of a multi-step development with their dependencies introduced in the same PR.
- **`F = 1` AND `N ≤ 5` AND `A = false` → S1 blocking.** A single .lean file with at most a handful of declarations and no external anchor is an incremental contribution, not a project. (Exception: a complete formalization of a famous *named* problem in `≤ 5` declarations, e.g. an Erdős problem statement, with the problem named in the diff.)
- **`N ≥ 5` AND `F ≥ 2` AND (`A = true` OR `C = true`) → run S2–S7.** This is the "candidate project" shape; apply the full rules.
- **Anything else:** judgement call; lean toward `request_changes` and explain in the summary.

When in the summary, **state the values of N, F, A, C explicitly** so a maintainer can audit the verdict.

## Rules

### S1. Significance

**Severity:** blocking.

The PR must contribute substantive content at the **graduate or research level**, anchored in a paper, textbook, or named problem. The Decision flow above is the primary gate; this rule fills in the qualitative cases. Flag any PR that:

- adds only one or two declarations without a paper / textbook / problem anchor (regardless of how technical the proof is — see the binomial example in calibration);
- formalizes only an undergraduate-textbook exercise (probability identities, group-axiom-style commutativity / associativity / distributivity, basic real-analysis lemmas, etc.);
- consists of refactors, renamings, or reformulations of existing material with no new mathematical content;
- adds tactic helpers, `simp` lemmas, or general-purpose API without a paper / textbook anchoring them;
- looks like agent-driven incremental output ("add corollaries", "generalize API", "convolution lemma", "addition lemma") without a headline result.

**Do not be charitable** with phrases like "graduate-level," "self-contained," "main theorem," or "substantive." Apply them only when:

- "graduate-level" — the result would not appear in an undergraduate textbook in the field;
- "self-contained" — the diff *develops* a result through multiple intermediate definitions and lemmas, ending at a final theorem you can name in one phrase;
- "main theorem" — the PR description / project card *announces* it as such, not just any named declaration in the diff;
- "substantive" — there is an external anchor (paper, textbook, problem statement) the maintainer can compare against.

A PR's named declaration being labelled `theorem` or `lemma` does **not** make it a "main theorem" of a project. Most lemmas in mathlib are not project main theorems.

When the PR is small but the mathematics is genuinely nontrivial (a short proof of a *published* research result with the paper cited, a *named* open problem like Erdős 124, etc.), do **not** flag.

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

Applies to Lean **declarations** — `theorem`, `lemma`, `def`, `instance`, `structure`, etc. Does **not** apply to `import` statements: see the explicit non-target below.

Flag declarations that:

- restate something already provable in one line from another declaration in the same file or PR (`X.symm`, `X ▸ rfl`, `Eq.trans X Y`, alpha-renamings);
- are trivial reformulations of an immediately preceding lemma;
- exist only to be used once, immediately, inside the next proof, where they could be inlined or replaced with a `have`;
- look like a possible mathlib duplicate (advisory only — phrase as "possible duplicate of `Mathlib.X.Y` — please check"; you may be wrong).

Suggest the fix: delete, inline, or use the existing form.

**Do not flag** transitively-redundant `import` lines, especially in the root `LeanPool.lean` file. That file is auto-generated by `lake exe mk_all` (mathlib convention) and is required by the `mk_all --check` CI gate to import **every** `.lean` file in the library, regardless of whether some imports are reachable transitively. Flagging those produces broken suggestions.

### S7. Pointless infrastructure

**Severity:** info.

Flag changes that introduce types, structures, instances, or namespaces that do not appear to be used in the PR's main results, or that wrap existing mathlib structures without adding content. Building API for its own sake is the failure mode here.

## Output format

The reviewer must return JSON only, of the form:

```json
{
  "summary": "<2-3 sentences: what the PR claims to do, whether it belongs here, top concerns>",
  "shape": {
    "N": <int, count of new top-level declarations>,
    "F": <int, count of files with new declarations>,
    "A": <bool, paper/textbook/problem anchor present>,
    "C": <bool, project card docstring present>
  },
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

The `shape` field is **required**. If the Decision flow's automatic blockers fire (e.g. `N ≤ 2` and `A = false`), the verdict must be `request_changes` with at least one `S1` finding.

Verdict semantics:

- `approve` — clears all rules; no `blocking` or `warning` findings.
- `request_changes` — at least one `blocking` finding (S1, S2).
- `needs_discussion` — judgement is genuinely close (e.g. significance is borderline) and a human should weigh in.

If the PR has no rule violations, return `findings: []` and a one-sentence summary saying so.
