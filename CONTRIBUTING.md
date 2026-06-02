# Contributing to Lean Pool

Lean Pool sits between `mathlib` and `merely-true` — like arXiv for formal mathematics. We welcome medium and large formalizations of serious mathematics and related disciplines. Check the existing projects in Lean Pool for examples. Pull Requests need to pass the deterministic CI such as linters, the LLM reviewer and the profiler.

## Linting and Testing

**Never change the checks or gates themselves.** Do not modify `.github/workflows/`, `.github/CODE_QUALITY.md`, `python/lean_pool/quality.py`, `scripts/nolints-style.txt`, the `[leanOptions]`/lint settings in `lakefile.toml`, or any other CI step, quality gate, or linter configuration — and do not add an exception or waiver of any kind (a `size-limit-ok` comment, a `nolints-style.txt` entry, `set_option linter.X false`, etc.) — unless the user has explicitly asked for that exact change. If a check fails, fix the code, not the check. This applies to everyone, and especially to AI agents working on the repo.

### Lean

CI currently runs `lake exe mk_all --check`, `lake build LeanPool`, `lake exe runLinter LeanPool`, `lake exe lint-style LeanPool`, and the repository quality checker (see [`.github/workflows/lean_action_ci.yml`](.github/workflows/lean_action_ci.yml)). Build locally with `lake build`. Project-wide code-quality conventions and future work are documented in [`.github/CODE_QUALITY.md`](.github/CODE_QUALITY.md).
