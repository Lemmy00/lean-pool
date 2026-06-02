<p align="center">
  <img src="logo.png" alt="Lean Pool logo" width="240">
</p>

# lean-pool

[![Lean Action CI](https://github.com/Vilin97/lean-pool/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/Vilin97/lean-pool/actions/workflows/lean_action_ci.yml)
[![Documentation](https://img.shields.io/badge/docs-online-blue)](https://vilin97.github.io/lean-pool/)
[![License](https://img.shields.io/github/license/Vilin97/lean-pool)](LICENSE)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.20513444.svg)](https://doi.org/10.5281/zenodo.20513444)

Lean Pool sits between [`mathlib`](https://github.com/leanprover-community/mathlib4) and [`merely-true`](https://github.com/merely-true/merely-true), preserving Lean 4 formalizations that don't fit mathlib's scope. Instead of mathlib's high-bar human review, it relies on deterministic linters and LLM judgment, so it can grow faster while staying `sorry`-free and pinned to the latest Mathlib. See [`MOTIVATION.md`](MOTIVATION.md) for the why, and browse the API docs at <https://vilin97.github.io/lean-pool/>.

### How it works

`discover → lint → review → promote`

1. **Discover** Lean packages from the [Reservoir](https://reservoir.lean-lang.org) manifest plus a curated list of GitHub repos.
2. **Lint** deterministically: no `sorry`/`admit`, no axioms beyond `Classical.choice`/`propext`/`Quot.sound`, no `unsafe`/`partial`, file headers, and size limits.
3. **Review** with an LLM against [`.github/REVIEW_RULES.md`](.github/REVIEW_RULES.md) for fit, significance, and code quality.
4. **Promote** accepted projects into `LeanPool/` and register them in [`LeanPool/projects.yml`](LeanPool/projects.yml).

### Repository layout

| Path | Contents |
| --- | --- |
| [`LeanPool/`](LeanPool/) | The pooled library; each subfolder is one project. |
| [`LeanPool/projects.yml`](LeanPool/projects.yml) | Project registry: slug, authors, main results, source, tags. |
| [`python/`](python/) | Aggregation, quality, and LLM-review tooling. |
| [`candidates/`](candidates/) | Candidate intake: criteria, queues, decision log. |
| [`.github/`](.github/) | CI workflows, quality gates, review rules. |

### Getting started

Requires Lean (via [`elan`](https://leanprover-community.github.io/install/), with the toolchain pinned in [`lean-toolchain`](lean-toolchain)) and Python 3.13+ with [`uv`](https://docs.astral.sh/uv/).

```bash
make setup    # pull Mathlib oleans, build LeanPool, install Python tooling
```

### Contributing

See [`CONTRIBUTING.md`](CONTRIBUTING.md).

### Credits

Created as part of the [UW Lean Hackathon](https://uw2026leanhackathon.github.io/) by [Vasily Ilin](https://github.com/Vilin97) and [Justin Asher](https://github.com/justincasher).
