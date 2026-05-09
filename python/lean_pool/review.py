"""LLM-driven pull request review for Lean Pool.

Reads the rules from ``.github/REVIEW_RULES.md``, fetches the PR diff via the
GitHub CLI, asks the configured OpenAI model to apply the rules, and posts the
findings as a single PR comment that includes token usage, the service tier
that served the request, and (optionally) estimated USD cost.

The reviewer prefers OpenAI's `flex` tier (cheaper, slower, occasionally
unavailable). When flex returns 429 Resource Unavailable, the request is
retried with `service_tier="auto"` (standard pricing). The rendered comment
shows which tier was actually used and costs the request at that tier's rate.

Per-token prices live in the ``PRICING_PER_M`` table below — the OpenAI
API does not return cost in its responses, so we maintain a small lookup
keyed on (model, tier). Update it when bumping ``DEFAULT_MODEL`` or when
OpenAI changes pricing.

Environment variables:
    OPENAI_API_KEY: OpenAI credentials (required).
    PR_NUMBER:      Pull request number to review (required).
    GH_TOKEN:       Token for the GitHub CLI (required in CI).
    REVIEW_MODEL:   Model name; defaults to ``gpt-5.4-mini``.

Run:
    uv run python -m lean_pool.review
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path
from textwrap import dedent
from typing import Any

from openai import OpenAI, RateLimitError

REPO_ROOT = Path(__file__).resolve().parents[2]
RULES_PATH = REPO_ROOT / ".github" / "REVIEW_RULES.md"
DEFAULT_MODEL = "gpt-5.4-mini"
# Flex tier requests can take longer than the default 10-minute timeout.
REQUEST_TIMEOUT_SECONDS = 6000.0

# USD per 1M tokens, keyed by (model, tier) -> (input_per_M, output_per_M).
# Source: https://developers.openai.com/api/docs/pricing — update when
# bumping DEFAULT_MODEL or when OpenAI changes pricing.
PRICING_PER_M: dict[str, dict[str, tuple[float, float]]] = {
    "gpt-5.4-mini": {
        "flex": (0.375, 2.25),
        "standard": (0.75, 4.50),
    },
}

SEVERITY_ICON = {"info": "ℹ️", "warning": "⚠️", "blocking": "🛑"}
VERDICT_ICON = {
    "approve": "✅",
    "request_changes": "🛑",
    "needs_discussion": "🤔",
}

SYSTEM_PROMPT = dedent(
    """\
    You are an automated reviewer for Lean Pool, a curated repository of
    Lean 4 formalization projects. Your job is to make the judgement calls
    that automated linters cannot make: significance of contribution,
    self-containment, project-card presence, informal-vs-formal
    correspondence, proof verbosity, and redundancy.

    Mechanical checks (presence of sorry, file headers, naming, size limits,
    heartbeats, axiom audits, simp discipline, docstring presence) are
    handled by linters elsewhere in CI. Do NOT flag those here, even if you
    notice them.

    Before applying any qualitative rule, walk the Decision flow in the
    rules document. Compute and report in your JSON output:

    - N = number of new top-level declarations (theorem / lemma / def /
      instance / structure / inductive / class) in the diff
    - F = number of files containing new declarations
    - A = whether the PR description, project card, or doc comments cite
      a paper / textbook / named open problem
    - C = whether a `/-! ... -/` project-card docstring is present at the
      top of a new entry-point file under `LeanPool/`

    If `N <= 2` and `A` is false, OR if `F == 1` and `N <= 5` and `A` is
    false, the verdict MUST be `request_changes` with at least one `S1`
    finding. Do not be charitable with words like "substantive,"
    "graduate-level," "self-contained," or "main theorem" — apply them
    only when there is an external anchor and the PR develops a result
    through multiple intermediate steps. A declaration being labelled
    `theorem` does not make it the main theorem of a project.

    You flag only specific, actionable rule violations. You do not make
    stylistic comments outside the rules. When in doubt about everything
    else, you say nothing.

    You always respond with a single JSON object matching the schema given
    in the rules document. No prose outside the JSON.
    """
)


def run_gh(*args: str, stdin: str | None = None) -> str:
    """Run ``gh`` with the given arguments and return stdout.

    Args:
        *args: Arguments to pass after ``gh``.
        stdin: Optional string piped to the subprocess on stdin.

    Returns:
        The captured stdout, decoded as text.

    Raises:
        subprocess.CalledProcessError: If gh exits non-zero.
    """
    result = subprocess.run(
        ["gh", *args],
        check=True,
        capture_output=True,
        text=True,
        input=stdin,
    )
    return result.stdout


def fetch_diff(pr_number: str) -> str:
    """Return the full unified diff for ``pr_number``, untruncated."""
    return run_gh("pr", "diff", pr_number)


def request_review(model: str, rules: str, diff: str) -> tuple[dict, Any, str]:
    """Ask the model to apply ``rules`` to ``diff``.

    Tries the ``flex`` service tier first; if OpenAI returns 429 Resource
    Unavailable, retries with ``service_tier="auto"`` (standard tier).

    Returns:
        ``(payload, usage, tier)`` where ``payload`` is the parsed JSON
        review, ``usage`` is the OpenAI ``CompletionUsage`` object (or
        ``None``), and ``tier`` is ``"flex"`` or ``"standard"``.
    """
    client = OpenAI(timeout=REQUEST_TIMEOUT_SECONDS)
    user_content = f"## Review rules\n\n{rules}\n\n## PR diff\n\n```diff\n{diff}\n```"
    messages = [
        {"role": "system", "content": SYSTEM_PROMPT},
        {"role": "user", "content": user_content},
    ]

    try:
        response = client.chat.completions.create(
            model=model,
            messages=messages,
            response_format={"type": "json_object"},
            service_tier="flex",
        )
        tier = "flex"
    except RateLimitError:
        # Flex pool exhausted; retry on standard tier.
        response = client.chat.completions.create(
            model=model,
            messages=messages,
            response_format={"type": "json_object"},
            service_tier="auto",
        )
        tier = "standard"

    content = response.choices[0].message.content or "{}"
    return json.loads(content), response.usage, tier


def render_usage(usage: Any, model: str, tier: str) -> str:
    """Render a one-line token / tier / cost footer.

    Returns an empty string if ``usage`` is unavailable. Cost is computed
    from :data:`PRICING_PER_M` and suppressed when the model/tier pair is
    not listed there.
    """
    if usage is None:
        return ""
    in_tok = getattr(usage, "prompt_tokens", 0) or 0
    out_tok = getattr(usage, "completion_tokens", 0) or 0

    parts = [f"**Tokens:** {in_tok:,} in / {out_tok:,} out", f"**Tier:** `{tier}`"]
    rates = PRICING_PER_M.get(model, {}).get(tier)
    if rates is not None:
        in_price, out_price = rates
        cost = (in_tok * in_price + out_tok * out_price) / 1_000_000
        parts.append(f"**Cost:** ${cost:.4f}")
    else:
        parts.append(f"_(no pricing recorded for `{model}` at `{tier}` tier)_")
    return " · ".join(parts)


def render_shape(payload: dict) -> str:
    """Render the shape (N, F, A, C) audit line, or empty if absent."""
    shape = payload.get("shape") or {}
    if not shape:
        return ""
    n = shape.get("N", "?")
    f = shape.get("F", "?")
    a = shape.get("A")
    c = shape.get("C")
    a_str = "true" if a is True else "false" if a is False else "?"
    c_str = "true" if c is True else "false" if c is False else "?"
    return (
        f"**Shape:** `N={n}` (decls) · `F={f}` (files) · "
        f"`A={a_str}` (anchor) · `C={c_str}` (project card)"
    )


def render_comment(
    payload: dict,
    model: str,
    usage: Any,
    tier: str,
) -> str:
    """Render the model's payload as a Markdown PR comment body."""
    summary = (payload.get("summary") or "").strip()
    verdict = (payload.get("verdict") or "").strip()
    findings = payload.get("findings") or []

    lines = [f"## 🤖 LLM review (`{model}`)", ""]

    shape_line = render_shape(payload)
    if shape_line:
        lines.extend([shape_line, ""])

    if verdict:
        icon = VERDICT_ICON.get(verdict, "•")
        lines.extend([f"**Verdict:** {icon} `{verdict}`", ""])

    lines.extend([summary, ""])

    if not findings:
        lines.append("_No rule violations found._")
    else:
        lines.append(f"### Findings ({len(findings)})")
        lines.append("")
        for f in findings:
            icon = SEVERITY_ICON.get(f.get("severity", "info"), "•")
            path = f.get("file") or ""
            line_no = f.get("line", 0) or 0
            if path and line_no:
                ref = f"`{path}:{line_no}`"
            elif path:
                ref = f"`{path}`"
            else:
                ref = "_PR-wide_"
            rule = f.get("rule", "")
            body = (f.get("comment") or "").strip()
            lines.append(f"- {icon} **{rule}** — {ref}")
            lines.append(f"  {body}")

    lines.append("")
    lines.append("---")
    usage_line = render_usage(usage, model, tier)
    if usage_line:
        lines.append(usage_line)
    lines.append(
        "_Automated review against "
        "[`.github/REVIEW_RULES.md`](../blob/main/.github/REVIEW_RULES.md). "
        "Disagree? Reply on the PR; rules can be updated in a PR of their own._"
    )
    return "\n".join(lines)


def post_comment(pr_number: str, body: str) -> None:
    """Post ``body`` as a top-level PR comment."""
    run_gh("pr", "comment", pr_number, "--body-file", "-", stdin=body)


def main() -> int:
    """Entry point: orchestrate fetch, review, and post."""
    pr_number = os.environ.get("PR_NUMBER")
    if not pr_number:
        print("PR_NUMBER not set", file=sys.stderr)
        return 2
    if not os.environ.get("OPENAI_API_KEY"):
        print("OPENAI_API_KEY not set", file=sys.stderr)
        return 2

    model = os.environ.get("REVIEW_MODEL", DEFAULT_MODEL)
    rules = RULES_PATH.read_text(encoding="utf-8")
    diff = fetch_diff(pr_number)

    if not diff.strip():
        print("Empty diff; nothing to review.", file=sys.stderr)
        return 0

    payload, usage, tier = request_review(model=model, rules=rules, diff=diff)
    comment = render_comment(payload, model=model, usage=usage, tier=tier)
    post_comment(pr_number, comment)
    return 0


if __name__ == "__main__":
    sys.exit(main())
