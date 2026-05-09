"""LLM-driven pull request review for Lean Pool.

Reads the rules from ``.github/REVIEW_RULES.md``, fetches the PR diff via the
GitHub CLI, asks the configured OpenAI model to apply the rules, and posts the
findings as a single PR comment that includes token usage, the service tier
that served the request, and (optionally) estimated USD cost.

The reviewer prefers OpenAI's `flex` tier (cheaper, slower, occasionally
unavailable). When flex returns 429 Resource Unavailable, the request is
retried with `service_tier="auto"` (standard pricing). The rendered comment
shows which tier was actually used and costs the request at that tier's rate.

Environment variables:
    OPENAI_API_KEY:                 OpenAI credentials (required).
    PR_NUMBER:                      Pull request number to review (required).
    GH_TOKEN:                       Token for the GitHub CLI (required in CI).
    REVIEW_MODEL:                   Model name; defaults to ``gpt-5.4-mini``.
    INPUT_PRICE_PER_M_FLEX:         USD per 1M input tokens at flex rates.
    OUTPUT_PRICE_PER_M_FLEX:        USD per 1M output tokens at flex rates.
    INPUT_PRICE_PER_M_STANDARD:     USD per 1M input tokens at standard rates.
    OUTPUT_PRICE_PER_M_STANDARD:    USD per 1M output tokens at standard rates.

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
REQUEST_TIMEOUT_SECONDS = 900.0

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

    You flag only specific, actionable rule violations. You do not make
    stylistic comments outside the rules. When in doubt, you say nothing.

    You always respond with a single JSON object matching the schema given
    in the rules document. No prose outside the JSON.
    """
)


def _float_env(name: str) -> float:
    """Read a non-negative float from the environment, defaulting to 0."""
    raw = os.environ.get(name, "").strip()
    if not raw:
        return 0.0
    try:
        return max(0.0, float(raw))
    except ValueError:
        return 0.0


def load_pricing() -> dict[str, tuple[float, float]]:
    """Load (input_per_m, output_per_m) per service tier from the environment."""
    return {
        "flex": (
            _float_env("INPUT_PRICE_PER_M_FLEX"),
            _float_env("OUTPUT_PRICE_PER_M_FLEX"),
        ),
        "standard": (
            _float_env("INPUT_PRICE_PER_M_STANDARD"),
            _float_env("OUTPUT_PRICE_PER_M_STANDARD"),
        ),
    }


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


def render_usage(usage: Any, tier: str, prices: dict[str, tuple[float, float]]) -> str:
    """Render a one-line token / tier / cost footer.

    Returns an empty string if ``usage`` is unavailable.
    """
    if usage is None:
        return ""
    in_tok = getattr(usage, "prompt_tokens", 0) or 0
    out_tok = getattr(usage, "completion_tokens", 0) or 0
    in_price, out_price = prices.get(tier, (0.0, 0.0))

    parts = [f"**Tokens:** {in_tok:,} in / {out_tok:,} out"]
    parts.append(f"**Tier:** `{tier}`")
    if in_price > 0 or out_price > 0:
        cost = (in_tok * in_price + out_tok * out_price) / 1_000_000
        parts.append(f"**Cost:** ${cost:.4f}")
    else:
        parts.append(f"_(set INPUT/OUTPUT_PRICE_PER_M_{tier.upper()} for cost)_")
    return " · ".join(parts)


def render_comment(
    payload: dict,
    model: str,
    usage: Any,
    tier: str,
    prices: dict[str, tuple[float, float]],
) -> str:
    """Render the model's payload as a Markdown PR comment body."""
    summary = (payload.get("summary") or "").strip()
    verdict = (payload.get("verdict") or "").strip()
    findings = payload.get("findings") or []

    lines = [f"## 🤖 LLM review (`{model}`)", ""]

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
    usage_line = render_usage(usage, tier, prices)
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
    prices = load_pricing()

    rules = RULES_PATH.read_text(encoding="utf-8")
    diff = fetch_diff(pr_number)

    if not diff.strip():
        print("Empty diff; nothing to review.", file=sys.stderr)
        return 0

    payload, usage, tier = request_review(model=model, rules=rules, diff=diff)
    comment = render_comment(
        payload,
        model=model,
        usage=usage,
        tier=tier,
        prices=prices,
    )
    post_comment(pr_number, comment)
    return 0


if __name__ == "__main__":
    sys.exit(main())
