"""LLM-driven pull request review for Lean Pool.

Reads the rules from ``.github/REVIEW_RULES.md``, fetches the PR diff via the
GitHub CLI, asks the configured OpenAI model to apply the rules, and posts the
findings as a single PR comment.

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

from openai import OpenAI

REPO_ROOT = Path(__file__).resolve().parents[2]
RULES_PATH = REPO_ROOT / ".github" / "REVIEW_RULES.md"
MAX_DIFF_BYTES = 200_000
DEFAULT_MODEL = "gpt-5.4-mini"

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
    """Return the unified diff for ``pr_number``, truncated for cost control."""
    diff = run_gh("pr", "diff", pr_number)
    if len(diff) > MAX_DIFF_BYTES:
        diff = diff[:MAX_DIFF_BYTES] + "\n\n[diff truncated for length]"
    return diff


def request_review(model: str, rules: str, diff: str) -> dict:
    """Ask the model to apply ``rules`` to ``diff`` and return parsed JSON."""
    client = OpenAI()
    response = client.chat.completions.create(
        model=model,
        messages=[
            {"role": "system", "content": SYSTEM_PROMPT},
            {
                "role": "user",
                "content": (
                    f"## Review rules\n\n{rules}\n\n## PR diff\n\n```diff\n{diff}\n```"
                ),
            },
        ],
        response_format={"type": "json_object"},
    )
    content = response.choices[0].message.content or "{}"
    return json.loads(content)


def render_comment(payload: dict, model: str) -> str:
    """Render the model's payload as a Markdown PR comment body."""
    summary = (payload.get("summary") or "").strip()
    verdict = (payload.get("verdict") or "").strip()
    findings = payload.get("findings") or []

    verdict_line = ""
    if verdict:
        icon = VERDICT_ICON.get(verdict, "•")
        verdict_line = f"**Verdict:** {icon} `{verdict}`"

    lines = [f"## 🤖 LLM review (`{model}`)", ""]
    if verdict_line:
        lines.extend([verdict_line, ""])
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

    payload = request_review(model=model, rules=rules, diff=diff)
    comment = render_comment(payload, model=model)
    post_comment(pr_number, comment)
    return 0


if __name__ == "__main__":
    sys.exit(main())
