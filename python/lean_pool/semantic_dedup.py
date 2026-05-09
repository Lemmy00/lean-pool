"""Advisory LeanExplore duplicate search for changed Lean declarations."""

from __future__ import annotations

import argparse
import asyncio
import os
import re
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from lean_pool.quality import _strip_lean_comments

DECLARATION_PREFIX = (
    r"(?:@\[[^\n\]]+\]\s+)*"
    r"(?:(?:private|protected|noncomputable|scoped)\s+)*"
)
DECLARATION_RE = re.compile(
    rf"^\s*{DECLARATION_PREFIX}(?:theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_'.]*)\b"
)
NEXT_COMMAND_RE = re.compile(
    rf"^\s*{DECLARATION_PREFIX}"
    r"(?:theorem|lemma|def|abbrev|instance|class|structure|inductive)\b"
)


@dataclass(frozen=True)
class _Statement:
    path: Path
    line: int
    name: str
    query: str


@dataclass(frozen=True)
class _SearchResult:
    name: str
    module: str
    source_link: str


def _changed_lean_files(root: Path, base: str) -> list[Path]:
    process = subprocess.run(
        ["git", "diff", "--name-only", f"{base}...HEAD"],
        cwd=root,
        check=False,
        capture_output=True,
        text=True,
    )
    if process.returncode != 0:
        return sorted((root / "LeanPool").rglob("*.lean"))
    files = []
    for line in process.stdout.splitlines():
        path = root / line
        if path.suffix == ".lean" and path.is_file() and "LeanPool" in path.parts:
            files.append(path)
    return sorted(files)


def _extract_statements(path: Path) -> list[_Statement]:
    text = path.read_text()
    stripped_lines = _strip_lean_comments(text).splitlines()
    statements: list[_Statement] = []
    index = 0
    while index < len(stripped_lines):
        line = stripped_lines[index]
        match = DECLARATION_RE.match(line)
        if not match:
            index += 1
            continue
        if _is_private_declaration_line(line):
            index += 1
            continue
        end = _statement_end(stripped_lines, index)
        query = _statement_query(stripped_lines[index:end])
        if query:
            statements.append(_Statement(path, index + 1, match.group(1), query))
        index = end
    return statements


def _statement_end(lines: list[str], start: int) -> int:
    index = start + 1
    while index < len(lines):
        if ":=" in lines[index]:
            return index + 1
        if NEXT_COMMAND_RE.match(lines[index]):
            return index
        index += 1
    return len(lines)


def _is_private_declaration_line(line: str) -> bool:
    line = re.sub(r"^\s*(?:@\[[^\n\]]+\]\s+)*", "", line)
    return "private" in line.split()


def _statement_query(lines: list[str]) -> str:
    joined = " ".join(line.strip() for line in lines if line.strip())
    statement = joined.split(":=", maxsplit=1)[0]
    return re.sub(r"\s+", " ", statement).strip()


def _field(result: Any, field: str) -> Any:
    if isinstance(result, dict):
        return result.get(field)
    return getattr(result, field, None)


async def _search_statement(
    client: Any, statement: _Statement, limit: int
) -> list[_SearchResult]:
    response = await client.search(
        query=statement.query,
        limit=limit,
        packages=["Mathlib"],
    )
    results = []
    for result in getattr(response, "results", []):
        results.append(
            _SearchResult(
                name=str(_field(result, "name") or ""),
                module=str(_field(result, "module") or ""),
                source_link=str(_field(result, "source_link") or ""),
            )
        )
    return results


async def _run_search(
    statements: list[_Statement], limit: int
) -> dict[_Statement, list[_SearchResult]]:
    from lean_explore.api import ApiClient

    client = ApiClient()
    pairs = await asyncio.gather(
        *(_search_statement(client, statement, limit) for statement in statements)
    )
    return dict(zip(statements, pairs, strict=True))


def _markdown(
    root: Path,
    statements: list[_Statement],
    results: dict[_Statement, list[_SearchResult]],
) -> str:
    if not statements:
        return (
            "### LeanExplore semantic dedup\n\n"
            "No changed theorem or lemma statements found.\n"
        )

    lines = ["### LeanExplore semantic dedup", ""]
    for statement in statements:
        relative = statement.path.relative_to(root)
        lines.append(f"#### `{statement.name}` in `{relative}:{statement.line}`")
        lines.append("")
        matches = results.get(statement, [])
        if not matches:
            lines.append("No Mathlib candidates returned.")
            lines.append("")
            continue
        lines.append("| Candidate | Module | Source |")
        lines.append("| --- | --- | --- |")
        for match in matches:
            source = f"[link]({match.source_link})" if match.source_link else ""
            lines.append(
                f"| `{_escape(match.name)}` | `{_escape(match.module)}` | {source} |"
            )
        lines.append("")
    lines.append("_Advisory only: semantic similarity never blocks a PR by itself._")
    return "\n".join(lines) + "\n"


def _escape(value: str) -> str:
    return value.replace("|", r"\|")


def _parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--repo", type=Path, default=Path(__file__).resolve().parents[2]
    )
    parser.add_argument("--base", default="origin/main")
    parser.add_argument("--limit", type=int, default=5)
    parser.add_argument("--output", type=Path)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    """Run the LeanExplore duplicate search CLI."""
    args = _parse_args(sys.argv[1:] if argv is None else argv)
    root = args.repo.resolve()
    if not os.environ.get("LEANEXPLORE_API_KEY"):
        print("LEANEXPLORE_API_KEY is not set; skipping semantic dedup.")
        return 0

    statements = [
        statement
        for path in _changed_lean_files(root, args.base)
        for statement in _extract_statements(path)
    ]
    results = asyncio.run(_run_search(statements, args.limit)) if statements else {}
    markdown = _markdown(root, statements, results)
    if args.output:
        args.output.write_text(markdown)
    else:
        print(markdown)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
