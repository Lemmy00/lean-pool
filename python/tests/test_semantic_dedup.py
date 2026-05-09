"""Tests for LeanExplore semantic dedup query extraction."""

from __future__ import annotations

from pathlib import Path

from lean_pool.semantic_dedup import _extract_statements


def test_extract_statements_uses_docstring_query(tmp_path: Path) -> None:
    """LeanExplore queries come from natural-language theorem docstrings."""
    path = tmp_path / "Example.lean"
    path.write_text(
        "/-- Addition by zero leaves a natural number unchanged. -/\n"
        "@[simp] theorem add_zero_example (n : Nat) : n + 0 = n := by\n"
        "  exact Nat.add_zero n\n"
    )

    extraction = _extract_statements(path)

    assert len(extraction.statements) == 1
    assert extraction.statements[0].query == (
        "Addition by zero leaves a natural number unchanged."
    )
    assert extraction.skipped == []


def test_extract_statements_skips_undocumented_declarations(tmp_path: Path) -> None:
    """Undocumented theorems are not queried with Lean syntax."""
    path = tmp_path / "Example.lean"
    path.write_text("theorem undocumented (n : Nat) : n = n := rfl\n")

    extraction = _extract_statements(path)

    assert extraction.statements == []
    assert len(extraction.skipped) == 1
    assert extraction.skipped[0].name == "undocumented"
