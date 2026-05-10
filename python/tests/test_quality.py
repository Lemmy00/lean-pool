"""Tests for deterministic repository quality checks."""

from __future__ import annotations

from pathlib import Path

from lean_pool.quality import (
    _axiom_audit_missing,
    _axiom_audit_resolved,
    _Declaration,
    _parse_declarations,
    _strip_lean_comments,
    run_checks,
)

HEADER = """/-
Copyright (c) 2026 Test Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Test Author
-/
"""


def _write_minimal_repo(root: Path, basic_body: str = 'def hello := "world"\n') -> None:
    """Create the smallest LeanPool tree accepted by static checks."""
    (root / "LeanPool").mkdir()
    (root / "LeanPool.lean").write_text("import LeanPool.Basic\n")
    (root / "LeanPool" / "Basic.lean").write_text(f"{HEADER}\n{basic_body}")
    (root / "LeanPool" / "projects.yml").write_text("tags: []\nprojects: []\n")
    (root / "lakefile.toml").write_text(
        'name = "lean-pool"\nversion = "0.1.0"\ndefaultTargets = ["LeanPool"]\n'
    )


def _write_project_yaml(root: Path, projects: list[dict[str, str]]) -> None:
    """Write a `projects.yml` containing the given project entries.

    The entries share a single tag vocabulary so individual tests don't have to
    repeat boilerplate. Each entry uses an `arxiv` source by default.
    """
    lines = ["tags: [test]", "projects:"]
    for project in projects:
        lines.extend(
            [
                f"  - slug: {project['slug']}",
                f"    title: {project.get('title', 'Test Project')}",
                f"    entry_module: {project['entry_module']}",
                "    authors: [Test Author]",
                "    source:",
                f'      arxiv: "{project.get("arxiv", "1234.5678")}"',
                f"    status: {project.get('status', 'verified')}",
                "    main_declarations: [hello]",
                "    tags: [test]",
            ]
        )
    (root / "LeanPool" / "projects.yml").write_text("\n".join(lines) + "\n")


def test_strip_lean_comments_preserves_code_not_comments() -> None:
    """Forbidden tokens in comments and strings are ignored."""
    stripped = _strip_lean_comments(
        "-- set_option maxHeartbeats 0\n"
        'def label := "sorry"\n'
        "/- admit -/\n"
        "def safe := 1\n"
    )

    assert "set_option" not in stripped
    assert "sorry" not in stripped
    assert "admit" not in stripped
    assert "def safe := 1" in stripped


def test_minimal_repo_passes_static_quality_checks(tmp_path: Path) -> None:
    """A compliant minimal repo passes without invoking Lean."""
    _write_minimal_repo(tmp_path)

    assert run_checks(tmp_path, skip_lean_axioms=True) == []


def test_quality_check_rejects_set_option(tmp_path: Path) -> None:
    """Lean files may not override options locally."""
    _write_minimal_repo(tmp_path, "set_option maxHeartbeats 0\n\ndef hello := 1\n")

    errors = run_checks(tmp_path, skip_lean_axioms=True)

    assert any("set_option is forbidden" in error.message for error in errors)


def test_quality_check_rejects_unreachable_lean_file(tmp_path: Path) -> None:
    """Every Lean file under LeanPool must be imported by LeanPool.lean."""
    _write_minimal_repo(tmp_path)
    (tmp_path / "LeanPool" / "Extra.lean").write_text(f"{HEADER}\ndef extra := 1\n")

    errors = run_checks(tmp_path, skip_lean_axioms=True)

    assert any("not reachable" in error.message for error in errors)


def test_quality_check_rejects_missing_project_metadata(tmp_path: Path) -> None:
    """Project metadata is required even before there are projects."""
    _write_minimal_repo(tmp_path)
    (tmp_path / "LeanPool" / "projects.yml").unlink()

    errors = run_checks(tmp_path, skip_lean_axioms=True)

    assert any("missing LeanPool/projects.yml" in error.message for error in errors)


def test_quality_check_finds_prefixed_declarations(tmp_path: Path) -> None:
    """The axiom audit declaration parser handles common Lean prefixes."""
    _write_minimal_repo(
        tmp_path,
        "@[simp] theorem decorated_identity (n : Nat) : n = n := rfl\n",
    )

    declarations = _parse_declarations(tmp_path)

    assert any(declaration.name == "decorated_identity" for declaration in declarations)


def test_quality_check_rejects_non_verified_status(tmp_path: Path) -> None:
    """Only `status: verified` projects may merge; `draft` is not accepted."""
    _write_minimal_repo(tmp_path)
    _write_project_yaml(
        tmp_path,
        [{"slug": "p", "entry_module": "LeanPool.Basic", "status": "draft"}],
    )

    errors = run_checks(tmp_path, skip_lean_axioms=True)

    assert any("invalid status" in error.message for error in errors)


def test_axiom_audit_resolved_parses_success_lines() -> None:
    """`#print axioms` success lines populate the resolved set; _root_ stripped."""
    stdout = (
        "'_root_.Foo.bar' depends on axioms: [Classical.choice, propext]\n"
        "'baz' depends on axioms: []\n"
    )

    assert _axiom_audit_resolved(stdout) == {"Foo.bar", "baz"}


def test_axiom_audit_missing_attributes_stderr_to_each_declaration(
    tmp_path: Path,
) -> None:
    """Per-declaration errors quote the matching stderr line."""
    decl_a = _Declaration(name="foo'", path=tmp_path / "A.lean", line=12, kind="lemma")
    decl_b = _Declaration(name="bar", path=tmp_path / "B.lean", line=34, kind="lemma")
    stderr = "/tmp/x.lean:5:0: error: unknown constant '_root_.foo''\n"

    errors = _axiom_audit_missing([decl_a, decl_b], stderr)

    assert len(errors) == 2
    assert errors[0].path == tmp_path / "A.lean" and errors[0].line == 12
    assert "unknown constant" in errors[0].message
    assert errors[1].path == tmp_path / "B.lean" and errors[1].line == 34
    assert "produced no result" in errors[1].message


def test_quality_check_rejects_extra_axiom_status(tmp_path: Path) -> None:
    """`extra-axiom` status was previously valid; only `verified` is now accepted."""
    _write_minimal_repo(tmp_path)
    _write_project_yaml(
        tmp_path,
        [{"slug": "p", "entry_module": "LeanPool.Basic", "status": "extra-axiom"}],
    )

    errors = run_checks(tmp_path, skip_lean_axioms=True)

    assert any("invalid status" in error.message for error in errors)
