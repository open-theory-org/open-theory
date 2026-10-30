"""The blueprint as blueprint/export_blueprint.py reads it: one parser for CI, the feed and agents."""
from __future__ import annotations

import contextlib
import importlib.util
import io
import re

from . import ROOT

_spec = importlib.util.spec_from_file_location("export_blueprint", ROOT / "blueprint/export_blueprint.py")
exporter = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(exporter)

CONTENT = exporter.CONTENT_TEX


def nodes() -> dict[str, dict]:
    """Blueprint nodes by label, from content.tex as it is now (not the possibly stale JSON)."""
    return {n["id"]: n for n in exporter.blueprint_payload()["nodes"]}


def statements() -> dict[str, str]:
    text = CONTENT.read_text(encoding="utf-8")
    return {m.group(3): exporter.strip_macros(m.group(4)) for m in exporter.ENV_RE.finditer(text)}


def status(node: dict) -> str:
    if node["isVerified"]:
        return "verified"
    return "statement_only" if node["statementFormalized"] else "unformalized"


def regenerate() -> None:
    """Rewrite blueprint.json. The exporter prints to stdout, which belongs to the MCP stream."""
    with contextlib.redirect_stdout(io.StringIO()):
        exporter.parse_blueprint(exporter.DEFAULT_OUTPUT)


def mark_proved(tex: str, label: str) -> tuple[str, list[str]]:
    """Add `\\leanok` to the statement and to the proof of `label` (Massot convention).

    Returns the new text and notes on anything that could not be marked.
    """
    for m in exporter.ENV_RE.finditer(tex):
        if m.group(3) == label:
            break
    else:
        return tex, [f"no environment labelled {label} in content.tex"]
    kind, body = m.group(1), m.group(4)
    notes = []

    after = tex[m.end():]
    proof = exporter.PROOF_RE.match(after)
    if proof and r"\leanok" not in proof.group(1):
        opening = after.index(r"\begin{proof}", 0, proof.end()) + len(r"\begin{proof}")
        after = after[:opening] + "\n\\leanok" + after[opening:]
    elif not proof and kind != "definition":
        notes.append(f"{label} has no proof environment, so the blueprint cannot record the proof; add one")

    if r"\leanok" not in body:
        lean = list(re.finditer(r"\\lean\{.*?\}", body))
        if lean:
            body = body[:lean[-1].end()] + "\n\\leanok" + body[lean[-1].end():]
        else:
            notes.append(rf"{label} has no \lean{{}} reference")
    start = m.start(4)
    return tex[:start] + body + tex[m.end(4):m.end()] + after, notes
