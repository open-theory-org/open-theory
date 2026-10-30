# /// script
# requires-python = ">=3.11"
# dependencies = ["mcp>=1.10,<2"]
# ///
"""OpenTheory MCP server (stdio). Run: `uv run interfaces/mcp/server.py`.

The tools live in opentheory_mcp/ (standard library only, tested in CI); this file only
describes them to MCP clients.
"""
from __future__ import annotations

import sys
from pathlib import Path
from typing import Annotated, Any, Literal

import anyio
from mcp.server.fastmcp import FastMCP
from mcp.types import ToolAnnotations
from pydantic import Field

sys.path.insert(0, str(Path(__file__).resolve().parent))
from opentheory_mcp import tools  # noqa: E402

INSTRUCTIONS = """\
OpenTheory: a Lean 4 + Mathlib library with a leanblueprint (blueprint/src/content.tex).
Work loop: list_targets → get_target → check_proof (repeat until ok) → commit_proof.
- A proof is the Lean text after `:=` (usually a `by` block). The statement is never edited.
- A proof counts only when the Lean kernel accepts it and `#print axioms` shows nothing beyond
  propext, Classical.choice and Quot.sound. sorry/admit and new commands are refused.
- commit_proof creates a new branch off HEAD; it does not change the checkout or push anything.
"""

mcp = FastMCP("opentheory", instructions=INSTRUCTIONS, log_level="WARNING")
READ = ToolAnnotations(readOnlyHint=True, idempotentHint=True, openWorldHint=False)

Target = Annotated[str, Field(description="Blueprint label (e.g. 'lem:alignment_nonneg') or Lean name "
                                          "(full, or a unique suffix such as 'alignment_nonneg')")]
PROOF = ("Lean text that replaces everything after the declaration's `:=`: "
         "a term, or a `by` block such as 'by\\n  intro x\\n  simp'")
Proof = Annotated[str, Field(description=PROOF)]
Timeout = Annotated[int, Field(ge=10, le=7200, description="Seconds before Lean is stopped")]


async def _call(fn, *args):
    # Lean runs take minutes; keep the event loop free for the protocol meanwhile.
    return await anyio.to_thread.run_sync(lambda: fn(*args))


@mcp.tool(annotations=READ)
async def list_targets(
    include_verified: Annotated[bool, Field(description="Also list nodes whose proof is already verified")] = False,
    kind: Annotated[Literal["definition", "lemma", "theorem", "proposition", "corollary", "conjecture"] | None,
                    Field(description="Only this blueprint environment")] = None,
    ready_only: Annotated[bool, Field(description="Only targets whose dependencies are all verified")] = False,
    min_bounty_usd: Annotated[int | None, Field(description="Only targets whose blueprint bounty is at least this")] = None,
) -> dict[str, Any]:
    """List blueprint nodes that are not yet verified, with their Lean declarations and whether each
    still uses sorry. Also reports inconsistencies between the blueprint and the Lean source."""
    return await _call(tools.list_targets, include_verified, kind, ready_only, min_bounty_usd)


@mcp.tool(annotations=READ)
async def get_target(target: Target) -> dict[str, Any]:
    """Everything needed to prove a target: its LaTeX statement and informal proof, its Lean
    declarations with source, and each dependency's statement in LaTeX and Lean."""
    return await _call(tools.get_target, target)


@mcp.tool(annotations=READ)
async def check_proof(
    target: Target,
    proof: Annotated[str | None, Field(description=PROOF + ". Omit to check the file as it is")] = None,
    timeout_s: Timeout = 900,
) -> dict[str, Any]:
    """Check a proof with the Lean kernel without touching the repository: the declaration's file is
    copied with the proof spliced in, compiled with `lake env lean`, and its axioms printed.
    ok is true only with no errors and only the standard axioms."""
    return await _call(tools.check_proof, target, proof, timeout_s)


@mcp.tool(annotations=ToolAnnotations(readOnlyHint=False, destructiveHint=False, idempotentHint=False,
                                      openWorldHint=False))
async def commit_proof(
    target: Target,
    proof: Proof,
    branch: Annotated[str | None, Field(description="New branch name (default proof/<name>)")] = None,
    message: Annotated[str | None, Field(description="Commit subject (default 'proof: <Lean name>')")] = None,
    timeout_s: Timeout = 900,
) -> dict[str, Any]:
    """Re-check the proof, then commit it to a new branch off HEAD together with the blueprint update
    (\\leanok in content.tex, regenerated blueprint.json). The checkout is left unchanged. Refused
    if the files involved have uncommitted changes or the branch exists."""
    return await _call(tools.commit_proof, target, proof, branch, message, timeout_s)


@mcp.tool(annotations=READ)
async def audit_repository(
    build: Annotated[bool, Field(description="Run `lake build` first (needed after Lean changes)")] = True,
    timeout_s: Annotated[int, Field(ge=10, le=14400, description="Seconds allowed per step")] = 3600,
) -> dict[str, Any]:
    """Run the repository's own checks, as CI does: blueprint \\lean names, method catalog, blueprint.json
    freshness, lake build and the whole-library axiom audit."""
    return await _call(tools.audit_repository, build, timeout_s)


@mcp.tool(annotations=READ)
async def verify_certificate(
    bundle: Annotated[str, Field(description="Certificate bundle directory (holding certificate.json), "
                                             "absolute or relative to the repository")],
    timeout_s: Annotated[int, Field(ge=10, le=7200, description="Lean kernel time limit in seconds")] = 1800,
) -> dict[str, Any]:
    """`ot verify`: check a certificate bundle and report the claim, its assurance level, what was
    checked, what is assumed and what is trusted."""
    return await _call(tools.verify_certificate, bundle, timeout_s)


if __name__ == "__main__":
    mcp.run()
