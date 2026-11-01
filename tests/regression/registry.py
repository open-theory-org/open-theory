"""Shared loader for the registries: the cards of specs/ and the manifests of catalog/.

One link per fact, each written once:

    claim card (specs/claims)        what is claimed: a Spec, and the `Sound` theorem(s) for it
      ↑ establishes                  a certifying method: its accepted check is the `accepts` of `Sound`
    method (catalog/methods)         how: the check the kernel runs and why it is correct
      ↑ feeds                        a method computing an input another method checks
    guarantee (catalog/guarantees)   what a certificate names: one claim and the methods it uses

A method's level is derived from these links (`derive`), never only declared.
"""
from __future__ import annotations

import re
import tomllib
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SPECS = ROOT / "specs"
LEVELS = ["experimental", "specified", "verified"]
MODES = {"verified-implementation", "verified-checker"}


def cards(kind: str) -> dict[str, tuple[Path, dict | None]]:
    """The cards of specs/<kind>/, by file stem, each with its `+++` TOML header (None if absent)."""
    out = {}
    for path in sorted((SPECS / kind).glob("*.md")):
        if path.name == "README.md":
            continue
        m = re.match(r"\+\+\+\n(.*?)\n\+\+\+\n", path.read_text(encoding="utf-8"), re.S)
        out[path.stem] = (path, tomllib.loads(m.group(1)) if m else None)
    return out


def catalog(kind: str) -> dict[str, tuple[Path, dict]]:
    """The manifests of catalog/<kind>/, by file stem."""
    return {p.stem: (p, tomllib.loads(p.read_text(encoding="utf-8")))
            for p in sorted((ROOT / "catalog" / kind).glob("*.toml"))}


def registry_checks() -> set[str]:
    """The fast checks of formal/core/Checks/Registry.lean, by their CLI name."""
    return set(re.findall(r'cli := "([^"]+)"', (ROOT / "formal/core/Checks/Registry.lean").read_text()))


def derive(m: dict, claims: dict) -> tuple[str, list[str]]:
    """The level the evidence supports, and what is missing for `verified`.

    verified      a kernel-checked chain to a claim's `Sound` (or to a method it feeds),
                  with a Lean specification, correctness theorems and a conformance test
    specified     a Lean specification, and a stated reason it is not verified
    experimental  otherwise
    """
    lean = m.get("lean", {})
    if m.get("not_verified_because"):
        return ("specified" if lean.get("spec") else "experimental"), ["not_verified_because is set"]
    missing = []
    if m.get("mode") not in MODES:
        missing.append(f"mode in {sorted(MODES)}")
    for k in ("spec", "correctness"):
        if not lean.get(k):
            missing.append(f"lean.{k}")
    if not m.get("conformance"):
        missing.append("a conformance test")
    if not m.get("establishes") and not m.get("feeds"):
        missing.append("a claim it establishes or a method it feeds")
    for c in m.get("establishes", []):
        card = claims.get(c, (None, None))[1]
        if card is not None and not card.get("sound"):
            missing.append(f"a Sound theorem for claim '{c}'")
    return ("verified" if not missing else "experimental"), missing


def establishing(claim_id: str, methods: dict) -> list[str]:
    """The methods that establish a claim."""
    return [mid for mid, (_, m) in methods.items() if claim_id in m.get("establishes", [])]


def feeders(method_id: str, methods: dict) -> list[str]:
    """The methods that compute an input of a method."""
    return [mid for mid, (_, m) in methods.items() if method_id in m.get("feeds", [])]
