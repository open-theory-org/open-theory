"""OpenTheory certificate verifier, v0.1 (standard library only; `pool-rate` also needs `py_ecc`
and `openssl` for its beacon and timestamp checks, see verifier/attestations/).

A certificate bundle is a directory holding `certificate.json` and the files it names
(model, data). Verification follows specs/protocols/verification.md:

  1. pins       the Lean toolchain matches this checkout
  2. template   the claim type is known; its Lean statement is written here, not taken from the bundle
  3. bindings   every file digest matches
  4. kernel     the generated Lean file is checked by the Lean kernel
  5. axioms     `#print axioms` shows only propext, Classical.choice, Quot.sound
  6. report     claim, level (from catalog/), assumptions (from specs/), trusted base, scope

The bundle contributes data only (integers), never Lean source. A bug here can make the
verifier reject a true claim; the Lean statement it writes is fixed by the claim template,
so it cannot make the kernel accept a false one, except through the generator listed as
trusted in the report.
"""
from __future__ import annotations

import hashlib
import json
import os
import re
import subprocess
import tempfile
import time
import tomllib
from dataclasses import dataclass, field
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
FORMAT = "opentheory-certificate/0.1"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


class Reject(Exception):
    """The certificate is invalid. The message says why."""


@dataclass
class Report:
    accepted: bool
    claim: str = ""
    claim_type: str = ""
    level: str = ""
    guarantee: str = ""
    assumptions: list[tuple[str, str]] = field(default_factory=list)
    checked: list[str] = field(default_factory=list)
    trusted: list[str] = field(default_factory=list)
    does_not_cover: list[str] = field(default_factory=list)
    warnings: list[str] = field(default_factory=list)
    reason: str = ""
    seconds: float = 0.0

    def to_dict(self):
        d = dict(self.__dict__)
        d["assumptions"] = [{"id": i, "statement": s} for i, s in self.assumptions]
        return d


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def assumption_texts() -> dict[str, str]:
    text = (ROOT / "specs/assumptions/README.md").read_text(encoding="utf-8")
    return {m.group(1): m.group(2).strip() for m in re.finditer(r"^## (A\d+-[\w-]+): (.+)$", text, re.M)}


def guarantee(gid: str) -> dict:
    path = ROOT / "catalog/guarantees" / f"{gid}.toml"
    if not path.exists():
        raise Reject(f"unknown guarantee '{gid}'")
    return tomllib.loads(path.read_text(encoding="utf-8"))


def require(obj, key, kind, where):
    if key not in obj:
        raise Reject(f"{where}: missing '{key}'")
    v = obj[key]
    if kind is int and (type(v) is not int):
        raise Reject(f"{where}.{key}: must be an integer")
    if kind is not int and not isinstance(v, kind):
        raise Reject(f"{where}.{key}: must be {kind.__name__}")
    return v


def load_file(bundle: Path, ref: dict, where: str):
    rel = require(ref, "path", str, where)
    digest = require(ref, "sha256", str, where)
    path = (bundle / rel).resolve()
    if bundle.resolve() not in path.parents:
        raise Reject(f"{where}.path escapes the bundle: {rel}")
    if not path.is_file():
        raise Reject(f"{where}.path not found: {rel}")
    actual = sha256(path)
    if actual != digest:
        raise Reject(f"{where}: sha256 mismatch for {rel} (certificate {digest[:12]}…, file {actual[:12]}…)")
    try:
        obj = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as e:
        raise Reject(f"{where}: {rel} is not valid JSON: {e}")
    if not isinstance(obj, dict):
        raise Reject(f"{where}: {rel} must be a JSON object")
    return obj, actual


def lean_command() -> tuple[list[str], dict]:
    """`lean` with the workspace's LEAN_PATH, without starting `lake` (which costs ~3 s)."""
    toolchain = (ROOT / "lean-toolchain").read_text().strip()
    lean = Path.home() / ".elan" / "toolchains" / toolchain.replace("/", "--").replace(":", "---") / "bin" / "lean"
    if not lean.exists():
        return ["lake", "env", "lean"], {}
    paths = [ROOT / ".lake/build/lib/lean", *sorted((ROOT / ".lake/packages").glob("*/.lake/build/lib/lean"))]
    return [str(lean)], {"LEAN_PATH": ":".join(str(p) for p in paths)}


def run_lean(source: str, timeout: int) -> tuple[bool, str]:
    cmd, env = lean_command()
    with tempfile.TemporaryDirectory(prefix="ot-verify-") as tmp:
        path = Path(tmp) / "Check.lean"
        path.write_text(source, encoding="utf-8")
        try:
            res = subprocess.run([*cmd, str(path)], cwd=ROOT, env={**os.environ, **env},
                                 capture_output=True, text=True, timeout=timeout)
        except subprocess.TimeoutExpired:
            raise Reject(f"Lean kernel did not finish within {timeout}s")
        except FileNotFoundError:
            raise RuntimeError("`lake` not found: install elan and run `lake build` in the OpenTheory checkout")
    out = res.stdout + res.stderr
    return res.returncode == 0 and ": error" not in out, out


OT_CHECK = ROOT / ".lake/build/bin/ot_check"


def run_fast(args: list, timeout: int) -> bool:
    """Run a decision procedure as compiled Lean (`lake build ot_check`)."""
    if not OT_CHECK.exists():
        raise RuntimeError("the compiled checker is missing: run `lake build ot_check`")
    try:
        res = subprocess.run([str(OT_CHECK), *map(str, args)], capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        raise Reject(f"the compiled checker did not finish within {timeout}s")
    if res.returncode != 0 or res.stdout.strip() not in ("true", "false"):
        raise RuntimeError(f"ot_check failed: {res.stderr.strip()[:200]}")
    return res.stdout.strip() == "true"


def check_axioms(output: str, theorem: str) -> list[str]:
    m = re.search(rf"'{re.escape(theorem)}' depends on axioms: \[([^\]]*)\]", output)
    if not m:
        if f"'{theorem}' does not depend on any axioms" in output:
            return []
        raise Reject("axiom report missing from Lean output")
    axioms = [a.strip() for a in m.group(1).replace("\n", " ").split(",") if a.strip()]
    bad = sorted(set(axioms) - ALLOWED_AXIOMS)
    if bad:
        raise Reject(f"disallowed axioms: {', '.join(bad)}")
    return axioms


def verify(bundle: str | Path, timeout: int = 1800, compiled: bool = False) -> Report:
    """Verify a certificate bundle (directory with certificate.json, or the JSON file itself).

    Claim types with a decision procedure have the Lean kernel evaluate it (level from the catalog).
    `compiled=True` runs the compiled code instead: faster, but it trusts the Lean compiler, so the
    report is labelled separately and is never `verified` (specs/protocols/assurance-levels.md)."""
    from .heldout_error import HANDLERS as HELDOUT  # claim-type handlers
    from .pool_rate import HANDLERS as POOL
    HANDLERS = {**HELDOUT, **POOL}

    t0 = time.time()
    bundle = Path(bundle)
    if bundle.is_file():
        bundle = bundle.parent
    report = Report(accepted=False)
    try:
        cert_path = bundle / "certificate.json"
        if not cert_path.is_file():
            raise Reject(f"no certificate.json in {bundle}")
        try:
            cert = json.loads(cert_path.read_text(encoding="utf-8"))
        except json.JSONDecodeError as e:
            raise Reject(f"certificate.json is not valid JSON: {e}")
        if not isinstance(cert, dict):
            raise Reject("certificate.json must be a JSON object")
        if cert.get("format") != FORMAT:
            raise Reject(f"format must be '{FORMAT}'")
        claim = require(cert, "claim", dict, "certificate")
        ctype = require(claim, "type", str, "claim")
        report.claim_type = ctype

        # 1. pins
        pins = require(cert, "pins", dict, "certificate")
        toolchain = (ROOT / "lean-toolchain").read_text().strip()
        if require(pins, "lean_toolchain", str, "pins") != toolchain:
            raise Reject(f"pinned toolchain {pins['lean_toolchain']} differs from this verifier's {toolchain}")
        head = subprocess.run(["git", "rev-parse", "HEAD"], cwd=ROOT, capture_output=True, text=True).stdout.strip()
        commit = pins.get("opentheory_commit", "")
        if commit != head:
            report.warnings.append(f"certificate pins OpenTheory {commit[:12] or '(none)'}; verifying with {head[:12]}. "
                                   "Exact commit pinning is enforced from the first tagged release.")

        # 2. template
        handler = HANDLERS.get(ctype)
        if handler is None:
            raise Reject(f"unknown claim type '{ctype}' (known: {', '.join(sorted(HANDLERS))})")

        # 3. bindings (+ claim-specific parsing)
        task = handler(bundle, cert, load_file)
        g = guarantee(task.guarantee)
        texts = assumption_texts()
        declared = cert.get("assumptions", [])
        missing = [a for a in g["assumptions"] if a not in declared]
        if missing:
            raise Reject(f"certificate omits assumptions required by '{task.guarantee}': {', '.join(missing)}")
        report.claim, report.guarantee, report.level = task.words, task.guarantee, g["level"]
        report.assumptions = [(a, texts.get(a, "(unknown assumption)")) for a in g["assumptions"]]
        report.does_not_cover = task.does_not_cover
        report.trusted = [f"Lean kernel ({toolchain})", *task.trusted]

        # 4–5. decision procedure (compiled) or kernel, and axioms
        if task.fast is not None and compiled:
            if not run_fast(task.fast, timeout):
                raise Reject("the decision procedure returned false: " + task.fast_explain())
            report.checked = task.checked + [
                f"{task.fast_call} = true (compiled Lean decision procedure, ot_check)",
                task.fast_meaning]
            report.level = ("compiled check, not verified: trusts the Lean compiler "
                            "(run `ot verify` without --compiled for the kernel check)")
            report.trusted = [f"Lean compiler and runtime ({toolchain}), which run the decision procedure",
                              f"Lean kernel ({toolchain}), which checked the library theorems at build time",
                              *task.trusted]
        else:
            ok, out = run_lean(task.lean, timeout)
            if not ok:
                raise Reject("the Lean kernel refused the certificate: " + task.explain(out))
            axioms = check_axioms(out, task.theorem)
            report.checked = task.checked + (
                [f"{task.fast_call} = true (Lean kernel)", task.fast_meaning] if task.fast is not None else []
            ) + [f"axioms of {task.theorem}: {', '.join(axioms) or 'none'} (Lean)"]
        report.accepted = True
    except Reject as e:
        report.reason = str(e)
    report.seconds = round(time.time() - t0, 1)
    return report
