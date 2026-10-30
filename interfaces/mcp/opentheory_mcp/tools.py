"""The six MCP tools, as plain functions returning JSON-ready dicts.

Bad input (an unknown target) raises ValueError; a proof that fails is a normal result with ok=False.
"""
from __future__ import annotations

import importlib.util
import re
import sys
import tempfile
import threading
from pathlib import Path

from . import ENV, LEAN_ROOTS, ROOT, blueprint, run
from .lean_source import (Decl, Index, SpliceError, top_level_assign, declarations, is_complete, mask,
                          splice_proof)


def _load_sdk():
    """interfaces/python/opentheory, loaded the way its own tests load it (nothing added to sys.path)."""
    if "opentheory" not in sys.modules:
        init = ROOT / "interfaces/python/opentheory/__init__.py"
        spec = importlib.util.spec_from_file_location("opentheory", init, submodule_search_locations=[str(init.parent)])
        sys.modules["opentheory"] = module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
    return sys.modules["opentheory"]


_load_sdk()
from opentheory_verifier.engine import ALLOWED_AXIOMS  # noqa: E402

PROOF_KINDS = ("theorem", "lemma")
INDEX = Index(LEAN_ROOTS)
DIAGNOSTIC = re.compile(r"^(?P<file>.+?):(?P<line>\d+):(?P<col>\d+): (?P<severity>error|warning|info)\b[^:]*: ",
                        re.MULTILINE)
AXIOMS = re.compile(r"'(?P<name>[^\n]+?)' (?:depends on axioms: \[(?P<list>[^\]]*)\]|does not depend on any axioms)")
_commit_lock = threading.Lock()


def _rel(path: Path) -> str:
    return path.relative_to(ROOT).as_posix()


# ---- targets ---------------------------------------------------------------------------------------

def _resolve(target: str) -> tuple[dict | None, list[Decl]]:
    """A blueprint label or a Lean name (full or a unique suffix) → (node, declarations)."""
    target = target.strip()
    nodes, decls = blueprint.nodes(), INDEX.all()
    if target in nodes:
        node = nodes[target]
        return node, [decls[n] for n in node["leanNames"] if n in decls]
    decl = decls.get(target)
    if decl is None:
        hits = [d for name, d in decls.items() if name.endswith("." + target)]
        if len(hits) > 1:
            raise ValueError(f"'{target}' is ambiguous: {', '.join(sorted(d.name for d in hits)[:10])}")
        if not hits:
            raise ValueError(f"no blueprint label or Lean declaration '{target}' (list_targets shows the labels)")
        decl = hits[0]
    node = next((n for n in nodes.values() if decl.name in n["leanNames"]), None)
    return node, [decl]


def _proof_target(target: str) -> tuple[dict | None, Decl]:
    node, decls = _resolve(target)
    candidates = [d for d in decls if d.kind in PROOF_KINDS]
    open_ = [d for d in candidates if not is_complete(d.source())]
    if len(candidates) == 1 or len(open_) == 1:
        return node, (open_ or candidates)[0]
    if not candidates:
        raise ValueError(f"'{target}' has no theorem or lemma in Lean to prove")
    raise ValueError(f"'{target}' has {len(candidates)} theorems; pass one Lean name: "
                     + ", ".join(d.name for d in candidates))


def _lean_entry(name: str, decls: dict[str, Decl], with_source: bool = False) -> dict:
    decl = decls.get(name)
    if decl is None:
        return {"name": name, "found": False}
    source = decl.source()
    entry = {"name": name, "found": True, "kind": decl.kind, "file": _rel(decl.path), "line": decl.line,
             "complete": is_complete(source)}
    if with_source:
        entry["source"] = source
    return entry


def _statement_of(decl: Decl) -> str:
    """A theorem's statement (its text up to `:=`); a definition in full, since its body is the meaning."""
    source = decl.source()
    if decl.kind in PROOF_KINDS and (assign := top_level_assign(mask(source))) is not None:
        return source[:assign].rstrip()
    return source if len(source) <= 4000 else source[:4000] + "\n-- … (truncated)"


def list_targets(include_verified: bool = False, kind: str | None = None, ready_only: bool = False,
                 min_bounty_usd: int | None = None) -> dict:
    nodes, decls = blueprint.nodes(), INDEX.all()
    counts = {"verified": 0, "statement_only": 0, "unformalized": 0}
    targets, inconsistencies = [], []
    for node in nodes.values():
        status = blueprint.status(node)
        counts[status] += 1
        lean = [_lean_entry(n, decls) for n in node["leanNames"]]
        missing = [e["name"] for e in lean if not e["found"]]
        open_ = [e["name"] for e in lean if e["found"] and not e["complete"]]
        if missing:
            inconsistencies.append({"id": node["id"], "problem": f"\\lean names not found in Lean: {missing}"})
        if status == "verified" and open_:
            inconsistencies.append({"id": node["id"], "problem": f"proof marked \\leanok but {open_} use sorry"})
        unmet = [d for d in node["dependencies"] if not nodes.get(d, {}).get("isVerified")]
        if (status == "verified" and not include_verified) or (kind and node["kind"] != kind) \
                or (ready_only and unmet) or (min_bounty_usd is not None and (node["bountyUsd"] or 0) < min_bounty_usd):
            continue
        targets.append({"id": node["id"], "kind": node["kind"], "title": node["title"], "status": status,
                        "lean": lean, "bounty_usd": node["bountyUsd"], "dependencies": node["dependencies"],
                        "unmet_dependencies": unmet})
    targets.sort(key=lambda t: (bool(t["unmet_dependencies"]), -(t["bounty_usd"] or 0), t["id"]))
    return {"counts": counts, "targets": targets, "inconsistencies": inconsistencies}


def get_target(target: str) -> dict:
    node, found = _resolve(target)
    decls = INDEX.all()
    result: dict = {"axiom_policy": {"allowed": sorted(ALLOWED_AXIOMS),
                                     "note": "check_proof rejects any other axiom, sorryAx included"}}
    if node is None:
        result["blueprint"] = None
        result["lean"] = [_lean_entry(d.name, decls, with_source=True) for d in found]
        return result
    nodes, statements = blueprint.nodes(), blueprint.statements()
    result.update({
        "id": node["id"], "kind": node["kind"], "title": node["title"], "status": blueprint.status(node),
        "bounty_usd": node["bountyUsd"], "statement": statements.get(node["id"]),
        "informal_proof": node["informalSketch"],
        "lean": [_lean_entry(n, decls, with_source=True) for n in node["leanNames"]],
        "dependencies": [],
    })
    for dep in node["dependencies"]:
        dn = nodes.get(dep)
        if dn is None:
            result["dependencies"].append({"id": dep, "problem": "not in the blueprint"})
            continue
        result["dependencies"].append({
            "id": dep, "kind": dn["kind"], "title": dn["title"], "status": blueprint.status(dn),
            "statement": statements.get(dep),
            "lean": [{"name": n, "statement": _statement_of(decls[n])} if n in decls else {"name": n, "found": False}
                     for n in dn["leanNames"]],
        })
    return result


# ---- the kernel ------------------------------------------------------------------------------------

def _diagnostics(output: str, path: str) -> list[dict]:
    found = []
    matches = list(DIAGNOSTIC.finditer(output))
    for i, m in enumerate(matches):
        end = matches[i + 1].start() if i + 1 < len(matches) else len(output)
        found.append({"severity": m["severity"], "line": int(m["line"]), "column": int(m["col"]),
                      "in_checked_file": m["file"] == path, "message": output[m.end():end].strip()})
    return found


def _kernel_check(text: str, decl: Decl, timeout: float) -> dict:
    """Compile `text` as a copy of decl's file with `lake env lean`, then `#print axioms` the target."""
    with tempfile.TemporaryDirectory(prefix="ot-mcp-") as tmp:
        path = Path(tmp) / decl.path.name
        # Full names, since the file may `open Classical` and print `choice`.
        path.write_text(f"{text.rstrip()}\n\nset_option pp.fullNames true in\n#print axioms {decl.name}\n",
                        encoding="utf-8")
        res = run(["lake", "env", "lean", str(path)], timeout)
    diags = _diagnostics(AXIOMS.sub("", res.output), str(path))
    errors = [d for d in diags if d["severity"] == "error"]
    reports = list(AXIOMS.finditer(res.output))
    axioms = None
    if reports:
        axioms = [a.strip() for a in (reports[-1]["list"] or "").replace("\n", " ").split(",") if a.strip()]
    disallowed = sorted(set(axioms or []) - ALLOWED_AXIOMS)
    result = {"ok": res.ok and not errors and axioms is not None and not disallowed,
              "target": decl.name, "file": _rel(decl.path), "seconds": round(res.seconds, 1),
              "axioms": axioms, "disallowed_axioms": disallowed, "errors": errors,
              "warnings": [d for d in diags if d["severity"] == "warning"][:20]}
    if not diags and not res.ok:
        result["output"] = res.tail()
    if "object file" in res.output and "does not exist" in res.output:
        result["hint"] = "the imports are not built: run `lake build` (or the audit_repository tool) first"
    if result["ok"]:
        result["summary"] = f"{decl.name} checked by the Lean kernel; axioms: {', '.join(axioms) or 'none'}"
    return result


def check_proof(target: str, proof: str | None = None, timeout_s: int = 900) -> dict:
    _, decl = _proof_target(target)
    text = decl.path.read_text(encoding="utf-8")
    if proof is not None:
        try:
            text = splice_proof(text, decl, proof)
        except SpliceError as e:
            return {"ok": False, "target": decl.name, "file": _rel(decl.path), "reason": str(e)}
    result = _kernel_check(text, decl, timeout_s)
    checked = next(d for d in declarations(decl.path, text) if d.name == decl.name)
    result["declaration"] = {"first_line": checked.line, "text": text[checked.start:checked.end]}
    return result


# ---- commits ---------------------------------------------------------------------------------------

def _git(*args: str, env: dict | None = None) -> str:
    res = run(["git", *args], 60, env=env)
    if not res.ok:
        raise RuntimeError(f"git {' '.join(args)}: {res.output}")
    return res.output


def commit_proof(target: str, proof: str, branch: str | None = None, message: str | None = None,
                 timeout_s: int = 900) -> dict:
    """Check the proof, then commit it (with the blueprint update) to a new branch off HEAD.

    The commit is built in a private index, so the checkout, its branch and any other
    uncommitted work are left exactly as they were.
    """
    with _commit_lock:
        node, decl = _proof_target(target)
        files = [decl.path] + ([blueprint.CONTENT, blueprint.exporter.DEFAULT_OUTPUT] if node else [])
        branch = branch or "proof/" + re.sub(r"[^A-Za-z0-9._-]+", "-", decl.name.removeprefix("OpenTheory."))
        refusal = _commit_refusal(files, branch)
        if refusal:
            return {"ok": False, "target": decl.name, "reason": refusal}

        try:
            text = splice_proof(decl.path.read_text(encoding="utf-8"), decl, proof)
        except SpliceError as e:
            return {"ok": False, "target": decl.name, "reason": str(e)}
        checked = _kernel_check(text, decl, timeout_s)
        if not checked["ok"]:
            return {**checked, "reason": "the proof did not check; nothing was committed"}

        originals = {p: p.read_bytes() for p in files}
        notes: list[str] = []
        try:
            decl.path.write_text(text, encoding="utf-8")
            marked = node is not None and _mark_blueprint(node, notes)
            changed = [p for p in files if p.read_bytes() != originals[p]]
            subject = message or f"proof: {decl.name}"
            body = (f"Kernel-checked with `lake env lean` and `#print axioms`: {', '.join(checked['axioms']) or 'none'}."
                    + (f"\nBlueprint: \\leanok on {node['id']}." if marked else ""))
            commit = _commit(changed, branch, f"{subject}\n\n{body}\n")
        finally:
            for path, data in originals.items():
                path.write_bytes(data)
        return {"ok": True, "target": decl.name, "branch": branch, "commit": commit,
                "files": [_rel(p) for p in changed], "axioms": checked["axioms"], "blueprint_marked": marked,
                "diffstat": _git("diff", "--stat", "HEAD", commit), "notes": notes,
                "next": f"`git switch {branch}` to see it, or push it and open a pull request; "
                        "CI reruns lake build and the axiom audit over the whole library"}


def _commit_refusal(files: list[Path], branch: str) -> str | None:
    if not run(["git", "rev-parse", "--verify", "--quiet", "HEAD"], 30).ok:
        return "not a git checkout with a HEAD commit"
    if not run(["git", "check-ref-format", "--branch", branch], 30).ok:
        return f"invalid branch name '{branch}'"
    if run(["git", "rev-parse", "--verify", "--quiet", f"refs/heads/{branch}"], 30).ok:
        return f"branch '{branch}' already exists; pass another branch name"
    for path in files:
        rel = _rel(path)
        if not run(["git", "ls-files", "--error-unmatch", "--", rel], 30).ok:
            return f"{rel} is not tracked by git; commit it first"
        if run(["git", "status", "--porcelain", "--", rel], 30).output:
            return f"{rel} has uncommitted changes; commit or stash them so the proof commit holds only the proof"
    return None


def _mark_blueprint(node: dict, notes: list[str]) -> bool:
    """\\leanok the node, only if every Lean declaration it names is now free of sorry."""
    decls = INDEX.all()
    missing = [n for n in node["leanNames"] if n not in decls]
    open_ = [n for n in node["leanNames"] if n in decls and not is_complete(decls[n].source())]
    if missing or open_:
        notes.append(f"blueprint left unchanged: {node['id']} still has open or missing declarations "
                     f"{open_ + missing}")
        return False
    tex, more = blueprint.mark_proved(blueprint.CONTENT.read_text(encoding="utf-8"), node["id"])
    notes.extend(more)
    blueprint.CONTENT.write_text(tex, encoding="utf-8")
    blueprint.regenerate()
    return blueprint.nodes()[node["id"]]["isVerified"]


def _commit(changed: list[Path], branch: str, message: str) -> str:
    with tempfile.TemporaryDirectory(prefix="ot-mcp-git-") as tmp:
        env = {**ENV, "GIT_INDEX_FILE": str(Path(tmp) / "index")}
        _git("read-tree", "HEAD", env=env)
        _git("update-index", "--", *(_rel(p) for p in changed), env=env)
        tree = _git("write-tree", env=env)
    commit = _git("commit-tree", tree, "-p", "HEAD", "-m", message)
    _git("update-ref", f"refs/heads/{branch}", commit, "")
    return commit


# ---- whole-repository checks -----------------------------------------------------------------------

def audit_repository(build: bool = True, timeout_s: int = 3600) -> dict:
    py = sys.executable
    steps = [
        ("blueprint \\lean names exist", [py, "tests/regression/check_lean_decls.py"]),
        ("method catalog", [py, "tests/regression/check_catalog.py"]),
        ("blueprint.json is current", [py, "blueprint/export_blueprint.py", "--check"]),
    ]
    if build:
        steps.append(("lake build", ["lake", "build"]))
    steps.append(("axiom audit", ["lake", "env", "lean", "--run", "verifier/backends/formal/audit_axioms.lean"]))
    results = []
    for name, cmd in steps:
        res = run(cmd, timeout_s)
        results.append({"step": name, "ok": res.ok, "seconds": round(res.seconds, 1), "output": res.tail()})
    return {"ok": all(r["ok"] for r in results), "steps": results}


def verify_certificate(bundle: str, timeout_s: int = 1800) -> dict:
    path = Path(bundle).expanduser()
    return _load_sdk().verify(path if path.is_absolute() else ROOT / path, timeout=timeout_s).to_dict()
