#!/usr/bin/env python3
"""Each claim card says what its `Sound` theorems say.

A claim card (specs/claims/) states an observable, a domain, an aggregate and the models; its
`sound` theorems state a `Spec` (formal/core/Specs/). This script reads the `Spec` out of each
elaborated theorem (tests/regression/spec_shapes.lean) and fails when they differ:

  observable  the property card's `kind` (property | quantity) is the `Observable` constructor
  domain      the domain card's `kind`, or `pair(k1,k2)` for two cards, is the `Domain` constructor
  aggregate   the card's aggregate is the `Aggregate` constructor
  model       the `M` of `Spec M X` is the `type` of one of the card's model cards, or a variable
              (the theorem holds for every model)

Needs a built workspace (`lake build`); about a minute, most of it importing the environment.

    python3 tests/regression/check_spec_shapes.py
"""
from __future__ import annotations

import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from registry import ROOT, cards  # noqa: E402


def main() -> int:
    claims = {k: c for k, (_, c) in cards("claims").items() if c}
    props = {k: c for k, (_, c) in cards("properties").items() if c}
    doms = {k: c for k, (_, c) in cards("domains").items() if c}
    models = {k: c for k, (_, c) in cards("models").items() if c}
    names = sorted({s for c in claims.values() for s in c.get("sound", [])})
    out = subprocess.run(["lake", "env", "lean", "--run", "tests/regression/spec_shapes.lean", *names],
                         cwd=ROOT, capture_output=True, text=True)
    shapes: dict[str, list[list[str]]] = {}
    for line in out.stdout.splitlines():
        name, *rest = line.split("|")
        shapes.setdefault(name, []).append(rest)
    errors = []
    for cid, c in sorted(claims.items()):
        where = f"specs/claims/{cid}.md"
        dom = c["domain"]
        want_dom = (f"pair({','.join(doms[d]['kind'] for d in dom)})" if isinstance(dom, list)
                    else doms.get(dom, {}).get("kind"))
        want = {"observable": props.get(c["observable"], {}).get("kind"), "domain": want_dom,
                "aggregate": c["aggregate"]}
        types = {models[m]["type"] for m in c.get("models", []) if m in models}
        for s in c.get("sound", []):
            got = shapes.get(s)
            if not got or got[0] in (["missing"], ["none"]):
                errors.append(f"{where}: {s} states no Spec ({(got or [['no output']])[0][0]})")
                continue
            for model, obs, d, agg in got:
                for field, value in (("observable", obs), ("domain", d), ("aggregate", agg)):
                    if value != want[field]:
                        errors.append(f"{where}: {field} is {want[field]!r} on the card but {value!r} in {s}")
                if model != "*" and model not in types:
                    errors.append(f"{where}: {s} is about {model}, which is the type of none of {c.get('models')}")
    if out.returncode not in (0, 1) or not out.stdout:
        errors.append(f"spec_shapes.lean failed: {out.stderr.strip()[:500]}")
    for e in errors:
        print(f"[FAIL] {e}")
    if errors:
        return 1
    print(f"[OK] {len(names)} Sound theorems state the Spec their {len(claims)} claim cards say")
    return 0


if __name__ == "__main__":
    sys.exit(main())
