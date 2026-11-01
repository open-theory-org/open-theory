#!/usr/bin/env python3
"""Each claim card says what its claim types say.

A claim card (specs/claims/) names its claim types: terms of `OpenTheory.ClaimType` in
`formal/core/Specs/ClaimTypes.lean`, each a specification with parameters and its `Sound` theorem.
This script reads every term's elaborated definition (tests/regression/spec_shapes.lean) and fails
when the card differs:

  property    the named property the observable applies is one of the property card's `lean`
              names, and its kind (property | quantity) is the card's `kind`
  domain      the domain card's `kind`, or `pair(k1,k2)` for two cards, is the `Domain` constructor
  aggregate   the card's aggregate is the `Aggregate` constructor
  model       the `M` of `ClaimType M X` is the `type` of one of the card's model cards, or a
              variable (the claim type holds for every model)
  location    the term lives in `OpenTheory.ClaimTypes`

Needs a built workspace (`lake build`); about a minute, most of it importing the environment.

    python3 tests/regression/check_spec_shapes.py
"""
from __future__ import annotations

import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from registry import ROOT, cards  # noqa: E402

PREFIX = "OpenTheory.ClaimTypes."


def main() -> int:
    claims = {k: c for k, (_, c) in cards("claims").items() if c}
    props = {k: c for k, (_, c) in cards("properties").items() if c}
    doms = {k: c for k, (_, c) in cards("domains").items() if c}
    models = {k: c for k, (_, c) in cards("models").items() if c}
    names = sorted({s for c in claims.values() for s in c.get("claim_types", [])})
    out = subprocess.run(["lake", "env", "lean", "--run", "tests/regression/spec_shapes.lean", *names],
                         cwd=ROOT, capture_output=True, text=True)
    shapes = {}
    for line in out.stdout.splitlines():
        name, *rest = line.split("|")
        shapes[name] = rest
    errors = []
    if not out.stdout:
        errors.append(f"spec_shapes.lean failed: {out.stderr.strip()[:500]}")
    sounds = []
    for cid, c in sorted(claims.items()):
        where = f"specs/claims/{cid}.md"
        prop = props.get(c["observable"], {})
        dom = c["domain"]
        want_dom = (f"pair({','.join(doms[d]['kind'] for d in dom)})" if isinstance(dom, list)
                    else doms.get(dom, {}).get("kind"))
        types = {models[m]["type"] for m in c.get("models", []) if m in models}
        for name in c.get("claim_types", []):
            got = shapes.get(name)
            if not name.startswith(PREFIX):
                errors.append(f"{where}: claim type {name} must live in {PREFIX[:-1]} (Specs/ClaimTypes.lean)")
            if not got or len(got) != 6:
                errors.append(f"{where}: {name}: {(got or ['no output'])[0]}")
                continue
            model, kind, named, d, agg, sound = got
            if kind != prop.get("kind"):
                errors.append(f"{where}: observable kind is {prop.get('kind')!r} on the card but {kind!r} in {name}")
            if named not in prop.get("lean", []):
                errors.append(f"{where}: {name} applies {named}, which is not a `lean` name of property card "
                              f"{c['observable']!r} ({prop.get('lean')})")
            if d != want_dom:
                errors.append(f"{where}: domain is {want_dom!r} on the card but {d!r} in {name}")
            if agg != c["aggregate"]:
                errors.append(f"{where}: aggregate is {c['aggregate']!r} on the card but {agg!r} in {name}")
            if model != "*" and model not in types:
                errors.append(f"{where}: {name} is about {model}, which is the type of none of {c.get('models')}")
            sounds.append(sound)
    for e in errors:
        print(f"[FAIL] {e}")
    if errors:
        return 1
    print(f"[OK] {len(names)} claim types state the property, domain, aggregate and model their "
          f"{len(claims)} claim cards say; guarantees: {', '.join(s.rsplit('.', 1)[-1] for s in sounds)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
