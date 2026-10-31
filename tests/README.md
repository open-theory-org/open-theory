# tests/

| Folder | What | Run |
| --- | --- | --- |
| [conformance/](conformance/) | Honest certificates accepted, forgeries rejected | `tests/conformance/certified_accuracy.sh` (~2 min) |
| [conformance/](conformance/) | `pool-rate`: honest variants from recorded fixtures accepted, forgeries rejected, compiled and kernel modes | `python tests/conformance/pool_rate_verify.py` (needs `py_arkworks_bls12381` or `py_ecc`; ~10 s) |
| [conformance/](conformance/) | `judged-rate`: the same for a judge plus gold audit | `python tests/conformance/judged_rate_verify.py` (~20 s) |
| [conformance/](conformance/) | `pool` / `pool-witness` checks: kernel and compiled lanes agree with each other and with a Python reading | `python3 tests/conformance/pool_check_lanes.py` (~5 s) |
| [integration/](integration/) | Certificate generators end to end | `python3 -m unittest discover -s tests/integration` |
| [adversarial/](adversarial/) | Attacks on the verifier | see its README |
| [regression/](regression/) | Honesty gates: blueprint names, axiom audit, catalog levels, Lean smoke tests | see below |

```bash
python3 tests/regression/check_lean_decls.py
python3 tests/regression/check_catalog.py
lake env lean --run verifier/backends/formal/audit_axioms.lean
python3 -m unittest discover -s tests/regression
for f in tests/regression/lean/*.lean; do lake env lean "$f"; done
```
