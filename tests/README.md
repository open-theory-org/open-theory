# tests/

| Folder | What | Run |
| --- | --- | --- |
| [conformance/](conformance/) | Honest certificates accepted, forgeries rejected | `tests/conformance/certified_accuracy.sh` (~2 min) |
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
