# core: the verify engine

- [`engine.py`](engine.py) runs protocol steps 1–6 ([verification.md](../../specs/protocols/verification.md)) and returns a `Report`.
- [`heldout_error.py`](heldout_error.py) is the `heldout-error` v0.1 handler. It writes the Lean statement from the template and the hashed data.
- Uses only the Python standard library, plus `lake` from the OpenTheory checkout.
- Entry points: `interfaces/cli/ot verify <bundle>` and `opentheory.verify(bundle)`.

**Trusted:** the Lean kernel, the template statement, and the JSON → Lean data translation in `heldout_error.py`. The batch error counts computed here are not trusted, because the kernel rechecks them.
