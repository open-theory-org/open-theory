"""OpenTheory Python SDK: `verify(bundle)` returns a Report (see verifier/core/engine.py).

The verifier is loaded from verifier/core as the package `opentheory_verifier`. Nothing is added
to `sys.path`: in particular the untrusted producers in methods/ are never importable from here.
"""
import importlib.util
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
_CORE = ROOT / "verifier" / "core"


def _load_verifier():
    name = "opentheory_verifier"
    if name in sys.modules:
        return sys.modules[name]
    spec = importlib.util.spec_from_file_location(name, _CORE / "__init__.py",
                                                  submodule_search_locations=[str(_CORE)])
    pkg = importlib.util.module_from_spec(spec)
    sys.modules[name] = pkg
    spec.loader.exec_module(pkg)
    return pkg


_load_verifier()
from opentheory_verifier.engine import Report, verify  # noqa: E402

__all__ = ["verify", "Report", "ROOT"]
