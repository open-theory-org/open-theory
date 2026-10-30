"""`ot` keeps untrusted code off the verifier's import path and never reports a crash as a verdict."""
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
OT = ROOT / "interfaces/cli/ot"


def ot(*args):
    return subprocess.run([sys.executable, str(OT), *args], capture_output=True, text=True)


class VerifierIsolation(unittest.TestCase):
    def test_sdk_does_not_put_producers_on_path(self):
        code = ("import sys; sys.path.insert(0, %r); import opentheory; "
                "print(any('methods' in p or 'verifier' in p for p in sys.path), 'engine' in sys.modules)"
                % str(ROOT / "interfaces/python"))
        out = subprocess.run([sys.executable, "-c", code], capture_output=True, text=True, check=True).stdout
        self.assertEqual(out.split(), ["False", "False"])


class ExitCodes(unittest.TestCase):
    def test_missing_bundle_is_a_rejection(self):
        self.assertEqual(ot("verify", "/nonexistent").returncode, 1)

    def test_non_object_certificate_is_a_rejection(self):
        with tempfile.TemporaryDirectory() as d:
            (Path(d) / "certificate.json").write_text(json.dumps([1, 2]))
            r = ot("verify", d, "--json")
            self.assertEqual(r.returncode, 1)
            self.assertIn("JSON object", json.loads(r.stdout)["reason"])

    def test_usage_error_is_not_a_verdict(self):
        self.assertEqual(ot("verify").returncode, 2)


if __name__ == "__main__":
    unittest.main()
