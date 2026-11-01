"""The catalog's levels are derived from its links (tests/regression/registry.py): breaking a link
must lower the level, so a method can never stay verified on a missing proof or test."""
import copy
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from registry import cards, catalog, derive  # noqa: E402


class DerivedLevels(unittest.TestCase):
    def setUp(self):
        self.claims = {k: v for k, v in cards("claims").items() if v[1]}
        self.methods = {k: m for k, (_, m) in catalog("methods").items()}

    def level(self, mid, method=None, claims=None):
        m, c = copy.deepcopy(self.methods[mid]), copy.deepcopy(self.claims)
        if method:
            method(m)
        if claims:
            claims(c)
        return derive(m, c)[0]

    def test_declared_equals_derived(self):
        for mid, m in self.methods.items():
            self.assertEqual(m["level"], derive(m, self.claims)[0], mid)

    def test_claim_without_sound_is_not_verified(self):
        self.assertEqual(self.level("heldout-binomial-bound",
                                    claims=lambda c: c["heldout-error"][1].update(sound=[])), "experimental")

    def test_missing_conformance_correctness_or_link(self):
        for mutate in (lambda m: m.update(conformance=[]), lambda m: m["lean"].update(correctness=[]),
                       lambda m: m.pop("establishes"), lambda m: m.pop("mode")):
            self.assertEqual(self.level("pool-rate-certificate", method=mutate), "experimental")

    def test_stated_reason_caps_at_specified(self):
        self.assertEqual(self.level("pool-rate-certificate",
                                    method=lambda m: m.update(not_verified_because="floating point")), "specified")


if __name__ == "__main__":
    unittest.main()
