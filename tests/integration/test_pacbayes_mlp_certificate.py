"""Exact arithmetic regressions for the PAC-Bayes certificate generator."""
import importlib.util
from fractions import Fraction
from pathlib import Path
import math
import unittest

SCRIPT = Path(__file__).resolve().parents[2] / "methods/statistical/pacbayes_mlp_certificate.py"
spec = importlib.util.spec_from_file_location("pacbayes_certificate", SCRIPT)
certificate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(certificate)


def indexed_scores(model, x):
    """Independent index-based forward pass, as in the original decoder."""
    d, h, c = model["inputs"], model["hidden"], model["classes"]
    w = [v - 2 for v in model["codes"]]
    hid = [max(0, sum(w[i * d + j] * x[j] for j in range(d)) + model["hidden_bias_scale"] * w[d * h + i])
           for i in range(h)]
    st = d * h + h
    return [sum(w[st + k * h + i] * hid[i] for i in range(h)) + model["output_bias_scale"] * w[st + c * h + k]
            for k in range(c)]


class ForwardPassTests(unittest.TestCase):
    def model(self, codes):
        return dict(certificate.ARCH, levels=4, codes=codes)

    def test_list_pass_matches_indexed_pass(self):
        import random
        rng = random.Random(7)
        p = certificate.parameter_count(certificate.ARCH)
        for _ in range(50):
            model = self.model([rng.randrange(4) for _ in range(p)])
            x = [rng.randrange(17) for _ in range(64)]
            self.assertEqual(certificate.scores(model, x), indexed_scores(model, x))

    def test_ties_choose_first_class(self):
        self.assertEqual(certificate.argmax_first([3, 5, 5, 1]), 1)
        self.assertEqual(certificate.argmax_first([0, 0]), 0)
        self.assertEqual(certificate.argmax_first([]), 0)

    def test_architecture_is_fixed(self):
        p = certificate.parameter_count(certificate.ARCH)
        model = self.model([2] * p)
        model["hidden"] = 8
        with self.assertRaises(ValueError):
            certificate.validate(model)


class NumericsTests(unittest.TestCase):
    def test_rational_constants_bound_the_real_quantities(self):
        num = certificate.numerics(16, 397, 1210, Fraction(3, 4))
        c, t = float(num["c"]), float(num["t"])
        self.assertGreaterEqual(float(num["E"]), math.exp(c))
        self.assertLessEqual(float(num["L"]), math.exp(t))
        self.assertGreaterEqual(float(num["B"]), (1 - math.exp(-c)) / (1 - math.exp(-t)))

    def test_certificate_is_recomputed_from_predictions(self):
        # An all-zero network predicts class zero; stale metadata must not help.
        p = certificate.parameter_count(certificate.ARCH)
        artifact = dict(model=self_model([2] * p), heldout_rows=[[0] * 64 + [1]] * 397,
                        certificate=dict(heldout_errors=0))
        report = certificate.verify(artifact)
        self.assertEqual(report["heldout_errors"], 397)
        self.assertGreater(report["population_error_upper_bound_float"], 0.99)


def self_model(codes):
    return dict(certificate.ARCH, levels=4, codes=codes)


if __name__ == "__main__":
    unittest.main()
