"""Exact arithmetic regressions for the classifier that receives the certificate."""
import importlib.util
from pathlib import Path
import unittest

SCRIPT = Path(__file__).resolve().parents[2] / "methods/statistical/quantized_mlp_certificate.py"
spec = importlib.util.spec_from_file_location("certificate", SCRIPT)
certificate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(certificate)


class ExactClassifierTests(unittest.TestCase):
    def setUp(self):
        # Two ReLU units detect positive and negative inputs, respectively.
        self.model = dict(inputs=1, hidden=2, classes=2, levels=4,
                          codes=[3, 1, 2, 2, 3, 2, 2, 3, 2, 2])

    def test_nonlinear_forward_and_tie_rule(self):
        self.assertEqual(certificate.predict(self.model, [64]), 0)
        self.assertEqual(certificate.predict(self.model, [-64]), 1)
        self.assertEqual(certificate.predict(self.model, [0]), 0)

    def test_output_bias_uses_hidden_scale(self):
        self.model["codes"][-1] = 3
        self.assertEqual(certificate.predict(self.model, [64]), 1)
        self.assertEqual(certificate.predict(self.model, [256]), 0)

    def test_all_weights_and_biases_are_charged(self):
        self.assertEqual(certificate.parameter_count(self.model), 10)
        self.assertEqual(certificate.description_bits(self.model), 20)

    def test_invalid_code_is_rejected(self):
        self.model["codes"][0] = 4
        with self.assertRaises(ValueError):
            certificate.predict(self.model, [64])

    def test_wrong_length_is_rejected(self):
        self.model["codes"].pop()
        with self.assertRaises(ValueError):
            certificate.predict(self.model, [64])

    def test_saved_certificate_is_recomputed_from_actual_predictions(self):
        # An all-zero model predicts class zero. Stale metadata must not turn
        # 1400 wrong labels into a spurious non-vacuous certificate.
        model = dict(inputs=16, hidden=4, classes=10, levels=4, codes=[2]*118)
        artifact = dict(model=model, training_rows=[[0]*16+[1]]*1400,
                        heldout_rows=[[0]*16+[0]], certificate=dict(training_errors=0))
        report = certificate.verify(artifact)
        self.assertEqual(report["training_errors"], 1400)
        self.assertEqual(report["population_error_upper_bound"], 1.25)


if __name__ == "__main__":
    unittest.main()
