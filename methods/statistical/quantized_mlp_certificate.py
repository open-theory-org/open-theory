#!/usr/bin/env python3
"""Train and audit a fixed 16–4–10, two-bit ReLU MLP on sklearn digits.

The certificate concerns this deterministic quantized network. Training may
select any of its 4**118 codes; no held-out observations are used for selection.
Verification of a saved artifact needs only the Python standard library.
"""
import argparse
import hashlib
import json
import math
from fractions import Fraction
from pathlib import Path


def parameter_count(model):
    d, h, c = (model[k] for k in ("inputs", "hidden", "classes"))
    return d * h + h + h * c + c


def description_bits(model):
    return parameter_count(model) * math.log2(model["levels"])


def validate(model):
    if model["levels"] != 4:
        raise ValueError("The decoder has exactly four levels: -2, -1, 0, 1")
    if any(type(model[k]) is not int or model[k] <= 0
           for k in ("inputs", "hidden", "classes")):
        raise ValueError("Dimensions must be positive integers")
    if len(model["codes"]) != parameter_count(model):
        raise ValueError("All weights and biases must be present")
    if any(type(v) is not int or not 0 <= v < 4 for v in model["codes"]):
        raise ValueError("Codes must be integers in [0, 4)")


def predict(model, x):
    """Integer-only forward pass; ties go to the smallest class index."""
    validate(model)
    d, h, c = (model[k] for k in ("inputs", "hidden", "classes"))
    if len(x) != d or any(type(v) is not int for v in x):
        raise ValueError("Inputs must be an integer vector of the declared size")
    w = [v - 2 for v in model["codes"]]
    hidden = [max(0, sum(w[i*d+j] * x[j] for j in range(d))
                  + 64 * w[d*h+i]) for i in range(h)]
    start = d*h+h
    scores = [sum(w[start+k*h+i] * hidden[i] for i in range(h))
              + 128 * w[start+c*h+k] for k in range(c)]
    return max(range(c), key=scores.__getitem__)


def error_count(model, rows):
    return sum(predict(model, row[:-1]) != row[-1] for row in rows)


def verify(artifact):
    model = artifact["model"]
    validate(model)
    if (model["inputs"], model["hidden"], model["classes"]) != (16, 4, 10):
        raise ValueError("This certificate fixes the architecture before training")
    rows = artifact["training_rows"]
    if len(rows) != 1400:
        raise ValueError("The numerical Lean certificate uses exactly 1400 samples")
    for row in rows + artifact["heldout_rows"]:
        if len(row) != 17 or any(type(v) is not int or not 0 <= v <= 64 for v in row[:-1]):
            raise ValueError("Invalid pooled digit")
        if type(row[-1]) is not int or not 0 <= row[-1] < 10:
            raise ValueError("Invalid class label")
    errors = error_count(model, rows)
    heldout_errors = error_count(model, artifact["heldout_rows"])
    epsilon = 0.25
    log_failure = math.log(2) + description_bits(model)*math.log(2) - 2*1400*epsilon**2
    return dict(parameters=parameter_count(model), bits=description_bits(model),
                n=1400, training_errors=errors, training_error=errors/1400,
                heldout_n=len(artifact["heldout_rows"]), heldout_errors=heldout_errors,
                heldout_error=heldout_errors/len(artifact["heldout_rows"]),
                gap=epsilon, population_error_upper_bound=errors/1400+epsilon,
                failure_probability_upper_bound=math.exp(log_failure),
                confidence_at_least=0.95,
                assumptions="IID labeled examples from one distribution; fixed decoder")


def refine(artifact):
    """Coordinate search within the same codebook, using only training rows."""
    import numpy as np
    x = np.asarray([r[:-1] for r in artifact["training_rows"]], dtype=np.int64)
    y = np.asarray([r[-1] for r in artifact["training_rows"]], dtype=np.int64)
    weights = np.asarray(artifact["model"]["codes"], dtype=np.int64)-2

    def evaluate(w):
        hidden = np.maximum(0, x @ w[:64].reshape(4, 16).T + 64*w[64:68])
        scores = hidden @ w[68:108].reshape(10, 4).T + 128*w[108:118]
        errors = int(np.sum(scores.argmax(1) != y))
        z = scores / 128 * 3
        z -= z.max(axis=1, keepdims=True)
        ce = float(np.mean(np.log(np.exp(z).sum(1))-z[np.arange(len(y)), y]))
        return errors, ce

    rng = np.random.default_rng(54)
    best = evaluate(weights)
    for epoch in range(30):
        previous = best
        for i in rng.permutation(len(weights)):
            choice = int(weights[i])
            for value in range(-2, 2):
                weights[i] = value
                score = evaluate(weights)
                if score < best:
                    best, choice = score, value
            weights[i] = choice
        if best == previous:
            break
    artifact["model"]["codes"] = (weights+2).tolist()
    artifact["provenance"]["refinement"] = dict(
        method="coordinate search, training errors then cross entropy", seed=54, passes=epoch+1)
    artifact["certificate"] = verify(artifact)
    return artifact


def export_lean(artifact, output):
    """Emit exact observations and proofs; Lean must check every error count."""
    report = verify(artifact)
    errors = report["training_errors"]
    rate = Fraction(errors, 1400)
    parts = ["import Specs.QuantizedMLP.Occam\n\n"
             "/-! Exact saved weights, observations, and kernel-checked error count.\n"
             "Generated by methods/statistical/quantized_mlp_certificate.py export. Error counts are checked\n"
             "by kernel reduction (`decide +kernel`); no native_decide. -/\n\n"
             "set_option maxRecDepth 100000\nset_option maxHeartbeats 0\n\n"
             "namespace OpenTheory.QuantizedMLPDigits\nopen OpenTheory.QuantizedMLP\n\n"
             "def networkCodes : List ℕ := "+str(artifact["model"]["codes"])+"\n\n"
             "theorem networkCodes_length : networkCodes.length = digits16.parameterCount := by\n"
             "  decide +kernel\n\n"
             # The type must be syntactically `digits16.parameterCount`, not its
             # value 118, or `simp`/`rw` cannot match `errorCount` lemmas.
             "def network : Code digits16.parameterCount 4 := codeOfList _ networkCodes\n"]
    names = []
    for i in range(0, 1400, 20):
        name = f"batch{i//20:02d}"
        names.append(name)
        chunk = artifact["training_rows"][i:i+20]
        rows = ",\n  ".join("("+str(row[:-1])+", "+str(row[-1])+")" for row in chunk)
        parts.append(f"\ndef {name} : List Observation := [\n  {rows}]\n\n"
                     f"theorem {name}_errors : errorCount digits16 network {name} = "
                     f"{error_count(artifact['model'], chunk)} := by\n"
                     "  rw [network, errorCount_codeOfList _ _ networkCodes_length]\n"
                     "  decide +kernel\n")
    parts.append("\ndef trainingRows : List Observation :=\n  "+" ++ ".join(names)+"\n")
    parts.append("\ntheorem trainingRows_length : trainingRows.length = 1400 := by decide\n")
    parts.append(f"\ntheorem training_errors : errorCount digits16 network trainingRows = {errors} := by\n"
                 "  simp only [trainingRows, errorCount_append, "+", ".join(n+"_errors" for n in names)+"]\n"
                 "\ntheorem empirical_error :\n"
                 "    StatLean.StatisticalLearning.empRisk (classificationLoss digits16) trainingRows.get network =\n"
                 f"      ({rate.numerator} / {rate.denominator} : ℝ) := by\n"
                 "  rw [empiricalRisk_eq_errorCount, training_errors, trainingRows_length]\n  norm_num\n\n"
                 "end OpenTheory.QuantizedMLPDigits\n")
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text("".join(parts))


def train(output):
    import numpy as np
    import torch
    from sklearn.datasets import load_digits

    torch.set_num_threads(1)
    torch.set_default_dtype(torch.float64)
    digits = load_digits()
    # Fixed 2x2 block sums: integer pixels in [0,64], no fitted preprocessing.
    x = digits.images.astype(np.int64).reshape(-1, 4, 2, 4, 2).sum(axis=(2, 4)).reshape(-1, 16)
    rows = np.column_stack((x, digits.target)).tolist()
    order = np.random.default_rng(20261023).permutation(len(rows))
    train_rows = [rows[i] for i in order[:1400]]
    heldout_rows = [rows[i] for i in order[1400:]]
    tx = torch.tensor([r[:-1] for r in train_rows]) / 64
    ty = torch.tensor([r[-1] for r in train_rows], dtype=torch.long)
    best = None
    for seed in range(12):
        torch.manual_seed(seed)
        params = [torch.nn.Parameter(torch.randn(shape)*0.3) for shape in
                  [(4, 16), (4,), (10, 4), (10,)]]
        with torch.no_grad():
            params[1].fill_(0.7)
        opt = torch.optim.Adam(params, lr=0.01)
        for epoch in range(2500):
            # Straight-through optimization only chooses a member of a fixed class.
            quantized = (params if epoch < 600 else
                         [p + (p.round().clamp(-2, 1)-p).detach() for p in params])
            w1, b1, w2, b2 = quantized
            hidden = torch.relu(tx @ (w1*0.5).T + b1*0.5)
            logits = (hidden @ w2.T + b2) * 3
            loss = torch.nn.functional.cross_entropy(logits, ty)
            opt.zero_grad()
            loss.backward()
            opt.step()
            with torch.no_grad():
                for p in params:
                    p.clamp_(-2.49, 1.49)
            if epoch >= 600 and epoch % 25 == 0:
                errors = int((logits.argmax(dim=1) != ty).sum())
                if best is None or errors < best[0]:
                    codes = torch.cat([p.detach().flatten() for p in quantized]).round().to(torch.int64)
                    best = (errors, (codes+2).tolist(), seed, epoch)
        print(f"seed={seed} best_training_errors={best[0]}/1400", flush=True)
    model = dict(inputs=16, hidden=4, classes=10, levels=4, codes=best[1])
    artifact = dict(model=model, training_rows=train_rows, heldout_rows=heldout_rows,
                    provenance=dict(dataset="sklearn.datasets.load_digits", split_seed=20261023,
                                    training_seeds=12, selected_seed=best[2], selected_epoch=best[3],
                                    raw_data_sha256=hashlib.sha256(digits.data.tobytes()).hexdigest(),
                                    target_sha256=hashlib.sha256(digits.target.tobytes()).hexdigest()))
    artifact["certificate"] = verify(artifact)
    if artifact["certificate"]["training_errors"] != best[0]:
        raise RuntimeError("Floating-point training and integer inference disagree")
    artifact = refine(artifact)
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(artifact, separators=(",", ":"))+"\n")
    print(json.dumps(artifact["certificate"], indent=2))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=["train", "verify", "export"])
    parser.add_argument("artifact", type=Path)
    parser.add_argument("--lean-output", type=Path,
                        default=Path("examples/certified_accuracy/lean/CertifiedDigits/QuantizedMLPDigits.lean"))
    args = parser.parse_args()
    if args.mode == "train":
        train(args.artifact)
    elif args.mode == "export":
        export_lean(json.loads(args.artifact.read_text()), args.lean_output)
    else:
        print(json.dumps(verify(json.loads(args.artifact.read_text())), indent=2))


if __name__ == "__main__":
    main()
