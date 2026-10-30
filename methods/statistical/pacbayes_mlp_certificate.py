#!/usr/bin/env python3
"""Train and certify a 64–16–10 two-bit ReLU MLP with a learned PAC-Bayes prior.

Protocol, fixed before the bound observations were used:
  * prior data: the 1400 training rows. The architecture was chosen by the
    PAC-Bayes bound on an internal 700/700 split of these rows only;
  * bound data: the 397 held-out rows, used only by `verify` and `export`;
  * prior: product over coordinates centred on the trained code, m = 20;
  * posterior: the Dirac mass at the centre; t from an 8-point grid; δ = 1/20.

Verification and Lean export need only the Python standard library. The integer
forward pass mirrors `OpenTheory.QuantizedMLP.scoresOfWeights` exactly.
"""
import argparse
import hashlib
import json
import math
from fractions import Fraction
from pathlib import Path

ARCH = dict(inputs=64, hidden=16, classes=10, hidden_bias_scale=16, output_bias_scale=32)
SPLIT_SEED = 20261023
N_TRAIN = 1400
M = 20
T_GRID = [Fraction(k + 1, 4) for k in range(8)]
DELTA = Fraction(1, 20)
LOG2_HI = Fraction(6931471808, 10 ** 10)      # Real.log_two_lt_d9
GAMMA = 3 + 3 * LOG2_HI                       # ≥ log (8 / δ) = log 160
TAYLOR = 8
BATCH = 20


def parameter_count(model):
    d, h, c = (model[k] for k in ("inputs", "hidden", "classes"))
    return d * h + h + h * c + c


def validate(model):
    for k, v in ARCH.items():
        if model[k] != v:
            raise ValueError(f"The certificate fixes {k} = {v} before training")
    if model["levels"] != 4:
        raise ValueError("The decoder has exactly four levels: -2, -1, 0, 1")
    if len(model["codes"]) != parameter_count(model):
        raise ValueError("All weights and biases must be present")
    if any(type(v) is not int or not 0 <= v < 4 for v in model["codes"]):
        raise ValueError("Codes must be integers in [0, 4)")


def dot(ws, xs):
    return sum(a * b for a, b in zip(ws, xs))


def rows(k, r, ws):
    return [ws[i * k:(i + 1) * k] for i in range(r)]


def scores(model, x):
    """Mirror of `scoresOfWeights`: zips truncate exactly like `List.zipWith`."""
    d, h, c = (model[k] for k in ("inputs", "hidden", "classes"))
    s1, s2 = model["hidden_bias_scale"], model["output_bias_scale"]
    ws = [v - 2 for v in model["codes"]]
    rest = ws[d * h:]
    out = rest[h:]
    hidden = [max(0, dot(row, x) + s1 * b) for row, b in zip(rows(d, h, ws), rest[:h])]
    return [dot(row, hidden) + s2 * b for row, b in zip(rows(h, c, out), out[h * c:][:c])]


def argmax_first(s):
    best = (s[0] if s else 0, 0)
    for i, v in enumerate(s):
        if best[0] < v:
            best = (v, i)
    return best[1]


def error_count(model, data):
    return sum(argmax_first(scores(model, row[:-1])) != row[-1] for row in data)


def factorial(k):
    return math.factorial(k)


def ceil_to(x, scale):
    return Fraction(math.ceil(x * scale), scale)


def floor_to(x, scale):
    return Fraction(math.floor(x * scale), scale)


def numerics(errors, n, p, t):
    """Rational constants for `dirac_certificate` at one grid point."""
    x = Fraction(3, 2 ** M)
    kl = p * x / (1 - x)
    c_hi = t * Fraction(errors, n) + (kl + GAMMA) / n
    c = ceil_to(c_hi, 10 ** 8)
    if not 0 <= c <= 1:
        return None                     # outside the range of the Taylor bound
    e_taylor = sum(c ** i / factorial(i) for i in range(TAYLOR)) + \
        c ** TAYLOR * (TAYLOR + 1) / (factorial(TAYLOR) * TAYLOR)
    E = ceil_to(e_taylor, 10 ** 12)
    l_taylor = sum(t ** i / factorial(i) for i in range(TAYLOR))
    L = floor_to(l_taylor, 10 ** 12)
    B = ceil_to((1 - 1 / E) / (1 - 1 / L), 10 ** 4)
    return dict(t=t, c=c, E=E, L=L, B=B)


def verify(artifact):
    model = artifact["model"]
    validate(model)
    data = artifact["heldout_rows"]
    for row in data:
        if len(row) != ARCH["inputs"] + 1 or any(type(v) is not int or not 0 <= v <= 16
                                                for v in row[:-1]):
            raise ValueError("Invalid pixel row")
        if type(row[-1]) is not int or not 0 <= row[-1] < ARCH["classes"]:
            raise ValueError("Invalid class label")
    n, p = len(data), parameter_count(model)
    errors = error_count(model, data)
    candidates = [r for r in (numerics(errors, n, p, t) for t in T_GRID) if r is not None]
    best = min(candidates, key=lambda r: (r["B"], r["t"])) if candidates else \
        dict(t=T_GRID[0], B=Fraction(1))   # vacuous: nothing to certify
    # Exact Catoni optimum over the grid, for comparison with the rounded certificate.
    kl = -p * math.log(1 - 3 / 2 ** M)
    exact = min((1 - math.exp(-(float(t) * errors / n + (kl + math.log(8 / float(DELTA))) / n)))
                / (1 - math.exp(-float(t))) for t in T_GRID)
    return dict(parameters=p, bound_n=n, heldout_errors=errors, heldout_error=errors / n,
                prior_sharpness_m=M, t=str(best["t"]), population_error_upper_bound=str(best["B"]),
                population_error_upper_bound_float=float(best["B"]),
                unrounded_catoni_bound=exact, confidence_at_least=float(1 - DELTA),
                assumptions="held-out rows IID from the population and independent of the "
                            "training rows; prior and architecture fixed from training rows")


def lean_rat(x):
    x = Fraction(x)
    return f"({x.numerator} / {x.denominator} : ℝ)" if x.denominator != 1 else f"({x.numerator} : ℝ)"


def export_lean(artifact, output):
    report = verify(artifact)
    model, data = artifact["model"], artifact["heldout_rows"]
    n, p = len(data), parameter_count(model)
    errors = report["heldout_errors"]
    num = numerics(errors, n, p, Fraction(report["t"]))
    if num is None or num["B"] >= 1:
        raise ValueError("No non-vacuous certificate to export")
    k0 = T_GRID.index(num["t"])
    a = ARCH
    parts = [f"""import Specs.QuantizedMLP.PACBayes

/-! # PAC-Bayes certificate for a 64–16–10 two-bit MLP on held-out digits

Generated by `methods/statistical/pacbayes_mlp_certificate.py export`; do not edit.
The network, trained on the 1400 training rows only, is the prior centre.
The 397 held-out rows are the bound sample. Error counts are checked by
kernel reduction (`decide +kernel`, no `native_decide`). -/

set_option maxRecDepth 100000

namespace OpenTheory.PACBayesMLPDigits
open MeasureTheory StatLean.StatisticalLearning OpenTheory.PACBayes OpenTheory.QuantizedMLP

def arch : Arch := ⟨{a['inputs']}, {a['hidden']}, {a['classes']}, {a['hidden_bias_scale']}, {a['output_bias_scale']}⟩

def networkCodes : List ℕ := {model['codes']}

theorem networkCodes_length : networkCodes.length = arch.parameterCount := by decide +kernel

/-- The prior centre, trained on the training rows only. -/
def network : Code arch.parameterCount 4 := codeOfList _ networkCodes
"""]
    names = []
    for i in range(0, n, BATCH):
        name = f"batch{i // BATCH:02d}"
        names.append(name)
        chunk = data[i:i + BATCH]
        body = ",\n  ".join(f"({row[:-1]}, {row[-1]})" for row in chunk)
        parts.append(f"""
def {name} : List Observation := [
  {body}]

theorem {name}_errors : errorCount arch network {name} = {error_count(model, chunk)} := by
  rw [network, errorCount_codeOfList _ _ networkCodes_length]
  decide +kernel
""")
    parts.append(f"""
def heldoutRows : List Observation :=
  {" ++ ".join(names)}

theorem heldoutRows_length : heldoutRows.length = {n} := by decide +kernel

theorem heldout_errors : errorCount arch network heldoutRows = {errors} := by
  simp only [heldoutRows, errorCount_append, {", ".join(nm + "_errors" for nm in names)}]

/-- The saved held-out rows, indexed as a sample of size {n}. -/
def heldoutSample : Fin {n} → Observation :=
  fun i => heldoutRows.get (Fin.cast heldoutRows_length.symm i)

theorem heldout_empirical_error :
    empRisk (classificationLoss arch) heldoutSample network = ({errors} / {n} : ℝ) := by
  unfold heldoutSample
  rw [empiricalRisk_eq_errorCount_cast arch network heldoutRows heldoutRows_length,
    heldout_errors]
  norm_num

/-- The grid of Catoni temperatures `t = 1/4, …, 2`, fixed in advance. -/
noncomputable def tGrid : Finset ℝ := (Finset.range 8).image fun k : ℕ => ((k : ℝ) + 1) / 4

theorem tGrid_card : tGrid.card = 8 := by
  rw [tGrid, Finset.card_image_of_injective _ fun a b h => by
    have : ((a : ℝ) + 1) / 4 = ((b : ℝ) + 1) / 4 := h
    exact_mod_cast (by linarith : (a : ℝ) = b)]
  simp

theorem tGrid_nonempty : tGrid.Nonempty := ⟨1 / 4, Finset.mem_image.2 ⟨0, by simp, by norm_num⟩⟩

/-- **PAC-Bayes for the learned prior.** With probability at least 95% over the
held-out sample, every posterior on codes satisfies Catoni's inequality for every
grid temperature, relative to the prior centred on `network` with `m = {M}`. -/
theorem heldout_pacBayes (P : Population Observation) :
    sampleLaw P.law {n} (⋃ t ∈ tGrid, badEvent (classificationLoss arch) P.law
      (centredPrior {M} network) {n} t (1 / 20 / tGrid.card)) ≤ ENNReal.ofReal (1 / 20) :=
  mlp_pacBayes P arch network (by norm_num) {n} tGrid tGrid_nonempty (by norm_num)

theorem t_mem : {lean_rat(num['t'])} ∈ tGrid := Finset.mem_image.2 ⟨{k0}, by simp, by norm_num⟩

theorem log_confidence_le : Real.log (1 / (1 / 20 / tGrid.card)) ≤ 3 + 3 * 0.6931471808 := by
  simpa [tGrid_card] using log_one_div_twenty_div_eight_le

theorem catoni_rhs_le : {lean_rat(num['t'])} * ({errors} / {n} : ℝ) +
    (arch.parameterCount * ((3 / 2 ^ {M}) / (1 - 3 / 2 ^ {M})) + (3 + 3 * 0.6931471808)) / {n} ≤
      {lean_rat(num['c'])} := by
  norm_num [Arch.parameterCount, arch]

theorem exp_c_le : Real.exp {lean_rat(num['c'])} ≤ {lean_rat(num['E'])} :=
  (Real.exp_bound' (by norm_num) (by norm_num) (n := {TAYLOR}) (by norm_num)).trans
    (by norm_num [Finset.sum_range_succ, Nat.factorial])

theorem le_exp_t : {lean_rat(num['L'])} ≤ Real.exp {lean_rat(num['t'])} :=
  le_trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
    (Real.sum_le_exp_of_nonneg (by norm_num) {TAYLOR})

theorem inversion_le : (1 - 1 / {lean_rat(num['E'])}) / (1 - 1 / {lean_rat(num['L'])}) ≤
    {lean_rat(num['B'])} := by
  norm_num

/-- **Certificate.** With probability at least 95% over {n} IID held-out
observations, if the saved network makes at most {errors} errors on them then its
population error is at most {float(num['B']):.2%}. -/
theorem heldout_certificate (P : Population Observation) :
    sampleLaw P.law {n} {{s | empRisk (classificationLoss arch) s network ≤ ({errors} / {n} : ℝ) ∧
      {lean_rat(num['B'])} < P.risk (classificationLoss arch network)}} ≤ ENNReal.ofReal (1 / 20) :=
  dirac_certificate P arch network (m := {M}) (n := {n}) (by norm_num) (by norm_num) tGrid
    tGrid_nonempty (by norm_num) t_mem (by norm_num) log_confidence_le catoni_rhs_le
    (by norm_num) exp_c_le le_exp_t (by norm_num) inversion_le

/-- The realized held-out sample lies in the 5% failure event exactly when the
saved network's population error exceeds the certified bound. -/
theorem heldoutSample_fails_iff (P : Population Observation) :
    heldoutSample ∈ {{s | empRisk (classificationLoss arch) s network ≤ ({errors} / {n} : ℝ) ∧
      {lean_rat(num['B'])} < P.risk (classificationLoss arch network)}} ↔
      {lean_rat(num['B'])} < P.risk (classificationLoss arch network) := by
  simp [heldout_empirical_error]

end OpenTheory.PACBayesMLPDigits
""")
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text("".join(parts))


def load_rows():
    import numpy as np
    from sklearn.datasets import load_digits
    digits = load_digits()
    x = digits.images.astype(np.int64).reshape(-1, 64)
    allrows = np.column_stack((x, digits.target)).tolist()
    order = np.random.default_rng(SPLIT_SEED).permutation(len(allrows))
    return digits, [allrows[i] for i in order[:N_TRAIN]], [allrows[i] for i in order[N_TRAIN:]]


def train_codes(model, train_rows, seeds=range(6), epochs=2500):
    """Straight-through quantized training, then coordinate refinement.
    Selection uses training rows only."""
    import numpy as np
    import torch
    torch.set_num_threads(1)
    torch.set_default_dtype(torch.float64)
    d, h, c = model["inputs"], model["hidden"], model["classes"]
    s1, s2 = model["hidden_bias_scale"], model["output_bias_scale"]
    x = np.asarray([r[:-1] for r in train_rows], dtype=np.int64)
    y = np.asarray([r[-1] for r in train_rows], dtype=np.int64)
    tx, ty = torch.tensor(x, dtype=torch.float64), torch.tensor(y)

    def int_errors(w):
        W1, b1 = w[:d * h].reshape(h, d), w[d * h:d * h + h]
        o = w[d * h + h:]
        W2, b2 = o[:h * c].reshape(c, h), o[h * c:h * c + c]
        hid = np.maximum(0, x @ W1.T + s1 * b1)
        return int(((hid @ W2.T + s2 * b2).argmax(1) != y).sum())

    best = None
    for seed in seeds:
        torch.manual_seed(seed)
        P = [torch.nn.Parameter(torch.randn(s) * 0.3) for s in [(h, d), (h,), (c, h), (c,)]]
        with torch.no_grad():
            P[1].fill_(0.5)
        opt = torch.optim.Adam(P, lr=0.01)
        for ep in range(epochs):
            q = ep >= epochs // 4
            W1, b1, W2, b2 = [p + (p.round().clamp(-2, 1) - p).detach() if q else p for p in P]
            # float view of the integer net: hidden = hidden_int / s1, logit = score / s2
            hid = torch.relu((tx / s1) @ W1.T + b1)
            loss = torch.nn.functional.cross_entropy(3.0 * ((s1 / s2) * hid @ W2.T + b2), ty)
            opt.zero_grad()
            loss.backward()
            opt.step()
            with torch.no_grad():
                for p in P:
                    p.clamp_(-2.49, 1.49)
        w = np.concatenate([p.detach().round().clamp(-2, 1).numpy().astype(np.int64).ravel()
                            for p in P])
        e = int_errors(w)
        print(f"seed={seed} training_errors={e}/{len(y)}", flush=True)
        if best is None or e < best[0]:
            best = (e, w, seed)
    e, w, seed = best
    rng = np.random.default_rng(54)
    passes = 0
    for passes in range(1, 11):
        previous = e
        for i in rng.permutation(len(w)):
            keep = w[i]
            for v in range(-2, 2):
                w[i] = v
                ev = int_errors(w)
                if ev < e:
                    e, keep = ev, v
            w[i] = keep
        if e == previous:
            break
    return (w + 2).tolist(), dict(training_seeds=len(seeds), selected_seed=seed,
                                  training_errors=e, refinement_passes=passes, epochs=epochs)


def train(output):
    digits, train_rows, heldout_rows = load_rows()
    model = dict(ARCH, levels=4)
    model["codes"], record = train_codes(model, train_rows)
    import numpy, sklearn, torch
    artifact = dict(
        model=model, training_rows=train_rows, heldout_rows=heldout_rows,
        provenance=dict(dataset="sklearn.datasets.load_digits", inputs="raw 8x8 pixels in [0,16]",
                        split_seed=SPLIT_SEED, **record,
                        raw_data_sha256=hashlib.sha256(digits.data.tobytes()).hexdigest(),
                        target_sha256=hashlib.sha256(digits.target.tobytes()).hexdigest(),
                        versions=dict(numpy=numpy.__version__, torch=torch.__version__,
                                      sklearn=sklearn.__version__)),
        protocol=dict(prior="centred on the trained code", m=M, t_grid=[str(t) for t in T_GRID],
                      delta=str(DELTA), posterior="Dirac at the prior centre"))
    artifact["certificate"] = verify(artifact)
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(artifact, separators=(",", ":")) + "\n")
    print(json.dumps(artifact["certificate"], indent=2))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=["train", "verify", "export"])
    parser.add_argument("artifact", type=Path)
    parser.add_argument("--lean-output", type=Path,
                        default=Path("examples/certified_accuracy/lean/CertifiedDigits/PACBayesMLPDigits.lean"))
    args = parser.parse_args()
    if args.mode == "train":
        train(args.artifact)
    elif args.mode == "export":
        export_lean(json.loads(args.artifact.read_text()), args.lean_output)
    else:
        print(json.dumps(verify(json.loads(args.artifact.read_text())), indent=2))


if __name__ == "__main__":
    main()
