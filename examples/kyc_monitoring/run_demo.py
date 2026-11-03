#!/usr/bin/env python3
"""KYC monitoring demo: six months of certified, re-checkable monitoring claims (SYNTHETIC data).

    run_demo.py generate OUT [--offline]   data, policy, commitments, draws, bundles (~7 min, online)
    run_demo.py verify OUT                 re-check everything and print the monthly report (offline)
    run_demo.py tamper OUT                 two forgeries of month 4, both rejected (offline)

`generate` is the bank's side and is untrusted; `verify` is what a regulator runs. Every bound is
checked by the Lean kernel through `ot verify`; this script only orchestrates the `ot` CLI and
reads the verified bundles. See README.md for what each claim means and assumes.
"""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import os
import shutil
import ssl
import subprocess
import sys
import time
import urllib.request
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
OT = [sys.executable, str(ROOT / "interfaces" / "cli" / "ot")]
sys.path.insert(0, str(HERE))
import make_stream  # noqa: E402


def load(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


producer = load("ot_pool_producer", ROOT / "methods" / "statistical" / "pool_rate_certificate.py")

FREETSA_URL = "https://freetsa.org/tsr"
FREETSA_ROOT_URL = "https://freetsa.org/files/cacert.pem"
FREETSA_ROOT_SHA256 = "a6379e7cecc05faa3cbf076013d745e327bbbaa38c0b9af22469d4701d18aabc"  # DER, pinned

ISSUER = "demo-bank"
FRAUD_N, FRAUD_DELTA, STANDARD = 3000, 1000, Fraction(1, 100)
DRIFT_N, DRIFT_DELTAS, TOLERANCE = 5000, [4000, 4000, 4000, 4000], Fraction(10, 100)
DRIFT_VALUE = "online"  # a share strictly between 0 and 1 in every month (see README: a 0% or 100% pool)

POLICY = {
    "format": "opentheory-kyc-demo-policy/0.1",
    "issuer": ISSUER,
    "task": "client onboarding (KYC): the model approves or rejects each applicant",
    "data": "SYNTHETIC (examples/kyc_monitoring/make_stream.py)",
    "window": "calendar month",
    "baseline_month": 1,
    "claims": {
        "fraud": {
            "measures": "share of the month's approved applicants later confirmed fraudulent",
            "certificate": "pool-rate", "pool": "approved_M.jsonl", "n": FRAUD_N, "delta": f"1/{FRAUD_DELTA}",
            "standard": f"at most {STANDARD.numerator}/{STANDARD.denominator}",
            "action": "if the standard cannot be certified: model review",
        },
        "drift": {
            "measures": f"share of applicants arriving through '{DRIFT_VALUE}', month M against the baseline month",
            "certificate": "rate-gap", "pools": ["applicants_1.jsonl", "applicants_M.jsonl"], "n": DRIFT_N,
            "deltas": [f"1/{d}" for d in DRIFT_DELTAS],
            "tolerance": f"{TOLERANCE.numerator}/{TOLERANCE.denominator}",
            "action": "if a shift beyond the tolerance is certified: revalidate the model on the new mix",
        },
    },
}


def claims() -> list[tuple[str, int]]:
    out = []
    for m in range(1, make_stream.MONTHS + 1):
        if m > 1:
            out.append(("drift", m))
        out.append(("fraud", m))
    return out


def cid(kind: str, m: int) -> str:
    return f"m{m}-{kind}"


def sha256_file(p: Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()


def ot(*args: str, env=None, check=True) -> subprocess.CompletedProcess:
    r = subprocess.run([*OT, *args], capture_output=True, text=True, env=env)
    if check and r.returncode != 0:
        sys.exit(f"ot {' '.join(args[:3])} failed:\n{r.stdout}{r.stderr}")
    return r


# ---------------------------------------------------------------- generate (the bank, untrusted)

def generate(out: Path, offline_tsa: bool) -> None:
    if (out / "bundles").exists():
        sys.exit(f"{out} already holds a run; choose another directory")
    data, roots, work = out / "data", out / "tsa_roots", out / "work"
    for d in (roots, work):
        d.mkdir(parents=True, exist_ok=True)
    print("1. synthetic stream: 6 months × 20,000 applicants")
    make_stream.make(data)

    if offline_tsa:
        tsa_dir = (out / "test_tsa").resolve()
        producer.make_test_tsa(tsa_dir)
        shutil.copy(tsa_dir / "ca.crt", roots / "test-tsa.pem")
        stamp, tsa_args, who = (lambda sha: producer.tsa_local(sha, tsa_dir)), ["--test-tsa", str(tsa_dir)], \
            "a local TEST authority"
    else:
        pem = urllib.request.urlopen(FREETSA_ROOT_URL, timeout=30).read().decode()
        if hashlib.sha256(ssl.PEM_cert_to_DER_cert(pem)).hexdigest() != FREETSA_ROOT_SHA256:
            sys.exit("the FreeTSA root does not match its pinned fingerprint")
        (roots / "freetsa.pem").write_text(pem)
        stamp, tsa_args, who = (lambda sha: producer.tsa_url(sha, FREETSA_URL)), ["--tsa-url", FREETSA_URL], \
            "FreeTSA (public RFC 3161 authority; only digests are sent)"

    print(f"2. policy (claims, thresholds, actions) written and timestamped by {who}")
    (out / "policy.json").write_text(json.dumps(POLICY, indent=1))
    (out / "policy.tsr").write_bytes(stamp(sha256_file(out / "policy.json")))

    first = producer.drand_get(producer.DEFAULT_CHAIN, "public/latest")["round"] + 3
    plan = [(kind, m, first + i) for i, (kind, m) in enumerate(claims())]
    print(f"3. {len(plan)} commitments, each to its own future drand round ({first}–{first + len(plan) - 1})")
    for kind, m, rnd in plan:
        c = work / cid(kind, m)
        common = ["--issuer", ISSUER, "--round", str(rnd), *tsa_args, "--out", str(c)]
        if kind == "fraud":
            ot("certify", "pool-rate", "commit", "--pool", str(data / f"approved_{m}.jsonl"), "--n", str(FRAUD_N),
               "--delta-den", str(FRAUD_DELTA), *common)
        else:
            ot("certify", "pool-rate", "commit", "--pool", str(data / "applicants_1.jsonl"), "--n", str(DRIFT_N),
               "--pool-b", str(data / f"applicants_{m}.jsonl"), "--n-b", str(DRIFT_N),
               "--positive", json.dumps(DRIFT_VALUE), "--deltas", *map(str, DRIFT_DELTAS), *common)
        print(f"   committed {cid(kind, m):9s} → round {rnd}")

    eta = producer.drand_get(producer.DEFAULT_CHAIN, "info")
    last = eta["genesis_time"] + (plan[-1][2] - 1) * eta["period"]
    print(f"4. draws and bundles (the last round is published in about {max(0, int(last - time.time()))} s)")
    for kind, m, rnd in plan:
        b = out / "bundles" / cid(kind, m)
        if kind == "fraud":
            r = ot("certify", "pool-rate", "prove", "--commitment", str(work / cid(kind, m)),
                   "--pool", str(data / f"approved_{m}.jsonl"), "--out", str(b))
        else:
            r = ot("certify", "pool-rate", "prove", "--commitment", str(work / cid(kind, m)),
                   "--pool", str(data / "applicants_1.jsonl"), "--pool-b", str(data / f"applicants_{m}.jsonl"),
                   "--out", str(b))
        print(f"   {cid(kind, m):9s} round {rnd}: {r.stdout.strip().splitlines()[-1]}")
    print(f"\ndone. Now: python3 {Path(__file__).relative_to(ROOT)} verify {out}")


# ---------------------------------------------------------------- verify (the regulator)

def env_for(out: Path) -> dict:
    return {**os.environ, "OT_TSA_ROOTS": str((out / "tsa_roots").resolve())}


def verify_bundle(out: Path, b: Path) -> dict:
    r = ot("verify", str(b), "--json", env=env_for(out), check=False)
    if r.returncode == 2:
        sys.exit(f"the verifier could not run on {b.name}:\n{r.stdout}{r.stderr}")
    return json.loads(r.stdout)


def frac(x: dict) -> Fraction:
    return Fraction(x["num"], x["den"])


def pct(x: Fraction) -> str:
    return f"{float(x):.2%}"


def check_policy(out: Path) -> tuple[bool, str]:
    os.environ["OT_TSA_ROOTS"] = str((out / "tsa_roots").resolve())
    rfc = load("ot_rfc3161", ROOT / "verifier" / "attestations" / "rfc3161.py")
    drand = load("ot_drand", ROOT / "verifier" / "attestations" / "drand.py")
    ok, when, _ = rfc.check((out / "policy.tsr").read_bytes(), sha256_file(out / "policy.json"))
    first = min(json.loads((b / "commitment.json").read_text())["beacon"]["round"]
                for b in (out / "bundles").iterdir())
    published = drand.round_time(producer.DEFAULT_CHAIN, first)
    before = ok and when is not None and when.timestamp() < published
    return before, (f"policy sha256:{sha256_file(out / 'policy.json')[:12]}… timestamped {when:%Y-%m-%d %H:%M:%S} UTC, "
                    f"before the first draw (round {first})" if before else "policy timestamp INVALID or not before the draws")


def verify(out: Path) -> None:
    tf = out / "data" / "truth.json"  # the synthetic answer key: on the bank's side only, optional here
    truth = json.loads(tf.read_text()) if tf.exists() else {}
    ok, line = check_policy(out)
    print(("✔ " if ok else "✘ ") + line + "\n")
    rows, details = [], []
    for m in range(1, make_stream.MONTHS + 1):
        sample = json.loads((out / "bundles" / cid("fraud", m) / "sample.json").read_text())
        row = {"m": m, "model": sample["items"][0]["leaf"].get("model", "?"), "truth": truth.get(str(m))}
        for kind in ("drift", "fraud"):
            b = out / "bundles" / cid(kind, m)
            if not b.exists():
                continue
            rep = verify_bundle(out, b)
            details.append((cid(kind, m), rep))
            cert = json.loads((b / "certificate.json").read_text())["claim"]
            if not rep["accepted"]:
                row[kind] = {"status": "REJECTED", "text": rep["reason"]}
                continue
            if kind == "fraud":
                u = frac(cert["bound"])
                meets = u <= STANDARD
                row[kind] = {"status": "MEETS STANDARD" if meets else "NOT CERTIFIED → model review",
                             "text": f"≤ {pct(u)} ({cert['count']}/{FRAUD_N} sampled)"}
            else:
                pA, qA, pB, qB = (frac(cert[k]["bound"]) for k in ("upperA", "lowerA", "upperB", "lowerB"))
                eps = frac(cert["epsilon"])
                shift = max(Fraction(0), (1 - qB) - pA, (1 - qA) - pB)
                if eps <= TOLERANCE:
                    status, text = "STABLE", f"change ≤ {pct(eps)}"
                elif shift > TOLERANCE:
                    status, text = "DRIFT → revalidate", f"change ≥ {pct(shift)} (≤ {pct(eps)})"
                else:
                    status, text = "UNCLEAR", f"change ≤ {pct(eps)}, not certified either way"
                row[kind] = {"status": status, "text": text + f"; month {m} in [{pct(1 - qB)}, {pct(pB)}]"}
        rows.append(row)
        f, d = row.get("fraud", {}), row.get("drift")
        print(f"month {m} [{row['model']}]  fraud among approved: {f.get('text', '')} → {f.get('status', '')}")
        print(f"                 client mix vs month 1:  "
              + (f"{d['text']} → {d['status']}" if d else "baseline"))
    write_report(out, rows, details, line)
    n_ok = sum(rep["accepted"] for _, rep in details)
    print(f"\n{n_ok}/{len(details)} certificates accepted by the Lean kernel; report: {out / 'report.md'}")


def write_report(out: Path, rows, details, policy_line: str) -> None:
    L = ["# KYC monitoring report (SYNTHETIC data)", "",
         f"Policy: {policy_line}.", "",
         f"Standard: fraud among approved applicants ≤ {pct(STANDARD)} (δ = 1/{FRAUD_DELTA} per month). "
         f"Drift tolerance: the share of `{DRIFT_VALUE}` applicants moves ≤ {pct(TOLERANCE)} points from month 1 "
         f"(δ = 1/1000 per month).", "",
         "| Month | Model | Fraud among approved (certified) | Status | Client mix vs month 1 (certified) | Status | True values (synthetic oracle) |",
         "| --- | --- | --- | --- | --- | --- | --- |"]
    known = lambda t: f"fraud {t['fraud_among_approved']:.2%}, online share {t['online_share']:.2%}" if t else "not available"
    for r in rows:
        f, d = r.get("fraud", {}), r.get("drift")
        L.append(f"| {r['m']} | {r['model']} | {f.get('text', '')} | **{f.get('status', '')}** | "
                 f"{d['text'] if d else 'baseline'} | **{d['status'] if d else '—'}** | "
                 f"{known(r['truth'])} |")
    L += ["", "## Each certificate, as `ot verify` reports it", ""]
    for name, rep in details:
        L += [f"### {name}", "", f"- {'ACCEPTED' if rep['accepted'] else 'REJECTED'}: {rep['summary']}",
              f"- Claim: {rep['claim'] or rep['reason']}"]
        L += [f"- Assumed: {a}" for a in rep.get("assumptions", [])]
        L += [f"- Does not cover: {x}" for x in rep.get("does_not_cover", [])]
        L.append("")
    L += ["The \"change ≥\" figure of a drift row is derived from two of the four kernel-checked bounds of that "
          "certificate (month M's lower bound minus month 1's upper bound), so it holds whenever they do.", ""]
    (out / "report.md").write_text("\n".join(L))


# ---------------------------------------------------------------- tamper (two forgeries, both must fail)

def tamper(out: Path) -> None:
    src = out / "bundles" / cid("fraud", 4)
    cases = []

    hide = out / "tampered" / "hide-a-fraud-case"
    shutil.rmtree(hide, ignore_errors=True)
    shutil.copytree(src, hide)
    sample = json.loads((hide / "sample.json").read_text())
    item = next(x for x in sample["items"] if x["leaf"]["label"] != x["leaf"]["output"])
    item["leaf"]["label"] = "approve"  # relabel a confirmed fraud as legitimate
    producer.write_json(hide / "sample.json", sample)
    cert = json.loads((hide / "certificate.json").read_text())
    cert["evidence"]["sample"]["sha256"] = sha256_file(hide / "sample.json")  # and cover the tracks
    producer.write_json(hide / "certificate.json", cert)
    cases.append(("the bank relabels one confirmed fraud case as legitimate", hide))

    claim = out / "tampered" / "claim-the-standard"
    shutil.rmtree(claim, ignore_errors=True)
    shutil.copytree(src, claim)
    cert = json.loads((claim / "certificate.json").read_text())
    cert["claim"]["bound"] = {"num": STANDARD.numerator * cert["claim"]["bound"]["den"] // STANDARD.denominator,
                              "den": cert["claim"]["bound"]["den"]}
    producer.write_json(claim / "certificate.json", cert)
    cases.append((f"the bank claims month 4 meets the {pct(STANDARD)} standard", claim))

    for what, b in cases:
        rep = verify_bundle(out, b)
        print(f"{what}:\n  {'ACCEPTED (this is a bug)' if rep['accepted'] else 'REJECTED'} — {rep['reason']}\n")


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    s = p.add_subparsers(dest="cmd", required=True)
    g = s.add_parser("generate")
    g.add_argument("out", type=Path)
    g.add_argument("--offline", action="store_true", help="local TEST timestamp authority instead of FreeTSA")
    for name in ("verify", "tamper"):
        s.add_parser(name).add_argument("out", type=Path)
    a = p.parse_args()
    {"generate": lambda: generate(a.out, a.offline), "verify": lambda: verify(a.out),
     "tamper": lambda: tamper(a.out)}[a.cmd]()


if __name__ == "__main__":
    main()
