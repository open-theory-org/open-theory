#!/usr/bin/env python3
"""A SYNTHETIC six-month stream of client-onboarding (KYC) decisions, seeded and reproducible.

The story the data tell:

| Months | What happens |
| --- | --- |
| 1–3 | two channels (branch, online); model `kyc-v1` lets about 0.15% fraud through among approvals |
| 4–5 | a new distribution partner (`partner-api`, 30% of applicants) brings a synthetic-identity ring the model was never trained on; the online share falls from 65% to 45%; fraud among approvals rises to about 2.4% |
| 6 | the bank retrains (`kyc-v2`); fraud among approvals falls back to about 0.25%, the new mix stays |

Two pools per month are written, one JSON object per line (`pool-rate` reads the field `output`):

* `applicants_M.jsonl`: every applicant, `output` = the channel (the drift claim counts "online");
* `approved_M.jsonl`: every approved applicant, `output` = "approve", `label` = the decision the
  confirmed outcome calls for ("reject" if the client turned out to be fraudulent). An item fails
  (`output` ≠ `label`) exactly when the model approved a fraudster. The outcome is committed with
  the decision, so the verifier never has to trust labels supplied after the draw.
"""
from __future__ import annotations

import hashlib
import json
import random
import sys
from pathlib import Path

MONTHS = 6
APPLICANTS = 20_000

# channel: (share in months 1–3, share in months 4–6, fraud-attempt rate, legit approval rate)
CHANNELS = {
    "branch": (0.35, 0.25, 0.005, 0.85),
    "online": (0.65, 0.45, 0.020, 0.80),
    "partner-api": (0.00, 0.30, 0.100, 0.78),
}
# model: channel -> probability of rejecting a fraud attempt
CATCH = {
    "kyc-v1": {"branch": 0.92, "online": 0.92, "partner-api": 0.40},
    "kyc-v2": {"branch": 0.95, "online": 0.95, "partner-api": 0.95},
}


def model_for(month: int) -> str:
    return "kyc-v2" if month == 6 else "kyc-v1"


def make(out: Path, seed: int = 2026) -> dict:
    rng = random.Random(seed)
    out.mkdir(parents=True, exist_ok=True)
    stats = {}
    for m in range(1, MONTHS + 1):
        model = model_for(m)
        names = list(CHANNELS)
        weights = [CHANNELS[c][0 if m <= 3 else 1] for c in names]
        applicants, approved = [], []
        for i in range(APPLICANTS):
            ch = rng.choices(names, weights)[0]
            _, _, fraud_rate, approve_rate = CHANNELS[ch]
            fraud = rng.random() < fraud_rate
            ok = rng.random() >= CATCH[model][ch] if fraud else rng.random() < approve_rate
            cid = hashlib.sha256(f"{seed}/{m}/{i}".encode()).hexdigest()[:24]
            applicants.append({"id": cid, "month": m, "field": "channel", "output": ch})
            if ok:
                approved.append({"id": cid, "month": m, "model": model, "channel": ch,
                                 "output": "approve", "label": "reject" if fraud else "approve"})
        for name, rows in (("applicants", applicants), ("approved", approved)):
            with (out / f"{name}_{m}.jsonl").open("w", encoding="utf-8") as f:
                for r in rows:
                    f.write(json.dumps(r, separators=(",", ":")) + "\n")
        stats[m] = {"model": model, "applicants": len(applicants), "approved": len(approved),
                    "online_share": sum(a["output"] == "online" for a in applicants) / len(applicants),
                    "fraud_among_approved": sum(a["label"] == "reject" for a in approved) / len(approved)}
    (out / "truth.json").write_text(json.dumps(stats, indent=1))
    return stats


if __name__ == "__main__":
    for m, s in make(Path(sys.argv[1] if len(sys.argv) > 1 else "stream")).items():
        print(f"month {m}: {s}")
