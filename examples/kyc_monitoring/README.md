# kyc_monitoring: six months of certified KYC monitoring, re-checkable by anyone

**The question a regulator asks** (PRA SS1/23, principle 5: monitoring): *is your client-onboarding
model still meeting its standard, and would you notice if the clients changed?* Today the answer is a
report the regulator has to trust. Here it is a set of certificates the regulator re-checks in about a
minute, on their own machine, without trusting the bank's numbers.

The data are **SYNTHETIC** (`make_stream.py`): 20,000 applicants a month for six months.

| Months | What happens in the data |
| --- | --- |
| 1–3 | model `kyc-v1`, two channels; about 0.15% of approved clients turn out fraudulent |
| 4–5 | a new partner channel (30% of applicants) brings a fraud ring the model never saw: about 2.3%; the online share falls from 65% to 45% |
| 6 | the bank retrains (`kyc-v2`): back to about 0.26%; the new client mix stays |

## Run it

A recorded run: 11/11 certificates accepted; `verify` took 12.5 s; months 4–5 flagged for review and
drift, month 6 back within the standard (drift stays: the new mix is permanent).

```bash
lake build ot_kernel ot_check && pip install py_arkworks_bls12381     # once

python3 examples/kyc_monitoring/run_demo.py generate /tmp/kyc   # the bank: ~7 min, needs the network
python3 examples/kyc_monitoring/run_demo.py verify   /tmp/kyc   # the regulator: offline, ~1 min
python3 examples/kyc_monitoring/run_demo.py tamper   /tmp/kyc   # two forgeries, both rejected
```

`generate --offline` uses a local test timestamp authority instead of FreeTSA (drand is still needed).
Each bundle in `/tmp/kyc/bundles/` can also be checked alone: `OT_TSA_ROOTS=/tmp/kyc/tsa_roots ot verify <bundle>`.

## What happens

1. **The policy is fixed first.** `policy.json` states the task, the two claims, the standard
   (fraud among approved ≤ 1%), the drift tolerance (10 points), the sample sizes, δ and the action
   each alert triggers. It is timestamped before any draw, so no threshold can be tuned afterwards.
2. **Each month is committed.** A Merkle root of all of that month's decisions, with their confirmed
   outcomes, is timestamped and bound to a future drand round. Nothing can be added, removed or
   relabelled afterwards.
3. **Public randomness picks the sample.** 3,000 approved clients for the fraud claim, and 5,000
   applicants from each of month 1 and month M for the drift claim.
4. **The Lean kernel checks every bound** (`ot verify`); what an accepted check means is proved once
   (`ClaimTypes.poolRate`, `RateGap.gap_sound`).
5. **The policy decides.** For each month: `MEETS STANDARD` or `NOT CERTIFIED → model review`;
   `STABLE`, `DRIFT → revalidate` or `UNCLEAR`.

## What each certificate says

| Claim | Certificate | Example sentence |
| --- | --- | --- |
| fraud | `pool-rate` on `approved_M` | "At most 0.37% of the 16,144 approved clients of month 1 were fraudulent; wrong with probability ≤ 10⁻³." |
| drift | `rate-gap` between `applicants_1` and `applicants_M` | "The share of online applicants differs by at most 5.3 points between month 1 and month 2", or, from month 4, a certified fall of at least 15 points |

## What is assumed, and what is not covered

| Assumed | Meaning here |
| --- | --- |
| A5 beacon | the drand round was unpredictable |
| A6 timestamp | FreeTSA's clock and key are honest (for a bank: a qualified timestamp authority) |
| A7 issuer identity | the bank declares every commitment it made to a round |
| A12 commitment binding | the committed items are the checked ones (SHA-256) |
| the outcomes | the confirmed-fraud labels in the log are right; they are committed with the decisions, before the draw |

**Not covered:** clients outside the committed months; next month (each month is certified when it
closes); *why* a rate changed. The drift claim covers one variable (the online share); other
variables need their own claim. A drift variable must have a share strictly between 0% and 100%
in both months: `rate-gap` cannot certify a pool where every or no item is counted (the trivial
bound 1 does not pass its tail check), so a brand-new channel is measured through the share it
takes from an existing one. The data are synthetic; `truth.json` holds the true rates so the
report can show that every certified bound contains them.

**Not private yet:** each bundle contains the sampled records. A private version would hand the
regulator a zero-knowledge receipt instead (`docs/privacy.md`, §3).
