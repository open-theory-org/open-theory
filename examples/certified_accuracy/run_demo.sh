#!/usr/bin/env bash
# Unforgeable generalization bound: one honest claim, four forgery attempts.
# Each run takes ~1.5 min (the Lean kernel re-runs the network on 397 examples); all five run in parallel.
cd "$(dirname "$0")/../.."
D=examples/certified_accuracy
mkdir -p $D/out
python3 $D/certify.py                    > $D/out/1_honest.txt &
python3 $D/certify.py --claim-errors 10  > $D/out/2_fake_error_count.txt &
python3 $D/certify.py --claim-bound 0.03 > $D/out/3_fake_tight_bound.txt &
python3 $D/certify.py --tamper-label 5   > $D/out/4_tampered_test_data.txt &
python3 $D/certify.py --tamper-weight 100 > $D/out/5_tampered_model.txt &
wait
for f in $D/out/[1-5]_*.txt; do echo; echo "################ $(basename $f .txt)"; cat $f; done
