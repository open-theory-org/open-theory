#!/usr/bin/env bash
# Conformance for `heldout-error`: the honest certificate must be accepted, every forgery rejected.
# About 2 minutes (five kernel runs in parallel). Requires `lake build`.
set -u
cd "$(dirname "$0")/../.."
C=examples/certified_accuracy/certify.py
LOG=examples/certified_accuracy/out
mkdir -p "$LOG"
declare -a NAMES=(honest fake_error_count fake_tight_bound tampered_test_data tampered_model)
declare -a ARGS=("" "--claim-errors 10" "--claim-bound 0.03" "--tamper-label 5" "--tamper-weight 100")
declare -a EXPECT=(0 1 1 1 1)
pids=()
for i in "${!NAMES[@]}"; do
  python3 $C ${ARGS[$i]} > "$LOG/$((i + 1))_${NAMES[$i]}.txt" 2>&1 &
  pids+=($!)
done
fail=0
for i in "${!NAMES[@]}"; do
  wait "${pids[$i]}"; got=$?
  [ "$got" -ne 0 ] && got=1
  if [ "$got" -eq "${EXPECT[$i]}" ]; then verdict=ok; else verdict=FAIL; fail=1; fi
  want=$([ "${EXPECT[$i]}" -eq 0 ] && echo accept || echo reject)
  echo "[$verdict] ${NAMES[$i]}: expected $want"
done
exit $fail
