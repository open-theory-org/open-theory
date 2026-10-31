#!/usr/bin/env python3
"""A SYNTHETIC traffic log for the pool-rate example (seeded, so the Merkle root is reproducible).

Each pool item is one logged response: `{"id", "prompt_sha256", "output"}`. No label is in the
pool: labels are produced only for the sampled items, after sampling (`labels.json` simulates the
labeler with a reference answer for every item). About 1.5% of outputs are wrong.
"""
import hashlib
import json
import random
import sys
from pathlib import Path


def make(out: Path, size: int = 100_000, error_rate: float = 0.015, seed: int = 2026) -> None:
    rng = random.Random(seed)
    out.mkdir(parents=True, exist_ok=True)
    labels = {}
    with (out / "pool.jsonl").open("w", encoding="utf-8") as f:
        for i in range(size):
            a, b = rng.randrange(1000), rng.randrange(1000)
            prompt = f"What is {a} + {b}?"
            answer = str(a + b)
            output = answer if rng.random() >= error_rate else str(a + b + rng.choice([-10, -1, 1, 10]))
            item = {"id": f"req-{i:06d}", "prompt_sha256": hashlib.sha256(prompt.encode()).hexdigest(),
                    "output": output}
            f.write(json.dumps(item, separators=(",", ":")) + "\n")
            labels[str(i)] = answer
    (out / "labels.json").write_text(json.dumps(labels, separators=(",", ":")))


if __name__ == "__main__":
    make(Path(sys.argv[1] if len(sys.argv) > 1 else "pool"))
