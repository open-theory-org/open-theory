#!/usr/bin/env python3
"""SYNTHETIC credit decisions for the rate-gap example (seeded, so the Merkle roots are reproducible).

Two committed pools, one per group: `pool_a.jsonl`, the protected group (30,000 applications, about
55% approved), and `pool_b.jsonl`, the reference group (40,000 applications, about 60% approved).
Each item is one logged decision: `{"id", "applicant_sha256", "output": "approve" | "decline"}`.
The group is the pool (A10). The four-fifths rule asks whether rate_A ≥ 0.8 · rate_B.
"""
import hashlib
import json
import random
import sys
from pathlib import Path


def pool(path: Path, size: int, rate: float, tag: str, rng: random.Random) -> None:
    with path.open("w", encoding="utf-8") as f:
        for i in range(size):
            item = {"id": f"{tag}-{i:06d}",
                    "applicant_sha256": hashlib.sha256(f"{tag}{i}{rng.random()}".encode()).hexdigest(),
                    "output": "approve" if rng.random() < rate else "decline"}
            f.write(json.dumps(item, separators=(",", ":")) + "\n")


def make(out: Path, seed: int = 2028) -> None:
    rng = random.Random(seed)
    out.mkdir(parents=True, exist_ok=True)
    pool(out / "pool_a.jsonl", 30_000, 0.55, "A", rng)
    pool(out / "pool_b.jsonl", 40_000, 0.60, "B", rng)


if __name__ == "__main__":
    make(Path(sys.argv[1] if len(sys.argv) > 1 else "pools"))
