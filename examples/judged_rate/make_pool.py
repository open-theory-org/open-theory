#!/usr/bin/env python3
"""A SYNTHETIC judged traffic log for the judged-rate example (seeded, so the Merkle root is reproducible).

Each pool item is one logged response with the verdict of an AI judge committed next to it:
`{"id", "prompt_sha256", "output", "judge"}` (`judge` is the judge's reference answer; the judge
fails the item when `output ≠ judge`). Gold labels (`gold.json`, one per item) are only read for the
audited sample. The model is wrong on 8% of items. The judge is fooled by 5% of the model's errors
(it agrees with the wrong answer) and raises a false alarm on 1% of correct answers.
"""
import hashlib
import json
import random
import sys
from pathlib import Path


def make(out: Path, size: int = 100_000, error_rate: float = 0.08, fooled: float = 0.05,
         false_alarm: float = 0.01, seed: int = 2027) -> None:
    rng = random.Random(seed)
    out.mkdir(parents=True, exist_ok=True)
    gold = {}
    with (out / "pool.jsonl").open("w", encoding="utf-8") as f:
        for i in range(size):
            a, b = rng.randrange(1000), rng.randrange(1000)
            answer = str(a + b)
            wrong = rng.random() < error_rate
            output = str(a + b + rng.choice([-10, -1, 1, 10])) if wrong else answer
            if wrong:
                judge = output if rng.random() < fooled else answer
            else:
                judge = str(a + b + rng.choice([-100, 100])) if rng.random() < false_alarm else answer
            item = {"id": f"req-{i:06d}", "prompt_sha256": hashlib.sha256(f"{a}+{b}".encode()).hexdigest(),
                    "output": output, "judge": judge}
            f.write(json.dumps(item, separators=(",", ":")) + "\n")
            gold[str(i)] = answer
    (out / "gold.json").write_text(json.dumps(gold, separators=(",", ":")))


if __name__ == "__main__":
    make(Path(sys.argv[1] if len(sys.argv) > 1 else "pool"))
