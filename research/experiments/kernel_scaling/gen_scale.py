#!/usr/bin/env python3
"""Scaling sweep: packed probe for 784-h-10 nets. Usage: gen_scale.py OUT_DIR H [H ...]"""
import random, sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
import gen_packed as g
from pacbayes_mlp_certificate import scores, argmax_first

def main(out, hs):
    out = Path(out)
    for h in hs:
        g.ARCH = dict(inputs=784, hidden=h, classes=10, hidden_bias_scale=256, output_bias_scale=512)
        rng = random.Random(20261024 + h)
        d, c = 784, 10
        p = d * h + h + h * c + c
        codes = [rng.randrange(4) for _ in range(p)]
        model = dict(g.ARCH, codes=codes)
        rows = [([rng.randrange(256) if rng.random() < 0.2 else 0 for _ in range(d)], rng.randrange(10)) for _ in range(5)]
        padded = codes + [0] * (-len(codes) % g.CHUNK)
        chunks = [g.pack(padded[i:i + g.CHUNK], 4) for i in range(0, len(padded), g.CHUNK)]
        head = g.header(chunks, p)
        for k in (1, 5):
            errs = sum(argmax_first(scores(model, x)) != y for x, y in rows[:k])
            body = ",\n  ".join(f"(image {g.pack(x, 256)}, {y})" for x, y in rows[:k])
            (out / f"scale_h{h}_r{k}.lean").write_text(head + f"""
def batch : List Observation := [
  {body}]

theorem batch_errors : errorCount arch network batch = {errs} := by
  rw [network, errorCount_codeOfList _ _ networkCodes_length]
  decide +kernel

end MnistProbe
""")
        print(h, p)

main(sys.argv[1], [int(x) for x in sys.argv[2:]])
