#!/usr/bin/env python3
"""Benchmark requests for `ot_kernel mlp-exact`: a random quantized ReLU MLP, five honest
certificates and three tampered ones (an output, a weight, an input), each checked here to make
a false claim. The producer is `methods/neural/mlp_exact_certificate.py`.

    python3 gen_mlp.py 784 128 10 > requests.txt
    .lake/build/bin/ot_kernel --time --stdin < requests.txt
"""
from __future__ import annotations

import random
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[3] / "methods" / "neural"))
from mlp_exact_certificate import certificate, random_network, request, tampered  # noqa: E402


def main() -> None:
    dims = [int(v) for v in sys.argv[1:]] or [784, 128, 10]
    rng = random.Random(0)
    layers, x = random_network(dims, 8, rng)
    honest = certificate(layers, x, 8)
    params = sum(dims[l] * dims[l + 1] for l in range(len(dims) - 1))
    print(f"# dims={dims} params={params} slot_bits={honest[0]}", file=sys.stderr)
    for _ in range(5):
        print(request(honest))
    for t in tampered(layers, x, 8, rng):
        print(request(t))


if __name__ == "__main__":
    main()
