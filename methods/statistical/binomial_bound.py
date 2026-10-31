#!/usr/bin/env python3
"""Exact binomial (Clopper–Pearson) held-out bound: the untrusted search.

Finds the smallest a / scale with delta_den · P(Bin(n, a / scale) ≤ k) ≤ 1. Nothing here
is trusted: the certificate states the integer inequality
`delta_den * tailNumerator n k a scale ≤ scale ^ n`, the Lean kernel re-checks it, and
`OpenTheory.BinomialTail.testSet_bound` turns it into a population bound.
"""


def tail_numerator(n, k, a, b):
    """b^n · P(Bin(n, a/b) ≤ k) for a ≤ b: `OpenTheory.BinomialTail.tailNumerator`, computed by
    Horner's rule like `OpenTheory.FastCheck.tailFast` (linear in k)."""
    if n <= k:
        return b ** n
    q, c, p, s = b - a, 1, 1, 1
    for i in range(k):
        c = c * (n - i) // (i + 1)
        p *= a
        s = s * q + c * p
    return q ** (n - k) * s


def holds(n, k, a, scale, delta_den):
    """The inequality the kernel checks."""
    return delta_den * tail_numerator(n, k, a, scale) <= scale ** n


def tightest_bound(n, k, scale=10_000, delta_den=20):
    """Smallest a with `holds(n, k, a, scale, delta_den)`, by bisection (the tail is monotone in a)."""
    lo, hi = 0, scale
    while lo < hi:
        mid = (lo + hi) // 2
        if holds(n, k, mid, scale, delta_den):
            hi = mid
        else:
            lo = mid + 1
    return lo


if __name__ == "__main__":
    import sys
    n, k = map(int, sys.argv[1:3])
    print(tightest_bound(n, k))
