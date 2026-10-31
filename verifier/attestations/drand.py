"""drand beacon rounds: pinned chains and BLS signature checks.

The verifier trusts only the chains pinned here, never chain parameters from a bundle. Checking a
signature needs `py_arkworks_bls12381` (native, ~3 ms) or `py_ecc` (pure Python, ~0.4 s); without
either, `verify_round` raises `BackendUnavailable`, which the verifier reports as "could not run",
never as a verdict.
"""
from __future__ import annotations

import hashlib


class BackendUnavailable(RuntimeError):
    pass


# drand mainnet "default" chain (League of Entropy): G2 signatures, chained rounds.
CHAINS = {
    "8990e7a9aaed2ffed73dbd7092123d6f289930540d7651336225dc172e51b2ce": {
        "name": "drand mainnet (default)",
        "public_key": "868f005eb8e6e4ca0a47c8a77ceaa5309a47978a7c71bc5cce96366b5d7a569937c529eeda66c7293784a9402801af31",
        "period": 30,
        "genesis_time": 1595431050,
        "scheme": "pedersen-bls-chained",
    },
}


def round_time(chain: str, round_: int) -> int:
    """Unix time at which `round_` is published."""
    c = CHAINS[chain]
    return c["genesis_time"] + (round_ - 1) * c["period"]


DST = b"BLS_SIG_BLS12381G2_XMD:SHA-256_SSWU_RO_NUL_"


def backend() -> str:
    """The BLS implementation in use: arkworks (native, ~3 ms) or py_ecc (pure Python, ~0.4 s)."""
    try:
        import py_arkworks_bls12381  # noqa: F401
        return "arkworks"
    except ImportError:
        pass
    try:
        import py_ecc  # noqa: F401
        return "py_ecc"
    except ImportError as e:
        raise BackendUnavailable("checking a drand round needs py_arkworks_bls12381 or py_ecc "
                                 "(pip install py_arkworks_bls12381)") from e


def verify_round(chain: str, round_: int, signature: bytes, previous_signature: bytes) -> bool:
    """Is `signature` the drand signature of `round_` on the pinned chain?"""
    c = CHAINS[chain]
    if c["scheme"] != "pedersen-bls-chained":
        raise BackendUnavailable(f"unsupported drand scheme {c['scheme']}")
    message = hashlib.sha256(previous_signature + round_.to_bytes(8, "big")).digest()
    pk = bytes.fromhex(c["public_key"])
    try:  # malformed or off-subgroup points are invalid signatures
        if backend() == "arkworks":
            from py_arkworks_bls12381 import GT, G1Point, G2Point
            sig = G2Point.from_compressed_bytes(signature)
            return GT.pairing(G1Point(), sig) == GT.pairing(G1Point.from_compressed_bytes(pk),
                                                            G2Point.hash_to_curve(message, DST))
        from py_ecc.bls import G2Basic
        return bool(G2Basic.Verify(pk, message, signature))
    except BackendUnavailable:
        raise
    except Exception:
        return False
