"""Merkle trees as in RFC 9162 (Certificate Transparency v2), standard library only.

Leaf hash `SHA-256(0x00 ‖ leaf)`, node hash `SHA-256(0x01 ‖ left ‖ right)`. A pool item is
hashed as its canonical JSON (sorted keys, no spaces, UTF-8). The verifier uses
`verify_inclusion`; producers use `levels`, `root` and `inclusion_proof`.
"""
from __future__ import annotations

import hashlib
import json


def canonical(obj) -> bytes:
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode("utf-8")


def leaf_hash(data: bytes) -> bytes:
    return hashlib.sha256(b"\x00" + data).digest()


def node_hash(left: bytes, right: bytes) -> bytes:
    return hashlib.sha256(b"\x01" + left + right).digest()


def verify_inclusion(index: int, size: int, leaf: bytes, proof: list[bytes], root: bytes) -> bool:
    """RFC 9162 §2.1.3.2: does `proof` show that `leaf` (a leaf hash) is at `index` in the tree?"""
    if not 0 <= index < size:
        return False
    fn, sn, r = index, size - 1, leaf
    for p in proof:
        if sn == 0:
            return False
        if fn & 1 or fn == sn:
            r = node_hash(p, r)
            while not fn & 1 and fn != 0:
                fn >>= 1
                sn >>= 1
        else:
            r = node_hash(r, p)
        fn >>= 1
        sn >>= 1
    return sn == 0 and r == root


def levels(leaves: list[bytes]) -> list[list[bytes]]:
    """All levels bottom-up. An unpaired last node moves up unchanged, which gives the RFC 9162
    left-balanced tree."""
    if not leaves:
        raise ValueError("empty tree")
    out = [list(leaves)]
    while len(out[-1]) > 1:
        cur = out[-1]
        nxt = [node_hash(cur[i], cur[i + 1]) for i in range(0, len(cur) - 1, 2)]
        if len(cur) % 2:
            nxt.append(cur[-1])
        out.append(nxt)
    return out


def root(tree: list[list[bytes]]) -> bytes:
    return tree[-1][0]


def inclusion_proof(tree: list[list[bytes]], index: int) -> list[bytes]:
    proof = []
    for level in tree[:-1]:
        sibling = index ^ 1
        if sibling < len(level):
            proof.append(level[sibling])
        index >>= 1
    return proof
