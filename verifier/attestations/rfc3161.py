"""RFC 3161 timestamp tokens, checked with the `openssl ts` command.

A token is accepted only if it chains to a root in the verifier's trust directory
(`verifier/attestations/tsa_roots/`, or `$OT_TSA_ROOTS`), never to a certificate from the bundle.
Without `openssl` or without any trusted root, `check` raises `BackendUnavailable`.
"""
from __future__ import annotations

import os
import re
import subprocess
import tempfile
from datetime import datetime, timezone
from pathlib import Path


class BackendUnavailable(RuntimeError):
    pass


DEFAULT_ROOTS = Path(__file__).resolve().parent / "tsa_roots"


def roots_dir() -> Path:
    return Path(os.environ.get("OT_TSA_ROOTS", DEFAULT_ROOTS))


def check(token: bytes, sha256_hex: str) -> tuple[bool, datetime | None, str]:
    """Verify `token` over the SHA-256 digest `sha256_hex`. Returns (ok, time, detail)."""
    roots = sorted(roots_dir().glob("*.pem"))
    if not roots:
        raise BackendUnavailable(f"no trusted timestamp roots in {roots_dir()}")
    with tempfile.TemporaryDirectory(prefix="ot-tsa-") as tmp:
        tok = Path(tmp) / "token.tsr"
        tok.write_bytes(token)
        bundle = Path(tmp) / "roots.pem"
        bundle.write_bytes(b"".join(p.read_bytes() for p in roots))
        try:
            v = subprocess.run(["openssl", "ts", "-verify", "-digest", sha256_hex, "-sha256",
                                "-in", str(tok), "-CAfile", str(bundle)],
                               capture_output=True, text=True, timeout=60)
            t = subprocess.run(["openssl", "ts", "-reply", "-in", str(tok), "-text"],
                               capture_output=True, text=True, timeout=60)
            p7 = Path(tmp) / "token.p7"
            subprocess.run(["openssl", "ts", "-reply", "-in", str(tok), "-token_out", "-out", str(p7)],
                           capture_output=True, timeout=60)
            certs = subprocess.run(["openssl", "pkcs7", "-inform", "DER", "-in", str(p7), "-print_certs",
                                    "-noout"], capture_output=True, text=True, timeout=60).stdout
        except FileNotFoundError as e:
            raise BackendUnavailable("checking an RFC 3161 token needs the openssl command") from e
    out = (v.stdout + v.stderr).strip()
    if v.returncode != 0 or "Verification: OK" not in out:
        return False, None, out.splitlines()[-1] if out else "invalid token"
    m = re.search(r"Time stamp: (.+)", t.stdout)
    if not m:
        return False, None, "no time in token"
    stamp = " ".join(m.group(1).replace(" GMT", "").split())
    when = None
    for fmt in ("%b %d %H:%M:%S %Y", "%b %d %H:%M:%S.%f %Y"):
        try:
            when = datetime.strptime(stamp, fmt)
            break
        except ValueError:
            pass
    if when is None:
        return False, None, f"unreadable time {stamp!r}"
    signer = re.search(r"subject=\s*(.+)", certs)
    return True, when.replace(tzinfo=timezone.utc), signer.group(1).strip() if signer else "an unnamed authority"
