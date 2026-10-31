# Trusted timestamp roots

PEM root certificates of the RFC 3161 timestamp authorities this verifier trusts, one `*.pem` per
authority. `pool-rate` certificates are rejected unless their ordering token chains to one of them.
The directory is empty by default: choosing a timestamp authority is a trust decision for whoever
runs the verifier. `$OT_TSA_ROOTS` replaces this directory (the conformance tests use it for a
local test authority).
