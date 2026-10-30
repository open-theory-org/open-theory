# mcp: OpenTheory for local agents

A stdio [MCP](https://modelcontextprotocol.io) server that lets an agent find open blueprint
targets, check proofs with the Lean kernel and commit them. It runs on your checkout, starts
no network service and pushes nothing.

```bash
uv run interfaces/mcp/server.py        # or: pip install "mcp>=1.10,<2" && python3 interfaces/mcp/server.py
```

Run `lake build` once first: proofs are checked against the built imports.

## Client configuration

Claude Code:

```bash
claude mcp add opentheory -- uv run /path/to/open_theory/interfaces/mcp/server.py
```

Claude Desktop, Cursor and others (`mcpServers` in their JSON config):

```json
{
  "mcpServers": {
    "opentheory": {
      "command": "uv",
      "args": ["run", "/path/to/open_theory/interfaces/mcp/server.py"]
    }
  }
}
```

The server finds `lake` on `PATH`, `~/.elan/bin`, `/opt/homebrew/bin` or `/usr/local/bin`.

## Tools

| Tool | Changes the repo | What it does |
| --- | --- | --- |
| `list_targets` | no | Blueprint nodes not yet verified, with each Lean declaration and whether it still uses `sorry`. Also reports blueprint/Lean disagreements |
| `get_target` | no | LaTeX statement and informal proof, Lean source, and every dependency's statement in LaTeX and Lean |
| `check_proof` | no | Splices a proof into a copy of the file, runs `lake env lean` and `#print axioms` |
| `commit_proof` | new branch only | Re-checks, then commits the proof, `\leanok` and the regenerated `blueprint.json` to `proof/<name>` |
| `audit_repository` | build outputs only | The CI checks: `\lean` names, catalog, `blueprint.json` freshness, `lake build`, axiom audit |
| `verify_certificate` | no | `ot verify` on a certificate bundle |

A target is a blueprint label (`lem:alignment_nonneg`) or a Lean name (`OpenTheory.alignment_nonneg`,
or a unique suffix such as `alignment_nonneg`).

## What a passing check means

A proof is the Lean text after the declaration's `:=`, usually a `by` block. The server keeps the
statement byte for byte and replaces only the body. `check_proof` reports `ok` only if all three hold:

- Lean compiles the file with the proof and reports no errors;
- `#print axioms` on the target lists only `propext`, `Classical.choice` and `Quot.sound`
  (the verifier's `ALLOWED_AXIOMS`), so `sorryAx`, `native_decide` and custom axioms fail;
- the proof contains no `sorry`/`admit` and opens no new command (`theorem`, `axiom`, `attribute`,
  `#exit`, `end`, …), so it cannot change anything but its own declaration.

`commit_proof` builds the commit in a private git index. Your branch, checkout and uncommitted work
stay as they were. It refuses when the Lean file, `content.tex` or `blueprint.json` has
uncommitted changes, so the commit holds only the proof. It adds `\leanok` only when every
`\lean{}` declaration of the node is free of `sorry`. CI then rebuilds everything and reruns the
whole-library axiom audit.

## Layout

- `server.py`: the MCP surface (tool schemas and descriptions), on the official `mcp` SDK.
- `opentheory_mcp/`: the logic, standard library only. It reads the blueprint with
  `blueprint/export_blueprint.py` and verifies certificates with `verifier/core`, so CI, the
  platform feed and agents share one parser. Tested by `tests/regression/test_mcp_server.py`.
