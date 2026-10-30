"""OpenTheory MCP server logic, standard library only. server.py exposes it over MCP stdio."""
from __future__ import annotations

import os
import shutil
import signal
import subprocess
import time
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
# The same roots as tests/regression/check_lean_decls.py: where blueprint \lean names live.
LEAN_ROOTS = [ROOT / "formal" / "core", ROOT / "examples"]

# MCP clients often start servers with a minimal PATH; add where elan puts lake.
_FALLBACK = [str(Path.home() / ".elan" / "bin"), "/opt/homebrew/bin", "/usr/local/bin"]
ENV = {**os.environ, "PATH": os.pathsep.join([os.environ.get("PATH", ""), *_FALLBACK])}


@dataclass
class Run:
    ok: bool
    output: str
    seconds: float

    def tail(self, lines: int = 40) -> str:
        return "\n".join(self.output.splitlines()[-lines:])


def run(cmd: list[str], timeout: float, env: dict | None = None) -> Run:
    """Run a command in the repository. stdin is closed: it belongs to the MCP stream.
    On timeout the whole process group goes, so no `lean` outlives its `lake`."""
    start = time.monotonic()
    env = env or ENV
    # Popen may search the server's own PATH, not env's, so resolve the program here.
    program = shutil.which(cmd[0], path=env["PATH"])
    if program is None:
        hint = " (install elan, then run `lake build`)" if cmd[0] == "lake" else ""
        return Run(False, f"`{cmd[0]}` not found{hint}", 0.0)
    proc = subprocess.Popen([program, *cmd[1:]], cwd=ROOT, env=env, stdin=subprocess.DEVNULL,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, start_new_session=True)
    try:
        out, _ = proc.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        os.killpg(proc.pid, signal.SIGKILL)
        out, _ = proc.communicate()
        out = f"{out}\n[timed out after {timeout:.0f}s]"
        return Run(False, out.strip(), time.monotonic() - start)
    return Run(proc.returncode == 0, out.strip(), time.monotonic() - start)
