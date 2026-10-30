"""Lean source as text: a declaration index and proof splicing.

Nothing here runs Lean. The index locates declarations so a proof can be spliced in;
whether the result proves anything is decided by the kernel (tools.check_proof).
"""
from __future__ import annotations

import re
import textwrap
from dataclasses import dataclass
from pathlib import Path

DECL = re.compile(
    r"^(?P<indent>[ \t]*)(?:@\[[^\]\n]*\][ \t]*)?"
    r"(?:(?:private|protected|noncomputable|partial|unsafe|nonrec|public)[ \t]+)*"
    r"(?P<kind>theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque|axiom)[ \t]+"
    r"(?P<name>[^\s:({\[⦃]+)",
    re.MULTILINE,
)
SCOPE = re.compile(
    r"^[ \t]*(?:noncomputable[ \t]+)?(namespace|section|end)\b(?:[ \t]+([^\s]+))?", re.MULTILINE
)
# Lines at the declaration's own indentation that still belong to it.
CONTINUATION = re.compile(r"(?:by|:=|\||where|deriving|termination_by|decreasing_by)\b")
TRAILER = re.compile(r"^[ \t]*(?:where|termination_by|decreasing_by)\b", re.MULTILINE)

INCOMPLETE = re.compile(r"\b(sorry|admit)\b")
# A proof is one term or `by` block; anything that opens a new command could change the file
# around the target, so it is refused rather than spliced in.
COMMAND = re.compile(
    r"^[ \t]*(?:@\[|#|(?:(?:private|protected|noncomputable|local|scoped)[ \t]+)*"
    r"(?:axiom|theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque|example|"
    r"namespace|section|end|attribute|variable|universe|import|mutual|notation|infixl?|infixr|"
    r"prefix|postfix|macro|macro_rules|syntax|elab|elab_rules|initialize)\b)",
    re.MULTILINE,
)
OPEN, CLOSE = "([{⟨⦃", ")]}⟩⦄"
SPECIAL = re.compile(r"--|/-|\"|'")
CHAR = re.compile(r"'(?:\\.|[^\\'\n])'")


class SpliceError(ValueError):
    """The proof cannot be placed in the declaration. The message says why."""


@dataclass(frozen=True)
class Decl:
    name: str  # fully qualified
    kind: str
    path: Path
    line: int  # 1-based line of the declaration keyword
    indent: str
    start: int  # offset of the declaration line
    end: int  # offset just past its last non-blank line

    def source(self) -> str:
        return self.path.read_text(encoding="utf-8")[self.start:self.end]


def mask(text: str) -> str:
    """Blank out comments and string/char literals, keeping every offset and newline."""
    out = list(text)

    def blank(a: int, b: int) -> None:
        for k in range(a, min(b, len(text))):
            if out[k] != "\n":
                out[k] = " "

    i = 0
    while m := SPECIAL.search(text, i):
        i, tok = m.start(), m.group()
        if tok == "--":
            j = text.find("\n", i)
            j = len(text) if j < 0 else j
        elif tok == "/-":
            depth, j = 1, i + 2
            while j < len(text) and depth:
                if text.startswith("/-", j):
                    depth, j = depth + 1, j + 2
                elif text.startswith("-/", j):
                    depth, j = depth - 1, j + 2
                else:
                    j += 1
        elif tok == '"':
            j = i + 1
            while j < len(text) and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            j += 1
        else:  # a char literal, unless the quote ends an identifier such as h'
            c = CHAR.match(text, i)
            if not c or (i and (text[i - 1].isalnum() or text[i - 1] in "_'")):
                i += 1
                continue
            j = c.end()
        blank(i, j)
        i = j
    return "".join(out)


def declarations(path: Path, text: str | None = None) -> list[Decl]:
    """Declarations of `path`, or of `text` read as if it were that file."""
    text = path.read_text(encoding="utf-8") if text is None else text
    masked = mask(text)
    events = sorted([(m.start(), 0, m) for m in SCOPE.finditer(masked)]
                    + [(m.start(), 1, m) for m in DECL.finditer(masked)], key=lambda e: e[:2])
    scopes: list[str] = []
    found = []
    for _, is_decl, m in events:
        if not is_decl:
            kind, name = m.groups()
            if kind == "end":
                if scopes:
                    scopes.pop()
            else:
                scopes.append((name or "") if kind == "namespace" else "")
            continue
        raw = m["name"]
        prefix = ".".join(s for s in scopes if s)
        name = raw[len("_root_."):] if raw.startswith("_root_.") else (f"{prefix}.{raw}" if prefix else raw)
        found.append(Decl(name, m["kind"], path, masked.count("\n", 0, m.start()) + 1, m["indent"],
                          m.start(), _decl_end(masked, m.end(), len(m["indent"]))))
    return found


def _decl_end(masked: str, pos: int, indent: int) -> int:
    """End of the last line that belongs to the declaration. Blank and comment-only lines
    (blank once masked) never extend it, so the next docstring stays outside."""
    end = masked.find("\n", pos)
    end = len(masked) if end < 0 else end
    start = end + 1
    while start < len(masked):
        stop = masked.find("\n", start)
        stop = len(masked) if stop < 0 else stop
        line = masked[start:stop]
        body = line.lstrip()
        if body:
            if len(line) - len(body) <= indent and not CONTINUATION.match(body):
                break
            end = stop
        start = stop + 1
    return end


class Index:
    """Declarations under some roots, re-read only when a file changes."""

    def __init__(self, roots: list[Path]):
        self.roots = roots
        self._files: dict[Path, tuple[int, list[Decl]]] = {}

    def all(self) -> dict[str, Decl]:
        names: dict[str, Decl] = {}
        for path in sorted(p for r in self.roots for p in r.rglob("*.lean")):
            stamp = path.stat().st_mtime_ns
            cached = self._files.get(path)
            if cached is None or cached[0] != stamp:
                cached = self._files[path] = (stamp, declarations(path))
            for decl in cached[1]:
                names.setdefault(decl.name, decl)
        return names

    def find(self, name: str) -> Decl | None:
        return self.all().get(name)


def is_complete(source: str) -> bool:
    return INCOMPLETE.search(mask(source)) is None


def splice_proof(text: str, decl: Decl, proof: str) -> str:
    """Replace everything after the top-level `:=` of `decl` with `proof`.

    `proof` is what follows `:=`: a term or a `by` block (a leading `:=` is accepted).
    The statement is kept byte for byte, and so is the rest of the file.
    """
    masked = mask(proof)
    if m := INCOMPLETE.search(masked):
        raise SpliceError(f"the proof uses `{m.group(1)}`")
    if m := COMMAND.search(masked):
        raise SpliceError("the proof must be a single term or `by` block; "
                          f"it starts a new command: {proof[m.start():].splitlines()[0].strip()!r}")
    body = proof.strip()
    if body.startswith(":="):
        body = body[2:].lstrip()
    if not body:
        raise SpliceError("the proof is empty")

    decl_masked = mask(text[decl.start:decl.end])
    assign = top_level_assign(decl_masked)
    if assign is None:
        raise SpliceError(f"`{decl.name}` has no `:=` body (equation-style declarations are not supported)")
    if TRAILER.search(decl_masked, assign):
        raise SpliceError(f"`{decl.name}` has a `where` or termination clause after its proof; edit the file directly")

    header = text[decl.start:decl.start + assign].rstrip()
    first, _, rest = body.partition("\n")
    rendered = first.rstrip()
    if rest.strip():
        rendered += "\n" + textwrap.indent(textwrap.dedent(rest), decl.indent + "  ").rstrip()
    return f"{text[:decl.start]}{header} := {rendered}{text[decl.end:]}"


def top_level_assign(masked: str) -> int | None:
    depth = 0
    for i, ch in enumerate(masked):
        if ch in OPEN:
            depth += 1
        elif ch in CLOSE:
            depth = max(depth - 1, 0)
        elif depth == 0 and masked.startswith(":=", i):
            return i
    return None
