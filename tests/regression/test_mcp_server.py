"""The MCP server finds what the blueprint names, splices proofs without touching statements,
and refuses proofs that could change anything else. (No Lean and no MCP SDK needed.)"""
import re
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "interfaces/mcp"))
from opentheory_mcp import blueprint, tools  # noqa: E402
from opentheory_mcp.lean_source import SpliceError, declarations, is_complete, splice_proof  # noqa: E402

SOURCE = """import Mathlib

/-! A module docstring that mentions sorry. -/

namespace OpenTheory

theorem easy (n : ℕ) (h : n = n := rfl) :
    n + 0 = n := by
  -- sorry, not yet
  sorry

/-- The next declaration. -/
def double (n : ℕ) : ℕ := 2 * n

namespace Inner

lemma pattern : ℕ → ℕ
  | 0 => 0
  | n + 1 => n

end Inner

end OpenTheory
"""
FAKE = Path("Fake.lean")


def decl(name):
    return next(d for d in declarations(FAKE, SOURCE) if d.name == name)


class Index(unittest.TestCase):
    def test_every_blueprint_name_is_found(self):
        text = (ROOT / "blueprint/src/content.tex").read_text(encoding="utf-8")
        names = {n.strip() for b in re.findall(r"\\lean\{([^}]+)\}", text) for n in b.split(",") if n.strip()}
        self.assertEqual(sorted(names - tools.INDEX.all().keys()), [])

    def test_namespaces_spans_and_comments(self):
        self.assertEqual([d.name for d in declarations(FAKE, SOURCE)],
                         ["OpenTheory.easy", "OpenTheory.double", "OpenTheory.Inner.pattern"])
        easy = decl("OpenTheory.easy")
        self.assertTrue(SOURCE[easy.start:easy.end].endswith("  sorry"))
        self.assertFalse(is_complete(SOURCE[easy.start:easy.end]))
        self.assertTrue(is_complete("theorem t : True := by\n  -- sorry\n  /- admit /- nested -/ -/ trivial"))
        self.assertTrue(is_complete('def s : String := "sorry"'))


class Splice(unittest.TestCase):
    def test_statement_and_rest_of_file_are_kept(self):
        easy = decl("OpenTheory.easy")
        out = splice_proof(SOURCE, easy, "by\n    simp\n    rfl\n")
        header = "theorem easy (n : ℕ) (h : n = n := rfl) :\n    n + 0 = n"
        self.assertIn(header + " := by\n  simp\n  rfl\n\n/-- The next declaration. -/", out)
        self.assertEqual(out[:easy.start], SOURCE[:easy.start])
        self.assertTrue(out.endswith(SOURCE[easy.end:]))
        self.assertEqual(splice_proof(SOURCE, easy, ":= Nat.add_zero n"),
                         splice_proof(SOURCE, easy, "Nat.add_zero n"))

    def test_refusals(self):
        easy = decl("OpenTheory.easy")
        for proof in ["by sorry", "by\n  admit", "", "by simp\n\naxiom cheat : False", "by simp\n#exit",
                      "by simp\nend OpenTheory", "by simp\n@[simp] theorem t : True := trivial"]:
            with self.subTest(proof=proof), self.assertRaises(SpliceError):
                splice_proof(SOURCE, easy, proof)
        with self.assertRaises(SpliceError):
            splice_proof(SOURCE, decl("OpenTheory.Inner.pattern"), "fun n => n")


class Blueprint(unittest.TestCase):
    TEX = ("\\begin{lemma}[T]\\label{lem:t}\n\\lean{OpenTheory.t}\n\\uses{def:x}\nStatement.\n\\end{lemma}\n"
           "\\begin{proof}\nSketch.\n\\end{proof}\n")

    def test_mark_proved_is_massot_and_idempotent(self):
        tex, notes = blueprint.mark_proved(self.TEX, "lem:t")
        self.assertEqual(notes, [])
        self.assertIn("\\lean{OpenTheory.t}\n\\leanok\n\\uses", tex)
        self.assertIn("\\begin{proof}\n\\leanok\nSketch.", tex)
        self.assertEqual(blueprint.mark_proved(tex, "lem:t")[0], tex)

    def test_missing_proof_environment_is_reported(self):
        tex, notes = blueprint.mark_proved(self.TEX.split("\\begin{proof}")[0], "lem:t")
        self.assertIn("no proof environment", notes[0])

    def test_blueprint_and_lean_agree(self):
        report = tools.list_targets(include_verified=True)
        self.assertEqual(report["inconsistencies"], [])
        self.assertEqual(sum(report["counts"].values()), len(blueprint.nodes()))


if __name__ == "__main__":
    unittest.main()
