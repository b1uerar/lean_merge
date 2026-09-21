"""Merging declarations without selecting or completing a sorry."""

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

from lean_merge import MergeError, merge, normalize


ROOT = Path(__file__).resolve().parents[1]


def setUpModule():
    environment = patch.dict(os.environ, {"LEAN_TOOL_FAILURE_ARCHIVE": "0"})
    environment.start()
    unittest.addModuleCleanup(environment.stop)


class DeclarationMergeTests(unittest.TestCase):
    def check_merge(self, base, donor, **options):
        result = merge(base, donor, declarations_only=True, **options)
        self.assertTrue(result["verified"])
        self.assertTrue(result["declarations_only"])
        self.assertIsNone(result["target"])
        self.assertIsNone(result["proof"])
        self.assertEqual(result["source"], result["content"])
        self.assertNotIn("sorryAx", result["axioms"])
        self.assertEqual(set(result["inserted"]), {
            name for command in result["added_commands"] for name in command["names"]})
        return result

    def test_adds_helpers_without_matching_target(self):
        base = "theorem target : False := sorry\n"
        donor = ("def identity (n : Nat) := n\n"
                 "/-- Keep this helper. -/\n"
                 "theorem helper (n : Nat) : identity n = n := by rfl\n")
        result = self.check_merge(base, donor)
        self.assertIn(base, result["content"])
        self.assertIn(donor, result["content"].replace("\n\n", "\n"))
        self.assertIn("identity", result["inserted"])
        self.assertIn("helper", result["inserted"])

    def test_accepts_zero_or_multiple_sorries(self):
        for base in ("", "def baseValue : Nat := 7\n",
                     "theorem first : False := sorry\ntheorem second : True := sorry\n"):
            with self.subTest(base=base):
                result = self.check_merge(base, "def addedValue : Nat := 11\n")
                self.assertIn(base, result["content"])
                self.assertIn("addedValue", result["inserted"])

    def test_reuses_definitions_and_preserves_existing_proofs(self):
        base = ("def value : Nat := 7\n"
                "theorem pending : True := sorry\n"
                "theorem done : True := True.intro\n")
        donor = ("def value : Nat := 7\n"
                 "theorem pending : True := True.intro\n"
                 "theorem done : True := sorry\n"
                 "theorem helper : value = 7 := rfl\n")
        result = self.check_merge(base, donor)
        self.assertIn(base, result["content"])
        self.assertEqual(result["content"].count("def value"), 1)
        self.assertEqual(result["content"].count("theorem pending"), 1)
        self.assertEqual(set(result["reused"]), {"value", "pending", "done"})
        self.assertEqual(result["inserted"], ["helper"])

    def test_matching_placeholder_is_reused_without_filling_it(self):
        base = "theorem target : False := sorry\n"
        result = self.check_merge(base, base + "theorem helper : True := True.intro\n")
        self.assertEqual(result["content"].count(base), 1)
        self.assertIn("target", result["reused"])

    def test_reports_axioms_of_all_added_declarations(self):
        result = self.check_merge(
            "theorem pending : False := sorry\n",
            "theorem sameProp (p q : Prop) (h : p ↔ q) : p = q := propext h\n"
            "theorem reflexive (n : Nat) : n = n := rfl\n")
        self.assertEqual(result["axioms"], ["propext"])

    def test_preserves_scopes_imports_comments_and_crlf(self):
        base = ("import Init\r\nopen Nat\r\nvariable (unused : Nat)\r\ninclude unused\r\n"
                "local notation \"value\" => (1 : Nat)\r\n"
                "def baseValue : Nat := value\r\n"
                "-- 保留\r\ntheorem target : False := sorry\r\n")
        donor = ("import Std\nnamespace Helpers\nsection\n"
                 "local notation \"value\" => (2 : Nat)\n"
                 "@[simp] theorem helper : value = 2 := by rfl\n"
                 "end\nend Helpers\n"
                 "example : Helpers.helper = (rfl : (2 : Nat) = 2) := rfl\n")
        result = self.check_merge(base, donor)
        self.assertIn("import Std\r\n", result["content"])
        self.assertIn("-- 保留\r\ntheorem target : False := sorry", result["content"])
        self.assertIn("@[simp] theorem helper : value = 2 := by rfl", result["content"])
        self.assertNotIn("\n", result["content"].replace("\r\n", ""))

    def test_private_dependency_reused_and_generated_names_recorded(self):
        shared = "namespace N\nprivate opaque T : Type := Nat\n"
        result = self.check_merge(
            shared + "end N\n",
            shared + "theorem helper (x : T) : x = x := rfl\nend N\n"
            "structure Box where\n  value : Nat\n")
        self.assertEqual(result["content"].count("private opaque T"), 1)
        self.assertTrue(any(name.endswith(".N.T") for name in result["reused"]))
        self.assertIn("N.helper", result["inserted"])
        self.assertIn("Box.mk", result["inserted"])
        self.assertIn("Box.rec", result["inserted"])

    def test_conflicting_declarations_rejected(self):
        for base, donor in (
            ("def value : Nat := 1\n", "def value : Nat := 2\n"),
            ("theorem pending : True := sorry\n", "theorem pending : False := sorry\n"),
            ("structure Box where\n  value : Nat\n", "structure Box where\n  value : Bool\n"),
        ):
            with self.subTest(base=base), self.assertRaisesRegex(MergeError, "Source name conflict"):
                merge(base, donor, declarations_only=True)

    def test_new_unfinished_declarations_and_axioms_rejected(self):
        base = "theorem pending : False := sorry\n"
        for donor in ("theorem helper : True := sorry\n", "axiom invented : True\n",
                      base + "theorem helper : False := pending\n"):
            with self.subTest(donor=donor), self.assertRaisesRegex(MergeError, "unsupported axioms|unfinished proofs"):
                merge(base, donor, declarations_only=True)

    def test_import_cannot_change_base_definition(self):
        with tempfile.TemporaryDirectory() as directory:
            folder = Path(directory)
            module = folder / "ChangingDefault.lean"
            module.write_text("instance (priority := 2000) : Inhabited Nat := ⟨7⟩\n")
            compiled = subprocess.run([
                "lean", "--root", str(folder), "-o", str(module.with_suffix(".olean")), str(module),
            ], capture_output=True, text=True)
            self.assertEqual(compiled.returncode, 0, compiled.stdout + compiled.stderr)
            lean_path = str(folder) + os.pathsep + os.environ.get("LEAN_PATH", "")
            with patch.dict(os.environ, {"LEAN_PATH": lean_path}):
                with self.assertRaisesRegex(MergeError, "Additional imports changed the value of value"):
                    merge("def value : Nat := default\n", "import ChangingDefault\n",
                          declarations_only=True)

    def test_rejects_target_options_and_normalize(self):
        for options in ({"target": "target"}, {"proof": "helper"}):
            with self.subTest(options=options), self.assertRaisesRegex(MergeError, "--declarations-only"):
                merge("", "", declarations_only=True, **options)
        with self.assertRaisesRegex(MergeError, "--declarations-only"):
            normalize("", declarations_only=True)

    def test_cli_adds_declarations(self):
        with tempfile.TemporaryDirectory() as directory:
            folder = Path(directory)
            base, donor, output = (folder / name for name in ("Base.lean", "Donor.lean", "Merged.lean"))
            base.write_text("theorem target : False := sorry\n")
            donor.write_text("theorem helper : True := True.intro\n")
            proc = subprocess.run([
                sys.executable, str(ROOT / "lean_merge.py"), "merge", str(base), str(donor),
                "--declarations-only", "-o", str(output), "--json",
            ], text=True, capture_output=True)
            self.assertEqual(proc.returncode, 0, proc.stdout + proc.stderr)
            result = json.loads(proc.stdout)
            self.assertTrue(result["declarations_only"])
            self.assertIsNone(result["target"])
            self.assertEqual(output.read_text(), result["content"])
            self.assertIn(base.read_text(), result["content"])
            self.assertIn(donor.read_text().strip(), result["content"])
