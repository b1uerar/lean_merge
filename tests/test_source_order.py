"""Regressions for moving original commands without printing proof expressions."""

import os
import unittest
from unittest.mock import patch

from lean_merge import MergeError, merge, normalize


def setUpModule():
    environment = patch.dict(os.environ, {"LEAN_TOOL_FAILURE_ARCHIVE": "0"})
    environment.start()
    unittest.addModuleCleanup(environment.stop)


class SourceOrderTests(unittest.TestCase):
    def test_preserves_tactic_only_dependency_and_comments(self):
        helper = "def identity (n : Nat) := n"
        proof = "theorem target (n : Nat) : n = n := by\n  -- keep this tactic\n  change identity n = n\n  rfl"
        result = merge("theorem target (n : Nat) : n = n := sorry\n",
                       helper + "\n\n" + proof + "\n", proof="target")
        self.assertIn(helper, result["source"])
        self.assertIn(proof, result["source"])
        self.assertEqual(result["strategy"], "source")
        self.assertNotIn("LeanMergeAux", result["source"])

    def test_normalize_preserves_notation_and_proof_text(self):
        proof = 'theorem target (n : Nat) : n = n := by change identity n = n; rfl'
        source = ('namespace N\nsection\nlocal notation "identity" => (fun n : Nat => n)\n'
                  + proof + '\nend\nend N\n')
        result = normalize(source, target="N.target")
        self.assertIn(proof, result["content"])
        self.assertIn('local notation "identity"', result["content"])
        self.assertIn("namespace N", result["content"])

    def test_conflict_does_not_fall_back_to_expansion(self):
        with self.assertRaisesRegex(MergeError, "Source name conflict"):
            merge("def f : Nat := 1\ntheorem target : 2 = 2 := sorry\n",
                  "def f : Nat := 2\ntheorem target : 2 = 2 := Eq.refl f\n",
                  target="target", proof="target")

    def test_normalize_private_type_after_removing_unused_private_declaration(self):
        source = ("private def unused : Nat := 1\nprivate opaque T : Type := Nat\n"
                  "theorem target (x : T) : x = x := by rfl\n")
        result = normalize(source, target="target")
        self.assertNotIn("unused", result["content"])
        self.assertIn("private opaque T : Type := Nat", result["content"])
        self.assertIn("theorem target (x : T) : x = x := by rfl", result["content"])
