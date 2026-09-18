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


class MergeTests(unittest.TestCase):
    def check_merge(self, base, donor, **kwargs):
        result = merge(base, donor, **kwargs)
        self.assertTrue(result["verified"])
        self.assertNotIn("sorryAx", result["axioms"])
        return result

    def test_changed_binder_and_theorem_names(self):
        result = self.check_merge(
            "theorem target (n : Nat) : n = n := by sorry\n",
            "theorem solution (m : Nat) : m = m := by rfl\n",
        )
        self.assertEqual(result["target"], "target")
        self.assertEqual(result["proof"], "solution")

    def test_namespace_section_attributes_private_helper(self):
        result = self.check_merge(
            "namespace N\nvariable (n : Nat)\n/-- keep doc -/\n"
            "@[simp] theorem target : n + 0 = n := by sorry\nend N\n"
            "example : 3 + 0 = 3 := N.target 3\n",
            "private theorem helper (m : Nat) : m + 0 = m := by rfl\n"
            "theorem solution (m : Nat) : m + 0 = m := helper m\n",
            target="N.target", proof="solution",
        )
        self.assertIn("/-- keep doc -/\n@[simp] theorem", result["content"])
        self.assertIn("example : 3 + 0 = 3 := N.target 3", result["content"])
        self.assertEqual(len(result["inserted"]), 1)

    def test_universe_binders(self):
        self.check_merge(
            "universe u\ntheorem target {A : Sort u} (a : A) : a = a := sorry\n",
            "universe v\ntheorem proof {B : Sort v} (b : B) : b = b := rfl\n",
        )

    def test_included_section_parameters(self):
        result = self.check_merge(
            "section\nvariable (p : Prop) (h : p)\ninclude h\n"
            "theorem target : p := sorry\ntheorem afterTarget : p := h\nend\n",
            "theorem proof (p : Prop) (h : p) : p := h\n", target="target",
        )
        self.assertIn("include h", result["content"])

    def test_same_definition_reused(self):
        result = self.check_merge(
            "def f (n : Nat) := n + 1\ntheorem target (n : Nat) : f n = n + 1 := sorry\n",
            "def f (m : Nat) := m + 1\ntheorem proof (m : Nat) : f m = m + 1 := rfl\n",
        )
        self.assertIn("f", result["reused"])

    def test_repeated_structure_with_universes_and_projections(self):
        def source(level, binder, theorem):
            return (f"universe {level}\nnamespace N\n"
                    f"structure Box ({binder} : Type {level}) where\n  value : {binder}\n"
                    f"{theorem}\nend N\n")
        result = self.check_merge(
            source("u", "A", "theorem target {A : Type u} (x : Box A) : x.value = x.value := sorry"),
            source("v", "B", "theorem solution {B : Type v} (y : Box B) : y.value = y.value := rfl"),
            proof="N.solution",
        )
        self.assertIn("N.Box", result["reused"])
        self.assertIn("N.Box.value", result["reused"])
        self.assertEqual(result["content"].count("structure Box"), 1)

    def test_repeated_recursive_inductive_with_induction(self):
        shared = ("inductive Count where\n| zero\n| next : Count → Count\n"
                  "def count : Count → Nat\n| .zero => 0\n| .next n => count n + 1\n")
        result = self.check_merge(
            shared + "theorem target (n : Count) : 0 ≤ count n := sorry\n",
            shared + "theorem solution (n : Count) : 0 ≤ count n := by\n"
            "  induction n with\n  | zero => exact Nat.le_refl 0\n"
            "  | next n ih => exact Nat.le_trans ih (Nat.le_succ _)\n",
            proof="solution",
        )
        self.assertIn("Count.rec", result["reused"])
        self.assertEqual(result["content"].count("inductive Count"), 1)

    def test_repeated_private_structure(self):
        shared = "private structure Box where\n  value : Nat\n"
        result = self.check_merge(
            shared + "theorem target (x : Box) : x.value = x.value := sorry\n",
            shared + "theorem solution (x : Box) : x.value = x.value := rfl\n",
            proof="solution",
        )
        self.assertEqual(result["content"].count("private structure Box"), 1)

    def test_repeated_class_and_structure_inheritance(self):
        shared = ("class Flag where\n  flag : Nat\n"
                  "structure Parent where\n  x : Nat\n"
                  "structure Child extends Parent where\n  y : Nat\n")
        result = self.check_merge(
            shared + "theorem target [Flag] (x : Child) : x.x + Flag.flag = x.x + Flag.flag := sorry\n",
            shared + "theorem solution [Flag] (x : Child) : x.x + Flag.flag = x.x + Flag.flag := rfl\n",
            proof="solution",
        )
        self.assertIn("Flag", result["reused"])
        self.assertIn("Parent", result["reused"])
        self.assertIn("Child", result["reused"])

    def test_repeated_mutual_and_nested_inductives(self):
        declarations = [
            ("mutual\ninductive Even where\n| zero\n| next : Odd → Even\n"
             "inductive Odd where\n| next : Even → Odd\nend\n", "Even", ["Even", "Odd"]),
            ("inductive Tree where\n| leaf\n| branch : List Tree → Tree\n", "Tree", ["Tree.rec_1"]),
            ("inductive Vec (A : Type u) : Nat → Type u where\n"
             "| nil : Vec A 0\n| cons : A → Vec A n → Vec A (n + 1)\n", "Vec Nat 2", ["Vec"]),
        ]
        for shared, type_name, reused in declarations:
            with self.subTest(type=type_name):
                result = self.check_merge(
                    shared + f"theorem target (x : {type_name}) : x = x := sorry\n",
                    shared + f"theorem solution (x : {type_name}) : x = x := rfl\n",
                    proof="solution",
                )
                for name in reused:
                    self.assertIn(name, result["reused"])

    def test_conflicting_inductives_rejected(self):
        cases = [
            ("structure Box where\n  value : Nat\n", "structure Box where\n  value : Bool\n", "Box"),
            ("inductive Color where\n| red\n| blue\n", "inductive Color where\n| blue\n| red\n", "Color"),
            ("inductive Color where\n| red\n", "inductive Color where\n| red\n| blue\n", "Color"),
            ("def T := Nat\nstructure Box where\n  value : T\n",
             "def T := Bool\nstructure Box where\n  value : T\n", "Box"),
        ]
        for base, donor, type_name in cases:
            with self.subTest(base=base, donor=donor):
                with self.assertRaisesRegex(MergeError, "Conflicting inductive"):
                    merge(base + f"theorem target (x : {type_name}) : x = x := sorry\n",
                          donor + f"theorem solution (x : {type_name}) : x = x := rfl\n",
                          proof="solution")

    def test_new_structure_dependency(self):
        result = self.check_merge(
            "theorem target : 2 = 2 := sorry\n",
            "structure Box where\n  value : Nat\n"
            "def box : Box := ⟨2⟩\n"
            "theorem solution : 2 = 2 := Eq.refl box.value\n",
            proof="solution",
        )
        self.assertIn("inductive _root_.LeanMergeAux", result["content"])

    def test_new_structure_avoids_future_constructor_name(self):
        result = self.check_merge(
            "namespace N\nsection\nvariable (p : Prop) (h : p)\ninclude h\n"
            "theorem target : p := sorry\nend\nend N\n"
            "def LeanMergeAux0.mk : Nat := 7\n",
            "structure Box (p : Prop) where\n  proof : p\n"
            "theorem solution (p : Prop) (h : p) : p := (Box.mk h).proof\n",
            proof="solution",
        )
        self.assertNotIn("LeanMergeAux0", result["inserted"])
        self.assertIn("def LeanMergeAux0.mk : Nat := 7", result["content"])

    def test_new_parameterized_mutual_and_nested_inductives(self):
        declarations = [
            ("inductive Box (A : Type u) where\n| mk : A → Box A\n", "Box Nat", "Box.mk 2"),
            ("mutual\ninductive Even where\n| zero\n| next : Odd → Even\n"
             "inductive Odd where\n| next : Even → Odd\nend\n", "Even", "Even.zero"),
            ("inductive Tree where\n| leaf\n| branch : List Tree → Tree\n", "Tree", "Tree.branch []"),
            ("inductive Vec (A : Type u) : Nat → Type u where\n"
             "| nil : Vec A 0\n| cons : A → Vec A n → Vec A (n + 1)\n", "Vec Nat 0", "Vec.nil"),
        ]
        for shared, type_name, value in declarations:
            with self.subTest(type=type_name):
                self.check_merge(
                    "theorem target : True := sorry\n",
                    shared + f"def helper (_ : {type_name}) : True := True.intro\n"
                    f"theorem solution : True := helper ({value})\n",
                    proof="solution",
                )

    def test_normalize_local_structure_then_merge(self):
        normalized = normalize(
            "structure Box where\n  value : Nat\n"
            "theorem target (x : Box) : x.value = x.value := sorry\n"
        )
        self.check_merge(
            normalized["content"],
            "structure Box where\n  value : Nat\n"
            "theorem solution (x : Box) : x.value = x.value := rfl\n",
            proof="solution",
        )

    def test_normalize_inductive_with_generated_dependencies(self):
        result = normalize(
            "structure Box where\n  value : Nat\n"
            "theorem target (a b : Nat) (h : Box.mk a = Box.mk b) : a = b := by cases h; rfl\n"
        )
        self.assertTrue(result["verified"])
        self.assertEqual(result["targets"], ["target"])

    def test_conflicting_definitions_not_conflated(self):
        with self.assertRaisesRegex(MergeError, "Type mismatch"):
            merge(
                "def f : Nat := 1\ntheorem target : f = 2 := sorry\n",
                "def f : Nat := 2\ntheorem proof : f = 2 := rfl\n",
            )

    def test_helper_name_conflict_and_future_name(self):
        result = self.check_merge(
            "def helper : Nat := 1\ntheorem target : 2 = 2 := sorry\n"
            "def LeanMergeAux0 : Nat := 7\n",
            "def helper : Nat := 2\ntheorem proof : 2 = 2 := Eq.refl helper\n",
        )
        self.assertNotIn("LeanMergeAux0", result["inserted"])
        self.assertTrue(result["inserted"])
        self.assertIn("def helper : Nat := 1", result["content"])

    def test_reuse_complete_base_proof_for_donor_placeholder(self):
        result = self.check_merge(
            "theorem helper : 1 = 1 := rfl\ntheorem target : 1 = 1 := sorry\n",
            "theorem helper : 1 = 1 := sorry\ntheorem proof : 1 = 1 := helper\n",
            target="target", proof="proof",
        )
        self.assertIn("helper", result["reused"])

    def test_indirect_sorry_rejected(self):
        with self.assertRaisesRegex(MergeError, "sorryAx|unfinished"):
            merge("theorem target : True := sorry\n",
                  "theorem helper : True := sorry\ntheorem proof : True := helper\n",
                  proof="proof")

    def test_axiom_rejected(self):
        with self.assertRaisesRegex(MergeError, "axiom"):
            merge("theorem target : False := sorry\n",
                  "axiom cheat : False\ntheorem proof : False := cheat\n")

    def test_false_proof_rejected(self):
        with self.assertRaisesRegex(MergeError, "elaboration failed"):
            merge("theorem target : False := sorry\n", "theorem proof : False := by rfl\n")

    def test_complete_target_rejected(self):
        with self.assertRaisesRegex(MergeError, "already has a complete proof"):
            merge("theorem target : True := True.intro\n",
                  "theorem proof : True := True.intro\n", target="target")

    def test_ambiguous_candidate(self):
        with self.assertRaisesRegex(MergeError, "Multiple matching proofs"):
            merge("theorem target : True := sorry\n",
                  "theorem a : True := True.intro\ntheorem b : True := True.intro\n")

    def test_same_name_preferred(self):
        result = self.check_merge("theorem target : True := sorry\n",
                                 "theorem a : True := True.intro\n"
                                 "theorem target : True := a\n")
        self.assertEqual(result["proof"], "target")

    def test_other_sorries_preserved(self):
        result = self.check_merge(
            "-- keep sorry in comment\ntheorem other : False := sorry\n"
            "theorem target : True := sorry\n", "theorem proof : True := True.intro\n",
            target="target",
        )
        self.assertIn("theorem other : False := sorry", result["content"])
        self.assertIn("-- keep sorry in comment", result["content"])

    def test_automatic_target_ignores_downstream_dependencies(self):
        result = self.check_merge(
            (ROOT / "examples/Base.lean").read_text(),
            (ROOT / "examples/Proof.lean").read_text(),
            proof="solution",
        )
        self.assertEqual(result["target"], "Demo.target")
        self.assertIn("theorem downstream", result["content"])

    def test_automatic_target_finds_sorry_in_generated_helper(self):
        result = self.check_merge(
            "theorem target (n : Nat) : n = n := helper n\nwhere\n"
            "  helper (k : Nat) : k = k := by sorry\n"
            "theorem downstream (n : Nat) : n = n := target n\n",
            "theorem solution (n : Nat) : n = n := rfl\n",
        )
        self.assertEqual(result["target"], "target")

    def test_automatic_target_still_rejects_multiple_own_sorries(self):
        with self.assertRaisesRegex(MergeError, "found 2 theorems with their own sorry"):
            merge("theorem first : True := sorry\ntheorem second : True := by sorry\n"
                  "theorem downstream : True := first\n",
                  "theorem solution : True := True.intro\n")

    def test_automatic_target_ignores_sorry_comments_and_definition_dependency(self):
        result = self.check_merge(
            "def unfinished : True := sorry\n"
            "theorem indirect : True := unfinished\n"
            "/-- sorry -/ theorem done : True := True.intro\n"
            "theorem target : True := by sorry\n",
            "theorem solution : True := True.intro\n",
        )
        self.assertEqual(result["target"], "target")

    def test_definitional_equality(self):
        self.check_merge("theorem target : (fun x : Nat => x) 3 = 3 := sorry\n",
                         "theorem proof : 3 = 3 := rfl\n")

    def test_structural_comparison_option(self):
        with self.assertRaisesRegex(MergeError, "Type mismatch"):
            merge("theorem target : (fun x : Nat => x) 3 = 3 := sorry\n",
                  "theorem proof : 3 = 3 := rfl\n", use_def_eq=False)

    def test_import_union(self):
        result = self.check_merge("theorem target : 2 + 2 = 4 := sorry\n",
                                 "import Std\ntheorem proof : 2 + 2 = 4 := by decide\n")
        self.assertEqual(result["content"].count("import Std"), 1)

    def test_import_cannot_change_base_definitions(self):
        with tempfile.TemporaryDirectory() as directory:
            folder = Path(directory)
            module = folder / "ChangingDefault.lean"
            module.write_text("instance (priority := 2000) : Inhabited Nat := ⟨7⟩\n", encoding="utf-8")
            compiled = subprocess.run([
                "lean", "--root", str(folder), "-o", str(module.with_suffix(".olean")), str(module),
            ], capture_output=True, text=True)
            self.assertEqual(compiled.returncode, 0, compiled.stdout + compiled.stderr)
            lean_path = str(folder) + os.pathsep + os.environ.get("LEAN_PATH", "")
            with patch.dict(os.environ, {"LEAN_PATH": lean_path}):
                with self.assertRaisesRegex(MergeError, "Additional imports changed the value"):
                    merge("def value : Nat := default\ntheorem target : value = value := sorry\n",
                          "import ChangingDefault\ntheorem proof : (7 : Nat) = 7 := rfl\n")

    def test_opaque_dependency(self):
        self.check_merge("theorem target : True := sorry\n",
                         "opaque helper : True := True.intro\n"
                         "theorem proof : True := helper\n")

    def test_unicode_and_comments(self):
        result = self.check_merge(
            "-- 中文 sorry\n/- nested /- sorry -/ comment -/\n"
            "theorem «原定理» (α : Nat) : α = α := by sorry\n",
            "theorem «新证明» (β : Nat) : β = β := rfl\n",
        )
        self.assertIn("-- 中文 sorry", result["content"])
        self.assertIn("原定理", result["target"])

    def test_recursive_helper(self):
        self.check_merge("theorem target : 2 = 2 := sorry\n",
                         "def f : Nat → Nat\n| 0 => 0\n| n + 1 => f n + 1\n"
                         "theorem proof : 2 = 2 := Eq.refl (f 2)\n")

    def test_normalize_sections_and_dependencies(self):
        result = normalize("namespace N\nvariable (n : Nat)\ndef f := n + 0\n"
                           "theorem a : f n = n := by simp [f]\n"
                           "theorem b : f n = n := a n\nend N\n")
        self.assertTrue(result["verified"])
        self.assertNotIn("namespace N", result["content"])
        self.assertIn("_root_.N.f", result["content"])
        self.assertIn("_root_.N.a", result["content"])

    def test_normalize_sorry_then_merge(self):
        normalized = normalize("namespace N\ntheorem target : True := sorry\nend N\n")
        self.check_merge(normalized["content"], "theorem proof : True := True.intro\n")

    def test_normalize_private_and_opaque_helpers(self):
        result = normalize("opaque helper : True := True.intro\n"
                           "private theorem aux : True := helper\n"
                           "theorem proof : True := aux\n")
        self.assertTrue(result["verified"])
        self.assertEqual(result["targets"], ["proof"])

    def test_timeout(self):
        with self.assertRaisesRegex(MergeError, "timed out"):
            merge("theorem t : True := sorry", "theorem p : True := True.intro", timeout=0.001)

    def test_cli_failed_merge_leaves_existing_output(self):
        with tempfile.TemporaryDirectory() as directory:
            folder = Path(directory)
            base, donor, output = (folder / x for x in ("Base.lean", "Proof.lean", "Output.lean"))
            base.write_text("theorem target : False := sorry\n")
            donor.write_text("theorem proof : True := True.intro\n")
            output.write_text("keep this content\n")
            proc = subprocess.run([
                sys.executable, str(ROOT / "lean_merge.py"), "merge", str(base), str(donor),
                "-o", str(output), "--force", "--json",
            ], text=True, capture_output=True)
            self.assertEqual(proc.returncode, 1)
            self.assertFalse(json.loads(proc.stdout)["okay"])
            self.assertEqual(output.read_text(), "keep this content\n")

    @unittest.skipUnless(os.environ.get("LEAN_MERGE_TEST_PROJECT"), "optional Lake/Mathlib project")
    def test_mathlib_project(self):
        self.check_merge(
            "import Mathlib\ntheorem target (x : ℝ) : (x + 1)^2 = x^2 + 2*x + 1 := sorry\n",
            "import Mathlib\nlemma proof (y : ℝ) : (y + 1)^2 = y^2 + 2*y + 1 := by ring\n",
            project=os.environ["LEAN_MERGE_TEST_PROJECT"], timeout=240,
        )


if __name__ == "__main__":
    unittest.main()
