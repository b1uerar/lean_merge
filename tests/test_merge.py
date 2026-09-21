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
    # Child CLI processes inherit the same archive setting.
    environment = patch.dict(os.environ, {"LEAN_TOOL_FAILURE_ARCHIVE": "0"})
    environment.start()
    unittest.addModuleCleanup(environment.stop)


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

    def test_local_function_with_unused_proof_parameters(self):
        base = "theorem target (n : Nat) : n = n := by sorry\n"
        for keyword in ["have", "let"]:
            with self.subTest(keyword=keyword):
                donor = f'''theorem solution (n : Nat) : n = n := by
  {keyword} htop : ∀ {{x : Nat}}, x > 0 → x < n → x = x := by
    intro x hxN hxr
    rfl
  rfl
'''
                self.check_merge(base, donor, target="target", proof="solution")
                normalized = normalize(donor, target="solution")
                self.check_merge(base, normalized["content"], target="target", proof="solution")

    def check_shared_expression(self, build):
        base = ("import Lean\nuniverse u\nnamespace N\n"
                "theorem target {A : Type u} (x : A) : x = x := sorry\nend N\n")
        donor = '''import Lean
open Lean Elab Tactic
elab "shared_proof" : tactic => do
  let goal <- getMainGoal
  goal.withContext do
    let p <- goal.getType
    let x := p.getAppArgs[1]!
''' + build + '''
    goal.assign proof
  replaceMainGoal []
universe v
theorem solution {A : Type v} (x : A) : x = x := by shared_proof
'''
        result = self.check_merge(base, donor, target="N.target", proof="solution")
        self.assertLess(len(result["content"].encode()), 100000)
        self.assertTrue(result["inserted"])
        self.assertEqual(set(result["inserted"]), {
            name for command in result["added_commands"] for name in command["names"]})
        self.assertIn('elab "shared_proof"', result["content"])
        self.assertIn("by shared_proof", result["content"])
        self.assertNotIn("LeanMergeAux", result["content"])
        normalized = normalize(donor, target="solution")
        self.assertLess(len(normalized["content"].encode()), 100000)
        self.check_merge(base, normalized["content"], target="N.target", proof="solution")

    def test_shared_proof_with_local_variables_and_universes(self):
        self.check_shared_expression('''    let mut proof <- Meta.mkEqRefl x
    for _ in [:16] do
      proof := mkApp3 (mkConst ``And.left) p p
        (mkApp4 (mkConst ``And.intro) p p proof proof)''')

    def test_shared_data_preserves_reduction(self):
        self.check_shared_expression('''    let mut value := x
    for _ in [:16] do
      let pair <- Meta.mkAppM ``Prod.mk #[value, value]
      value <- Meta.mkAppM ``Prod.fst #[pair]
    let proof <- Meta.mkEqRefl value''')

    def test_shared_proof_with_applied_implicit_lambdas(self):
        for binder in ["implicit", "instImplicit"]:
            with self.subTest(binder=binder):
                self.check_shared_expression('''    let fn <- Meta.withLocalDecl `a .''' + binder + ''' (<- Meta.inferType x) fun a => do
      Meta.mkLambdaFVars #[a] (<- Meta.mkEqRefl a)
    let mut proof := mkApp fn x
    for _ in [:16] do
      proof := mkApp3 (mkConst ``And.left) p p
        (mkApp4 (mkConst ``And.intro) p p proof proof)''')

    def test_included_section_parameters(self):
        result = self.check_merge(
            "section\nvariable (p : Prop) (h : p)\ninclude h\n"
            "theorem target : p := sorry\ntheorem afterTarget : p := h\nend\n",
            "theorem proof (p : Prop) (h : p) : p := h\n", target="target",
        )
        self.assertIn("include h", result["content"])

    def test_scoped_include_preserves_target_binders(self):
        cases = [
            ("variable (A : Type)\ninclude A in\ntheorem target : True := sorry\n",
             "theorem solution (A : Type) : True := True.intro\n"),
            ("namespace N\nsection\nvariable (p : Prop) (h : p) (unused : Nat)\n"
             "include unused\ninclude h in\nomit unused in\n"
             "/-- keep doc -/\ntheorem target : p := sorry\n"
             "theorem sibling : True := True.intro\nend\nend N\n",
             "theorem solution (p : Prop) (h : p) : p := h\n"),
        ]
        for base, donor in cases:
            for newline in ("\n", "\r\n"):
                with self.subTest(base=base, newline=newline):
                    result = self.check_merge(base.replace("\n", newline), donor,
                                              target="target", proof="solution")
                    self.assertIn("True.intro" if "True" in donor else ":= h", result["content"])
                    if newline == "\r\n":
                        self.assertNotIn("\n", result["content"].replace("\r\n", ""))

    def test_scoped_include_in_mutual_preserves_siblings(self):
        sibling = "theorem sibling : True := True.intro\n"
        result = self.check_merge(
            "section\nvariable (p : Prop) (h : p)\ninclude h in\nmutual\n" +
            sibling + "theorem target : p := sorry\nend\n"
            "theorem afterTarget : True := True.intro\nend\n",
            "theorem solution (p : Prop) (h : p) : p := h\n",
            target="target", proof="solution")
        self.assertIn(sibling, result["content"])

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

    def test_private_opaque_dependency_reused(self):
        shared = "namespace N\nprivate opaque T : Type := Nat\n"
        result = self.check_merge(
            shared + "theorem target (x : T) : x = x := sorry\nend N\n",
            shared + "theorem solution (x : T) : x = x := rfl\nend N\n",
            proof="N.solution")
        self.assertTrue(any(name.endswith(".N.T") for name in result["reused"]))
        self.assertEqual(result["inserted"], [])

    def test_private_complete_proof_reused_for_placeholder(self):
        result = self.check_merge(
            "namespace N\nprivate theorem helper : True := True.intro\n"
            "theorem target : True := sorry\nend N\n",
            "namespace N\nprivate theorem helper : True := sorry\n"
            "theorem solution : True := helper\nend N\n",
            target="N.target", proof="N.solution")
        self.assertTrue(any(name.endswith(".N.helper") for name in result["reused"]))
        self.assertEqual(result["inserted"], [])

    def test_private_conflicting_dependency_not_reused(self):
        with self.assertRaisesRegex(MergeError, "Type mismatch|Source name conflict"):
            merge("private opaque T : Type := Nat\ntheorem target (x : T) : x = x := sorry\n",
                  "private opaque T : Type := Bool\ntheorem solution (x : T) : x = x := rfl\n",
                  proof="solution")
        for helper in ("private theorem helper : True := sorry\n",
                       "private theorem helper : (1 : Nat) = 1 := rfl\n",
                       "namespace Other\nprivate theorem helper : True := True.intro\nend Other\n"):
            with self.subTest(helper=helper), self.assertRaisesRegex(MergeError, "sorryAx|Source name conflict"):
                merge(helper + "theorem target : True := sorry\n",
                      "private theorem helper : True := sorry\ntheorem solution : True := helper\n",
                      target="target", proof="solution")

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
                with self.assertRaisesRegex(MergeError, "Type mismatch|Source name conflict"):
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
        self.assertIn("structure Box where\n  value : Nat", result["content"])
        self.assertIn("Eq.refl box.value", result["content"])

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
        with self.assertRaisesRegex(MergeError, "Type mismatch|Source name conflict"):
            merge(
                "def f : Nat := 1\ntheorem target : f = 2 := sorry\n",
                "def f : Nat := 2\ntheorem proof : f = 2 := rfl\n",
            )

    def test_helper_name_conflict_and_future_name(self):
        with self.assertRaisesRegex(MergeError, "Source name conflict: helper"):
            merge("def helper : Nat := 1\ntheorem target : 2 = 2 := sorry\n",
                  "def helper : Nat := 2\ntheorem proof : 2 = 2 := Eq.refl helper\n")


    def test_reuse_complete_base_proof_for_donor_placeholder(self):
        result = self.check_merge(
            "theorem helper : 1 = 1 := rfl\ntheorem target : 1 = 1 := sorry\n",
            "theorem helper : 1 = 1 := sorry\ntheorem proof : 1 = 1 := helper\n",
            target="target", proof="proof",
        )
        self.assertIn("helper", result["reused"])

    def test_reused_definition_discards_unreachable_dependencies(self):
        for declaration, type_name in [("theorem hidden : True := sorry", "True"),
                                       ("noncomputable def hidden : Nat := sorry", "Nat")]:
            with self.subTest(declaration=declaration):
                result = self.check_merge(
                    "def d : Nat := 1\ntheorem target : d = d := sorry\n",
                    declaration + "\n" +
                    f"def d : Nat := (fun (_ : {type_name}) => 1) hidden\n"
                    "theorem target : d = d := rfl\n",
                    target="target", proof="target",
                )
                self.assertIn("d", result["reused"])
                self.assertEqual(result["inserted"], [])
                self.assertEqual(result["added_commands"], [])
                self.assertNotIn("sorryAx", result["content"])
                self.assertNotIn("LeanMergeAux", result["content"])

    def test_reused_definition_keeps_shared_dependencies(self):
        result = self.check_merge(
            "def d : Nat := 1\ntheorem target : d = d := sorry\n",
            "theorem helper : True := True.intro\n"
            "theorem wrapper : True := helper\n"
            "def d : Nat := (fun (_ : True) => 1) wrapper\n"
            "theorem target : d = d := (fun (_ : True) => rfl) wrapper\n",
            target="target", proof="target",
        )
        self.assertIn("d", result["reused"])
        self.assertEqual(len(result["inserted"]), 2)
        recorded = {name for command in result["added_commands"] for name in command["names"]}
        self.assertEqual(set(result["inserted"]), recorded)

    def test_merge_retains_dependencies_of_unused_constructors(self):
        result = self.check_merge(
            "theorem target : True := sorry\n",
            "def Field := Nat\nmutual\n"
            "inductive Left where\n| next : Right -> Left\n"
            "inductive Right where\n| empty\n| field : Field -> Right\nend\n"
            "theorem target : True := (fun (_ : Right) => True.intro) Right.empty\n",
            target="target", proof="target",
        )
        self.assertIn("Left", result["inserted"])
        self.assertIn("Right", result["inserted"])
        self.assertIn("def Field := Nat", result["content"])
        recorded = {name for command in result["added_commands"] for name in command["names"]}
        self.assertTrue(any(name.endswith(".field") for name in recorded))
        self.assertTrue(set(result["inserted"]).issubset(recorded))

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

    def test_private_same_name_preferred_and_explicit_proof_respected(self):
        base = "namespace N\nprivate theorem target : True := sorry\nend N\n"
        donor = ("namespace N\nprivate theorem other : True := True.intro\n"
                 "private theorem target : True := True.intro\nend N\n"
                 "namespace Other\nprivate theorem target : True := True.intro\nend Other\n")
        for proof, expected in ((None, ".N.target"), ("N.other", ".N.other")):
            with self.subTest(proof=proof):
                result = self.check_merge(base, donor, target="N.target", proof=proof)
                self.assertTrue(result["proof"].endswith(expected))

    def test_private_same_name_in_other_namespaces_stays_ambiguous(self):
        with self.assertRaisesRegex(MergeError, "Multiple matching proofs"):
            merge("namespace Goal\nprivate theorem target : True := sorry\nend Goal\n",
                  "namespace A\nprivate theorem target : True := True.intro\nend A\n"
                  "namespace B\nprivate theorem target : True := True.intro\nend B\n")

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

    def test_mutual_merge_locates_target_with_matching_short_names(self):
        first = "theorem target : True := True.intro\n"
        result = self.check_merge(
            "namespace N\nmutual\n" + first +
            "theorem Sub.target : True := sorry\nend\nend N\n",
            "theorem solution : True := True.intro\n",
            target="N.Sub.target", proof="solution")
        self.assertEqual(result["target"], "N.Sub.target")
        self.assertIn(first, result["content"])
        self.assertIn("theorem _root_.N.Sub.target", result["content"])

    def test_mutual_reuses_complete_sibling_for_placeholder(self):
        for modifier in ("", "private "):
            with self.subTest(modifier=modifier):
                helper = modifier + "theorem helper : True := True.intro\n"
                result = self.check_merge(
                    "namespace N\nmutual\n" + helper +
                    "theorem target : True := sorry\nend\nend N\n",
                    "namespace N\n" + modifier + "theorem helper : True := sorry\n"
                    "theorem solution : True := helper\nend N\n",
                    target="N.target", proof="N.solution")
                self.assertTrue(any(name.endswith("N.helper") for name in result["reused"]))
                self.assertEqual(result["inserted"], [])
                self.assertEqual(result["added_commands"], [])
                self.assertIn(helper, result["content"])

    def test_mutual_reused_sibling_available_to_inserted_helpers(self):
        result = self.check_merge(
            "mutual\ntheorem helper : True := aux where\n  aux : True := True.intro\n"
            "theorem target : True := sorry\nend\n",
            "theorem helper : True := sorry\n"
            "def support : True := helper\ntheorem solution : True := support\n",
            target="target", proof="solution")
        self.assertIn("helper", result["reused"])
        self.assertTrue(result["inserted"])

    def test_mutual_reuse_preserves_existing_automatic_proof_selection(self):
        result = self.check_merge(
            "mutual\ntheorem helper : True := True.intro\n"
            "theorem target : True := sorry\nend\n",
            "theorem helper : True := sorry\ntheorem solution : True := True.intro\n",
            target="target")
        self.assertEqual(result["proof"], "solution")
        self.assertEqual(result["inserted"], [])

    def test_explicit_proof_must_contain_a_complete_source_proof(self):
        with self.assertRaisesRegex(MergeError, "sorryAx"):
            merge(
                "section\nvariable (p : Prop) (h : p)\ninclude h in\nmutual\n"
                "theorem helper : p := h\ntheorem target : p := sorry\nend\nend\n",
                "theorem helper (p : Prop) (h : p) : p := sorry\n",
                target="target", proof="helper")

    def test_mutual_does_not_reuse_target_dependent_proofs(self):
        for base in (
            "mutual\ntheorem target : True := sorry\ntheorem helper : True := target\nend\n",
            "mutual\ntheorem helper : True := target\ntheorem target : True := sorry\nend\n",
        ):
            with self.subTest(base=base), self.assertRaisesRegex(MergeError, "Source name conflict|sorryAx"):
                merge(base, "theorem helper : True := sorry\ntheorem solution : True := helper\n",
                      target="target", proof="solution")

    def test_moves_later_complete_dependency_before_target(self):
        helper = "theorem helper : True := True.intro"
        result = self.check_merge("theorem target : True := sorry\n" + helper + "\n",
                                  "theorem helper : True := sorry\n"
                                  "theorem target : True := by exact helper\n",
                                  target="target", proof="target")
        self.assertEqual(result["content"].count(helper), 1)
        self.assertLess(result["content"].index(helper), result["content"].index("theorem target"))
        self.assertIn("by exact helper", result["content"])
        self.assertEqual(result["inserted"], [])


    def test_mutual_automatic_target_follows_only_its_own_where_helper(self):
        downstream = "theorem downstream (n : Nat) : n = n := target n\n"
        result = self.check_merge(
            "namespace N\nmutual\ntheorem first : True := True.intro\n"
            "private theorem target (n : Nat) : n = n := helper n\nwhere\n"
            "  helper (k : Nat) : k = k := by sorry\n" + downstream + "end\nend N\n",
            "theorem solution (n : Nat) : n = n := rfl\n", proof="solution")
        self.assertTrue(result["target"].endswith(".N.target"))
        self.assertIn(downstream, result["content"])
        self.assertNotIn("where", result["content"])

    def test_mutual_automatic_target_rejects_multiple_holes(self):
        with self.assertRaisesRegex(MergeError, "found 2 theorems with their own sorry"):
            merge("mutual\ntheorem first : True := sorry\n"
                  "theorem second : True := sorry\nend\n",
                  "theorem solution : True := True.intro\n", proof="solution")

    def test_mutual_other_declaration_type_still_checked(self):
        with self.assertRaisesRegex(MergeError, "changed the type of sibling"):
            merge("mutual\ntheorem target : True := sorry\n"
                  "theorem sibling (x : helper) : (helper : Type) = helper := rfl\nend\n",
                  "def helper : Type := Nat\n"
                  "theorem solution : True := (fun (_ : helper) => True.intro) (0 : Nat)\n",
                  target="target", proof="solution")

    def test_mutual_preserves_sibling_where_helper_and_section_scope(self):
        sibling = ("  theorem sibling : p := helper where\n    helper : p := h\n"
                   "  theorem forced : True := True.intro\n")
        after = "theorem afterTarget : p := h\n"
        base = ("section\nvariable (p : Prop) (h : p)\ninclude h\nmutual\n" + sibling +
                "  theorem target (unused : Nat) :\n    p := sorry\nend\n" + after + "end\n")
        for newline in ("\n", "\r\n"):
            with self.subTest(newline=newline):
                result = self.check_merge(
                    base.replace("\n", newline),
                    "theorem solution (p : Prop) (h : p) (unused : Nat) : p := h\n",
                    target="target", proof="solution")
                self.assertIn(sibling.replace("\n", newline), result["content"])
                self.assertIn(after.replace("\n", newline), result["content"])
                self.assertNotIn("\r\r\n", result["content"])
                if newline == "\r\n":
                    self.assertNotIn("\n", result["content"].replace("\r\n", ""))
                recorded = {name for command in result["added_commands"] for name in command["names"]}
                self.assertTrue(set(result["inserted"]).issubset(recorded))

    def test_mutual_recursive_theorems(self):
        second = ("theorem second (n : Nat) : n = n := by\n"
                  "  cases n with\n  | zero => rfl\n"
                  "  | succ n => exact congrArg Nat.succ (first n)\n")
        result = self.check_merge(
            "mutual\ntheorem first (n : Nat) : n = n := by\n"
            "  cases n with\n  | zero => sorry\n"
            "  | succ n => exact congrArg Nat.succ (second n)\n" + second + "end\n",
            "theorem solution (n : Nat) : n = n := rfl\n",
            target="first", proof="solution")
        self.assertIn(second, result["content"])

    def test_mutual_rejects_changed_sibling_universe_parameters(self):
        # Moving the target out changes Lean's shared mutual universe parameters.
        with self.assertRaisesRegex(MergeError, "changed the type of sibling"):
            merge(
                "universe u\nsection\nvariable {A : Sort u} (a : A)\ninclude a\nmutual\n"
                "theorem sibling : True := True.intro\n"
                "theorem target (x : B) : x = x := sorry\nend\nend\n",
                "theorem solution {A : Sort u} (a : A) {B : Sort v} (x : B) : x = x := rfl\n",
                target="target", proof="solution")

    def test_normalize_mutual_keeps_all_declared_theorems(self):
        result = normalize(
            "namespace N\nmutual\ntheorem first : True := True.intro\n"
            "theorem Sub.first : True := helper where\n  helper : True := True.intro\n"
            "end\nend N\n")
        self.assertTrue(result["verified"])
        self.assertEqual(set(result["targets"]), {"N.first", "N.Sub.first"})
        self.assertIn("theorem first", result["content"])
        self.assertIn("theorem Sub.first", result["content"])

    def test_definitional_equality(self):
        self.check_merge("theorem target : (fun x : Nat => x) 3 = 3 := sorry\n",
                         "theorem proof : 3 = 3 := rfl\n")

    def test_structural_comparison_option(self):
        with self.assertRaisesRegex(MergeError, "Type mismatch|Source name conflict"):
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

    def test_import_cannot_make_completed_theorem_depend_on_untrusted_axioms(self):
        for imported_proof in ("sorry", "untrusted"):
            with self.subTest(proof=imported_proof), tempfile.TemporaryDirectory() as directory:
                folder = Path(directory)
                module = folder / "ChangingProof.lean"
                module.write_text(
                    "axiom untrusted : True\n"
                    "instance (priority := 2000) : Inhabited True := "
                    f"{{ default := {imported_proof} }}\n", encoding="utf-8")
                compiled = subprocess.run([
                    "lean", "--root", str(folder), "-o", str(module.with_suffix(".olean")), str(module),
                ], capture_output=True, text=True)
                self.assertEqual(compiled.returncode, 0, compiled.stdout + compiled.stderr)
                lean_path = str(folder) + os.pathsep + os.environ.get("LEAN_PATH", "")
                with patch.dict(os.environ, {"LEAN_PATH": lean_path}):
                    base = ("axiom baseUntrusted : True\n"
                            "theorem existingComplete : True := True.intro\n"
                            "theorem existingIncomplete : True := sorry\n"
                            "theorem existingUntrusted : True := baseUntrusted\n"
                            "instance : Inhabited True := { default := True.intro }\n"
                            "theorem sibling : True := default\n"
                            "theorem target : True := sorry\n")
                    donor = "import ChangingProof\ntheorem solution : True := True.intro\n"
                    with self.assertRaisesRegex(MergeError, "introduced unsupported axioms in sibling"):
                        merge(base, donor, target="target", proof="solution")
                    result = self.check_merge(
                        base.replace("sibling : True := default", "sibling : True := sorry"),
                        donor, target="target", proof="solution")
                    self.assertIn("theorem sibling : True := sorry", result["content"])

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
        self.assertIn("namespace N", result["content"])
        self.assertIn("def f := n + 0", result["content"])
        self.assertIn("by simp [f]", result["content"])

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

    def test_helper_cannot_change_unrelated_declaration_type(self):
        with self.assertRaisesRegex(MergeError, "changed the type of sibling"):
            merge("theorem target : True := sorry\n"
                  "theorem sibling (x : helper) : x = x := rfl\n",
                  "def helper : Type := Nat\n"
                  "theorem target : True := (fun (_ : helper) => True.intro) (0 : Nat)\n",
                  target="target", proof="target")

    def test_private_target(self):
        self.check_merge("namespace N\nprivate theorem target : True := sorry\nend N\n",
                         "theorem solution : True := True.intro\n", target="N.target")

    def test_merge_scope_crlf_and_unrelated_source(self):
        before = "namespace N\r\ntheorem target (n : Nat) : n = n := sorry\r\nend N\r\n"
        current = before.replace("end N", "theorem sibling : True := True.intro\r\nend N")
        candidate = before.replace("theorem target (n : Nat) : n = n := sorry",
            'section\r\nlocal notation "identity" => (fun n : Nat => n)\r\n'
            'theorem target (m : Nat) : m = m := by change identity m = m; rfl\r\nend')
        result = merge(current, candidate, target="N.target", proof="N.target")
        self.assertEqual(result["strategy"], "source")
        self.assertIn("local notation", result["source"])
        self.assertIn("theorem sibling : True := True.intro\r\nend N\r\n", result["source"])
        self.assertNotIn("\n", result["source"].replace("\r\n", ""))
        self.assertTrue(any("local notation" in cmd["source"] for cmd in result["added_commands"]))

    def test_merge_conflicting_structure_and_private_target(self):
        with self.assertRaisesRegex(MergeError, "Source name conflict: Box"):
            merge("structure Box where\n  value : Nat\nprivate theorem target : True := sorry\n",
                  "structure Box where\n  value : Bool\ndef box : Box := ⟨true⟩\n"
                  "private theorem target : True := (fun (_ : Box) => True.intro) box\n",
                  target="target", proof="target")


    def test_merge_uses_current_and_needed_dependencies_only(self):
        current = "def value : Nat := 1\ntheorem target : value = 1 := by sorry\n"
        candidate = ("axiom unused : False\ntheorem unfinished : True := sorry\n"
                     "def value : Nat := 2\ntheorem target : (1 : Nat) = 1 := rfl\n")
        result = merge(current, candidate, target="target", proof="target")
        self.assertTrue(result["verified"])
        self.assertIn("def value : Nat := 1\n", result["source"])
        self.assertNotIn("unused", result["source"])
        self.assertNotIn("unfinished", result["source"])

    def test_merge_rejects_wrong_proof_or_unfinished_dependency(self):
        current = "theorem target : True := sorry\n"
        for candidate in ["theorem target : (1 : Nat) = 1 := rfl\n",
                          "axiom invented : True\ntheorem target : True := invented\n",
                          "theorem pending : True := sorry\ntheorem target : True := pending\n"]:
            with self.subTest(candidate=candidate), self.assertRaises(MergeError):
                merge(current, candidate, target="target", proof="target")

    def test_merge_records_all_generated_inductive_names(self):
        result = self.check_merge("theorem target : True := sorry\n",
            "structure Box where\n  value : Nat\n"
            "theorem proof : True := (fun (_ : Box) => True.intro) ⟨1⟩\n")
        recorded = {name for command in result["added_commands"] for name in command["names"]}
        for name in result["inserted"]:
            self.assertIn(name, recorded)
        self.assertTrue(any(name.endswith(".mk") for name in recorded))
        self.assertTrue(any(name.endswith(".rec") for name in recorded))

    def test_merge_crlf_imports_unicode_and_comments(self):
        result = self.check_merge(
            "-- 中文\r\nimport Init\r\nnamespace Δ\r\n"
            "/-- 保留 -/\r\ntheorem target (α : Nat) : α = α := sorry\r\n"
            "-- trailing\r\nend Δ\r\n",
            "import Std\ntheorem proof (β : Nat) : β = β := rfl\n")
        self.assertIn("-- 中文\r\nimport Init", result["source"])
        self.assertIn("import Std\r\n", result["source"])
        self.assertIn("-- trailing\r\nend Δ\r\n", result["source"])
        self.assertNotIn("\n", result["source"].replace("\r\n", ""))

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
