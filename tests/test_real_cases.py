"""Real timeout regressions; set LEAN_MERGE_TEST_PROJECT to a built Mathlib project."""

import hashlib
import json
import os
from pathlib import Path
import sys
import tempfile
import time
import unittest

from lean_merge import MergeError, Runner, merge


FIXTURES = Path(__file__).resolve().parent / "fixtures"
MANIFEST = json.loads((FIXTURES / "manifest.json").read_text(encoding="utf-8"))
PERMITTED_AXIOMS = {"propext", "Quot.sound", "Classical.choice"}


class FixtureTests(unittest.TestCase):
    def test_original_inputs(self):
        for name, expected in MANIFEST["files"].items():
            with self.subTest(file=name):
                data = (FIXTURES / name).read_bytes()
                self.assertEqual(len(data), expected["bytes"])
                self.assertEqual(hashlib.sha256(data).hexdigest(), expected["sha256"])


@unittest.skipUnless(os.environ.get("LEAN_MERGE_TEST_PROJECT"),
                     "real cases require LEAN_MERGE_TEST_PROJECT with built Mathlib")
class RealMergeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.project = Path(os.environ["LEAN_MERGE_TEST_PROJECT"]).expanduser().resolve()
        cls.timeout = float(os.environ.get("LEAN_MERGE_TEST_TIMEOUT", "300"))

    def setUp(self):
        artifacts = os.environ.get("LEAN_MERGE_TEST_OUTPUT")
        if artifacts:
            parent = Path(artifacts).expanduser().resolve()
            parent.mkdir(parents=True, exist_ok=True)
            self.work = Path(tempfile.mkdtemp(prefix=self._testMethodName + "-", dir=parent))
            print(f"\nArtifacts: {self.work}", file=sys.stderr, flush=True)
        else:
            temporary = tempfile.TemporaryDirectory(prefix="lean-merge-real-test-")
            self.addCleanup(temporary.cleanup)
            self.work = Path(temporary.name)

    def fixture(self, name):
        data = (FIXTURES / name).read_bytes()
        self.assertEqual(hashlib.sha256(data).hexdigest(), MANIFEST["files"][name]["sha256"])
        return data.decode("utf-8")

    def check_case(self, case_id, *, current=None, previous_targets=()):
        case = MANIFEST["cases"][case_id]
        base = self.fixture(case["base"]) if current is None else current
        donor = self.fixture(case["donor"])
        target = case["target"]
        folder = self.work / case_id
        folder.mkdir()
        (folder / "Base.lean").write_text(base, encoding="utf-8")
        (folder / "Donor.lean").write_text(donor, encoding="utf-8")
        started = time.monotonic()
        try:
            result = merge(base, donor, target=target, proof=target,
                           project=self.project, timeout=self.timeout)
        except MergeError as exc:
            (folder / "error.log").write_text(str(exc), encoding="utf-8")
            raise
        merge_seconds = time.monotonic() - started
        content = result["content"]
        (folder / "Merged.lean").write_text(content, encoding="utf-8")
        metadata = {key: value for key, value in result.items() if key not in {"content", "source"}}
        metadata.update(merge_seconds=merge_seconds, output_bytes=len(content.encode("utf-8")))
        (folder / "result.json").write_text(json.dumps(metadata, indent=2), encoding="utf-8")

        self.assertTrue(result["okay"])
        self.assertTrue(result["verified"])
        self.assertEqual(result["target"], target)
        self.assertEqual(result["source"], content)
        self.assertLessEqual(set(result["axioms"]), PERMITTED_AXIOMS)
        recorded = {name for command in result["added_commands"] for name in command["names"]}
        self.assertTrue(result["inserted"])
        self.assertLessEqual(set(result["inserted"]), recorded)
        limit = case["max_output_bytes"] if current is None else MANIFEST["sequence_max_output_bytes"]
        self.assertLessEqual(metadata["output_bytes"], limit)

        # Check every accepted target again in a fresh Lean process, including earlier merges.
        targets = (*previous_targets, target)
        names = ", ".join("`" + name for name in targets)
        checks = "\nrun_cmd do\n  for name in #[" + names + "] do\n" + '''    let bad := (<- Lean.collectAxioms name).filter fun ax =>
      !(#[`propext, `Quot.sound, `Classical.choice] : Array Lean.Name).contains ax
    unless bad.isEmpty do
      throwError "{name} depends on unsupported axioms: {bad}"
'''
        checked = folder / "Checked.lean"
        checked.write_text(content + checks, encoding="utf-8")
        started = time.monotonic()
        try:
            output = Runner(self.timeout, self.project).run([
                "lake", "env", "lean", "--json", str(checked),
            ])
        except MergeError as exc:
            (folder / "compile-error.log").write_text(str(exc), encoding="utf-8")
            raise
        metadata["compile_seconds"] = time.monotonic() - started
        metadata["checked_targets"] = targets
        (folder / "lean.jsonl").write_text(output, encoding="utf-8")
        (folder / "result.json").write_text(json.dumps(metadata, indent=2), encoding="utf-8")
        print(f"\n{case_id}: merge={merge_seconds:.1f}s, "
              f"compile={metadata['compile_seconds']:.1f}s, bytes={metadata['output_bytes']}",
              file=sys.stderr, flush=True)
        return content

    def test_brualdi_ch1_5(self):
        self.check_case("brualdi_ch1_5")

    def test_egmo_card_blackCell_eq_card_whiteCell(self):
        self.check_case("egmo_card_colours")

    def test_egmo_card_perfectCover_eq_gridMatchingCount(self):
        self.check_case("egmo_perfect_cover_count")

    def test_egmo_charpoly_pathAdj(self):
        self.check_case("egmo_charpoly")

    def test_egmo_consecutive_merges(self):
        current = None
        targets = []
        for case_id in MANIFEST["egmo_sequence"]:
            current = self.check_case(case_id, current=current, previous_targets=targets)
            targets.append(MANIFEST["cases"][case_id]["target"])


if __name__ == "__main__":
    unittest.main()
