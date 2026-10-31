import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


class ExplanationPathTests(unittest.TestCase):
    def run_explanation(self, lhs, rhs, recorded=()):
        with tempfile.TemporaryDirectory() as directory:
            entries = Path(directory) / "entries.json"
            duals = Path(directory) / "duals.json"
            entries.write_text(json.dumps(recorded))
            duals.write_text("[]")
            return subprocess.run(
                [sys.executable, str(Path(__file__).resolve().parents[1] / "explain_implication.py"),
                 "--entries-file", str(entries), "--duals-file", str(duals), lhs, rhs],
                capture_output=True, text=True,
            )

    def test_unrecorded_implication_is_unknown(self):
        result = self.run_explanation("Equation1", "Equation2")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout.strip(), "Unknown")

    def test_unrecorded_equation_still_implies_itself(self):
        result = self.run_explanation("Equation1", "Equation1")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout.strip(), "Equation1 => Equation1  (tautology)")

    def test_recorded_implication_keeps_its_explanation(self):
        entry = {"variant": {"implication": {"lhs": "Equation1", "rhs": "Equation2"}},
                 "name": "one_implies_two", "filename": "equational_theories/Test.lean",
                 "proven": True}
        result = self.run_explanation("Equation1", "Equation2", [entry])
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("Equation1 => Equation2", result.stdout)
        self.assertIn("one_implies_two  in  Test.lean", result.stdout)
