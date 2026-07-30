#!/usr/bin/env python3
"""Test suite for mathforge CLI (Windows compatible)."""
from __future__ import annotations

import json
import sys
import tempfile
import unittest
from datetime import datetime, timezone
from pathlib import Path
from types import ModuleType

# Load mathforge code as a module
_repo_root = Path(__file__).parent
_mathforge_path = _repo_root / "bin" / "mathforge"

mathforge = ModuleType("mathforge")
mathforge.__file__ = str(_mathforge_path)
sys.modules["mathforge"] = mathforge

with open(_mathforge_path, encoding="utf-8") as f:
    code = compile(f.read(), str(_mathforge_path), "exec")
    exec(code, mathforge.__dict__)


class TestMathforgeCLI(unittest.TestCase):
    """Test mathforge CLI commands."""

    def setUp(self):
        """Create temporary workspace for each test."""
        self.temp_dir = Path(tempfile.mkdtemp())
        self.orig_root = mathforge.ROOT
        self.orig_catalog = mathforge.CATALOG
        self.orig_problems = mathforge.PROBLEMS
        self.orig_attacks = mathforge.ATTACKS

        # Override paths to temp directory
        mathforge.ROOT = self.temp_dir
        mathforge.CATALOG = self.temp_dir / "catalog" / "problems.json"
        mathforge.PROBLEMS = self.temp_dir / "problems"
        mathforge.ATTACKS = self.temp_dir / "attacks"

    def tearDown(self):
        """Restore original paths and clean up."""
        mathforge.ROOT = self.orig_root
        mathforge.CATALOG = self.orig_catalog
        mathforge.PROBLEMS = self.orig_problems
        mathforge.ATTACKS = self.orig_attacks

        # Clean up temp directory
        import shutil
        shutil.rmtree(self.temp_dir, ignore_errors=True)

    def test_catalog_seed(self):
        """Test: catalog seed creates demo problems."""
        result = mathforge.main(["catalog", "seed"])
        self.assertEqual(result, 0)

        # Verify catalog file exists and has content
        self.assertTrue(mathforge.CATALOG.exists())
        data = json.loads(mathforge.CATALOG.read_text(encoding="utf-8"))
        self.assertGreater(len(data.get("problems", [])), 0)
        self.assertIsNotNone(data.get("updated_at"))

    def test_status_empty(self):
        """Test: status command works with empty catalog."""
        # Capture stdout
        from io import StringIO
        old_stdout = sys.stdout
        sys.stdout = mystdout = StringIO()

        try:
            result = mathforge.main(["status"])
            self.assertEqual(result, 0)
            output = mystdout.getvalue()
            self.assertIn("0 catalog entries", output)
            self.assertIn("Active attacks: 0", output)
        finally:
            sys.stdout = old_stdout

    def test_status_with_catalog(self):
        """Test: status command displays catalog summary."""
        # Seed catalog first
        mathforge.main(["catalog", "seed"])

        from io import StringIO
        old_stdout = sys.stdout
        sys.stdout = mystdout = StringIO()

        try:
            result = mathforge.main(["status"])
            self.assertEqual(result, 0)
            output = mystdout.getvalue()
            self.assertIn("catalog entries", output)
            self.assertIn("Problems by status:", output)
        finally:
            sys.stdout = old_stdout

    def test_problem_new(self):
        """Test: problem new creates dossier files."""
        result = mathforge.main([
            "problem", "new",
            "test-problem-001",
            "--title", "Test Problem",
            "--domain", "test,demo",
            "--notes", "Test notes"
        ])
        self.assertEqual(result, 0)

        # Verify problem directory and files
        prob_dir = mathforge.PROBLEMS / "test-problem-001"
        self.assertTrue(prob_dir.exists())
        self.assertTrue((prob_dir / "STATEMENT.md").exists())
        self.assertTrue((prob_dir / "ATTACK_LOG.md").exists())

        # Verify catalog entry
        data = json.loads(mathforge.CATALOG.read_text(encoding="utf-8"))
        prob = next((p for p in data["problems"] if p["id"] == "test-problem-001"), None)
        self.assertIsNotNone(prob)
        self.assertEqual(prob["title"], "Test Problem")
        self.assertIn("test", prob["domain"])

    def test_score(self):
        """Test: score command writes feasibility score."""
        # Create a problem first
        mathforge.main([
            "problem", "new",
            "test-score-001",
            "--title", "Scorable Problem"
        ])

        result = mathforge.main([
            "score",
            "test-score-001",
            "--formalizable", "4.5",
            "--partial", "3.5",
            "--recommendation", "attack",
            "--rationale", "Test scoring"
        ])
        self.assertEqual(result, 0)

        # Verify score file
        score_file = mathforge.PROBLEMS / "test-score-001" / "feasibility.json"
        self.assertTrue(score_file.exists())
        score_data = json.loads(score_file.read_text(encoding="utf-8"))
        self.assertEqual(score_data["id"], "test-score-001")
        self.assertEqual(score_data["dimensions"]["formalizable"], 4.5)
        self.assertEqual(score_data["recommendation"], "attack")

    def test_attack_start(self):
        """Test: attack start creates attack directory and files."""
        # Create and score a problem first
        mathforge.main([
            "problem", "new",
            "test-attack-001",
            "--title", "Attackable Problem"
        ])

        result = mathforge.main([
            "attack", "start",
            "test-attack-001",
            "--strategy", "reduction",
            "--budget-tokens", "100000",
            "--notes", "Initial attempt"
        ])
        self.assertEqual(result, 0)

        # Verify attack directory exists
        self.assertTrue(mathforge.ATTACKS.exists())
        attack_dirs = list(mathforge.ATTACKS.glob("test-attack-001-*"))
        self.assertEqual(len(attack_dirs), 1)

        attack_dir = attack_dirs[0]
        self.assertTrue((attack_dir / "STATUS.json").exists())
        self.assertTrue((attack_dir / "LOG.md").exists())
        self.assertTrue((attack_dir / "STRATEGIES.md").exists())

        # Verify status data
        status_data = json.loads((attack_dir / "STATUS.json").read_text(encoding="utf-8"))
        self.assertEqual(status_data["problem_id"], "test-attack-001")
        self.assertEqual(status_data["status"], "active")
        self.assertEqual(status_data["strategy"], "reduction")
        self.assertEqual(status_data["budget_tokens"], 100000)

    def test_attack_start_unknown_problem(self):
        """Test: attack start fails gracefully on unknown problem."""
        result = mathforge.main([
            "attack", "start",
            "nonexistent-problem"
        ])
        self.assertEqual(result, 1)

    def test_status_with_active_attack(self):
        """Test: status command counts active attacks."""
        # Create problem and start attack
        mathforge.main(["problem", "new", "test-active-001", "--title", "Active Test"])
        mathforge.main(["attack", "start", "test-active-001"])

        from io import StringIO
        old_stdout = sys.stdout
        sys.stdout = mystdout = StringIO()

        try:
            result = mathforge.main(["status"])
            self.assertEqual(result, 0)
            output = mystdout.getvalue()
            self.assertIn("Active attacks: 1", output)
        finally:
            sys.stdout = old_stdout

    def test_claim_prepare(self):
        """Test: claim prepare creates claim packet."""
        # Create a problem first
        mathforge.main([
            "problem", "new",
            "test-claim-001",
            "--title", "Claimable Problem"
        ])

        result = mathforge.main([
            "claim", "prepare",
            "test-claim-001"
        ])
        self.assertEqual(result, 0)

        # Verify claim packet
        packet_file = mathforge.PROBLEMS / "test-claim-001" / "CLAIM_PACKET.md"
        self.assertTrue(packet_file.exists())
        content = packet_file.read_text(encoding="utf-8")
        self.assertIn("DRAFT — board only", content)
        self.assertIn("default is NO CLAIM", content)

    def test_windows_path_compatibility(self):
        """Test: Windows path handling (backslashes, drive letters)."""
        # This test runs on all platforms but validates Path behavior
        result = mathforge.main(["catalog", "seed"])
        self.assertEqual(result, 0)

        # Verify paths work correctly
        self.assertTrue(mathforge.CATALOG.exists())
        # Path should be absolute
        self.assertTrue(mathforge.CATALOG.is_absolute())

    def test_timestamp_format(self):
        """Test: Timestamps are ISO 8601 UTC."""
        mathforge.main(["catalog", "seed"])
        data = json.loads(mathforge.CATALOG.read_text(encoding="utf-8"))
        timestamp = data.get("updated_at")

        # Validate format: YYYY-MM-DDTHH:MM:SSZ
        self.assertIsNotNone(timestamp)
        self.assertTrue(timestamp.endswith("Z"))
        # Should parse without error
        parsed = datetime.strptime(timestamp, "%Y-%m-%dT%H:%M:%SZ")
        self.assertIsNotNone(parsed)


if __name__ == "__main__":
    unittest.main()
