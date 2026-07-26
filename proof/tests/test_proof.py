#!/usr/bin/env python3
"""Automated positive, independence, and mutation tests for the proof package."""

from __future__ import annotations

import ast
import json
import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path


PROOF = Path(__file__).resolve().parents[1]
ROOT = PROOF.parent
CLAIMS = PROOF / "claims" / "theorem.json"
FIXTURES = PROOF / "tests" / "fixtures"


def run_checker(name: str, mutation: Path | None = None) -> subprocess.CompletedProcess[str]:
    with tempfile.TemporaryDirectory(prefix="q1435-test-cache-") as cache:
        command = [
            sys.executable,
            "-I",
            "-X",
            f"pycache_prefix={cache}",
            str(PROOF / name),
            "--claims",
            str(CLAIMS),
        ]
        if mutation is not None:
            command.extend(["--mutation", str(mutation)])
        environment = {
            "PATH": os.environ.get("PATH", "/usr/bin:/bin"),
            "LANG": "C.UTF-8",
            "LC_ALL": "C.UTF-8",
            "TZ": "UTC",
            "PYTHONHASHSEED": "0",
        }
        return subprocess.run(
            command,
            cwd=ROOT,
            env=environment,
            text=True,
            capture_output=True,
            check=False,
        )


class ProofPackageTests(unittest.TestCase):
    def test_primary_and_cleanroom_accept_unmodified_claims(self) -> None:
        for checker in ("primary_checker.py", "cleanroom_checker.py"):
            with self.subTest(checker=checker):
                result = run_checker(checker)
                self.assertEqual(result.returncode, 0, result.stderr)
                payload = json.loads(result.stdout)
                self.assertEqual(payload["verdict"], "PASS")
                self.assertIn("machine-verified", payload["claim_status"])

    def test_cleanroom_has_no_primary_or_generated_import(self) -> None:
        path = PROOF / "cleanroom_checker.py"
        source = path.read_text(encoding="utf-8")
        tree = ast.parse(source, filename=str(path))
        imported = set()
        for node in ast.walk(tree):
            if isinstance(node, ast.Import):
                imported.update(alias.name.split(".")[0] for alias in node.names)
            elif isinstance(node, ast.ImportFrom) and node.module:
                imported.add(node.module.split(".")[0])
        self.assertNotIn("primary_checker", imported)
        self.assertNotIn("proof", imported)
        allowed = {
            "__future__",
            "argparse",
            "json",
            "sys",
            "collections",
            "fractions",
            "itertools",
            "math",
            "pathlib",
            "typing",
        }
        self.assertLessEqual(imported, allowed)

    def test_all_mutation_fixtures_are_rejected_by_primary(self) -> None:
        fixtures = sorted(FIXTURES.glob("*.json"))
        self.assertGreaterEqual(len(fixtures), 6)
        for fixture in fixtures:
            expected = json.loads(fixture.read_text(encoding="utf-8"))["expected_failure"]
            with self.subTest(fixture=fixture.name):
                result = run_checker("primary_checker.py", fixture)
                self.assertEqual(result.returncode, 2, result.stderr)
                self.assertIn(f"FAIL {expected}:", result.stderr)

    def test_fragile_mutations_are_also_rejected_cleanroom(self) -> None:
        fixtures = (
            "broken_identity51.json",
            "broken_anti_identity.json",
            "omitted_normal_form.json",
            "altered_collision_table.json",
            "altered_p03_enumerator.json",
        )
        for filename in fixtures:
            fixture = FIXTURES / filename
            with self.subTest(fixture=filename):
                result = run_checker("cleanroom_checker.py", fixture)
                self.assertEqual(result.returncode, 2, result.stderr)

    def test_p01_bounds_are_individually_necessary_in_branch_ledger(self) -> None:
        result = run_checker("primary_checker.py")
        self.assertEqual(result.returncode, 0, result.stderr)
        payload = json.loads(result.stdout)
        mutation_survivors = payload["facts"]["p01"]["mutation_survivors"]
        self.assertGreater(mutation_survivors["without_42"], 0)
        self.assertGreater(mutation_survivors["without_36"], 0)
        self.assertEqual(payload["facts"]["p01"]["ledger_survivors"], [])


if __name__ == "__main__":
    unittest.main(verbosity=2)
