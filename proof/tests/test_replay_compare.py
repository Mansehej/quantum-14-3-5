#!/usr/bin/env python3
"""Mutation tests for the replay consensus comparison and artifact hygiene."""

from __future__ import annotations

import copy
import json
import os
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from typing import Any, Callable

PROOF = Path(__file__).resolve().parents[1]
ROOT = PROOF.parent
CLAIMS = PROOF / "claims" / "theorem.json"
sys.path.insert(0, str(PROOF))

import replay  # noqa: E402


def run_generator(command: list[str], cwd: Path) -> str:
    environment = {
        "PATH": os.environ.get("PATH", "/usr/bin:/bin"),
        "LANG": "C.UTF-8",
        "LC_ALL": "C.UTF-8",
        "TZ": "UTC",
        "PYTHONHASHSEED": "0",
    }
    result = subprocess.run(
        command,
        cwd=cwd,
        env=environment,
        text=True,
        capture_output=True,
        check=False,
    )
    if result.returncode:
        raise AssertionError(f"{command} failed: {result.stderr}")
    return result.stdout


class ReplayComparisonTests(unittest.TestCase):
    """Regenerate the five certificates once, then mutate them in memory."""

    claims: dict[str, Any]
    primary: dict[str, Any]
    cleanroom: dict[str, Any]
    algebra: dict[str, Any]
    finite: dict[str, Any]
    javascript: dict[str, Any]

    @classmethod
    def setUpClass(cls) -> None:
        node = shutil.which("node")
        if node is None:
            raise unittest.SkipTest("Node.js is required for the consensus test")
        cls.claims = json.loads(CLAIMS.read_text(encoding="utf-8"))
        with tempfile.TemporaryDirectory(prefix="q1435-consensus-") as directory:
            output = Path(directory)
            python = [sys.executable, "-I", "-X", f"pycache_prefix={output}/cache"]
            run_generator(
                python
                + [
                    str(PROOF / "primary_checker.py"),
                    "--claims",
                    str(CLAIMS),
                    "--output",
                    str(output / "primary.json"),
                ],
                ROOT,
            )
            run_generator(
                python
                + [
                    str(PROOF / "cleanroom_checker.py"),
                    "--claims",
                    str(CLAIMS),
                    "--output",
                    str(output / "cleanroom.json"),
                ],
                ROOT,
            )
            cls.primary = json.loads(
                (output / "primary.json").read_text(encoding="utf-8")
            )
            cls.cleanroom = json.loads(
                (output / "cleanroom.json").read_text(encoding="utf-8")
            )
            cls.algebra = json.loads(
                run_generator(
                    python + [str(PROOF / "exact_algebra.py"), "--json"], ROOT
                )
            )
            cls.finite = json.loads(
                run_generator(
                    python + [str(PROOF / "finite_geometry.py"), "--json"], ROOT
                )
            )
            cls.javascript = json.loads(
                run_generator(
                    [node, str(PROOF / "cleanroom_checker.js"), "--json"], ROOT
                )
            )

    def compare(
        self,
        mutate: Callable[[dict[str, Any], dict[str, Any], dict[str, Any]], None]
        | None = None,
    ) -> dict[str, Any]:
        claims = copy.deepcopy(self.claims)
        primary = copy.deepcopy(self.primary)
        algebra = copy.deepcopy(self.algebra)
        if mutate is not None:
            mutate(claims, primary, algebra)
        return replay.compare_certificates(
            claims,
            primary,
            copy.deepcopy(self.cleanroom),
            algebra,
            copy.deepcopy(self.finite),
            copy.deepcopy(self.javascript),
        )

    def test_fresh_certificates_reach_consensus(self) -> None:
        consensus = self.compare()
        self.assertEqual(consensus["verdict"], "PASS")
        self.assertEqual(len(consensus["comparisons"]), 35)
        self.assertIn("machine-verified", consensus["claim_status"])

    def test_mutated_certificates_are_rejected(self) -> None:
        def mutation(path: list[Any], value: Any) -> Callable[..., None]:
            def apply(
                claims: dict[str, Any],
                primary: dict[str, Any],
                algebra: dict[str, Any],
            ) -> None:
                roots = {"claims": claims, "primary": primary, "algebra": algebra}
                current: Any = roots[path[0]]
                for key in path[1:-1]:
                    current = current[key]
                current[path[-1]] = value

            return apply

        cases: dict[str, Callable[..., None]] = {
            "primary verdict flipped": mutation(["primary", "verdict"], "FAIL"),
            "even relation altered": mutation(
                ["primary", "facts", "even", "elimination_relation", 0], 161
            ),
            "identity 51 rhs altered": mutation(
                ["algebra", "odd_51_identity", "combined_rhs"], -50
            ),
            "odd profiles altered": mutation(
                ["primary", "facts", "odd", "profiles", 0], [0, 2]
            ),
            "p11 integrality altered": mutation(
                ["primary", "facts", "p11", "integrality", 0, "required_S2"], "1/3"
            ),
            "p01 S3 formula altered": mutation(
                ["primary", "facts", "p01", "formulas", "S3", "constant"], 23
            ),
            "p01 collision count altered": mutation(
                ["primary", "facts", "p01", "collision", "pairs"], 91
            ),
            "p01 42-bin bound loosened": mutation(
                ["primary", "checks", "P01.BINS_42", "integer_upper_bound"], 15
            ),
            "shadow incidence altered": mutation(
                [
                    "primary",
                    "facts",
                    "geometry",
                    "shadow_incidence_8d",
                    "eligible_incidence_max",
                ],
                31,
            ),
            "p03 upper bound reaches lower bound": mutation(
                [
                    "primary",
                    "facts",
                    "p03",
                    "collisions",
                    "p2",
                    "top24_edge_upper_bound",
                ],
                30,
            ),
            "p03 contradiction lower bound altered": mutation(
                ["primary", "checks", "P03.COLLISION_CONTRADICTION", "lower_bound"],
                29,
            ),
            "required check added to claims": mutation(
                ["claims", "required_checks", 0], "FAKE.NOT_IMPLEMENTED"
            ),
        }

        def drop_recorded_check(
            claims: dict[str, Any],
            primary: dict[str, Any],
            algebra: dict[str, Any],
        ) -> None:
            del primary["checks"]["P03.WORDS_9828"]

        cases["recorded check removed from primary"] = drop_recorded_check

        for label, mutate in cases.items():
            with self.subTest(case=label):
                with self.assertRaises(replay.ReplayFailure):
                    self.compare(mutate)

    def test_clear_generated_removes_all_replay_artifacts(self) -> None:
        original = replay.GENERATED
        try:
            with tempfile.TemporaryDirectory(prefix="q1435-generated-") as directory:
                replay.GENERATED = Path(directory)
                artifact_names = (
                    *replay.GENERATED_ARTIFACTS,
                    "SHA256SUMS",
                    *replay.DEPRECATED_GENERATED,
                )
                for name in artifact_names:
                    (replay.GENERATED / name).write_text("stale\n", encoding="utf-8")
                foreign = replay.GENERATED / "not_owned_by_replay.txt"
                foreign.write_text("kept\n", encoding="utf-8")
                replay.clear_generated()
                for name in artifact_names:
                    self.assertFalse((replay.GENERATED / name).exists(), name)
                self.assertTrue(foreign.exists())
        finally:
            replay.GENERATED = original


if __name__ == "__main__":
    unittest.main(verbosity=2)
