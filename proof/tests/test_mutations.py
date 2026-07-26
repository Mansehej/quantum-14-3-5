#!/usr/bin/env python3
"""Positive and mutation tests for the claims-driven primary checker."""

from __future__ import annotations

import json
import sys
import unittest
from pathlib import Path

PROOF = Path(__file__).resolve().parents[1]
CLAIMS = PROOF / "claims" / "theorem.json"
FIXTURES = Path(__file__).resolve().parent / "fixtures"
sys.path.insert(0, str(PROOF))

import primary_checker as checker  # noqa: E402


class PrimaryClaimsTests(unittest.TestCase):
    def test_unmutated_claims_pass_all_required_checks(self) -> None:
        claims = checker.load_claims(CLAIMS, None)
        result = checker.run(claims)
        self.assertEqual(result["verdict"], "PASS")
        self.assertEqual(
            set(claims["required_checks"]),
            set(result["checks"]) - {"COVERAGE.REQUIRED"},
        )
        self.assertEqual(len(result["checks"]), 33)

    def assertMutationRejected(self, fixture_name: str) -> None:  # noqa: N802
        fixture = FIXTURES / fixture_name
        expected = json.loads(fixture.read_text(encoding="utf-8"))[
            "expected_failure"
        ]
        claims = checker.load_claims(CLAIMS, fixture)
        with self.assertRaises(checker.CheckFailure) as captured:
            checker.run(claims)
        self.assertEqual(captured.exception.check_id, expected)

    def test_broken_identity_rejected(self) -> None:
        self.assertMutationRejected("broken_identity51.json")

    def test_omitted_normal_form_rejected(self) -> None:
        self.assertMutationRejected("omitted_normal_form.json")

    def test_altered_collision_table_rejected(self) -> None:
        self.assertMutationRejected("altered_collision_table.json")

    def test_altered_even_relation_rejected(self) -> None:
        self.assertMutationRejected("altered_even_relation.json")

    def test_altered_odd_profiles_rejected(self) -> None:
        self.assertMutationRejected("altered_odd_profiles.json")

    def test_altered_lagrangian_count_rejected(self) -> None:
        self.assertMutationRejected("altered_lagrangian_count.json")

    def test_altered_extension_average_rejected(self) -> None:
        self.assertMutationRejected("altered_extension_average.json")

    def test_broken_anti_identity_ii_rejected(self) -> None:
        self.assertMutationRejected("broken_anti_identity_ii.json")

    def test_altered_universal_branch_formula_rejected(self) -> None:
        self.assertMutationRejected("altered_universal_branch_formula.json")

    def test_altered_p11_integrality_rejected(self) -> None:
        self.assertMutationRejected("altered_p11_integrality.json")

    def test_altered_p01_formula_rejected(self) -> None:
        self.assertMutationRejected("altered_p01_formula.json")

    def test_altered_p01_collision_rejected(self) -> None:
        self.assertMutationRejected("altered_p01_collision.json")

    def test_omitted_required_check_rejected(self) -> None:
        self.assertMutationRejected("omitted_required_check.json")


if __name__ == "__main__":
    unittest.main()
