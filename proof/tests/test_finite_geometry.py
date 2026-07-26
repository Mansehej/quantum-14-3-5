#!/usr/bin/env python3
"""Positive tests for exact finite geometry checks."""

from __future__ import annotations

import sys
import unittest
from pathlib import Path

PROOF = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(PROOF))

import finite_geometry as fg  # noqa: E402


class FiniteGeometryTests(unittest.TestCase):
    def test_quadratic_and_coset(self) -> None:
        result = fg.quadratic_and_coset_certificate()
        self.assertEqual(result["quadratic_local_cases"], 16)
        self.assertTrue(result["shadow_plus_shadow_equals_normalizer"])
        self.assertEqual(result["quotient_dimension6_gauss_magnitude"], 8)

    def test_lagrangians(self) -> None:
        result = fg.lagrangian_certificate()
        self.assertEqual(result["lagrangian_count"], 135)
        self.assertEqual(result["incidence_per_nonzero_point"], 15)
        self.assertEqual(result["singular_lagrangians_per_even_shift"], 30)
        self.assertEqual(result["singular_lagrangians_per_odd_shift"], 0)

    def test_normal_forms_are_exhaustive(self) -> None:
        result = fg.normal_form_certificate()
        self.assertEqual(result["normal_form_count"], 4)
        self.assertEqual(
            result["rank2_complete_signatures"],
            [[2, 2], [3, 1], [4, 0]],
        )
        self.assertEqual(
            result["rank3_allowed_pair_signatures_given_no_A5_A6"],
            [[0, 0]],
        )

    def test_all_weight_three_words_and_collisions(self) -> None:
        result = fg.collision_certificate()
        self.assertEqual(result["weight3_word_count"], 9828)
        bounds = sorted(
            item["collision_pair_upper_bound"]
            for item in result["normal_forms"].values()
        )
        self.assertEqual(bounds, [12, 12, 13, 28])

    def test_p01_bounds(self) -> None:
        result = fg.p01_certificate()
        incidence = result["repeated_coordinate_pauli_incidence"]
        self.assertEqual(incidence["L_bound_without_S2"], 14)
        self.assertEqual(incidence["bins_with_S2"], 36)
        self.assertEqual(incidence["L_bound_with_S2"], 12)
        self.assertEqual(
            result["unique_A4_translation_pairs"][
                "compatible_pairs_of_distinct_colliding_orbits"
            ],
            0,
        )


if __name__ == "__main__":
    unittest.main()
