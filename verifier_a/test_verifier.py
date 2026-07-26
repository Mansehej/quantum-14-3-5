#!/usr/bin/env python3
"""Deterministic regression and independent small-instance cross-checks."""

from __future__ import annotations

import random
import sys
import traceback
from pathlib import Path
from typing import Callable, Sequence

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT))

from verifier import (
    VerificationError,
    check_claim,
    classify_vector,
    enumerate_span_gray,
    load_literal_matrix,
    parse_literal_matrix,
    verify_literal_matrix,
)

FIXTURES = ROOT / "fixtures"


def _expect_verification_error(
    function: Callable[[], object], required_text: str
) -> None:
    try:
        function()
    except VerificationError as error:
        assert required_text in str(error), (required_text, str(error))
    else:
        raise AssertionError(f"expected VerificationError containing {required_text!r}")


def test_standard_five_qubit_code() -> None:
    rows = load_literal_matrix(FIXTURES / "five_qubit_5_1_3.txt")
    report = verify_literal_matrix(rows, expected_n=5)
    check_claim(
        report, expected_n=5, expected_rank=4, expected_k=1, exact_distance=3
    )
    assert report.normalizer_dimension == 6
    assert report.normalizer_size == 64
    assert report.stabilizer_size == 16
    assert report.logical_vector_count == 48
    assert report.stabilizer_weight_distribution == (1, 0, 0, 0, 15, 0)
    assert report.logical_weight_distribution == (0, 0, 0, 30, 0, 18)
    assert report.matrix_sha256 == (
        "136a761d188e9ec27f0df73a83f5a1a65f38f9e80483f9a6b55fd244f8a91cf5"
    )


def test_table_fourteen_qubit_code() -> None:
    rows = load_literal_matrix(FIXTURES / "table_14_3_4.txt")
    report = verify_literal_matrix(rows, expected_n=14)
    check_claim(
        report, expected_n=14, expected_rank=11, expected_k=3, exact_distance=4
    )
    assert report.normalizer_dimension == 17
    assert report.normalizer_size == 131_072
    assert report.stabilizer_size == 2_048
    assert report.logical_vector_count == 129_024
    assert report.stabilizer_weight_distribution == (
        1,
        2,
        1,
        0,
        0,
        6,
        18,
        72,
        249,
        454,
        485,
        376,
        246,
        114,
        24,
    )
    assert report.logical_weight_distribution == (
        0,
        0,
        0,
        0,
        105,
        588,
        2_079,
        6_216,
        14_322,
        24_192,
        30_198,
        27_384,
        16_821,
        6_132,
        987,
    )
    assert report.minimum_logical_witness is not None
    assert report.matrix_sha256 == (
        "b5bf2521d0e7d3561e8229809bea27b3665419cf0db4d63769e207fc312e85d7"
    )


def test_duplicate_row_rank_corruption() -> None:
    rows = load_literal_matrix(FIXTURES / "table_14_3_4.txt")
    corrupted = [row[:] for row in rows]
    corrupted[-1] = corrupted[0][:]
    _expect_verification_error(
        lambda: verify_literal_matrix(corrupted), "not full row rank"
    )


def test_one_bit_commutation_corruption() -> None:
    rows = load_literal_matrix(FIXTURES / "table_14_3_4.txt")
    corrupted = [row[:] for row in rows]
    corrupted[0][0] ^= 1
    _expect_verification_error(lambda: verify_literal_matrix(corrupted), "not isotropic")


def test_low_weight_logical_is_rejected_by_claim() -> None:
    rows = load_literal_matrix(FIXTURES / "low_logical_2_1_1.txt")
    report = verify_literal_matrix(rows)
    assert report.minimum_logical_weight == 1
    assert report.logical_weight_distribution == (0, 3, 3)
    _expect_verification_error(
        lambda: check_claim(report, minimum_distance=2),
        "required distance at least 2",
    )
    logical_ix = [0, 1, 0, 0]
    assert classify_vector(rows, logical_ix) == "logical"


def test_low_weight_stabilizer_is_not_logical() -> None:
    rows = load_literal_matrix(FIXTURES / "degenerate_6_1_3.txt")
    report = verify_literal_matrix(rows)
    check_claim(
        report, expected_n=6, expected_rank=5, expected_k=1, exact_distance=3
    )
    assert report.stabilizer_weight_distribution[1] == 1
    assert report.logical_weight_distribution[1] == 0
    assert report.logical_weight_distribution[2] == 0
    assert classify_vector(rows, rows[0]) == "stabilizer"


def test_dimension_and_bit_validation() -> None:
    _expect_verification_error(
        lambda: verify_literal_matrix([[1, 0, 0]]), "positive even"
    )
    _expect_verification_error(
        lambda: verify_literal_matrix([[1, 0, 0, 1], [0, 1]]),
        "has length 2",
    )
    _expect_verification_error(
        lambda: verify_literal_matrix([[1, 0, 2, 1]]), "not an integer bit"
    )
    _expect_verification_error(
        lambda: verify_literal_matrix([[1, 0, True, 1]]), "not an integer bit"
    )
    _expect_verification_error(
        lambda: verify_literal_matrix([[1, 0, 0, 1]], expected_n=3),
        "expected n=3",
    )


def test_literal_parser() -> None:
    parsed = parse_literal_matrix(
        """
        # comments and either compact or spaced rows are accepted
        H = [
          [1 0 0 | 0 1 0],
          010|001
        ]
        """
    )
    assert parsed == [
        [1, 0, 0, 0, 1, 0],
        [0, 1, 0, 0, 0, 1],
    ]
    _expect_verification_error(
        lambda: parse_literal_matrix("10|001"), "X half has 2 bits"
    )
    _expect_verification_error(
        lambda: parse_literal_matrix("10A|001"), "invalid bit character"
    )


def test_gray_span_enumerator() -> None:
    basis = (0b0001, 0b0110, 0b1010)
    observed = list(enumerate_span_gray(basis))
    assert len(observed) == 8
    assert len(set(observed)) == 8
    expected = {
        first ^ second ^ third
        for first in (0, basis[0])
        for second in (0, basis[1])
        for third in (0, basis[2])
    }
    assert set(observed) == expected


# The routines below deliberately do not call verifier.py's symplectic,
# membership, weight, packing, or nullspace helpers.  For n<=5 they enumerate
# the entire 4^n Pauli space and the entire stabilizer span.


def _brute_pack(row: Sequence[int]) -> int:
    value = 0
    for index in range(len(row)):
        if row[index] == 1:
            value += 1 << index
    return value


def _brute_symplectic(left: int, right: int, n: int) -> int:
    total = 0
    for qubit in range(n):
        left_x = (left // (1 << qubit)) % 2
        left_z = (left // (1 << (n + qubit))) % 2
        right_x = (right // (1 << qubit)) % 2
        right_z = (right // (1 << (n + qubit))) % 2
        total = (total + left_x * right_z + left_z * right_x) % 2
    return total


def _brute_weight(vector: int, n: int) -> int:
    total = 0
    for qubit in range(n):
        x_bit = (vector // (1 << qubit)) % 2
        z_bit = (vector // (1 << (n + qubit))) % 2
        if x_bit != 0 or z_bit != 0:
            total += 1
    return total


def _brute_span(rows: Sequence[int]) -> set[int]:
    span = {0}
    for row in rows:
        old_span = tuple(span)
        span.update(value ^ row for value in old_span)
    return span


def _brute_report(
    literal_rows: Sequence[Sequence[int]],
) -> tuple[tuple[int, ...], tuple[int, ...]]:
    n = len(literal_rows[0]) // 2
    packed_rows = [_brute_pack(row) for row in literal_rows]
    stabilizer = _brute_span(packed_rows)
    stabilizer_distribution = [0] * (n + 1)
    logical_distribution = [0] * (n + 1)

    for vector in range(1 << (2 * n)):
        if any(_brute_symplectic(row, vector, n) for row in packed_rows):
            continue
        weight = _brute_weight(vector, n)
        if vector in stabilizer:
            stabilizer_distribution[weight] += 1
        else:
            logical_distribution[weight] += 1
    return tuple(stabilizer_distribution), tuple(logical_distribution)


def _random_isotropic_rows(
    random_source: random.Random, n: int, rank: int
) -> list[list[int]]:
    selected: list[int] = []
    selected_span = {0}
    candidates = list(range(1, 1 << (2 * n)))
    random_source.shuffle(candidates)
    for candidate in candidates:
        if candidate in selected_span:
            continue
        if any(
            _brute_symplectic(candidate, existing, n) for existing in selected
        ):
            continue
        selected.append(candidate)
        old_span = tuple(selected_span)
        selected_span.update(value ^ candidate for value in old_span)
        if len(selected) == rank:
            break
    assert len(selected) == rank
    return [
        [(row >> column) & 1 for column in range(2 * n)] for row in selected
    ]


RANDOM_SEED = 14_003_005
RANDOM_CASE_COUNT = 30


def test_random_small_n_against_full_pauli_enumeration() -> None:
    random_source = random.Random(RANDOM_SEED)
    cases_checked = 0
    for repetition in range(3):
        for n in range(2, 6):
            for rank in range(1, n):
                rows = _random_isotropic_rows(random_source, n, rank)
                report = verify_literal_matrix(rows, expected_n=n)
                brute_stabilizer, brute_logical = _brute_report(rows)
                assert report.stabilizer_weight_distribution == brute_stabilizer, (
                    repetition,
                    n,
                    rank,
                    report.stabilizer_weight_distribution,
                    brute_stabilizer,
                )
                assert report.logical_weight_distribution == brute_logical, (
                    repetition,
                    n,
                    rank,
                    report.logical_weight_distribution,
                    brute_logical,
                )
                expected_minimum = next(
                    (
                        weight
                        for weight, count in enumerate(brute_logical)
                        if count != 0
                    ),
                    None,
                )
                assert report.minimum_logical_weight == expected_minimum
                cases_checked += 1
    assert cases_checked == RANDOM_CASE_COUNT


TESTS: tuple[tuple[str, Callable[[], None]], ...] = (
    ("standard_five_qubit_code", test_standard_five_qubit_code),
    ("table_fourteen_qubit_code", test_table_fourteen_qubit_code),
    ("duplicate_row_rank_corruption", test_duplicate_row_rank_corruption),
    ("one_bit_commutation_corruption", test_one_bit_commutation_corruption),
    ("low_weight_logical_rejected", test_low_weight_logical_is_rejected_by_claim),
    ("low_weight_stabilizer_excluded", test_low_weight_stabilizer_is_not_logical),
    ("dimension_and_bit_validation", test_dimension_and_bit_validation),
    ("literal_parser", test_literal_parser),
    ("gray_span_enumerator", test_gray_span_enumerator),
    (
        "random_small_n_full_pauli_crosscheck",
        test_random_small_n_against_full_pauli_enumeration,
    ),
)


def main() -> int:
    passed = 0
    for name, test in TESTS:
        try:
            test()
        except Exception:
            print(f"FAIL {name}")
            traceback.print_exc()
        else:
            print(f"PASS {name}")
            passed += 1
    print(f"RANDOM seed={RANDOM_SEED} cases={RANDOM_CASE_COUNT}")
    print(f"SUMMARY passed={passed} total={len(TESTS)}")
    return 0 if passed == len(TESTS) else 1


if __name__ == "__main__":
    raise SystemExit(main())
