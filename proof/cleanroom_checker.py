#!/usr/bin/env python3
"""Structurally independent clean-room cross-check.

This file imports no primary proof module.  It uses literal Pauli tuples,
RREF-generated quotient subspaces, and independently written exact polynomial
code to cross-check the fragile enumerators and collision calculations.
"""

from __future__ import annotations

import argparse
import json
import sys
from collections import Counter
from fractions import Fraction
from itertools import combinations, permutations, product
from math import comb
from pathlib import Path
from typing import Any, Iterable, Sequence


LENGTH = 14
LETTERS = ("X", "Y", "Z")


class Failure(RuntimeError):
    def __init__(self, check_id: str, message: str) -> None:
        super().__init__(message)
        self.check_id = check_id


def demand(check_id: str, condition: bool, message: str) -> None:
    if not condition:
        raise Failure(check_id, message)


def kraw(j: int, i: int) -> int:
    total = 0
    for chosen_from_i in range(j + 1):
        chosen_from_rest = j - chosen_from_i
        if chosen_from_i <= i and chosen_from_rest <= LENGTH - i:
            total += (
                (-1) ** chosen_from_i
                * 3**chosen_from_rest
                * comb(i, chosen_from_i)
                * comb(LENGTH - i, chosen_from_rest)
            )
    return total


K = [[kraw(j, i) for i in range(15)] for j in range(15)]


def mw(vector: Sequence[Fraction | int], alternating: bool = False) -> list[Fraction]:
    return [
        sum(
            Fraction(vector[i])
            * K[j][i]
            * ((-1) ** i if alternating else 1)
            for i in range(15)
        )
        / 16384
        for j in range(15)
    ]


def convolution(left: Sequence[int], right: Sequence[int]) -> list[int]:
    result = [0] * (len(left) + len(right) - 1)
    for i in range(len(left)):
        for j in range(len(right)):
            result[i + j] += left[i] * right[j]
    return result


def binomial_linear(plus_y: int, exponent: int) -> list[int]:
    return [comb(exponent, degree) * plus_y**degree for degree in range(exponent + 1)]


def solve(matrix: Sequence[Sequence[int | Fraction]], rhs: Sequence[int | Fraction]) -> list[Fraction]:
    n = len(matrix)
    augmented = [
        [Fraction(value) for value in row] + [Fraction(rhs[index])]
        for index, row in enumerate(matrix)
    ]
    for column in range(n):
        pivot = next(row for row in range(column, n) if augmented[row][column])
        augmented[column], augmented[pivot] = augmented[pivot], augmented[column]
        divisor = augmented[column][column]
        augmented[column] = [value / divisor for value in augmented[column]]
        for row in range(n):
            if row == column:
                continue
            factor = augmented[row][column]
            if factor:
                augmented[row] = [
                    value - factor * pivot_value
                    for value, pivot_value in zip(augmented[row], augmented[column])
                ]
    return [augmented[index][-1] for index in range(n)]


def selfdual_rows() -> list[list[int]]:
    rows = []
    for index in range(8):
        left = binomial_linear(1, LENGTH - 2 * index)
        right = [0] * index + binomial_linear(-1, index)
        rows.append(convolution(left, right))
    return rows


def anti_rows() -> list[list[int]]:
    rows = []
    for index in range(7):
        rows.append(
            convolution(
                binomial_linear(1, 13 - 2 * index),
                binomial_linear(-3, 2 * index + 1),
            )
        )
    return rows


def expand_selfdual(low: Sequence[int | Fraction]) -> list[Fraction]:
    rows = selfdual_rows()
    coefficients: list[Fraction] = []
    for weight in range(7):
        coefficients.append(
            Fraction(low[weight])
            - sum(coefficients[index] * rows[index][weight] for index in range(weight))
        )
    shadow_zero = [mw(row, alternating=True)[0] for row in rows]
    coefficients.append(
        -sum(coefficients[index] * shadow_zero[index] for index in range(7))
        / shadow_zero[7]
    )
    return [
        sum(coefficients[index] * rows[index][weight] for index in range(8))
        for weight in range(15)
    ]


def derive_identity51() -> dict[str, int]:
    equations: dict[str, dict[str, int]] = {}
    equations["T"] = {f"A{i}": 1 for i in range(1, 15)}
    equations["T"]["constant"] = -2047
    equations["P"] = {f"A{i}": 1 for i in range(2, 15, 2)}
    equations["P"]["constant"] = -1023
    for j in range(1, 5):
        equations[f"M{j}"] = {
            f"A{i}": K[j][i] - (2048 if i == j else 0)
            for i in range(1, 15)
        }
        equations[f"M{j}"]["constant"] = K[j][0]
    for j in (1, 4):
        equations[f"Q{j}"] = {f"A{i}": K[j][i] for i in range(2, 15, 2)}
        equations[f"Q{j}"][f"E{j}"] = -1024
        equations[f"Q{j}"]["constant"] = K[j][0]
    multipliers = {
        "T": -147,
        "P": -148,
        "M1": -42,
        "M2": -42,
        "M3": -7,
        "M4": -7,
        "Q1": 8,
        "Q4": 4,
    }
    result: Counter[str] = Counter()
    for name, multiplier in multipliers.items():
        for variable, coefficient in equations[name].items():
            result[variable] += multiplier * coefficient
    return {
        name: coefficient // -2048
        for name, coefficient in sorted(result.items())
        if coefficient
    }


def symp6(left: int, right: int) -> int:
    return (
        ((left & 7) & (right >> 3)).bit_count()
        + ((left >> 3) & (right & 7)).bit_count()
    ) & 1


def rref_bases_3_by_6() -> list[tuple[int, int, int]]:
    bases: list[tuple[int, int, int]] = []
    for pivots in combinations(range(6), 3):
        free = [
            (row, column)
            for row in range(3)
            for column in range(pivots[row] + 1, 6)
            if column not in pivots
        ]
        for bits in product((0, 1), repeat=len(free)):
            rows = [1 << pivot for pivot in pivots]
            for bit, (row, column) in zip(bits, free):
                if bit:
                    rows[row] |= 1 << column
            bases.append(tuple(rows))
    return bases


def span_basis(rows: Sequence[int]) -> frozenset[int]:
    return frozenset(
        (rows[0] if mask & 1 else 0)
        ^ (rows[1] if mask & 2 else 0)
        ^ (rows[2] if mask & 4 else 0)
        for mask in range(8)
    )


def lagrangian_facts() -> dict[str, int]:
    bases = rref_bases_3_by_6()
    spaces = [span_basis(rows) for rows in bases]
    if len(set(spaces)) != len(spaces):
        raise Failure(
            "CLEAN.LAGRANGIAN",
            "RREF generator produced duplicate six-dimensional subspaces",
        )
    lagrangians = [
        space
        for rows, space in zip(bases, spaces)
        if all(symp6(rows[i], rows[j]) == 0 for i in range(3) for j in range(i + 1, 3))
    ]
    counts = [sum(point in space for space in lagrangians) for point in range(1, 64)]
    return {
        "subspaces": len(spaces),
        "lagrangians": len(lagrangians),
        "point_incidence_min": min(counts),
        "point_incidence_max": max(counts),
        "double_count": sum(len(space) - 1 for space in lagrangians),
    }


def multiply_letter(left: str, right: str) -> str:
    if left == "I":
        return right
    if right == "I":
        return left
    if left == right:
        return "I"
    return ({"X", "Y", "Z"} - {left, right}).pop()


def multiply_word(left: tuple[str, ...], right: tuple[str, ...]) -> tuple[str, ...]:
    return tuple(multiply_letter(a, b) for a, b in zip(left, right))


def weight(word: Sequence[str]) -> int:
    return sum(letter != "I" for letter in word)


def commute(left: Sequence[str], right: Sequence[str]) -> bool:
    return (
        sum(a != "I" and b != "I" and a != b for a, b in zip(left, right)) % 2
        == 0
    )


def bins(word: Sequence[str]) -> frozenset[tuple[int, str]]:
    return frozenset((index, letter) for index, letter in enumerate(word) if letter != "I")


def words_of_weight_three() -> list[tuple[str, ...]]:
    result = []
    for support in combinations(range(LENGTH), 3):
        for labels in product(LETTERS, repeat=3):
            word = ["I"] * LENGTH
            for coordinate, label in zip(support, labels):
                word[coordinate] = label
            result.append(tuple(word))
    return result


def form_strings() -> dict[str, list[str]]:
    return {
        "independent": ["XXXXIIIIIIIIII", "IIIIXXXXIIIIII", "IIIIIIIIXXXXII"],
        "p0": ["XXXXIIIIIIIIII", "ZZZZIIIIIIIIII", "YYYYIIIIIIIIII"],
        "p1": ["XIXXXIIIIIIIII", "IXXZZIIIIIIIII", "XXIYYIIIIIIIII"],
        "p2": ["XXIIXXIIIIIIII", "IIXXXXIIIIIIII", "XXXXIIIIIIIIII"],
    }


def classify_forms() -> dict[str, Any]:
    # Independently enumerate the five simultaneous S3 column orbits.
    group = list(permutations(LETTERS))
    alphabet = ("I",) + LETTERS
    unseen = set(product(alphabet, repeat=2))
    orbits = []
    while unseen:
        seed = min(unseen)
        orbit = set()
        for permutation in group:
            action = {"I": "I", **dict(zip(LETTERS, permutation))}
            orbit.add((action[seed[0]], action[seed[1]]))
        orbits.append(orbit)
        unseen -= orbit

    planes = []
    for a, b, c, d in product(range(5), repeat=4):
        if a + c + d == 4 and b + c + d == 4 and a + b + d == 4 and d % 2 == 0:
            planes.append({"A": a, "B": b, "C": c, "D": d})
    independent_pairs = []
    for a, b, c, d in product(range(9), repeat=4):
        if a + c + d == 4 and b + c + d == 4 and a + b + d == 8 and d % 2 == 0:
            independent_pairs.append({"A": a, "B": b, "C": c, "D": d})
    return {
        "local_orbits": len(orbits),
        "rank2_category_solutions": planes,
        "rank3_pair_solutions": independent_pairs,
        "representatives": form_strings(),
    }


def collision_facts(
    words: Sequence[tuple[str, ...]], forms: dict[str, list[str]]
) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for name, text_generators in forms.items():
        generators = [tuple(text) for text in text_generators]
        histogram: Counter[int] = Counter()
        commuting_histogram: Counter[int] = Counter()
        shared_sizes: set[int] = set()
        for word in words:
            degree = 0
            for generator in generators:
                translated = multiply_word(word, generator)
                shared = bins(word) & bins(translated)
                if weight(translated) == 3 and shared:
                    degree += 1
                    shared_sizes.add(len(shared))
            histogram[degree] += 1
            if all(commute(word, generator) for generator in generators):
                commuting_histogram[degree] += 1
        maximum = max(histogram)
        all_counts = [histogram[degree] for degree in range(maximum + 1)]
        commuting_counts = [
            commuting_histogram[degree] for degree in range(maximum + 1)
        ]
        ordered_degrees = sorted(
            (
                degree
                for degree, count in commuting_histogram.items()
                for _ in range(count)
            ),
            reverse=True,
        )
        result[name] = {
            "all_words": all_counts,
            "commuting_words": commuting_counts,
            "commuting_total": sum(commuting_counts),
            "maximum_degree": maximum,
            "top24_edge_upper_bound": sum(ordered_degrees[:24]) // 2,
            "edge_shared_bin_sizes": sorted(shared_sizes),
        }
    return result


def p01_collision_facts(words: Sequence[tuple[str, ...]]) -> dict[str, int]:
    u = tuple("XXXXIIIIIIIIII")
    pairs: list[tuple[tuple[str, ...], tuple[str, ...]]] = []
    sizes = []
    for word in words:
        if not commute(word, u):
            continue
        translated = multiply_word(word, u)
        shared = bins(word) & bins(translated)
        if weight(translated) == 3 and shared and word < translated:
            pairs.append((word, translated))
            sizes.append(len(shared))
    compatible = 0
    for first, second in combinations(pairs, 2):
        if all(
            multiply_word(left, right) == u or weight(multiply_word(left, right)) >= 5
            for left in first
            for right in second
        ):
            compatible += 1
    return {
        "pairs": len(pairs),
        "pair_pairs_checked": comb(len(pairs), 2),
        "mutually_compatible_pair_pairs": compatible,
        "shared_bins_min": min(sizes),
        "shared_bins_max": max(sizes),
    }


def anti_identities() -> tuple[list[int], list[int]]:
    rows = anti_rows()
    low = [[rows[row][column] for column in range(7)] for row in range(7)]
    identity_i = solve(low, [-rows[row][14] for row in range(7)])
    shadow3 = [mw(row, alternating=True)[3] / 2 for row in rows]
    identity_ii = solve(low, [-16 * shadow3[row] for row in range(7)])
    return (
        [int(value) for value in identity_i] + [1],
        [int(value) for value in identity_ii] + [16],
    )


def derive_p03_enumerators() -> dict[str, list[int]]:
    # Solve N5,N6 directly from the two zero shadow coefficients.
    n00 = expand_selfdual([1, 0, 0, 0, 3, 0, 0])
    n10 = expand_selfdual([1, 0, 0, 0, 3, 1, 0])
    n01 = expand_selfdual([1, 0, 0, 0, 3, 0, 1])
    shadows = [mw(vector, alternating=True) for vector in (n00, n10, n01)]
    matrix = [
        [shadows[1][index] - shadows[0][index], shadows[2][index] - shadows[0][index]]
        for index in (2, 4)
    ]
    rhs = [-shadows[0][index] for index in (2, 4)]
    n5, n6 = solve(matrix, rhs)
    n = expand_selfdual([1, 0, 0, 0, 3, n5, n6])

    anti = anti_rows()
    low_matrix = [[anti[column][row] for column in range(7)] for row in range(7)]
    low_a = [1, 0, 0, 0, 3, 0, 0]
    low_g = [16 * low_a[index] - 9 * n[index] for index in range(7)]
    coordinates = solve(low_matrix, low_g)
    g = [
        sum(coordinates[index] * anti[index][weight_index] for index in range(7))
        for weight_index in range(15)
    ]
    a = [(g[index] + 9 * n[index]) / 16 for index in range(15)]
    b = [8 * value for value in mw(a)]
    s = [8 * value for value in mw(a, alternating=True)]
    t = mw(n, alternating=True)
    vectors = {"A": a, "B": b, "S": s, "N": n, "T": t}
    demand(
        "CLEAN.ENUM.P03",
        all(value.denominator == 1 for vector in vectors.values() for value in vector),
        "nonintegral independently reconstructed enumerator",
    )
    return {
        name: [int(value) for value in vector] for name, vector in vectors.items()
    }


def mutate(claims: dict[str, Any], path: Path | None) -> dict[str, Any]:
    if path is None:
        return claims
    fixture = json.loads(path.read_text(encoding="utf-8"))
    current: Any = claims
    for key in fixture["path"][:-1]:
        current = current[key]
    current[fixture["path"][-1]] = fixture["value"]
    return claims


def run(claims: dict[str, Any]) -> dict[str, Any]:
    checks: dict[str, Any] = {}
    identity51 = derive_identity51()
    demand("ODD.IDENTITY51", identity51 == claims["odd_identity51"], "identity 51 mismatch")
    checks["CLEAN.ODD.IDENTITY51"] = identity51

    lagrangian = lagrangian_facts()
    demand("CLEAN.LAGRANGIAN", lagrangian == claims["lagrangian_6d"], "6D incidence mismatch")
    checks["CLEAN.LAGRANGIAN"] = lagrangian

    identity_i, identity_ii = anti_identities()
    demand("CLEAN.ANTI.I", identity_i == claims["anti_identity_i"], "anti identity I mismatch")
    demand("CLEAN.ANTI.II", identity_ii == claims["anti_identity_ii"], "anti identity II mismatch")
    checks["CLEAN.ANTI"] = {"identity_i": identity_i, "identity_ii": identity_ii}

    p03_enumerators = derive_p03_enumerators()
    demand(
        "CLEAN.ENUM.P03",
        p03_enumerators == claims["p03_enumerators"],
        "p03 enumerator mismatch",
    )
    checks["CLEAN.ENUM.P03"] = p03_enumerators

    classification = classify_forms()
    demand(
        "P03.NORMAL_FORMS_4",
        classification["local_orbits"] == 5
        and classification["rank2_category_solutions"]
        == [
            {"A": 0, "B": 0, "C": 0, "D": 4},
            {"A": 1, "B": 1, "C": 1, "D": 2},
            {"A": 2, "B": 2, "C": 2, "D": 0},
        ]
        and classification["rank3_pair_solutions"]
        == [{"A": 4, "B": 4, "C": 0, "D": 0}]
        and classification["representatives"] == claims["normal_forms"],
        "normal-form coverage mismatch",
    )
    checks["CLEAN.NORMAL_FORMS"] = classification

    words = words_of_weight_three()
    demand(
        "CLEAN.WORDS.9828",
        len(words) == len(set(words)) == 9828,
        "weight-three generator is incomplete or duplicated",
    )
    collisions = collision_facts(words, classification["representatives"])
    demand(
        "P03.DEGREE_HISTOGRAMS",
        collisions == claims["collision_tables"],
        "collision table mismatch",
    )
    checks["CLEAN.COLLISIONS"] = collisions

    p01 = p01_collision_facts(words)
    demand("CLEAN.P01.COLLISION", p01 == claims["p01_collision"], "p01 pair table mismatch")
    checks["CLEAN.P01.COLLISION"] = p01

    return {
        "schema": "quantum-14-3-5-cleanroom-proof-v1",
        "verdict": "PASS",
        "claim_status": "machine-verified proof artifact; see the accompanying paper",
        "implementation": "standalone literal-Pauli/RREF clean room",
        "checks": checks,
    }


def main(argv: Sequence[str] | None = None) -> int:
    root = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser()
    parser.add_argument("--claims", type=Path, default=root / "claims" / "theorem.json")
    parser.add_argument("--mutation", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args(argv or sys.argv[1:])
    claims = mutate(json.loads(args.claims.read_text(encoding="utf-8")), args.mutation)
    try:
        result = run(claims)
    except Failure as error:
        print(f"FAIL {error.check_id}: {error}", file=sys.stderr)
        return 2
    text = json.dumps(result, sort_keys=True, indent=2) + "\n"
    if args.output:
        args.output.write_text(text, encoding="utf-8")
    else:
        sys.stdout.write(text)
    print(
        f"PASS cleanroom checks={len(result['checks'])} "
        "status=machine-verified",
        file=sys.stderr,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
