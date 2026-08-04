#!/usr/bin/env python3
"""Exact primary checker for the [[14,3,5]] nonexistence proof.

This program deliberately uses only the Python standard library.  It derives
the target-specific algebra and exhausts every finite configuration used by
the argument.  Foundational coding-theory lemmas are stated separately in
LEMMAS.md; none of the JSON claims is trusted without regeneration here.
"""

from __future__ import annotations

import argparse
import json
import sys
from collections import Counter
from dataclasses import dataclass
from fractions import Fraction
from functools import reduce
from itertools import combinations, permutations, product
from math import comb, gcd, lcm
from pathlib import Path
from typing import Any, Iterable, Iterator, Mapping, Sequence


N = 14
SIZE_C = 1 << 11
MASK = (1 << N) - 1


class CheckFailure(RuntimeError):
    """A stable-ID proof-check failure."""

    def __init__(self, check_id: str, detail: str) -> None:
        super().__init__(f"{check_id}: {detail}")
        self.check_id = check_id
        self.detail = detail


@dataclass
class Recorder:
    checks: dict[str, Any]

    def require(self, check_id: str, condition: bool, payload: Any) -> None:
        if not condition:
            raise CheckFailure(check_id, repr(payload))
        self.checks[check_id] = payload


def canonical_json(value: Any) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True)


def json_fraction(value: Fraction | int) -> int | str:
    value = Fraction(value)
    if value.denominator == 1:
        return value.numerator
    return f"{value.numerator}/{value.denominator}"


def rref(rows: Sequence[Sequence[Fraction | int]]) -> list[list[Fraction]]:
    answer = [[Fraction(value) for value in row] for row in rows]
    if not answer:
        return []
    pivot_row = 0
    for column in range(len(answer[0]) - 1):
        selected = next(
            (row for row in range(pivot_row, len(answer)) if answer[row][column]),
            None,
        )
        if selected is None:
            continue
        answer[pivot_row], answer[selected] = answer[selected], answer[pivot_row]
        pivot = answer[pivot_row][column]
        answer[pivot_row] = [value / pivot for value in answer[pivot_row]]
        for row in range(len(answer)):
            if row == pivot_row or not answer[row][column]:
                continue
            factor = answer[row][column]
            answer[row] = [
                left - factor * right
                for left, right in zip(answer[row], answer[pivot_row])
            ]
        pivot_row += 1
        if pivot_row == len(answer):
            break
    return answer


def matrix_rank(rows: Sequence[Sequence[int | Fraction]]) -> int:
    if not rows:
        return 0
    reduced = rref([list(row) + [0] for row in rows])
    return sum(any(value for value in row[:-1]) for row in reduced)


def integerize(values: Sequence[Fraction | int]) -> list[int]:
    fractions = [Fraction(value) for value in values]
    denominator = reduce(lcm, (value.denominator for value in fractions), 1)
    integers = [int(value * denominator) for value in fractions]
    divisor = reduce(gcd, (abs(value) for value in integers if value), 0) or 1
    integers = [value // divisor for value in integers]
    first = next((value for value in reversed(integers) if value), 1)
    if first < 0:
        integers = [-value for value in integers]
    return integers


def krawtchouk(j: int, i: int, n: int = N) -> int:
    return sum(
        (-1) ** t
        * 3 ** (j - t)
        * comb(i, t)
        * comb(n - i, j - t)
        for t in range(j + 1)
        if t <= i and j - t <= n - i
    )


K = [[krawtchouk(j, i) for i in range(N + 1)] for j in range(N + 1)]


def transform(
    coefficients: Sequence[Any], *, alternating: bool = False
) -> list[Any]:
    scale = Fraction(1, 1 << N)
    return [
        scale
        * sum(
            coefficients[i] * K[j][i] * ((-1) ** i if alternating else 1)
            for i in range(N + 1)
        )
        for j in range(N + 1)
    ]


def poly_mul(left: Sequence[int], right: Sequence[int]) -> list[int]:
    answer = [0] * (len(left) + len(right) - 1)
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            answer[i + j] += a * b
    return answer


def linear_power(a: int, b: int, exponent: int) -> list[int]:
    return [comb(exponent, j) * a ** (exponent - j) * b**j for j in range(exponent + 1)]


class Affine:
    """A rational affine expression in named formal variables."""

    __slots__ = ("constant", "coefficients")

    def __init__(
        self,
        constant: Fraction | int = 0,
        coefficients: Mapping[str, Fraction | int] | None = None,
    ) -> None:
        self.constant = Fraction(constant)
        self.coefficients = {
            key: Fraction(value)
            for key, value in (coefficients or {}).items()
            if value
        }

    @classmethod
    def variable(cls, name: str) -> "Affine":
        return cls(0, {name: 1})

    @staticmethod
    def coerce(value: "Affine | Fraction | int") -> "Affine":
        return value if isinstance(value, Affine) else Affine(value)

    def __add__(self, other: "Affine | Fraction | int") -> "Affine":
        other = self.coerce(other)
        keys = set(self.coefficients) | set(other.coefficients)
        return Affine(
            self.constant + other.constant,
            {
                key: self.coefficients.get(key, 0)
                + other.coefficients.get(key, 0)
                for key in keys
            },
        )

    __radd__ = __add__

    def __neg__(self) -> "Affine":
        return Affine(
            -self.constant, {key: -value for key, value in self.coefficients.items()}
        )

    def __sub__(self, other: "Affine | Fraction | int") -> "Affine":
        return self + (-self.coerce(other))

    def __rsub__(self, other: "Affine | Fraction | int") -> "Affine":
        return self.coerce(other) - self

    def __mul__(self, scalar: Fraction | int) -> "Affine":
        scalar = Fraction(scalar)
        return Affine(
            self.constant * scalar,
            {key: value * scalar for key, value in self.coefficients.items()},
        )

    __rmul__ = __mul__

    def __truediv__(self, scalar: Fraction | int) -> "Affine":
        return self * (1 / Fraction(scalar))

    def coefficient(self, variable: str) -> Fraction:
        return self.coefficients.get(variable, Fraction(0))

    def without(self, variables: Iterable[str]) -> "Affine":
        blocked = set(variables)
        return Affine(
            self.constant,
            {
                key: value
                for key, value in self.coefficients.items()
                if key not in blocked
            },
        )

    def substitute(
        self, substitutions: Mapping[str, "Affine | Fraction | int"]
    ) -> "Affine":
        answer = Affine(self.constant)
        for key, value in self.coefficients.items():
            answer += self.coerce(substitutions.get(key, Affine.variable(key))) * value
        return answer

    def is_zero(self) -> bool:
        return self.constant == 0 and not self.coefficients

    def as_json(self) -> dict[str, Any]:
        return {
            "constant": json_fraction(self.constant),
            "coefficients": {
                key: json_fraction(value)
                for key, value in sorted(self.coefficients.items())
            },
        }

    def __repr__(self) -> str:
        return canonical_json(self.as_json())


def solve_affine_system(
    matrix: Sequence[Sequence[Fraction | int]], rhs: Sequence[Affine]
) -> list[Affine]:
    size = len(matrix)
    if size == 0 or any(len(row) != size for row in matrix) or len(rhs) != size:
        raise ValueError("expected a square affine system")
    left = [[Fraction(value) for value in row] for row in matrix]
    right = list(rhs)
    for column in range(size):
        selected = next(
            (row for row in range(column, size) if left[row][column]), None
        )
        if selected is None:
            raise ValueError("singular affine system")
        left[column], left[selected] = left[selected], left[column]
        right[column], right[selected] = right[selected], right[column]
        pivot = left[column][column]
        left[column] = [value / pivot for value in left[column]]
        right[column] = right[column] / pivot
        for row in range(size):
            if row == column or not left[row][column]:
                continue
            factor = left[row][column]
            left[row] = [
                value - factor * pivot_value
                for value, pivot_value in zip(left[row], left[column])
            ]
            right[row] = right[row] - factor * right[column]
    return right


def solve_named_affine(equations: Sequence[Affine], variables: Sequence[str]) -> dict[str, Affine]:
    matrix = [[equation.coefficient(name) for name in variables] for equation in equations]
    rhs = [-equation.without(variables) for equation in equations]
    solution = solve_affine_system(matrix, rhs)
    return dict(zip(variables, solution))


def span(vectors: Sequence[int]) -> tuple[int, ...]:
    values = {0}
    for vector in vectors:
        values |= {value ^ vector for value in tuple(values)}
    return tuple(sorted(values))


def gf2_rank(vectors: Sequence[int]) -> int:
    pivots: dict[int, int] = {}
    for source in vectors:
        value = source
        while value:
            pivot = value.bit_length() - 1
            if pivot not in pivots:
                pivots[pivot] = value
                break
            value ^= pivots[pivot]
    return len(pivots)


def symplectic(value: int, other: int, half_dimension: int) -> int:
    mask = (1 << half_dimension) - 1
    x1, z1 = value & mask, value >> half_dimension
    x2, z2 = other & mask, other >> half_dimension
    return ((x1 & z2) ^ (z1 & x2)).bit_count() & 1


def quadratic(value: int, half_dimension: int) -> int:
    mask = (1 << half_dimension) - 1
    return ((value & mask) & (value >> half_dimension)).bit_count() & 1


def enumerate_subspaces(dimension: int, subdimension: int) -> list[tuple[int, ...]]:
    if subdimension != 3:
        raise ValueError("this small exhaustive enumerator is specialized to k=3")
    found: set[tuple[int, ...]] = set()
    for generators in combinations(range(1, 1 << dimension), subdimension):
        generated = span(generators)
        if len(generated) == 1 << subdimension:
            found.add(generated)
    return sorted(found)


def pauli_weight(value: int) -> int:
    return ((value & MASK) | ((value >> N) & MASK)).bit_count()


def pauli_symbol(value: int, coordinate: int) -> int:
    return ((value >> coordinate) & 1) | (((value >> (N + coordinate)) & 1) << 1)


def pack_symbols(symbols: Sequence[int]) -> int:
    value = 0
    for coordinate, symbol in enumerate(symbols):
        if symbol & 1:
            value |= 1 << coordinate
        if symbol & 2:
            value |= 1 << (N + coordinate)
    return value


def pack_string(word: str) -> int:
    table = {"I": 0, "X": 1, "Z": 2, "Y": 3}
    if len(word) != N or any(letter not in table for letter in word):
        raise ValueError(f"invalid Pauli word {word!r}")
    return pack_symbols([table[letter] for letter in word])


def pauli_incidences(value: int) -> frozenset[tuple[int, int]]:
    return frozenset(
        (coordinate, symbol)
        for coordinate in range(N)
        if (symbol := pauli_symbol(value, coordinate))
    )


def weight_three_words() -> list[int]:
    words: list[int] = []
    for support in combinations(range(N), 3):
        for labels in product((1, 2, 3), repeat=3):
            symbols = [0] * N
            for coordinate, label in zip(support, labels):
                symbols[coordinate] = label
            words.append(pack_symbols(symbols))
    return words


def derive_even_branch(recorder: Recorder, claims: Mapping[str, Any]) -> dict[str, Any]:
    even_weights = tuple(range(0, N + 1, 2))
    rows: list[list[Fraction]] = [
        [Fraction(int(weight == 0)) for weight in even_weights] + [Fraction(1)],
        [Fraction(1) for _ in even_weights] + [Fraction(SIZE_C)],
    ]
    for j in range(1, 5):
        rows.append(
            [
                Fraction(K[j][weight] - (SIZE_C if weight == j else 0))
                for weight in even_weights
            ]
            + [Fraction(0)]
        )
    reduced = rref(rows)
    pivot_rows: dict[int, list[Fraction]] = {}
    for row in reduced:
        pivot = next((index for index, value in enumerate(row[:-1]) if value), None)
        if pivot is not None:
            pivot_rows[pivot] = row
    selected = [pivot_rows[index] for index in (1, 2, 3)]

    # Express A2,A4,A6 as affine functions of p=A12 and q=A14.
    expressions: list[tuple[Fraction, Fraction, Fraction]] = []
    for row in selected:
        expressions.append((row[-1], -row[6], -row[7]))
    p_coefficients = [expression[1] for expression in expressions]
    q_coefficients = [expression[2] for expression in expressions]
    relation = [
        p_coefficients[1] * q_coefficients[2]
        - p_coefficients[2] * q_coefficients[1],
        p_coefficients[2] * q_coefficients[0]
        - p_coefficients[0] * q_coefficients[2],
        p_coefficients[0] * q_coefficients[1]
        - p_coefficients[1] * q_coefficients[0],
    ]
    constant = sum(
        coefficient * expression[0]
        for coefficient, expression in zip(relation, expressions)
    )
    primitive_relation = integerize([*relation, -constant])
    # Present the derived primitive relation at the conventional scale with
    # coefficient +20 on A6.
    scale = Fraction(20, primitive_relation[2])
    normalized_relation = [int(Fraction(value) * scale) for value in primitive_relation]

    equations = []
    for index, expression in zip((2, 4, 6), expressions):
        # Clear denominators in Ai = constant + p*pcoef + q*qcoef.
        equation = integerize([1, -expression[1], -expression[2], -expression[0]])
        equations.append({"variable": f"A{index}", "A": equation[0], "p": equation[1], "q": equation[2], "constant": equation[3]})

    expected = claims["even"]["elimination_relation"]
    recorder.require(
        "EVEN.RREF",
        normalized_relation == expected,
        {"derived": normalized_relation, "claimed": expected},
    )
    recorder.require(
        "EVEN.CONTRADICTION",
        normalized_relation == [160, 90, 20, -70]
        and Fraction(70, 20) == Fraction(7, 2),
        {
            "reason": "nonnegativity forces A2=A4=0, hence A6=7/2",
            "A6": "7/2",
        },
    )
    return {"rref_equations": equations, "elimination_relation": normalized_relation}


def add_rows(*weighted_rows: tuple[int, Mapping[str, Fraction | int]]) -> dict[str, Fraction]:
    answer: dict[str, Fraction] = {}
    for multiplier, row in weighted_rows:
        for key, value in row.items():
            answer[key] = answer.get(key, Fraction(0)) + multiplier * Fraction(value)
    return {key: value for key, value in answer.items() if value}


def derive_odd_identity(recorder: Recorder, claims: Mapping[str, Any]) -> dict[str, Any]:
    t_row = {f"A{i}": 1 for i in range(1, N + 1)}
    t_row["constant"] = -2047
    p_row = {f"A{i}": 1 for i in range(2, N + 1, 2)}
    p_row["constant"] = -1023
    m_rows: dict[int, dict[str, int]] = {}
    for j in range(1, 5):
        row = {
            f"A{i}": K[j][i] - (SIZE_C if i == j else 0)
            for i in range(1, N + 1)
        }
        row["constant"] = K[j][0]
        m_rows[j] = row
    q_rows: dict[int, dict[str, int]] = {}
    for j in (1, 4):
        row = {f"A{i}": K[j][i] for i in range(2, N + 1, 2)}
        row[f"E{j}"] = -1024
        row["constant"] = K[j][0]
        q_rows[j] = row
    combined = add_rows(
        (-147, t_row),
        (-148, p_row),
        (-42, m_rows[1]),
        (-42, m_rows[2]),
        (-7, m_rows[3]),
        (-7, m_rows[4]),
        (8, q_rows[1]),
        (4, q_rows[4]),
    )
    derived = {
        key: json_fraction(value / -2048)
        for key, value in sorted(combined.items())
        if value
    }
    expected = claims["odd_identity51"]
    recorder.require(
        "ODD.IDENTITY51",
        derived == expected,
        {"derived": derived, "claimed": expected},
    )

    weights = {
        "A1": 168,
        "A2": 28,
        "A3": 63,
        "A4": 15,
        "A5": 14,
        "A6": 4,
        "A14": 2,
        "E1": 4,
        "E4": 2,
    }
    names = tuple(weights)
    solutions: list[dict[str, int]] = []

    def visit(index: int, remaining: int, current: dict[str, int]) -> None:
        if index == len(names):
            if remaining == 0 and current["E1"] >= current["A1"] and current["E4"] >= current["A4"]:
                solutions.append(dict(current))
            return
        name = names[index]
        coefficient = weights[name]
        for value in range(remaining // coefficient + 1):
            current[name] = value
            visit(index + 1, remaining - coefficient * value, current)
        current.pop(name, None)

    visit(0, 51, {})
    profiles = sorted({(row["A2"], row["A4"]) for row in solutions})
    claimed_profiles = [tuple(value) for value in claims["odd_profiles"]]
    recorder.require(
        "ODD.PROFILES",
        profiles == claimed_profiles
        and all(row["A1"] == row["A3"] == 0 for row in solutions),
        {
            "profiles": profiles,
            "claimed": claimed_profiles,
            "integer_solutions": len(solutions),
        },
    )
    return {
        "identity": derived,
        "profiles": [list(value) for value in profiles],
        "integer_solutions": len(solutions),
    }


def selfdual_basis() -> list[list[int]]:
    answer = []
    for i in range(8):
        first = linear_power(1, 1, N - 2 * i)
        second = [0] * i + linear_power(1, -1, i)
        answer.append(poly_mul(first, second))
    return answer


def anti_basis() -> list[list[int]]:
    answer = []
    for t in range(7):
        answer.append(
            poly_mul(
                linear_power(1, 1, 13 - 2 * t),
                linear_power(1, -3, 2 * t + 1),
            )
        )
    return answer


def expand_selfdual(
    low_coefficients: Sequence[Affine | Fraction | int],
) -> tuple[list[Affine], list[Affine], list[Affine]]:
    basis = selfdual_basis()
    coefficients: list[Affine] = []
    for weight in range(7):
        target = Affine.coerce(low_coefficients[weight])
        correction = sum(
            (coefficients[index] * basis[index][weight] for index in range(weight)),
            Affine(),
        )
        diagonal = basis[weight][weight]
        if diagonal != 1:
            raise AssertionError(("non-unit triangular basis", weight, diagonal))
        coefficients.append(target - correction)
    shadow_zero_contributions = [
        transform([Fraction(value) for value in row], alternating=True)[0]
        for row in basis
    ]
    numerator = sum(
        (
            coefficients[index] * shadow_zero_contributions[index]
            for index in range(7)
        ),
        Affine(),
    )
    denominator = shadow_zero_contributions[7]
    if denominator:
        coefficients.append(-numerator / denominator)
    else:
        raise AssertionError("unexpected self-dual shadow triangularity")
    enumerator = [
        sum(
            (
                coefficients[index] * basis[index][weight]
                for index in range(8)
            ),
            Affine(),
        )
        for weight in range(N + 1)
    ]
    shadow = transform(enumerator, alternating=True)
    return enumerator, shadow, coefficients


def derive_selfdual_and_anti(
    recorder: Recorder, claims: Mapping[str, Any]
) -> dict[str, Any]:
    basis = selfdual_basis()
    invariant = all(
        transform([Fraction(value) for value in row]) == [Fraction(value) for value in row]
        for row in basis
    )
    recorder.require(
        "EXT.SELFDUAL_BASIS",
        invariant and matrix_rank(basis) == 8,
        {"basis_size": len(basis), "rank": matrix_rank(basis), "fixed": invariant},
    )

    a2, a4 = Affine.variable("A2"), Affine.variable("A4")
    n5, n6 = Affine.variable("N5"), Affine.variable("N6")
    generic_n, generic_t, generic_c = expand_selfdual([1, 0, a2, 0, a4, n5, n6])
    recorder.require(
        "EXT.SHADOW_T0",
        generic_t[0].is_zero() and generic_c[7].is_zero(),
        {"T0": generic_t[0].as_json(), "c7": generic_c[7].as_json()},
    )

    m, r = Affine.variable("m"), Affine.variable("r")
    solution = solve_named_affine(
        [generic_t[2] - Fraction(2, 9) * m, generic_t[4] - Fraction(2, 9) * r],
        ["N5", "N6"],
    )
    average_n = [value.substitute(solution) for value in generic_n]
    average_t = [value.substitute(solution) for value in generic_t]
    average_formulas = {
        "9N5": (average_n[5] * 9).as_json(),
        "9N6": (average_n[6] * 9).as_json(),
        "N14_generic": generic_n[14].as_json(),
        "T2": average_t[2].as_json(),
        "T4": average_t[4].as_json(),
    }
    recorder.require(
        "EXT.AVERAGE_IDENTITIES",
        average_formulas == claims["extension_average_formulas"],
        {"derived": average_formulas, "claimed": claims["extension_average_formulas"]},
    )

    anti = anti_basis()
    anti_fixed = all(
        transform([Fraction(value) for value in row])
        == [-Fraction(value) for value in row]
        for row in anti
    )
    recorder.require(
        "ANTI.BASIS",
        anti_fixed and matrix_rank(anti) == 7,
        {"basis_size": len(anti), "rank": matrix_rank(anti), "anti_fixed": anti_fixed},
    )

    low_matrix = [[anti[row][column] for column in range(7)] for row in range(7)]
    identity_i = solve_affine_system(
        low_matrix,
        [Affine(-anti[row][14]) for row in range(7)],
    )
    identity_i_int = [int(value.constant) for value in identity_i] + [1]
    recorder.require(
        "ANTI.IDENTITY_I",
        all(not value.coefficients and value.constant.denominator == 1 for value in identity_i)
        and identity_i_int == claims["anti_identity_i"],
        {"derived": identity_i_int, "claimed": claims["anti_identity_i"]},
    )

    shadow_s3 = [
        transform([Fraction(value) for value in row], alternating=True)[3] / 2
        for row in anti
    ]
    identity_ii = solve_affine_system(
        low_matrix,
        [Affine(-16 * shadow_s3[row]) for row in range(7)],
    )
    identity_ii_int = [int(value.constant) for value in identity_ii] + [16]
    recorder.require(
        "ANTI.IDENTITY_II",
        all(not value.coefficients and value.constant.denominator == 1 for value in identity_ii)
        and identity_ii_int == claims["anti_identity_ii"],
        {"derived": identity_ii_int, "claimed": claims["anti_identity_ii"]},
    )

    a5, a6 = Affine.variable("A5"), Affine.variable("A6")
    low_a = [Affine(1), Affine(0), a2, Affine(0), a4, a5, a6]
    low_g = [16 * low_a[index] - 9 * average_n[index] for index in range(7)]
    reconstruction_matrix = [
        [anti[column][row] for column in range(7)] for row in range(7)
    ]
    anti_coordinates = solve_affine_system(reconstruction_matrix, low_g)
    full_g = [
        sum(
            (
                anti_coordinates[index] * anti[index][weight]
                for index in range(7)
            ),
            Affine(),
        )
        for weight in range(N + 1)
    ]
    universal_a = [(full_g[index] + 9 * average_n[index]) / 16 for index in range(N + 1)]
    universal_s3 = transform(full_g, alternating=True)[3] / 2
    universal = {
        "A14": universal_a[14].as_json(),
        "S3": universal_s3.as_json(),
    }
    recorder.require(
        "ANTI.UNIVERSAL_BRANCH_FORMULAS",
        universal == claims["universal_branch_formulas"],
        {"derived": universal, "claimed": claims["universal_branch_formulas"]},
    )
    return {
        "basis": basis,
        "average_n": average_n,
        "average_t": average_t,
        "anti_basis": anti,
        "universal_a": universal_a,
        "universal_s3": universal_s3,
        "facts": {
            "average_formulas": average_formulas,
            "identity_i": identity_i_int,
            "identity_ii": identity_ii_int,
            "universal": universal,
        },
    }


def derive_geometry(recorder: Recorder, claims: Mapping[str, Any]) -> dict[str, Any]:
    local_ok = True
    for left, right in product(range(4), repeat=2):
        left_x, left_z = left & 1, (left >> 1) & 1
        right_x, right_z = right & 1, (right >> 1) & 1
        bracket = (left_x * right_z + left_z * right_x) & 1
        local_ok &= (
            int(bool(left ^ right))
            == (int(bool(left)) + int(bool(right)) + bracket) % 2
        )
    recorder.require(
        "ALG.QFORM.POLAR",
        local_ok,
        {"local_pairs_checked": 16},
    )

    k_square = [
        [sum(K[row][middle] * K[middle][column] for middle in range(N + 1)) for column in range(N + 1)]
        for row in range(N + 1)
    ]
    expected_diagonal = 1 << (2 * N)
    k_ok = all(
        k_square[row][column] == (expected_diagonal if row == column else 0)
        for row in range(N + 1)
        for column in range(N + 1)
    )
    recorder.require(
        "ALG.KRAW.K2",
        k_ok,
        {"dimension": 15, "diagonal": expected_diagonal},
    )

    subspaces = enumerate_subspaces(6, 3)
    lagrangians = [
        subspace
        for subspace in subspaces
        if all(symplectic(left, right, 3) == 0 for left in subspace for right in subspace)
    ]
    incidences = {
        point: sum(point in lagrangian for lagrangian in lagrangians)
        for point in range(1, 64)
    }
    six_d = {
        "subspaces": len(subspaces),
        "lagrangians": len(lagrangians),
        "point_incidence_min": min(incidences.values()),
        "point_incidence_max": max(incidences.values()),
        "double_count": sum(len(space) - 1 for space in lagrangians),
    }
    recorder.require(
        "EXT.LAGRANGIAN_6D",
        six_d == claims["lagrangian_6d"],
        {"derived": six_d, "claimed": claims["lagrangian_6d"]},
    )

    # Canonical O^+(8,2) quotient, with r anisotropic.
    r_vector = 1 | (1 << 4)
    candidates = [
        value
        for value in range(1, 256)
        if value != r_vector and symplectic(value, r_vector, 4) == 0
    ]
    extensions: set[tuple[int, ...]] = set()
    for a, b, c in combinations(candidates, 3):
        generators = (r_vector, a, b, c)
        if gf2_rank(generators) != 4:
            continue
        if any(
            symplectic(generators[i], generators[j], 4)
            for i in range(4)
            for j in range(i + 1, 4)
        ):
            continue
        extensions.add(span(generators))
    eligible = [
        value
        for value in range(256)
        if quadratic(value, 4) == 0
        and symplectic(value, r_vector, 4) == 1
    ]
    shadow_incidence: Counter[int] = Counter()
    shadow_sizes: set[int] = set()
    shadow_parities: set[int] = set()
    for extension in extensions:
        shadow = [
            h
            for h in range(256)
            if all(
                symplectic(h, d, 4) == quadratic(d, 4)
                for d in extension
            )
        ]
        shadow_sizes.add(len(shadow))
        shadow_parities.update(quadratic(h, 4) for h in shadow)
        shadow_incidence.update(shadow)
    incidence_values = [shadow_incidence[value] for value in eligible]

    anisotropic = {value for value in range(256) if quadratic(value, 4) == 1}
    orbit = {r_vector}
    changed = True
    while changed:
        changed = False
        for value in tuple(orbit):
            for axis in anisotropic:
                image = value ^ (axis if symplectic(value, axis, 4) else 0)
                if image not in orbit:
                    orbit.add(image)
                    changed = True
    eight_d = {
        "extensions": len(extensions),
        "eligible_even_vectors": len(eligible),
        "shadow_sizes": sorted(shadow_sizes),
        "shadow_parities": sorted(shadow_parities),
        "eligible_incidence_min": min(incidence_values),
        "eligible_incidence_max": max(incidence_values),
        "total_incidence": sum(shadow_incidence.values()),
        "anisotropic_vectors": len(anisotropic),
        "anisotropic_orbit": len(orbit),
    }
    recorder.require(
        "EXT.SHADOW_INCIDENCE_8D",
        eight_d == claims["shadow_incidence_8d"]
        and orbit == anisotropic
        and all(
            count == 0
            for value, count in shadow_incidence.items()
            if value not in eligible
        ),
        {"derived": eight_d, "claimed": claims["shadow_incidence_8d"]},
    )
    return {"lagrangian_6d": six_d, "shadow_incidence_8d": eight_d}


def affine_equal(left: Affine, right: Affine | Fraction | int) -> bool:
    return (left - right).is_zero()


def branch_substitution(
    algebra: Mapping[str, Any], substitutions: Mapping[str, Affine | Fraction | int]
) -> tuple[list[Affine], Affine]:
    return (
        [value.substitute(substitutions) for value in algebra["universal_a"]],
        algebra["universal_s3"].substitute(substitutions),
    )


def derive_p11(
    recorder: Recorder, claims: Mapping[str, Any], algebra: Mapping[str, Any]
) -> dict[str, Any]:
    overlap_cases = []
    for intersection in range(3):
        for equal in range(intersection + 1):
            if (intersection - equal) % 2:
                continue
            overlap_cases.append(
                {
                    "intersection": intersection,
                    "equal": equal,
                    "sum_weight": 6 - intersection - equal,
                }
            )
    admissible = [
        row
        for row in overlap_cases
        if row["sum_weight"] not in (2, 4)
    ]
    recorder.require(
        "P11.OVERLAP",
        admissible == [{"intersection": 0, "equal": 0, "sum_weight": 6}],
        {"commuting_cases": overlap_cases, "admissible": admissible},
    )

    possibilities = []
    for a5 in range(4):
        for a6 in range(1, 14):
            for a14 in range(4):
                for s1 in range(3):
                    for s4 in range(4):
                        if 14 * a5 + 4 * a6 + 2 * a14 + 4 * s1 + 2 * s4 == 6:
                            possibilities.append((a5, a6, a14, s1, s4))
    expected_possibilities = [(0, 1, 0, 0, 1), (0, 1, 1, 0, 0)]
    recorder.require(
        "P11.IDENTITY_BRANCH",
        possibilities == expected_possibilities,
        {"possibilities": possibilities},
    )

    universal_a14 = algebra["universal_a"][14].substitute(
        {"A2": 1, "A4": 1, "A5": 0, "A6": 1}
    )
    results = []
    for _a5, _a6, a14, _s1, s4 in possibilities:
        equation = universal_a14.substitute({"r": s4}) - a14
        solved = solve_named_affine([equation], ["m"])["m"]
        results.append({"A14": a14, "S4": s4, "required_S2": json_fraction(solved.constant)})
    recorder.require(
        "P11.INTEGRALITY",
        results == claims["p11_integrality"]
        and all("/" in str(row["required_S2"]) for row in results),
        {"derived": results, "claimed": claims["p11_integrality"]},
    )
    return {"overlap_cases": overlap_cases, "integrality": results}


def derive_p01_formulas(algebra: Mapping[str, Any]) -> dict[str, Affine]:
    a, b, s = Affine.variable("a"), Affine.variable("b"), Affine.variable("s")
    c = algebra["universal_a"][14].substitute(
        {"A2": 0, "A4": 1, "A5": a, "A6": b}
    )
    # The regenerated 51 identity specialized to profile (0,1).
    equation = 15 + 14 * a + 4 * b + 2 * c + 4 * s + 2 * (1 + Affine.variable("r")) - 51
    b_solution = solve_named_affine([equation], ["b"])["b"]
    substitutions = {"b": b_solution, "A6": b_solution}
    return {
        "b": b_solution,
        "c": c.substitute(substitutions),
        "S3": algebra["universal_s3"]
        .substitute({"A2": 0, "A4": 1, "A5": a, "A6": b})
        .substitute(substitutions),
    }


def derive_p01(
    recorder: Recorder,
    claims: Mapping[str, Any],
    algebra: Mapping[str, Any],
    words: Sequence[int],
) -> dict[str, Any]:
    formulas = derive_p01_formulas(algebra)
    formula_json = {key: value.as_json() for key, value in formulas.items()}
    recorder.require(
        "P01.FORMULAS",
        formula_json == claims["p01_formulas"],
        {"derived": formula_json, "claimed": claims["p01_formulas"]},
    )

    # The unique weight-four stabilizer is normalized by LC/permutation.
    u = pack_string("XXXXIIIIIIIIII")
    weight_one = [
        pack_symbols([label if coordinate == position else 0 for coordinate in range(N)])
        for position in range(N)
        for label in (1, 2, 3)
    ]
    s1_pair_max = max(
        pauli_weight(left ^ right)
        for left, right in combinations(weight_one, 2)
    )
    recorder.require(
        "P01.S1",
        len(weight_one) == 42 and s1_pair_max <= 2,
        {"weight_one_words": len(weight_one), "maximum_pair_difference_weight": s1_pair_max},
    )

    s1_to_s2_max = 0
    s1_to_s3_candidates: Counter[int] = Counter()
    # Enumerate weight two directly, without touching the 2^28 ambient space.
    w2: list[int] = []
    for support in combinations(range(N), 2):
        for labels in product((1, 2, 3), repeat=2):
            symbols = [0] * N
            for coordinate, label in zip(support, labels):
                symbols[coordinate] = label
            w2.append(pack_symbols(symbols))
    for h in weight_one:
        s1_to_s2_max = max(s1_to_s2_max, *(pauli_weight(h ^ v) for v in w2))
        candidate = h ^ u
        if pauli_weight(candidate) == 3:
            s1_to_s3_candidates[h] += 1
    recorder.require(
        "P01.S1_TRANSLATIONS",
        len(w2) == 819
        and all(count <= 1 for count in s1_to_s3_candidates.values())
        and s1_to_s2_max <= 3,
        {
            "weight_two_words": len(w2),
            "maximum_weight1_weight2_difference": s1_to_s2_max,
            "maximum_weight3_translate_count": max(s1_to_s3_candidates.values(), default=0),
        },
    )

    collision_pairs: list[tuple[int, int]] = []
    collision_bin_counts: list[int] = []
    for g in words:
        if symplectic(g, u, N):
            continue
        h = g ^ u
        shared = pauli_incidences(g) & pauli_incidences(h)
        if pauli_weight(h) == 3 and shared and g < h:
            collision_pairs.append((g, h))
            collision_bin_counts.append(len(shared))
    mutually_compatible = 0
    for first, second in combinations(collision_pairs, 2):
        if all(
            (left ^ right) == u or pauli_weight(left ^ right) >= 5
            for left in first
            for right in second
        ):
            mutually_compatible += 1
    collision_fact = {
        "pairs": len(collision_pairs),
        "pair_pairs_checked": comb(len(collision_pairs), 2),
        "mutually_compatible_pair_pairs": mutually_compatible,
        "shared_bins_min": min(collision_bin_counts),
        "shared_bins_max": max(collision_bin_counts),
    }
    recorder.require(
        "P01.COLLISION_90",
        collision_fact == claims["p01_collision"],
        {"derived": collision_fact, "claimed": claims["p01_collision"]},
    )

    # Normalize the unique weight-two shadow word to XX.  The distance and
    # parity-kernel argument first proves wt(h+g)=5.  The coordinate categories
    # then force disjoint support, which in turn implies that h and g commute.
    # Exhaust all 9,828 g and verify the resulting disjoint-support condition,
    # leaving 12*3=36 incidence bins.  The explicit commutation filter below is
    # therefore redundant but harmless; it is retained as a consistency check.
    shadow_h = pack_string("XXIIIIIIIIIIII")
    shadow_h_support = {
        coordinate
        for coordinate, _label in pauli_incidences(shadow_h)
    }
    admissible_w3 = [
        g
        for g in words
        if symplectic(shadow_h, g, N) == 0
        and pauli_weight(shadow_h ^ g) == 5
    ]
    disjoint_w3 = [
        g
        for g in words
        if not (
            shadow_h_support
            & {coordinate for coordinate, _label in pauli_incidences(g)}
        )
    ]
    admissible_bins = {
        incidence
        for g in admissible_w3
        for incidence in pauli_incidences(g)
    }
    recorder.require(
        "P01.BINS_36",
        set(admissible_w3) == set(disjoint_w3)
        and len(admissible_w3) == comb(12, 3) * 3**3
        and len(admissible_bins) == 36
        and (36 + 1) // 3 == 12,
        {
            "canonical_weight_two_shadow": "XXIIIIIIIIIIII",
            "weight_three_words_checked": len(words),
            "admissible_weight_three_words": len(admissible_w3),
            "disjoint_weight_three_words": len(disjoint_w3),
            "support_disjointness_equivalent": set(admissible_w3) == set(disjoint_w3),
            "remaining_bins": len(admissible_bins),
            "integer_upper_bound": 12,
        },
    )

    # Machine-check the elementary occupancy inequality used for 42 and 36 bins.
    occupancy_ok = all(comb(multiplicity, 2) >= multiplicity - 1 for multiplicity in range(73))
    recorder.require(
        "P01.BINS_42",
        occupancy_ok and (42 + 1) // 3 == 14,
        {"bins": 42, "incidence_bound": "3*S3-1<=42", "integer_upper_bound": 14},
    )

    def ledger(use_42: bool = True, use_36: bool = True) -> list[dict[str, int]]:
        survivors: list[dict[str, int]] = []
        for s in range(2):
            for a in range(3):
                for m in range(4):
                    for r in range(12):
                        substitutions = {"s": s, "a": a, "m": m, "r": r}
                        b = formulas["b"].substitute(substitutions).constant
                        c = formulas["c"].substitute(substitutions).constant
                        s3 = formulas["S3"].substitute(substitutions).constant
                        if any(value.denominator != 1 or value < 0 for value in (b, c, s3)):
                            continue
                        row = {
                            "s": s,
                            "a": a,
                            "m": m,
                            "r": r,
                            "b": int(b),
                            "c": int(c),
                            "S3": int(s3),
                        }
                        if s == 1:
                            if m != 0 or s3 > 1:
                                continue
                        else:
                            if use_42 and s3 > 14:
                                continue
                            if m == 1 and use_36 and s3 > 12:
                                continue
                        survivors.append(row)
        return survivors

    survivors = ledger()
    without_42 = ledger(use_42=False)
    without_36 = ledger(use_36=False)
    recorder.require(
        "P01.EXHAUSTED",
        not survivors and without_42 and without_36,
        {
            "survivors": survivors,
            "without_42_count": len(without_42),
            "without_36_count": len(without_36),
            "without_36": without_36,
        },
    )
    return {
        "formulas": formula_json,
        "collision": collision_fact,
        "ledger_survivors": survivors,
        "mutation_survivors": {
            "without_42": len(without_42),
            "without_36": len(without_36),
        },
    }


def normal_form_representatives() -> dict[str, list[str]]:
    return {
        "independent": [
            "XXXXIIIIIIIIII",
            "IIIIXXXXIIIIII",
            "IIIIIIIIXXXXII",
        ],
        "p0": [
            "XXXXIIIIIIIIII",
            "ZZZZIIIIIIIIII",
            "YYYYIIIIIIIIII",
        ],
        "p1": [
            "XIXXXIIIIIIIII",
            "IXXZZIIIIIIIII",
            "XXIYYIIIIIIIII",
        ],
        "p2": [
            "XXIIXXIIIIIIII",
            "IIXXXXIIIIIIII",
            "XXXXIIIIIIIIII",
        ],
    }


def derive_normal_forms(recorder: Recorder, claims: Mapping[str, Any]) -> dict[str, Any]:
    symbol_permutations = list(permutations((1, 2, 3)))

    def act(pair: tuple[int, int], permutation: tuple[int, int, int]) -> tuple[int, int]:
        mapping = {0: 0, 1: permutation[0], 2: permutation[1], 3: permutation[2]}
        return mapping[pair[0]], mapping[pair[1]]

    unseen = set(product(range(4), repeat=2))
    local_orbits: list[list[tuple[int, int]]] = []
    while unseen:
        seed = min(unseen)
        orbit = sorted({act(seed, permutation) for permutation in symbol_permutations})
        local_orbits.append(orbit)
        unseen -= set(orbit)
    orbit_signatures = sorted(
        (
            len(orbit),
            int(orbit[0][0] != 0),
            int(orbit[0][1] != 0),
            int(
                orbit[0][0] != 0
                and orbit[0][1] != 0
                and orbit[0][0] == orbit[0][1]
            ),
        )
        for orbit in local_orbits
    )

    rank2_solutions = []
    for a, b, c, d in product(range(5), repeat=4):
        if a + c + d == b + c + d == a + b + d == 4 and d % 2 == 0:
            rank2_solutions.append({"A": a, "B": b, "C": c, "D": d})
    rank3_pair_solutions = []
    for a, b, c, d in product(range(9), repeat=4):
        if a + c + d == 4 and b + c + d == 4 and a + b + d == 8 and d % 2 == 0:
            rank3_pair_solutions.append({"A": a, "B": b, "C": c, "D": d})

    representatives = normal_form_representatives()
    validation: dict[str, Any] = {}
    for name, strings in representatives.items():
        generators = [pack_string(word) for word in strings]
        generated = span(generators)
        weight_distribution = Counter(pauli_weight(value) for value in generated)
        validation[name] = {
            "rank": gf2_rank(generators),
            "commuting": all(
                symplectic(left, right, N) == 0
                for left, right in combinations(generators, 2)
            ),
            "nonzero_weight_distribution": {
                str(weight): count
                for weight, count in sorted(weight_distribution.items())
                if weight
            },
        }
    facts = {
        "local_orbit_count": len(local_orbits),
        "local_orbit_signatures": [list(value) for value in orbit_signatures],
        "rank2_category_solutions": rank2_solutions,
        "rank3_pair_solutions": rank3_pair_solutions,
        "representatives": representatives,
        "validation": validation,
    }
    representative_validation_ok = (
        validation["independent"]
        == {
            "rank": 3,
            "commuting": True,
            "nonzero_weight_distribution": {"4": 3, "8": 3, "12": 1},
        }
        and all(
            validation[name]
            == {
                "rank": 2,
                "commuting": True,
                "nonzero_weight_distribution": {"4": 3},
            }
            for name in ("p0", "p1", "p2")
        )
    )
    recorder.require(
        "P03.NORMAL_FORMS_4",
        rank2_solutions
        == [
            {"A": 0, "B": 0, "C": 0, "D": 4},
            {"A": 1, "B": 1, "C": 1, "D": 2},
            {"A": 2, "B": 2, "C": 2, "D": 0},
        ]
        and rank3_pair_solutions == [{"A": 4, "B": 4, "C": 0, "D": 0}]
        and representatives == claims["normal_forms"]
        and len(local_orbits) == 5
        and orbit_signatures
        == [
            (1, 0, 0, 0),
            (3, 0, 1, 0),
            (3, 1, 0, 0),
            (3, 1, 1, 1),
            (6, 1, 1, 0),
        ]
        and representative_validation_ok,
        {"derived": facts, "claimed_representatives": claims["normal_forms"]},
    )
    return facts


def collision_tables(
    recorder: Recorder,
    claims: Mapping[str, Any],
    words: Sequence[int],
    representatives: Mapping[str, Sequence[str]],
) -> dict[str, Any]:
    derived: dict[str, Any] = {}
    for name, strings in representatives.items():
        stabilizers = [pack_string(word) for word in strings]
        full_histogram: Counter[int] = Counter()
        commuting_histogram: Counter[int] = Counter()
        shared_bin_sizes: set[int] = set()
        for word in words:
            degree = 0
            for stabilizer in stabilizers:
                translated = word ^ stabilizer
                shared = pauli_incidences(word) & pauli_incidences(translated)
                if pauli_weight(translated) == 3 and shared:
                    degree += 1
                    shared_bin_sizes.add(len(shared))
            full_histogram[degree] += 1
            if all(symplectic(word, stabilizer, N) == 0 for stabilizer in stabilizers):
                commuting_histogram[degree] += 1
        maximum_degree = max(full_histogram)
        full = [full_histogram[index] for index in range(maximum_degree + 1)]
        commuting = [
            commuting_histogram[index] for index in range(maximum_degree + 1)
        ]
        degrees = sorted(
            (
                degree
                for degree, count in commuting_histogram.items()
                for _ in range(count)
            ),
            reverse=True,
        )
        upper_bound = sum(degrees[:24]) // 2
        derived[name] = {
            "all_words": full,
            "commuting_words": commuting,
            "commuting_total": sum(commuting),
            "maximum_degree": maximum_degree,
            "top24_edge_upper_bound": upper_bound,
            "edge_shared_bin_sizes": sorted(shared_bin_sizes),
        }
    recorder.require(
        "P03.WORDS_9828",
        len(words) == comb(14, 3) * 3**3 == 9828 and len(set(words)) == len(words),
        {"generated": len(words), "unique": len(set(words)), "formula": 9828},
    )
    recorder.require(
        "P03.DEGREE_HISTOGRAMS",
        derived == claims["collision_tables"],
        {"derived": derived, "claimed": claims["collision_tables"]},
    )
    occupancy_inequality = all(
        comb(multiplicity, 2) >= multiplicity - 1
        for multiplicity in range(73)
    )
    upper_bounds = [derived[name]["top24_edge_upper_bound"] for name in sorted(derived)]
    recorder.require(
        "P03.COLLISION_CONTRADICTION",
        occupancy_inequality
        and 72 - 42 == 30
        and all(bound < 30 for bound in upper_bounds),
        {"lower_bound": 30, "upper_bounds": dict(zip(sorted(derived), upper_bounds))},
    )
    return derived


def evaluate_affine(value: Affine) -> int:
    if value.coefficients or value.constant.denominator != 1:
        raise AssertionError(value)
    return int(value.constant)


def derive_p03(
    recorder: Recorder,
    claims: Mapping[str, Any],
    algebra: Mapping[str, Any],
    normal_forms: Mapping[str, Any],
    words: Sequence[int],
) -> dict[str, Any]:
    # In profile (A2,A4)=(0,3), the regenerated 51 identity has already
    # contributed exactly 51 through 15*A4+2*E4 with E4=A4+S4.
    # Its remaining nonnegative terms must therefore all vanish.
    branch_solutions = []
    for a5, a6, a14, s1, s4 in product(range(2), repeat=5):
        remainder = 14 * a5 + 4 * a6 + 2 * a14 + 4 * s1 + 2 * s4
        if remainder == 0:
            branch_solutions.append(
                {"A5": a5, "A6": a6, "A14": a14, "S1": s1, "S4": s4}
            )
    forced_zero = {"A5": 0, "A6": 0, "A14": 0, "S1": 0, "S4": 0}
    recorder.require(
        "P03.IDENTITY_BRANCH",
        branch_solutions == [forced_zero],
        {
            "identity_remainder": "14*A5+4*A6+2*A14+4*S1+2*S4=0",
            "nonnegative_solutions": branch_solutions,
        },
    )
    a14_pre = algebra["universal_a"][14].substitute(
        {
            "A2": 0,
            "A4": 3,
            "A5": forced_zero["A5"],
            "A6": forced_zero["A6"],
            "r": forced_zero["S4"],
        }
    )
    m_solution = solve_named_affine([a14_pre], ["m"])["m"]
    substitutions = {
        "A2": 0,
        "A4": 3,
        "A5": forced_zero["A5"],
        "A6": forced_zero["A6"],
        "m": m_solution,
        "r": forced_zero["S4"],
    }
    full_a = [value.substitute(substitutions) for value in algebra["universal_a"]]
    a = [evaluate_affine(value) for value in full_a]
    b = [
        evaluate_affine(value)
        for value in [8 * entry for entry in transform([Affine(value) for value in a])]
    ]
    s = [
        evaluate_affine(value)
        for value in [8 * entry for entry in transform([Affine(value) for value in a], alternating=True)]
    ]
    n = [
        evaluate_affine(value.substitute(substitutions))
        for value in algebra["average_n"]
    ]
    t = [
        evaluate_affine(value)
        for value in transform([Affine(value) for value in n], alternating=True)
    ]
    enumerators = {"A": a, "B": b, "S": s, "N": n, "T": t}
    recorder.require(
        "ENUM.P03_FULL",
        enumerators == claims["p03_enumerators"]
        and sum(a) == 1 << 11
        and sum(b) == 1 << 17
        and sum(s) == 1 << 17
        and sum(n) == sum(t) == 1 << 14,
        {"derived": enumerators, "claimed": claims["p03_enumerators"]},
    )
    s3 = algebra["universal_s3"].substitute(substitutions)
    recorder.require(
        "P03.PROFILE_ALGEBRA",
        m_solution.is_zero() and evaluate_affine(s3) == 24,
        {"S2": m_solution.as_json(), "S3": evaluate_affine(s3)},
    )
    collisions = collision_tables(
        recorder, claims, words, normal_forms["representatives"]
    )
    return {"enumerators": enumerators, "collisions": collisions}


def apply_mutation(claims: Any, mutation_path: Path | None) -> Any:
    if mutation_path is None:
        return claims
    mutation = json.loads(mutation_path.read_text(encoding="utf-8"))
    path = mutation["path"]
    current = claims
    for key in path[:-1]:
        current = current[key] if isinstance(key, str) else current[key]
    current[path[-1]] = mutation["value"]
    return claims


def load_claims(path: Path, mutation: Path | None) -> dict[str, Any]:
    claims = json.loads(path.read_text(encoding="utf-8"))
    return apply_mutation(claims, mutation)


def run(claims: Mapping[str, Any]) -> dict[str, Any]:
    recorder = Recorder({})
    geometry = derive_geometry(recorder, claims)
    even = derive_even_branch(recorder, claims)
    odd = derive_odd_identity(recorder, claims)
    algebra = derive_selfdual_and_anti(recorder, claims)
    words = weight_three_words()
    p11 = derive_p11(recorder, claims, algebra)
    p01 = derive_p01(recorder, claims, algebra, words)
    normal_forms = derive_normal_forms(recorder, claims)
    p03 = derive_p03(recorder, claims, algebra, normal_forms, words)

    missing = sorted(set(claims["required_checks"]) - set(recorder.checks))
    recorder.require(
        "COVERAGE.REQUIRED",
        not missing,
        {"missing": missing, "completed_before_coverage": len(recorder.checks)},
    )
    return {
        "schema": "quantum-14-3-5-primary-proof-v1",
        "verdict": "PASS",
        "claim_status": "machine-verified proof artifact; see the accompanying paper",
        "arithmetic": "exact integers and fractions only",
        "checks": recorder.checks,
        "facts": {
            "geometry": geometry,
            "even": even,
            "odd": odd,
            "algebra": algebra["facts"],
            "p11": p11,
            "p01": p01,
            "normal_forms": normal_forms,
            "p03": p03,
        },
    }


def parse_args(argv: Sequence[str]) -> argparse.Namespace:
    root = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser()
    parser.add_argument("--claims", type=Path, default=root / "claims" / "theorem.json")
    parser.add_argument("--mutation", type=Path)
    parser.add_argument("--output", type=Path)
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    arguments = parse_args(argv or sys.argv[1:])
    try:
        claims = load_claims(arguments.claims, arguments.mutation)
        result = run(claims)
    except CheckFailure as error:
        print(f"FAIL {error.check_id}: {error.detail}", file=sys.stderr)
        return 2
    serialized = json.dumps(result, sort_keys=True, indent=2) + "\n"
    if arguments.output:
        arguments.output.write_text(serialized, encoding="utf-8")
    else:
        sys.stdout.write(serialized)
    print(
        f"PASS primary checks={len(result['checks'])} "
        "status=machine-verified",
        file=sys.stderr,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
