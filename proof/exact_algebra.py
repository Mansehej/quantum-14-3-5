#!/usr/bin/env python3
"""Exact algebra certificate for the [[14,3,5]] nonexistence proof.

This module deliberately uses only Python's standard library and
``fractions.Fraction``.  Every polynomial, row reduction, transform, and
enumerator in the returned certificate is regenerated when
``build_certificate`` is called.

The finite incidence and collision enumerators live in separate modules.  This
file covers the algebraic half of the certificate and records precisely where
it consumes the incidence bounds proved by those modules.
"""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass
from fractions import Fraction
from functools import reduce
from math import comb, gcd
from typing import Callable, Iterable, Mapping, Sequence


N = 14
STABILIZER_SIZE = 2**11


def _lcm(a: int, b: int) -> int:
    if not a or not b:
        return 0
    return abs(a // gcd(a, b) * b)


def _lcm_many(values: Iterable[int]) -> int:
    return reduce(_lcm, values, 1)


def krawtchouk(j: int, i: int, n: int = N) -> int:
    """Return the q=4 Krawtchouk coefficient K_j(i), exactly."""

    total = 0
    for ell in range(j + 1):
        if ell <= i and j - ell <= n - i:
            total += (
                (-1) ** ell
                * 3 ** (j - ell)
                * comb(i, ell)
                * comb(n - i, j - ell)
            )
    return total


def poly_add(a: Sequence[Fraction], b: Sequence[Fraction]) -> list[Fraction]:
    size = max(len(a), len(b))
    out = [Fraction(0) for _ in range(size)]
    for i, value in enumerate(a):
        out[i] += value
    for i, value in enumerate(b):
        out[i] += value
    return out


def poly_scale(a: Sequence[Fraction], scalar: Fraction | int) -> list[Fraction]:
    scalar = Fraction(scalar)
    return [scalar * value for value in a]


def poly_mul(a: Sequence[Fraction], b: Sequence[Fraction]) -> list[Fraction]:
    out = [Fraction(0) for _ in range(len(a) + len(b) - 1)]
    for i, left in enumerate(a):
        for j, right in enumerate(b):
            out[i + j] += left * right
    return out


def poly_pow(a: Sequence[Fraction], exponent: int) -> list[Fraction]:
    out = [Fraction(1)]
    base = list(a)
    power = exponent
    while power:
        if power & 1:
            out = poly_mul(out, base)
        base = poly_mul(base, base)
        power >>= 1
    return out


def homogeneous_substitute(
    polynomial: Sequence[Fraction],
    first: Sequence[Fraction],
    second: Sequence[Fraction],
    scale: Fraction | int = 1,
) -> list[Fraction]:
    """Substitute two linear forms in a homogeneous weight enumerator.

    ``polynomial[w]`` is the coefficient of x^(n-w)y^w.  ``first`` and
    ``second`` contain the x and y coefficients of the substituted x and y.
    """

    degree = len(polynomial) - 1
    out = [Fraction(0) for _ in range(degree + 1)]
    for weight, coefficient in enumerate(polynomial):
        term = poly_mul(
            poly_pow(first, degree - weight),
            poly_pow(second, weight),
        )
        for index, value in enumerate(term):
            out[index] += coefficient * value
    divisor = Fraction(scale)
    return [value / divisor for value in out]


def macwilliams_normalized(polynomial: Sequence[Fraction]) -> list[Fraction]:
    """M(W)=2^-14 W(x+3y,x-y)."""

    return homogeneous_substitute(
        polynomial, [Fraction(1), Fraction(3)], [Fraction(1), Fraction(-1)], 2**N
    )


def shadow_transform_selfdual(polynomial: Sequence[Fraction]) -> list[Fraction]:
    """R(W)=2^-14 W(x+3y,y-x), the self-dual shadow transform."""

    return homogeneous_substitute(
        polynomial, [Fraction(1), Fraction(3)], [Fraction(-1), Fraction(1)], 2**N
    )


def global_shadow_transform(polynomial: Sequence[Fraction]) -> list[Fraction]:
    """S=2^-11 A(x+3y,y-x) for an odd stabilizer C."""

    return homogeneous_substitute(
        polynomial,
        [Fraction(1), Fraction(3)],
        [Fraction(-1), Fraction(1)],
        STABILIZER_SIZE,
    )


def rref(
    matrix: Sequence[Sequence[Fraction | int]],
    pivot_columns: int | None = None,
) -> tuple[list[list[Fraction]], list[int]]:
    """Compute deterministic exact reduced row echelon form."""

    work = [[Fraction(value) for value in row] for row in matrix]
    if not work:
        return [], []
    columns = len(work[0]) if pivot_columns is None else pivot_columns
    pivot_row = 0
    pivots: list[int] = []
    for column in range(columns):
        selected = next(
            (row for row in range(pivot_row, len(work)) if work[row][column]),
            None,
        )
        if selected is None:
            continue
        work[pivot_row], work[selected] = work[selected], work[pivot_row]
        divisor = work[pivot_row][column]
        work[pivot_row] = [value / divisor for value in work[pivot_row]]
        for row in range(len(work)):
            if row == pivot_row:
                continue
            multiple = work[row][column]
            if multiple:
                work[row] = [
                    value - multiple * pivot
                    for value, pivot in zip(work[row], work[pivot_row])
                ]
        pivots.append(column)
        pivot_row += 1
        if pivot_row == len(work):
            break
    return work, pivots


def solve_square(
    matrix: Sequence[Sequence[Fraction | int]],
    right_hand_side: Sequence[Fraction | int],
) -> list[Fraction]:
    size = len(matrix)
    if size != len(right_hand_side) or any(len(row) != size for row in matrix):
        raise ValueError("solve_square requires a square matrix")
    augmented = [
        [Fraction(value) for value in row] + [Fraction(right_hand_side[index])]
        for index, row in enumerate(matrix)
    ]
    reduced, pivots = rref(augmented, pivot_columns=size)
    if pivots != list(range(size)):
        raise ValueError("singular exact system")
    return [reduced[index][-1] for index in range(size)]


def nullspace(matrix: Sequence[Sequence[Fraction | int]]) -> list[list[Fraction]]:
    if not matrix:
        return []
    columns = len(matrix[0])
    reduced, pivots = rref(matrix, pivot_columns=columns)
    free = [column for column in range(columns) if column not in pivots]
    vectors: list[list[Fraction]] = []
    for free_column in free:
        vector = [Fraction(0) for _ in range(columns)]
        vector[free_column] = Fraction(1)
        for row, pivot in enumerate(pivots):
            vector[pivot] = -reduced[row][free_column]
        vectors.append(vector)
    return vectors


def canonical_integer_vector(vector: Sequence[Fraction]) -> list[int]:
    denominator = _lcm_many(value.denominator for value in vector)
    integers = [int(value * denominator) for value in vector]
    common = reduce(gcd, (abs(value) for value in integers if value), 0)
    if common:
        integers = [value // common for value in integers]
    last_nonzero = next((value for value in reversed(integers) if value), 1)
    if last_nonzero < 0:
        integers = [-value for value in integers]
    return integers


@dataclass(frozen=True)
class Linear:
    """A small exact affine-linear expression."""

    terms: Mapping[str, Fraction]

    @staticmethod
    def constant(value: Fraction | int) -> "Linear":
        value = Fraction(value)
        return Linear({} if value == 0 else {"$": value})

    @staticmethod
    def variable(name: str) -> "Linear":
        return Linear({name: Fraction(1)})

    def coefficient(self, name: str) -> Fraction:
        return self.terms.get(name, Fraction(0))

    def __add__(self, other: "Linear" | Fraction | int) -> "Linear":
        if not isinstance(other, Linear):
            other = Linear.constant(other)
        result = dict(self.terms)
        for name, value in other.terms.items():
            result[name] = result.get(name, Fraction(0)) + value
            if result[name] == 0:
                del result[name]
        return Linear(result)

    def __radd__(self, other: "Linear" | Fraction | int) -> "Linear":
        return self + other

    def __neg__(self) -> "Linear":
        return Linear({name: -value for name, value in self.terms.items()})

    def __sub__(self, other: "Linear" | Fraction | int) -> "Linear":
        if not isinstance(other, Linear):
            other = Linear.constant(other)
        return self + (-other)

    def __rsub__(self, other: "Linear" | Fraction | int) -> "Linear":
        return Linear.constant(other) - self

    def __mul__(self, scalar: Fraction | int) -> "Linear":
        scalar = Fraction(scalar)
        return Linear(
            {name: value * scalar for name, value in self.terms.items() if value * scalar}
        )

    def __rmul__(self, scalar: Fraction | int) -> "Linear":
        return self * scalar

    def substitute(self, name: str, replacement: "Linear") -> "Linear":
        coefficient = self.coefficient(name)
        remaining = Linear(
            {key: value for key, value in self.terms.items() if key != name}
        )
        return remaining + coefficient * replacement

    def evaluate(self, values: Mapping[str, Fraction | int]) -> Fraction:
        total = self.coefficient("$")
        for name, coefficient in self.terms.items():
            if name != "$":
                total += coefficient * Fraction(values[name])
        return total

    def as_dict(self) -> dict[str, Fraction]:
        ordered: dict[str, Fraction] = {}
        if "$" in self.terms:
            ordered["constant"] = self.terms["$"]
        for name in sorted(key for key in self.terms if key != "$"):
            ordered[name] = self.terms[name]
        return ordered


def solve_linear_expression(expression: Linear, variable: str) -> Linear:
    coefficient = expression.coefficient(variable)
    if coefficient == 0:
        raise ValueError(f"cannot solve expression for absent variable {variable}")
    rest = expression.substitute(variable, Linear.constant(0))
    return rest * (-1 / coefficient)


def gleason_basis(index: int) -> list[Fraction]:
    """(x+y)^(14-2i) [y(x-y)]^i."""

    if not 0 <= index <= 7:
        raise ValueError("Gleason basis index must lie in [0,7]")
    return poly_mul(
        poly_pow([Fraction(1), Fraction(1)], N - 2 * index),
        [Fraction(0)] * index
        + poly_pow([Fraction(1), Fraction(-1)], index),
    )


GLEASON_BASIS = [gleason_basis(index) for index in range(8)]


def combine_polynomials(
    coefficients: Sequence[Fraction | int],
    basis: Sequence[Sequence[Fraction]] = GLEASON_BASIS,
) -> list[Fraction]:
    out = [Fraction(0) for _ in range(N + 1)]
    for coefficient, polynomial in zip(coefficients, basis):
        out = poly_add(out, poly_scale(polynomial, Fraction(coefficient)))
    return out


def complete_selfdual_enumerator(
    low_weights: Sequence[Fraction | int],
    shadow_weight_2: Fraction | int = 0,
    shadow_weight_4: Fraction | int = 0,
) -> tuple[list[Fraction], list[Fraction], list[Fraction]]:
    """Solve all eight Gleason coefficients from low W and low shadow W.

    The first five coefficients are obtained triangularly from W_0,...,W_4.
    The last three are obtained by exact Gaussian elimination from shadow
    coefficients at weights 0,2,4, imposing shadow_0=0.
    """

    if len(low_weights) != 5:
        raise ValueError("low_weights must contain weights 0 through 4")
    coefficients = [Fraction(0) for _ in range(8)]
    for weight in range(5):
        already = sum(
            coefficients[index] * GLEASON_BASIS[index][weight]
            for index in range(weight)
        )
        diagonal = GLEASON_BASIS[weight][weight]
        coefficients[weight] = (Fraction(low_weights[weight]) - already) / diagonal

    shadow_basis = [shadow_transform_selfdual(polynomial) for polynomial in GLEASON_BASIS]
    rows = []
    rhs = []
    targets = {
        0: Fraction(0),
        2: Fraction(shadow_weight_2),
        4: Fraction(shadow_weight_4),
    }
    for weight in (0, 2, 4):
        rows.append([shadow_basis[index][weight] for index in (5, 6, 7)])
        known = sum(
            coefficients[index] * shadow_basis[index][weight] for index in range(5)
        )
        rhs.append(targets[weight] - known)
    tail = solve_square(rows, rhs)
    coefficients[5:] = tail
    enumerator = combine_polynomials(coefficients)
    shadow = shadow_transform_selfdual(enumerator)
    return coefficients, enumerator, shadow


def _all_even_certificate() -> dict[str, object]:
    variable_weights = list(range(2, 15, 2))
    equations: list[list[Fraction]] = []
    for j in range(5):
        row = [
            Fraction(
                krawtchouk(j, weight)
                - (STABILIZER_SIZE if weight == j else 0)
            )
            for weight in variable_weights
        ]
        rhs = -krawtchouk(j, 0) + (STABILIZER_SIZE if j == 0 else 0)
        equations.append(row + [Fraction(rhs)])

    reduced, pivots = rref(equations, pivot_columns=len(variable_weights))
    free = [index for index in range(len(variable_weights)) if index not in pivots]
    if free != [5, 6]:
        raise AssertionError(f"unexpected all-even free columns: {free}")

    parameterization: dict[str, list[Fraction]] = {}
    for row_index, pivot in enumerate(pivots):
        # vector is [constant, coefficient of A12, coefficient of A14].
        parameterization[f"A{variable_weights[pivot]}"] = [
            reduced[row_index][-1],
            -reduced[row_index][free[0]],
            -reduced[row_index][free[1]],
        ]
    parameterization["A12"] = [Fraction(0), Fraction(1), Fraction(0)]
    parameterization["A14"] = [Fraction(0), Fraction(0), Fraction(1)]

    features = [
        [Fraction(1), Fraction(0), Fraction(0)],
        parameterization["A2"],
        parameterization["A4"],
        parameterization["A6"],
    ]
    coefficient_matrix = [
        [features[column][component] for column in range(4)]
        for component in range(3)
    ]
    relations = nullspace(coefficient_matrix)
    if len(relations) != 1:
        raise AssertionError("expected a unique relation among 1,A2,A4,A6")
    primitive_relation = canonical_integer_vector(relations[0])
    if primitive_relation != [-7, 16, 9, 2]:
        raise AssertionError(f"unexpected all-even relation: {primitive_relation}")
    constant, coefficient_a2, coefficient_a4, coefficient_a6 = primitive_relation
    rhs = -constant
    nonnegative_integer_solutions = []
    for a2 in range(rhs // coefficient_a2 + 1):
        for a4 in range(rhs // coefficient_a4 + 1):
            for a6 in range(rhs // coefficient_a6 + 1):
                if coefficient_a2 * a2 + coefficient_a4 * a4 + coefficient_a6 * a6 == rhs:
                    nonnegative_integer_solutions.append(
                        {"A2": a2, "A4": a4, "A6": a6}
                    )
    if nonnegative_integer_solutions:
        raise AssertionError(
            "all-even relation unexpectedly has a nonnegative integer solution"
        )
    scaled_relation = [10 * coefficient for coefficient in primitive_relation]

    expected_parameterization = {
        "A2": [Fraction(-1145, 40), Fraction(1, 40), Fraction(6, 40)],
        "A4": [Fraction(-35, 10), Fraction(1, 10), Fraction(-14, 10)],
        "A6": [Fraction(4965, 20), Fraction(-13, 20), Fraction(102, 20)],
    }
    for name, expected in expected_parameterization.items():
        if parameterization[name] != expected:
            raise AssertionError(
                f"all-even parameterization mismatch for {name}: "
                f"{parameterization[name]}"
            )

    return {
        "variable_order": [f"A{weight}" for weight in variable_weights],
        "equations_j0_through_j4_augmented": equations,
        "rref": reduced,
        "pivot_columns": pivots,
        "free_variables": ["A12", "A14"],
        "parameterization_vectors_constant_A12_A14": parameterization,
        "derived_primitive_relation_on_1_A2_A4_A6": primitive_relation,
        "scaled_relation": {
            "identity": "20*A6=70-160*A2-90*A4",
            "zero_form_coefficients_constant_A2_A4_A6": scaled_relation,
        },
        "contradiction": {
            "reason": (
                "The primitive relation is 16*A2+9*A4+2*A6=7. "
                "Nonnegative integrality makes A2=A4=0, after which "
                "A6=7/2 is not an integer."
            ),
            "nonnegative_integer_solutions": nonnegative_integer_solutions,
        },
    }


def _odd_identity_certificate() -> dict[str, object]:
    variables = [f"A{index}" for index in range(1, 15)] + ["E1", "E4"]
    positions = {name: index for index, name in enumerate(variables)}
    rows: dict[str, tuple[list[Fraction], Fraction]] = {}

    row = [Fraction(0) for _ in variables]
    for index in range(1, 15):
        row[positions[f"A{index}"]] = Fraction(1)
    rows["T"] = (row, Fraction(2047))

    row = [Fraction(0) for _ in variables]
    for index in range(2, 15, 2):
        row[positions[f"A{index}"]] = Fraction(1)
    rows["P"] = (row, Fraction(1023))

    for j in range(1, 5):
        row = [Fraction(0) for _ in variables]
        for index in range(1, 15):
            row[positions[f"A{index}"]] = Fraction(
                krawtchouk(j, index)
                - (STABILIZER_SIZE if index == j else 0)
            )
        rows[f"M{j}"] = (row, Fraction(-krawtchouk(j, 0)))

    for j in (1, 4):
        row = [Fraction(0) for _ in variables]
        for index in range(2, 15, 2):
            row[positions[f"A{index}"]] = Fraction(krawtchouk(j, index))
        row[positions[f"E{j}"]] = Fraction(-(2**10))
        rows[f"Q{j}"] = (row, Fraction(-krawtchouk(j, 0)))

    combination = {
        "T": -147,
        "P": -148,
        "M1": -42,
        "M2": -42,
        "M3": -7,
        "M4": -7,
        "Q1": 8,
        "Q4": 4,
    }
    combined = [Fraction(0) for _ in variables]
    combined_rhs = Fraction(0)
    for name, multiple in combination.items():
        coefficients, rhs = rows[name]
        combined = [
            value + multiple * coefficient
            for value, coefficient in zip(combined, coefficients)
        ]
        combined_rhs += multiple * rhs
    combined = [value / -2048 for value in combined]
    combined_rhs /= -2048

    nonzero = {
        name: coefficient
        for name, coefficient in zip(variables, combined)
        if coefficient
    }
    expected = {
        "A1": Fraction(168),
        "A2": Fraction(28),
        "A3": Fraction(63),
        "A4": Fraction(15),
        "A5": Fraction(14),
        "A6": Fraction(4),
        "A14": Fraction(2),
        "E1": Fraction(4),
        "E4": Fraction(2),
    }
    if combined_rhs != 51 or nonzero != expected:
        raise AssertionError("the regenerated odd coefficient identity is incorrect")

    profiles = []
    for a2 in range(2):
        for a4 in range(4):
            if a4 % 2 == 1 and 28 * a2 + 15 * a4 <= 51:
                profiles.append([a2, a4])
    if profiles != [[0, 1], [0, 3], [1, 1]]:
        raise AssertionError(f"unexpected odd profiles: {profiles}")

    return {
        "variable_order": variables,
        "source_rows": {
            name: {"coefficients": coefficients, "rhs": rhs}
            for name, (coefficients, rhs) in rows.items()
        },
        "row_combination_before_division": combination,
        "division": -2048,
        "combined_rhs": combined_rhs,
        "combined_nonzero_coefficients": nonzero,
        "profile_reduction": {
            "A1_equals_0": "168*A1 <= 51",
            "A3_equals_0": "63*A3 <= 51",
            "A4_is_odd": "reduce the identity modulo 2",
            "possible_A2_A4": profiles,
        },
    }


def _selfdual_certificate() -> tuple[dict[str, object], dict[str, list[Fraction]]]:
    profile_low = {
        "p01": [1, 0, 0, 0, 1],
        "p03": [1, 0, 0, 0, 3],
        "p11": [1, 0, 1, 0, 1],
    }
    expected_coefficients = {
        "p01": [1, -14, 63, -112, 78, 0, 0, 0],
        "p03": [1, -14, 63, -112, 80, 0, 0, 0],
        "p11": [1, -14, 64, -120, 92, 0, 0, 0],
    }
    expected_enumerators = {
        "p01": [1, 0, 0, 0, 1, 44, 116, 400, 1283, 2504, 3488, 3856, 3035, 1388, 268],
        "p03": [1, 0, 0, 0, 3, 48, 110, 384, 1287, 2528, 3492, 3840, 3029, 1392, 270],
        "p11": [1, 0, 1, 0, 1, 56, 129, 416, 1339, 2512, 3355, 3744, 3075, 1464, 291],
    }

    profiles: dict[str, object] = {}
    bases: dict[str, list[Fraction]] = {}
    for name, low in profile_low.items():
        coefficients, enumerator, shadow = complete_selfdual_enumerator(low)
        if coefficients != [Fraction(value) for value in expected_coefficients[name]]:
            raise AssertionError(f"unexpected Gleason coefficients for {name}")
        if enumerator != [Fraction(value) for value in expected_enumerators[name]]:
            raise AssertionError(f"unexpected base enumerator for {name}")
        if macwilliams_normalized(enumerator) != enumerator:
            raise AssertionError(f"base enumerator for {name} is not M-invariant")
        if any(shadow[index] for index in (0, 2, 4)):
            raise AssertionError(
                f"zero-low-shadow base for {name} has a nonzero weight 0,2,or 4"
            )
        bases[name] = enumerator
        profiles[name] = {
            "low_weights_0_through_4": low,
            "gleason_coefficients": coefficients,
            "enumerator": enumerator,
            "shadow": shadow,
            "checks": {
                "M_invariant": True,
                "shadow_weights_0_2_4_zero": True,
            },
        }

    zero_coefficients, zero_enumerator, _ = complete_selfdual_enumerator(profile_low["p01"])
    unit2_coefficients, unit2_enumerator, unit2_shadow = complete_selfdual_enumerator(
        profile_low["p01"], shadow_weight_2=1
    )
    unit4_coefficients, unit4_enumerator, unit4_shadow = complete_selfdual_enumerator(
        profile_low["p01"], shadow_weight_4=1
    )
    delta2_coefficients = [
        right - left for left, right in zip(zero_coefficients, unit2_coefficients)
    ]
    delta4_coefficients = [
        right - left for left, right in zip(zero_coefficients, unit4_coefficients)
    ]
    delta2 = [right - left for left, right in zip(zero_enumerator, unit2_enumerator)]
    delta4 = [right - left for left, right in zip(zero_enumerator, unit4_enumerator)]
    expected_delta2 = [0, 0, 0, 0, 0, -12, 28, -16, 16, -8, -88, 112, 16, -76, 28]
    expected_delta4 = [0, 0, 0, 0, 0, -2, 2, 8, -8, -12, 12, 8, -8, -2, 2]
    if delta2 != [Fraction(value) for value in expected_delta2]:
        raise AssertionError("unit weight-2 extension-shadow perturbation mismatch")
    if delta4 != [Fraction(value) for value in expected_delta4]:
        raise AssertionError("unit weight-4 extension-shadow perturbation mismatch")
    if unit2_shadow[2] != 1 or any(
        unit2_shadow[index] for index in (0, 4)
    ):
        raise AssertionError("unit weight-2 shadow solve did not meet its constraints")
    if unit4_shadow[4] != 1 or any(
        unit4_shadow[index] for index in (0, 2)
    ):
        raise AssertionError("unit weight-4 shadow solve did not meet its constraints")

    shadow_basis = [shadow_transform_selfdual(polynomial) for polynomial in GLEASON_BASIS]
    low_shadow_system = [
        [shadow_basis[index][weight] for index in (5, 6, 7)]
        for weight in (0, 2, 4)
    ]
    return (
        {
            "basis_definition": "(x+y)^(14-2i) * [y*(x-y)]^i, i=0..7",
            "basis_polynomials": GLEASON_BASIS,
            "profiles": profiles,
            "tail_solve": {
                "unknown_coefficients": ["c5", "c6", "c7"],
                "shadow_weights": [0, 2, 4],
                "matrix": low_shadow_system,
                "base_target": [0, 0, 0],
                "unit_weight_2_coefficients_delta": delta2_coefficients,
                "unit_weight_4_coefficients_delta": delta4_coefficients,
            },
            "unit_extension_shadow_weight_2": {
                "enumerator_delta": delta2,
                "shadow_low_weights_0_2_4": [
                    unit2_shadow[0],
                    unit2_shadow[2],
                    unit2_shadow[4],
                ],
            },
            "unit_extension_shadow_weight_4": {
                "enumerator_delta": delta4,
                "shadow_low_weights_0_2_4": [
                    unit4_shadow[0],
                    unit4_shadow[2],
                    unit4_shadow[4],
                ],
            },
            "global_to_average_extension_shadow": {
                "t2": "2*S2/9",
                "t4": "2*S4/9",
                "boundary": (
                    "The factors 2/9 are supplied by the separately checked "
                    "Lagrangian incidence count 30/135."
                ),
            },
        },
        {
            "delta2": delta2,
            "delta4": delta4,
            **bases,
        },
    )


def _anti_certificate() -> tuple[dict[str, object], list[Fraction], list[Fraction]]:
    anti_basis = [
        poly_mul(
            poly_pow([Fraction(1), Fraction(1)], 13 - 2 * index),
            poly_pow([Fraction(1), Fraction(-3)], 2 * index + 1),
        )
        for index in range(7)
    ]
    for polynomial in anti_basis:
        transformed = macwilliams_normalized(polynomial)
        if transformed != poly_scale(polynomial, -1):
            raise AssertionError("anti-invariant basis failed M(P)=-P")

    low_matrix = [
        [anti_basis[basis_index][weight] for weight in range(7)]
        for basis_index in range(7)
    ]
    g14_targets = [polynomial[14] for polynomial in anti_basis]
    g14_lambda = solve_square(low_matrix, g14_targets)

    transformed_basis = [
        shadow_transform_selfdual(polynomial) for polynomial in anti_basis
    ]
    r3_targets = [polynomial[3] for polynomial in transformed_basis]
    r3_lambda = solve_square(low_matrix, r3_targets)

    expected_g14 = [
        Fraction(-1368),
        Fraction(-468),
        Fraction(-306),
        Fraction(-108),
        Fraction(-48),
        Fraction(-12),
        Fraction(-3),
    ]
    expected_r3 = [
        Fraction(-1365, 8),
        Fraction(-741, 8),
        Fraction(-357, 8),
        Fraction(-163, 8),
        Fraction(-59, 8),
        Fraction(-19, 8),
        Fraction(-3, 8),
    ]
    if g14_lambda != expected_g14:
        raise AssertionError(f"unexpected I14 functional: {g14_lambda}")
    if r3_lambda != expected_r3:
        raise AssertionError(f"unexpected R3 functional: {r3_lambda}")

    i14_left_coefficients = [-value for value in g14_lambda]
    is3_g_coefficients = [-8 * value for value in r3_lambda]
    return (
        {
            "coordinate_change": {
                "u": "x+y",
                "v": "x-3y",
                "M_action": "u -> u, v -> -v",
            },
            "anti_basis_definition": "u^(13-2r) v^(2r+1), r=0..6",
            "anti_basis_polynomials": anti_basis,
            "low_weight_matrix_rows_basis_columns_g0_through_g6": low_matrix,
            "I14": {
                "solved_g14_as_function_of_g0_through_g6": g14_lambda,
                "identity_coefficients_after_g14": i14_left_coefficients,
                "identity": (
                    "g14+1368g0+468g1+306g2+108g3+48g4+12g5+3g6=0"
                ),
            },
            "R3": {
                "solved_R(G)_3_as_function_of_g0_through_g6": r3_lambda,
                "incidence_relation": "S3=R(G)_3/2",
                "incidence_reason": (
                    "R(Nbar)_3=0 because odd global-shadow points occur in no "
                    "extension shadow; A=(G+9*Nbar)/16."
                ),
            },
            "IS3": {
                "identity_coefficients_after_16S3": is3_g_coefficients,
                "identity": (
                    "16S3+1365g0+741g1+357g2+163g3+59g4+19g5+3g6=0"
                ),
            },
        },
        i14_left_coefficients,
        is3_g_coefficients,
    )


def _profile_linear_forms(
    low: Sequence[int],
    base: Sequence[Fraction],
    delta2: Sequence[Fraction],
    delta4: Sequence[Fraction],
    i14_coefficients: Sequence[Fraction],
    is3_coefficients: Sequence[Fraction],
) -> tuple[Linear, Linear]:
    a = Linear.variable("A5")
    b = Linear.variable("A6")
    m = Linear.variable("S2")
    r = Linear.variable("S4")
    c = Linear.variable("A14")

    def g_at(weight: int) -> Linear:
        nbar = (
            Linear.constant(base[weight])
            + Fraction(2, 9) * delta2[weight] * m
            + Fraction(2, 9) * delta4[weight] * r
        )
        if weight <= 4:
            aval = Linear.constant(low[weight])
        elif weight == 5:
            aval = a
        elif weight == 6:
            aval = b
        elif weight == 14:
            aval = c
        else:
            aval = Linear.constant(0)
        return 16 * aval - 9 * nbar

    i14_expression = g_at(14)
    for weight, coefficient in enumerate(i14_coefficients):
        i14_expression += coefficient * g_at(weight)
    c_formula = solve_linear_expression(i14_expression, "A14")

    s3 = Linear.variable("S3")
    is3_expression = 16 * s3
    for weight, coefficient in enumerate(is3_coefficients):
        is3_expression += coefficient * g_at(weight)
    s3_formula = solve_linear_expression(is3_expression, "S3")
    return c_formula, s3_formula


def _profiles_certificate(
    bases: Mapping[str, Sequence[Fraction]],
    delta2: Sequence[Fraction],
    delta4: Sequence[Fraction],
    i14_coefficients: Sequence[Fraction],
    is3_coefficients: Sequence[Fraction],
) -> dict[str, object]:
    low_profiles = {
        "p01": [1, 0, 0, 0, 1],
        "p03": [1, 0, 0, 0, 3],
        "p11": [1, 0, 1, 0, 1],
    }
    formulas: dict[str, tuple[Linear, Linear]] = {}
    for name in ("p01", "p03", "p11"):
        formulas[name] = _profile_linear_forms(
            low_profiles[name],
            bases[name],
            delta2,
            delta4,
            i14_coefficients,
            is3_coefficients,
        )

    expected_c = {
        "p01": Linear.constant(24)
        - 12 * Linear.variable("A5")
        - 3 * Linear.variable("A6")
        - 4 * Linear.variable("S2")
        - 2 * Linear.variable("S4"),
        "p03": -12 * Linear.variable("A5")
        - 3 * Linear.variable("A6")
        - 4 * Linear.variable("S2")
        - 2 * Linear.variable("S4"),
        "p11": Linear.constant(6)
        - 12 * Linear.variable("A5")
        - 3 * Linear.variable("A6")
        - 4 * Linear.variable("S2")
        - 2 * Linear.variable("S4"),
    }
    for name in expected_c:
        if formulas[name][0] != expected_c[name]:
            raise AssertionError(f"unexpected I14 profile formula for {name}")

    a = Linear.variable("A5")
    b = Linear.variable("A6")
    m = Linear.variable("S2")
    r = Linear.variable("S4")
    s = Linear.variable("S1")

    # p01: substitute I14 into the regenerated 51 identity and solve for A6.
    p01_51 = 15 + 14 * a + 4 * b + 2 * formulas["p01"][0] + 4 * s + 2 * (1 + r) - 51
    p01_b = solve_linear_expression(p01_51, "A6")
    p01_c = formulas["p01"][0].substitute("A6", p01_b)
    p01_l = formulas["p01"][1].substitute("A6", p01_b)
    expected_b = 7 - 5 * a - 4 * m - r + 2 * s
    expected_c01 = 3 + 3 * a + 8 * m + r - 6 * s
    expected_l = 22 - 4 * a - 6 * m - r - 6 * s
    if (p01_b, p01_c, p01_l) != (expected_b, expected_c01, expected_l):
        raise AssertionError("p01 elimination formulas did not regenerate")

    # Exhaust the bounded integer region implied by A6>=0 and S1<=1.
    algebraically_nonnegative = []
    after_incidence_bounds = []
    for sval in range(2):
        for aval in range(2):  # 5*A5 <= 9 follows from A6>=0 and S1<=1.
            for mval in range(3):  # 4*S2 <= 9.
                for rval in range(10):  # S4 <= 9.
                    values = {"A5": aval, "S2": mval, "S4": rval, "S1": sval}
                    bval = int(p01_b.evaluate(values))
                    cval = int(p01_c.evaluate(values))
                    lval = int(p01_l.evaluate(values))
                    if min(bval, cval, lval) < 0:
                        continue
                    record = {
                        **values,
                        "A6": bval,
                        "A14": cval,
                        "S3": lval,
                    }
                    algebraically_nonnegative.append(record)
                    passes = True
                    if sval == 1:
                        passes = mval == 0 and lval <= 1
                    else:
                        passes = lval <= 14
                        if mval == 1:
                            passes = passes and lval <= 12
                    if passes:
                        after_incidence_bounds.append(record)
    if after_incidence_bounds:
        raise AssertionError(f"p01 incidence bounds left survivors: {after_incidence_bounds}")

    # p11: the independently proved geometry gives A5=0,A6=1.
    p11_51 = (
        28
        + 15
        + 14 * a
        + 4 * b
        + 2 * Linear.variable("A14")
        + 4 * s
        + 2 * (1 + r)
        - 51
    )
    p11_after_geometry = p11_51.substitute("A5", Linear.constant(0)).substitute(
        "A6", Linear.constant(1)
    )
    p11_cases = []
    for cval in range(2):
        for sval in range(2):
            for rval in range(2):
                if p11_after_geometry.evaluate(
                    {"A14": cval, "S1": sval, "S4": rval}
                ) == 0:
                    c_formula = formulas["p11"][0]
                    m_solution = solve_linear_expression(
                        c_formula.substitute("A5", Linear.constant(0))
                        .substitute("A6", Linear.constant(1))
                        .substitute("S4", Linear.constant(rval))
                        - cval,
                        "S2",
                    )
                    p11_cases.append(
                        {
                            "A14": cval,
                            "S1": sval,
                            "S4": rval,
                            "required_S2": m_solution.coefficient("$"),
                            "integral": m_solution.coefficient("$").denominator == 1,
                        }
                    )
    if [(case["A14"], case["S4"], case["required_S2"]) for case in p11_cases] != [
        (0, 1, Fraction(1, 4)),
        (1, 0, Fraction(1, 2)),
    ]:
        raise AssertionError(f"unexpected p11 cases: {p11_cases}")

    # p03: the 51 identity is a sum of nonnegative terms and kills all five.
    p03_51_after_constant = 14 * a + 4 * b + 2 * Linear.variable(
        "A14"
    ) + 4 * s + 2 * r
    p03_51_nonnegative_solutions = []
    # Each positive coefficient already bounds its variable by zero when the
    # right-hand side is zero.  Enumerate a larger finite box anyway so the
    # generated certificate witnesses uniqueness instead of just testing the
    # anticipated assignment.
    for aval in range(2):
        for bval in range(2):
            for cval in range(2):
                for sval in range(2):
                    for rval in range(2):
                        values = {
                            "A5": aval,
                            "A6": bval,
                            "A14": cval,
                            "S1": sval,
                            "S4": rval,
                        }
                        if p03_51_after_constant.evaluate(values) == 0:
                            p03_51_nonnegative_solutions.append(values)
    p03_zero_values = {"A5": 0, "A6": 0, "A14": 0, "S1": 0, "S4": 0}
    if p03_51_nonnegative_solutions != [p03_zero_values]:
        raise AssertionError(
            "p03 51 identity did not uniquely force the five zero values"
        )
    p03_m_formula = solve_linear_expression(
        formulas["p03"][0]
        .substitute("A5", Linear.constant(0))
        .substitute("A6", Linear.constant(0))
        .substitute("A14", Linear.constant(0))
        .substitute("S4", Linear.constant(0)),
        "S2",
    )
    p03_l_value = formulas["p03"][1].evaluate(
        {"A5": 0, "A6": 0, "S2": 0, "S4": 0}
    )
    if p03_m_formula.coefficient("$") != 0 or p03_l_value != 24:
        raise AssertionError("p03 did not force S2=0 and S3=24")

    return {
        "raw_I14_A14_formulas": {
            name: formula[0].as_dict() for name, formula in formulas.items()
        },
        "raw_IS3_S3_formulas": {
            name: formula[1].as_dict() for name, formula in formulas.items()
        },
        "p11": {
            "geometry_input": "A5=0 and A6=1",
            "regenerated_51_expression_after_geometry": p11_after_geometry.as_dict(),
            "cases": p11_cases,
            "conclusion": "both cases require a nonintegral S2",
        },
        "p01": {
            "A6_formula": p01_b.as_dict(),
            "A14_formula": p01_c.as_dict(),
            "S3_formula": p01_l.as_dict(),
            "coverage_bounds_from_A6_nonnegative_and_S1_at_most_1": {
                "A5": [0, 1],
                "S2": [0, 2],
                "S4": [0, 9],
                "S1": [0, 1],
            },
            "algebraically_nonnegative_assignments": algebraically_nonnegative,
            "incidence_bounds_consumed": {
                "S1=1": "S2=0 and S3<=1",
                "S1=0": "S3<=14",
                "S1=0,S2=1": "S3<=12 (36-bin refinement)",
            },
            "survivors_after_incidence_bounds": after_incidence_bounds,
        },
        "p03": {
            "regenerated_nonnegative_51_remainder": p03_51_after_constant.as_dict(),
            "nonnegative_solutions_in_coefficient_bounded_box": (
                p03_51_nonnegative_solutions
            ),
            "forced_zero": p03_zero_values,
            "required_S2": p03_m_formula.coefficient("$"),
            "forced_S3": p03_l_value,
        },
    }


def _forced_p03_certificate(
    base: Sequence[Fraction],
) -> dict[str, object]:
    forced_low_a = [
        Fraction(1),
        Fraction(0),
        Fraction(0),
        Fraction(0),
        Fraction(3),
        Fraction(0),
        Fraction(0),
    ]
    low_g = [
        16 * a_value - 9 * nbar_value
        for a_value, nbar_value in zip(forced_low_a, base[:7])
    ]
    if low_g != [
        Fraction(7),
        Fraction(0),
        Fraction(0),
        Fraction(0),
        Fraction(21),
        Fraction(-432),
        Fraction(-990),
    ]:
        raise AssertionError("regenerated p03 low G coefficients changed")
    anti_basis = [
        poly_mul(
            poly_pow([Fraction(1), Fraction(1)], 13 - 2 * index),
            poly_pow([Fraction(1), Fraction(-3)], 2 * index + 1),
        )
        for index in range(7)
    ]
    low_system = [
        [anti_basis[column][row] for column in range(7)] for row in range(7)
    ]
    anti_coordinates = solve_square(low_system, low_g)
    g_polynomial = combine_polynomials(anti_coordinates, anti_basis)
    a_polynomial = [
        (g_value + 9 * nbar_value) / 16
        for g_value, nbar_value in zip(g_polynomial, base)
    ]
    b_polynomial = [
        9 * nbar_value - 8 * a_value
        for nbar_value, a_value in zip(base, a_polynomial)
    ]
    s_polynomial = global_shadow_transform(a_polynomial)
    expected_a = [
        1, 0, 0, 0, 3, 0, 0, 24, 207, 424, 336, 360, 477, 216, 0
    ]
    expected_b = [
        1, 0, 0, 0, 3, 432, 990, 3264, 9927, 19360, 28740, 31680,
        23445, 10800, 2430
    ]
    expected_s = [
        0, 0, 0, 24, 0, 216, 1440, 2928, 10368, 17456, 32832, 27000,
        26496, 9720, 2592
    ]
    if a_polynomial != [Fraction(value) for value in expected_a]:
        raise AssertionError(f"forced p03 A mismatch: {a_polynomial}")
    if b_polynomial != [Fraction(value) for value in expected_b]:
        raise AssertionError(f"forced p03 B mismatch: {b_polynomial}")
    if s_polynomial != [Fraction(value) for value in expected_s]:
        raise AssertionError(f"forced p03 S mismatch: {s_polynomial}")

    direct_b = poly_scale(
        homogeneous_substitute(
            a_polynomial,
            [Fraction(1), Fraction(3)],
            [Fraction(1), Fraction(-1)],
        ),
        Fraction(1, STABILIZER_SIZE),
    )
    if direct_b != b_polynomial:
        raise AssertionError("forced p03 B failed direct MacWilliams transform")
    if sum(a_polynomial) != STABILIZER_SIZE:
        raise AssertionError("forced p03 A does not have size 2^11")
    if sum(b_polynomial) != 2**17:
        raise AssertionError("forced p03 B does not have size 2^17")
    if sum(s_polynomial) != 2**17:
        raise AssertionError("forced p03 S does not have size 2^17")

    return {
        "forced_low_A_weights_0_through_6": forced_low_a,
        "base_Nbar_weights_0_through_6": list(base[:7]),
        "input_low_G_weights_0_through_6": low_g,
        "solved_anti_basis_coordinates": anti_coordinates,
        "G": g_polynomial,
        "A": a_polynomial,
        "B": b_polynomial,
        "S": s_polynomial,
        "checks": {
            "B_equals_direct_MacWilliams_of_A": True,
            "S_equals_direct_global_shadow_transform_of_A": True,
            "sum_A": sum(a_polynomial),
            "sum_B": sum(b_polynomial),
            "sum_S": sum(s_polynomial),
        },
    }


def _json_safe(value: object) -> object:
    if isinstance(value, Fraction):
        if value.denominator == 1:
            return value.numerator
        return f"{value.numerator}/{value.denominator}"
    if isinstance(value, dict):
        return {str(key): _json_safe(item) for key, item in value.items()}
    if isinstance(value, (list, tuple)):
        return [_json_safe(item) for item in value]
    return value


def build_certificate() -> dict[str, object]:
    """Regenerate and return the complete JSON-safe exact algebra certificate."""

    if sys.flags.optimize:
        raise RuntimeError("optimized Python is unsupported: exact assertions must run")
    all_even = _all_even_certificate()
    odd_identity = _odd_identity_certificate()
    selfdual, polynomial_data = _selfdual_certificate()
    anti, i14_coefficients, is3_coefficients = _anti_certificate()
    profiles = _profiles_certificate(
        polynomial_data,
        polynomial_data["delta2"],
        polynomial_data["delta4"],
        i14_coefficients,
        is3_coefficients,
    )
    forced_p03 = _forced_p03_certificate(polynomial_data["p03"])
    exact = {
        "schema": "quantum-14-3-5-exact-algebra-v1",
        "status": "PASS",
        "arithmetic": "fractions.Fraction only",
        "scope": (
            "Algebraic certificate conditional on the separately certified "
            "shadow/Lagrangian incidence and collision lemmas explicitly named "
            "in this output."
        ),
        "all_even": all_even,
        "odd_51_identity": odd_identity,
        "selfdual_extensions": selfdual,
        "anti_macwilliams": anti,
        "profile_eliminations": profiles,
        "forced_p03_enumerators": forced_p03,
    }
    return _json_safe(exact)  # type: ignore[return-value]


def self_test() -> None:
    first = build_certificate()
    second = build_certificate()
    if first != second:
        raise AssertionError("build_certificate is not deterministic")
    if first["status"] != "PASS":
        raise AssertionError("certificate did not report PASS")
    encoded = json.dumps(first, sort_keys=True, separators=(",", ":"))
    decoded = json.loads(encoded)
    if decoded != first:
        raise AssertionError("certificate is not JSON round-trip safe")


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--json",
        action="store_true",
        help="print the regenerated certificate as deterministic JSON",
    )
    parser.add_argument(
        "--self-test",
        action="store_true",
        help="run determinism and JSON-safety checks",
    )
    arguments = parser.parse_args(argv)
    if arguments.self_test:
        self_test()
    certificate = build_certificate()
    if arguments.json:
        print(json.dumps(certificate, sort_keys=True, indent=2))
    else:
        print("PASS exact_algebra")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
