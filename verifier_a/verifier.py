#!/usr/bin/env python3
"""Exact verifier for binary qubit stabilizer matrices.

The input convention is a literal binary matrix H=[X|Z].  Within a packed
integer, bit i is X_i and bit n+i is Z_i.  This module uses only the Python 3
standard library.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Iterator, Sequence


class VerificationError(ValueError):
    """Raised when a matrix or a claimed parameter fails exact verification."""


def _parity(value: int) -> int:
    return value.bit_count() & 1


def symplectic_inner(left: int, right: int, n: int) -> int:
    """Return <left,right>_s for packed (x|z) vectors over GF(2)."""

    mask = (1 << n) - 1
    left_x = left & mask
    left_z = (left >> n) & mask
    right_x = right & mask
    right_z = (right >> n) & mask
    return _parity((left_x & right_z) ^ (left_z & right_x))


def pauli_weight(vector: int, n: int) -> int:
    """Return the number of qubits on which (x_i,z_i) is nonzero."""

    mask = (1 << n) - 1
    return ((vector & mask) | ((vector >> n) & mask)).bit_count()


def split_bit_string(vector: int, n: int) -> str:
    """Serialize a packed vector in the declared X_1..X_n|Z_1..Z_n order."""

    x_bits = "".join(str((vector >> i) & 1) for i in range(n))
    z_bits = "".join(str((vector >> (n + i)) & 1) for i in range(n))
    return f"{x_bits}|{z_bits}"


def pauli_string(vector: int, n: int) -> str:
    """Serialize a packed vector as an I/X/Y/Z string in qubit order."""

    symbols = ("I", "X", "Z", "Y")
    return "".join(
        symbols[((vector >> i) & 1) | (((vector >> (n + i)) & 1) << 1)]
        for i in range(n)
    )


def pack_row(row: Sequence[int]) -> int:
    """Pack an already validated binary row."""

    value = 0
    for bit_index, bit in enumerate(row):
        value |= bit << bit_index
    return value


def _gauss_jordan(rows: Iterable[int], width: int) -> tuple[list[int], list[int]]:
    """Return GF(2) RREF rows and ascending pivot columns.

    This routine is used for rank and nullspace construction.  Stabilizer
    membership during enumeration deliberately uses ``PackedRowSpace`` below.
    """

    if width < 0:
        raise ValueError("width must be nonnegative")
    width_mask = (1 << width) - 1
    matrix = [row & width_mask for row in rows if row & width_mask]
    pivot_columns: list[int] = []
    pivot_row = 0

    for column in range(width):
        selected = next(
            (
                row_index
                for row_index in range(pivot_row, len(matrix))
                if (matrix[row_index] >> column) & 1
            ),
            None,
        )
        if selected is None:
            continue
        matrix[pivot_row], matrix[selected] = matrix[selected], matrix[pivot_row]
        for row_index in range(len(matrix)):
            if row_index != pivot_row and ((matrix[row_index] >> column) & 1):
                matrix[row_index] ^= matrix[pivot_row]
        pivot_columns.append(column)
        pivot_row += 1
        if pivot_row == len(matrix):
            break

    return matrix[:pivot_row], pivot_columns


def gf2_rank(rows: Iterable[int], width: int) -> int:
    """Return the exact GF(2) rank of packed rows."""

    _, pivots = _gauss_jordan(rows, width)
    return len(pivots)


def gf2_nullspace(equations: Iterable[int], width: int) -> tuple[int, ...]:
    """Return a deterministic basis for the nullspace of binary equations."""

    rref_rows, pivot_columns = _gauss_jordan(equations, width)
    pivot_set = set(pivot_columns)
    free_columns = [column for column in range(width) if column not in pivot_set]
    basis: list[int] = []

    for free_column in free_columns:
        vector = 1 << free_column
        for row, pivot_column in zip(rref_rows, pivot_columns):
            if (row >> free_column) & 1:
                vector |= 1 << pivot_column
        basis.append(vector)

    # Internal construction check: each returned vector satisfies every RREF
    # equation, and the free-coordinate identity block makes the basis
    # independent.
    for vector in basis:
        if any(_parity(row & vector) for row in rref_rows):
            raise AssertionError("internal nullspace construction failure")
    if gf2_rank(basis, width) != len(basis):
        raise AssertionError("internal nullspace basis dependence")
    return tuple(basis)


class PackedRowSpace:
    """Independent high-pivot reducer for repeated row-space membership tests."""

    def __init__(self, rows: Iterable[int], width: int):
        self.width = width
        self._width_mask = (1 << width) - 1
        self._basis_by_pivot: dict[int, int] = {}
        for row in rows:
            self._insert(row)

    def _insert(self, row: int) -> bool:
        remainder = row & self._width_mask
        while remainder:
            pivot = remainder.bit_length() - 1
            basis_row = self._basis_by_pivot.get(pivot)
            if basis_row is None:
                self._basis_by_pivot[pivot] = remainder
                return True
            remainder ^= basis_row
        return False

    @property
    def rank(self) -> int:
        return len(self._basis_by_pivot)

    def contains(self, vector: int) -> bool:
        if vector & ~self._width_mask:
            return False
        remainder = vector
        while remainder:
            pivot = remainder.bit_length() - 1
            basis_row = self._basis_by_pivot.get(pivot)
            if basis_row is None:
                return False
            remainder ^= basis_row
        return True


def enumerate_span_gray(basis: Sequence[int]) -> Iterator[int]:
    """Enumerate every span element once using binary-reflected Gray order."""

    value = 0
    previous_gray = 0
    yield value
    for index in range(1, 1 << len(basis)):
        gray = index ^ (index >> 1)
        changed = gray ^ previous_gray
        basis_index = changed.bit_length() - 1
        value ^= basis[basis_index]
        yield value
        previous_gray = gray


def _swap_halves(vector: int, n: int) -> int:
    mask = (1 << n) - 1
    return ((vector & mask) << n) | ((vector >> n) & mask)


def _canonical_matrix_text(rows: Sequence[int], n: int) -> str:
    return "".join(f"{split_bit_string(row, n)}\n" for row in rows)


@dataclass(frozen=True)
class VerificationReport:
    n: int
    row_count: int
    rank: int
    k: int
    isotropic: bool
    stabilizer_dimension: int
    normalizer_dimension: int
    stabilizer_size: int
    normalizer_size: int
    logical_vector_count: int
    stabilizer_weight_distribution: tuple[int, ...]
    logical_weight_distribution: tuple[int, ...]
    minimum_logical_weight: int | None
    minimum_logical_witness: int | None
    normalizer_basis: tuple[int, ...]
    matrix_sha256: str

    def as_dict(self) -> dict[str, object]:
        witness = self.minimum_logical_witness
        return {
            "format": "binary-symplectic-H=[X|Z]",
            "isotropic": self.isotropic,
            "k": self.k,
            "logical_vector_count": self.logical_vector_count,
            "logical_weight_distribution": list(self.logical_weight_distribution),
            "matrix_sha256": self.matrix_sha256,
            "minimum_logical_weight": self.minimum_logical_weight,
            "minimum_logical_witness": (
                None
                if witness is None
                else {
                    "bits": split_bit_string(witness, self.n),
                    "packed_hex": hex(witness),
                    "pauli": pauli_string(witness, self.n),
                }
            ),
            "n": self.n,
            "normalizer_basis": [
                {
                    "bits": split_bit_string(vector, self.n),
                    "packed_hex": hex(vector),
                    "pauli": pauli_string(vector, self.n),
                }
                for vector in self.normalizer_basis
            ],
            "normalizer_dimension": self.normalizer_dimension,
            "normalizer_size": self.normalizer_size,
            "rank": self.rank,
            "row_count": self.row_count,
            "stabilizer_dimension": self.stabilizer_dimension,
            "stabilizer_size": self.stabilizer_size,
            "stabilizer_weight_distribution": list(
                self.stabilizer_weight_distribution
            ),
        }


def validate_literal_rows(
    literal_rows: Sequence[Sequence[int]], expected_n: int | None = None
) -> tuple[tuple[int, ...], int]:
    """Validate dimensions and bits, then pack a literal H=[X|Z] matrix."""

    if not isinstance(literal_rows, Sequence) or isinstance(
        literal_rows, (str, bytes)
    ):
        raise VerificationError("H must be a sequence of binary rows")
    if not literal_rows:
        raise VerificationError("H must contain at least one row")

    first_length: int | None = None
    packed_rows: list[int] = []
    for row_index, row in enumerate(literal_rows):
        if not isinstance(row, Sequence) or isinstance(row, (str, bytes)):
            raise VerificationError(f"row {row_index} is not a bit sequence")
        if first_length is None:
            first_length = len(row)
            if first_length == 0 or first_length & 1:
                raise VerificationError(
                    "row width must be a positive even number (2n)"
                )
        elif len(row) != first_length:
            raise VerificationError(
                f"row {row_index} has length {len(row)}; expected {first_length}"
            )
        for column, bit in enumerate(row):
            if type(bit) is not int or bit not in (0, 1):
                raise VerificationError(
                    f"H[{row_index}][{column}]={bit!r} is not an integer bit"
                )
        packed_rows.append(pack_row(row))

    assert first_length is not None
    n = first_length // 2
    if expected_n is not None and n != expected_n:
        raise VerificationError(f"n={n}; expected n={expected_n}")
    if len(packed_rows) > n:
        raise VerificationError(
            f"an isotropic subspace in 2n dimensions has at most n={n} "
            f"independent rows, but H has {len(packed_rows)} rows"
        )
    return tuple(packed_rows), n


def verify_literal_matrix(
    literal_rows: Sequence[Sequence[int]], expected_n: int | None = None
) -> VerificationReport:
    """Verify a literal full-row-rank isotropic H and compute exact distance."""

    rows, n = validate_literal_rows(literal_rows, expected_n=expected_n)
    width = 2 * n
    rank = gf2_rank(rows, width)
    if rank != len(rows):
        raise VerificationError(
            f"H is not full row rank: rank={rank}, rows={len(rows)}"
        )

    for left_index, left in enumerate(rows):
        for right_index in range(left_index + 1, len(rows)):
            if symplectic_inner(left, rows[right_index], n):
                raise VerificationError(
                    "H is not isotropic: "
                    f"rows {left_index} and {right_index} anticommute"
                )

    # <h,v>_s = swap(h) dot v, so the symplectic normalizer is this
    # ordinary binary nullspace.
    normalizer_equations = tuple(_swap_halves(row, n) for row in rows)
    normalizer_basis = gf2_nullspace(normalizer_equations, width)
    expected_normalizer_dimension = width - rank
    if len(normalizer_basis) != expected_normalizer_dimension:
        raise AssertionError("normalizer dimension disagrees with rank-nullity")
    if any(
        symplectic_inner(row, basis_vector, n)
        for row in rows
        for basis_vector in normalizer_basis
    ):
        raise AssertionError("constructed normalizer basis does not commute")

    row_space = PackedRowSpace(rows, width)
    if row_space.rank != rank:
        raise AssertionError("independent membership reducer has wrong rank")

    stabilizer_distribution = [0] * (n + 1)
    logical_distribution = [0] * (n + 1)
    minimum_weight: int | None = None
    minimum_witness: int | None = None
    enumerated_count = 0
    stabilizer_count = 0

    for vector in enumerate_span_gray(normalizer_basis):
        enumerated_count += 1
        weight = pauli_weight(vector, n)
        if row_space.contains(vector):
            stabilizer_count += 1
            stabilizer_distribution[weight] += 1
        else:
            logical_distribution[weight] += 1
            if minimum_weight is None or weight < minimum_weight:
                minimum_weight = weight
                minimum_witness = vector

    normalizer_size = 1 << len(normalizer_basis)
    stabilizer_size = 1 << rank
    if enumerated_count != normalizer_size:
        raise AssertionError("normalizer enumeration count failure")
    if stabilizer_count != stabilizer_size:
        raise AssertionError(
            "membership enumeration found the wrong number of stabilizers"
        )
    logical_count = normalizer_size - stabilizer_size
    if sum(logical_distribution) != logical_count:
        raise AssertionError("logical distribution count failure")

    k = n - rank
    matrix_text = _canonical_matrix_text(rows, n)
    return VerificationReport(
        n=n,
        row_count=len(rows),
        rank=rank,
        k=k,
        isotropic=True,
        stabilizer_dimension=rank,
        normalizer_dimension=len(normalizer_basis),
        stabilizer_size=stabilizer_size,
        normalizer_size=normalizer_size,
        logical_vector_count=logical_count,
        stabilizer_weight_distribution=tuple(stabilizer_distribution),
        logical_weight_distribution=tuple(logical_distribution),
        minimum_logical_weight=minimum_weight,
        minimum_logical_witness=minimum_witness,
        normalizer_basis=normalizer_basis,
        matrix_sha256=hashlib.sha256(matrix_text.encode("ascii")).hexdigest(),
    )


def check_claim(
    report: VerificationReport,
    *,
    expected_n: int | None = None,
    expected_rank: int | None = None,
    expected_k: int | None = None,
    exact_distance: int | None = None,
    minimum_distance: int | None = None,
) -> None:
    """Raise VerificationError unless a report satisfies requested parameters."""

    if exact_distance is not None and minimum_distance is not None:
        raise ValueError("choose exact_distance or minimum_distance, not both")
    checks = (
        ("n", report.n, expected_n),
        ("rank", report.rank, expected_rank),
        ("k", report.k, expected_k),
    )
    for label, observed, expected in checks:
        if expected is not None and observed != expected:
            raise VerificationError(f"{label}={observed}; expected {expected}")

    distance = report.minimum_logical_weight
    if exact_distance is not None and distance != exact_distance:
        raise VerificationError(
            f"distance={distance}; required exact distance {exact_distance}"
        )
    if minimum_distance is not None and (
        distance is None or distance < minimum_distance
    ):
        raise VerificationError(
            f"distance={distance}; required distance at least {minimum_distance}"
        )


def classify_vector(
    literal_rows: Sequence[Sequence[int]], vector_row: Sequence[int]
) -> str:
    """Classify a literal vector as stabilizer, logical, or detectable."""

    rows, n = validate_literal_rows(literal_rows)
    if len(vector_row) != 2 * n:
        raise VerificationError(
            f"vector has length {len(vector_row)}; expected {2 * n}"
        )
    for column, bit in enumerate(vector_row):
        if type(bit) is not int or bit not in (0, 1):
            raise VerificationError(
                f"vector[{column}]={bit!r} is not an integer bit"
            )
    vector = pack_row(vector_row)
    if PackedRowSpace(rows, 2 * n).contains(vector):
        return "stabilizer"
    if all(symplectic_inner(row, vector, n) == 0 for row in rows):
        return "logical"
    return "detectable"


def _parse_half(text: str, line_number: int) -> list[int]:
    compact = "".join(character for character in text if not character.isspace())
    compact = compact.replace(",", "")
    if not compact:
        raise VerificationError(f"line {line_number}: empty matrix half")
    invalid = sorted(set(compact) - {"0", "1"})
    if invalid:
        raise VerificationError(
            f"line {line_number}: invalid bit character(s) {invalid}"
        )
    return [int(character) for character in compact]


def parse_literal_matrix(text: str) -> list[list[int]]:
    """Parse one ``X bits | Z bits`` matrix row per line."""

    rows: list[list[int]] = []
    for line_number, raw_line in enumerate(text.splitlines(), start=1):
        line = raw_line.split("#", 1)[0].strip()
        if not line:
            continue
        normalized = "".join(line.split())
        if normalized in {"H=[", "[", "]", "],", "H="}:
            continue
        if "|" not in line:
            raise VerificationError(
                f"line {line_number}: expected exactly one X|Z separator"
            )
        if line.count("|") != 1:
            raise VerificationError(
                f"line {line_number}: expected exactly one X|Z separator"
            )
        if "=" in line:
            line = line.split("=", 1)[1].strip()
        line = line.rstrip(",").strip()
        if line.startswith("["):
            line = line[1:]
        if line.endswith("]"):
            line = line[:-1]
        left, right = line.split("|")
        x_bits = _parse_half(left, line_number)
        z_bits = _parse_half(right, line_number)
        if len(x_bits) != len(z_bits):
            raise VerificationError(
                f"line {line_number}: X half has {len(x_bits)} bits and "
                f"Z half has {len(z_bits)} bits"
            )
        rows.append(x_bits + z_bits)
    if not rows:
        raise VerificationError("input contains no H=[X|Z] rows")
    return rows


def load_literal_matrix(path: Path) -> list[list[int]]:
    try:
        text = path.read_text(encoding="utf-8")
    except OSError as error:
        raise VerificationError(f"cannot read {path}: {error}") from error
    return parse_literal_matrix(text)


def _build_argument_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description=(
            "Exactly verify a binary qubit stabilizer H=[X|Z] and enumerate "
            "its complete symplectic normalizer."
        )
    )
    parser.add_argument("matrix", type=Path, help="literal X|Z matrix text file")
    parser.add_argument("--expect-n", type=int)
    parser.add_argument("--expect-rank", type=int)
    parser.add_argument("--expect-k", type=int)
    distance_group = parser.add_mutually_exclusive_group()
    distance_group.add_argument(
        "--require-distance",
        type=int,
        metavar="D",
        help="require exact minimum logical weight D",
    )
    distance_group.add_argument(
        "--require-at-least-distance",
        type=int,
        metavar="D",
        help="require minimum logical weight at least D",
    )
    parser.add_argument(
        "--compact", action="store_true", help="emit compact rather than indented JSON"
    )
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    parser = _build_argument_parser()
    arguments = parser.parse_args(argv)
    try:
        literal_rows = load_literal_matrix(arguments.matrix)
        report = verify_literal_matrix(literal_rows, expected_n=arguments.expect_n)
        check_claim(
            report,
            expected_n=arguments.expect_n,
            expected_rank=arguments.expect_rank,
            expected_k=arguments.expect_k,
            exact_distance=arguments.require_distance,
            minimum_distance=arguments.require_at_least_distance,
        )
    except VerificationError as error:
        print(f"VERIFICATION FAILED: {error}", file=sys.stderr)
        return 1

    if arguments.compact:
        print(json.dumps(report.as_dict(), sort_keys=True, separators=(",", ":")))
    else:
        print(json.dumps(report.as_dict(), indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
