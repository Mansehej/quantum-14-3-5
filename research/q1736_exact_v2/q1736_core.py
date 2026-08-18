#!/usr/bin/env python3
"""Exact fixed-logical-matrix search core for a pure [[17,3,6]] stabilizer.

A graph-state parent is represented by a symmetric zero-diagonal adjacency
matrix Gamma.  A rank-three binary matrix P specifies the codimension-three
subcode C={ (x,Gamma x) : P x = 0 }.  Its normalizer consists exactly of

    (x, Gamma x + P^T lambda),  x in F_2^17, lambda in F_2^3.

Because the enumerator argument proves that any [[17,3,6]] candidate is pure
through weight five, existence is equivalent to

    wt(x OR (Gamma x + P^T lambda)) >= 6

for every pair whose X-support has size at most five, except the zero pair.
This module generates that condition as CryptoMiniSat XOR-CNF and independently
verifies any returned model by exhaustive binary arithmetic.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import math
from pathlib import Path
from typing import Iterable, Iterator, Sequence

N = 17
K = 3
D = 6
EDGE_PAIRS = tuple((i, j) for i in range(N) for j in range(i + 1, N))
EDGE_TO_VAR = {pair: index + 1 for index, pair in enumerate(EDGE_PAIRS)}
EDGE_VARIABLES = len(EDGE_PAIRS)  # 136


def parity(value: int) -> int:
    return value.bit_count() & 1


def gf2_rank(vectors: Iterable[int], width: int) -> int:
    basis: dict[int, int] = {}
    mask = (1 << width) - 1
    for vector in vectors:
        remainder = vector & mask
        while remainder:
            pivot = remainder.bit_length() - 1
            row = basis.get(pivot)
            if row is None:
                basis[pivot] = remainder
                break
            remainder ^= row
    return len(basis)


def gf2_nullspace(equations: Sequence[int], width: int) -> tuple[int, ...]:
    rows = [row & ((1 << width) - 1) for row in equations if row]
    pivot_columns: list[int] = []
    pivot_row = 0
    for column in range(width):
        selected = next(
            (r for r in range(pivot_row, len(rows)) if (rows[r] >> column) & 1),
            None,
        )
        if selected is None:
            continue
        rows[pivot_row], rows[selected] = rows[selected], rows[pivot_row]
        for r in range(len(rows)):
            if r != pivot_row and ((rows[r] >> column) & 1):
                rows[r] ^= rows[pivot_row]
        pivot_columns.append(column)
        pivot_row += 1
        if pivot_row == len(rows):
            break
    rows = rows[:pivot_row]
    pivots = set(pivot_columns)
    basis: list[int] = []
    for free in range(width):
        if free in pivots:
            continue
        vector = 1 << free
        for row, pivot in zip(rows, pivot_columns):
            if (row >> free) & 1:
                vector |= 1 << pivot
        basis.append(vector)
    if gf2_rank(basis, width) != len(basis):
        raise AssertionError("nullspace construction produced dependent vectors")
    if any(parity(eq & vector) for eq in equations for vector in basis):
        raise AssertionError("nullspace construction failed an equation")
    return tuple(basis)


def invertible_linear_permutations() -> tuple[tuple[int, ...], ...]:
    """Return the 168 permutations of F_2^3 induced by GL(3,2)."""
    permutations: set[tuple[int, ...]] = set()
    for r0 in range(1, 8):
        for r1 in range(1, 8):
            for r2 in range(1, 8):
                if gf2_rank((r0, r1, r2), 3) != 3:
                    continue
                image = tuple(
                    parity(r0 & v) | (parity(r1 & v) << 1) | (parity(r2 & v) << 2)
                    for v in range(8)
                )
                permutations.add(image)
    result = tuple(sorted(permutations))
    if len(result) != 168:
        raise AssertionError(f"expected 168 GL(3,2) actions, found {len(result)}")
    return result


def weak_compositions(total: int, parts: int) -> Iterator[tuple[int, ...]]:
    """Generate all ordered weak compositions of total into parts entries."""
    for bars in itertools.combinations(range(total + parts - 1), parts - 1):
        previous = -1
        values: list[int] = []
        for bar in bars + (total + parts - 1,):
            values.append(bar - previous - 1)
            previous = bar
        yield tuple(values)


def act_on_counts(counts: tuple[int, ...], permutation: tuple[int, ...]) -> tuple[int, ...]:
    output = [0] * 8
    for source, count in enumerate(counts):
        output[permutation[source]] = count
    return tuple(output)


def count_tuple_rank(counts: Sequence[int]) -> int:
    return gf2_rank((v for v in range(1, 8) if counts[v]), 3)


def logical_weights_from_counts(counts: Sequence[int]) -> tuple[int, ...]:
    return tuple(
        sum(counts[column] for column in range(8) if parity(lam & column))
        for lam in range(1, 8)
    )


def enumerate_p_types() -> list[dict[str, object]]:
    """Enumerate rank-three P column multisets modulo GL(3,2).

    Coordinate permutations reduce P to the multiplicities of its eight
    possible columns.  Left multiplication by GL(3,2) only relabels lambda, so
    the orbit set below covers every rank-three 3x17 binary matrix.
    """
    actions = invertible_linear_permutations()
    seen: set[tuple[int, ...]] = set()
    canonical_types: list[tuple[int, ...]] = []
    for counts in weak_compositions(N, 8):
        if counts in seen:
            continue
        orbit = {act_on_counts(counts, action) for action in actions}
        seen.update(orbit)
        canonical = min(orbit)
        if count_tuple_rank(canonical) == 3:
            canonical_types.append(canonical)
    canonical_types.sort()
    if len(canonical_types) != 592:
        raise AssertionError(
            f"complete P-orbit enumeration should contain 592 types, found {len(canonical_types)}"
        )
    result: list[dict[str, object]] = []
    for type_id, counts in enumerate(canonical_types):
        weights = logical_weights_from_counts(counts)
        result.append(
            {
                "type_id": type_id,
                "counts": list(counts),
                "logical_weights": list(weights),
                "minimum_logical_weight": min(weights),
                "maximum_logical_weight": max(weights),
            }
        )
    return result


def columns_from_counts(counts: Sequence[int]) -> tuple[int, ...]:
    columns = tuple(value for value, count in enumerate(counts) for _ in range(count))
    if len(columns) != N:
        raise ValueError(f"P counts must sum to {N}")
    if gf2_rank((value for value in columns if value), 3) != 3:
        raise ValueError("P columns must span F_2^3")
    return columns


def edge_variable(i: int, j: int) -> int:
    if i == j:
        raise ValueError("Gamma has zero diagonal")
    if i > j:
        i, j = j, i
    return EDGE_TO_VAR[(i, j)]


def expected_xor_count() -> int:
    return sum(
        math.comb(N, weight)
        * (7 if weight == 0 else 8)
        * (N - weight)
        for weight in range(D)
    )


def expected_cnf_count() -> int:
    total = 0
    for weight in range(D):
        outside = N - weight
        required = D - weight
        clause_size = outside - required + 1
        if clause_size != 12:
            raise AssertionError("the [[17,3,6]] cardinality clauses should all have length 12")
        total += (
            math.comb(N, weight)
            * (7 if weight == 0 else 8)
            * math.comb(outside, clause_size)
        )
    return total


def generate_fixed_p_xcnf(
    columns: Sequence[int],
    output_path: Path,
    metadata_path: Path | None = None,
) -> dict[str, object]:
    """Stream the complete fixed-P XOR-CNF instance to output_path."""
    columns = tuple(int(value) for value in columns)
    if len(columns) != N or any(not 0 <= value < 8 for value in columns):
        raise ValueError("columns must be 17 values in [0,7]")
    if gf2_rank((value for value in columns if value), 3) != 3:
        raise ValueError("P must have rank three")

    xor_count = expected_xor_count()
    cnf_count = expected_cnf_count()
    total_variables = EDGE_VARIABLES + xor_count
    total_clauses = xor_count + cnf_count
    next_variable = EDGE_VARIABLES + 1

    output_path.parent.mkdir(parents=True, exist_ok=True)
    digest = hashlib.sha256()
    with output_path.open("wb", buffering=1024 * 1024) as handle:
        def emit(text: str) -> None:
            encoded = text.encode("ascii")
            handle.write(encoded)
            digest.update(encoded)

        emit(f"p cnf {total_variables} {total_clauses}\n")
        generated_xor = 0
        generated_cnf = 0
        universe = tuple(range(N))
        for weight in range(D):
            for support_tuple in itertools.combinations(universe, weight):
                support = frozenset(support_tuple)
                outside = tuple(i for i in universe if i not in support)
                lambdas = range(1, 8) if weight == 0 else range(8)
                for lam in lambdas:
                    syndrome_variables: list[int] = []
                    for coordinate in outside:
                        y_variable = next_variable
                        next_variable += 1
                        syndrome_variables.append(y_variable)
                        gamma_variables = [
                            edge_variable(coordinate, source) for source in support_tuple
                        ]
                        constant = parity(lam & columns[coordinate])
                        # CryptoMiniSat's x-line has right-hand side one.  Thus
                        #   x -y vars 0  means y XOR vars = 0,
                        #   x  y vars 0  means y XOR vars = 1.
                        signed_y = y_variable if constant else -y_variable
                        literals = " ".join(str(value) for value in (signed_y, *gamma_variables))
                        emit(f"x {literals} 0\n")
                        generated_xor += 1

                    required = D - weight
                    clause_size = len(outside) - required + 1
                    for clause in itertools.combinations(syndrome_variables, clause_size):
                        emit(" ".join(map(str, clause)) + " 0\n")
                        generated_cnf += 1

    if next_variable - 1 != total_variables:
        raise AssertionError((next_variable - 1, total_variables))
    if generated_xor != xor_count or generated_cnf != cnf_count:
        raise AssertionError((generated_xor, xor_count, generated_cnf, cnf_count))

    metadata: dict[str, object] = {
        "format": "CryptoMiniSat XOR-DIMACS",
        "n": N,
        "k": K,
        "distance_target": D,
        "p_columns": list(columns),
        "p_counts": [columns.count(value) for value in range(8)],
        "logical_weights": [
            sum(parity(lam & column) for column in columns) for lam in range(1, 8)
        ],
        "edge_variables": EDGE_VARIABLES,
        "syndrome_auxiliary_variables": xor_count,
        "total_variables": total_variables,
        "xor_clauses": xor_count,
        "cnf_clauses": cnf_count,
        "total_clauses": total_clauses,
        "sha256": digest.hexdigest(),
    }
    if metadata_path is not None:
        metadata_path.parent.mkdir(parents=True, exist_ok=True)
        metadata_path.write_text(json.dumps(metadata, indent=2, sort_keys=True) + "\n")
    return metadata


def parse_cms_model(text: str) -> dict[int, bool]:
    assignments: dict[int, bool] = {}
    for line in text.splitlines():
        stripped = line.strip()
        if not stripped.startswith("v"):
            continue
        for token in stripped[1:].split():
            literal = int(token)
            if literal == 0:
                continue
            assignments[abs(literal)] = literal > 0
    return assignments


def gamma_rows_from_assignment(assignment: dict[int, bool]) -> tuple[int, ...]:
    rows = [0] * N
    for variable, (i, j) in enumerate(EDGE_PAIRS, start=1):
        if assignment.get(variable, False):
            rows[i] |= 1 << j
            rows[j] |= 1 << i
    return tuple(rows)


def gamma_times(rows: Sequence[int], vector: int) -> int:
    result = 0
    for coordinate, row in enumerate(rows):
        if parity(row & vector):
            result |= 1 << coordinate
    return result


def p_times(columns: Sequence[int], vector: int) -> int:
    result = 0
    for row in range(3):
        mask = sum(1 << i for i, column in enumerate(columns) if (column >> row) & 1)
        result |= parity(mask & vector) << row
    return result


def pt_times(columns: Sequence[int], lam: int) -> int:
    return sum(
        (parity(column & lam) << coordinate)
        for coordinate, column in enumerate(columns)
    )


def enumerate_span_gray(basis: Sequence[int]) -> Iterator[int]:
    value = 0
    previous_gray = 0
    yield value
    for index in range(1, 1 << len(basis)):
        gray = index ^ (index >> 1)
        changed = gray ^ previous_gray
        value ^= basis[changed.bit_length() - 1]
        previous_gray = gray
        yield value


def split_bits(vector: int) -> str:
    x = "".join(str((vector >> i) & 1) for i in range(N))
    z = "".join(str((vector >> (N + i)) & 1) for i in range(N))
    return f"{x}|{z}"


def verify_graph_candidate(
    columns: Sequence[int],
    assignment: dict[int, bool],
    exhaustive_normalizer: bool = True,
) -> dict[str, object]:
    columns = tuple(columns)
    if len(columns) != N or gf2_rank((value for value in columns if value), 3) != 3:
        raise ValueError("invalid rank-three P")
    missing = [variable for variable in range(1, EDGE_VARIABLES + 1) if variable not in assignment]
    if missing:
        raise ValueError(f"model omits original variables, beginning with {missing[:5]}")
    gamma_rows = gamma_rows_from_assignment(assignment)
    if any((gamma_rows[i] >> i) & 1 for i in range(N)):
        raise AssertionError("Gamma diagonal is nonzero")
    for i in range(N):
        for j in range(N):
            if ((gamma_rows[i] >> j) & 1) != ((gamma_rows[j] >> i) & 1):
                raise AssertionError("Gamma is not symmetric")

    checked_low_weight = 0
    minimum_checked = 2 * N
    minimum_checked_pair: tuple[int, int] | None = None
    universe = tuple(range(N))
    for support_weight in range(D):
        for support in itertools.combinations(universe, support_weight):
            x = sum(1 << coordinate for coordinate in support)
            lambdas = range(1, 8) if x == 0 else range(8)
            gx = gamma_times(gamma_rows, x)
            for lam in lambdas:
                z = gx ^ pt_times(columns, lam)
                pauli_weight = (x | z).bit_count()
                checked_low_weight += 1
                if pauli_weight < minimum_checked:
                    minimum_checked = pauli_weight
                    minimum_checked_pair = (x, lam)
                if pauli_weight < D:
                    raise ValueError(
                        f"candidate has forbidden normalizer representative: "
                        f"x={x:#x}, lambda={lam}, weight={pauli_weight}"
                    )

    p_rows = tuple(
        sum(1 << coordinate for coordinate, column in enumerate(columns) if (column >> row) & 1)
        for row in range(3)
    )
    kernel_basis = gf2_nullspace(p_rows, N)
    if len(kernel_basis) != N - K:
        raise AssertionError("ker(P) should have dimension 14")

    h_rows: list[int] = []
    for x in kernel_basis:
        z = gamma_times(gamma_rows, x)
        h_rows.append(x | (z << N))
    if gf2_rank(h_rows, 2 * N) != N - K:
        raise AssertionError("constructed stabilizer does not have rank 14")
    mask = (1 << N) - 1
    for left_index, left in enumerate(h_rows):
        lx, lz = left & mask, (left >> N) & mask
        for right in h_rows[left_index + 1 :]:
            rx, rz = right & mask, (right >> N) & mask
            if parity((lx & rz) ^ (lz & rx)):
                raise AssertionError("constructed stabilizer generators do not commute")

    minimum_stabilizer_weight = N + 1
    for x in enumerate_span_gray(kernel_basis):
        if x == 0:
            continue
        minimum_stabilizer_weight = min(
            minimum_stabilizer_weight,
            (x | gamma_times(gamma_rows, x)).bit_count(),
        )
    if minimum_stabilizer_weight < D:
        raise AssertionError("candidate is not pure through weight five")

    minimum_logical_weight: int | None = None
    minimum_logical_witness: tuple[int, int, int] | None = None
    normalizer_vectors_checked = 0
    if exhaustive_normalizer:
        for x in range(1 << N):
            gx = gamma_times(gamma_rows, x)
            px = p_times(columns, x)
            for lam in range(8):
                if lam == 0 and px == 0:
                    continue  # exactly the stabilizer C
                z = gx ^ pt_times(columns, lam)
                weight = (x | z).bit_count()
                normalizer_vectors_checked += 1
                if minimum_logical_weight is None or weight < minimum_logical_weight:
                    minimum_logical_weight = weight
                    minimum_logical_witness = (x, z, lam)
        if minimum_logical_weight is None or minimum_logical_weight < D:
            raise AssertionError("exhaustive normalizer check failed the target distance")

    return {
        "verified": True,
        "parameters": [N, K, minimum_logical_weight],
        "target_distance": D,
        "p_columns": list(columns),
        "p_counts": [columns.count(value) for value in range(8)],
        "logical_weights_at_x_zero": [
            pt_times(columns, lam).bit_count() for lam in range(1, 8)
        ],
        "gamma_rows_hex": [hex(row) for row in gamma_rows],
        "low_weight_pairs_checked": checked_low_weight,
        "minimum_weight_in_low_support_check": minimum_checked,
        "minimum_low_support_pair": (
            None
            if minimum_checked_pair is None
            else {"x": hex(minimum_checked_pair[0]), "lambda": minimum_checked_pair[1]}
        ),
        "stabilizer_rank": len(kernel_basis),
        "minimum_stabilizer_weight": minimum_stabilizer_weight,
        "normalizer_vectors_checked": normalizer_vectors_checked,
        "minimum_logical_weight": minimum_logical_weight,
        "minimum_logical_witness": (
            None
            if minimum_logical_witness is None
            else {
                "x": hex(minimum_logical_witness[0]),
                "z": hex(minimum_logical_witness[1]),
                "lambda": minimum_logical_witness[2],
            }
        ),
        "H_binary_symplectic": [split_bits(row) for row in h_rows],
    }


def self_test() -> dict[str, object]:
    types = enumerate_p_types()
    xor_count = expected_xor_count()
    cnf_count = expected_cnf_count()
    if xor_count != 936343:
        raise AssertionError(xor_count)
    if cnf_count != 1577940:
        raise AssertionError(cnf_count)
    eligible = [entry for entry in types if entry["minimum_logical_weight"] >= D]
    return {
        "gl_order": len(invertible_linear_permutations()),
        "all_rank_three_p_orbits": len(types),
        "eligible_after_x_zero_distance_filter": len(eligible),
        "xor_count_per_fixed_p_instance": xor_count,
        "cnf_count_per_fixed_p_instance": cnf_count,
        "variables_per_fixed_p_instance": EDGE_VARIABLES + xor_count,
        "clauses_per_fixed_p_instance": xor_count + cnf_count,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    subparsers = parser.add_subparsers(dest="command", required=True)

    subparsers.add_parser("self-test")

    list_parser = subparsers.add_parser("list-types")
    list_parser.add_argument("--output", type=Path, required=True)
    list_parser.add_argument("--eligible-only", action="store_true")

    generate_parser = subparsers.add_parser("generate")
    generate_parser.add_argument("--type-id", type=int, required=True)
    generate_parser.add_argument("--output", type=Path, required=True)
    generate_parser.add_argument("--metadata", type=Path, required=True)

    verify_parser = subparsers.add_parser("verify")
    verify_parser.add_argument("--type-id", type=int, required=True)
    verify_parser.add_argument("--solver-output", type=Path, required=True)
    verify_parser.add_argument("--report", type=Path, required=True)
    verify_parser.add_argument("--skip-full-normalizer", action="store_true")

    args = parser.parse_args()
    types = enumerate_p_types()

    if args.command == "self-test":
        print(json.dumps(self_test(), indent=2, sort_keys=True))
        return 0

    if args.command == "list-types":
        selected = types
        if args.eligible_only:
            selected = [entry for entry in types if entry["minimum_logical_weight"] >= D]
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(selected, indent=2, sort_keys=True) + "\n")
        return 0

    if not 0 <= args.type_id < len(types):
        parser.error("type id is outside [0,591]")
    entry = types[args.type_id]
    columns = columns_from_counts(entry["counts"])

    if args.command == "generate":
        metadata = generate_fixed_p_xcnf(columns, args.output, args.metadata)
        metadata["type"] = entry
        args.metadata.write_text(json.dumps(metadata, indent=2, sort_keys=True) + "\n")
        print(json.dumps(metadata, sort_keys=True))
        return 0

    if args.command == "verify":
        model_text = args.solver_output.read_text(errors="replace")
        assignment = parse_cms_model(model_text)
        report = verify_graph_candidate(
            columns,
            assignment,
            exhaustive_normalizer=not args.skip_full_normalizer,
        )
        report["type"] = entry
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
        print(json.dumps(report, sort_keys=True))
        return 0

    raise AssertionError("unreachable")


if __name__ == "__main__":
    raise SystemExit(main())
