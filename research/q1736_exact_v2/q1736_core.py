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
    """Enumerate feasible rank-three P column multisets modulo GL(3,2).

    Coordinate permutations reduce P to the multiplicities of its eight
    possible columns. Left multiplication by GL(3,2) only relabels lambda.

    There are 2967 rank-three orbits in total.  A pure [[17,3,6]] candidate
    must additionally satisfy wt(P^T lambda) >= 6 for each nonzero lambda,
    because these are the x=0 logical operators.  Exactly 592 orbits survive
    that necessary condition; only those complete cases are returned.
    """
    actions = invertible_linear_permutations()
    seen: set[tuple[int, ...]] = set()
    rank_three_types: list[tuple[int, ...]] = []
    feasible_types: list[tuple[int, ...]] = []
    for counts in weak_compositions(N, 8):
        if counts in seen:
            continue
        orbit = {act_on_counts(counts, action) for action in actions}
        seen.update(orbit)
        canonical = min(orbit)
        if count_tuple_rank(canonical) != 3:
            continue
        rank_three_types.append(canonical)
        if min(logical_weights_from_counts(canonical)) >= D:
            feasible_types.append(canonical)
    rank_three_types.sort()
    feasible_types.sort()
    if len(rank_three_types) != 2967:
        raise AssertionError(
            "complete rank-three P-orbit enumeration should contain 2967 "
            f"types, found {len(rank_three_types)}"
        )
    if len(feasible_types) != 592:
        raise AssertionError(
            "the logical-weight-at-least-six filter should leave 592 P-orbits, "
            f"found {len(feasible_types)}"
        )
    result: list[dict[str, object]] = []
    for type_id, counts in enumerate(feasible_types):
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
    with output_path.open("w", encoding="utf-8") as handle:
        handle.write(f"p cnf {total_variables} {total_clauses}\n")
        for weight in range(D):
            for support in itertools.combinations(range(N), weight):
                support_set = set(support)
                lambdas = range(1, 8) if weight == 0 else range(8)
                for lam in lambdas:
                    syndrome_variables: list[int] = []
                    for row in range(N):
                        if row in support_set:
                            continue
                        variable = next_variable
                        next_variable += 1
                        syndrome_variables.append(variable)
                        xor_literals = [variable]
                        rhs = parity(lam & columns[row])
                        for column in support:
                            xor_literals.append(edge_variable(row, column))
                        # CryptoMiniSat's `x ... 0` means XOR of literals = 1.
                        # Negating one literal toggles the right-hand side.
                        if rhs == 0:
                            xor_literals[0] = -xor_literals[0]
                        handle.write("x " + " ".join(map(str, xor_literals)) + " 0\n")

                    required = D - weight
                    forbidden_zero_count = len(syndrome_variables) - required + 1
                    for zero_subset in itertools.combinations(
                        syndrome_variables, forbidden_zero_count
                    ):
                        handle.write(" ".join(map(str, zero_subset)) + " 0\n")

    if next_variable != total_variables + 1:
        raise AssertionError(
            f"variable count mismatch: emitted through {next_variable - 1}, "
            f"declared {total_variables}"
        )
    metadata = {
        "format": "q1736-fixed-p-xcnf-v1",
        "n": N,
        "k": K,
        "distance_target": D,
        "counts": [columns.count(value) for value in range(8)],
        "columns": list(columns),
        "edge_variables": EDGE_VARIABLES,
        "syndrome_variables": xor_count,
        "variables": total_variables,
        "xor_clauses": xor_count,
        "cnf_clauses": cnf_count,
        "clauses": total_clauses,
        "sha256": hashlib.sha256(output_path.read_bytes()).hexdigest(),
    }
    if metadata_path is not None:
        metadata_path.parent.mkdir(parents=True, exist_ok=True)
        metadata_path.write_text(json.dumps(metadata, indent=2) + "\n", encoding="utf-8")
    return metadata


def parse_solver_model(text: str, variable_count: int) -> tuple[bool, ...]:
    if "s SATISFIABLE" not in text:
        raise ValueError("solver output does not contain a SAT result")
    assignment = [False] * (variable_count + 1)
    seen: set[int] = set()
    for line in text.splitlines():
        if not line.startswith("v "):
            continue
        for literal_text in line[2:].split():
            literal = int(literal_text)
            if literal == 0:
                continue
            variable = abs(literal)
            if variable <= variable_count:
                assignment[variable] = literal > 0
                seen.add(variable)
    if not all(variable in seen for variable in range(1, EDGE_VARIABLES + 1)):
        raise ValueError("solver model is missing one or more graph variables")
    return tuple(assignment)


def graph_columns_from_assignment(assignment: Sequence[bool]) -> tuple[int, ...]:
    columns = [0] * N
    for variable, (i, j) in enumerate(EDGE_PAIRS, start=1):
        if assignment[variable]:
            columns[i] |= 1 << j
            columns[j] |= 1 << i
    return tuple(columns)


def graph_action(graph_columns: Sequence[int], x: int) -> int:
    result = 0
    while x:
        bit = x & -x
        column = bit.bit_length() - 1
        result ^= graph_columns[column]
        x ^= bit
    return result


def p_transpose_lambda(columns: Sequence[int], lam: int) -> int:
    result = 0
    for coordinate, column in enumerate(columns):
        if parity(lam & column):
            result |= 1 << coordinate
    return result


def verify_graph_candidate(
    graph_columns: Sequence[int], p_columns: Sequence[int]
) -> dict[str, object]:
    if len(graph_columns) != N or len(p_columns) != N:
        raise ValueError("candidate must have length 17")
    if any((graph_columns[i] >> i) & 1 for i in range(N)):
        raise ValueError("graph has a nonzero diagonal")
    if any(
        ((graph_columns[i] >> j) & 1) != ((graph_columns[j] >> i) & 1)
        for i in range(N)
        for j in range(N)
    ):
        raise ValueError("graph is not symmetric")
    if gf2_rank((column for column in p_columns if column), K) != K:
        raise ValueError("P does not have rank three")

    logical_shifts = tuple(p_transpose_lambda(p_columns, lam) for lam in range(8))
    minimum_normalizer_weight = N + 1
    witness: tuple[int, int, int] | None = None
    checked_pairs = 0
    for x in range(1 << N):
        gamma_x = graph_action(graph_columns, x)
        for lam, shift in enumerate(logical_shifts):
            if x == 0 and lam == 0:
                continue
            weight = (x | (gamma_x ^ shift)).bit_count()
            checked_pairs += 1
            if weight < minimum_normalizer_weight:
                minimum_normalizer_weight = weight
                witness = (x, lam, gamma_x ^ shift)
    kernel_basis = gf2_nullspace(tuple(p_columns), N)
    if len(kernel_basis) != N - K:
        raise AssertionError("ker(P) should have dimension fourteen")
    stabilizer_rows = tuple(x | (graph_action(graph_columns, x) << N) for x in kernel_basis)
    rank = gf2_rank(stabilizer_rows, 2 * N)
    if rank != N - K:
        raise AssertionError("constructed stabilizer does not have rank fourteen")

    def symplectic(left: int, right: int) -> int:
        mask = (1 << N) - 1
        left_x, left_z = left & mask, left >> N
        right_x, right_z = right & mask, right >> N
        return parity((left_x & right_z) ^ (left_z & right_x))

    isotropic = all(
        symplectic(left, right) == 0
        for left, right in itertools.combinations(stabilizer_rows, 2)
    )
    if not isotropic:
        raise AssertionError("constructed stabilizer rows do not commute")

    minimum_stabilizer_weight = min(
        (x | graph_action(graph_columns, x)).bit_count()
        for x in range(1, 1 << N)
        if all(parity(column & x) == 0 for column in p_columns)
    )
    accepted = minimum_normalizer_weight >= D and minimum_stabilizer_weight >= D
    return {
        "format": "q1736-verified-graph-candidate-v1",
        "accepted": accepted,
        "n": N,
        "k": K,
        "distance_target": D,
        "normalizer_pairs_checked": checked_pairs,
        "minimum_normalizer_weight": minimum_normalizer_weight,
        "minimum_stabilizer_weight": minimum_stabilizer_weight,
        "minimum_witness": (
            None
            if witness is None
            else {"x": witness[0], "lambda": witness[1], "z": witness[2]}
        ),
        "p_counts": [p_columns.count(value) for value in range(8)],
        "p_columns": list(p_columns),
        "graph_columns": list(graph_columns),
        "stabilizer_rows_packed_xz": list(stabilizer_rows),
    }


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    subparsers = parser.add_subparsers(dest="command", required=True)

    subparsers.add_parser("self-test")

    list_parser = subparsers.add_parser("list-types")
    list_parser.add_argument("--output", type=Path)

    generate_parser = subparsers.add_parser("generate-fixed")
    generate_parser.add_argument("--type-id", type=int, required=True)
    generate_parser.add_argument("--output", type=Path, required=True)
    generate_parser.add_argument("--metadata", type=Path)

    verify_parser = subparsers.add_parser("verify-fixed")
    verify_parser.add_argument("--type-id", type=int, required=True)
    verify_parser.add_argument("--solver-output", type=Path, required=True)
    verify_parser.add_argument("--output", type=Path)

    args = parser.parse_args(argv)
    types = enumerate_p_types()

    if args.command == "self-test":
        report = {
            "format": "q1736-core-self-test-v2",
            "gl3_action_count": len(invertible_linear_permutations()),
            "rank_three_orbit_count": 2967,
            "feasible_p_type_count": len(types),
            "expected_p_type_count": 592,
            "expected_xor_count": expected_xor_count(),
            "expected_cnf_count": expected_cnf_count(),
        }
        if len(types) != 592:
            raise AssertionError("self-test did not recover the 592 feasible P-types")
        print(json.dumps(report, indent=2))
        return 0

    if args.command == "list-types":
        payload = {"format": "q1736-p-types-v2", "types": types}
        text = json.dumps(payload, indent=2) + "\n"
        if args.output:
            args.output.write_text(text, encoding="utf-8")
        else:
            print(text, end="")
        return 0

    type_entry = types[args.type_id]
    counts = tuple(int(value) for value in type_entry["counts"])
    columns = columns_from_counts(counts)

    if args.command == "generate-fixed":
        metadata = generate_fixed_p_xcnf(columns, args.output, args.metadata)
        print(json.dumps(metadata, indent=2))
        return 0

    if args.command == "verify-fixed":
        assignment = parse_solver_model(
            args.solver_output.read_text(encoding="utf-8", errors="replace"),
            EDGE_VARIABLES,
        )
        graph_columns = graph_columns_from_assignment(assignment)
        report = verify_graph_candidate(graph_columns, columns)
        text = json.dumps(report, indent=2) + "\n"
        if args.output:
            args.output.write_text(text, encoding="utf-8")
        else:
            print(text, end="")
        if not report["accepted"]:
            raise SystemExit("solver assignment failed independent verification")
        return 0

    raise AssertionError("unreachable")


if __name__ == "__main__":
    raise SystemExit(main())
