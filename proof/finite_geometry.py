#!/usr/bin/env python3
"""Exact finite checks used by the [[14,3,5]] nonexistence proof.

This module deliberately uses only Python integers and tuples.  It does not
import the enumerator-algebra implementation.  Pauli words are represented by
tuples with I=0, X=1, Z=2, Y=3; multiplication modulo phase is XOR.
"""

from __future__ import annotations

import argparse
import itertools
import json
import sys
from collections import Counter
from typing import Iterable, Iterator, Sequence

N = 14
I, X, Z, Y = range(4)
PAULI = "IXZY"


def add(a: Sequence[int], b: Sequence[int]) -> tuple[int, ...]:
    return tuple(x ^ y for x, y in zip(a, b, strict=True))


def weight(a: Sequence[int]) -> int:
    return sum(x != I for x in a)


def symplectic(a: Sequence[int], b: Sequence[int]) -> int:
    """Binary symplectic product of two phase-free Pauli words."""
    value = 0
    for x, y in zip(a, b, strict=True):
        value ^= ((x & 1) * ((y >> 1) & 1)) ^ (((x >> 1) & 1) * (y & 1))
    return value


def parity_q(a: Sequence[int]) -> int:
    """The weight-parity quadratic refinement."""
    return weight(a) & 1


def parse_pauli(text: str, n: int = N) -> tuple[int, ...]:
    mapping = {"I": I, "X": X, "Z": Z, "Y": Y}
    padded = text + "I" * (n - len(text))
    if len(padded) != n or any(ch not in mapping for ch in padded):
        raise ValueError(f"invalid length-{n} Pauli word: {text!r}")
    return tuple(mapping[ch] for ch in padded)


def pauli_text(word: Sequence[int]) -> str:
    return "".join(PAULI[x] for x in word)


def words_of_weight(w: int, n: int = N) -> Iterator[tuple[int, ...]]:
    for support in itertools.combinations(range(n), w):
        for labels in itertools.product((X, Z, Y), repeat=w):
            word = [I] * n
            for coordinate, label in zip(support, labels, strict=True):
                word[coordinate] = label
            yield tuple(word)


def span_binary(basis: Sequence[int]) -> frozenset[int]:
    values = {0}
    for vector in basis:
        values |= {x ^ vector for x in tuple(values)}
    return frozenset(values)


def symp6(a: int, b: int) -> int:
    """Canonical symplectic product on F_2^3 x F_2^3."""
    ax, az = a & 7, (a >> 3) & 7
    bx, bz = b & 7, (b >> 3) & 7
    return ((ax & bz).bit_count() + (az & bx).bit_count()) & 1


def q6(a: int) -> int:
    return ((a & 7) & ((a >> 3) & 7)).bit_count() & 1


def enumerate_lagrangians() -> list[frozenset[int]]:
    """Enumerate every 3-space isotropic for the canonical form."""
    spaces: set[frozenset[int]] = set()
    for a, b, c in itertools.combinations(range(1, 64), 3):
        space = span_binary((a, b, c))
        if len(space) != 8:
            continue
        if symp6(a, b) or symp6(a, c) or symp6(b, c):
            continue
        spaces.add(space)
    return sorted(spaces, key=lambda s: tuple(sorted(s)))


def lagrangian_certificate() -> dict:
    spaces = enumerate_lagrangians()
    point_incidence = Counter()
    for space in spaces:
        for point in space:
            if point:
                point_incidence[point] += 1

    shifted_singular_counts: dict[int, int] = {}
    for h in range(64):
        shifted_singular_counts[h] = sum(
            all(q6(v) == symp6(h, v) for v in space) for space in spaces
        )

    even_counts = sorted(
        {shifted_singular_counts[h] for h in range(64) if q6(h) == 0}
    )
    odd_counts = sorted(
        {shifted_singular_counts[h] for h in range(64) if q6(h) == 1}
    )
    singular_shifts_per_space = sorted(
        {
            sum(
                all(q6(v) == symp6(h, v) for v in space)
                for h in range(64)
            )
            for space in spaces
        }
    )

    assert len(spaces) == 135
    assert set(point_incidence) == set(range(1, 64))
    assert set(point_incidence.values()) == {15}
    assert sum(q6(h) == 0 for h in range(64)) == 36
    assert sum(q6(h) == 1 for h in range(64)) == 28
    assert even_counts == [30]
    assert odd_counts == [0]
    assert singular_shifts_per_space == [8]
    assert 36 * 30 == 135 * 8
    return {
        "ambient_dimension": 6,
        "lagrangian_dimension": 3,
        "lagrangian_count": len(spaces),
        "nonzero_point_count": len(point_incidence),
        "incidence_per_nonzero_point": min(point_incidence.values()),
        "quadratic_even_shift_count": 36,
        "quadratic_odd_shift_count": 28,
        "singular_lagrangians_per_even_shift": even_counts[0],
        "singular_lagrangians_per_odd_shift": odd_counts[0],
        "singular_shifts_per_lagrangian": singular_shifts_per_space[0],
        "double_count": 36 * 30,
    }


def quadratic_and_coset_certificate() -> dict:
    """Check local quadratic identity and canonical index-two coset algebra."""
    local_words = [(x,) for x in range(4)]
    quadratic_cases = 0
    for a in local_words:
        for b in local_words:
            assert parity_q(add(a, b)) == (
                parity_q(a) ^ parity_q(b) ^ symplectic(a, b)
            )
            quadratic_cases += 1

    # Exact one-coordinate Fourier transform of the anisotropic Pauli
    # quadratic form.  Tensoring 14 copies gives +2^14*(-1)^q(t), which is
    # the sign used in the shadow-Arf lemma.
    local_fourier = {}
    for t in local_words:
        transform = sum(
            (-1) ** (parity_q(b) ^ symplectic(b, t)) for b in local_words
        )
        assert transform == -2 * ((-1) ** parity_q(t))
        local_fourier[pauli_text(t)] = transform
    ambient_n14_gauss_magnitude = 2**14
    quotient_gauss_magnitude = ambient_n14_gauss_magnitude // (2**11)
    assert quotient_gauss_magnitude == 8

    # A canonical exhaustive model for E/B of any finite binary index-two
    # extension.  Linear changes of coordinates reduce every such pair to it.
    dimension = 6
    B = {v for v in range(1 << dimension) if (v & 1) == 0}
    S = {v for v in range(1 << dimension) if (v & 1) == 1}
    assert {s ^ t for s in S for t in S} == B
    assert all({s ^ b for s in S} == S for b in B)
    assert all({s ^ t for t in S} == B for s in S)
    return {
        "quadratic_local_cases": quadratic_cases,
        "local_fourier_transform": local_fourier,
        "ambient_n14_gauss_magnitude": ambient_n14_gauss_magnitude,
        "quotient_dimension6_gauss_magnitude": quotient_gauss_magnitude,
        "canonical_coset_dimension": dimension,
        "subspace_size": len(B),
        "shadow_coset_size": len(S),
        "shadow_plus_shadow_equals_normalizer": True,
        "normalizer_translation_preserves_shadow": True,
    }


def support(word: Sequence[int]) -> set[int]:
    return {i for i, x in enumerate(word) if x}


def pair_signature(u: Sequence[int], v: Sequence[int]) -> tuple[int, int]:
    """(support intersection, equal nonzero labels in the intersection)."""
    common = support(u) & support(v)
    return len(common), sum(u[i] == v[i] for i in common)


P03_FORMS = {
    "rank3_disjoint": (
        parse_pauli("XXXX"),
        parse_pauli("IIIIXXXX"),
        parse_pauli("IIIIIIIIXXXX"),
    ),
    "rank2_p0_t4_q0": (
        parse_pauli("XXXX"),
        parse_pauli("ZZZZ"),
        parse_pauli("YYYY"),
    ),
    "rank2_p1_t3_q1": (
        parse_pauli("XIXXX"),
        parse_pauli("IXXZZ"),
        parse_pauli("XXIYY"),
    ),
    "rank2_p2_t2_q2": (
        parse_pauli("XXIIXX"),
        parse_pauli("IIXXXX"),
        parse_pauli("XXXXII"),
    ),
}


def normal_form_certificate() -> dict:
    """Exhaust the pair signatures after fixing the first word to XXXX.

    Any weight-four Pauli is mapped to XXXX by a coordinate permutation and
    independent one-qubit Clifford label permutations.  The stabilizer of X
    acts transitively on {Z,Y}, so (t,q) completely determines the remaining
    pair up to those same operations.
    """
    u = parse_pauli("XXXX")
    signature_counts: Counter[tuple[int, int]] = Counter()
    commuting_candidates = 0
    for v in words_of_weight(4):
        if v == u or symplectic(u, v):
            continue
        commuting_candidates += 1
        if weight(add(u, v)) == 4:
            signature_counts[pair_signature(u, v)] += 1

    expected_signatures = {(4, 0), (3, 1), (2, 2)}
    assert set(signature_counts) == expected_signatures

    canonical = {}
    for name, generators in P03_FORMS.items():
        assert len(set(generators)) == 3
        assert all(weight(g) == 4 for g in generators)
        assert all(
            symplectic(a, b) == 0
            for a, b in itertools.combinations(generators, 2)
        )
        if name.startswith("rank2"):
            assert add(generators[0], generators[1]) == generators[2]
            assert span_binary_paulis(generators[:2]) == {
                (I,) * N,
                *generators,
            }
            signature = pair_signature(generators[0], generators[1])
            assert signature in expected_signatures
            canonical[name] = {
                "rank": 2,
                "signature": list(signature),
                "generators": [pauli_text(g) for g in generators],
            }
        else:
            assert len(span_binary_paulis(generators)) == 8
            assert all(
                not (support(a) & support(b))
                for a, b in itertools.combinations(generators, 2)
            )
            canonical[name] = {
                "rank": 3,
                "pairwise_disjoint": True,
                "generators": [pauli_text(g) for g in generators],
            }

    # In the rank-three case a pair sum is neither zero nor one of the three
    # listed A4 words.  The already-derived A5=A6=0 forces its weight >= 7.
    # Exhaust all possible canonical pair signatures satisfying that fact.
    rank3_allowed = set()
    for v in words_of_weight(4):
        if v == u or symplectic(u, v):
            continue
        if weight(add(u, v)) >= 7:
            rank3_allowed.add(pair_signature(u, v))
    assert rank3_allowed == {(0, 0)}

    return {
        "fixed_first_word": pauli_text(u),
        "commuting_weight4_candidates": commuting_candidates,
        "rank2_signature_counts": {
            f"{t},{q}": signature_counts[(t, q)]
            for t, q in sorted(signature_counts)
        },
        "rank2_complete_signatures": [list(x) for x in sorted(expected_signatures)],
        "rank3_allowed_pair_signatures_given_no_A5_A6": [
            list(x) for x in sorted(rank3_allowed)
        ],
        "local_clifford_permutation_normal_forms": canonical,
        "normal_form_count": len(canonical),
    }


def span_binary_paulis(
    basis: Sequence[Sequence[int]],
) -> set[tuple[int, ...]]:
    values = {(I,) * len(basis[0])}
    for vector in basis:
        values |= {add(x, vector) for x in tuple(values)}
    return values


def shared_bins(a: Sequence[int], b: Sequence[int]) -> tuple[tuple[int, int], ...]:
    return tuple(
        (i, x) for i, (x, y) in enumerate(zip(a, b, strict=True)) if x and x == y
    )


def collision_degree(word: Sequence[int], stabilizers: Sequence[Sequence[int]]) -> int:
    degree = 0
    for stabilizer in stabilizers:
        mate = add(word, stabilizer)
        if weight(mate) == 3 and shared_bins(word, mate):
            degree += 1
    return degree


def collision_certificate() -> dict:
    words = list(words_of_weight(3))
    assert len(words) == 9828
    expected = {
        "rank3_disjoint": ([9288, 540, 0, 0], 12),
        "rank2_p0_t4_q0": ([9288, 540, 0, 0], 12),
        "rank2_p1_t3_q1": ([9290, 537, 0, 1], 13),
        "rank2_p2_t2_q2": ([9376, 372, 72, 8], 28),
    }
    results = {}
    for name, form in P03_FORMS.items():
        degrees = [collision_degree(word, form) for word in words]
        histogram = [degrees.count(d) for d in range(4)]
        top24_sum = sum(sorted(degrees, reverse=True)[:24])
        upper_bound = top24_sum // 2
        assert sum(histogram) == len(words)
        assert (histogram, upper_bound) == expected[name]
        assert upper_bound < 30
        results[name] = {
            "degree_histogram_d0_to_d3": histogram,
            "maximum_degree": max(degrees),
            "top_24_degree_sum": top24_sum,
            "collision_pair_upper_bound": upper_bound,
            "required_collision_pairs": 30,
            "contradiction": upper_bound < 30,
        }
    return {
        "weight3_word_count": len(words),
        "formula": "C(14,3)*3^3",
        "normal_forms": results,
    }


def orbit_compatible(
    left: tuple[tuple[int, ...], tuple[int, ...]],
    right: tuple[tuple[int, ...], tuple[int, ...]],
    unique_a4: Sequence[int],
) -> bool:
    for a in left:
        for b in right:
            difference = add(a, b)
            if difference != tuple(unique_a4) and weight(difference) < 5:
                return False
    return True


def p01_certificate() -> dict:
    w1 = list(words_of_weight(1))
    w2 = list(words_of_weight(2))
    w3 = list(words_of_weight(3))
    assert (len(w1), len(w2), len(w3)) == (42, 819, 9828)

    # Two distinct S1 words would differ by a forbidden B word of weight <= 2.
    s1_pair_max_difference = max(
        weight(add(a, b)) for a, b in itertools.combinations(w1, 2)
    )
    assert s1_pair_max_difference <= 2

    # An S1 and S2 word would differ by a forbidden B word of weight <= 3.
    s1_s2_max_difference = max(weight(add(a, b)) for a in w1 for b in w2)
    assert s1_s2_max_difference <= 3

    unique_a4 = parse_pauli("XXXX")
    # With one S1 and a fixed unique A4, at most the translated word s+c can
    # be an S3.  Enumerate all 42 canonical possibilities.
    s1_to_s3_counts = []
    for s in w1:
        candidates = [g for g in w3 if add(s, g) == unique_a4]
        s1_to_s3_counts.append(len(candidates))
    assert max(s1_to_s3_counts) <= 1

    # Classify all weight-three translation pairs for the canonical A4 word.
    seen: set[tuple[tuple[int, ...], tuple[int, ...]]] = set()
    pair_types: Counter[tuple[int, int, int]] = Counter()
    colliding_orbits = []
    for g in w3:
        mate = add(g, unique_a4)
        if weight(mate) != 3 or symplectic(g, unique_a4):
            continue
        orbit = tuple(sorted((g, mate)))
        if orbit in seen:
            continue
        seen.add(orbit)
        t = len(support(g) & support(unique_a4))
        d = sum(
            g[i] != unique_a4[i]
            for i in support(g) & support(unique_a4)
        )
        bins = len(shared_bins(g, mate))
        pair_types[(t, d, bins)] += 1
        if bins:
            colliding_orbits.append(orbit)

    assert set(pair_types) == {(2, 0, 1), (3, 2, 0)}
    assert colliding_orbits
    compatible_distinct_pairs = sum(
        orbit_compatible(a, b, unique_a4)
        for a, b in itertools.combinations(colliding_orbits, 2)
    )
    assert compatible_distinct_pairs == 0

    # The repeated-bin inequality used twice in p01.
    repeated_bin_checks = 0
    for bins in (42, 36):
        for incidences in range(73):
            # C(m,2) >= m-1 for every nonempty occupancy m.  Summing gives
            # P >= incidences - occupied_bins >= incidences - bins.
            for occupancy in range(incidences + 1):
                assert occupancy * (occupancy - 1) // 2 >= max(0, occupancy - 1)
                repeated_bin_checks += 1
            if incidences >= bins:
                assert incidences - bins >= 0
        for L in range(25):
            if 3 * L - 1 > bins:
                assert L > (bins + 1) // 3
    assert (42 + 1) // 3 == 14
    assert (36 + 1) // 3 == 12

    # If S2=1, the parity/quadratic argument forces every S3 word to commute
    # with it and have a weight-five sum.  Exhaustively check that this is
    # exactly disjoint support, leaving 12*3=36 possible bins.
    shadow_w2 = parse_pauli("XX")
    admissible_w3 = [
        g
        for g in w3
        if symplectic(shadow_w2, g) == 0 and weight(add(shadow_w2, g)) == 5
    ]
    assert admissible_w3
    assert all(not (support(shadow_w2) & support(g)) for g in admissible_w3)
    disjoint_w3 = [g for g in w3 if not (support(shadow_w2) & support(g))]
    assert set(admissible_w3) == set(disjoint_w3)
    used_bins = {
        (i, label)
        for g in admissible_w3
        for i, label in enumerate(g)
        if label
    }
    assert len(used_bins) == 36

    return {
        "low_weight_word_counts": {
            "weight1": len(w1),
            "weight2": len(w2),
            "weight3": len(w3),
        },
        "S1_at_most_one": {
            "checked_pairs": len(w1) * (len(w1) - 1) // 2,
            "maximum_difference_weight": s1_pair_max_difference,
            "bound": 1,
        },
        "S1_excludes_S2": {
            "checked_pairs": len(w1) * len(w2),
            "maximum_difference_weight": s1_s2_max_difference,
        },
        "S1_bounds_S3": {
            "fixed_A4": pauli_text(unique_a4),
            "checked_S1_words": len(w1),
            "maximum_compatible_S3_words": max(s1_to_s3_counts),
        },
        "unique_A4_translation_pairs": {
            "pair_type_counts": {
                f"t={t},different={d},shared_bins={b}": count
                for (t, d, b), count in sorted(pair_types.items())
            },
            "colliding_orbit_count_before_distance_filter": len(colliding_orbits),
            "compatible_pairs_of_distinct_colliding_orbits": compatible_distinct_pairs,
            "maximum_colliding_orbits_after_distance_filter": 1,
        },
        "repeated_coordinate_pauli_incidence": {
            "integer_inequality_checks": repeated_bin_checks,
            "bins_without_S2": 42,
            "L_bound_without_S2": 14,
            "bins_with_S2": len(used_bins),
            "L_bound_with_S2": 12,
        },
        "S2_equals_one_restriction": {
            "canonical_S2": pauli_text(shadow_w2),
            "admissible_weight3_words": len(admissible_w3),
            "all_supports_disjoint": True,
            "available_coordinate_pauli_bins": len(used_bins),
        },
    }


def build_finite_certificate() -> dict:
    if sys.flags.optimize:
        raise RuntimeError("optimized Python is unsupported: finite assertions must run")
    return {
        "representation": {
            "pauli_encoding": {"I": I, "X": X, "Z": Z, "Y": Y},
            "addition": "coordinatewise XOR; phase discarded",
            "arithmetic": "integers only",
        },
        "quadratic_and_shadow_coset": quadratic_and_coset_certificate(),
        "lagrangian_incidence": lagrangian_certificate(),
        "p03_normal_forms": normal_form_certificate(),
        "weight3_collision_enumeration": collision_certificate(),
        "p01_finite_bounds": p01_certificate(),
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()
    certificate = build_finite_certificate()
    if args.json:
        print(json.dumps(certificate, indent=2, sort_keys=True))
    else:
        print("PASS finite geometry and collision checks")
        print(f"Lagrangians: {certificate['lagrangian_incidence']['lagrangian_count']}")
        print(
            "Weight-3 Paulis:",
            certificate["weight3_collision_enumeration"]["weight3_word_count"],
        )
        print(
            "p03 normal forms:",
            certificate["p03_normal_forms"]["normal_form_count"],
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
