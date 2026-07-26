#!/usr/bin/env python3
"""Deterministic one-command replay for the [[14,3,5]] nonexistence proof."""

from __future__ import annotations

import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any, Sequence


PROOF = Path(__file__).resolve().parent
ROOT = PROOF.parent
GENERATED = PROOF / "generated"
CLAIMS = PROOF / "claims" / "theorem.json"
PYTHON = Path(sys.executable).resolve()

GENERATED_ARTIFACTS = (
    "certificate.json",
    "cleanroom_certificate.json",
    "algebra_certificate.json",
    "finite_geometry_certificate.json",
    "js_cleanroom_certificate.json",
    "consensus.json",
    "versions.json",
    "report.json",
    "REPORT.txt",
    "replay.log",
)
DEPRECATED_GENERATED = (
    "primary_results.json",
    "cleanroom_results.json",
)

LOG: list[str] = [
    "Binary stabilizer [[14,3,5]] proof deterministic replay",
]
TEMP_ROOT: Path | None = None
CHILD_ENV: dict[str, str] = {}
NODE: Path | None = None
PYTHON_CALL_INDEX = 0


class ReplayFailure(RuntimeError):
    """A deterministic replay failure."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ReplayFailure(message)


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        while chunk := handle.read(1 << 20):
            digest.update(chunk)
    return digest.hexdigest()


def write_json(path: Path, value: object) -> None:
    path.write_text(
        json.dumps(value, sort_keys=True, indent=2) + "\n",
        encoding="utf-8",
    )


def load_json(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    require(isinstance(value, dict), f"{path} does not contain a JSON object")
    return value


def render_command(command: Sequence[str | Path]) -> str:
    rendered: list[str] = []
    for item in command:
        text = str(item)
        if text == str(PYTHON):
            text = "python3"
        elif NODE is not None and text == str(NODE):
            text = "node"
        if TEMP_ROOT is not None:
            text = text.replace(str(TEMP_ROOT), "<FRESH_TEMP>")
        text = text.replace(str(ROOT), "<PACKAGE_ROOT>")
        rendered.append(text)
    return " ".join(rendered)


def normalize_output(text: str) -> str:
    if TEMP_ROOT is not None:
        text = text.replace(str(TEMP_ROOT), "<FRESH_TEMP>")
    text = text.replace(str(ROOT), "<PACKAGE_ROOT>")
    text = re.sub(r"Ran (\d+) tests in [0-9.]+s", r"Ran \1 tests", text)
    text = re.sub(
        r"(duration_ms:\s*)[0-9.]+", r"\1<normalized>", text
    )
    text = re.sub(
        r"(# duration_ms\s+)[0-9.]+", r"\1<normalized>", text
    )
    return text.rstrip()


def execute(
    label: str,
    command: Sequence[str | Path],
    *,
    cwd: Path = ROOT,
    include_stdout: bool = True,
) -> subprocess.CompletedProcess[str]:
    result = subprocess.run(
        [str(item) for item in command],
        cwd=cwd,
        env=CHILD_ENV,
        text=True,
        capture_output=True,
        check=False,
        timeout=900,
    )
    LOG.append(f"$ {render_command(command)}")
    LOG.append(f"[{label}] exit={result.returncode}")
    if include_stdout and result.stdout.strip():
        LOG.append(normalize_output(result.stdout))
    elif result.stdout:
        digest = hashlib.sha256(result.stdout.encode("utf-8")).hexdigest()
        LOG.append(f"[stdout suppressed] sha256={digest}")
    if result.stderr.strip():
        LOG.append(normalize_output(result.stderr))
    if result.returncode:
        detail = normalize_output(result.stderr or result.stdout)
        raise ReplayFailure(
            f"{label} failed with exit {result.returncode}: {detail}"
        )
    return result


def python_command(script_or_module: str | Path, *arguments: str | Path) -> list[str | Path]:
    global PYTHON_CALL_INDEX
    require(TEMP_ROOT is not None, "fresh temporary root is not initialized")
    PYTHON_CALL_INDEX += 1
    cache = TEMP_ROOT / f"pycache-{PYTHON_CALL_INDEX:02d}"
    return [
        PYTHON,
        "-I",
        "-X",
        f"pycache_prefix={cache}",
        script_or_module,
        *arguments,
    ]


def stdout_json_certificate(
    label: str,
    command_factory: Any,
    destination: Path,
) -> dict[str, Any]:
    first = execute(label, command_factory(), include_stdout=False)
    try:
        value = json.loads(first.stdout)
    except json.JSONDecodeError as error:
        raise ReplayFailure(f"{label} emitted invalid JSON: {error}") from error
    require(isinstance(value, dict), f"{label} did not emit a JSON object")
    second = execute(
        f"{label}-byte-replay", command_factory(), include_stdout=False
    )
    require(
        first.stdout.encode("utf-8") == second.stdout.encode("utf-8"),
        f"{label} output is not byte reproducible",
    )
    destination.write_text(first.stdout, encoding="utf-8")
    return value


def file_json_certificate(
    label: str,
    command_factory: Any,
    destination: Path,
) -> dict[str, Any]:
    if destination.exists():
        destination.unlink()
    execute(label, command_factory(destination))
    require(destination.is_file(), f"{label} did not create {destination.name}")
    first = destination.read_bytes()
    require(TEMP_ROOT is not None, "fresh temporary root is not initialized")
    second_path = TEMP_ROOT / f"{destination.stem}-second.json"
    execute(
        f"{label}-byte-replay",
        command_factory(second_path),
        include_stdout=False,
    )
    require(second_path.is_file(), f"{label} second run produced no JSON")
    require(
        first == second_path.read_bytes(),
        f"{label} output is not byte reproducible",
    )
    return load_json(destination)


def exact_agreement(
    comparisons: dict[str, str],
    name: str,
    *values: object,
) -> None:
    require(len(values) >= 2, f"comparison {name} has fewer than two values")
    first = values[0]
    require(
        all(value == first for value in values[1:]),
        f"independent disagreement in {name}",
    )
    comparisons[name] = "exact agreement"


def padded_histogram(values: Sequence[int]) -> list[int]:
    result = list(values)
    require(len(result) <= 4, f"invalid collision histogram length {len(result)}")
    return result + [0] * (4 - len(result))


def compare_certificates(
    claims: dict[str, Any],
    primary: dict[str, Any],
    cleanroom: dict[str, Any],
    algebra: dict[str, Any],
    finite: dict[str, Any],
    javascript: dict[str, Any],
) -> dict[str, Any]:
    comparisons: dict[str, str] = {}

    require(primary.get("verdict") == "PASS", "primary verdict is not PASS")
    require(cleanroom.get("verdict") == "PASS", "clean-room verdict is not PASS")
    require(algebra.get("status") == "PASS", "exact-algebra status is not PASS")
    require(
        "machine-verified" in primary.get("claim_status", ""),
        "primary output lost the machine-verified label",
    )
    require(
        "machine-verified" in cleanroom.get("claim_status", ""),
        "clean-room output lost the machine-verified label",
    )

    primary_checks = set(primary["checks"])
    required_checks = set(claims["required_checks"])
    exact_agreement(
        comparisons,
        "required-check coverage",
        sorted(primary_checks - {"COVERAGE.REQUIRED"}),
        sorted(required_checks),
    )
    require(
        primary["checks"]["COVERAGE.REQUIRED"]["missing"] == [],
        "primary required-check ledger reports missing checks",
    )

    exact_relation = algebra["all_even"]["scaled_relation"][
        "zero_form_coefficients_constant_A2_A4_A6"
    ]
    exact_agreement(
        comparisons,
        "all-even elimination relation",
        primary["facts"]["even"]["elimination_relation"],
        exact_relation[1:] + exact_relation[:1],
    )

    exact_odd = dict(
        algebra["odd_51_identity"]["combined_nonzero_coefficients"]
    )
    exact_odd["constant"] = -algebra["odd_51_identity"]["combined_rhs"]
    exact_agreement(
        comparisons,
        "odd coefficient identity 51",
        primary["facts"]["odd"]["identity"],
        cleanroom["checks"]["CLEAN.ODD.IDENTITY51"],
        exact_odd,
    )
    exact_agreement(
        comparisons,
        "odd profile reduction",
        primary["facts"]["odd"]["profiles"],
        algebra["odd_51_identity"]["profile_reduction"]["possible_A2_A4"],
    )

    exact_i = (
        algebra["anti_macwilliams"]["I14"][
            "identity_coefficients_after_g14"
        ]
        + [1]
    )
    exact_ii = (
        algebra["anti_macwilliams"]["IS3"][
            "identity_coefficients_after_16S3"
        ]
        + [16]
    )
    exact_agreement(
        comparisons,
        "anti-MacWilliams identity I14",
        primary["facts"]["algebra"]["identity_i"],
        cleanroom["checks"]["CLEAN.ANTI"]["identity_i"],
        exact_i,
    )
    exact_agreement(
        comparisons,
        "anti-MacWilliams identity IS3",
        primary["facts"]["algebra"]["identity_ii"],
        cleanroom["checks"]["CLEAN.ANTI"]["identity_ii"],
        exact_ii,
    )

    exact_agreement(
        comparisons,
        "self-dual extension p03 base enumerator",
        primary["facts"]["p03"]["enumerators"]["N"],
        cleanroom["checks"]["CLEAN.ENUM.P03"]["N"],
        algebra["selfdual_extensions"]["profiles"]["p03"]["enumerator"],
    )
    exact_agreement(
        comparisons,
        "forced p03 A enumerator",
        primary["facts"]["p03"]["enumerators"]["A"],
        cleanroom["checks"]["CLEAN.ENUM.P03"]["A"],
        algebra["forced_p03_enumerators"]["A"],
    )
    exact_agreement(
        comparisons,
        "forced p03 B enumerator",
        primary["facts"]["p03"]["enumerators"]["B"],
        cleanroom["checks"]["CLEAN.ENUM.P03"]["B"],
        algebra["forced_p03_enumerators"]["B"],
    )
    exact_agreement(
        comparisons,
        "forced p03 shadow enumerator",
        primary["facts"]["p03"]["enumerators"]["S"],
        cleanroom["checks"]["CLEAN.ENUM.P03"]["S"],
        algebra["forced_p03_enumerators"]["S"],
    )

    p11_primary = sorted(
        (
            row["A14"],
            row["S4"],
            row["required_S2"],
        )
        for row in primary["facts"]["p11"]["integrality"]
    )
    p11_algebra = sorted(
        (
            row["A14"],
            row["S4"],
            row["required_S2"],
        )
        for row in algebra["profile_eliminations"]["p11"]["cases"]
    )
    exact_agreement(
        comparisons, "p11 nonintegral eliminations", p11_primary, p11_algebra
    )

    p01_primary = primary["facts"]["p01"]["formulas"]
    p01_algebra = algebra["profile_eliminations"]["p01"]
    exact_agreement(
        comparisons,
        "p01 A6 formula",
        [
            p01_primary["b"]["constant"],
            p01_primary["b"]["coefficients"]["a"],
            p01_primary["b"]["coefficients"]["m"],
            p01_primary["b"]["coefficients"]["r"],
            p01_primary["b"]["coefficients"]["s"],
        ],
        [
            p01_algebra["A6_formula"]["constant"],
            p01_algebra["A6_formula"]["A5"],
            p01_algebra["A6_formula"]["S2"],
            p01_algebra["A6_formula"]["S4"],
            p01_algebra["A6_formula"]["S1"],
        ],
    )
    exact_agreement(
        comparisons,
        "p01 A14 formula",
        [
            p01_primary["c"]["constant"],
            p01_primary["c"]["coefficients"]["a"],
            p01_primary["c"]["coefficients"]["m"],
            p01_primary["c"]["coefficients"]["r"],
            p01_primary["c"]["coefficients"]["s"],
        ],
        [
            p01_algebra["A14_formula"]["constant"],
            p01_algebra["A14_formula"]["A5"],
            p01_algebra["A14_formula"]["S2"],
            p01_algebra["A14_formula"]["S4"],
            p01_algebra["A14_formula"]["S1"],
        ],
    )
    exact_agreement(
        comparisons,
        "p01 S3 formula",
        [
            p01_primary["S3"]["constant"],
            p01_primary["S3"]["coefficients"]["a"],
            p01_primary["S3"]["coefficients"]["m"],
            p01_primary["S3"]["coefficients"]["r"],
            p01_primary["S3"]["coefficients"]["s"],
        ],
        [
            p01_algebra["S3_formula"]["constant"],
            p01_algebra["S3_formula"]["A5"],
            p01_algebra["S3_formula"]["S2"],
            p01_algebra["S3_formula"]["S4"],
            p01_algebra["S3_formula"]["S1"],
        ],
    )

    lag_primary = primary["facts"]["geometry"]["lagrangian_6d"]
    lag_clean = cleanroom["checks"]["CLEAN.LAGRANGIAN"]
    lag_finite = finite["lagrangian_incidence"]
    exact_agreement(
        comparisons,
        "six-dimensional Lagrangian count/incidence",
        [
            lag_primary["lagrangians"],
            lag_primary["point_incidence_min"],
            lag_primary["point_incidence_max"],
        ],
        [
            lag_clean["lagrangians"],
            lag_clean["point_incidence_min"],
            lag_clean["point_incidence_max"],
        ],
        [
            lag_finite["lagrangian_count"],
            lag_finite["incidence_per_nonzero_point"],
            lag_finite["incidence_per_nonzero_point"],
        ],
    )
    shadow = primary["facts"]["geometry"]["shadow_incidence_8d"]
    require(
        [
            shadow["extensions"],
            shadow["shadow_sizes"],
            shadow["eligible_even_vectors"],
            shadow["eligible_incidence_min"],
            shadow["eligible_incidence_max"],
            shadow["total_incidence"],
            shadow["anisotropic_orbit"],
        ]
        == [135, [16], 72, 30, 30, 2160, 120],
        "eight-dimensional shadow-incidence exhaustion changed",
    )
    exact_agreement(
        comparisons,
        "even/odd extension-shadow incidence",
        [
            shadow["eligible_incidence_min"],
            0,
        ],
        [
            lag_finite["singular_lagrangians_per_even_shift"],
            lag_finite["singular_lagrangians_per_odd_shift"],
        ],
    )
    quadratic = finite["quadratic_and_shadow_coset"]
    require(
        quadratic["quadratic_local_cases"] == 16
        and quadratic["shadow_plus_shadow_equals_normalizer"] is True
        and quadratic["normalizer_translation_preserves_shadow"] is True,
        "finite shadow-coset translation checks changed",
    )

    p01_clean = cleanroom["checks"]["CLEAN.P01.COLLISION"]
    exact_agreement(
        comparisons,
        "p01 90-orbit collision obstruction",
        primary["facts"]["p01"]["collision"],
        p01_clean,
    )
    p01_finite = finite["p01_finite_bounds"]
    require(
        p01_finite["S1_at_most_one"]["bound"] == 1,
        "finite S1 bound changed",
    )
    require(
        p01_finite["unique_A4_translation_pairs"][
            "colliding_orbit_count_before_distance_filter"
        ]
        == 90
        and p01_finite["unique_A4_translation_pairs"][
            "compatible_pairs_of_distinct_colliding_orbits"
        ]
        == 0,
        "finite p01 orbit obstruction changed",
    )
    exact_agreement(
        comparisons,
        "p01 repeated-bin bounds",
        [
            primary["checks"]["P01.BINS_42"]["bins"],
            primary["checks"]["P01.BINS_42"]["integer_upper_bound"],
            primary["checks"]["P01.BINS_36"]["remaining_bins"],
            primary["checks"]["P01.BINS_36"]["integer_upper_bound"],
        ],
        [
            p01_finite["repeated_coordinate_pauli_incidence"][
                "bins_without_S2"
            ],
            p01_finite["repeated_coordinate_pauli_incidence"][
                "L_bound_without_S2"
            ],
            p01_finite["repeated_coordinate_pauli_incidence"]["bins_with_S2"],
            p01_finite["repeated_coordinate_pauli_incidence"][
                "L_bound_with_S2"
            ],
        ],
        [42, 14, 36, 12],
    )
    exact_agreement(
        comparisons,
        "p01 S2=1 disjoint-support enumeration",
        [
            primary["checks"]["P01.BINS_36"][
                "admissible_weight_three_words"
            ],
            primary["checks"]["P01.BINS_36"]["disjoint_weight_three_words"],
            primary["checks"]["P01.BINS_36"][
                "support_disjointness_equivalent"
            ],
        ],
        [
            p01_finite["S2_equals_one_restriction"][
                "admissible_weight3_words"
            ],
            p01_finite["S2_equals_one_restriction"][
                "admissible_weight3_words"
            ],
            p01_finite["S2_equals_one_restriction"]["all_supports_disjoint"],
        ],
    )

    primary_forms = primary["facts"]["normal_forms"]
    clean_forms = cleanroom["checks"]["CLEAN.NORMAL_FORMS"]
    exact_agreement(
        comparisons,
        "symbolic local-Clifford normal-form reduction",
        {
            "local_orbits": primary_forms["local_orbit_count"],
            "rank2": primary_forms["rank2_category_solutions"],
            "rank3": primary_forms["rank3_pair_solutions"],
            "representatives": primary_forms["representatives"],
        },
        {
            "local_orbits": clean_forms["local_orbits"],
            "rank2": clean_forms["rank2_category_solutions"],
            "rank3": clean_forms["rank3_pair_solutions"],
            "representatives": clean_forms["representatives"],
        },
    )
    require(
        set(primary_forms["representatives"])
        == {"independent", "p0", "p1", "p2"},
        "primary normal-form set is not exactly four forms",
    )
    require(
        all(item["commuting"] for item in primary_forms["validation"].values())
        and primary_forms["validation"]["independent"]["rank"] == 3
        and all(
            primary_forms["validation"][name]["rank"] == 2
            for name in ("p0", "p1", "p2")
        ),
        "normal-form rank or commutation validation changed",
    )

    finite_form_names = {
        "independent": "rank3_disjoint",
        "p0": "rank2_p0_t4_q0",
        "p1": "rank2_p1_t3_q1",
        "p2": "rank2_p2_t2_q2",
    }
    javascript_form_names = {
        "independent": "disjoint",
        "p0": "p0",
        "p1": "p1",
        "p2": "p2",
    }
    finite_forms = finite["p03_normal_forms"][
        "local_clifford_permutation_normal_forms"
    ]
    for primary_name in ("independent", "p0", "p1", "p2"):
        exact_agreement(
            comparisons,
            f"{primary_name} canonical representative",
            primary_forms["representatives"][primary_name],
            finite_forms[finite_form_names[primary_name]]["generators"],
            javascript["normalForms"][
                javascript_form_names[primary_name]
            ]["generators"],
        )

    exact_agreement(
        comparisons,
        "rank-two fixed-first exhaustive signatures",
        finite["p03_normal_forms"]["rank2_signature_counts"],
        javascript["rankTwoPlaneEnumeration"]["signatureCounts"],
    )
    require(
        finite["p03_normal_forms"][
            "rank3_allowed_pair_signatures_given_no_A5_A6"
        ]
        == [[0, 0]],
        "rank-three disjoint-pair exhaustion changed",
    )
    require(
        javascript["rankTwoPlaneEnumeration"]["candidateSecondWords"] == 81081
        and javascript["rankTwoPlaneEnumeration"]["normalizationFailures"] == 0,
        "JavaScript normal-form enumeration is incomplete",
    )

    require(
        primary["checks"]["P03.WORDS_9828"]["generated"] == 9828
        and finite["weight3_collision_enumeration"]["weight3_word_count"] == 9828
        and javascript["weightThreeEnumeration"]["wordCount"] == 9828,
        "a weight-three enumerator did not produce exactly 9,828 words",
    )
    exact_agreement(
        comparisons,
        "primary/clean-room collision tables",
        primary["facts"]["p03"]["collisions"],
        cleanroom["checks"]["CLEAN.COLLISIONS"],
    )

    upper_bounds: dict[str, int] = {}
    for primary_name in ("independent", "p0", "p1", "p2"):
        primary_collision = primary["facts"]["p03"]["collisions"][primary_name]
        finite_collision = finite["weight3_collision_enumeration"][
            "normal_forms"
        ][finite_form_names[primary_name]]
        js_collision = javascript["normalForms"][
            javascript_form_names[primary_name]
        ]
        exact_agreement(
            comparisons,
            f"{primary_name} collision-degree histogram",
            padded_histogram(primary_collision["all_words"]),
            finite_collision["degree_histogram_d0_to_d3"],
            js_collision["degreeHistogram"],
        )
        exact_agreement(
            comparisons,
            f"{primary_name} top-24 collision upper bound",
            primary_collision["top24_edge_upper_bound"],
            finite_collision["collision_pair_upper_bound"],
            js_collision["collisionUpperBound"],
        )
        upper_bounds[primary_name] = primary_collision[
            "top24_edge_upper_bound"
        ]

    contradiction = primary["checks"]["P03.COLLISION_CONTRADICTION"]
    exact_agreement(
        comparisons,
        "p03 collision contradiction upper bounds",
        contradiction["upper_bounds"],
        upper_bounds,
    )
    require(
        contradiction["lower_bound"] == 30
        and all(bound < contradiction["lower_bound"] for bound in upper_bounds.values()),
        "p03 collision bounds no longer contradict",
    )
    require(
        primary["checks"]["P03.IDENTITY_BRANCH"]["nonnegative_solutions"]
        == [{"A14": 0, "A5": 0, "A6": 0, "S1": 0, "S4": 0}],
        "p03 coefficient-identity branch is not uniquely forced",
    )

    return {
        "schema": "quantum-14-3-5-proof-consensus-v1",
        "verdict": "PASS",
        "claim_status": "machine-verified proof artifact; see the accompanying paper",
        "comparisons": dict(sorted(comparisons.items())),
        "implementations": [
            "claims-driven packed-symplectic exact Python checker",
            "standalone literal-Pauli/RREF clean-room Python checker",
            "independent Fraction-based exact-algebra Python checker",
            "independent finite-geometry Python enumerator",
            "independently authored literal-Pauli JavaScript enumerator",
        ],
        "byte_reproducible_certificates": 5,
    }


def parse_python_tests(result: subprocess.CompletedProcess[str], expected: int) -> int:
    match = re.search(r"Ran (\d+) tests", result.stdout + result.stderr)
    require(match is not None, "Python test count was not reported")
    observed = int(match.group(1))
    require(observed == expected, f"expected {expected} Python tests, got {observed}")
    return observed


def parse_node_tests(result: subprocess.CompletedProcess[str], expected: int) -> int:
    matches = re.findall(r"^# tests (\d+)$", result.stdout, flags=re.MULTILINE)
    require(matches, "Node test count was not reported")
    observed = int(matches[-1])
    require(observed == expected, f"expected {expected} Node tests, got {observed}")
    return observed


def run_test_suites() -> dict[str, int]:
    execute(
        "exact-algebra-self-test",
        python_command(PROOF / "exact_algebra.py", "--self-test"),
    )
    execute(
        "javascript-cleanroom-self-test",
        [NODE, PROOF / "cleanroom_checker.js", "--self-test"],
    )
    proof_tests = execute(
        "proof-python-tests",
        python_command(
            "-m",
            "unittest",
            "discover",
            "-s",
            PROOF / "tests",
            "-p",
            "test_*.py",
        ),
    )
    proof_test_count = parse_python_tests(proof_tests, 27)

    js_cleanroom_test = execute(
        "javascript-cleanroom-tests",
        [
            NODE,
            "--test",
            "--test-reporter=tap",
            PROOF / "tests" / "cleanroom.test.js",
        ],
    )
    require(
        "cleanroom.test.js PASS (6 checks)" in js_cleanroom_test.stdout,
        "JavaScript clean-room internal mutation count changed",
    )
    parse_node_tests(js_cleanroom_test, 1)

    verifier_a = execute(
        "verifier-a-tests",
        python_command(ROOT / "verifier_a" / "test_verifier.py"),
        cwd=ROOT / "verifier_a",
    )
    match = re.search(r"SUMMARY passed=(\d+) total=(\d+)", verifier_a.stdout)
    require(match is not None, "verifier A did not report a deterministic summary")
    require(match.groups() == ("10", "10"), "verifier A did not pass 10/10")

    verifier_b = execute(
        "verifier-b-tests",
        [
            NODE,
            "--test",
            "--test-reporter=tap",
            ROOT / "verifier_b" / "test" / "verifier-b.test.js",
        ],
        cwd=ROOT / "verifier_b",
    )
    verifier_b_count = parse_node_tests(verifier_b, 9)

    execute(
        "verifier-b-five-qubit-calibration",
        [
            NODE,
            ROOT / "verifier_b" / "src" / "cli.js",
            ROOT / "verifier_b" / "fixtures" / "5_1_3.pauli",
            "--max-weight",
            "5",
            "--expect-n",
            "5",
            "--expect-k",
            "1",
            "--expect-distance",
            "3",
        ],
        cwd=ROOT / "verifier_b",
    )
    execute(
        "verifier-b-fourteen-qubit-calibration",
        [
            NODE,
            ROOT / "verifier_b" / "src" / "cli.js",
            ROOT / "verifier_b" / "fixtures" / "14_3_4.pauli",
            "--max-weight",
            "5",
            "--expect-n",
            "14",
            "--expect-k",
            "3",
            "--expect-distance",
            "4",
        ],
        cwd=ROOT / "verifier_b",
    )
    return {
        "proof_python_tests": proof_test_count,
        "javascript_cleanroom_internal_checks": 6,
        "verifier_a_tests": 10,
        "verifier_b_tests": verifier_b_count,
        "primary_mutation_fixtures": 16,
        "cleanroom_python_mutation_fixtures": 5,
    }


def runtime_versions() -> dict[str, Any]:
    python_result = execute("python-version", [PYTHON, "--version"])
    node_result = execute("node-version", [NODE, "--version"])
    python_text = (python_result.stdout or python_result.stderr).strip()
    node_text = (node_result.stdout or node_result.stderr).strip()
    python_match = re.search(r"Python (\d+)\.(\d+)\.(\d+)", python_text)
    node_match = re.search(r"v(\d+)\.(\d+)\.(\d+)", node_text)
    require(python_match is not None, f"unparseable Python version: {python_text}")
    require(node_match is not None, f"unparseable Node version: {node_text}")
    require(
        tuple(map(int, python_match.groups()[:2])) >= (3, 11),
        "Python 3.11 or newer is required",
    )
    require(int(node_match.group(1)) >= 18, "Node.js 18 or newer is required")
    return {
        "schema": "quantum-14-3-5-proof-runtime-v1",
        "python": {
            "version": python_text,
            "executable": str(PYTHON),
            "sha256": sha256(PYTHON),
            "isolated": bool(sys.flags.isolated),
            "optimized": bool(sys.flags.optimize),
        },
        "node": {
            "version": node_text,
            "executable": str(NODE),
            "sha256": sha256(NODE),
        },
        "proof_dependencies": {
            "python": "standard library only",
            "javascript": "Node.js standard library only",
            "third_party": [],
            "package_manager_invocations": [],
        },
        "arithmetic": (
            "Python arbitrary-precision int and fractions.Fraction; "
            "JavaScript safe exact integers and proof-critical BigInt division; "
            "no tolerance-based or inexact decision"
        ),
    }


def critical_path_candidates() -> list[Path]:
    paths: set[Path] = {
        ROOT / "README.md",
        ROOT / "SPECIFICATION.md",
    }
    for path in PROOF.rglob("*"):
        if not path.is_file():
            continue
        relative = path.relative_to(PROOF)
        if relative.parts[0] == "generated":
            continue
        if "__pycache__" in relative.parts or path.suffix == ".pyc":
            continue
        paths.add(path)
    for directory in (ROOT / "verifier_a", ROOT / "verifier_b"):
        for path in directory.rglob("*"):
            if not path.is_file():
                continue
            relative = path.relative_to(directory)
            if (
                "__pycache__" in relative.parts
                or "node_modules" in relative.parts
                or path.suffix == ".pyc"
            ):
                continue
            paths.add(path)
    for name in GENERATED_ARTIFACTS:
        paths.add(GENERATED / name)
    return sorted(paths, key=lambda path: str(path.relative_to(ROOT)))


def check_generated_layout() -> None:
    allowed = set(GENERATED_ARTIFACTS) | {"SHA256SUMS"}
    unexpected = sorted(
        path.name
        for path in GENERATED.iterdir()
        if path.is_file() and path.name not in allowed
    )
    require(not unexpected, f"unexpected stale generated files: {unexpected}")


def write_and_verify_manifest() -> tuple[int, str]:
    paths = critical_path_candidates()
    missing = [str(path.relative_to(ROOT)) for path in paths if not path.is_file()]
    require(not missing, f"proof-critical file missing: {missing}")
    entries = [
        f"{sha256(path)}  {path.relative_to(ROOT)}"
        for path in paths
    ]
    manifest = GENERATED / "SHA256SUMS"
    manifest.write_text("\n".join(entries) + "\n", encoding="utf-8")
    for line in manifest.read_text(encoding="utf-8").splitlines():
        expected, relative = line.split("  ", 1)
        observed = sha256(ROOT / relative)
        require(
            observed == expected,
            f"manifest verification failed for {relative}",
        )
    return len(entries), sha256(manifest)


def clear_generated() -> None:
    """Remove every replay-owned artifact so no stale result can survive.

    A failed replay must not leave a previous successful run's PASS-labelled
    certificates, consensus, report, or manifest beside its FAIL report.
    Files not owned by the replay are left in place and are rejected later by
    check_generated_layout.
    """
    GENERATED.mkdir(parents=True, exist_ok=True)
    for name in (*GENERATED_ARTIFACTS, "SHA256SUMS", *DEPRECATED_GENERATED):
        path = GENERATED / name
        if path.is_file():
            path.unlink()


def main() -> int:
    global CHILD_ENV, NODE, TEMP_ROOT
    try:
        require(sys.flags.isolated, "invoke replay with Python -I")
        require(not sys.flags.optimize, "optimized Python is unsupported")
        require(
            Path.cwd().resolve() == ROOT,
            f"invoke replay from repository root {ROOT}",
        )
        node_name = shutil.which("node")
        require(node_name is not None, "Node.js executable was not found")
        NODE = Path(node_name).resolve()
        safe_path = os.pathsep.join(
            dict.fromkeys(
                [
                    str(PYTHON.parent),
                    str(NODE.parent),
                    "/usr/bin",
                    "/bin",
                ]
            )
        )
        CHILD_ENV = {
            "PATH": safe_path,
            "LANG": "C.UTF-8",
            "LC_ALL": "C.UTF-8",
            "TZ": "UTC",
            "PYTHONHASHSEED": "0",
            "NO_COLOR": "1",
            "NODE_DISABLE_COLORS": "1",
            "TERM": "dumb",
        }
        clear_generated()

        with tempfile.TemporaryDirectory(prefix="q1435-replay-") as directory:
            TEMP_ROOT = Path(directory)
            versions = runtime_versions()
            write_json(GENERATED / "versions.json", versions)

            claims = load_json(CLAIMS)
            primary = file_json_certificate(
                "primary",
                lambda output: python_command(
                    PROOF / "primary_checker.py",
                    "--claims",
                    CLAIMS,
                    "--output",
                    output,
                ),
                GENERATED / "certificate.json",
            )
            cleanroom = file_json_certificate(
                "python-cleanroom",
                lambda output: python_command(
                    PROOF / "cleanroom_checker.py",
                    "--claims",
                    CLAIMS,
                    "--output",
                    output,
                ),
                GENERATED / "cleanroom_certificate.json",
            )
            algebra = stdout_json_certificate(
                "exact-algebra",
                lambda: python_command(
                    PROOF / "exact_algebra.py",
                    "--json",
                ),
                GENERATED / "algebra_certificate.json",
            )
            finite = stdout_json_certificate(
                "finite-geometry",
                lambda: python_command(
                    PROOF / "finite_geometry.py",
                    "--json",
                ),
                GENERATED / "finite_geometry_certificate.json",
            )
            javascript = stdout_json_certificate(
                "javascript-cleanroom",
                lambda: [NODE, PROOF / "cleanroom_checker.js", "--json"],
                GENERATED / "js_cleanroom_certificate.json",
            )

            consensus = compare_certificates(
                claims, primary, cleanroom, algebra, finite, javascript
            )
            write_json(GENERATED / "consensus.json", consensus)
            LOG.append(
                f"[independent comparison] {len(consensus['comparisons'])} "
                "proof-critical exact agreements"
            )
            test_counts = run_test_suites()

            manifest_file_count = len(critical_path_candidates())
            report = {
                "schema": "quantum-14-3-5-proof-report-v1",
                "verdict": "PASS",
                "claim_status": "machine-verified proof artifact; see the accompanying paper",
                "scope": (
                    "binary additive qubit stabilizer codes [[14,3,d>=5]], "
                    "including degenerate codes"
                ),
                "proof_checks": {
                    "primary": len(primary["checks"]),
                    "python_cleanroom": len(cleanroom["checks"]),
                    "independent_exact_comparisons": len(
                        consensus["comparisons"]
                    ),
                    "certificates_byte_reproduced": 5,
                    "normal_forms": 4,
                    "weight_three_words_per_form": 9828,
                    "collision_lower_bound": 30,
                    "collision_upper_bounds": {
                        name: primary["facts"]["p03"]["collisions"][name][
                            "top24_edge_upper_bound"
                        ]
                        for name in ("independent", "p0", "p1", "p2")
                    },
                },
                "tests": test_counts,
                "runtime": versions,
                "manifest_files_excluding_manifest": manifest_file_count,
                "network_access": "not used",
            }
            write_json(GENERATED / "report.json", report)

            report_lines = [
                "Binary stabilizer [[14,3,5]] proof replay",
                "",
                f"Primary exact checks: {len(primary['checks'])} PASS",
                f"Python clean-room checks: {len(cleanroom['checks'])} PASS",
                (
                    "Independent exact comparisons: "
                    f"{len(consensus['comparisons'])} PASS"
                ),
                "Byte-identical certificate replays: 5/5 PASS",
                (
                    "Mutation fixtures: primary 16/16 and Python clean-room "
                    "5/5 rejected"
                ),
                "JavaScript clean-room mutations: PASS (6 internal checks)",
                "Verifier A: 10/10 PASS",
                "Verifier B: 9/9 PASS",
                "Calibration codes: [[5,1,3]] PASS; [[14,3,4]] PASS",
                "Normal forms: 4/4 generated and validated",
                "Weight-three Paulis per form: 9,828/9,828 enumerated",
                "Collision upper bounds: 12, 12, 13, 28; lower bound: 30",
                "Arithmetic: exact integer/rational decisions only",
                "Network access: not used",
                f"Manifest coverage: {manifest_file_count} files",
                "",
                "PROOF REPLAY PASS",
            ]
            (GENERATED / "REPORT.txt").write_text(
                "\n".join(report_lines) + "\n",
                encoding="utf-8",
            )
            LOG.append("[report] generated/report.json and REPORT.txt written")
            LOG.append(f"[manifest] coverage prepared for {manifest_file_count} files")
            LOG.append("[result] PROOF REPLAY PASS")
            (GENERATED / "replay.log").write_text(
                "\n".join(LOG) + "\n",
                encoding="utf-8",
            )
            check_generated_layout()
            manifest_count, manifest_digest = write_and_verify_manifest()
            require(
                manifest_count == manifest_file_count,
                "manifest path count changed during replay",
            )

        print("PROOF REPLAY PASS")
        print(
            f"primary_checks={len(primary['checks'])} "
            f"independent_comparisons={len(consensus['comparisons'])} "
            f"manifest_files={manifest_count}"
        )
        print(f"SHA256SUMS sha256={manifest_digest}")
        return 0
    except Exception as error:  # noqa: BLE001 — any failure must leave a FAIL report
        clear_generated()
        failure = f"FAIL proof replay: {error}"
        LOG.append(f"[result] {failure}")
        (GENERATED / "REPORT.txt").write_text(
            failure + "\n",
            encoding="utf-8",
        )
        (GENERATED / "replay.log").write_text(
            "\n".join(LOG) + "\n",
            encoding="utf-8",
        )
        print(failure, file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
