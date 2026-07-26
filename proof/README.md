# Reproducible nonexistence proof

This package is the machine-verified proof artifact accompanying the paper
in [`../paper/`](../paper/): five independent exact implementations, a
one-command offline replay, and mutation-tested certificates.

## Exact scope

The checked statement is:

> There is no 11-dimensional isotropic binary subspace
> \(C\subseteq\mathbb F_2^{28}\) for which
> \(\min\{\operatorname{wt}(v):v\in C^{\perp_s}\setminus C\}\ge5\).

Consequently, subject to the named algebraic lemmas in
[`LEMMAS.md`](LEMMAS.md), there is no binary additive qubit stabilizer code
with exact parameters `[[14,3,5]]`.

This scope includes degenerate stabilizer codes and does not assume purity,
CSS form, GF(4)-linearity, symmetry, or a restricted ansatz.  It does not
cover nonadditive, subsystem, entanglement-assisted, qudit, or approximate
codes.  Pauli phases are discarded exactly as frozen in
[`../SPECIFICATION.md`](../SPECIFICATION.md).

## One-command replay

From the repository root:

```bash
python3 -I proof/replay.py
```

The command needs no network access, installation step, session transcript,
cached agent state, solver, or floating-point tolerance.  It overwrites only
the reproducible files under `proof/generated/`.

## What the replay derives

The primary checker regenerates, from exact coefficient matrices and finite
enumeration:

1. the contradiction in the all-even branch;
2. the odd-code coefficient identity with constant 51 and the three possible
   low profiles `(0,1)`, `(0,3)`, `(1,1)`;
3. all 1,395 three-subspaces of \(\mathbb F_2^6\), the 135 Lagrangians,
   15-fold point incidence, and the average-extension formula;
4. the corrected eight-dimensional extension-shadow incidence calculation:
   135 extensions, 72 eligible even classes, and incidence 30, giving
   \(\overline T_j=2S_j/9\) for even global-shadow coefficients;
5. the self-dual extension basis and two anti-MacWilliams identities;
6. the `(1,1)` and `(0,1)` eliminations, including `S1 <= 1`, the exhaustive
   90-pair p01 compatibility calculation, the 42-bin bound, and the
   unique-weight-two 36-bin restriction;
7. the forced `(0,3)` enumerators;
8. exhaustiveness of one rank-three and three rank-two
   local-Clifford/permutation normal forms;
9. all \(\binom{14}{3}3^3=9,828\) weight-three Paulis for every form and the
   collision upper bounds `12, 12, 13, 28`, all below the required lower
   bound 30.

The JSON claim file is only a mutation target and comparison contract.  Both
checkers regenerate its values; changing a coefficient, omitting a normal
form, or altering a collision table causes failure.

## Independent implementations

- `primary_checker.py` uses packed symplectic integers, exact affine
  expressions, direct subspace generation, and an \(O^+(8,2)\) incidence
  enumeration.
- `cleanroom_checker.py` imports none of the primary implementation.  It uses
  literal Pauli tuples, explicit phase-free multiplication, independently
  generated RREF bases, and separately written polynomial elimination.
- `exact_algebra.py` is a separate `Fraction`-based polynomial,
  substitution, and branch-elimination certificate.
- `finite_geometry.py` independently regenerates quotient incidence,
  fixed-first normal-form signatures, and the p01/p03 collision calculations
  with tuple-valued Paulis.
- `cleanroom_checker.js` is a separately authored Node.js implementation of
  the orbit and collision enumerators.  It exhausts the 81,081 fixed-first
  candidates and all 9,828 weight-three words.
- The four Python test modules run 27 tests, including sixteen primary
  mutation fixtures — one for every claims region a required check compares —
  five clean-room mutations, and direct in-memory mutation tests of the
  replay consensus comparison and generated-artifact hygiene.  The Node.js
  test adds independent omitted-form and altered-table mutations.  The tests
  also verify that deleting either fragile p01 bin rule leaves a surviving
  algebraic branch.
- The pre-existing `verifier_a` and `verifier_b` calibration suites are run
  from fresh processes and continue to reproduce the standard `[[5,1,3]]`
  and published `[[14,3,4]]` examples, including corruptions.

## Layout

```text
proof/
├── README.md
├── LEMMAS.md
├── REQUIREMENTS.md
├── claims/theorem.json
├── primary_checker.py
├── cleanroom_checker.py
├── exact_algebra.py
├── finite_geometry.py
├── cleanroom_checker.js
├── replay.py
├── tests/
│   ├── test_proof.py
│   ├── test_mutations.py
│   ├── test_finite_geometry.py
│   ├── test_replay_compare.py
│   ├── cleanroom.test.js
│   └── fixtures/*.json
└── generated/
    ├── certificate.json
    ├── cleanroom_certificate.json
    ├── algebra_certificate.json
    ├── finite_geometry_certificate.json
    ├── js_cleanroom_certificate.json
    ├── consensus.json
    ├── versions.json
    ├── report.json
    ├── REPORT.txt
    ├── replay.log
    └── SHA256SUMS
```

Result-producing checkers never read `generated/`; the replay compares
freshly regenerated certificates before writing them there.  Generated files
are outputs, not trusted inputs.  `SHA256SUMS` covers every proof source,
fixture, frozen specification, critical calibration-verifier file, and
generated artifact except the manifest itself.

## Trust boundary

This is executable mathematics, not a formal proof-assistant development.
The small conceptual bridge is isolated and proved in `LEMMAS.md` and in
the accompanying paper: MacWilliams character counting, the Pauli-weight
quadratic refinement, the all-even MacWilliams elimination, the odd-code
shadow coset, self-dual extensions as Lagrangians, the induced plus-type
quadratic quotient, and local-Clifford invariance.  Every target-specific
coefficient, branch, incidence count, orbit, word, and collision
consequence is machine checked with exact arithmetic by independent
implementations.
