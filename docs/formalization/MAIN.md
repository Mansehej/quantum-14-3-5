# Lean formalization

## Result

The Lean project under [`formal/`](../../formal/) proves the nonexistence of
a binary stabilizer code with parameters `[[14,3,5]]`.

[`Final.lean`](../../formal/Quantum1435/Final.lean) contains two final forms:

- `noBinaryStabilizer1435 : NoBinaryStabilizer1435` excludes every
  11-dimensional totally isotropic subspace whose logical distance is at
  least five.
- `noBinaryStabilizerExact1435` excludes the exact-minimum formulation with
  `LogicalDistanceIs S 5`.

The phase-free Pauli space is modeled as `(ZMod 2 × ZMod 2)^14`. Logical
operators are the vectors in the symplectic normalizer `Sᵖ` but not in `S`,
and distance is their minimum Pauli weight. Low-weight vectors inside `S`
are allowed throughout, so the theorem includes degenerate codes.

No JSON file, hash, Python/JavaScript result, or recorded `PASS` value is an
input to either theorem.

This is an alternative formal proof of the theorem in the binary symplectic
model, not a line-by-line formalization of every manuscript computation. The
artifact formalizes phase-free Pauli vectors and isotropic stabilizer
subspaces directly; the standard Hilbert-space/Pauli-group correspondence is
the modeling boundary rather than an additional theorem proved here.

## Mathematical model

- [`Basic.lean`](../../formal/Quantum1435/Basic.lean) defines Pauli vectors,
  Pauli weight, the symplectic form, total isotropy, `Sᵖ`, logical operators,
  and exact/lower-bound logical distance.
- [`Normalizer.lean`](../../formal/Quantum1435/Normalizer.lean) proves the
  form nondegenerate and computes normalizer dimension.
- [`LogicalQuotient.lean`](../../formal/Quantum1435/LogicalQuotient.lean)
  constructs `Sᵖ/S`, proves it is six-dimensional at the target parameters,
  and proves its induced symplectic form nondegenerate.
- [`Statement.lean`](../../formal/Quantum1435/Statement.lean) states the
  dimension-11, isotropic, distance-at-least-five candidate predicate and
  the nonexistence proposition.

## Proof architecture

1. **Parity and the all-even branch.**
   [`Parity.lean`](../../formal/Quantum1435/Parity.lean) proves the quadratic
   refinement identity and the exhaustive parity split.
   [`WeightEnumerator.lean`](../../formal/Quantum1435/WeightEnumerator.lean),
   [`CharacterOrthogonality.lean`](../../formal/Quantum1435/CharacterOrthogonality.lean),
   [`MacWilliamsBridge.lean`](../../formal/Quantum1435/MacWilliamsBridge.lean),
   and [`LocalKrawtchouk.lean`](../../formal/Quantum1435/LocalKrawtchouk.lean)
   derive the semantic MacWilliams identities for actual submodules.
   [`AllEvenComplete.lean`](../../formal/Quantum1435/AllEvenComplete.lean)
   eliminates the all-even case with the checked identity
   `16 A₂ + 9 A₄ + 2 A₆ = 7`.

2. **Odd enumerators and profile trichotomy.**
   [`OddSemantic.lean`](../../formal/Quantum1435/OddSemantic.lean) constructs
   the dimension-10 parity kernel of an odd stabilizer, derives its source
   rows, and connects the proved Identity-51 certificate to actual word
   counts. [`ProfileReduction.lean`](../../formal/Quantum1435/ProfileReduction.lean)
   proves that the only profiles are
   `(A₂,A₄) = (0,1), (0,3), (1,1)`.

3. **Literal shadow and the universal rows.**
   [`ShadowCoset.lean`](../../formal/Quantum1435/ShadowCoset.lean) defines the
   literal shadow `C₀ᵖ \\ Sᵖ` and proves its coset, pairing, translation, and
   dimension properties. [`ShadowEnumeratorBridge.lean`](../../formal/Quantum1435/ShadowEnumeratorBridge.lean)
   proves the coefficient partition `E_j = B_j + S_j`, specializing to
   `E_j = A_j + S_j` only below logical distance.

   [`OddSignedShadow2.lean`](../../formal/Quantum1435/OddSignedShadow2.lean),
   [`OddSignedShadow3.lean`](../../formal/Quantum1435/OddSignedShadow3.lean),
   and [`OddSignedShadow4.lean`](../../formal/Quantum1435/OddSignedShadow4.lean)
   derive the signed-shadow rows directly by subtracting the ordinary
   stabilizer MacWilliams row from the parity-kernel MacWilliams row.
   [`OddUniversalA14Certificate.lean`](../../formal/Quantum1435/OddUniversalA14Certificate.lean)
   and [`OddUniversalS3Certificate.lean`](../../formal/Quantum1435/OddUniversalS3Certificate.lean)
   prove the two universal formulas as pure-integer linear combinations.
   [`OddUniversalSemantic.lean`](../../formal/Quantum1435/OddUniversalSemantic.lean)
   instantiates those certificates with actual stabilizer and shadow counts.

   This direct derivation replaces the manuscript's self-dual-extension,
   Lagrangian-incidence, and quadratic/Witt averaging route. Those finite
   classifications are therefore not assumptions and are not needed by the
   final theorem.

4. **Profile p11.**
   [`P11Geometry.lean`](../../formal/Quantum1435/P11Geometry.lean) proves the
   required overlap implication for actual stabilizer words, and
   [`P11SemanticElimination.lean`](../../formal/Quantum1435/P11SemanticElimination.lean)
   combines it with Identity 51 and the first universal row to obtain a
   contradiction.

5. **Profile p03.**
   The `P03*` modules construct the actual set of 24 weight-three shadow
   vectors, prove a 42-bin incidence lower bound of 60 ordered shared-bin
   pairs, classify the three actual weight-four stabilizer translations,
   and prove representative-free collision upper bounds 24, 26, 56, and 24
   for the four invariant geometries. The lower and upper bounds contradict
   in every case. [`P03SemanticElimination.lean`](../../formal/Quantum1435/P03SemanticElimination.lean)
   exports the unconditional theorem `p03_candidate_false`.

   The four `P03*Check` modules and
   [`P03ThresholdBounds.lean`](../../formal/Quantum1435/P03ThresholdBounds.lean)
   provide an independent exact-coordinate cross-check. They are intentionally
   excluded from the default target and are not dependencies of `Final`.

6. **Profile p01.**
   [`P01ShadowLowWeights.lean`](../../formal/Quantum1435/P01ShadowLowWeights.lean)
   handles the low shadow coefficients.
   [`P01InvariantPairs.lean`](../../formal/Quantum1435/P01InvariantPairs.lean)
   proves, by an invariant argument, that at most two ordered weight-three
   shadow pairs share a bin.
   [`P01IncidenceBounds.lean`](../../formal/Quantum1435/P01IncidenceBounds.lean)
   proves the 42-bin bound `S₃ ≤ 14`, and
   [`P01ReducedBins.lean`](../../formal/Quantum1435/P01ReducedBins.lean)
   proves the reduced 36-bin bound `S₃ ≤ 12` when `S₂ = 1`: logical distance,
   the vanishing low stabilizer coefficients, uniqueness of the weight-four
   stabilizer word, and the parity-kernel pairing theorem first force the sum
   of the weight-two and any weight-three shadow word to have weight five,
   and the coordinate-category identities then force disjoint support.
   [`P01SemanticElimination.lean`](../../formal/Quantum1435/P01SemanticElimination.lean)
   feeds these actual bounds into the checked Presburger contradiction.

7. **Composition.**
   [`Final.lean`](../../formal/Quantum1435/Final.lean) eliminates the all-even
   branch, applies the odd profile trichotomy, eliminates p01/p03/p11, and
   proves both final nonexistence formulations.

## Computation and certificate boundary

Identities and candidate certificates come from untrusted search. The
development proves soundness of the generic integer certificate checker and
checks every concrete identity in the kernel. The large universal-row
certificates are isolated as pure-`Int` theorems so elaboration remains
memory-bounded.

The opt-in p03 normal-form checks use `decide +kernel`; they produce ordinary
proof terms checked by the Lean kernel. The default final proof instead uses
the representative-free invariant bounds. The project uses neither
`native_decide` nor the compiled evaluator as a trusted oracle.

[`P03CollisionChecker.lean`](../../formal/Quantum1435/P03CollisionChecker.lean)
records proposed exact degree-histogram and certificate values, but asserts no
theorem accepting those tables. Their validity is deliberately non-load-bearing:
the invariant bounds are sufficient for the final contradiction.

## Toolchain, verification, and trusted base

[`lean-toolchain`](../../formal/lean-toolchain) pins Lean to `v4.32.2`, and
[`lakefile.toml`](../../formal/lakefile.toml) pins mathlib to `v4.32.2`.
Resolved dependency revisions are recorded in
[`lake-manifest.json`](../../formal/lake-manifest.json).

For a fresh clone, obtain mathlib's precompiled cache before building; Lake
materializes the pinned dependencies recorded in `lake-manifest.json` on
demand. Do not run `lake update`, which would rewrite those pins.

```bash
cd formal
lake exe cache get
lake build
lake env lean Quantum1435/Axioms.lean
rg -n 'sorry|admit|axiom |native_decide|Lean\.trustCompiler' \
  Quantum1435 Quantum1435.lean -g '*.lean'
```

The development is split into many small modules, in particular the
linear-combination certificates, so that no single module's elaboration is
memory-heavy; a full build of the project's modules takes a few minutes on
commodity hardware.

The independent exact-coordinate p03 route is opt-in:

```bash
lake build +Quantum1435.P03ThresholdBounds
lake env lean Quantum1435/P03OptionalAxioms.lean
```

The logical trust boundary is the Lean kernel implementation together with
the three standard principles reported for the final theorems: `propext`,
`Classical.choice`, and `Quot.sound`. Mathlib declarations, the elaborator,
and tactics such as `omega` and `linear_combination` produce proof terms that
the kernel checks; they are not separate proof oracles. Operational
reproduction additionally trusts the pinned Lean executable to implement its
kernel correctly.

The audit in [`Axioms.lean`](../../formal/Quantum1435/Axioms.lean) covers the
load-bearing final route. [`P03OptionalAxioms.lean`](../../formal/Quantum1435/P03OptionalAxioms.lean)
separately audits the opt-in cross-check. There are no placeholder proofs or
custom computational assumptions. Every audited theorem, including both final
formulations, reports only `propext`, `Classical.choice`, and `Quot.sound`.
The workflow in [`.github/workflows/lean.yml`](../../.github/workflows/lean.yml)
repeats the forbidden-token scan, both builds, and both audits on every push.
