# I3322 audited Lean core

This is a Lean 4 + Mathlib formalization of the largest clean, assumption-free
kernel that could be completed for the audited I3322 argument without hiding
the measure-theoretic and operator-algebraic bridges.

## Exact environment

- Lean: `leanprover/lean4:v4.32.1`
- Mathlib commit: `520045ab14e26149ee970e2e617ca04b09bde5d6`

The archive includes `lake-manifest.json`, a clean build transcript, and a
SHA-256 manifest.

## What the kernel proves

The compiled modules prove:

- the frozen Collins--Gisin deterministic convention;
- exact conversion from the Pál--Vértesi/Connor setting order by swapping the
  first two settings on both parties, with no affine shift or rescaling;
- the local deterministic bound `0`, by closed kernel evaluation of all 64
  assignments, and explicit saturating assignments;
- exact two-by-two reflection and projector identities;
- the exact scalar polynomial expansion of `4 + 4 I3322` in observable
  variables;
- the exact rational witness inequality above `1/4`;
- a finite diagonal effect-to-positive-spectral-projection best-response
  theorem;
- the exact scalar Halmos dilation idempotence identity;
- the reflected-product two-by-two sum-of-squares certificate and its
  cross-term consequence;
- the scalar interval-to-determinant implication and the elementary strict
  upper threshold below `1/3`;
- finite atomic Hellinger, reflection, and two-point countermonotone
  rearrangement identities;
- the endpoint-extension margin and finite geometric-chain rigidity kernels;
- finite spectral-support union cardinality and the abstract strict-support
  reduction;
- six mutation controls covering convention, local bound, reflection,
  reflected-product positivity, rigidity, and dimension-to-support counting.

## What the kernel does **not** prove

This project does **not** claim a complete formalization of the August 2026
I3322 resolution. In particular, it does not kernel-prove:

1. the general noncommutative functional-calculus lift from the two-by-two
   reflected block to arbitrary bounded operators `g(X)`;
2. the full effect-to-projection theorem for arbitrary finite-dimensional
   noncommuting effects and trace objectives;
3. reflected Hellinger duality for arbitrary Borel probability measures;
4. Sion minimax and the full quantile/countermonotone coupling theorem in the
   exact form used by the preprint;
5. existence of a maximizing probability measure for the complete variational
   functional;
6. the measurable quantile matcher, deletion of exceptional fibers, Borel
   orbit transversal, conditional disintegration, normalized orbit weights,
   and extraction of one normalizable maximizing Jacobi chain;
7. the operator spectral-measure construction mapping every finite-dimensional
   strategy to a finite scalar support while preserving the needed bound;
8. the unconditional exact variational characterization or unrestricted
   finite-dimensional nonattainment theorem.

`I3322.ConditionalBridge` contains ordinary structures naming these missing
bridges and proves only what follows after an explicit instance is supplied.
They are not axioms, are not instantiated, and are not imported as facts about
I3322.

## Reproducibility item from the audit

The preprint names `i3322_witness100_verify.py` and
`i3322_piecewise_dual_verify.py`, but those supplementary files were not
publicly discoverable during the audit. They are non-load-bearing for the
analytic theorem. This archive resolves the formalization-side ambiguity by
not trusting or importing them: the rational witness comparison, the `1/3`
threshold, and every algebraic certificate present here are recomputed by Lean.
The absent scripts remain a provenance/reproducibility issue for the preprint's
numerical orientation material, not an input to this project.

## Build

```bash
lake update
lake exe cache get
lake build
lake env lean I3322/AxiomCheck.lean
```

The release build used `lake clean` before `lake build`; see `BUILD_LOG.txt`.

## Trust boundary

There are no `sorry`, `admit`, `unsafe`, custom `axiom`, opaque proof
placeholders, `native_decide`, compiler-trust hooks, or external certificates
accepted as proof. `#print axioms` is run for every exported theorem listed in
`I3322/AxiomCheck.lean`.
