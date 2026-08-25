# Axiom report

`I3322/AxiomCheck.lean` runs `#print axioms` on every exported theorem named in
`THEOREM_MAP.md`. The complete compiler output is captured in `BUILD_LOG.txt`.

## Project-level trust audit

The source scan rejects:

- `sorry`
- `admit`
- `unsafe`
- project declarations using `axiom`
- opaque proof placeholders
- `native_decide`
- `Lean.trustCompiler`
- `implemented_by`
- `extern`

No project theorem assumes the I3322 headline, an optimizing measure, an orbit
decomposition, or a spectral reduction as an unnamed proposition. The two
incomplete bridges are ordinary structures:

- `FiniteSpectrumBridge`
- `MeasurableQuantileOrbitBridge`

and no instance is constructed in the archive.

## Standard Lean/Mathlib axioms

Depending on theorem elaboration and imported library lemmas, `#print axioms`
may report the standard logical axioms used throughout Mathlib, commonly:

- `propext`: propositional extensionality;
- `Classical.choice`: choice used by classical finite-set and algebraic
  infrastructure;
- `Quot.sound`: quotient soundness used by standard quotient-based types.

Their occurrence does not introduce an I3322-specific mathematical premise.
The authoritative per-theorem list is the actual `#print axioms` output in the
captured clean build log, not this explanatory summary.

## Conditional theorem warning

`conditional_finite_nonattainment` and `conditional_maximizing_chain` are
kernel-proved implications, but their bridge arguments are not instantiated.
They must not be cited as a machine proof of unrestricted I3322 nonattainment
or spatial attainment.
