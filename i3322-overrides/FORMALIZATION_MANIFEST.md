# Formalization manifest

Status vocabulary:

- **KERNEL**: theorem is proved in Lean without project axioms or placeholders.
- **PARTIAL KERNEL**: a genuine load-bearing algebraic or finite special case is
  proved, but the general analytic/operator statement is not.
- **CONDITIONAL**: Lean theorem requires an explicitly named bridge structure;
  no instance is supplied.
- **UNFORMALIZED**: no theorem in this archive proves the claim.

| Program item | Status | Lean location | Exact scope |
|---|---|---|---|
| A. Frozen probability convention | KERNEL | `Convention.lean` | Exact CG deterministic polynomial and PV/Connor setting swap |
| A. Local bound | KERNEL | `deterministic_bits_local_bound`, `deterministic_local_bound` | All 64 deterministic assignments; exact bound and saturators |
| B. Reflection/projector construction | KERNEL | `BellAlgebra.lean` | Transparent real `2 x 2` blocks |
| B. Bell observable expansion | PARTIAL KERNEL | `scalar_observable_expansion` | Exact commuting scalar polynomial; not the general noncommutative operator rewrite |
| B. Exact witness inequality | KERNEL | `exact_rational_witness_above_quarter` | Rational comparison only; no claim that this witness is globally optimal |
| C. Effect-to-projection reduction | PARTIAL KERNEL | `diagonal_objective_le_response` | Arbitrary finite diagonal objectives; general noncommuting trace theorem unformalized |
| C. Halmos dilation | PARTIAL KERNEL | `halmosBlock_mul_self`, `halmosBlock_compression` | Exact scalar `2 x 2` algebra; simultaneous operator dilation unformalized |
| D. Reflected-product positivity | KERNEL | `reflectedQuadratic_sos_identity`, `reflected_product_quadratic_nonnegative` | Exact real `2 x 2` SOS certificate |
| D. Functional-calculus operator lift | UNFORMALIZED | — | Arbitrary bounded operators and Borel functional calculus |
| D. Scalar interval/product implication | KERNEL | `reflected_interval_to_determinant`, `goldenUpper_lt_one_third` | Exact real algebra |
| E. Hellinger duality | PARTIAL KERNEL | `atomic_pair_lower_bound`, `atomic_pair_contact_value` | Finite one-pair square-root-coordinate kernel |
| E. Reflection | KERNEL | `atomic_pair_reflection` | Exact atomic reflection identity |
| E. Countermonotone rearrangement | PARTIAL KERNEL | `two_point_countermonotone` | Exact two-point swap inequality |
| E. General measures, quantiles, Sion minimax | UNFORMALIZED | — | No general Borel measure theorem exported |
| E. Optimizing-measure compactness | UNFORMALIZED | — | No upper-semicontinuity/compactness theorem exported |
| F. Support cardinality | KERNEL | `spectral_union_card_le_sum` | Finite-set cardinal arithmetic |
| F. Strict finite-support logical reduction | KERNEL | `finite_summary_strictly_below` | Applies after a valid finite spectral summary is supplied |
| F. Strategy-to-spectral-support operator map | CONDITIONAL | `FiniteSpectrumBridge`, `conditional_finite_nonattainment` | Missing bridge is explicit and uninstantiated |
| G. Endpoint extension margin | KERNEL | `extensionMargin_positive` | Exact worst-case scalar margin for `E < 1/3` |
| G. Stationarity/Jacobi rigidity kernels | KERNEL | `stationarity_propagates_previous_label`, `jacobi_reverse_step`, `finite_geometric_chain_zero` | Algebraic recurrence kernels only |
| G. Measurable quantile matching and orbit disintegration | CONDITIONAL / UNFORMALIZED | `MeasurableQuantileOrbitBridge` | Interface only; no instance |
| H. Exact unrestricted variational characterization | UNFORMALIZED | — | Not exported |
| H. No finite-dimensional I3322 maximizer | CONDITIONAL ONLY | `conditional_finite_nonattainment` | Requires `FiniteSpectrumBridge` and a finite-support strict theorem for the actual functional |
| H. Infinite-dimensional attaining strategy | CONDITIONAL ONLY | `conditional_maximizing_chain` | Requires `MeasurableQuantileOrbitBridge` |
| Full claimed I3322 resolution | **NOT FORMALIZED** | — | No theorem in the archive states it unconditionally |

## Mutation controls

| Mutation | Kernel counterexample |
|---|---|
| Missing Alice marginal | `missingAliceMarginal_breaks_local_bound` |
| Wrong reflection sign | `Mat2.wrong_sign_not_reflection` |
| Missing Halmos off-diagonal | `zero_offDiagonal_halmos_not_projector` |
| Missing reflected-product determinant | `missing_reflected_product_counterexample` |
| Incomplete reflected swap | `incomplete_reflection_counterexample` |
| Dropped chain boundary | `dropping_boundary_allows_nonzero_geometric_chain` |
| `max(dA,dB)` substituted for `dA+dB` | `max_instead_of_sum_counterexample` |
| Aggregate control | `negative_control_bundle` |

## Source provenance

The project is a clean-room Lean encoding of the audited proof kernels. It does
not import executable results, floating-point output, the Apsiape shooting
profile, or the decertified amplitude-compatibility equation.
