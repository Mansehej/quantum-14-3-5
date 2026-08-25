# Theorem map

## Convention and local polytope

- `I3322.pv_eq_cg_after_swaps`
  - Exact equality between the audited Pál--Vértesi/Connor ordering and the
    frozen Collins--Gisin ordering after swapping settings 1 and 2 for both
    parties.
- `I3322.deterministic_bits_local_bound`
  - Closed exhaustive kernel evaluation of the six Boolean variables.
- `I3322.deterministic_local_bound`
  - Response-function form of the exact local bound.
- `I3322.allZero_saturates`, `I3322.allOne_saturates`
  - Exact saturators.

## Finite Bell construction algebra

- `I3322.Mat2.reflection_mul_self`
- `I3322.Mat2.projector_mul_self`
- `I3322.scalar_observable_expansion`
- `I3322.exact_rational_witness_above_quarter`

These prove the exact finite block identities and the scalar Bell polynomial.
They do not construct the complete bi-infinite maximizing strategy.

## Effect replacement and dilation kernels

- `I3322.responseProjection_is_effect`
- `I3322.diagonal_objective_le_response`
- `I3322.halmosBlock_mul_self`
- `I3322.halmosBlock_compression`

The general noncommuting trace-class best-response theorem and simultaneous
Naimark dilation remain outside the theorem graph.

## Reflected-product positivity

- `I3322.reflectedQuadratic_sos_identity`
- `I3322.reflected_product_quadratic_nonnegative`
- `I3322.reflected_cross_term_bound`
- `I3322.reflected_interval_to_determinant`
- `I3322.goldenUpper_lt_one_third`

This is the exact real two-point SOS kernel. It is not silently identified with
the general spectral-functional-calculus theorem.

## Finite Hellinger and rearrangement kernels

- `I3322.atomic_pair_lower_bound`
- `I3322.atomic_pair_contact_value`
- `I3322.atomic_pair_reflection`
- `I3322.two_point_countermonotone`

General probability measures, Radon--Nikodym derivatives, quantile functions,
weak topology, and Sion minimax are not formalized here.

## Rigidity kernels

- `I3322.extensionMargin_positive`
- `I3322.extensionMargin_at_one_third`
- `I3322.stationarity_propagates_previous_label`
- `I3322.jacobi_reverse_step`
- `I3322.finite_geometric_chain_zero`

These are the exact algebraic recurrence steps used after the analytic chain
has been extracted. The extraction itself is not kernel-proved.

## Finite support and dimension reduction

- `I3322.spectral_union_card_le_sum`
- `I3322.finite_summary_strictly_below`
- `I3322.finite_summary_support_card_bound`

The operator theorem producing a `FiniteSpectralSummary` from an arbitrary
finite-dimensional I3322 strategy is represented only by the uninstantiated
structure `I3322.FiniteSpectrumBridge`.

## Conditional interfaces

- `I3322.conditional_finite_nonattainment`
  - Requires an explicit `FiniteSpectrumBridge` and strict obstruction for the
    actual finite-support functional.
- `I3322.conditional_maximizing_chain`
  - Requires an explicit `MeasurableQuantileOrbitBridge`.

Neither theorem is an unconditional I3322 headline theorem.

## Negative controls

- `I3322.missingAliceMarginal_breaks_local_bound`
- `I3322.Mat2.wrong_sign_not_reflection`
- `I3322.zero_offDiagonal_halmos_not_projector`
- `I3322.missing_reflected_product_counterexample`
- `I3322.same_order_pairing_strict_counterexample`
- `I3322.incomplete_reflection_counterexample`
- `I3322.dropping_boundary_allows_nonzero_geometric_chain`
- `I3322.max_instead_of_sum_counterexample`
- `I3322.negative_control_bundle`

Every theorem above appears in `I3322/AxiomCheck.lean`.
