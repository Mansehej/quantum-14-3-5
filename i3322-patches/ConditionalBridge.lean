import I3322.Rigidity
import I3322.SpectralSupport

namespace I3322

/-- Data carried by one normalized Jacobi-chain component. -/
structure NormalizedChain where
  value : ℝ
  normalized : Prop
  finiteSupport : Prop

/--
The exact remaining bridge not proved in this archive.

It packages the measurable quantile matching, Borel orbit decomposition,
normalization of orbit weights, the diagonal-and-edge barycenter identity,
and extraction of one maximizing chain.  This is a structure parameter, not a
logical axiom and not a claim that these fields have been constructed in Lean.
-/
structure MeasurableQuantileOrbitBridge (beta : ℝ) where
  chain : NormalizedChain
  chain_normalized : chain.normalized
  chain_value : chain.value = beta
  finite_components_strict : ∀ C : NormalizedChain,
    C.normalized → C.finiteSupport → C.value < beta

/-- The measurable bridge plus finite-component rigidity forces an infinite maximizing chain. -/
theorem conditional_infinite_maximizing_chain {beta : ℝ}
    (B : MeasurableQuantileOrbitBridge beta) :
    B.chain.normalized ∧ B.chain.value = beta ∧ ¬ B.chain.finiteSupport := by
  refine ⟨B.chain_normalized, B.chain_value, ?_⟩
  intro hfinite
  have hlt := B.finite_components_strict B.chain B.chain_normalized hfinite
  rw [B.chain_value] at hlt
  exact (lt_irrefl beta) hlt

/--
A separately named conditional wrapper for the finite-dimensional conclusion.
Its two hypotheses are the precise unformalized analytic bridges: measurable
chain extraction and the operator-to-scalar spectral reduction for an actual
Bell strategy.  The support-counting implication itself is kernel-proved in
`SpectralSupport.lean`.
-/
theorem conditional_no_finite_dimensional_attainer
    {Strategy : Type*} {beta : ℝ}
    (value : Strategy → ℝ) (finiteDimensional : Strategy → Prop)
    (spectralReduction : ∀ S : Strategy,
      finiteDimensional S → value S < beta) :
    ¬ ∃ S : Strategy, finiteDimensional S ∧ value S = beta := by
  rintro ⟨S, hfin, hval⟩
  have hlt := spectralReduction S hfin
  rw [hval] at hlt
  exact (lt_irrefl beta) hlt

end I3322
