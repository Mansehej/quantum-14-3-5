import Mathlib
import I3322.SpectralSupport

namespace I3322

/-- Abstract interface for the pieces of the audited theorem that are not all
formalized in this archive. -/
structure ResolutionModel where
  Strategy : Type
  Chain : Type
  strategyValue : Strategy → ℝ
  chainValue : Chain → ℝ
  finiteDimensional : Strategy → Prop
  supportValue : Finset ℝ → ℝ
  beta : ℝ

/-- The precise finite-dimensional-to-finite-spectral-support bridge still
missing from the unconditional operator development.

The intended implementation sends a finite-dimensional projective strategy to
the union of the spectral supports of `X_A` and `Y_B`, and proves the scalar
variational upper bound for that support. -/
structure FiniteSpectrumBridge (M : ResolutionModel) where
  summarize : ∀ S, M.finiteDimensional S → FiniteSpectralSummary M.supportValue
  preservesValue :
    ∀ S hS, (summarize S hS).value = M.strategyValue S

/-- The precise measurable quantile/orbit bridge still missing from the
unconditional development.

The intended implementation supplies the Borel quantile matching, a measurable
transversal for the response orbits, normalized conditional orbit weights, and
a single normalizable Jacobi chain attaining the variational value. -/
structure MeasurableQuantileOrbitBridge (M : ResolutionModel) where
  maximizingChain : M.Chain
  maximizingChainValue : M.chainValue maximizingChain = M.beta

/-- Conditional finite-dimensional nonattainment from the explicitly named
spectral bridge and the kernel-level finite-support obstruction. -/
theorem conditional_finite_nonattainment
    (M : ResolutionModel)
    (hBridge : FiniteSpectrumBridge M)
    (hNoFinite : NoFiniteSupportOptimizer M.supportValue M.beta)
    (S : M.Strategy) (hS : M.finiteDimensional S) :
    M.strategyValue S < M.beta := by
  have hs := finite_summary_strictly_below hNoFinite (hBridge.summarize S hS)
  simpa [hBridge.preservesValue S hS] using hs

/-- The conditional orbit interface really does provide a chain at the target
value; this theorem is intentionally labelled conditional and is not exported
as a completed I3322 resolution. -/
theorem conditional_maximizing_chain
    (M : ResolutionModel)
    (hOrbit : MeasurableQuantileOrbitBridge M) :
    ∃ chain, M.chainValue chain = M.beta := by
  exact ⟨hOrbit.maximizingChain, hOrbit.maximizingChainValue⟩

end I3322
