import I3322.Convention
import I3322.BellAlgebra
import I3322.EffectReduction
import I3322.OperatorCore
import I3322.AtomicHellinger
import I3322.Rigidity
import I3322.SpectralSupport

namespace I3322

/-- Mutation control for reflected Hellinger pairing: swapping the masses but
not the dual values is not a symmetry. -/
theorem incomplete_reflection_counterexample :
    atomicPairCost 1 2 3 4 ≠ atomicPairCost 2 1 3 4 := by
  norm_num [atomicPairCost]

/-- All required corruption tests collected in one kernel-checked statement. -/
theorem negative_control_bundle :
    i3322MissingAliceMarginal allOne allOne = 1
    ∧ Mat2.mul (Mat2.wrongSignReflection 0 1) (Mat2.wrongSignReflection 0 1)
        ≠ Mat2.one
    ∧ reflectedQuadratic (3 / 2) (3 / 2) 1 1 (-1) = -1
    ∧ atomicPairCost 1 2 3 4 ≠ atomicPairCost 2 1 3 4
    ∧ (∃ v : ℕ → ℝ, (∀ n, v (n + 1) = 2 * v n) ∧ v 0 = 1)
    ∧ (({0} : Finset ℕ) ∪ ({1} : Finset ℕ)).card > max 1 1 := by
  exact ⟨missingAliceMarginal_breaks_local_bound,
    Mat2.wrong_sign_not_reflection,
    missing_reflected_product_counterexample,
    incomplete_reflection_counterexample,
    dropping_boundary_allows_nonzero_geometric_chain,
    max_instead_of_sum_counterexample⟩

end I3322
