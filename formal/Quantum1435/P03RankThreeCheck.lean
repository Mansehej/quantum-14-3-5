import Quantum1435.P03AnalyticBounds

/-!
# Opt-in kernel check for the p03 rank-three normal form

This resource-heavy theorem is intentionally isolated from the default
aggregate build.  It splits the outer coordinate into fourteen independent
ordinary kernel-reduction checks.
-/

namespace Quantum1435

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- The disjoint-support rank-three normal form has degree at most one. -/
theorem rankThree_sparse_degree_le_one :
    ∀ i j k : Fin 14, ∀ a b c : Fin 3,
      i < j ∧ j < k →
        sparseCollisionDegree rankThreeGenerators i j k a b c ≤ 1 := by
  intro i
  fin_cases i <;> decide +kernel

end Quantum1435
