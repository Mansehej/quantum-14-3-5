import Quantum1435.P03RankThreeCheck

/-!
# Opt-in kernel check for the p03 rank-two p0 normal form

This resource-heavy theorem is intentionally isolated from the default
aggregate build.  It uses ordinary kernel reduction only.
-/

namespace Quantum1435

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- The common-support, three-label rank-two normal form has degree at most
one. -/
theorem rankTwo0_sparse_degree_le_one :
    ∀ i j k : Fin 14, ∀ a b c : Fin 3,
      i < j ∧ j < k →
        sparseCollisionDegree rankTwo0Generators i j k a b c ≤ 1 := by
  intro i
  fin_cases i <;> decide +kernel

end Quantum1435
