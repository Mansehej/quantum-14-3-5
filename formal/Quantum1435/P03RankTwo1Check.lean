import Quantum1435.P03RankTwo0Check

/-!
# Opt-in kernel check for the p03 rank-two p1 normal form

This resource-heavy theorem is intentionally isolated from the default
aggregate build.  It uses ordinary kernel reduction only.
-/

namespace Quantum1435

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- In the p1 normal form, the only word with degree above one is the all-X
word supported on coordinates `0,1,2`. -/
theorem rankTwo1_sparse_high_iff :
    ∀ i j k : Fin 14, ∀ a b c : Fin 3,
      i < j ∧ j < k →
        (1 < sparseCollisionDegree rankTwo1Generators i j k a b c ↔
          i = 0 ∧ j = 1 ∧ k = 2 ∧ a = 0 ∧ b = 0 ∧ c = 0) := by
  intro i
  fin_cases i <;> decide +kernel

end Quantum1435
