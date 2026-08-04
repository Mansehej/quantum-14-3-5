import Quantum1435.P03RankTwo1Check

/-!
# Opt-in kernel check for the p03 rank-two p2 normal form

This resource-heavy theorem is intentionally isolated from the default
aggregate build.  It uses ordinary kernel reduction only.
-/

namespace Quantum1435

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- In the p2 normal form, degree three forces one all-X coordinate from
each of the pairs `{0,1}`, `{2,3}`, and `{4,5}`. -/
theorem rankTwo2_sparse_high_iff :
    ∀ i j k : Fin 14, ∀ a b c : Fin 3,
      i < j ∧ j < k →
        (2 < sparseCollisionDegree rankTwo2Generators i j k a b c ↔
          (i = 0 ∨ i = 1) ∧ (j = 2 ∨ j = 3) ∧ (k = 4 ∨ k = 5) ∧
            a = 0 ∧ b = 0 ∧ c = 0) := by
  intro i
  fin_cases i <;> decide +kernel

end Quantum1435
