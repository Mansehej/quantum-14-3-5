import Quantum1435.AllEvenComplete
import Quantum1435.OddSemantic

/-!
# Global profile reduction

The completed all-even elimination forces every candidate into the odd
branch.  The semantic MacWilliams and parity-kernel transforms then force
the three manuscript profiles for its actual weight distribution.
-/

namespace Quantum1435

/-- Every putative `[[14,3,≥5]]` stabilizer has one of the three low-weight
profiles `(A₂,A₄) = (0,1), (0,3), (1,1)`, with `A₁=A₃=0`. -/
theorem candidate_profile_trichotomy
    (S : Submodule F₂ (Pauli 14)) (hcandidate : IsCandidate1435 S) :
    weightDistribution S 1 = 0 ∧ weightDistribution S 3 = 0 ∧
      ((weightDistribution S 2 = 0 ∧ weightDistribution S 4 = 1) ∨
       (weightDistribution S 2 = 0 ∧ weightDistribution S 4 = 3) ∨
       (weightDistribution S 2 = 1 ∧ weightDistribution S 4 = 1)) :=
  oddCandidate_profile_trichotomy S hcandidate
    (candidate_containsOddWord S hcandidate)

end Quantum1435
