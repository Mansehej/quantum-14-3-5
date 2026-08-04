import Quantum1435.LocalKrawtchouk
import Quantum1435.EvenConclusion

/-!
# Completed all-even branch

The four local symplectic character sums are now proved, so the semantic
MacWilliams bridge and the checked integer certificate eliminate the
all-even branch without any remaining hypotheses.
-/

namespace Quantum1435

theorem fixedWeightCharacterSums_14_oneToFour :
    ∀ j : Fin 4, FixedWeightCharacterSum 14 (j.1 + 1) := by
  intro j
  fin_cases j
  · exact fixedWeightCharacterSum_14_1
  · exact fixedWeightCharacterSum_14_2
  · exact fixedWeightCharacterSum_14_3
  · exact fixedWeightCharacterSum_14_4

/-- No all-even 11-dimensional isotropic stabilizer on 14 qubits has
logical distance at least five. -/
theorem no_allEven_candidate
    (S : Submodule F₂ (Pauli 14))
    (hcandidate : IsCandidate1435 S)
    (heven : IsAllEven S) : False :=
  no_allEven_candidate_of_fixedWeightCharacterSums S hcandidate heven
    fixedWeightCharacterSums_14_oneToFour

/-- Consequently every putative candidate lies in the odd parity branch. -/
theorem candidate_containsOddWord
    (S : Submodule F₂ (Pauli 14))
    (hcandidate : IsCandidate1435 S) : ContainsOddWord S := by
  rcases parity_split S with heven | hodd
  · exact (no_allEven_candidate S hcandidate heven).elim
  · exact hodd

end Quantum1435
