import Quantum1435.MacWilliamsBridge
import Quantum1435.EvenSemantic

/-!
# End-to-end all-even reduction

This module joins the proved character-orthogonality/double-counting bridge
to the semantic all-even certificate elimination.  Its only remaining
hypothesis is the local fixed-weight character sum for weights one through
four.
-/

namespace Quantum1435

/-- The local Krawtchouk character identities imply the four semantic
MacWilliams rows for an 11-dimensional stabilizer. -/
theorem hasMacWilliamsRowsOneToFour_of_fixedWeightCharacterSums
    (S : Submodule F₂ (Pauli 14))
    (hdim : Module.finrank F₂ S = 11)
    (hlocal : ∀ j : Fin 4, FixedWeightCharacterSum 14 (j.1 + 1)) :
    HasMacWilliamsRowsOneToFour S := by
  intro j
  have h := macWilliams_coefficient_of_fixedWeightCharacterSum S (hlocal j)
  rw [submodule_card_of_finrank_eleven S hdim] at h
  simpa [mul_comm] using h.symm

/-- End-to-end elimination of an actual all-even stabilizer candidate,
conditional only on the four local fixed-weight character identities. -/
theorem no_allEven_candidate_of_fixedWeightCharacterSums
    (S : Submodule F₂ (Pauli 14))
    (hcandidate : IsCandidate1435 S)
    (heven : IsAllEven S)
    (hlocal : ∀ j : Fin 4, FixedWeightCharacterSum 14 (j.1 + 1)) : False :=
  no_allEven_candidate_of_macWilliamsRows S hcandidate heven
    (hasMacWilliamsRowsOneToFour_of_fixedWeightCharacterSums S hcandidate.1 hlocal)

end Quantum1435
