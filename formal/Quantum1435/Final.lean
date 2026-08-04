import Quantum1435.ProfileReduction
import Quantum1435.P01SemanticElimination
import Quantum1435.P03SemanticElimination
import Quantum1435.P11SemanticElimination

/-!
# Nonexistence of a binary `[[14,3,5]]` stabilizer code

The all-even branch is impossible, so every candidate has an odd word and
lies in one of the three actual low-weight profiles.  The semantic p01, p03,
and p11 theorems eliminate those profiles exhaustively.
-/

namespace Quantum1435

/-- Candidate-level contradiction for an arbitrary 11-dimensional totally
isotropic stabilizer whose logical distance is at least five. -/
theorem noCandidate1435
    (S : Submodule F₂ (Pauli 14)) (hcandidate : IsCandidate1435 S) :
    False := by
  have hodd := candidate_containsOddWord S hcandidate
  obtain ⟨_hA1, _hA3, hprofiles⟩ :=
    candidate_profile_trichotomy S hcandidate
  rcases hprofiles with h01 | h03 | h11
  · exact p01_candidate_false
      S hcandidate hodd h01.1 h01.2
  · exact p03_candidate_false
      S hcandidate hodd h03.1 h03.2
  · exact p11_candidate_false
      S hcandidate hodd h11.1 h11.2

/-- There is no binary `[[14,3]]` stabilizer code of logical distance at
least five.  Because the logical-distance predicate quantifies over
`Sᵖ \\ S`, this includes degenerate codes. -/
theorem noBinaryStabilizer1435 : NoBinaryStabilizer1435 := by
  rintro ⟨S, hcandidate⟩
  exact noCandidate1435 S hcandidate

/-- In particular, no binary `[[14,3,5]]` stabilizer code exists when
distance is stated as the exact minimum weight in `Sᵖ \\ S`. -/
theorem noBinaryStabilizerExact1435 :
    ¬ ∃ S : Submodule F₂ (Pauli 14),
      Module.finrank F₂ S = 11 ∧
        IsTotallyIsotropic S ∧ LogicalDistanceIs S 5 := by
  rintro ⟨S, hdim, hiso, hdistance⟩
  exact noBinaryStabilizer1435
    ⟨S, exactDistanceFive_isCandidate hdim hiso hdistance⟩

end Quantum1435
