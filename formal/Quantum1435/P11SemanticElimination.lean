import Quantum1435.P11Geometry
import Quantum1435.P03ShadowVertices
import Quantum1435.OddUniversalSemantic
import Mathlib.Tactic

/-!
# Semantic elimination of the p11 profile

This module connects the actual stabilizer and shadow coefficients to the
already checked p11 arithmetic contradiction. The universal-row interface is
populated by the literal signed-shadow theorem.
-/

noncomputable section

namespace Quantum1435

/-- An actual candidate in profile p11 is impossible once the two universal
odd-branch rows have been derived. Only the first universal row is needed in
this branch. -/
theorem p11_candidate_false_of_semanticOddUniversalRows
    (S : Submodule F₂ (Pauli 14)) (hcandidate : IsCandidate1435 S)
    (hodd : ContainsOddWord S)
    (hA2 : weightDistribution S 2 = 1)
    (hA4 : weightDistribution S 4 = 1)
    (hrows : SemanticOddUniversalRows S hcandidate.2.1) :
    False := by
  have hprofile := oddCandidate_profile_trichotomy S hcandidate hodd
  have hA1 : weightDistribution S 1 = 0 := hprofile.1
  have hA3 : weightDistribution S 3 = 0 := hprofile.2.1
  have hid := identity51_of_sourceRows
    (oddIdentity51SourceRows S hcandidate hodd)
  change
    168 * weightDistribution S 1 + 28 * weightDistribution S 2 +
      63 * weightDistribution S 3 + 15 * weightDistribution S 4 +
      14 * weightDistribution S 5 + 4 * weightDistribution S 6 +
      2 * weightDistribution S 14 +
      4 * weightDistribution
        (symplecticNormalizer
          (parityKernelAmbient S hcandidate.2.1)) 1 +
      2 * weightDistribution
        (symplecticNormalizer
          (parityKernelAmbient S hcandidate.2.1)) 4 = 51 at hid
  have hpartition1 :=
    parityKernelNormalizer_weightDistribution_eq_stabilizer_add_shadow
      S hcandidate.2.1 hcandidate.2.2 (j := 1) (by omega)
  have hpartition4 :=
    parityKernelNormalizer_weightDistribution_eq_stabilizer_add_shadow
      S hcandidate.2.1 hcandidate.2.2 (j := 4) (by omega)
  rw [hpartition1, hpartition4] at hid
  have hidentity :
      14 * weightDistribution S 5 + 4 * weightDistribution S 6 +
        2 * weightDistribution S 14 +
        4 * shadowWeightDistribution S hcandidate.2.1 1 +
        2 * shadowWeightDistribution S hcandidate.2.1 4 = 6 := by
    omega
  have hA6 : 1 ≤ weightDistribution S 6 :=
    p11_weightDistribution_six_pos
      S hcandidate.2.1 hA1 hA2 hA4
  have ha14 :
      weightDistribution S 14 + 12 * weightDistribution S 5 +
        3 * weightDistribution S 6 +
        4 * shadowWeightDistribution S hcandidate.2.1 2 +
        2 * shadowWeightDistribution S hcandidate.2.1 4 = 6 := by
    have h := hrows.a14Row
    omega
  exact noP11ArithmeticData
    ⟨{
      A5 := weightDistribution S 5
      A6 := weightDistribution S 6
      A14 := weightDistribution S 14
      S1 := shadowWeightDistribution S hcandidate.2.1 1
      S2 := shadowWeightDistribution S hcandidate.2.1 2
      S4 := shadowWeightDistribution S hcandidate.2.1 4
      identitySpecialized := hidentity
      a6Positive := hA6
      a14Row := ha14
    }⟩

/-- No actual odd candidate can lie in profile `(A₂,A₄)=(1,1)`. -/
theorem p11_candidate_false
    (S : Submodule F₂ (Pauli 14)) (hcandidate : IsCandidate1435 S)
    (hodd : ContainsOddWord S)
    (hA2 : weightDistribution S 2 = 1)
    (hA4 : weightDistribution S 4 = 1) :
    False :=
  p11_candidate_false_of_semanticOddUniversalRows
    S hcandidate hodd hA2 hA4
      (semanticOddUniversalRows S hcandidate hodd)

end Quantum1435
