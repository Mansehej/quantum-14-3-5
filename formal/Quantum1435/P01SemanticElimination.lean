import Quantum1435.P01ReducedBins
import Quantum1435.OddUniversalSemantic
import Mathlib.Tactic

/-!
# Semantic elimination of the p01 profile

The actual stabilizer and literal shadow populate `P01ArithmeticData` using
Identity 51, the two proved universal rows, low-shadow geometry, and the
invariant 42/36-bin incidence bounds.  The checked Presburger contradiction
then eliminates the profile.
-/

noncomputable section

namespace Quantum1435

/-- No actual odd candidate can lie in profile `(A₂,A₄)=(0,1)`. -/
theorem p01_candidate_false
    (S : Submodule F₂ (Pauli 14)) (hcandidate : IsCandidate1435 S)
    (hodd : ContainsOddWord S)
    (hA2 : weightDistribution S 2 = 0)
    (hA4 : weightDistribution S 4 = 1) :
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
        2 * shadowWeightDistribution S hcandidate.2.1 4 = 34 := by
    omega
  have hrows := semanticOddUniversalRows S hcandidate hodd
  have ha14 :
      weightDistribution S 14 + 12 * weightDistribution S 5 +
        3 * weightDistribution S 6 +
        4 * shadowWeightDistribution S hcandidate.2.1 2 +
        2 * shadowWeightDistribution S hcandidate.2.1 4 = 24 := by
    have h := hrows.a14Row
    omega
  have hs3 :
      2 * shadowWeightDistribution S hcandidate.2.1 3 +
        38 * weightDistribution S 5 + 6 * weightDistribution S 6 +
        36 * shadowWeightDistribution S hcandidate.2.1 2 +
        8 * shadowWeightDistribution S hcandidate.2.1 4 = 86 := by
    have h := hrows.s3Row
    omega
  have ha6Specialized :
      weightDistribution S 6 + 5 * weightDistribution S 5 +
        4 * shadowWeightDistribution S hcandidate.2.1 2 +
        shadowWeightDistribution S hcandidate.2.1 4 =
      7 + 2 * shadowWeightDistribution S hcandidate.2.1 1 := by
    omega
  have ha14Specialized :
      weightDistribution S 14 +
        6 * shadowWeightDistribution S hcandidate.2.1 1 =
      3 + 3 * weightDistribution S 5 +
        8 * shadowWeightDistribution S hcandidate.2.1 2 +
        shadowWeightDistribution S hcandidate.2.1 4 := by
    omega
  have hs3Specialized :
      shadowWeightDistribution S hcandidate.2.1 3 +
        4 * weightDistribution S 5 +
        6 * shadowWeightDistribution S hcandidate.2.1 2 +
        shadowWeightDistribution S hcandidate.2.1 4 +
        6 * shadowWeightDistribution S hcandidate.2.1 1 = 22 := by
    omega
  exact noP01ArithmeticData
    ⟨{
      A5 := weightDistribution S 5
      A6 := weightDistribution S 6
      A14 := weightDistribution S 14
      S1 := shadowWeightDistribution S hcandidate.2.1 1
      S2 := shadowWeightDistribution S hcandidate.2.1 2
      S3 := shadowWeightDistribution S hcandidate.2.1 3
      S4 := shadowWeightDistribution S hcandidate.2.1 4
      a6Row := ha6Specialized
      a14Row := ha14Specialized
      s3Row := hs3Specialized
      s1LeOne :=
        p01_shadowWeightDistribution_one_le_one
          S hcandidate hA1 hA2
      s1One :=
        p01_shadow_one_forces_two_zero_three_le_one
          S hcandidate hA1 hA2 hA3 hA4
      fortyTwoBinBound := fun _hS1 ↦
        p01_shadowWeightDistribution_three_le_fourteen
          S hcandidate hA1 hA2 hA3 hA4
      thirtySixBinBound := fun _hS1 hS2 ↦
        p01_shadowWeightDistribution_three_le_twelve_of_two_eq_one
          S hcandidate hA1 hA2 hA3 hA4 hS2
    }⟩

end Quantum1435
