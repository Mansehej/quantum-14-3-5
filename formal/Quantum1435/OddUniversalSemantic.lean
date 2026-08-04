import Quantum1435.OddUniversalS3Certificate
import Quantum1435.OddSignedShadow4
import Quantum1435.P03ShadowVertices
import Mathlib.Tactic

/-!
# Universal odd-branch rows from the literal signed shadow

The semantic work establishes the ordinary and signed-shadow source rows.
The final elimination is delegated to kernel-checked pure-integer
certificates, so no extension-space or Lagrangian classification is needed.
-/

noncomputable section

namespace Quantum1435

/-- Every odd `[[14,3,≥5]]` candidate satisfies the two universal rows for
its literal shadow `C₀ᵖ \\ Sᵖ`. -/
theorem semanticOddUniversalRows
    (S : Submodule F₂ (Pauli 14)) (hcandidate : IsCandidate1435 S)
    (hodd : ContainsOddWord S) :
    SemanticOddUniversalRows S hcandidate.2.1 := by
  have hprofile := oddCandidate_profile_trichotomy S hcandidate hodd
  let d : OddUniversalSourceRows :=
    { A1 := (weightDistribution S 1 : ℤ)
      A2 := (weightDistribution S 2 : ℤ)
      A3 := (weightDistribution S 3 : ℤ)
      A4 := (weightDistribution S 4 : ℤ)
      A5 := (weightDistribution S 5 : ℤ)
      A6 := (weightDistribution S 6 : ℤ)
      A7 := (weightDistribution S 7 : ℤ)
      A8 := (weightDistribution S 8 : ℤ)
      A9 := (weightDistribution S 9 : ℤ)
      A10 := (weightDistribution S 10 : ℤ)
      A11 := (weightDistribution S 11 : ℤ)
      A12 := (weightDistribution S 12 : ℤ)
      A13 := (weightDistribution S 13 : ℤ)
      A14 := (weightDistribution S 14 : ℤ)
      S2 := (shadowWeightDistribution S hcandidate.2.1 2 : ℤ)
      S3 := (shadowWeightDistribution S hcandidate.2.1 3 : ℤ)
      S4 := (shadowWeightDistribution S hcandidate.2.1 4 : ℤ)
      a1Zero := by exact_mod_cast hprofile.1
      a3Zero := by exact_mod_cast hprofile.2.1
      total := candidate_nonzeroWeightTotal S hcandidate.1
      evenTotal := by
        exact_mod_cast
          (oddBranch_evenWeightTotal
            S hcandidate.2.1 hcandidate.1 hodd)
      macWilliams1 := oddMacWilliams1 S hcandidate
      macWilliams2 := oddMacWilliams2 S hcandidate
      macWilliams3 := oddMacWilliams3 S hcandidate
      macWilliams4 := oddMacWilliams4 S hcandidate
      signedShadow2 := oddSignedShadow2 S hcandidate hodd
      signedShadow3 := oddSignedShadow3 S hcandidate hodd
      signedShadow4 := oddSignedShadow4 S hcandidate hodd }
  constructor
  · have h := oddUniversalA14_of_sourceRows d
    dsimp only [d] at h
    exact_mod_cast h
  · have h := oddUniversalS3_of_sourceRows d
    dsimp only [d] at h
    exact_mod_cast h

end Quantum1435
