import Quantum1435.P03ShadowVertices
import Quantum1435.P03TripleClassification

/-!
# Semantic p03 weight-four geometry

This module feeds the actual p03 profile and the semantically forced
coefficient `A₆ = 0` into the invariant classification of the three actual
weight-four stabilizer words. The reusable theorem takes the two universal
odd-branch rows through the explicit `SemanticOddUniversalRows` interface;
the final elimination supplies that interface semantically.
-/

namespace Quantum1435

/-- An actual p03 candidate has an exhaustive weight-four triple of one of
the three rank-two category types or the pairwise-disjoint rank-three type,
assuming the explicit semantic universal-row interface. -/
theorem p03_candidate_exists_classified_weightFour_triple
    (S : Submodule F₂ (Pauli 14)) (hcandidate : IsCandidate1435 S)
    (hodd : ContainsOddWord S)
    (hA2 : weightDistribution S 2 = 0)
    (hA4 : weightDistribution S 4 = 3)
    (hrows : SemanticOddUniversalRows S hcandidate.2.1) :
    ∃ u v w : Pauli 14,
      u ∈ S ∧ pauliWeight u = 4 ∧
      v ∈ S ∧ pauliWeight v = 4 ∧
      w ∈ S ∧ pauliWeight w = 4 ∧
      u ≠ v ∧ u ≠ w ∧ v ≠ w ∧
      (∀ x, x ∈ S ∧ pauliWeight x = 4 ↔
        x = u ∨ x = v ∨ x = w) ∧
      P03TripleGeometry u v w := by
  have hprofile := oddCandidate_profile_trichotomy S hcandidate hodd
  have hA1 : weightDistribution S 1 = 0 := hprofile.1
  have hA3 : weightDistribution S 3 = 0 := hprofile.2.1
  have hforced := p03_semantic_forced_counts
    S hcandidate hodd hA2 hA4 hrows
  have hA6 : weightDistribution S 6 = 0 := hforced.2.1
  exact p03_exists_classified_weightFour_triple
    S hcandidate.2.1 hA1 hA2 hA3 hA4 hA6

end Quantum1435
