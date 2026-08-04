import Quantum1435.ShadowEnumeratorBridge
import Mathlib.Tactic

/-!
# Semantic shadow vertices for the p03 branch

This module replaces the abstract coefficient `S3` in the p03 arithmetic
record by the cardinality of an actual finite set of weight-three shadow
vectors. The Identity-51 remainder is derived from the semantic source rows
and the proved coefficientwise partition `E_j = B_j + S_j`.

The two universal rows used by the manuscript are stated through an explicit
semantic interface below. `OddUniversalSemantic` discharges that interface
from the literal signed-shadow transform, without an extension-space or
Lagrangian enumeration. Once supplied, Lean constructs the corresponding
`P03ForcedData` and obtains exactly 24 actual shadow vectors.
-/

noncomputable section

namespace Quantum1435

/-- The literal finite set of weight-`j` vectors in the odd shadow
`C0ᵖ \ Sᵖ`. -/
noncomputable def shadowWordsOfWeight {n : ℕ}
    (S : Submodule F₂ (Pauli n)) (hiso : IsTotallyIsotropic S) (j : ℕ) :
    Finset (Pauli n) := by
  classical
  exact Finset.univ.filter fun v ↦
    IsShadowWord S hiso v ∧ pauliWeight v = j

@[simp] theorem mem_shadowWordsOfWeight {n j : ℕ}
    (S : Submodule F₂ (Pauli n)) (hiso : IsTotallyIsotropic S)
    (v : Pauli n) :
    v ∈ shadowWordsOfWeight S hiso j ↔
      IsShadowWord S hiso v ∧ pauliWeight v = j := by
  classical
  simp [shadowWordsOfWeight]

/-- `shadowWeightDistribution` is the cardinality of the literal finite set,
not an independent arithmetic variable. -/
theorem card_shadowWordsOfWeight {n j : ℕ}
    (S : Submodule F₂ (Pauli n)) (hiso : IsTotallyIsotropic S) :
    (shadowWordsOfWeight S hiso j).card =
      shadowWeightDistribution S hiso j := by
  classical
  simp [shadowWordsOfWeight, shadowWeightDistribution]

/-- The actual shadow vertices used by the p03 incidence argument. -/
noncomputable def weightThreeShadowWords
    (S : Submodule F₂ (Pauli 14)) (hiso : IsTotallyIsotropic S) :
    Finset (Pauli 14) :=
  shadowWordsOfWeight S hiso 3

@[simp] theorem mem_weightThreeShadowWords
    (S : Submodule F₂ (Pauli 14)) (hiso : IsTotallyIsotropic S)
    (v : Pauli 14) :
    v ∈ weightThreeShadowWords S hiso ↔
      IsShadowWord S hiso v ∧ pauliWeight v = 3 := by
  simp [weightThreeShadowWords]

theorem card_weightThreeShadowWords
    (S : Submodule F₂ (Pauli 14)) (hiso : IsTotallyIsotropic S) :
    (weightThreeShadowWords S hiso).card =
      shadowWeightDistribution S hiso 3 := by
  simpa [weightThreeShadowWords] using
    (card_shadowWordsOfWeight S hiso (j := 3))

/-- The manuscript's two universal odd-branch rows, stated directly in terms
of the weight distribution of `S` and its literal shadow. The downstream
theorem `semanticOddUniversalRows` proves this interface for every odd
candidate. -/
structure SemanticOddUniversalRows
    (S : Submodule F₂ (Pauli 14)) (hiso : IsTotallyIsotropic S) : Prop where
  a14Row :
    weightDistribution S 14 + 18 * weightDistribution S 2 +
      12 * weightDistribution S 4 + 12 * weightDistribution S 5 +
      3 * weightDistribution S 6 +
      4 * shadowWeightDistribution S hiso 2 +
      2 * shadowWeightDistribution S hiso 4 = 36
  s3Row :
    2 * shadowWeightDistribution S hiso 3 +
      12 * weightDistribution S 2 + 19 * weightDistribution S 4 +
      38 * weightDistribution S 5 + 6 * weightDistribution S 6 +
      36 * shadowWeightDistribution S hiso 2 +
      8 * shadowWeightDistribution S hiso 4 = 105

/-- In profile p03, Identity 51 and the semantic partitions at weights one
and four give the zero remainder required by `P03ForcedData`.

The `B_j` term in `E_j = B_j + S_j` is replaced by `A_j` only via the
candidate's logical-distance hypothesis, so degenerate stabilizers are
handled correctly. -/
theorem p03_semantic_identity_remainder
    (S : Submodule F₂ (Pauli 14)) (hcandidate : IsCandidate1435 S)
    (hodd : ContainsOddWord S)
    (hA2 : weightDistribution S 2 = 0)
    (hA4 : weightDistribution S 4 = 3) :
    14 * weightDistribution S 5 + 4 * weightDistribution S 6 +
      2 * weightDistribution S 14 +
      4 * shadowWeightDistribution S hcandidate.2.1 1 +
      2 * shadowWeightDistribution S hcandidate.2.1 4 = 0 := by
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
  have hprofile := oddCandidate_profile_trichotomy S hcandidate hodd
  have hA1 := hprofile.1
  have hA3 := hprofile.2.1
  rw [hpartition1, hpartition4] at hid
  omega

/-- Assemble the arithmetic p03 record from an actual candidate, its actual
shadow coefficients, and the two semantic universal rows. -/
noncomputable def p03SemanticForcedData
    (S : Submodule F₂ (Pauli 14)) (hcandidate : IsCandidate1435 S)
    (hodd : ContainsOddWord S)
    (hA2 : weightDistribution S 2 = 0)
    (hA4 : weightDistribution S 4 = 3)
    (hrows : SemanticOddUniversalRows S hcandidate.2.1) : P03ForcedData where
  A5 := weightDistribution S 5
  A6 := weightDistribution S 6
  A14 := weightDistribution S 14
  S1 := shadowWeightDistribution S hcandidate.2.1 1
  S2 := shadowWeightDistribution S hcandidate.2.1 2
  S3 := shadowWeightDistribution S hcandidate.2.1 3
  S4 := shadowWeightDistribution S hcandidate.2.1 4
  identityRemainder :=
    p03_semantic_identity_remainder S hcandidate hodd hA2 hA4
  a14Row := by
    have h := hrows.a14Row
    omega
  s3Row := by
    have h := hrows.s3Row
    omega

/-- The arithmetic conclusion restated entirely for the actual stabilizer
and literal shadow distributions.  This is the semantic form used by the
subsequent weight-four geometry. -/
theorem p03_semantic_forced_counts
    (S : Submodule F₂ (Pauli 14)) (hcandidate : IsCandidate1435 S)
    (hodd : ContainsOddWord S)
    (hA2 : weightDistribution S 2 = 0)
    (hA4 : weightDistribution S 4 = 3)
    (hrows : SemanticOddUniversalRows S hcandidate.2.1) :
    weightDistribution S 5 = 0 ∧ weightDistribution S 6 = 0 ∧
      weightDistribution S 14 = 0 ∧
      shadowWeightDistribution S hcandidate.2.1 1 = 0 ∧
      shadowWeightDistribution S hcandidate.2.1 2 = 0 ∧
      shadowWeightDistribution S hcandidate.2.1 4 = 0 ∧
      shadowWeightDistribution S hcandidate.2.1 3 = 24 := by
  exact p03_forced_counts
    (p03SemanticForcedData S hcandidate hodd hA2 hA4 hrows)

/-- The p03 source rows force the literal finite set of weight-three shadow
vectors to have cardinality 24. -/
theorem p03_weightThreeShadowWords_card_eq_24
    (S : Submodule F₂ (Pauli 14)) (hcandidate : IsCandidate1435 S)
    (hodd : ContainsOddWord S)
    (hA2 : weightDistribution S 2 = 0)
    (hA4 : weightDistribution S 4 = 3)
    (hrows : SemanticOddUniversalRows S hcandidate.2.1) :
    (weightThreeShadowWords S hcandidate.2.1).card = 24 := by
  obtain ⟨-, -, -, -, -, -, hS3⟩ :=
    p03_forced_counts
      (p03SemanticForcedData S hcandidate hodd hA2 hA4 hrows)
  rw [card_weightThreeShadowWords]
  exact hS3

end Quantum1435
