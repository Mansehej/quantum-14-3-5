import Quantum1435.P03ShadowPairs
import Quantum1435.P11Geometry
import Mathlib.Tactic

/-!
# Low-weight shadow geometry in the p01 profile

These arguments use the literal shadow coset and logical-distance condition.
They do not depend on the extension-average rows or on a coordinate normal
form.
-/

noncomputable section

namespace Quantum1435

private theorem shadow_sum_mem_stabilizer_of_weight_le_four
    (S : Submodule F₂ (Pauli 14)) (hcandidate : IsCandidate1435 S)
    {u v : Pauli 14}
    (hu : IsShadowWord S hcandidate.2.1 u)
    (hv : IsShadowWord S hcandidate.2.1 v)
    (hweight : pauliWeight (u + v) ≤ 4) :
    u + v ∈ S := by
  have hnormalizer : u + v ∈ symplecticNormalizer S :=
    shadowWord_add_shadowWord_mem_normalizer hu hv
  by_contra hnotS
  have hdistance : 5 ≤ pauliWeight (u + v) :=
    hcandidate.2.2 (u + v) ⟨hnormalizer, hnotS⟩
  omega

private theorem shadow_sum_weight_ne_zero_of_different_weights
    {u v : Pauli 14} {j k : ℕ}
    (hu : pauliWeight u = j) (hv : pauliWeight v = k)
    (hjk : j ≠ k) :
    pauliWeight (u + v) ≠ 0 := by
  intro hzero
  have huv := eq_of_pauliWeight_add_eq_zero hzero
  rw [huv] at hu
  exact hjk (hu.symm.trans hv)

/-- If the stabilizer has no words of weights one or two, its literal
shadow contains at most one word of weight one. -/
theorem p01_shadowWeightDistribution_one_le_one
    (S : Submodule F₂ (Pauli 14)) (hcandidate : IsCandidate1435 S)
    (hA1 : weightDistribution S 1 = 0)
    (hA2 : weightDistribution S 2 = 0) :
    shadowWeightDistribution S hcandidate.2.1 1 ≤ 1 := by
  rw [← card_shadowWordsOfWeight S hcandidate.2.1 (j := 1),
    Finset.card_le_one]
  intro u hu v hv
  by_contra huv
  have huData :=
    (mem_shadowWordsOfWeight S hcandidate.2.1 u).mp hu
  have hvData :=
    (mem_shadowWordsOfWeight S hcandidate.2.1 v).mp hv
  have hsumle := pauliWeight_add_le u v
  rw [huData.2, hvData.2] at hsumle
  have hsumS : u + v ∈ S :=
    shadow_sum_mem_stabilizer_of_weight_le_four
      S hcandidate huData.1 hvData.1 (by omega)
  have hneZero : pauliWeight (u + v) ≠ 0 := by
    intro hzero
    exact huv (eq_of_pauliWeight_add_eq_zero hzero)
  have hcases :
      pauliWeight (u + v) = 1 ∨ pauliWeight (u + v) = 2 := by
    omega
  rcases hcases with hone | htwo
  · exact (not_mem_of_weightDistribution_eq_zero S hA1 hone) hsumS
  · exact (not_mem_of_weightDistribution_eq_zero S hA2 htwo) hsumS

/-- In profile p01, a unique weight-one shadow word excludes weight-two
shadow words and leaves at most one weight-three shadow word. -/
theorem p01_shadow_one_forces_two_zero_three_le_one
    (S : Submodule F₂ (Pauli 14)) (hcandidate : IsCandidate1435 S)
    (hA1 : weightDistribution S 1 = 0)
    (hA2 : weightDistribution S 2 = 0)
    (hA3 : weightDistribution S 3 = 0)
    (hA4 : weightDistribution S 4 = 1)
    (hS1 : shadowWeightDistribution S hcandidate.2.1 1 = 1) :
    shadowWeightDistribution S hcandidate.2.1 2 = 0 ∧
      shadowWeightDistribution S hcandidate.2.1 3 ≤ 1 := by
  have hcardOne :
      (shadowWordsOfWeight S hcandidate.2.1 1).card = 1 :=
    (card_shadowWordsOfWeight S hcandidate.2.1 (j := 1)).trans hS1
  obtain ⟨h, hwords⟩ := Finset.card_eq_one.mp hcardOne
  have hh :
      h ∈ shadowWordsOfWeight S hcandidate.2.1 1 := by
    simp [hwords]
  have hhData :=
    (mem_shadowWordsOfWeight S hcandidate.2.1 h).mp hh
  constructor
  · rw [← card_shadowWordsOfWeight S hcandidate.2.1 (j := 2)]
    by_contra hcard
    have hpos :
        0 < (shadowWordsOfWeight S hcandidate.2.1 2).card :=
      Nat.pos_of_ne_zero hcard
    obtain ⟨g, hg⟩ := Finset.card_pos.mp hpos
    have hgData :=
      (mem_shadowWordsOfWeight S hcandidate.2.1 g).mp hg
    have hsumle := pauliWeight_add_le h g
    rw [hhData.2, hgData.2] at hsumle
    have hsumS : h + g ∈ S :=
      shadow_sum_mem_stabilizer_of_weight_le_four
        S hcandidate hhData.1 hgData.1 (by omega)
    have hneZero : pauliWeight (h + g) ≠ 0 :=
      shadow_sum_weight_ne_zero_of_different_weights
        hhData.2 hgData.2 (by decide)
    have hcases : pauliWeight (h + g) = 1 ∨
        pauliWeight (h + g) = 2 ∨ pauliWeight (h + g) = 3 := by
      omega
    rcases hcases with hone | htwo | hthree
    · exact (not_mem_of_weightDistribution_eq_zero S hA1 hone) hsumS
    · exact (not_mem_of_weightDistribution_eq_zero S hA2 htwo) hsumS
    · exact (not_mem_of_weightDistribution_eq_zero S hA3 hthree) hsumS
  · rw [← card_shadowWordsOfWeight S hcandidate.2.1 (j := 3),
      Finset.card_le_one]
    intro g hg g' hg'
    have hgData :=
      (mem_shadowWordsOfWeight S hcandidate.2.1 g).mp hg
    have hg'Data :=
      (mem_shadowWordsOfWeight S hcandidate.2.1 g').mp hg'
    have hsumle := pauliWeight_add_le h g
    have hsumle' := pauliWeight_add_le h g'
    rw [hhData.2, hgData.2] at hsumle
    rw [hhData.2, hg'Data.2] at hsumle'
    have hsumS : h + g ∈ S :=
      shadow_sum_mem_stabilizer_of_weight_le_four
        S hcandidate hhData.1 hgData.1 (by omega)
    have hsumS' : h + g' ∈ S :=
      shadow_sum_mem_stabilizer_of_weight_le_four
        S hcandidate hhData.1 hg'Data.1 (by omega)
    have hneZero : pauliWeight (h + g) ≠ 0 :=
      shadow_sum_weight_ne_zero_of_different_weights
        hhData.2 hgData.2 (by decide)
    have hneZero' : pauliWeight (h + g') ≠ 0 :=
      shadow_sum_weight_ne_zero_of_different_weights
        hhData.2 hg'Data.2 (by decide)
    have hweightFour : pauliWeight (h + g) = 4 := by
      have hneOne : pauliWeight (h + g) ≠ 1 := by
        intro hone
        exact (not_mem_of_weightDistribution_eq_zero S hA1 hone) hsumS
      have hneTwo : pauliWeight (h + g) ≠ 2 := by
        intro htwo
        exact (not_mem_of_weightDistribution_eq_zero S hA2 htwo) hsumS
      have hneThree : pauliWeight (h + g) ≠ 3 := by
        intro hthree
        exact (not_mem_of_weightDistribution_eq_zero S hA3 hthree) hsumS
      omega
    have hweightFour' : pauliWeight (h + g') = 4 := by
      have hneOne : pauliWeight (h + g') ≠ 1 := by
        intro hone
        exact (not_mem_of_weightDistribution_eq_zero S hA1 hone) hsumS'
      have hneTwo : pauliWeight (h + g') ≠ 2 := by
        intro htwo
        exact (not_mem_of_weightDistribution_eq_zero S hA2 htwo) hsumS'
      have hneThree : pauliWeight (h + g') ≠ 3 := by
        intro hthree
        exact (not_mem_of_weightDistribution_eq_zero S hA3 hthree) hsumS'
      omega
    obtain ⟨u, hu, huUnique⟩ :=
      existsUnique_of_weightDistribution_eq_one S hA4
    have hgu : h + g = u := huUnique (h + g) ⟨hsumS, hweightFour⟩
    have hg'u : h + g' = u := huUnique (h + g') ⟨hsumS', hweightFour'⟩
    exact add_left_cancel (hgu.trans hg'u.symm)

end Quantum1435
