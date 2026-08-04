import Quantum1435.P01IncidenceBounds
import Mathlib.Tactic

/-!
# The reduced 36-bin incidence bound for p01

A weight-two shadow word is support-disjoint from every weight-three shadow
word in the p01 profile.  Removing its two coordinates leaves twelve
coordinates and hence thirty-six nonidentity coordinate/label bins.
-/

noncomputable section

namespace Quantum1435

open scoped BigOperators

/-- A weight-two shadow word vanishes on the support of every weight-three
shadow word in the p01 profile. -/
private theorem p01_weightTwoShadow_zero_on_weightThreeSupport
    (S : Submodule F₂ (Pauli 14)) (hcandidate : IsCandidate1435 S)
    (hA1 : weightDistribution S 1 = 0)
    (hA2 : weightDistribution S 2 = 0)
    (hA3 : weightDistribution S 3 = 0)
    (hA4 : weightDistribution S 4 = 1)
    {h g : Pauli 14}
    (hh : h ∈ shadowWordsOfWeight S hcandidate.2.1 2)
    (hg : g ∈ weightThreeShadowWords S hcandidate.2.1) :
    ∀ i, g i ≠ 0 → h i = 0 := by
  have hhData :=
    (mem_shadowWordsOfWeight S hcandidate.2.1 h).mp hh
  have hgData :=
    (mem_weightThreeShadowWords S hcandidate.2.1 g).mp hg
  have hsumFive : pauliWeight (h + g) = 5 := by
    have hupper := pauliWeight_add_le h g
    rw [hhData.2, hgData.2] at hupper
    have hnotLow : ¬ pauliWeight (h + g) ≤ 4 := by
      intro hlow
      have hnormalizer : h + g ∈ symplecticNormalizer S :=
        shadowWord_add_shadowWord_mem_normalizer hhData.1 hgData.1
      have hsumS : h + g ∈ S := by
        by_contra hnotS
        have hdistance : 5 ≤ pauliWeight (h + g) :=
          hcandidate.2.2 (h + g) ⟨hnormalizer, hnotS⟩
        omega
      have hneZero : pauliWeight (h + g) ≠ 0 := by
        intro hzero
        have heq : h = g := eq_of_pauliWeight_add_eq_zero hzero
        have hweightsEqual : (2 : ℕ) = 3 := by
          calc
            2 = pauliWeight h := hhData.2.symm
            _ = pauliWeight g := congrArg pauliWeight heq
            _ = 3 := hgData.2
        omega
      have hneOne : pauliWeight (h + g) ≠ 1 := by
        intro hone
        exact (not_mem_of_weightDistribution_eq_zero S hA1 hone) hsumS
      have hneTwo : pauliWeight (h + g) ≠ 2 := by
        intro htwo
        exact (not_mem_of_weightDistribution_eq_zero S hA2 htwo) hsumS
      have hneThree : pauliWeight (h + g) ≠ 3 := by
        intro hthree
        exact (not_mem_of_weightDistribution_eq_zero S hA3 hthree) hsumS
      have hweightFour : pauliWeight (h + g) = 4 := by
        omega
      obtain ⟨u, hu, huUnique⟩ :=
        existsUnique_of_weightDistribution_eq_one S hA4
      have hsumEq : h + g = u :=
        huUnique (h + g) ⟨hsumS, hweightFour⟩
      have hhEven : pauliParity h = 0 := by
        rw [pauliParity_eq_weight_cast, hhData.2]
        decide
      have huEven : pauliParity u = 0 := by
        rw [pauliParity_eq_weight_cast, hu.2]
        decide
      have huKernel : u ∈ parityKernelAmbient S hcandidate.2.1 :=
        (mem_parityKernelAmbient_iff S hcandidate.2.1 u).mpr
          ⟨hu.1, huEven⟩
      have hcomm : symplecticForm 14 u h = 0 :=
        shadowWord_commutes_with_parityKernel
          hhData.1 u huKernel
      have hself : h + h = 0 := by
        funext i
        change h i + h i = (0 : F₂ × F₂)
        exact CharTwo.add_self_eq_zero (h i)
      have huh : u + h = g := by
        calc
          u + h = (h + g) + h :=
            congrArg (fun x : Pauli 14 ↦ x + h) hsumEq.symm
          _ = (h + h) + g := by ac_rfl
          _ = 0 + g :=
            congrArg (fun x : Pauli 14 ↦ x + g)
              hself
          _ = g := zero_add g
      have hparityUg : pauliParity (u + h) = 0 := by
        rw [pauliParity_add, huEven, hhEven, hcomm]
        decide
      have hgOdd : pauliParity g = 1 := by
        rw [pauliParity_eq_weight_cast, hgData.2]
        decide
      rw [huh, hgOdd] at hparityUg
      exact (show (1 : F₂) ≠ 0 by decide) hparityUg
    omega
  have hhCategories := pauliWeight_eq_categories_ACD h g
  have hgCategories := pauliWeight_eq_categories_BCD h g
  have hsumCategories := pauliWeight_add_eq_categories_ABD h g
  rw [hhData.2] at hhCategories
  rw [hgData.2] at hgCategories
  rw [hsumFive] at hsumCategories
  have hCzero : p03CategoryC h g = 0 := by
    omega
  have hDzero : p03CategoryD h g = 0 := by
    omega
  intro i hgi
  by_contra hhi
  by_cases heq : h i = g i
  · have hCpos : 0 < p03CategoryC h g := by
      unfold p03CategoryC
      apply Finset.card_pos.mpr
      exact ⟨i, Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hhi, heq⟩⟩
    omega
  · have hDpos : 0 < p03CategoryD h g := by
      unfold p03CategoryD
      apply Finset.card_pos.mpr
      exact ⟨i, Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hhi, hgi, heq⟩⟩
    omega

/-- Coordinate/label bins away from the support of a fixed Pauli word. -/
def p01BinsAwayFrom (h : Pauli 14) : Finset P03Bin :=
  (Finset.univ.filter fun i : Fin 14 ↦ h i = 0).product
    (Finset.univ.erase (.I : LocalPauli))

@[simp] theorem mem_p01BinsAwayFrom
    (h : Pauli 14) (bin : P03Bin) :
    bin ∈ p01BinsAwayFrom h ↔
      h bin.1 = 0 ∧ bin.2 ≠ .I := by
  simp [p01BinsAwayFrom]

theorem p01BinsAwayFrom_subset_available (h : Pauli 14) :
    p01BinsAwayFrom h ⊆ p03AvailableBins := by
  intro bin hbin
  have hdata := (mem_p01BinsAwayFrom h bin).mp hbin
  simpa [p03AvailableBins] using hdata.2

theorem p01BinsAwayFrom_card_of_weight_two
    (h : Pauli 14) (hweight : pauliWeight h = 2) :
    (p01BinsAwayFrom h).card = 36 := by
  have hsplit :=
    (Finset.univ : Finset (Fin 14)).card_filter_add_card_filter_not
      (fun i ↦ h i = 0)
  have hnonzero :
      (Finset.univ.filter fun i : Fin 14 ↦ ¬ h i = 0).card = 2 := by
    simpa [pauliWeight] using hweight
  have hzero :
      (Finset.univ.filter fun i : Fin 14 ↦ h i = 0).card = 12 := by
    have huniv : (Finset.univ : Finset (Fin 14)).card = 14 := by
      simp
    rw [huniv] at hsplit
    omega
  have hlabels :
      ((Finset.univ : Finset LocalPauli).erase .I).card = 3 := by
    decide
  rw [p01BinsAwayFrom, Finset.product_eq_sprod,
    Finset.card_product, hzero, hlabels]

/-- A unique weight-two shadow word reduces the effective incidence space
from 42 bins to 36, forcing at most twelve weight-three shadow words. -/
theorem p01_shadowWeightDistribution_three_le_twelve_of_two_eq_one
    (S : Submodule F₂ (Pauli 14)) (hcandidate : IsCandidate1435 S)
    (hA1 : weightDistribution S 1 = 0)
    (hA2 : weightDistribution S 2 = 0)
    (hA3 : weightDistribution S 3 = 0)
    (hA4 : weightDistribution S 4 = 1)
    (hS2 : shadowWeightDistribution S hcandidate.2.1 2 = 1) :
    shadowWeightDistribution S hcandidate.2.1 3 ≤ 12 := by
  have hcardTwo :
      (shadowWordsOfWeight S hcandidate.2.1 2).card = 1 := by
    rw [card_shadowWordsOfWeight]
    exact hS2
  obtain ⟨h, hwords⟩ := Finset.card_eq_one.mp hcardTwo
  have hh : h ∈ shadowWordsOfWeight S hcandidate.2.1 2 := by
    simp [hwords]
  have hhData :=
    (mem_shadowWordsOfWeight S hcandidate.2.1 h).mp hh
  have hdegree :
      ∀ word ∈ p03ShadowCollisionWords S hcandidate.2.1,
        ((p01BinsAwayFrom h).filter
          fun bin ↦ p03WordIncident word bin).card = 3 := by
    intro word hword
    have hwordSubset : word.wordBins ⊆ p01BinsAwayFrom h := by
      rcases Finset.mem_image.mp hword with ⟨g, hg, rfl⟩
      intro bin hbin
      have hbinData :=
        (CollisionWord.mem_wordBins_ofPauli_iff g bin).mp hbin
      have hhzero :=
        p01_weightTwoShadow_zero_on_weightThreeSupport
          S hcandidate hA1 hA2 hA3 hA4 hh hg
            bin.1 hbinData.1
      have hlabel : bin.2 ≠ .I := by
        simpa [p03AvailableBins] using
          (CollisionWord.wordBins_subset_available
            (CollisionWord.ofPauli g) hbin)
      exact (mem_p01BinsAwayFrom h bin).mpr ⟨hhzero, hlabel⟩
    have hfilter :
        (p01BinsAwayFrom h).filter
            (fun bin ↦ p03WordIncident word bin) =
          word.wordBins := by
      ext bin
      constructor
      · intro hbin
        exact (Finset.mem_filter.mp hbin).2
      · intro hbin
        exact Finset.mem_filter.mpr ⟨hwordSubset hbin, hbin⟩
    rw [hfilter]
    exact p03ShadowCollisionWords_card_wordBins
      S hcandidate.2.1 word hword
  have hincidence :=
    six_mul_selected_card_le_two_mul_bins_card_add_pairSum
      (p03ShadowCollisionWords S hcandidate.2.1)
      (p01BinsAwayFrom h) p03WordIncident hdegree
  have hpairsAll :
      (∑ bin ∈ p03AvailableBins,
        incidenceOccupancy
            (p03ShadowCollisionWords S hcandidate.2.1)
            p03WordIncident bin *
          (incidenceOccupancy
            (p03ShadowCollisionWords S hcandidate.2.1)
            p03WordIncident bin - 1)) ≤ 2 := by
    calc
      (∑ bin ∈ p03AvailableBins,
        incidenceOccupancy
            (p03ShadowCollisionWords S hcandidate.2.1)
            p03WordIncident bin *
          (incidenceOccupancy
            (p03ShadowCollisionWords S hcandidate.2.1)
            p03WordIncident bin - 1)) =
          (p03ShadowSharedPairs S hcandidate.2.1).card :=
        (card_p03ShadowSharedPairs_eq_incidenceOccupancy_sum
          S hcandidate hA1 hA2).symm
      _ ≤ 2 :=
        p01_card_p03ShadowSharedPairs_le_two
          S hcandidate hA1 hA2 hA3 hA4
  have hpairsReduced :
      (∑ bin ∈ p01BinsAwayFrom h,
        incidenceOccupancy
            (p03ShadowCollisionWords S hcandidate.2.1)
            p03WordIncident bin *
          (incidenceOccupancy
            (p03ShadowCollisionWords S hcandidate.2.1)
            p03WordIncident bin - 1)) ≤ 2 := by
    calc
      (∑ bin ∈ p01BinsAwayFrom h,
        incidenceOccupancy
            (p03ShadowCollisionWords S hcandidate.2.1)
            p03WordIncident bin *
          (incidenceOccupancy
            (p03ShadowCollisionWords S hcandidate.2.1)
            p03WordIncident bin - 1)) ≤
          ∑ bin ∈ p03AvailableBins,
            incidenceOccupancy
                (p03ShadowCollisionWords S hcandidate.2.1)
                p03WordIncident bin *
              (incidenceOccupancy
                (p03ShadowCollisionWords S hcandidate.2.1)
                p03WordIncident bin - 1) :=
        Finset.sum_le_sum_of_subset
          (p01BinsAwayFrom_subset_available h)
      _ ≤ 2 := hpairsAll
  rw [p01BinsAwayFrom_card_of_weight_two h hhData.2,
    p03ShadowCollisionWords_card, card_weightThreeShadowWords] at hincidence
  omega

end Quantum1435
