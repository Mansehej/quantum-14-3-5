import Quantum1435.P01InvariantPairs
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Tactic

/-!
# Incidence bounds for the p01 shadow

The invariant shared-pair theorem bounds the ordered occupancy-product sum.
A generic double count then bounds the number of actual weight-three shadow
words.  This replaces the manuscript check over a fixed list of pairs.
-/

noncomputable section

namespace Quantum1435

open scoped BigOperators

private theorem p01_two_mul_le_two_add_mul_pred (n : ℕ) :
    2 * n ≤ 2 + n * (n - 1) := by
  by_cases hn0 : n = 0
  · simp [hn0]
  by_cases hn1 : n = 1
  · simp [hn1]
  have htwo : 2 ≤ n := by omega
  have hmul : 2 * (n - 1) ≤ n * (n - 1) :=
    Nat.mul_le_mul_right (n - 1) htwo
  calc
    2 * n = 2 + 2 * (n - 1) := by omega
    _ ≤ 2 + n * (n - 1) := Nat.add_le_add_left hmul 2

/-- Generic form of the incidence upper bound used in both p01 bin counts. -/
theorem six_mul_selected_card_le_two_mul_bins_card_add_pairSum
    {Vertex Bin : Type*} [DecidableEq Vertex] [DecidableEq Bin]
    (selected : Finset Vertex) (bins : Finset Bin)
    (incident : Vertex → Bin → Prop) [DecidableRel incident]
    (hdegree : ∀ vertex ∈ selected,
      (bins.filter fun bin ↦ incident vertex bin).card = 3) :
    6 * selected.card ≤ bins.card * 2 +
      ∑ bin ∈ bins,
        incidenceOccupancy selected incident bin *
          (incidenceOccupancy selected incident bin - 1) := by
  have hdouble :
      (∑ vertex ∈ selected,
          (bins.filter fun bin ↦ incident vertex bin).card) =
        ∑ bin ∈ bins, incidenceOccupancy selected incident bin := by
    simpa [incidenceOccupancy, Finset.bipartiteAbove,
      Finset.bipartiteBelow] using
      (Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
        (r := incident) (s := selected) (t := bins))
  have hleft :
      (∑ vertex ∈ selected,
          (bins.filter fun bin ↦ incident vertex bin).card) =
        selected.card * 3 := by
    calc
      (∑ vertex ∈ selected,
          (bins.filter fun bin ↦ incident vertex bin).card) =
          ∑ _vertex ∈ selected, 3 := Finset.sum_congr rfl hdegree
      _ = selected.card * 3 := by simp
  have hoccupancy :
      (∑ bin ∈ bins, incidenceOccupancy selected incident bin) =
        selected.card * 3 := by
    rw [← hdouble]
    exact hleft
  have hsum :
      2 * (∑ bin ∈ bins, incidenceOccupancy selected incident bin) ≤
        bins.card * 2 +
          ∑ bin ∈ bins,
            incidenceOccupancy selected incident bin *
              (incidenceOccupancy selected incident bin - 1) := by
    calc
      2 * (∑ bin ∈ bins, incidenceOccupancy selected incident bin) =
          ∑ bin ∈ bins, 2 * incidenceOccupancy selected incident bin := by
            rw [Finset.mul_sum]
      _ ≤ ∑ bin ∈ bins,
          (2 + incidenceOccupancy selected incident bin *
            (incidenceOccupancy selected incident bin - 1)) := by
            exact Finset.sum_le_sum fun bin _ ↦
              p01_two_mul_le_two_add_mul_pred
                (incidenceOccupancy selected incident bin)
      _ = bins.card * 2 +
          ∑ bin ∈ bins,
            incidenceOccupancy selected incident bin *
              (incidenceOccupancy selected incident bin - 1) := by
            rw [Finset.sum_add_distrib]
            simp
  rw [hoccupancy] at hsum
  omega

/-- In the p01 profile, the forty-two ordinary bins and the invariant
shared-pair bound force at most fourteen actual weight-three shadow words. -/
theorem p01_shadowWeightDistribution_three_le_fourteen
    (S : Submodule F₂ (Pauli 14)) (hcandidate : IsCandidate1435 S)
    (hA1 : weightDistribution S 1 = 0)
    (hA2 : weightDistribution S 2 = 0)
    (hA3 : weightDistribution S 3 = 0)
    (hA4 : weightDistribution S 4 = 1) :
    shadowWeightDistribution S hcandidate.2.1 3 ≤ 14 := by
  have hdegree : ∀ word ∈ p03ShadowCollisionWords S hcandidate.2.1,
      (p03AvailableBins.filter fun bin ↦ p03WordIncident word bin).card = 3 := by
    intro word hword
    have hfilter :
        (p03AvailableBins.filter fun bin ↦ p03WordIncident word bin) =
          word.wordBins := by
      ext bin
      constructor
      · intro hbin
        exact (Finset.mem_filter.mp hbin).2
      · intro hbin
        exact Finset.mem_filter.mpr
          ⟨CollisionWord.wordBins_subset_available word hbin, hbin⟩
    rw [hfilter]
    exact p03ShadowCollisionWords_card_wordBins
      S hcandidate.2.1 word hword
  have hincidence :=
    six_mul_selected_card_le_two_mul_bins_card_add_pairSum
      (p03ShadowCollisionWords S hcandidate.2.1)
      p03AvailableBins p03WordIncident hdegree
  have hpairs :=
    p01_card_p03ShadowSharedPairs_le_two
      S hcandidate hA1 hA2 hA3 hA4
  have hpairIdentity :=
    card_p03ShadowSharedPairs_eq_incidenceOccupancy_sum
      S hcandidate hA1 hA2
  rw [← hpairIdentity, p03AvailableBins_card,
    p03ShadowCollisionWords_card, card_weightThreeShadowWords] at hincidence
  omega

end Quantum1435
