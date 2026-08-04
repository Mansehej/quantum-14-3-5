import Quantum1435.P03ShadowVertices
import Quantum1435.P03NormalForms
import Mathlib.Tactic

/-!
# Semantic pair geometry for the p03 shadow

This file proves the pairwise facts needed to turn the twenty-four actual
weight-three shadow vectors into the manuscript's collision graph. A shared
bin is represented invariantly by a positive `p03CategoryC` count.

The argument is valid for degenerate codes. The sum of two shadow vectors
first lands in the symplectic normalizer. Only the logical-distance
hypothesis can then move a sufficiently low-weight sum into the stabilizer;
the stated zero stabilizer coefficients exclude the remaining low weights.
-/

noncomputable section

namespace Quantum1435

/-- If the weight-`j` coefficient of a submodule vanishes, no vector of that
weight belongs to the submodule. -/
theorem not_mem_of_weightDistribution_eq_zero {n j : ℕ}
    (S : Submodule F₂ (Pauli n))
    (hzero : weightDistribution S j = 0)
    {v : Pauli n} (hweight : pauliWeight v = j) :
    v ∉ S := by
  classical
  intro hvS
  have hcard :
      (Finset.univ.filter fun w : Pauli n ↦
        w ∈ S ∧ pauliWeight w = j).card = 0 := by
    simpa [weightDistribution] using hzero
  have hempty :
      Finset.univ.filter (fun w : Pauli n ↦
        w ∈ S ∧ pauliWeight w = j) = ∅ :=
    Finset.card_eq_zero.mp hcard
  have hmem :
      v ∈ Finset.univ.filter (fun w : Pauli n ↦
        w ∈ S ∧ pauliWeight w = j) := by
    simp [hvS, hweight]
  rw [hempty] at hmem
  simp at hmem

/-- In the binary Pauli space, a zero-weight sum means that the two summands
are equal. -/
theorem eq_of_pauliWeight_add_eq_zero {n : ℕ} {u v : Pauli n}
    (hweight : pauliWeight (u + v) = 0) :
    u = v := by
  have hzero : u + v = 0 := pauliWeight_eq_zero_iff.mp hweight
  funext i
  apply (localPauli_add_eq_zero_iff (u i) (v i)).mp
  have hi := congrFun hzero i
  simpa only [Pi.add_apply, Pi.zero_apply] using hi

/-- Distinct actual weight-three shadow words share at most one nonzero
coordinate/label bin when `A₁ = A₂ = 0`.

If two matching bins existed, category arithmetic would give a sum of weight
at most two. The sum is in the normalizer because both endpoints are shadow
words. Distance at least five therefore puts it in `S`; the two vanishing
coefficients and distinctness exclude weights two, one, and zero. -/
theorem p03CategoryC_le_one_of_distinct_weightThreeShadowWords
    (S : Submodule F₂ (Pauli 14))
    (hcandidate : IsCandidate1435 S)
    (hA1 : weightDistribution S 1 = 0)
    (hA2 : weightDistribution S 2 = 0)
    {u v : Pauli 14}
    (hu : u ∈ weightThreeShadowWords S hcandidate.2.1)
    (hv : v ∈ weightThreeShadowWords S hcandidate.2.1)
    (huv : u ≠ v) :
    p03CategoryC u v ≤ 1 := by
  have huData :=
    (mem_weightThreeShadowWords S hcandidate.2.1 u).mp hu
  have hvData :=
    (mem_weightThreeShadowWords S hcandidate.2.1 v).mp hv
  have hU := pauliWeight_eq_categories_ACD u v
  have hV := pauliWeight_eq_categories_BCD u v
  have hSum := pauliWeight_add_eq_categories_ABD u v
  rw [huData.2] at hU
  rw [hvData.2] at hV
  by_contra hnot
  have hC : 2 ≤ p03CategoryC u v := by omega
  have hsumle : pauliWeight (u + v) ≤ 2 := by omega
  have hnormalizer : u + v ∈ symplecticNormalizer S :=
    shadowWord_add_shadowWord_mem_normalizer huData.1 hvData.1
  have hsumS : u + v ∈ S := by
    by_contra hnotS
    have hdistance : 5 ≤ pauliWeight (u + v) :=
      hcandidate.2.2 (u + v) ⟨hnormalizer, hnotS⟩
    omega
  have hneZero : pauliWeight (u + v) ≠ 0 := by
    intro hzero
    exact huv (eq_of_pauliWeight_add_eq_zero hzero)
  have hneOne : pauliWeight (u + v) ≠ 1 := by
    intro hone
    exact (not_mem_of_weightDistribution_eq_zero S hA1 hone) hsumS
  have hneTwo : pauliWeight (u + v) ≠ 2 := by
    intro htwo
    exact (not_mem_of_weightDistribution_eq_zero S hA2 htwo) hsumS
  omega

/-- Distinct actual weight-three shadow words which share a nonzero
coordinate/label bin have a weight-four sum in the stabilizer when
`A₁ = A₂ = A₃ = 0`.

One matching bin makes the normalizer sum have weight at most four, so the
distance hypothesis puts it in `S`. Distinctness excludes weight zero and
the three vanishing coefficients exclude weights one through three. -/
theorem add_mem_stabilizer_and_weight_four_of_matching_shadowWords
    (S : Submodule F₂ (Pauli 14))
    (hcandidate : IsCandidate1435 S)
    (hA1 : weightDistribution S 1 = 0)
    (hA2 : weightDistribution S 2 = 0)
    (hA3 : weightDistribution S 3 = 0)
    {u v : Pauli 14}
    (hu : u ∈ weightThreeShadowWords S hcandidate.2.1)
    (hv : v ∈ weightThreeShadowWords S hcandidate.2.1)
    (huv : u ≠ v)
    (hmatching : 0 < p03CategoryC u v) :
    u + v ∈ S ∧ pauliWeight (u + v) = 4 := by
  have huData :=
    (mem_weightThreeShadowWords S hcandidate.2.1 u).mp hu
  have hvData :=
    (mem_weightThreeShadowWords S hcandidate.2.1 v).mp hv
  have hU := pauliWeight_eq_categories_ACD u v
  have hV := pauliWeight_eq_categories_BCD u v
  have hSum := pauliWeight_add_eq_categories_ABD u v
  rw [huData.2] at hU
  rw [hvData.2] at hV
  have hsumle : pauliWeight (u + v) ≤ 4 := by omega
  have hnormalizer : u + v ∈ symplecticNormalizer S :=
    shadowWord_add_shadowWord_mem_normalizer huData.1 hvData.1
  have hsumS : u + v ∈ S := by
    by_contra hnotS
    have hdistance : 5 ≤ pauliWeight (u + v) :=
      hcandidate.2.2 (u + v) ⟨hnormalizer, hnotS⟩
    omega
  have hneZero : pauliWeight (u + v) ≠ 0 := by
    intro hzero
    exact huv (eq_of_pauliWeight_add_eq_zero hzero)
  have hneOne : pauliWeight (u + v) ≠ 1 := by
    intro hone
    exact (not_mem_of_weightDistribution_eq_zero S hA1 hone) hsumS
  have hneTwo : pauliWeight (u + v) ≠ 2 := by
    intro htwo
    exact (not_mem_of_weightDistribution_eq_zero S hA2 htwo) hsumS
  have hneThree : pauliWeight (u + v) ≠ 3 := by
    intro hthree
    exact (not_mem_of_weightDistribution_eq_zero S hA3 hthree) hsumS
  exact ⟨hsumS, by omega⟩

end Quantum1435
