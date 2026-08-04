import Quantum1435.ShadowCoset
import Quantum1435.WeightEnumerator
import Mathlib.Tactic

/-!
# The semantic shadow-enumerator partition

The normalizer of the even parity kernel is the disjoint union of the
original normalizer and the shadow.  This file proves the resulting
coefficientwise identity directly from the finite sets of Pauli vectors.
It is the semantic bridge behind the manuscript identity `E_j = B_j + S_j`.
-/

namespace Quantum1435

/-- At every weight, the even-kernel normalizer coefficient splits into the
original normalizer coefficient and the actual shadow coefficient. -/
theorem parityKernelNormalizer_weightDistribution_eq_add_shadow {n j : ℕ}
    (S : Submodule F₂ (Pauli n)) (hiso : IsTotallyIsotropic S) :
    weightDistribution
        (symplecticNormalizer (parityKernelAmbient S hiso)) j =
      weightDistribution (symplecticNormalizer S) j +
        shadowWeightDistribution S hiso j := by
  classical
  let ambientWords : Finset (Pauli n) :=
    Finset.univ.filter fun v ↦
      v ∈ symplecticNormalizer (parityKernelAmbient S hiso) ∧
        pauliWeight v = j
  have hsplit := ambientWords.card_filter_add_card_filter_not
    (fun v ↦ v ∈ symplecticNormalizer S)
  have hnormalizer :
      ambientWords.filter (fun v ↦ v ∈ symplecticNormalizer S) =
        Finset.univ.filter (fun v ↦
          v ∈ symplecticNormalizer S ∧ pauliWeight v = j) := by
    ext v
    simp only [ambientWords, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨-, hw⟩, hv⟩
      exact ⟨hv, hw⟩
    · rintro ⟨hv, hw⟩
      exact ⟨⟨symplecticNormalizer_le_parityKernelNormalizer S hiso hv, hw⟩, hv⟩
  have hshadow :
      ambientWords.filter (fun v ↦ v ∉ symplecticNormalizer S) =
        Finset.univ.filter (fun v ↦
          IsShadowWord S hiso v ∧ pauliWeight v = j) := by
    ext v
    simp only [ambientWords, IsShadowWord, Finset.mem_filter,
      Finset.mem_univ, true_and]
    tauto
  unfold weightDistribution shadowWeightDistribution
  change ambientWords.card = _
  rw [← hnormalizer, ← hshadow]
  exact hsplit.symm

/-- Below the logical distance, the normalizer term in the shadow partition
is exactly the stabilizer term.  Degenerate low-weight stabilizers are
therefore retained rather than silently excluded. -/
theorem parityKernelNormalizer_weightDistribution_eq_stabilizer_add_shadow
    {n d j : ℕ} (S : Submodule F₂ (Pauli n))
    (hiso : IsTotallyIsotropic S) (hd : HasLogicalDistanceAtLeast S d)
    (hj : j < d) :
    weightDistribution
        (symplecticNormalizer (parityKernelAmbient S hiso)) j =
      weightDistribution S j + shadowWeightDistribution S hiso j := by
  rw [parityKernelNormalizer_weightDistribution_eq_add_shadow,
    normalizer_weightDistribution_eq_of_lt_distance S hiso hd hj]

end Quantum1435
