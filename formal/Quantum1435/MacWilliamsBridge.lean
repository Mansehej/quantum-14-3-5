import Quantum1435.CharacterOrthogonality
import Quantum1435.EvenBranch
import Mathlib.Tactic

/-!
# Semantic MacWilliams bridge

This file separates the symplectic MacWilliams argument into two parts.
Character orthogonality and all finite double-counting steps are proved here.
The remaining local obligation is `FixedWeightCharacterSum`: the character sum
over all ambient Paulis of a fixed weight is the corresponding quaternary
Krawtchouk value.
-/

namespace Quantum1435

noncomputable local instance {n : ℕ} {S : Submodule F₂ (Pauli n)} : Fintype S :=
  Fintype.ofFinite S

/-- The local coordinate identity which remains to be proved to complete the
symplectic MacWilliams transform. -/
def FixedWeightCharacterSum (n j : ℕ) : Prop :=
  ∀ v : Pauli n,
    (∑ w : Pauli n, if pauliWeight w = j then
      binarySign (symplecticForm n v w) else 0) =
        quantumKrawtchouk n j (pauliWeight v)
/-- The local identity at weight zero, where only the zero Pauli contributes. -/
theorem fixedWeightCharacterSum_zero (n : ℕ) : FixedWeightCharacterSum n 0 := by
  intro v
  simp [pauliWeight_eq_zero_iff, quantumKrawtchouk, binarySign]


/-- Regroup a sum over the actual vectors in a submodule by their Pauli
weight.  The range restriction is justified by the length bound on Pauli
weight. -/
theorem weighted_sum_weightDistribution {n : ℕ}
    (S : Submodule F₂ (Pauli n)) (f : ℕ → ℤ) :
    (∑ i ∈ Finset.range (n + 1), (weightDistribution S i : ℤ) * f i) =
      ∑ s : S, f (pauliWeight s.1) := by
  classical
  let words : Finset (Pauli n) := Finset.univ.filter fun v ↦ v ∈ S
  have hmaps : (words : Set (Pauli n)).MapsTo pauliWeight (Finset.range (n + 1)) := by
    intro v _
    rw [Finset.mem_coe, Finset.mem_range]
    exact Nat.lt_succ_of_le (pauliWeight_le_length v)
  calc
    (∑ i ∈ Finset.range (n + 1), (weightDistribution S i : ℤ) * f i) =
        ∑ i ∈ Finset.range (n + 1),
          ∑ v ∈ words with pauliWeight v = i, f (pauliWeight v) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [weightDistribution]
            rw [show (↑((Finset.univ.filter fun v : Pauli n ↦
                  v ∈ S ∧ pauliWeight v = i).card) : ℤ) =
                ∑ v ∈ Finset.univ.filter (fun v : Pauli n ↦
                  v ∈ S ∧ pauliWeight v = i), (1 : ℤ) by simp]
            rw [Finset.sum_mul]
            apply Finset.sum_congr
            · ext v
              simp [words]
            · intro v hv
              simp only [Finset.mem_filter] at hv
              rw [hv.2]
              simp
    _ = ∑ v ∈ words, f (pauliWeight v) :=
      Finset.sum_fiberwise_of_maps_to hmaps (fun v ↦ f (pauliWeight v))
    _ = ∑ s : S, f (pauliWeight s.1) := by
      apply Finset.sum_subtype words
      intro v
      simp [words]

/-- Character orthogonality evaluates the fixed-weight double count on the
ambient-vector side. -/
theorem fixedWeight_character_doubleCount {n j : ℕ}
    (S : Submodule F₂ (Pauli n)) :
    (∑ w : Pauli n, if pauliWeight w = j then
      ∑ s : S, binarySign (symplecticForm n s.1 w) else 0) =
      (Fintype.card S : ℤ) *
        (weightDistribution (symplecticNormalizer S) j : ℤ) := by
  classical
  calc
    (∑ w : Pauli n, if pauliWeight w = j then
        ∑ s : S, binarySign (symplecticForm n s.1 w) else 0) =
      ∑ w : Pauli n, if w ∈ symplecticNormalizer S ∧ pauliWeight w = j then
        (Fintype.card S : ℤ) else 0 := by
          apply Finset.sum_congr rfl
          intro w _
          by_cases hwWeight : pauliWeight w = j
          · by_cases hwNorm : w ∈ symplecticNormalizer S
            · rw [if_pos hwWeight,
                sum_binarySign_over_submodule_of_mem_normalizer S w hwNorm]
              simp [hwNorm, hwWeight]
            · rw [if_pos hwWeight,
                sum_binarySign_over_submodule_of_not_mem_normalizer S w hwNorm]
              simp [hwNorm]
          · simp [hwWeight]
    _ = (Fintype.card S : ℤ) *
        (weightDistribution (symplecticNormalizer S) j : ℤ) := by
      rw [weightDistribution]
      rw [← Finset.sum_filter]
      simp [mul_comm]

/-- Subject only to the local fixed-weight character identity, the actual
stabilizer and normalizer weight distributions satisfy one MacWilliams
coefficient equation. -/
theorem macWilliams_coefficient_of_fixedWeightCharacterSum {n j : ℕ}
    (S : Submodule F₂ (Pauli n)) (hlocal : FixedWeightCharacterSum n j) :
    (Fintype.card S : ℤ) *
        (weightDistribution (symplecticNormalizer S) j : ℤ) =
      ∑ i ∈ Finset.range (n + 1),
        (weightDistribution S i : ℤ) * quantumKrawtchouk n j i := by
  classical
  rw [← fixedWeight_character_doubleCount S]
  calc
    (∑ w : Pauli n, if pauliWeight w = j then
        ∑ s : S, binarySign (symplecticForm n s.1 w) else 0) =
      ∑ w : Pauli n, ∑ s : S, if pauliWeight w = j then
        binarySign (symplecticForm n s.1 w) else 0 := by
          apply Finset.sum_congr rfl
          intro w _
          by_cases hw : pauliWeight w = j <;> simp [hw]
    _ = ∑ s : S, ∑ w : Pauli n, if pauliWeight w = j then
        binarySign (symplecticForm n s.1 w) else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ s : S, quantumKrawtchouk n j (pauliWeight s.1) := by
      apply Finset.sum_congr rfl
      intro s _
      exact hlocal s.1
    _ = ∑ i ∈ Finset.range (n + 1),
        (weightDistribution S i : ℤ) * quantumKrawtchouk n j i :=
      (weighted_sum_weightDistribution S (quantumKrawtchouk n j)).symm

end Quantum1435
