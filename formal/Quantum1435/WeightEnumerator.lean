import Quantum1435.Statement
import Quantum1435.Parity
import Mathlib.FieldTheory.Finiteness
import Mathlib.InformationTheory.Hamming
import Mathlib.Tactic

/-!
# Semantic weight distributions

These definitions count actual Pauli vectors in a submodule.  They provide
the bridge from stabilizer distance and degeneracy to the low-weight
enumerator equalities; no serialized enumerator is involved.
-/

namespace Quantum1435

noncomputable local instance {n : ℕ} {S : Submodule F₂ (Pauli n)} : Fintype S :=
  Fintype.ofFinite S

/-- Number of words of Pauli weight `j` in `S`. -/
noncomputable def weightDistribution {n : ℕ} (S : Submodule F₂ (Pauli n)) (j : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter fun v : Pauli n ↦ v ∈ S ∧ pauliWeight v = j).card

/-- The project definition agrees with mathlib's Hamming norm. -/
theorem pauliWeight_eq_hammingNorm {n : ℕ} (v : Pauli n) :
    pauliWeight v = hammingNorm v := rfl

@[simp] theorem pauliWeight_eq_zero_iff {n : ℕ} {v : Pauli n} :
    pauliWeight v = 0 ↔ v = 0 := by
  exact hammingNorm_eq_zero

theorem pauliWeight_le_length {n : ℕ} (v : Pauli n) : pauliWeight v ≤ n := by
  simpa [pauliWeight_eq_hammingNorm] using (hammingNorm_le_card_fintype (x := v))

@[simp] theorem weightDistribution_zero {n : ℕ} (S : Submodule F₂ (Pauli n)) :
    weightDistribution S 0 = 1 := by
  classical
  unfold weightDistribution
  have hfilter :
      Finset.univ.filter (fun v : Pauli n ↦ v ∈ S ∧ pauliWeight v = 0) = {0} := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨-, hw⟩
      exact pauliWeight_eq_zero_iff.mp hw
    · intro hv
      subst v
      exact ⟨S.zero_mem, pauliWeight_eq_zero_iff.mpr rfl⟩
  rw [hfilter, Finset.card_singleton]

theorem weightDistribution_eq_zero_of_length_lt {n j : ℕ}
    (S : Submodule F₂ (Pauli n)) (h : n < j) : weightDistribution S j = 0 := by
  classical
  unfold weightDistribution
  rw [Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
  obtain ⟨-, hw⟩ := hv
  have hle := pauliWeight_le_length v
  omega

/-- The total of all length-admissible weight coefficients is the number of
vectors in the submodule. -/
theorem sum_weightDistribution {n : ℕ} (S : Submodule F₂ (Pauli n)) :
    (∑ j ∈ Finset.range (n + 1), weightDistribution S j) = Fintype.card S := by
  classical
  let words : Finset (Pauli n) := Finset.univ.filter fun v ↦ v ∈ S
  have hmaps : (words : Set (Pauli n)).MapsTo pauliWeight (Finset.range (n + 1)) := by
    intro v _
    rw [Finset.mem_coe, Finset.mem_range]
    exact Nat.lt_succ_of_le (pauliWeight_le_length v)
  have hfiber := Finset.card_eq_sum_card_fiberwise
    (f := pauliWeight) (s := words) (t := Finset.range (n + 1)) hmaps
  have hwords : words.card = Fintype.card S := by
    simpa [words] using (Fintype.card_subtype (fun v : Pauli n ↦ v ∈ S)).symm
  rw [← hwords, hfiber]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [weightDistribution, words, Finset.filter_filter]

/-- An `r`-dimensional binary subspace has exactly `2^r` vectors. -/
theorem submodule_card_eq_two_pow_finrank {n : ℕ}
    (S : Submodule F₂ (Pauli n)) :
    Fintype.card S = 2 ^ Module.finrank F₂ S := by
  simpa using (Module.card_eq_pow_finrank (K := F₂) (V := S))

theorem submodule_card_of_finrank_eleven {n : ℕ}
    (S : Submodule F₂ (Pauli n)) (h : Module.finrank F₂ S = 11) :
    Fintype.card S = 2048 := by
  rw [submodule_card_eq_two_pow_finrank, h]
  norm_num

/-- All-evenness makes every odd stabilizer coefficient vanish. -/
theorem weightDistribution_eq_zero_of_allEven_of_odd {n j : ℕ}
    (S : Submodule F₂ (Pauli n)) (heven : IsAllEven S) (hj : Odd j) :
    weightDistribution S j = 0 := by
  classical
  unfold weightDistribution
  rw [Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
  obtain ⟨hvS, hw⟩ := hv
  have hp := heven v hvS
  rw [pauliParity_eq_weight_cast, hw] at hp
  have hdvd : 2 ∣ j := (ZMod.natCast_eq_zero_iff j 2).mp hp
  exact hj.not_two_dvd_nat hdvd

/-- Isotropy and distance identify stabilizer and normalizer coefficients
strictly below the logical distance.  This permits degeneracy: both sides may
contain low-weight stabilizer words. -/
theorem normalizer_weightDistribution_eq_of_lt_distance {n d j : ℕ}
    (S : Submodule F₂ (Pauli n)) (hiso : IsTotallyIsotropic S)
    (hd : HasLogicalDistanceAtLeast S d) (hj : j < d) :
    weightDistribution (symplecticNormalizer S) j = weightDistribution S j := by
  classical
  unfold weightDistribution
  apply congrArg Finset.card
  ext v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hvN, hw⟩
    have hvS : v ∈ S := by
      by_contra hvS
      have hlow := hd v ⟨hvN, hvS⟩
      omega
    exact ⟨hvS, hw⟩
  · rintro ⟨hvS, hw⟩
    exact ⟨hiso.le_normalizer hvS, hw⟩

end Quantum1435
