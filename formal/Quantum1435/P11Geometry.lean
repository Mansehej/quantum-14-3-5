import Quantum1435.WeightEnumerator
import Mathlib.InformationTheory.Hamming
import Mathlib.Tactic

/-!
# The geometric elimination in the `(A₁,A₂,A₄) = (0,1,1)` profile

This file proves the load-bearing geometric fact used in the `p11` branch.
If a binary isotropic stabilizer has a unique word of weight two and a unique
word of weight four, their sum is a stabilizer word of weight six.

The weight calculation is expressed without choosing coordinates.  The two
Hamming triangle inequalities put the weight of the sum between two and six;
the quadratic-refinement identity and commutation make that weight even.
Uniqueness then excludes weights two and four.
-/

namespace Quantum1435

/-- A coefficient equal to one really supplies a unique word of that weight. -/
theorem existsUnique_of_weightDistribution_eq_one {n j : ℕ}
    (S : Submodule F₂ (Pauli n)) (h : weightDistribution S j = 1) :
    ∃! v : Pauli n, v ∈ S ∧ pauliWeight v = j := by
  classical
  let words : Finset (Pauli n) :=
    Finset.univ.filter fun v : Pauli n ↦ v ∈ S ∧ pauliWeight v = j
  have hcard : words.card = 1 := by
    simpa [words, weightDistribution] using h
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hcard
  refine ⟨v, ?_, ?_⟩
  · have : v ∈ words := by simp [hv]
    simpa [words] using this
  · intro w hw
    have : w ∈ words := by simpa [words] using hw
    simpa [hv] using this

/-- Hamming weight is subadditive for binary Pauli vectors. -/
theorem pauliWeight_add_le {n : ℕ} (u v : Pauli n) :
    pauliWeight (u + v) ≤ pauliWeight u + pauliWeight v := by
  have h := hammingDist_triangle (0 : Pauli n) u (u + v)
  simpa [hammingDist, pauliWeight, ne_comm] using h

/-- The reverse triangle inequality in the form needed below. -/
theorem pauliWeight_le_add_weight_add {n : ℕ} (u v : Pauli n) :
    pauliWeight v ≤ pauliWeight (u + v) + pauliWeight u := by
  have h := hammingDist_triangle (0 : Pauli n) (u + v) v
  simpa [hammingDist, pauliWeight, ne_comm, add_comm, add_left_comm, add_assoc] using h

/-- Commuting words of weights two and four have a sum of weight two, four,
or six.  This packages the support/label combinatorics in invariant Hamming
form: triangle inequalities give the bounds and commutation gives parity. -/
theorem pauliWeight_add_mem_two_four_six {n : ℕ} {u v : Pauli n}
    (hu : pauliWeight u = 2) (hv : pauliWeight v = 4)
    (hcomm : symplecticForm n u v = 0) :
    pauliWeight (u + v) = 2 ∨ pauliWeight (u + v) = 4 ∨
      pauliWeight (u + v) = 6 := by
  have hupper := pauliWeight_add_le u v
  have hlower := pauliWeight_le_add_weight_add u v
  rw [hu, hv] at hupper hlower
  have hparity : (pauliWeight (u + v) : F₂) = 0 := by
    rw [← pauliParity_eq_weight_cast, pauliParity_add, hcomm,
      pauliParity_eq_weight_cast, pauliParity_eq_weight_cast, hu, hv]
    decide
  have heven : 2 ∣ pauliWeight (u + v) :=
    (ZMod.natCast_eq_zero_iff (pauliWeight (u + v)) 2).mp hparity
  omega

/-- In the manuscript's `p11` profile, the unique weight-two and weight-four
stabilizers force a weight-six stabilizer.  The `A₁ = 0` hypothesis is kept in
the statement to match that profile, although the geometric implication is
strictly stronger and does not need it. -/
theorem p11_weightDistribution_six_pos {n : ℕ}
    (S : Submodule F₂ (Pauli n)) (hiso : IsTotallyIsotropic S)
    (_hA1 : weightDistribution S 1 = 0)
    (hA2 : weightDistribution S 2 = 1)
    (hA4 : weightDistribution S 4 = 1) :
    1 ≤ weightDistribution S 6 := by
  classical
  obtain ⟨u, hu, hu_unique⟩ := existsUnique_of_weightDistribution_eq_one S hA2
  obtain ⟨v, hv, hv_unique⟩ := existsUnique_of_weightDistribution_eq_one S hA4
  have hweights := pauliWeight_add_mem_two_four_six hu.2 hv.2 (hiso hu.1 hv.1)
  have huvS : u + v ∈ S := S.add_mem hu.1 hv.1
  have huvWeight : pauliWeight (u + v) = 6 := by
    rcases hweights with h2 | h4 | h6
    · have heq : u + v = u := hu_unique (u + v) ⟨huvS, h2⟩
      have hvzero : v = 0 := by
        apply add_left_cancel (a := u)
        simpa [add_assoc] using heq
      have : pauliWeight v = 0 := pauliWeight_eq_zero_iff.mpr hvzero
      omega
    · have heq : u + v = v := hv_unique (u + v) ⟨huvS, h4⟩
      have huzero : u = 0 := by
        apply add_right_cancel (b := v)
        simpa [add_assoc] using heq
      have : pauliWeight u = 0 := pauliWeight_eq_zero_iff.mpr huzero
      omega
    · exact h6
  unfold weightDistribution
  refine Finset.one_le_card.mpr ⟨u + v, ?_⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨huvS, huvWeight⟩⟩

end Quantum1435
