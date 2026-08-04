import Quantum1435.WeightEnumerator
import Quantum1435.CertificateChecker
import Mathlib.Tactic

/-!
# Semantic elimination of the all-even branch

This module connects the weight distribution of an actual stabilizer candidate
to the checked all-even integer certificate.  Its sole remaining mathematical
hypothesis is the symplectic MacWilliams identity in weights one through four.
-/

namespace Quantum1435

/-- The seven nonzero, even-weight coefficients of an actual length-14
stabilizer weight distribution. -/
noncomputable def evenWeightVector (S : Submodule F₂ (Pauli 14)) : Fin 7 → ℕ := ![
  weightDistribution S 2,
  weightDistribution S 4,
  weightDistribution S 6,
  weightDistribution S 8,
  weightDistribution S 10,
  weightDistribution S 12,
  weightDistribution S 14
]

/-- The four low-weight coefficient identities needed from the symplectic
MacWilliams transform.  This proposition is semantic: both sides count the
weight distributions of the actual submodules `S` and `Sᵖ`. -/
def HasMacWilliamsRowsOneToFour (S : Submodule F₂ (Pauli 14)) : Prop :=
  ∀ j : Fin 4,
    (∑ i ∈ Finset.range 15,
      quantumKrawtchouk 14 (j.1 + 1) i * (weightDistribution S i : ℤ)) =
      2048 * (weightDistribution (symplecticNormalizer S) (j.1 + 1) : ℤ)

private theorem allEven_totalEquation_holds
    (S : Submodule F₂ (Pauli 14))
    (hdim : Module.finrank F₂ S = 11)
    (heven : IsAllEven S) :
    evenTotalEquation.Holds (fun i ↦ (evenWeightVector S i : ℤ)) := by
  have hsum := sum_weightDistribution S
  rw [submodule_card_of_finrank_eleven S hdim] at hsum
  have h1 := weightDistribution_eq_zero_of_allEven_of_odd S heven (j := 1) (by decide)
  have h3 := weightDistribution_eq_zero_of_allEven_of_odd S heven (j := 3) (by decide)
  have h5 := weightDistribution_eq_zero_of_allEven_of_odd S heven (j := 5) (by decide)
  have h7 := weightDistribution_eq_zero_of_allEven_of_odd S heven (j := 7) (by decide)
  have h9 := weightDistribution_eq_zero_of_allEven_of_odd S heven (j := 9) (by decide)
  have h11 := weightDistribution_eq_zero_of_allEven_of_odd S heven (j := 11) (by decide)
  have h13 := weightDistribution_eq_zero_of_allEven_of_odd S heven (j := 13) (by decide)
  norm_num [Finset.sum_range_succ, h1, h3, h5, h7, h9, h11, h13,
    LinearEquation.Holds, evenTotalEquation, evenWeightVector,
    Fin.sum_univ_succ] at hsum ⊢
  omega

set_option maxHeartbeats 1000000 in
private theorem allEven_krawtchoukEquations_hold
    (S : Submodule F₂ (Pauli 14))
    (hiso : IsTotallyIsotropic S)
    (hdistance : HasLogicalDistanceAtLeast S 5)
    (heven : IsAllEven S)
    (hMW : HasMacWilliamsRowsOneToFour S) :
    ∀ j : Fin 4,
      (evenKrawtchoukEquation (j.1 + 1)).Holds
        (fun i ↦ (evenWeightVector S i : ℤ)) := by
  have h1 := weightDistribution_eq_zero_of_allEven_of_odd S heven (j := 1) (by decide)
  have h3 := weightDistribution_eq_zero_of_allEven_of_odd S heven (j := 3) (by decide)
  have h5 := weightDistribution_eq_zero_of_allEven_of_odd S heven (j := 5) (by decide)
  have h7 := weightDistribution_eq_zero_of_allEven_of_odd S heven (j := 7) (by decide)
  have h9 := weightDistribution_eq_zero_of_allEven_of_odd S heven (j := 9) (by decide)
  have h11 := weightDistribution_eq_zero_of_allEven_of_odd S heven (j := 11) (by decide)
  have h13 := weightDistribution_eq_zero_of_allEven_of_odd S heven (j := 13) (by decide)
  intro j
  fin_cases j
  · have h := hMW (0 : Fin 4)
    norm_num at h
    rw [normalizer_weightDistribution_eq_of_lt_distance S hiso hdistance (j := 1) (by omega)] at h
    norm_num [Finset.sum_range_succ, h1, h3, h5, h7, h9, h11, h13,
      quantumKrawtchouk, Nat.choose, LinearEquation.Holds, evenKrawtchoukEquation,
      evenDistanceCoefficient, evenWeightVector, Fin.sum_univ_succ] at h ⊢
    omega
  · have h := hMW (1 : Fin 4)
    norm_num at h
    rw [normalizer_weightDistribution_eq_of_lt_distance S hiso hdistance (j := 2) (by omega)] at h
    norm_num [Finset.sum_range_succ, h1, h3, h5, h7, h9, h11, h13,
      quantumKrawtchouk, Nat.choose, LinearEquation.Holds, evenKrawtchoukEquation,
      evenDistanceCoefficient, evenWeightVector, Fin.sum_univ_succ] at h ⊢
    omega
  · have h := hMW (2 : Fin 4)
    norm_num at h
    rw [normalizer_weightDistribution_eq_of_lt_distance S hiso hdistance (j := 3) (by omega)] at h
    norm_num [Finset.sum_range_succ, h1, h3, h5, h7, h9, h11, h13,
      quantumKrawtchouk, Nat.choose, LinearEquation.Holds, evenKrawtchoukEquation,
      evenDistanceCoefficient, evenWeightVector, Fin.sum_univ_succ] at h ⊢
    omega
  · have h := hMW (3 : Fin 4)
    norm_num at h
    rw [normalizer_weightDistribution_eq_of_lt_distance S hiso hdistance (j := 4) (by omega)] at h
    norm_num [Finset.sum_range_succ, h1, h3, h5, h7, h9, h11, h13,
      quantumKrawtchouk, Nat.choose, LinearEquation.Holds, evenKrawtchoukEquation,
      evenDistanceCoefficient, evenWeightVector, Fin.sum_univ_succ] at h ⊢
    omega

/-- An actual all-even candidate satisfying the four low MacWilliams rows
satisfies every input row of the checked finite certificate. -/
theorem allEven_candidate_satisfies_evenEquations
    (S : Submodule F₂ (Pauli 14))
    (hcandidate : IsCandidate1435 S)
    (heven : IsAllEven S)
    (hMW : HasMacWilliamsRowsOneToFour S) :
    ∀ j, (evenEquations j).Holds (fun i ↦ (evenWeightVector S i : ℤ)) := by
  intro j
  fin_cases j
  · exact allEven_totalEquation_holds S hcandidate.1 heven
  · exact allEven_krawtchoukEquations_hold S hcandidate.2.1 hcandidate.2.2 heven hMW 0
  · exact allEven_krawtchoukEquations_hold S hcandidate.2.1 hcandidate.2.2 heven hMW 1
  · exact allEven_krawtchoukEquations_hold S hcandidate.2.1 hcandidate.2.2 heven hMW 2
  · exact allEven_krawtchoukEquations_hold S hcandidate.2.1 hcandidate.2.2 heven hMW 3

/-- Semantic elimination of the all-even branch, conditional only on the four
low-weight symplectic MacWilliams coefficient identities. -/
theorem no_allEven_candidate_of_macWilliamsRows
    (S : Submodule F₂ (Pauli 14))
    (hcandidate : IsCandidate1435 S)
    (heven : IsAllEven S)
    (hMW : HasMacWilliamsRowsOneToFour S) : False :=
  noEvenEnumerator (evenWeightVector S)
    (allEven_candidate_satisfies_evenEquations S hcandidate heven hMW)

end Quantum1435
