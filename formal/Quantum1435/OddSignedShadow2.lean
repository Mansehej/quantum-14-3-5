import Quantum1435.ShadowEnumeratorBridge
import Mathlib.Tactic

/-!
# The literal signed-shadow row at weight two

This row is isolated so its expanded Krawtchouk normalization compiles in a
separate Lean process from the weight-three and weight-four rows.
-/

noncomputable section

namespace Quantum1435

/-- The weight-two signed-shadow identity obtained from the parity-kernel and
stabilizer MacWilliams transforms of an odd candidate. -/
theorem oddSignedShadow2
    (S : Submodule F₂ (Pauli 14)) (hcandidate : IsCandidate1435 S)
    (hodd : ContainsOddWord S) :
    -663 * (weightDistribution S 1 : ℤ) +
      523 * weightDistribution S 2 - 399 * weightDistribution S 3 +
      291 * weightDistribution S 4 - 199 * weightDistribution S 5 +
      123 * weightDistribution S 6 - 63 * weightDistribution S 7 +
      19 * weightDistribution S 8 + 9 * weightDistribution S 9 -
      21 * weightDistribution S 10 + 17 * weightDistribution S 11 +
      3 * weightDistribution S 12 - 39 * weightDistribution S 13 +
      91 * weightDistribution S 14 -
      2048 * shadowWeightDistribution S hcandidate.2.1 2 = -819 := by
  let K := parityKernelAmbient S hcandidate.2.1
  have hdimK : Module.finrank F₂ K = 10 :=
    parityKernelAmbient_finrank
      S hcandidate.2.1 hcandidate.1 hodd
  have hKEven : IsAllEven K :=
    parityKernelAmbient_isAllEven S hcandidate.2.1
  have h1 := weightDistribution_eq_zero_of_allEven_of_odd
    K hKEven (j := 1) (by decide)
  have h3 := weightDistribution_eq_zero_of_allEven_of_odd
    K hKEven (j := 3) (by decide)
  have h5 := weightDistribution_eq_zero_of_allEven_of_odd
    K hKEven (j := 5) (by decide)
  have h7 := weightDistribution_eq_zero_of_allEven_of_odd
    K hKEven (j := 7) (by decide)
  have h9 := weightDistribution_eq_zero_of_allEven_of_odd
    K hKEven (j := 9) (by decide)
  have h11 := weightDistribution_eq_zero_of_allEven_of_odd
    K hKEven (j := 11) (by decide)
  have h13 := weightDistribution_eq_zero_of_allEven_of_odd
    K hKEven (j := 13) (by decide)
  have h2 := weightDistribution_parityKernelAmbient_eq_of_even
    S hcandidate.2.1 (j := 2) (by decide)
  have h4 := weightDistribution_parityKernelAmbient_eq_of_even
    S hcandidate.2.1 (j := 4) (by decide)
  have h6 := weightDistribution_parityKernelAmbient_eq_of_even
    S hcandidate.2.1 (j := 6) (by decide)
  have h8 := weightDistribution_parityKernelAmbient_eq_of_even
    S hcandidate.2.1 (j := 8) (by decide)
  have h10 := weightDistribution_parityKernelAmbient_eq_of_even
    S hcandidate.2.1 (j := 10) (by decide)
  have h12 := weightDistribution_parityKernelAmbient_eq_of_even
    S hcandidate.2.1 (j := 12) (by decide)
  have h14 := weightDistribution_parityKernelAmbient_eq_of_even
    S hcandidate.2.1 (j := 14) (by decide)
  have hpartition :
      weightDistribution (symplecticNormalizer K) 2 =
        weightDistribution S 2 +
          shadowWeightDistribution S hcandidate.2.1 2 := by
    simpa [K] using
      parityKernelNormalizer_weightDistribution_eq_stabilizer_add_shadow
        S hcandidate.2.1 hcandidate.2.2 (j := 2) (by omega)
  have hK := macWilliams_coefficient_of_fixedWeightCharacterSum
    K fixedWeightCharacterSum_14_2
  rw [submodule_card_eq_two_pow_finrank, hdimK] at hK
  norm_num [Finset.sum_range_succ, quantumKrawtchouk, Nat.choose] at hK
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12,
    h13, h14, hpartition] at hK
  norm_num at hK
  have hS := oddMacWilliams2 S hcandidate
  linear_combination -hS - 2 * hK

end Quantum1435
