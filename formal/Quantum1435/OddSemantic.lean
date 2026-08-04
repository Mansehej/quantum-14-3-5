import Quantum1435.LocalKrawtchouk
import Quantum1435.OddIdentityCertificate
import Mathlib.Tactic

/-!
# Semantic source rows for the odd branch

This module connects an actual length-14 stabilizer candidate in the odd
parity branch to the arithmetic source rows for Identity 51.  The ordinary
MacWilliams rows follow from the proved local character identity.  Applying
the same identity to the parity kernel constructs the auxiliary `E`
enumerator used in the shadow equations.  All source rows therefore refer to
actual submodules and weight distributions.
-/

namespace Quantum1435

noncomputable local instance {n : ℕ} {S : Submodule F₂ (Pauli n)} : Fintype S :=
  Fintype.ofFinite S

/-- The even-weight kernel of the parity functional, transported back into
the ambient Pauli space. -/
noncomputable def parityKernelAmbient {n : ℕ}
    (S : Submodule F₂ (Pauli n)) (hiso : IsTotallyIsotropic S) :
    Submodule F₂ (Pauli n) :=
  (LinearMap.ker (parityLinearMap S hiso)).map S.subtype

theorem mem_parityKernelAmbient_iff {n : ℕ}
    (S : Submodule F₂ (Pauli n)) (hiso : IsTotallyIsotropic S)
    (v : Pauli n) :
    v ∈ parityKernelAmbient S hiso ↔ v ∈ S ∧ pauliParity v = 0 := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, hx⟩
  · rintro ⟨hvS, hvEven⟩
    exact ⟨⟨v, hvS⟩, hvEven, rfl⟩


/-- Transporting the parity kernel through the subtype inclusion preserves
its dimension. -/
theorem parityKernelAmbient_finrank {n : ℕ}
    (S : Submodule F₂ (Pauli n)) (hiso : IsTotallyIsotropic S)
    (hdim : Module.finrank F₂ S = 11) (hodd : ContainsOddWord S) :
    Module.finrank F₂ (parityKernelAmbient S hiso) = 10 := by
  rw [parityKernelAmbient, Submodule.finrank_map_subtype_eq]
  exact parityKernel_finrank S hiso hdim hodd

/-- Every vector in the transported parity kernel has even Pauli weight. -/
theorem parityKernelAmbient_isAllEven {n : ℕ}
    (S : Submodule F₂ (Pauli n)) (hiso : IsTotallyIsotropic S) :
    IsAllEven (parityKernelAmbient S hiso) := by
  intro v hv
  exact (mem_parityKernelAmbient_iff S hiso v).mp hv |>.2

/-- At an even weight, the parity-kernel coefficient is exactly the
corresponding coefficient of the original stabilizer. -/
theorem weightDistribution_parityKernelAmbient_eq_of_even {n j : ℕ}
    (S : Submodule F₂ (Pauli n)) (hiso : IsTotallyIsotropic S)
    (hj : Even j) :
    weightDistribution (parityKernelAmbient S hiso) j =
      weightDistribution S j := by
  classical
  unfold weightDistribution
  apply congrArg Finset.card
  ext v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hvKernel, hw⟩
    exact ⟨(mem_parityKernelAmbient_iff S hiso v).mp hvKernel |>.1, hw⟩
  · rintro ⟨hvS, hw⟩
    have hvParity : pauliParity v = 0 := by
      rw [pauliParity_eq_weight_cast, hw]
      exact (ZMod.natCast_eq_zero_iff j 2).mpr hj.two_dvd
    exact ⟨(mem_parityKernelAmbient_iff S hiso v).mpr ⟨hvS, hvParity⟩, hw⟩

/-- In the odd branch there are `2^10 - 1 = 1023` nonzero even-weight
stabilizer vectors. -/
theorem oddBranch_evenWeightTotal
    (S : Submodule F₂ (Pauli 14)) (hiso : IsTotallyIsotropic S)
    (hdim : Module.finrank F₂ S = 11) (hodd : ContainsOddWord S) :
    weightDistribution S 2 + weightDistribution S 4 +
      weightDistribution S 6 + weightDistribution S 8 +
      weightDistribution S 10 + weightDistribution S 12 +
      weightDistribution S 14 = 1023 := by
  let K := parityKernelAmbient S hiso
  have hdimK : Module.finrank F₂ K = 10 :=
    parityKernelAmbient_finrank S hiso hdim hodd
  have hsum := sum_weightDistribution K
  rw [submodule_card_eq_two_pow_finrank, hdimK] at hsum
  have hKEven : IsAllEven K := parityKernelAmbient_isAllEven S hiso
  have h1 := weightDistribution_eq_zero_of_allEven_of_odd K hKEven (j := 1) (by decide)
  have h3 := weightDistribution_eq_zero_of_allEven_of_odd K hKEven (j := 3) (by decide)
  have h5 := weightDistribution_eq_zero_of_allEven_of_odd K hKEven (j := 5) (by decide)
  have h7 := weightDistribution_eq_zero_of_allEven_of_odd K hKEven (j := 7) (by decide)
  have h9 := weightDistribution_eq_zero_of_allEven_of_odd K hKEven (j := 9) (by decide)
  have h11 := weightDistribution_eq_zero_of_allEven_of_odd K hKEven (j := 11) (by decide)
  have h13 := weightDistribution_eq_zero_of_allEven_of_odd K hKEven (j := 13) (by decide)
  have h2 := weightDistribution_parityKernelAmbient_eq_of_even S hiso (j := 2) (by decide)
  have h4 := weightDistribution_parityKernelAmbient_eq_of_even S hiso (j := 4) (by decide)
  have h6 := weightDistribution_parityKernelAmbient_eq_of_even S hiso (j := 6) (by decide)
  have h8 := weightDistribution_parityKernelAmbient_eq_of_even S hiso (j := 8) (by decide)
  have h10 := weightDistribution_parityKernelAmbient_eq_of_even S hiso (j := 10) (by decide)
  have h12 := weightDistribution_parityKernelAmbient_eq_of_even S hiso (j := 12) (by decide)
  have h14 := weightDistribution_parityKernelAmbient_eq_of_even S hiso (j := 14) (by decide)
  norm_num [Finset.sum_range_succ] at hsum
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14] at hsum
  norm_num at hsum
  omega


/-- An 11-dimensional stabilizer has 2047 nonzero vectors, grouped here by
their actual Pauli weights. -/
theorem candidate_nonzeroWeightTotal
    (S : Submodule F₂ (Pauli 14)) (hdim : Module.finrank F₂ S = 11) :
    (weightDistribution S 1 : ℤ) + weightDistribution S 2 +
      weightDistribution S 3 + weightDistribution S 4 +
      weightDistribution S 5 + weightDistribution S 6 +
      weightDistribution S 7 + weightDistribution S 8 +
      weightDistribution S 9 + weightDistribution S 10 +
      weightDistribution S 11 + weightDistribution S 12 +
      weightDistribution S 13 + weightDistribution S 14 = 2047 := by
  have hsum := sum_weightDistribution S
  rw [submodule_card_of_finrank_eleven S hdim] at hsum
  norm_num [Finset.sum_range_succ] at hsum
  have hnat :
      weightDistribution S 1 + weightDistribution S 2 + weightDistribution S 3 +
        weightDistribution S 4 + weightDistribution S 5 + weightDistribution S 6 +
        weightDistribution S 7 + weightDistribution S 8 + weightDistribution S 9 +
        weightDistribution S 10 + weightDistribution S 11 + weightDistribution S 12 +
        weightDistribution S 13 + weightDistribution S 14 = 2047 := by omega
  exact_mod_cast hnat

/-- The weight-one source row obtained from a semantic MacWilliams identity
and the candidate's distance condition. -/
theorem oddMacWilliams1
    (S : Submodule F₂ (Pauli 14)) (hcandidate : IsCandidate1435 S) :
    -2010 * (weightDistribution S 1 : ℤ) +
      34 * weightDistribution S 2 + 30 * weightDistribution S 3 +
      26 * weightDistribution S 4 + 22 * weightDistribution S 5 +
      18 * weightDistribution S 6 + 14 * weightDistribution S 7 +
      10 * weightDistribution S 8 + 6 * weightDistribution S 9 +
      2 * weightDistribution S 10 - 2 * weightDistribution S 11 -
      6 * weightDistribution S 12 - 10 * weightDistribution S 13 -
      14 * weightDistribution S 14 = -42 := by
  have h := macWilliams_coefficient_of_fixedWeightCharacterSum S
    fixedWeightCharacterSum_14_1
  rw [submodule_card_of_finrank_eleven S hcandidate.1] at h
  rw [normalizer_weightDistribution_eq_of_lt_distance S hcandidate.2.1
    hcandidate.2.2 (j := 1) (by omega)] at h
  norm_num [Finset.sum_range_succ, quantumKrawtchouk, Nat.choose] at h
  omega

/-- The weight-two source row obtained from the semantic MacWilliams
identity. -/
theorem oddMacWilliams2
    (S : Submodule F₂ (Pauli 14)) (hcandidate : IsCandidate1435 S) :
    663 * (weightDistribution S 1 : ℤ) -
      1525 * weightDistribution S 2 + 399 * weightDistribution S 3 +
      291 * weightDistribution S 4 + 199 * weightDistribution S 5 +
      123 * weightDistribution S 6 + 63 * weightDistribution S 7 +
      19 * weightDistribution S 8 - 9 * weightDistribution S 9 -
      21 * weightDistribution S 10 - 17 * weightDistribution S 11 +
      3 * weightDistribution S 12 + 39 * weightDistribution S 13 +
      91 * weightDistribution S 14 = -819 := by
  have h := macWilliams_coefficient_of_fixedWeightCharacterSum S
    fixedWeightCharacterSum_14_2
  rw [submodule_card_of_finrank_eleven S hcandidate.1] at h
  rw [normalizer_weightDistribution_eq_of_lt_distance S hcandidate.2.1
    hcandidate.2.2 (j := 2) (by omega)] at h
  norm_num [Finset.sum_range_succ, quantumKrawtchouk, Nat.choose] at h
  omega

/-- The weight-three source row obtained from the semantic MacWilliams
identity. -/
theorem oddMacWilliams3
    (S : Submodule F₂ (Pauli 14)) (hcandidate : IsCandidate1435 S) :
    7020 * (weightDistribution S 1 : ℤ) +
      4788 * weightDistribution S 2 + 1020 * weightDistribution S 3 +
      1796 * weightDistribution S 4 + 908 * weightDistribution S 5 +
      340 * weightDistribution S 6 + 28 * weightDistribution S 7 -
      92 * weightDistribution S 8 - 84 * weightDistribution S 9 -
      12 * weightDistribution S 10 + 60 * weightDistribution S 11 +
      68 * weightDistribution S 12 - 52 * weightDistribution S 13 -
      364 * weightDistribution S 14 = -9828 := by
  have h := macWilliams_coefficient_of_fixedWeightCharacterSum S
    fixedWeightCharacterSum_14_3
  rw [submodule_card_of_finrank_eleven S hcandidate.1] at h
  rw [normalizer_weightDistribution_eq_of_lt_distance S hcandidate.2.1
    hcandidate.2.2 (j := 3) (by omega)] at h
  norm_num [Finset.sum_range_succ, quantumKrawtchouk, Nat.choose] at h
  omega

/-- The weight-four source row obtained from the semantic MacWilliams
identity. -/
theorem oddMacWilliams4
    (S : Submodule F₂ (Pauli 14)) (hcandidate : IsCandidate1435 S) :
    50193 * (weightDistribution S 1 : ℤ) +
      28809 * weightDistribution S 2 + 14817 * weightDistribution S 3 +
      4313 * weightDistribution S 4 + 1841 * weightDistribution S 5 -
      87 * weightDistribution S 6 - 511 * weightDistribution S 7 -
      263 * weightDistribution S 8 + 81 * weightDistribution S 9 +
      201 * weightDistribution S 10 + 33 * weightDistribution S 11 -
      231 * weightDistribution S 12 - 143 * weightDistribution S 13 +
      1001 * weightDistribution S 14 = -81081 := by
  have h := macWilliams_coefficient_of_fixedWeightCharacterSum S
    fixedWeightCharacterSum_14_4
  rw [submodule_card_of_finrank_eleven S hcandidate.1] at h
  rw [normalizer_weightDistribution_eq_of_lt_distance S hcandidate.2.1
    hcandidate.2.2 (j := 4) (by omega)] at h
  norm_num [Finset.sum_range_succ, quantumKrawtchouk, Nat.choose] at h
  omega

/-- The two shadow-enumerator equations.  Their coefficients refer to the
actual even-weight distribution of `S`; `E1` and `E4` are nonnegative counts
in the symplectic normalizer of its parity kernel. -/
structure OddShadowRows (S : Submodule F₂ (Pauli 14)) where
  E1 : ℕ
  E4 : ℕ
  shadow1 :
    34 * (weightDistribution S 2 : ℤ) + 26 * weightDistribution S 4 +
      18 * weightDistribution S 6 + 10 * weightDistribution S 8 +
      2 * weightDistribution S 10 - 6 * weightDistribution S 12 -
      14 * weightDistribution S 14 - 1024 * E1 = -42
  shadow4 :
    28809 * (weightDistribution S 2 : ℤ) + 6361 * weightDistribution S 4 -
      87 * weightDistribution S 6 - 263 * weightDistribution S 8 +
      201 * weightDistribution S 10 - 231 * weightDistribution S 12 +
      1001 * weightDistribution S 14 - 1024 * E4 = -81081

/-- The auxiliary `E` enumerator is the symplectic normalizer enumerator of
the even parity kernel.  Its weight-one and weight-four coefficients satisfy
the two manuscript shadow rows by the same proved MacWilliams transform;
the literal shadow itself is the complementary coset formalized separately. -/
noncomputable def parityKernelShadowRows
    (S : Submodule F₂ (Pauli 14)) (hiso : IsTotallyIsotropic S)
    (hdim : Module.finrank F₂ S = 11) (hodd : ContainsOddWord S) :
    OddShadowRows S := by
  let K := parityKernelAmbient S hiso
  have hdimK : Module.finrank F₂ K = 10 :=
    parityKernelAmbient_finrank S hiso hdim hodd
  have hKEven : IsAllEven K := parityKernelAmbient_isAllEven S hiso
  have h1 := weightDistribution_eq_zero_of_allEven_of_odd K hKEven (j := 1) (by decide)
  have h3 := weightDistribution_eq_zero_of_allEven_of_odd K hKEven (j := 3) (by decide)
  have h5 := weightDistribution_eq_zero_of_allEven_of_odd K hKEven (j := 5) (by decide)
  have h7 := weightDistribution_eq_zero_of_allEven_of_odd K hKEven (j := 7) (by decide)
  have h9 := weightDistribution_eq_zero_of_allEven_of_odd K hKEven (j := 9) (by decide)
  have h11 := weightDistribution_eq_zero_of_allEven_of_odd K hKEven (j := 11) (by decide)
  have h13 := weightDistribution_eq_zero_of_allEven_of_odd K hKEven (j := 13) (by decide)
  have h2 := weightDistribution_parityKernelAmbient_eq_of_even S hiso (j := 2) (by decide)
  have h4 := weightDistribution_parityKernelAmbient_eq_of_even S hiso (j := 4) (by decide)
  have h6 := weightDistribution_parityKernelAmbient_eq_of_even S hiso (j := 6) (by decide)
  have h8 := weightDistribution_parityKernelAmbient_eq_of_even S hiso (j := 8) (by decide)
  have h10 := weightDistribution_parityKernelAmbient_eq_of_even S hiso (j := 10) (by decide)
  have h12 := weightDistribution_parityKernelAmbient_eq_of_even S hiso (j := 12) (by decide)
  have h14 := weightDistribution_parityKernelAmbient_eq_of_even S hiso (j := 14) (by decide)
  refine
    { E1 := weightDistribution (symplecticNormalizer K) 1
      E4 := weightDistribution (symplecticNormalizer K) 4
      shadow1 := ?_
      shadow4 := ?_ }
  · have h := macWilliams_coefficient_of_fixedWeightCharacterSum K
      fixedWeightCharacterSum_14_1
    rw [submodule_card_eq_two_pow_finrank, hdimK] at h
    norm_num [Finset.sum_range_succ, quantumKrawtchouk, Nat.choose] at h
    rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14] at h
    norm_num at h
    omega
  · have h := macWilliams_coefficient_of_fixedWeightCharacterSum K
      fixedWeightCharacterSum_14_4
    rw [submodule_card_eq_two_pow_finrank, hdimK] at h
    norm_num [Finset.sum_range_succ, quantumKrawtchouk, Nat.choose] at h
    rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14] at h
    norm_num at h
    omega


/-- Assemble all eight arithmetic source rows from an actual odd candidate.
No enumerator or shadow row is assumed. -/
noncomputable def oddIdentity51SourceRows
    (S : Submodule F₂ (Pauli 14)) (hcandidate : IsCandidate1435 S)
    (hodd : ContainsOddWord S) : Identity51SourceRows where
  A1 := weightDistribution S 1
  A2 := weightDistribution S 2
  A3 := weightDistribution S 3
  A4 := weightDistribution S 4
  A5 := weightDistribution S 5
  A6 := weightDistribution S 6
  A7 := weightDistribution S 7
  A8 := weightDistribution S 8
  A9 := weightDistribution S 9
  A10 := weightDistribution S 10
  A11 := weightDistribution S 11
  A12 := weightDistribution S 12
  A13 := weightDistribution S 13
  A14 := weightDistribution S 14
  E1 := (parityKernelShadowRows S hcandidate.2.1 hcandidate.1 hodd).E1
  E4 := (parityKernelShadowRows S hcandidate.2.1 hcandidate.1 hodd).E4
  total := candidate_nonzeroWeightTotal S hcandidate.1
  evenTotal := by
    exact_mod_cast oddBranch_evenWeightTotal S hcandidate.2.1 hcandidate.1 hodd
  macWilliams1 := oddMacWilliams1 S hcandidate
  macWilliams2 := oddMacWilliams2 S hcandidate
  macWilliams3 := oddMacWilliams3 S hcandidate
  macWilliams4 := oddMacWilliams4 S hcandidate
  shadow1 :=
    (parityKernelShadowRows S hcandidate.2.1 hcandidate.1 hodd).shadow1
  shadow4 :=
    (parityKernelShadowRows S hcandidate.2.1 hcandidate.1 hodd).shadow4

/-- The actual low-weight distribution of every odd candidate lies in the
Identity-51 profile trichotomy. -/
theorem oddCandidate_profile_trichotomy
    (S : Submodule F₂ (Pauli 14)) (hcandidate : IsCandidate1435 S)
    (hodd : ContainsOddWord S) :
    weightDistribution S 1 = 0 ∧ weightDistribution S 3 = 0 ∧
      ((weightDistribution S 2 = 0 ∧ weightDistribution S 4 = 1) ∨
       (weightDistribution S 2 = 0 ∧ weightDistribution S 4 = 3) ∨
       (weightDistribution S 2 = 1 ∧ weightDistribution S 4 = 1)) :=
  sourceRows_profile_trichotomy
    (oddIdentity51SourceRows S hcandidate hodd)

end Quantum1435
