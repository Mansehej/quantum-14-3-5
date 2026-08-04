import Quantum1435.OddSemantic
import Mathlib.Tactic

/-!
# The odd-branch shadow as an actual normalizer coset

For an odd totally isotropic stabilizer `S`, let `C0` be its even-weight
parity kernel.  The shadow is the literal set difference

`C0ᵖ \ Sᵖ`.

This file proves the associated coset facts in the ambient binary Pauli
space.  In particular, a shadow word pairs to one with every odd stabilizer
word, the sum of two shadow words lies in `Sᵖ`, and translation by `Sᵖ`
preserves the shadow.  For an 11-dimensional odd stabilizer on 14 qubits,
`Sᵖ` has codimension one in `C0ᵖ`, so the shadow is nonempty.
-/

noncomputable section

namespace Quantum1435

/-- The even parity kernel is contained in the original stabilizer. -/
theorem parityKernelAmbient_le {n : ℕ}
    (S : Submodule F₂ (Pauli n)) (hiso : IsTotallyIsotropic S) :
    parityKernelAmbient S hiso ≤ S := by
  intro v hv
  exact (mem_parityKernelAmbient_iff S hiso v).mp hv |>.1

/-- Every Pauli commuting with `S` also commutes with its parity kernel. -/
theorem symplecticNormalizer_le_parityKernelNormalizer {n : ℕ}
    (S : Submodule F₂ (Pauli n)) (hiso : IsTotallyIsotropic S) :
    symplecticNormalizer S ≤
      symplecticNormalizer (parityKernelAmbient S hiso) := by
  intro v hv
  rw [mem_symplecticNormalizer_iff] at hv ⊢
  intro k hk
  exact hv k ((parityKernelAmbient_le S hiso) hk)

/-- A shadow word is an actual element of `C0ᵖ \ Sᵖ`. -/
def IsShadowWord {n : ℕ} (S : Submodule F₂ (Pauli n))
    (hiso : IsTotallyIsotropic S) (v : Pauli n) : Prop :=
  v ∈ symplecticNormalizer (parityKernelAmbient S hiso) ∧
    v ∉ symplecticNormalizer S

/-- The actual number of weight-`j` shadow words. -/
def shadowWeightDistribution {n : ℕ}
    (S : Submodule F₂ (Pauli n)) (hiso : IsTotallyIsotropic S) (j : ℕ) : ℕ :=
  by
    classical
    exact Finset.card (Finset.univ.filter fun v ↦
      IsShadowWord S hiso v ∧ pauliWeight v = j)

theorem shadowWord_commutes_with_parityKernel {n : ℕ}
    {S : Submodule F₂ (Pauli n)} {hiso : IsTotallyIsotropic S}
    {v : Pauli n} (hv : IsShadowWord S hiso v) :
    ∀ k ∈ parityKernelAmbient S hiso, symplecticForm n k v = 0 := by
  exact (mem_symplecticNormalizer_iff.mp hv.1)

/-- A shadow word pairs to one with every odd stabilizer word. -/
theorem shadowWord_pairs_one_with_odd {n : ℕ}
    {S : Submodule F₂ (Pauli n)} {hiso : IsTotallyIsotropic S}
    {v s : Pauli n} (hv : IsShadowWord S hiso v)
    (hsS : s ∈ S) (hsOdd : pauliParity s = 1) :
    symplecticForm n s v = 1 := by
  have hvNot : ¬ ∀ t ∈ S, symplecticForm n t v = 0 := by
    intro h
    exact hv.2 (mem_symplecticNormalizer_iff.mpr h)
  push Not at hvNot
  obtain ⟨t, htS, htPairNe⟩ := hvNot
  have htOdd : pauliParity t = 1 := by
    generalize htParity : pauliParity t = q
    fin_cases q
    · exfalso
      apply htPairNe
      exact shadowWord_commutes_with_parityKernel hv t
        ((mem_parityKernelAmbient_iff S hiso t).mpr ⟨htS, htParity⟩)
    · rfl
  have htPair : symplecticForm n t v = 1 := by
    generalize hpair : symplecticForm n t v = q
    fin_cases q
    · exact (htPairNe hpair).elim
    · rfl
  have hstS : s + t ∈ S := S.add_mem hsS htS
  have hstEven : pauliParity (s + t) = 0 := by
    rw [pauliParity_add, hiso hsS htS, hsOdd, htOdd]
    decide
  have hstPair : symplecticForm n (s + t) v = 0 :=
    shadowWord_commutes_with_parityKernel hv (s + t)
      ((mem_parityKernelAmbient_iff S hiso (s + t)).mpr ⟨hstS, hstEven⟩)
  have hstPair' :
      symplecticForm n s v + symplecticForm n t v = 0 := by
    simpa only [map_add, LinearMap.add_apply] using hstPair
  rw [htPair] at hstPair'
  generalize hsPair : symplecticForm n s v = q at hstPair' ⊢
  fin_cases q
  · exfalso
    exact (show ¬ ((0 : F₂) + 1 = 0) by decide) hstPair'
  · rfl

/-- The sum of two shadow words lies in the original symplectic normalizer. -/
theorem shadowWord_add_shadowWord_mem_normalizer {n : ℕ}
    {S : Submodule F₂ (Pauli n)} {hiso : IsTotallyIsotropic S}
    {v w : Pauli n} (hv : IsShadowWord S hiso v)
    (hw : IsShadowWord S hiso w) :
    v + w ∈ symplecticNormalizer S := by
  rw [mem_symplecticNormalizer_iff]
  intro s hsS
  generalize hsParity : pauliParity s = q
  fin_cases q
  · have hsK : s ∈ parityKernelAmbient S hiso :=
      (mem_parityKernelAmbient_iff S hiso s).mpr ⟨hsS, hsParity⟩
    rw [map_add]
    rw [shadowWord_commutes_with_parityKernel hv s hsK,
      shadowWord_commutes_with_parityKernel hw s hsK]
    rfl
  · rw [map_add, shadowWord_pairs_one_with_odd hv hsS hsParity,
      shadowWord_pairs_one_with_odd hw hsS hsParity]
    decide

/-- Translating a shadow word by an element of `Sᵖ` remains in the shadow. -/
theorem shadowWord_add_normalizer {n : ℕ}
    {S : Submodule F₂ (Pauli n)} {hiso : IsTotallyIsotropic S}
    {v a : Pauli n} (hv : IsShadowWord S hiso v)
    (ha : a ∈ symplecticNormalizer S) :
    IsShadowWord S hiso (v + a) := by
  constructor
  · exact (symplecticNormalizer (parityKernelAmbient S hiso)).add_mem
      hv.1 (symplecticNormalizer_le_parityKernelNormalizer S hiso ha)
  · intro hva
    apply hv.2
    have hsub := (symplecticNormalizer S).sub_mem hva ha
    simpa using hsub

/-- Relative to a fixed shadow word, shadow membership is exactly membership
of the difference (equivalently, in characteristic two, the sum) in `Sᵖ`. -/
theorem shadowWord_iff_add_mem_normalizer {n : ℕ}
    {S : Submodule F₂ (Pauli n)} {hiso : IsTotallyIsotropic S}
    {v w : Pauli n} (hv : IsShadowWord S hiso v) :
    IsShadowWord S hiso w ↔ v + w ∈ symplecticNormalizer S := by
  constructor
  · intro hw
    exact shadowWord_add_shadowWord_mem_normalizer hv hw
  · intro hvw
    have htranslated := shadowWord_add_normalizer hv hvw
    have hvv : v + v = 0 := by
      calc
        v + v = (1 : F₂) • v + (1 : F₂) • v := by simp
        _ = ((1 : F₂) + 1) • v := by rw [add_smul]
        _ = 0 := by rw [show (1 : F₂) + 1 = 0 by decide, zero_smul]
    have hcollapse : v + (v + w) = w := by
      rw [← add_assoc, hvv, zero_add]
    simpa only [hcollapse] using htranslated

/-- The copy of `Sᵖ` as a subspace of `C0ᵖ`. -/
def normalizerInsideParityKernelNormalizer {n : ℕ}
    (S : Submodule F₂ (Pauli n)) (hiso : IsTotallyIsotropic S) :
    Submodule F₂ (symplecticNormalizer (parityKernelAmbient S hiso)) :=
  (symplecticNormalizer S).comap
    (symplecticNormalizer (parityKernelAmbient S hiso)).subtype

/-- The quotient `C0ᵖ / Sᵖ` which indexes the two normalizer cosets. -/
abbrev ShadowQuotient {n : ℕ}
    (S : Submodule F₂ (Pauli n)) (hiso : IsTotallyIsotropic S) :=
  (symplecticNormalizer (parityKernelAmbient S hiso)) ⧸
    normalizerInsideParityKernelNormalizer S hiso

theorem finrank_normalizerInsideParityKernelNormalizer {n : ℕ}
    (S : Submodule F₂ (Pauli n)) (hiso : IsTotallyIsotropic S) :
    Module.finrank F₂ (normalizerInsideParityKernelNormalizer S hiso) =
      Module.finrank F₂ (symplecticNormalizer S) := by
  exact LinearEquiv.finrank_eq
    (Submodule.comapSubtypeEquivOfLe
      (symplecticNormalizer_le_parityKernelNormalizer S hiso))

/-- For an odd 11-dimensional length-14 stabilizer, `Sᵖ` has codimension
one in `C0ᵖ`; equivalently the shadow quotient is one-dimensional over
`F₂` and hence has two cosets. -/
theorem finrank_shadowQuotient_14_11
    (S : Submodule F₂ (Pauli 14)) (hiso : IsTotallyIsotropic S)
    (hdim : Module.finrank F₂ S = 11) (hodd : ContainsOddWord S) :
    Module.finrank F₂ (ShadowQuotient S hiso) = 1 := by
  have hdimK : Module.finrank F₂ (parityKernelAmbient S hiso) = 10 :=
    parityKernelAmbient_finrank S hiso hdim hodd
  have hinside :
      Module.finrank F₂ (normalizerInsideParityKernelNormalizer S hiso) = 17 := by
    rw [finrank_normalizerInsideParityKernelNormalizer,
      finrank_symplecticNormalizer, hdim]
  have hambient : Module.finrank F₂
      (symplecticNormalizer (parityKernelAmbient S hiso)) = 18 := by
    rw [finrank_symplecticNormalizer, hdimK]
  have hquot :=
    (normalizerInsideParityKernelNormalizer S hiso).finrank_quotient_add_finrank
  rw [hinside, hambient] at hquot
  have hresult := Nat.eq_sub_of_add_eq hquot
  norm_num at hresult
  exact hresult

/-- The odd length-14 shadow is nonempty. -/
theorem exists_shadowWord_14_11
    (S : Submodule F₂ (Pauli 14)) (hiso : IsTotallyIsotropic S)
    (hdim : Module.finrank F₂ S = 11) (hodd : ContainsOddWord S) :
    ∃ v, IsShadowWord S hiso v := by
  have hle := symplecticNormalizer_le_parityKernelNormalizer S hiso
  have hdimK : Module.finrank F₂ (parityKernelAmbient S hiso) = 10 :=
    parityKernelAmbient_finrank S hiso hdim hodd
  have hne : symplecticNormalizer S ≠
      symplecticNormalizer (parityKernelAmbient S hiso) := by
    intro heq
    have hrank := congrArg
      (fun T : Submodule F₂ (Pauli 14) ↦ Module.finrank F₂ T) heq
    rw [finrank_symplecticNormalizer, finrank_symplecticNormalizer,
      hdim, hdimK] at hrank
    norm_num at hrank
  have hlt : symplecticNormalizer S <
      symplecticNormalizer (parityKernelAmbient S hiso) :=
    lt_of_le_of_ne hle hne
  obtain ⟨v, hvKernel, hvNot⟩ := SetLike.exists_of_lt hlt
  exact ⟨v, hvKernel, hvNot⟩

end Quantum1435
