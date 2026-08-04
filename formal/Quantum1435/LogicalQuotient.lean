import Quantum1435.Normalizer
import Mathlib.LinearAlgebra.Quotient.Bilinear
import Mathlib.Tactic

/-!
# Logical Pauli quotient

For a totally isotropic stabilizer `S`, the stabilizer is contained in its
symplectic normalizer.  This file realizes the logical Pauli space as the
quotient `Sᵖ / S` and computes its dimension.
-/

namespace Quantum1435

/-- The copy of `S` inside its symplectic normalizer.  For a non-isotropic
subspace this is its intersection with the normalizer; the intended quotient
theorems below assume total isotropy. -/
def stabilizerInNormalizer {n : ℕ} (S : Submodule F₂ (Pauli n)) :
    Submodule F₂ (symplecticNormalizer S) :=
  S.comap (symplecticNormalizer S).subtype

/-- Logical Paulis modulo stabilizers. -/
abbrev LogicalQuotient {n : ℕ} (S : Submodule F₂ (Pauli n)) :=
  (symplecticNormalizer S) ⧸ stabilizerInNormalizer S

theorem finrank_stabilizerInNormalizer {n : ℕ}
    {S : Submodule F₂ (Pauli n)} (hS : IsTotallyIsotropic S) :
    Module.finrank F₂ (stabilizerInNormalizer S) = Module.finrank F₂ S := by
  exact LinearEquiv.finrank_eq
    (Submodule.comapSubtypeEquivOfLe hS.le_normalizer)

/-- A totally isotropic subspace of the `2n`-dimensional nondegenerate Pauli
space has dimension at most `n`. -/
theorem isotropic_finrank_le_length {n : ℕ}
    {S : Submodule F₂ (Pauli n)} (hS : IsTotallyIsotropic S) :
    Module.finrank F₂ S ≤ n := by
  have hle := Submodule.finrank_mono hS.le_normalizer
  rw [finrank_symplecticNormalizer] at hle
  omega

/-- The logical quotient of an `r`-dimensional isotropic stabilizer has
dimension `2(n-r)`. -/
theorem finrank_logicalQuotient {n : ℕ}
    {S : Submodule F₂ (Pauli n)} (hS : IsTotallyIsotropic S) :
    Module.finrank F₂ (LogicalQuotient S) =
      2 * (n - Module.finrank F₂ S) := by
  have hquot := (stabilizerInNormalizer S).finrank_quotient_add_finrank
  rw [finrank_stabilizerInNormalizer hS, finrank_symplecticNormalizer] at hquot
  have hq : Module.finrank F₂ (LogicalQuotient S) + Module.finrank F₂ S =
      2 * n - Module.finrank F₂ S := hquot
  clear hquot
  have hle := isotropic_finrank_le_length hS
  omega

/-- An 11-dimensional isotropic stabilizer on 14 qubits has six independent
logical Pauli directions (three logical qubits, with X and Z directions). -/
theorem finrank_logicalQuotient_14_11
    {S : Submodule F₂ (Pauli 14)} (hS : IsTotallyIsotropic S)
    (hdim : Module.finrank F₂ S = 11) :
    Module.finrank F₂ (LogicalQuotient S) = 6 := by
  rw [finrank_logicalQuotient hS, hdim]

/-- The Pauli symplectic form is alternating, including in characteristic two. -/
theorem symplecticForm_isAlt (n : ℕ) : (symplecticForm n).IsAlt := by
  intro u
  change (∑ i, ((u i).1 * (u i).2 + (u i).2 * (u i).1)) = 0
  apply Finset.sum_eq_zero
  intro i _
  change (u i).1 * (u i).2 + (u i).2 * (u i).1 = 0
  rw [mul_comm (u i).2 (u i).1, ← two_mul]
  have htwo : (2 : F₂) = 0 := by decide
  rw [htwo, zero_mul]

/-- Restriction of the ambient commutation form to the normalizer. -/
def normalizerSymplecticForm {n : ℕ} (S : Submodule F₂ (Pauli n)) :
    LinearMap.BilinForm F₂ (symplecticNormalizer S) :=
  (symplecticForm n).restrict (symplecticNormalizer S)

theorem normalizerSymplecticForm_isAlt {n : ℕ}
    (S : Submodule F₂ (Pauli n)) : (normalizerSymplecticForm S).IsAlt := by
  intro x
  change symplecticForm n x.val x.val = 0
  exact symplecticForm_isAlt n x.val

/-- For an isotropic stabilizer, its copy in the normalizer is contained in
the radical of the restricted form. -/
theorem stabilizerInNormalizer_le_ker {n : ℕ}
    {S : Submodule F₂ (Pauli n)} (_hS : IsTotallyIsotropic S) :
    stabilizerInNormalizer S ≤ LinearMap.ker (normalizerSymplecticForm S) := by
  intro x hx
  rw [LinearMap.mem_ker]
  apply LinearMap.ext
  intro y
  change symplecticForm n x.val y.val = 0
  exact (mem_symplecticNormalizer_iff.mp y.prop) x.val hx

/-- The commutation form induced on logical Pauli classes. -/
def logicalSymplecticForm {n : ℕ} {S : Submodule F₂ (Pauli n)}
    (hS : IsTotallyIsotropic S) : LinearMap.BilinForm F₂ (LogicalQuotient S) := by
  refine (normalizerSymplecticForm S).liftQ₂
    (stabilizerInNormalizer S) (stabilizerInNormalizer S)
    (stabilizerInNormalizer_le_ker hS) ?_
  rw [(normalizerSymplecticForm_isAlt S).isRefl.ker_flip]
  exact stabilizerInNormalizer_le_ker hS

@[simp] theorem logicalSymplecticForm_mk {n : ℕ}
    {S : Submodule F₂ (Pauli n)} (hS : IsTotallyIsotropic S)
    (x y : symplecticNormalizer S) :
    logicalSymplecticForm hS (Submodule.Quotient.mk x)
      (Submodule.Quotient.mk y) = symplecticForm n x.val y.val := by
  rfl

/-- The induced logical commutation form remains alternating. -/
theorem logicalSymplecticForm_isAlt {n : ℕ}
    {S : Submodule F₂ (Pauli n)} (hS : IsTotallyIsotropic S) :
    (logicalSymplecticForm hS).IsAlt := by
  intro q
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [logicalSymplecticForm_mk]
  exact normalizerSymplecticForm_isAlt S x

/-- The induced alternating form on `Sᵖ / S` is nondegenerate. -/
theorem logicalSymplecticForm_nondegenerate {n : ℕ}
    {S : Submodule F₂ (Pauli n)} (hS : IsTotallyIsotropic S) :
    (logicalSymplecticForm hS).Nondegenerate := by
  apply (logicalSymplecticForm_isAlt hS).isRefl.nondegenerate_iff_separatingLeft.mpr
  intro q hq
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [Submodule.Quotient.mk_eq_zero]
  change x.val ∈ S
  have hxdouble :
      x.val ∈ (symplecticForm n).orthogonal ((symplecticForm n).orthogonal S) := by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro y hy
    have hyN : y ∈ symplecticNormalizer S := by
      exact hy
    let yN : symplecticNormalizer S := ⟨y, hyN⟩
    have hxy : symplecticForm n x.val y = 0 := by
      simpa [yN] using hq (Submodule.Quotient.mk yN)
    exact (symplecticForm_isAlt n).isRefl x.val y hxy
  rw [LinearMap.BilinForm.orthogonal_orthogonal
    (symplecticForm_nondegenerate n) (symplecticForm_isAlt n).isRefl S] at hxdouble
  exact hxdouble

end Quantum1435
