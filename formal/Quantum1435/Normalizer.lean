import Quantum1435.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic

/-!
# Nondegeneracy and normalizer dimension

The coordinate symplectic form is nondegenerate.  Consequently an
`r`-dimensional stabilizer in the `2n`-dimensional Pauli space has a
`(2n-r)`-dimensional symplectic normalizer.
-/

namespace Quantum1435

/-- The one-coordinate `X` Pauli at position `i`. -/
def singleX {n : ℕ} (i : Fin n) : Pauli n :=
  fun j ↦ if j = i then (1, 0) else 0

/-- The one-coordinate `Z` Pauli at position `i`. -/
def singleZ {n : ℕ} (i : Fin n) : Pauli n :=
  fun j ↦ if j = i then (0, 1) else 0

@[simp] theorem symplectic_singleZ_right {n : ℕ} (u : Pauli n) (i : Fin n) :
    symplecticForm n u (singleZ i) = (u i).1 := by
  classical
  change (∑ x, ((u x).1 * ((singleZ i) x).2 + (u x).2 * ((singleZ i) x).1)) = (u i).1
  rw [← Fintype.sum_ite_eq' i (fun x ↦ (u x).1)]
  apply Finset.sum_congr rfl
  intro x _
  split <;> simp_all [singleZ]

@[simp] theorem symplectic_singleX_right {n : ℕ} (u : Pauli n) (i : Fin n) :
    symplecticForm n u (singleX i) = (u i).2 := by
  classical
  change (∑ x, ((u x).1 * ((singleX i) x).2 + (u x).2 * ((singleX i) x).1)) = (u i).2
  rw [← Fintype.sum_ite_eq' i (fun x ↦ (u x).2)]
  apply Finset.sum_congr rfl
  intro x _
  split <;> simp_all [singleX]

@[simp] theorem symplectic_singleZ_left {n : ℕ} (u : Pauli n) (i : Fin n) :
    symplecticForm n (singleZ i) u = (u i).1 := by
  classical
  change (∑ x, (((singleZ i) x).1 * (u x).2 + ((singleZ i) x).2 * (u x).1)) = (u i).1
  rw [← Fintype.sum_ite_eq' i (fun x ↦ (u x).1)]
  apply Finset.sum_congr rfl
  intro x _
  split <;> simp_all [singleZ]

@[simp] theorem symplectic_singleX_left {n : ℕ} (u : Pauli n) (i : Fin n) :
    symplecticForm n (singleX i) u = (u i).2 := by
  classical
  change (∑ x, (((singleX i) x).1 * (u x).2 + ((singleX i) x).2 * (u x).1)) = (u i).2
  rw [← Fintype.sum_ite_eq' i (fun x ↦ (u x).2)]
  apply Finset.sum_congr rfl
  intro x _
  split <;> simp_all [singleX]

/-- The binary Pauli commutation form is nondegenerate. -/
theorem symplecticForm_nondegenerate (n : ℕ) :
    (symplecticForm n).Nondegenerate := by
  constructor
  · intro u hu
    funext i
    apply Prod.ext
    · simpa using hu (singleZ i)
    · simpa using hu (singleX i)
  · intro u hu
    funext i
    apply Prod.ext
    · simpa using hu (singleZ i)
    · simpa using hu (singleX i)

theorem finrank_pauli (n : ℕ) : Module.finrank F₂ (Pauli n) = 2 * n := by
  change Module.finrank F₂ (Fin n → F₂ × F₂) = 2 * n
  rw [Module.finrank_pi_fintype]
  simp [Module.finrank_prod]
  omega

/-- Dimension of the symplectic normalizer of an arbitrary Pauli subspace. -/
theorem finrank_symplecticNormalizer {n : ℕ}
    (S : Submodule F₂ (Pauli n)) :
    Module.finrank F₂ (symplecticNormalizer S) =
      2 * n - Module.finrank F₂ S := by
  rw [symplecticNormalizer,
    LinearMap.BilinForm.finrank_orthogonal (symplecticForm_nondegenerate n), finrank_pauli]

theorem finrank_normalizer_14_11 (S : Submodule F₂ (Pauli 14))
    (hS : Module.finrank F₂ S = 11) :
    Module.finrank F₂ (symplecticNormalizer S) = 17 := by
  rw [finrank_symplecticNormalizer, hS]

/-- An 11-dimensional subspace of the 28-dimensional Pauli space has a
logical Pauli.  Thus the minimum-distance relation is nonvacuous here. -/
theorem exists_logical_of_finrank_eleven
    (S : Submodule F₂ (Pauli 14))
    (hS : Module.finrank F₂ S = 11) :
    ∃ v, IsLogical S v := by
  by_contra h
  have hle : symplecticNormalizer S ≤ S := by
    intro v hvN
    by_contra hvS
    exact h ⟨v, hvN, hvS⟩
  have hdimle := Submodule.finrank_mono hle
  rw [finrank_normalizer_14_11 S hS, hS] at hdimle
  omega

end Quantum1435
