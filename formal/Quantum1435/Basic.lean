import Mathlib.Algebra.Module.ZMod
import Mathlib.Data.Finset.Card
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

/-!
# Binary Pauli spaces

The phase-free `n`-qubit Pauli group is the vector space
`(ZMod 2 × ZMod 2)^n`.  The first bit is the X component and the second bit
is the Z component.  This file defines Pauli weight, the symplectic
commutation form, totally isotropic stabilizers, and their symplectic
normalizers.
-/

namespace Quantum1435

abbrev F₂ := ZMod 2

/-- A phase-free Pauli vector on `n` qubits, in per-coordinate `(X,Z)` form. -/
abbrev Pauli (n : ℕ) := Fin n → (F₂ × F₂)

/-- The symplectic commutation form on phase-free Pauli vectors. -/
def symplecticForm (n : ℕ) : LinearMap.BilinForm F₂ (Pauli n) :=
  LinearMap.mk₂ F₂
    (fun u v ↦ ∑ i, ((u i).1 * (v i).2 + (u i).2 * (v i).1))
    (by
      intro u v w
      simp only [Pi.add_apply, Prod.fst_add, Prod.snd_add, add_mul]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring)
    (by
      intro c u v
      simp only [Pi.smul_apply, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring)
    (by
      intro u v w
      simp only [Pi.add_apply, Prod.fst_add, Prod.snd_add, mul_add]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring)
    (by
      intro c u v
      simp only [Pi.smul_apply, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring)

/-- Two Pauli vectors commute when their binary symplectic product vanishes. -/
def Commute {n : ℕ} (u v : Pauli n) : Prop := symplecticForm n u v = 0

/-- Pauli weight: the number of coordinates whose `(X,Z)` pair is nonzero. -/
def pauliWeight {n : ℕ} (v : Pauli n) : ℕ :=
  Finset.card (Finset.univ.filter fun i ↦ v i ≠ 0)

/-- `S` is totally isotropic when all of its elements commute pairwise. -/
def IsTotallyIsotropic {n : ℕ} (S : Submodule F₂ (Pauli n)) : Prop :=
  ∀ ⦃u⦄, u ∈ S → ∀ ⦃v⦄, v ∈ S → symplecticForm n u v = 0

/-- The symplectic normalizer `Sᵖ`: all phase-free Paulis commuting with `S`. -/
def symplecticNormalizer {n : ℕ} (S : Submodule F₂ (Pauli n)) :
    Submodule F₂ (Pauli n) :=
  (symplecticForm n).orthogonal S

@[simp] theorem mem_symplecticNormalizer_iff {n : ℕ}
    {S : Submodule F₂ (Pauli n)} {v : Pauli n} :
    v ∈ symplecticNormalizer S ↔ ∀ s ∈ S, symplecticForm n s v = 0 := by
  simp [symplecticNormalizer]

/-- Logical Paulis are normalizer elements outside the stabilizer itself. -/
def IsLogical {n : ℕ} (S : Submodule F₂ (Pauli n)) (v : Pauli n) : Prop :=
  v ∈ symplecticNormalizer S ∧ v ∉ S

/-- `d` is the minimum logical weight.  This relational definition exposes
both existence of a weight-`d` logical and minimality, and has no empty-set
convention hidden in it. -/
def LogicalDistanceIs {n : ℕ} (S : Submodule F₂ (Pauli n)) (d : ℕ) : Prop :=
  (∃ v, IsLogical S v ∧ pauliWeight v = d) ∧
    ∀ v, IsLogical S v → d ≤ pauliWeight v

/-- The lower-bound formulation used in the nonexistence theorem. -/
def HasLogicalDistanceAtLeast {n : ℕ}
    (S : Submodule F₂ (Pauli n)) (d : ℕ) : Prop :=
  ∀ v, IsLogical S v → d ≤ pauliWeight v

theorem LogicalDistanceIs.atLeast {n d : ℕ} {S : Submodule F₂ (Pauli n)}
    (h : LogicalDistanceIs S d) : HasLogicalDistanceAtLeast S d := h.2

theorem IsTotallyIsotropic.le_normalizer {n : ℕ}
    {S : Submodule F₂ (Pauli n)} (hS : IsTotallyIsotropic S) :
    S ≤ symplecticNormalizer S := by
  intro v hv
  rw [mem_symplecticNormalizer_iff]
  intro s hs
  exact hS hs hv

end Quantum1435
