import Quantum1435.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

/-!
# Pauli-weight parity

The parity of Pauli weight is the quadratic refinement of the symplectic
form.  On an isotropic stabilizer it therefore restricts to a linear map.
This supplies the exhaustive all-even/odd branch split used by the proof.
-/

namespace Quantum1435

/-- The one-coordinate indicator of a nonidentity Pauli, written as a
quadratic polynomial over `F₂`. -/
def localParity (p : F₂ × F₂) : F₂ := p.1 + p.2 + p.1 * p.2

/-- Pauli-weight parity as an `F₂`-valued quadratic form. -/
def pauliParity {n : ℕ} (v : Pauli n) : F₂ := ∑ i, localParity (v i)

@[simp] theorem localParity_zero : localParity (0 : F₂ × F₂) = 0 := by
  simp [localParity]

@[simp] theorem pauliParity_zero {n : ℕ} : pauliParity (0 : Pauli n) = 0 := by
  simp [pauliParity]

theorem localParity_add (u v : F₂ × F₂) :
    localParity (u + v) =
      localParity u + localParity v + (u.1 * v.2 + u.2 * v.1) := by
  rcases u with ⟨ux, uz⟩
  rcases v with ⟨vx, vz⟩
  simp only [localParity, Prod.fst_add, Prod.snd_add]
  ring

/-- The global quadratic-refinement identity. -/
theorem pauliParity_add {n : ℕ} (u v : Pauli n) :
    pauliParity (u + v) =
      pauliParity u + pauliParity v + symplecticForm n u v := by
  simp only [pauliParity, Pi.add_apply, localParity_add, symplecticForm,
    LinearMap.mk₂_apply]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]

theorem pauliParity_smul {n : ℕ} (c : F₂) (v : Pauli n) :
    pauliParity (c • v) = c * pauliParity v := by
  have hc : c * c = c := by
    fin_cases c <;> decide
  simp only [pauliParity, localParity, Pi.smul_apply, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring_nf
  rw [pow_two, hc]
  ring

private theorem localParity_eq_indicator (p : F₂ × F₂) :
    localParity p = if p = 0 then 0 else 1 := by
  rcases p with ⟨x, z⟩
  fin_cases x <;> fin_cases z <;> decide

/-- `pauliParity` is exactly the natural Pauli weight reduced modulo two. -/
theorem pauliParity_eq_weight_cast {n : ℕ} (v : Pauli n) :
    pauliParity v = (pauliWeight v : F₂) := by
  classical
  simpa [pauliParity, pauliWeight, localParity_eq_indicator] using
    (Finset.sum_boole (R := F₂) (fun i : Fin n ↦ v i ≠ 0) Finset.univ)

/-- The parity functional restricted to an isotropic stabilizer. -/
def parityLinearMap {n : ℕ} (S : Submodule F₂ (Pauli n))
    (hS : IsTotallyIsotropic S) : S →ₗ[F₂] F₂ where
  toFun v := pauliParity v.1
  map_add' u v := by
    change pauliParity (u.1 + v.1) = pauliParity u.1 + pauliParity v.1
    rw [pauliParity_add, hS u.2 v.2]
    simp
  map_smul' c v := by
    simpa [smul_eq_mul] using pauliParity_smul c v.1

/-- The stabilizer is in the all-even parity branch. -/
def IsAllEven {n : ℕ} (S : Submodule F₂ (Pauli n)) : Prop :=
  ∀ v ∈ S, pauliParity v = 0

/-- The stabilizer contains an odd-weight word. -/
def ContainsOddWord {n : ℕ} (S : Submodule F₂ (Pauli n)) : Prop :=
  ∃ v ∈ S, pauliParity v = 1

/-- Every stabilizer lies in one of the two parity branches. -/
theorem parity_split {n : ℕ} (S : Submodule F₂ (Pauli n)) :
    IsAllEven S ∨ ContainsOddWord S := by
  classical
  by_cases h : IsAllEven S
  · exact Or.inl h
  · right
    unfold IsAllEven at h
    push Not at h
    obtain ⟨v, hvS, hv⟩ := h
    refine ⟨v, hvS, ?_⟩
    generalize hq : pauliParity v = q
    fin_cases q
    · exact (hv hq).elim
    · rfl

/-- In the odd branch the even kernel has codimension one. -/
theorem parityKernel_finrank {n : ℕ} (S : Submodule F₂ (Pauli n))
    (hS : IsTotallyIsotropic S) (hdim : Module.finrank F₂ S = 11)
    (hodd : ContainsOddWord S) :
    Module.finrank F₂ (LinearMap.ker (parityLinearMap S hS)) = 10 := by
  obtain ⟨v, hvS, hv⟩ := hodd
  let f := parityLinearMap S hS
  have hone : (1 : F₂) ∈ LinearMap.range f := ⟨⟨v, hvS⟩, hv⟩
  have hrange : LinearMap.range f = ⊤ := by
    apply le_antisymm le_top
    intro x _
    fin_cases x
    · exact Submodule.zero_mem _
    · exact hone
  change Module.finrank F₂ (LinearMap.ker f) = 10
  have hrank := f.finrank_range_add_finrank_ker
  rw [hrange, hdim] at hrank
  norm_num at hrank
  omega

end Quantum1435
