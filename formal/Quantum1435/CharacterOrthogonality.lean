import Quantum1435.WeightEnumerator
import Mathlib.Algebra.Group.AddChar
import Mathlib.Tactic

/-!
# Character orthogonality for stabilizer subspaces

This is the group-character half of the symplectic MacWilliams proof.  The
remaining half is the local fixed-weight character sum giving the
Krawtchouk polynomial.
-/

namespace Quantum1435

noncomputable local instance {n : ℕ} {S : Submodule F₂ (Pauli n)} : Fintype S :=
  Fintype.ofFinite S

/-- The real-valued additive character of `F₂`. -/
def binarySign (a : F₂) : ℤ := if a = 0 then 1 else -1

@[simp] theorem binarySign_zero : binarySign 0 = 1 := by
  simp [binarySign]

theorem binarySign_add (a b : F₂) :
    binarySign (a + b) = binarySign a * binarySign b := by
  fin_cases a <;> fin_cases b <;> decide

/-- The character on `S` obtained by pairing with an ambient Pauli `w`. -/
def stabilizerCharacter {n : ℕ} (S : Submodule F₂ (Pauli n)) (w : Pauli n) :
    AddChar S ℤ where
  toFun s := binarySign (symplecticForm n s.1 w)
  map_zero_eq_one' := by simp [binarySign]
  map_add_eq_mul' a b := by
    rw [show symplecticForm n (a + b : S).1 w =
        symplecticForm n a.1 w + symplecticForm n b.1 w by simp]
    exact binarySign_add _ _

/-- The pairing character is trivial exactly on the symplectic normalizer. -/
theorem stabilizerCharacter_eq_zero_iff {n : ℕ}
    (S : Submodule F₂ (Pauli n)) (w : Pauli n) :
    stabilizerCharacter S w = 0 ↔ w ∈ symplecticNormalizer S := by
  constructor
  · intro hchar
    rw [mem_symplecticNormalizer_iff]
    intro s hs
    have hvalue := DFunLike.congr_fun hchar (⟨s, hs⟩ : S)
    change binarySign (symplecticForm n s w) = 1 at hvalue
    generalize hv : symplecticForm n s w = value at hvalue
    fin_cases value
    · rfl
    · have hne : binarySign (1 : F₂) ≠ 1 := by decide
      exact (hne hvalue).elim
  · intro hw
    apply AddChar.ext
    intro s
    have hzero := (mem_symplecticNormalizer_iff.mp hw) s.1 s.2
    change binarySign (symplecticForm n s.1 w) = (0 : AddChar S ℤ) s
    rw [hzero]
    simp [binarySign]

/-- A normalizer vector gives the trivial character sum. -/
theorem sum_binarySign_over_submodule_of_mem_normalizer {n : ℕ}
    (S : Submodule F₂ (Pauli n)) (w : Pauli n)
    (hw : w ∈ symplecticNormalizer S) :
    (∑ s : S, binarySign (symplecticForm n s.1 w)) =
      (Fintype.card S : ℤ) := by
  classical
  have hzero : stabilizerCharacter S w = 0 :=
    (stabilizerCharacter_eq_zero_iff S w).2 hw
  change (∑ s : S, (stabilizerCharacter S w) s) = (Fintype.card S : ℤ)
  rw [AddChar.sum_eq_ite, if_pos hzero]

/-- A vector outside the normalizer gives a vanishing character sum. -/
theorem sum_binarySign_over_submodule_of_not_mem_normalizer {n : ℕ}
    (S : Submodule F₂ (Pauli n)) (w : Pauli n)
    (hw : w ∉ symplecticNormalizer S) :
    (∑ s : S, binarySign (symplecticForm n s.1 w)) = 0 := by
  classical
  have hne : stabilizerCharacter S w ≠ 0 := by
    intro hzero
    exact hw ((stabilizerCharacter_eq_zero_iff S w).1 hzero)
  change (∑ s : S, (stabilizerCharacter S w) s) = 0
  rw [AddChar.sum_eq_ite, if_neg hne]

end Quantum1435
