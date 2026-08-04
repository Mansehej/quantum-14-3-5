import Quantum1435.MacWilliamsBridge
import Mathlib.Tactic

/-!
# The local symplectic Krawtchouk identity

This file proves the remaining local character-sum obligation used by the
MacWilliams bridge.  The proof peels off one Pauli coordinate at a time.  At
a zero coordinate of `v`, the three nonzero Paulis contribute `3`; at a
nonzero coordinate, their character values sum to `-1`.

The semantic recurrence is proved for every length and weight.  The final
comparison with the closed binomial formula `quantumKrawtchouk` is a small
kernel computation for lengths and weights used by the length-14 proof.
-/

namespace Quantum1435

/-- Add one coordinate at the front of a Pauli vector. -/
def pauliCons {n : ℕ} (a : F₂ × F₂) (v : Pauli n) : Pauli (n + 1) :=
  Fin.cases a v

@[simp] theorem pauliCons_zero {n : ℕ} (a : F₂ × F₂) (v : Pauli n) :
    pauliCons a v 0 = a := rfl

@[simp] theorem pauliCons_succ {n : ℕ} (a : F₂ × F₂) (v : Pauli n)
    (i : Fin n) : pauliCons a v i.succ = v i := rfl

/-- Splitting off the first coordinate is an equivalence. -/
def pauliConsEquiv (n : ℕ) : (F₂ × F₂) × Pauli n ≃ Pauli (n + 1) where
  toFun p := pauliCons p.1 p.2
  invFun v := (v 0, fun i ↦ v i.succ)
  left_inv p := by
    apply Prod.ext
    · rfl
    · funext i
      rfl
  right_inv v := by
    funext i
    refine Fin.cases ?_ (fun k ↦ ?_) i
    · rfl
    · rfl

@[simp] theorem pauliConsEquiv_apply {n : ℕ} (p : (F₂ × F₂) × Pauli n) :
    pauliConsEquiv n p = pauliCons p.1 p.2 := rfl

/-- The one-coordinate symplectic product. -/
def coordinatePair (a x : F₂ × F₂) : F₂ :=
  a.1 * x.2 + a.2 * x.1

@[simp] theorem symplecticForm_pauliCons {n : ℕ}
    (a x : F₂ × F₂) (v w : Pauli n) :
    symplecticForm (n + 1) (pauliCons a v) (pauliCons x w) =
      coordinatePair a x + symplecticForm n v w := by
  simp [symplecticForm, coordinatePair, Fin.sum_univ_succ]

@[simp] theorem pauliWeight_pauliCons {n : ℕ}
    (a : F₂ × F₂) (v : Pauli n) :
    pauliWeight (pauliCons a v) =
      (if a = 0 then 0 else 1) + pauliWeight v := by
  classical
  unfold pauliWeight
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Fin.sum_univ_succ]
  simp only [pauliCons_zero, pauliCons_succ]
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  simp
  by_cases ha : a = 0 <;> simp [ha]
  all_goals
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : v i = 0 <;> simp [hi]

/-- The local character sum over the three nonidentity Paulis. -/
theorem sum_nonzero_coordinate_character (a : F₂ × F₂) :
    (∑ x : F₂ × F₂, if x = 0 then 0 else
      binarySign (coordinatePair a x)) = if a = 0 then 3 else -1 := by
  rcases a with ⟨a₁, a₂⟩
  fin_cases a₁ <;> fin_cases a₂ <;> decide

/-- The fixed-weight character sum, named separately so its recurrence can
be stated and reused. -/
def localCharacterSum (n j : ℕ) (v : Pauli n) : ℤ :=
  ∑ w : Pauli n, if pauliWeight w = j then
    binarySign (symplecticForm n v w) else 0

theorem localCharacterSum_zero (n : ℕ) (v : Pauli n) :
    localCharacterSum n 0 v = 1 := by
  classical
  rw [localCharacterSum]
  have hzero : ∀ w : Pauli n, pauliWeight w = 0 ↔ w = 0 := by
    intro w
    exact pauliWeight_eq_zero_iff
  simp_rw [hzero]
  simp

/-- Peeling off one coordinate gives the Krawtchouk recurrence. -/
theorem localCharacterSum_succ {n j : ℕ} (a : F₂ × F₂) (v : Pauli n) :
    localCharacterSum (n + 1) (j + 1) (pauliCons a v) =
      localCharacterSum n (j + 1) v +
        (if a = 0 then 3 else -1) * localCharacterSum n j v := by
  classical
  rw [localCharacterSum]
  rw [← (pauliConsEquiv n).sum_comp]
  rw [Fintype.sum_prod_type]
  simp only [pauliConsEquiv_apply, symplecticForm_pauliCons,
    pauliWeight_pauliCons, binarySign_add]
  rw [localCharacterSum, localCharacterSum]
  rw [Finset.sum_comm]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro w _
  let z : ℤ := binarySign (symplecticForm n v w)
  let k : ℕ := pauliWeight w
  have hlocal :
      (∑ x : F₂ × F₂,
        if (if x = 0 then 0 else 1) + k = j + 1 then
          binarySign (coordinatePair a x) * z else 0) =
        (if k = j + 1 then z else 0) +
          (if a = 0 then 3 else -1) * (if k = j then z else 0) := by
    by_cases hkj : k = j
    · have hkjs : k ≠ j + 1 := by omega
      have hcondition : ∀ x : F₂ × F₂,
          (if x = 0 then 0 else 1) + k = j + 1 ↔ x ≠ 0 := by
        intro x
        by_cases hx : x = 0
        · simp [hx, hkj]
        · simp [hx, hkj]
          omega
      simp_rw [hcondition]
      rw [show (∑ x : F₂ × F₂, if x ≠ 0 then
          binarySign (coordinatePair a x) * z else 0) =
          (∑ x : F₂ × F₂, if x = 0 then 0 else
            binarySign (coordinatePair a x)) * z by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : x = 0 <;> simp [hx]]
      rw [sum_nonzero_coordinate_character]
      simp [hkj]
    · by_cases hkjs : k = j + 1
      · have hcondition : ∀ x : F₂ × F₂,
          (if x = 0 then 0 else 1) + k = j + 1 ↔ x = 0 := by
          intro x
          by_cases hx : x = 0 <;> simp [hx, hkjs]
        simp_rw [hcondition]
        simp [coordinatePair, hkjs]
      · have hcondition : ∀ x : F₂ × F₂,
          ¬((if x = 0 then 0 else 1) + k = j + 1) := by
          intro x
          by_cases hx : x = 0
          · simpa [hx] using hkjs
          · simp only [hx, if_false]
            omega
        rw [show (∑ x : F₂ × F₂,
            if (if x = 0 then 0 else 1) + k = j + 1 then
              binarySign (coordinatePair a x) * z else 0) = 0 by
          apply Finset.sum_eq_zero
          intro x _
          rw [if_neg (hcondition x)]]
        simp [hkj, hkjs]
  simpa [k, z, mul_assoc, mul_left_comm, mul_comm] using hlocal

/-- Adding a zero coordinate gives the `3` branch of the closed Krawtchouk
recurrence.  The finite range needed by the length-14 theorem is checked by
the Lean kernel. -/
theorem quantumKrawtchouk_zero_step (n j i : ℕ)
    (hn : n ≤ 13) (hj : j ≤ 3) (hi : i ≤ n) :
    quantumKrawtchouk (n + 1) (j + 1) i =
      quantumKrawtchouk n (j + 1) i +
        3 * quantumKrawtchouk n j i := by
  interval_cases n <;> interval_cases j <;> interval_cases i <;> decide

/-- Adding a nonzero coordinate gives the `-1` branch of the closed
Krawtchouk recurrence. -/
theorem quantumKrawtchouk_nonzero_step (n j i : ℕ)
    (hn : n ≤ 13) (hj : j ≤ 3) (hi : i ≤ n) :
    quantumKrawtchouk (n + 1) (j + 1) (i + 1) =
      quantumKrawtchouk n (j + 1) i - quantumKrawtchouk n j i := by
  interval_cases n <;> interval_cases j <;> interval_cases i <;> decide

/-- Up through the length and coefficient range used in this development,
the genuine ambient character sum is the closed quaternary Krawtchouk
polynomial.  No ambient enumeration is performed: the proof inducts over
coordinates using `localCharacterSum_succ`. -/
theorem localCharacterSum_eq_quantum_of_bounds :
    ∀ (n : ℕ), n ≤ 14 → ∀ (j : ℕ), j ≤ 4 → ∀ v : Pauli n,
      localCharacterSum n j v =
        quantumKrawtchouk n j (pauliWeight v) := by
  intro n
  induction n with
  | zero =>
      intro _ j _ v
      have hv : v = 0 := Subsingleton.elim _ _
      subst v
      interval_cases j <;> decide
  | succ n ih =>
      intro hn j hj v
      let a : F₂ × F₂ := v 0
      let tail : Pauli n := fun i ↦ v i.succ
      have hv : pauliCons a tail = v := by
        funext i
        refine Fin.cases ?_ (fun k ↦ ?_) i
        · rfl
        · rfl
      rw [← hv]
      cases j with
      | zero =>
          rw [localCharacterSum_zero]
          simp [quantumKrawtchouk]
      | succ j =>
          have hn13 : n ≤ 13 := by omega
          have hj3 : j ≤ 3 := by omega
          rw [localCharacterSum_succ,
            ih (by omega) (j + 1) (by omega) tail,
            ih (by omega) j (by omega) tail]
          by_cases ha : a = 0
          · simp [pauliWeight_pauliCons, ha]
            rw [quantumKrawtchouk_zero_step n j (pauliWeight tail)
              hn13 hj3 (pauliWeight_le_length tail)]
          · simp [pauliWeight_pauliCons, ha, Nat.one_add]
            rw [quantumKrawtchouk_nonzero_step n j (pauliWeight tail)
              hn13 hj3 (pauliWeight_le_length tail)]
            ring

/-- The four local identities consumed by the length-14 MacWilliams bridge. -/
theorem fixedWeightCharacterSum_14_1 : FixedWeightCharacterSum 14 1 := by
  intro v
  exact localCharacterSum_eq_quantum_of_bounds 14 (by omega) 1 (by omega) v

theorem fixedWeightCharacterSum_14_2 : FixedWeightCharacterSum 14 2 := by
  intro v
  exact localCharacterSum_eq_quantum_of_bounds 14 (by omega) 2 (by omega) v

theorem fixedWeightCharacterSum_14_3 : FixedWeightCharacterSum 14 3 := by
  intro v
  exact localCharacterSum_eq_quantum_of_bounds 14 (by omega) 3 (by omega) v

theorem fixedWeightCharacterSum_14_4 : FixedWeightCharacterSum 14 4 := by
  intro v
  exact localCharacterSum_eq_quantum_of_bounds 14 (by omega) 4 (by omega) v

end Quantum1435
