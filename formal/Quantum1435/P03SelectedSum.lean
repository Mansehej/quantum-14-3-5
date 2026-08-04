import Quantum1435.P03CollisionChecker

/-!
# Finite selected-set degree bounds

This module isolates the elementary top-`k` estimate needed by the p03
collision argument.  Unlike `ThresholdBound`, it does not enumerate an
ambient `Fintype`; it only asks for a pointwise maximum and a bound on the
exceptional elements of the selected set.
-/

namespace Quantum1435

/-- A pointwise base/maximum bound plus an exceptional-cardinality bound
controls the total score on a selected finite set. -/
theorem sum_le_of_selected_threshold
    {α : Type*} [DecidableEq α]
    (score : α → ℕ) (base maximum exceptionalCap selectedCap : ℕ)
    (hbase : base ≤ maximum)
    (selected : Finset α) (hselected : selected.card ≤ selectedCap)
    (hmaximum : ∀ x ∈ selected, score x ≤ maximum)
    (hexceptional :
      (selected.filter fun x => base < score x).card ≤ exceptionalCap) :
    (∑ x ∈ selected, score x) ≤
      base * selectedCap + (maximum - base) * exceptionalCap := by
  let exceptional := selected.filter fun x => base < score x
  have hpoint : ∀ x ∈ selected,
      score x ≤ base + (maximum - base) * if base < score x then 1 else 0 := by
    intro x hx
    by_cases hhigh : base < score x
    · simp only [hhigh, if_true, mul_one]
      have hxmax := hmaximum x hx
      omega
    · simp only [hhigh, if_false, mul_zero, add_zero]
      omega
  calc
    (∑ x ∈ selected, score x) ≤
        ∑ x ∈ selected,
          (base + (maximum - base) * if base < score x then 1 else 0) :=
      Finset.sum_le_sum hpoint
    _ = base * selected.card + (maximum - base) * exceptional.card := by
      have hindicator := sum_ite_const_eq_mul_card_filter selected
        (fun x => base < score x) (maximum - base)
      rw [Finset.sum_add_distrib]
      have hindicator' :
          (∑ x ∈ selected, if base < score x then maximum - base else 0) =
            (maximum - base) * exceptional.card := by
        simpa [exceptional] using hindicator
      simp only [mul_ite, mul_one, mul_zero]
      rw [hindicator']
      simp [mul_comm]
    _ ≤ base * selectedCap + (maximum - base) * exceptionalCap :=
      Nat.add_le_add (Nat.mul_le_mul_left base hselected)
        (Nat.mul_le_mul_left (maximum - base) hexceptional)

/-- A selected-set degree-sum bound yields the corresponding edge bound from
the usual handshake inequality. -/
theorem edges_le_of_selected_degree_sum
    {α : Type*} [DecidableEq α]
    (score : α → ℕ) (selected : Finset α) (degreeSumBound edges : ℕ)
    (hsum : (∑ x ∈ selected, score x) ≤ degreeSumBound)
    (handshake : 2 * edges ≤ ∑ x ∈ selected, score x) :
    edges ≤ degreeSumBound / 2 := by
  apply (Nat.le_div_iff_mul_le (by decide : 0 < 2)).2
  simpa [mul_comm] using handshake.trans hsum

end Quantum1435
