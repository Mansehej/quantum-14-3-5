import Mathlib

namespace I3322

/-- The worst-case first-order endpoint extension margin. -/
def extensionMargin (E : ℝ) : ℝ :=
  -3 / 2 + 1 / (2 * E)

/-- The endpoint extension margin is positive precisely on the side used by the proof. -/
theorem extensionMargin_positive
    {E : ℝ} (hE0 : 0 < E) (hE : E < 1 / 3) :
    0 < extensionMargin E := by
  have hnum : 0 < 1 - 3 * E := by nlinarith
  have hden : 0 < 2 * E := by positivity
  have hid : extensionMargin E = (1 - 3 * E) / (2 * E) := by
    field_simp [extensionMargin, ne_of_gt hE0]
    ring
  rw [hid]
  exact div_pos hnum hden

/-- Mutation control: at the forbidden threshold the strict margin disappears. -/
theorem extensionMargin_at_one_third :
    extensionMargin (1 / 3) = 0 := by
  norm_num [extensionMargin]

/-- The stationary equality kernel propagates an eventually constant label backwards. -/
theorem stationarity_propagates_previous_label
    {cPrev C lambda : ℝ}
    (hlambda : lambda ≠ 0)
    (hstationary : (cPrev - C) * lambda ^ 2 = 0) :
    cPrev = C := by
  have hlambdaSq : lambda ^ 2 ≠ 0 := pow_ne_zero 2 hlambda
  rcases mul_eq_zero.mp hstationary with hdiff | hsq
  · exact sub_eq_zero.mp hdiff
  · exact False.elim (hlambdaSq hsq)

/-- The Jacobi recurrence propagates the geometric amplitude ratio backwards. -/
theorem jacobi_reverse_step
    {r previous current : ℝ}
    (hr : r ≠ 0) (hstep : current = r * previous) :
    previous = current / r := by
  rw [hstep]
  field_simp [hr]

/-- A finite chain with a missing predecessor and a nonzero geometric ratio is identically zero. -/
theorem finite_geometric_chain_zero
    {r : ℝ} (hr : r ≠ 0)
    (v : ℕ → ℝ)
    (hleft : v 0 = 0)
    (hrec : ∀ n, v (n + 1) = r * v n) :
    ∀ n, v n = 0 := by
  intro n
  induction n with
  | zero => exact hleft
  | succ n ih =>
      rw [hrec n, ih, mul_zero]

/-- Mutation control: dropping the missing-predecessor boundary allows a nonzero geometric chain. -/
theorem dropping_boundary_allows_nonzero_geometric_chain :
    ∃ v : ℕ → ℝ,
      (∀ n, v (n + 1) = 2 * v n) ∧ v 0 = 1 := by
  refine ⟨fun n => (2 : ℝ) ^ n, ?_, ?_⟩
  · intro n
    rw [pow_succ]
    ring
  · norm_num

end I3322
