import Mathlib

namespace I3322

noncomputable section

/-- Worst endpoint-extension coefficient from Lemma XI.1. -/
def endpointCoefficient (E : ℝ) : ℝ := -3 / 2 + 1 / (2 * E)

/-- Strict extension margin for every active finite chain below one third. -/
theorem endpointCoefficient_pos {E : ℝ} (hE0 : 0 < E) (hE : E < 1 / 3) :
    0 < endpointCoefficient E := by
  have hthree : 3 * E < 1 := by nlinarith
  have hrecip : 3 < 1 / E := (lt_div_iff₀ hE0).2 hthree
  have hre : endpointCoefficient E = (1 / E - 3) / 2 := by
    rw [endpointCoefficient]
    field_simp [ne_of_gt hE0]
    ring
  rw [hre]
  nlinarith

/-- Mutation control: at the forbidden threshold the strict margin disappears. -/
theorem endpointCoefficient_at_third : endpointCoefficient (1 / 3) = 0 := by
  norm_num [endpointCoefficient]

/-- Interior stationarity at the first constant-tail site minus tail stationarity. -/
theorem stationarity_boundary_minus_tail
    (cPrev C r s : ℝ) :
    ((cPrev - 1 / 2) + (C + 1 / 2) * r ^ 2 - C * r / s) -
      ((C - 1 / 2) + (C + 1 / 2) * r ^ 2 - C * r / s) = cPrev - C := by
  ring

/-- Equality of the two stationarity equations forces the previous label to equal the tail label. -/
theorem stationarity_propagates_constant_tail
    {cPrev C r s : ℝ}
    (h : (cPrev - 1 / 2) + (C + 1 / 2) * r ^ 2 - C * r / s =
      (C - 1 / 2) + (C + 1 / 2) * r ^ 2 - C * r / s) :
    cPrev = C := by
  have hd := stationarity_boundary_minus_tail cPrev C r s
  linarith

/-- Comparing the Jacobi equations propagates the reciprocal amplitude ratio backwards. -/
theorem jacobi_backward_ratio
    {d s r u : ℝ} (hs : s ≠ 0) (hr : r ≠ 0)
    (h : d + s * (r + 1 / r) / 2 = d + s * (u + r) / 2) :
    u = 1 / r := by
  have h' := h
  field_simp [hr] at h'
  have hfactor : s * (1 - r * u) = 0 := by
    nlinarith [h']
  have hru : 1 - r * u = 0 := (mul_eq_zero.mp hfactor).resolve_left hs
  field_simp [hr]
  nlinarith

/-- A finite left endpoint is incompatible with a positive reciprocal predecessor. -/
theorem missing_predecessor_contradiction
    {lambda r : ℝ} (hl : 0 < lambda) (hr : 0 < r)
    (hmissing : lambda / r = 0) : False := by
  have : 0 < lambda / r := div_pos hl hr
  linarith

end

end I3322
