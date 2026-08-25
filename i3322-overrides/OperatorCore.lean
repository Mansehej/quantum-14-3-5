import Mathlib
import I3322.BellAlgebra

namespace I3322

/-- The real quadratic form of the reflected two-point operator block. -/
def reflectedQuadratic (g h z u v : ℝ) : ℝ :=
  g * u ^ 2 + 4 * z * u * v + h * v ^ 2

/-- Exact completion-of-the-square identity for the reflected block. -/
theorem reflectedQuadratic_sos_identity
    {g h z u v : ℝ} (hg : g ≠ 0) :
    reflectedQuadratic g h z u v
      = g * (u + (2 * z / g) * v) ^ 2
        + (h - 4 * z ^ 2 / g) * v ^ 2 := by
  field_simp [reflectedQuadratic, hg]
  ring

/-- The key finite-block positivity certificate.

This is the exact `2 × 2` sum-of-squares core of the dimension-free operator
inequality. The passage from this block identity to `g(X)` by spectral
functional calculus is deliberately outside the unconditional kernel scope. -/
theorem reflected_product_quadratic_nonnegative
    {g h z u v : ℝ}
    (hg : 0 < g) (hh : 0 ≤ h) (hdet : 4 * z ^ 2 ≤ g * h) :
    0 ≤ reflectedQuadratic g h z u v := by
  have hg0 : g ≠ 0 := ne_of_gt hg
  have hrest : 0 ≤ h - 4 * z ^ 2 / g := by
    rw [sub_nonneg]
    exact (div_le_iff₀ hg).2 hdet
  rw [reflectedQuadratic_sos_identity hg0]
  exact add_nonneg
    (mul_nonneg (le_of_lt hg) (sq_nonneg _))
    (mul_nonneg hrest (sq_nonneg _))

/-- Equivalent cross-term estimate extracted from the positive block. -/
theorem reflected_cross_term_bound
    {g h z u v : ℝ}
    (hg : 0 < g) (hh : 0 ≤ h) (hdet : 4 * z ^ 2 ≤ g * h) :
    -4 * z * u * v ≤ g * u ^ 2 + h * v ^ 2 := by
  have hq := reflected_product_quadratic_nonnegative
    (g := g) (h := h) (z := z) (u := u) (v := v) hg hh hdet
  simp [reflectedQuadratic] at hq
  linarith

/-- The reflected product hypothesis follows from `z²=1-x²`. -/
theorem reflected_interval_to_determinant
    {x z g h : ℝ}
    (hz : z ^ 2 = 1 - x ^ 2)
    (hprod : 4 * (1 - x ^ 2) ≤ g * h) :
    4 * z ^ 2 ≤ g * h := by
  nlinarith

/-- The elementary exact upper constant appearing in the audited proof. -/
def goldenUpper : ℝ := (Real.sqrt 5 - 1) / 4

/-- The elementary upper constant is strictly below the extension threshold `1/3`. -/
theorem goldenUpper_lt_one_third : goldenUpper < 1 / 3 := by
  have hs : (Real.sqrt 5) ^ 2 = (5 : ℝ) := by
    simpa using Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  have hn : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  simp [goldenUpper]
  nlinarith

/-- Mutation control: without the reflected-product determinant condition the form is negative. -/
theorem missing_reflected_product_counterexample :
    reflectedQuadratic (3 / 2) (3 / 2) 1 1 (-1) = -1 := by
  norm_num [reflectedQuadratic]

end I3322
