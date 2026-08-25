import Mathlib

namespace I3322

/-- Exact sum-of-squares identity behind the reflected-product inequality. -/
theorem quadratic_sos_identity (a b c x y : ℝ) :
    a * (a * x ^ 2 + b * y ^ 2 - 2 * c * x * y) =
      (a * x - c * y) ^ 2 + (a * b - c ^ 2) * y ^ 2 := by
  ring

/-- Scalar quadratic positivity, including the singular case `a=0`. -/
theorem quadratic_nonnegative {a b c x y : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : c ^ 2 ≤ a * b) :
    0 ≤ a * x ^ 2 + b * y ^ 2 - 2 * c * x * y := by
  by_cases hza : a = 0
  · have hc0 : c = 0 := by
      subst a
      have : c ^ 2 ≤ 0 := by simpa using hc
      nlinarith [sq_nonneg c]
    subst a
    subst c
    simpa using mul_nonneg hb (sq_nonneg y)
  · have hpa : 0 < a := lt_of_le_of_ne ha (Ne.symm hza)
    have hsos : 0 ≤ (a * x - c * y) ^ 2 + (a * b - c ^ 2) * y ^ 2 := by
      have hgap : 0 ≤ a * b - c ^ 2 := sub_nonneg.mpr hc
      positivity
    rw [← quadratic_sos_identity] at hsos
    have hsos' : 0 ≤ (a * x ^ 2 + b * y ^ 2 - 2 * c * x * y) * a := by
      simpa [mul_comm] using hsos
    exact nonneg_of_mul_nonneg_left hsos' hpa

/-- The scalar two-fibre version of the dimension-free operator remainder. -/
theorem reflected_product_quadratic {gPlus gMinus s u v : ℝ}
    (hp : 0 ≤ gPlus) (hm : 0 ≤ gMinus)
    (hprod : 4 * s ^ 2 ≤ gPlus * gMinus) :
    0 ≤ gPlus * u ^ 2 + gMinus * v ^ 2 - 4 * s * u * v := by
  have hc : (2 * s) ^ 2 ≤ gPlus * gMinus := by nlinarith
  have hq := quadratic_nonnegative (a := gPlus) (b := gMinus) (c := 2 * s)
    (x := u) (y := v) hp hm hc
  nlinarith [hq]

/-- Quadratic-form consequence when a cross term is bounded by Cauchy--Schwarz. -/
theorem dimension_free_cross_term {gPlus gMinus s u v q : ℝ}
    (hp : 0 ≤ gPlus) (hm : 0 ≤ gMinus) (hs : 0 ≤ s)
    (hprod : 4 * s ^ 2 ≤ gPlus * gMinus)
    (hq : -u * v ≤ q) :
    0 ≤ gPlus * u ^ 2 + gMinus * v ^ 2 + 4 * s * q := by
  have hcore := reflected_product_quadratic hp hm hprod (u := u) (v := v)
  have hcross : -4 * s * u * v ≤ 4 * s * q := by
    nlinarith
  linarith

/-- The exact perfect-square identity used for the elementary upper bound. -/
theorem analytic_upper_factorization (x : ℝ) :
    let r5 := Real.sqrt 5
    let R := -2 * x ^ 2 + (1 - r5) * x + (1 + 3 * r5) / 2
    R ^ 2 - 4 * (1 - x ^ 2) * (4 * x ^ 2 - 4 * x + 2) =
      20 * (x ^ 2 + (-1 / 2 + r5 / 10) * x - 1 / 4 - 3 * r5 / 20) ^ 2 := by
  dsimp
  have hs : (Real.sqrt 5) ^ 2 = 5 := by norm_num
  ring_nf
  simp only [hs]
  ring

/-- The elementary constant is strictly below one third. -/
theorem golden_upper_lt_one_third :
    (Real.sqrt 5 - 1) / 4 < (1 / 3 : ℝ) := by
  have hs0 : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have hs2 : (Real.sqrt 5) ^ 2 = 5 := by norm_num
  have hslt : Real.sqrt 5 < 7 / 3 := by
    by_contra h
    have hge : 7 / 3 ≤ Real.sqrt 5 := le_of_not_gt h
    nlinarith
  nlinarith

/-- Mutation control datum: the harmless sign choice is positive. -/
theorem violated_product_has_negative_vector :
    (3 / 2 : ℝ) * 1 ^ 2 + (3 / 2 : ℝ) * (-1) ^ 2 - 4 * 1 * 1 * (-1) > 0 := by
  norm_num

/-- The genuinely hostile sign choice for the same infeasible data is negative. -/
theorem violated_product_negative_cross :
    (3 / 2 : ℝ) * 1 ^ 2 + (3 / 2 : ℝ) * 1 ^ 2 - 4 * 1 * 1 * 1 = -1 := by
  norm_num

end I3322
