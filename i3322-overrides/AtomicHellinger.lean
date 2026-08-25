import Mathlib

namespace I3322

/-- Square-root-coordinate form of one reflected atomic Hellinger pair cost. -/
def atomicPairCost (P Q G H : ℝ) : ℝ :=
  P ^ 2 * G ^ 2 + Q ^ 2 * H ^ 2

/-- Exact finite atomic Hellinger lower bound.

Here `P²,Q²` are the two masses and `G²,H²` the two positive dual values.
The condition `GH ≥ 2s` is the square-root form of the reflected product
constraint. -/
theorem atomic_pair_lower_bound
    {P Q G H s : ℝ}
    (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hGH : 2 * s ≤ G * H) :
    4 * s * P * Q ≤ atomicPairCost P Q G H := by
  have hpq : 0 ≤ 2 * P * Q := by positivity
  have hscaled : 0 ≤ (2 * P * Q) * (G * H - 2 * s) :=
    mul_nonneg hpq (sub_nonneg.mpr hGH)
  have hsquare : 0 ≤ (P * G - Q * H) ^ 2 := sq_nonneg _
  simp [atomicPairCost] at *
  nlinarith

/-- Equality in the atomic lower bound under exact matching and product contact. -/
theorem atomic_pair_contact_value
    {P Q G H s : ℝ}
    (hmatch : P * G = Q * H)
    (hcontact : G * H = 2 * s) :
    atomicPairCost P Q G H = 4 * s * P * Q := by
  have hrewrite : atomicPairCost P Q G H = (P * G) ^ 2 + (Q * H) ^ 2 := by
    simp [atomicPairCost]
    ring
  rw [hrewrite, hmatch]
  rw [← hmatch]
  rw [hcontact]
  ring

/-- Reflection exchanges the two masses and the two dual values. -/
theorem atomic_pair_reflection (P Q G H : ℝ) :
    atomicPairCost P Q G H = atomicPairCost Q P H G := by
  simp [atomicPairCost]
  ring

/-- Two-point countermonotone rearrangement inequality. -/
theorem two_point_countermonotone
    {x1 x2 y1 y2 : ℝ}
    (hx : x1 ≤ x2) (hy : y1 ≤ y2) :
    x1 * y2 + x2 * y1 ≤ x1 * y1 + x2 * y2 := by
  have hp : 0 ≤ (x2 - x1) * (y2 - y1) :=
    mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hy)
  nlinarith

/-- Mutation control: same-order pairing is strictly more expensive in a simple case. -/
theorem same_order_pairing_strict_counterexample :
    (0 : ℝ) * 0 + 1 * 1 > 0 * 1 + 1 * 0 := by
  norm_num

end I3322
