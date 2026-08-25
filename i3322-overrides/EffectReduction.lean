import Mathlib
import I3322.BellAlgebra

open scoped BigOperators

namespace I3322

/-- A diagonal finite effect: every coordinate lies in `[0,1]`. -/
def IsDiagonalEffect {ι : Type*} (e : ι → ℝ) : Prop :=
  ∀ i, 0 ≤ e i ∧ e i ≤ 1

/-- The coordinatewise positive-spectral projection of a real weight. -/
def responseProjection {ι : Type*} (w : ι → ℝ) : ι → ℝ :=
  fun i => if 0 < w i then 1 else 0

/-- A finite diagonal linear objective. -/
def diagonalObjective {ι : Type*} [Fintype ι] (w e : ι → ℝ) : ℝ :=
  ∑ i, w i * e i

/-- The best-response replacement is itself an effect and is projection-valued. -/
theorem responseProjection_is_effect {ι : Type*} (w : ι → ℝ) :
    IsDiagonalEffect (responseProjection w) := by
  intro i
  by_cases h : 0 < w i <;> simp [responseProjection, h]

/-- Finite-dimensional diagonal effect-to-projection reduction.

For a fixed linear objective, replacing each effect coordinate by the positive
spectral projection never decreases the value. -/
theorem diagonal_objective_le_response
    {ι : Type*} [Fintype ι]
    (w e : ι → ℝ) (he : IsDiagonalEffect e) :
    diagonalObjective w e ≤ diagonalObjective w (responseProjection w) := by
  classical
  unfold diagonalObjective
  apply Finset.sum_le_sum
  intro i hi
  by_cases hw : 0 < w i
  · change w i * e i ≤ w i * (if 0 < w i then 1 else 0)
    rw [if_pos hw]
    exact mul_le_mul_of_nonneg_left (he i).2 (le_of_lt hw)
  · change w i * e i ≤ w i * (if 0 < w i then 1 else 0)
    rw [if_neg hw, mul_zero]
    exact mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hw) (he i).1

/-- The transparent scalar Halmos dilation block. -/
def halmosBlock (e r : ℝ) : Mat2 := ⟨e, r, r, 1 - e⟩

/-- Exact idempotence of the Halmos block under `r²=e(1-e)`. -/
theorem halmosBlock_mul_self
    {e r : ℝ} (hr : r ^ 2 = e * (1 - e)) :
    Mat2.mul (halmosBlock e r) (halmosBlock e r) = halmosBlock e r := by
  apply Mat2.ext <;> simp [Mat2.mul, halmosBlock] <;> nlinarith

/-- Compression to the first coordinate recovers the original effect. -/
theorem halmosBlock_compression (e r : ℝ) :
    (halmosBlock e r).a11 = e := by
  rfl

/-- Mutation control: omitting the off-diagonal square-root term destroys idempotence. -/
theorem zero_offDiagonal_halmos_not_projector :
    Mat2.mul (halmosBlock (1 / 2) 0) (halmosBlock (1 / 2) 0)
      ≠ halmosBlock (1 / 2) 0 := by
  intro h
  have h11 := congrArg Mat2.a11 h
  norm_num [Mat2.mul, halmosBlock] at h11

end I3322
