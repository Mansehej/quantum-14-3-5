import Mathlib

namespace I3322

/-- A transparent real `2 × 2` matrix used for the exact block calculations. -/
structure Mat2 where
  a11 : ℝ
  a12 : ℝ
  a21 : ℝ
  a22 : ℝ
  deriving Repr

namespace Mat2

/-- Explicit matrix multiplication. -/
def mul (A B : Mat2) : Mat2 :=
  ⟨A.a11 * B.a11 + A.a12 * B.a21,
   A.a11 * B.a12 + A.a12 * B.a22,
   A.a21 * B.a11 + A.a22 * B.a21,
   A.a21 * B.a12 + A.a22 * B.a22⟩

/-- The identity block. -/
def one : Mat2 := ⟨1, 0, 0, 1⟩

/-- The real reflection block with cosine/sine parameters. -/
def reflection (c s : ℝ) : Mat2 := ⟨c, s, s, -c⟩

/-- The outcome-one projector `(I + R)/2` associated with a reflection block. -/
def projector (c s : ℝ) : Mat2 :=
  ⟨(1 + c) / 2, s / 2, s / 2, (1 - c) / 2⟩

/-- The reflection squares to the identity when `c²+s²=1`. -/
theorem reflection_mul_self {c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) :
    mul (reflection c s) (reflection c s) = one := by
  apply Mat2.ext <;> simp [mul, reflection, one] <;> nlinarith

/-- The corresponding outcome-one block is an exact projector. -/
theorem projector_mul_self {c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) :
    mul (projector c s) (projector c s) = projector c s := by
  apply Mat2.ext <;> simp [mul, projector] <;> nlinarith

/-- A sign-corrupted block used as a negative control. -/
def wrongSignReflection (c s : ℝ) : Mat2 := ⟨c, s, -s, -c⟩

/-- Mutation control: the wrong off-diagonal sign is not a reflection. -/
theorem wrong_sign_not_reflection :
    mul (wrongSignReflection 0 1) (wrongSignReflection 0 1) ≠ one := by
  intro h
  have h11 := congrArg Mat2.a11 h
  norm_num [mul, wrongSignReflection, one] at h11

end Mat2

/-- Convert a dichotomic observable value to its outcome-one effect value. -/
def effectOfObservable (x : ℝ) : ℝ := (1 + x) / 2

/-- The Pál--Vértesi/Connor ordering of `I3322`, in scalar commuting form. -/
def bellPVScalar (A1 A2 A3 B1 B2 B3 : ℝ) : ℝ :=
  -A2 - B1 - 2 * B2
    + A1 * B1 + A1 * B2 - A1 * B3
    + A2 * B1 + A2 * B2 + A2 * B3
    - A3 * B1 + A3 * B2

/-- Alice's average observable. -/
def xAlice (a1 a2 : ℝ) : ℝ := (a1 + a2) / 2

/-- Alice's difference observable. -/
def zAlice (a1 a2 : ℝ) : ℝ := (a1 - a2) / 2

/-- The sign-reversed Bob average used in the audited expansion. -/
def yBob (b1 b2 : ℝ) : ℝ := -(b1 + b2) / 2

/-- Bob's difference observable. -/
def zBob (b1 b2 : ℝ) : ℝ := (b1 - b2) / 2

/-- Exact scalar recomputation of `4 + 4 I3322` in observable variables.

This is the commuting scalar polynomial underlying the operator identity. The
noncommutative spectral-functional-calculus passage is intentionally not
claimed here. -/
theorem scalar_observable_expansion
    (a1 a2 a3 b1 b2 b3 : ℝ) :
    4 + 4 * bellPVScalar
      (effectOfObservable a1) (effectOfObservable a2) (effectOfObservable a3)
      (effectOfObservable b1) (effectOfObservable b2) (effectOfObservable b3)
      =
    2 * xAlice a1 a2 + 2 * yBob b1 b2
      - 4 * xAlice a1 a2 * yBob b1 b2
      - 2 * zAlice a1 a2 * b3
      - 2 * zBob b1 b2 * a3 := by
  simp [bellPVScalar, effectOfObservable, xAlice, zAlice, yBob, zBob]
  ring

/-- Exact rational witness value used only to prove a strict gap above `1/4`. -/
theorem exact_rational_witness_above_quarter :
    (231482383 : ℚ) / 925444000 > 1 / 4 := by
  norm_num

end I3322
