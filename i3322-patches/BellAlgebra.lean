import Mathlib

namespace I3322

noncomputable section

/-- A transparent two-by-two real matrix used for the exact block algebra. -/
structure Mat2 where
  a11 : ℝ
  a12 : ℝ
  a21 : ℝ
  a22 : ℝ

namespace Mat2

instance : Zero Mat2 := ⟨⟨0, 0, 0, 0⟩⟩
instance : One Mat2 := ⟨⟨1, 0, 0, 1⟩⟩
instance : Add Mat2 := ⟨fun A B => ⟨A.a11 + B.a11, A.a12 + B.a12,
  A.a21 + B.a21, A.a22 + B.a22⟩⟩
instance : Neg Mat2 := ⟨fun A => ⟨-A.a11, -A.a12, -A.a21, -A.a22⟩⟩
instance : Sub Mat2 := ⟨fun A B => A + (-B)⟩
instance : SMul ℝ Mat2 := ⟨fun r A => ⟨r * A.a11, r * A.a12, r * A.a21, r * A.a22⟩⟩
instance : Mul Mat2 := ⟨fun A B =>
  ⟨A.a11 * B.a11 + A.a12 * B.a21,
   A.a11 * B.a12 + A.a12 * B.a22,
   A.a21 * B.a11 + A.a22 * B.a21,
   A.a21 * B.a12 + A.a22 * B.a22⟩⟩

@[ext] theorem ext {A B : Mat2}
    (h11 : A.a11 = B.a11) (h12 : A.a12 = B.a12)
    (h21 : A.a21 = B.a21) (h22 : A.a22 = B.a22) : A = B := by
  cases A
  cases B
  simp_all

/-- The canonical reflection block with cosine `c` and sine `s`. -/
def reflection (c s : ℝ) : Mat2 := ⟨c, s, s, -c⟩

/-- The reflection squares to the identity exactly when `c²+s²=1`. -/
theorem reflection_sq (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) :
    reflection c s * reflection c s = 1 := by
  apply ext
  · change c * c + s * s = 1
    nlinarith [h]
  · change c * s + s * (-c) = 0
    ring
  · change s * c + (-c) * s = 0
    ring
  · change s * s + (-c) * (-c) = 1
    nlinarith [h]

/-- The binary effect associated with a reflection. -/
def effectOfReflection (c s : ℝ) : Mat2 :=
  ⟨(1 + c) / 2, s / 2, s / 2, (1 - c) / 2⟩

/-- Every canonical reflected effect is idempotent. -/
theorem effectOfReflection_sq (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) :
    effectOfReflection c s * effectOfReflection c s = effectOfReflection c s := by
  apply ext
  · change ((1 + c) / 2) * ((1 + c) / 2) + (s / 2) * (s / 2) = (1 + c) / 2
    nlinarith [h]
  · change ((1 + c) / 2) * (s / 2) + (s / 2) * ((1 - c) / 2) = s / 2
    ring
  · change (s / 2) * ((1 + c) / 2) + ((1 - c) / 2) * (s / 2) = s / 2
    ring
  · change (s / 2) * (s / 2) + ((1 - c) / 2) * ((1 - c) / 2) = (1 - c) / 2
    nlinarith [h]

end Mat2

section NoncommutativeExpansion

variable {R : Type*} [Ring R]

/-- The effect-form Bell polynomial in the Pál--Vértesi setting order. -/
def bellPV (A₁ A₂ A₃ B₁ B₂ B₃ : R) : R :=
  -A₂ - B₁ - 2 * B₂
    + A₁ * B₁ + A₁ * B₂ - A₁ * B₃
    + A₂ * B₁ + A₂ * B₂ + A₂ * B₃
    - A₃ * B₁ + A₃ * B₂

/-- Convert an effect to its associated reflection. -/
def refl (A : R) : R := 2 * A - 1

/-- The exact noncommutative observable expansion before commuting the final cross term. -/
theorem bell_observable_expansion (A₁ A₂ A₃ B₁ B₂ B₃ : R) :
    4 + 4 * bellPV A₁ A₂ A₃ B₁ B₂ B₃ =
      (refl A₁ + refl A₂)
      - (refl B₁ + refl B₂)
      + (refl A₁ + refl A₂) * (refl B₁ + refl B₂)
      - (refl A₁ - refl A₂) * refl B₃
      - refl A₃ * (refl B₁ - refl B₂) := by
  simp only [bellPV, refl]
  noncomm_ring <;> abel

/-- Cross-party commutation permits the audited Bob-before-Alice ordering. -/
theorem commute_final_cross_term (A₃ B₁ B₂ : R)
    (h₁ : A₃ * B₁ = B₁ * A₃) (h₂ : A₃ * B₂ = B₂ * A₃) :
    refl A₃ * (refl B₁ - refl B₂) = (refl B₁ - refl B₂) * refl A₃ := by
  have hD : A₃ * (B₁ - B₂) = (B₁ - B₂) * A₃ := by
    calc
      A₃ * (B₁ - B₂) = A₃ * B₁ - A₃ * B₂ := by noncomm_ring
      _ = B₁ * A₃ - B₂ * A₃ := by rw [h₁, h₂]
      _ = (B₁ - B₂) * A₃ := by noncomm_ring
  simp only [refl]
  calc
    (2 * A₃ - 1) * (2 * B₁ - 1 - (2 * B₂ - 1)) =
        4 * (A₃ * (B₁ - B₂)) - 2 * (B₁ - B₂) := by noncomm_ring
    _ = 4 * ((B₁ - B₂) * A₃) - 2 * (B₁ - B₂) := by rw [hD]
    _ = (2 * B₁ - 1 - (2 * B₂ - 1)) * (2 * A₃ - 1) := by noncomm_ring

end NoncommutativeExpansion

/-- Rational cosine and sine used in the exact geometric witness. -/
def witnessC : ℚ := 56 / 65
def witnessSC : ℚ := 33 / 65
def witnessB : ℚ := 3 / 5
def witnessSB : ℚ := 4 / 5
def witnessR : ℚ := 35 / 36
def witnessT : ℚ := 8 / 9

def witnessDenominator : ℚ :=
  2 * witnessT ^ 2 + 2 / (1 - witnessR ^ 2)

def witnessNumerator : ℚ :=
  (witnessB - 1) * witnessT ^ 2 + 2 * witnessSB * witnessT
    + 2 * (witnessC * witnessB + (witnessC - witnessB) / 2 - 1)
    + 2 * ((witnessC ^ 2 - 1) * witnessR ^ 2 + witnessSC * witnessR) /
      (1 - witnessR ^ 2)

def exactGeometricWitness : ℚ := witnessNumerator / witnessDenominator

/-- Lean recomputes both Pythagorean identities used by the block construction. -/
theorem witness_pythagorean :
    witnessC ^ 2 + witnessSC ^ 2 = 1 ∧ witnessB ^ 2 + witnessSB ^ 2 = 1 := by
  norm_num [witnessC, witnessSC, witnessB, witnessSB]

/-- Exact value of the audited rational lower witness. -/
theorem exact_geometric_witness_value :
    exactGeometricWitness = 231482383 / 925444000 := by
  norm_num [exactGeometricWitness, witnessNumerator, witnessDenominator,
    witnessC, witnessSC, witnessB, witnessSB, witnessR, witnessT]

/-- The exact witness is strictly above the qubit/qutrit quarter ceiling. -/
theorem exact_geometric_witness_above_quarter :
    (1 / 4 : ℚ) < exactGeometricWitness := by
  rw [exact_geometric_witness_value]
  norm_num

end

end I3322
