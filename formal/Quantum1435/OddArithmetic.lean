import Quantum1435.Parity
import Mathlib.Tactic

/-!
# Kernel-checked arithmetic of the odd branch

This module checks the Presburger-arithmetic consequences used after the
MacWilliams, shadow, extension, and finite-geometry reductions.  Each record
states its reduction hypotheses explicitly.  Thus these theorems do not
silently assume that an arbitrary stabilizer has already been transported to
the manuscript's certificate data.
-/

namespace Quantum1435

/-- Nonnegative coefficients occurring in Identity 51. -/
structure Identity51Data where
  A1 : ℕ
  A2 : ℕ
  A3 : ℕ
  A4 : ℕ
  A5 : ℕ
  A6 : ℕ
  A14 : ℕ
  E1 : ℕ
  E4 : ℕ
  identity :
    168 * A1 + 28 * A2 + 63 * A3 + 15 * A4 + 14 * A5 + 4 * A6 +
      2 * A14 + 4 * E1 + 2 * E4 = 51

/-- Identity 51 leaves exactly the three low-weight profiles in the
manuscript. -/
theorem identity51_profile_trichotomy (d : Identity51Data) :
    d.A1 = 0 ∧ d.A3 = 0 ∧
      ((d.A2 = 0 ∧ d.A4 = 1) ∨
       (d.A2 = 0 ∧ d.A4 = 3) ∨
       (d.A2 = 1 ∧ d.A4 = 1)) := by
  rcases d with ⟨A1, A2, A3, A4, A5, A6, A14, E1, E4, hi⟩
  simp only at hi ⊢
  have hA1 : A1 = 0 := by omega
  have hA3 : A3 = 0 := by omega
  subst A1
  subst A3
  have hA4le : A4 ≤ 3 := by omega
  have hA4odd : A4 % 2 = 1 := by omega
  omega

/-- The two universal branch formulas, with denominators and subtraction
cleared so every quantity remains a natural word count. -/
structure OddUniversalRows where
  A2 : ℕ
  A4 : ℕ
  A5 : ℕ
  A6 : ℕ
  A14 : ℕ
  S2 : ℕ
  S3 : ℕ
  S4 : ℕ
  a14Row :
    A14 + 18 * A2 + 12 * A4 + 12 * A5 + 3 * A6 + 4 * S2 + 2 * S4 = 36
  s3Row :
    2 * S3 + 12 * A2 + 19 * A4 + 38 * A5 + 6 * A6 +
      36 * S2 + 8 * S4 = 105

/-- Arithmetic data remaining in profile `(A₂,A₄)=(1,1)` after the
geometric overlap argument has supplied `A₆ ≥ 1`. -/
structure P11ArithmeticData where
  A5 : ℕ
  A6 : ℕ
  A14 : ℕ
  S1 : ℕ
  S2 : ℕ
  S4 : ℕ
  identitySpecialized :
    14 * A5 + 4 * A6 + 2 * A14 + 4 * S1 + 2 * S4 = 6
  a6Positive : 1 ≤ A6
  a14Row : A14 + 12 * A5 + 3 * A6 + 4 * S2 + 2 * S4 = 6

/-- The p11 arithmetic subsystem has no nonnegative integral solution. -/
theorem noP11ArithmeticData : ¬ Nonempty P11ArithmeticData := by
  rintro ⟨d⟩
  have hi := d.identitySpecialized
  have hp := d.a6Positive
  have ha := d.a14Row
  omega

/-- The exact specialized formulas and incidence bounds used in profile
`(A₂,A₄)=(0,1)`.  The bound fields are semantic finite-geometry obligations;
the theorem below verifies that they suffice. -/
structure P01ArithmeticData where
  A5 : ℕ
  A6 : ℕ
  A14 : ℕ
  S1 : ℕ
  S2 : ℕ
  S3 : ℕ
  S4 : ℕ
  a6Row : A6 + 5 * A5 + 4 * S2 + S4 = 7 + 2 * S1
  a14Row : A14 + 6 * S1 = 3 + 3 * A5 + 8 * S2 + S4
  s3Row : S3 + 4 * A5 + 6 * S2 + S4 + 6 * S1 = 22
  s1LeOne : S1 ≤ 1
  s1One : S1 = 1 → S2 = 0 ∧ S3 ≤ 1
  fortyTwoBinBound : S1 = 0 → S3 ≤ 14
  thirtySixBinBound : S1 = 0 → S2 = 1 → S3 ≤ 12

/-- The three p01 cases are exhaustive and each contradicts the exact
coefficient formulas. -/
theorem noP01ArithmeticData : ¬ Nonempty P01ArithmeticData := by
  rintro ⟨d⟩
  have ha6 := d.a6Row
  have hs3 := d.s3Row
  have hs1le := d.s1LeOne
  by_cases hs1 : d.S1 = 0
  · have hs2 : d.S2 ≤ 1 := by omega
    by_cases hs20 : d.S2 = 0
    · have hb := d.fortyTwoBinBound hs1
      omega
    · have hs21 : d.S2 = 1 := by omega
      have hb := d.thirtySixBinBound hs1 hs21
      omega
  · have hs11 : d.S1 = 1 := by omega
    obtain ⟨hs20, hb⟩ := d.s1One hs11
    omega

/-- The p03 coefficient subsystem before its forced values are extracted. -/
structure P03ForcedData where
  A5 : ℕ
  A6 : ℕ
  A14 : ℕ
  S1 : ℕ
  S2 : ℕ
  S3 : ℕ
  S4 : ℕ
  identityRemainder :
    14 * A5 + 4 * A6 + 2 * A14 + 4 * S1 + 2 * S4 = 0
  a14Row : A14 + 12 * A5 + 3 * A6 + 4 * S2 + 2 * S4 = 0
  s3Row :
    2 * S3 + 38 * A5 + 6 * A6 + 36 * S2 + 8 * S4 = 48

/-- Profile p03 forces the exact enumerator coefficients needed by the
collision argument. -/
theorem p03_forced_counts (d : P03ForcedData) :
    d.A5 = 0 ∧ d.A6 = 0 ∧ d.A14 = 0 ∧ d.S1 = 0 ∧ d.S2 = 0 ∧
      d.S4 = 0 ∧ d.S3 = 24 := by
  have hi := d.identityRemainder
  have ha := d.a14Row
  have hs := d.s3Row
  omega

/-- The four normal forms used by the p03 finite collision computation. -/
inductive P03NormalForm
  | rankTwo0
  | rankTwo1
  | rankTwo2
  | rankThree
  deriving DecidableEq, Repr

/-- Upper-bound values recorded by the external finite computation. The
exact collision histograms are not replayed here; the final semantic proof
instead establishes sufficient representative-free upper bounds. -/
def p03CollisionUpperBound : P03NormalForm → ℕ
  | .rankTwo0 => 12
  | .rankTwo1 => 13
  | .rankTwo2 => 28
  | .rankThree => 12

/-- Closed kernel check that every recorded p03 upper bound is below the
30-edge incidence lower bound. -/
theorem p03CollisionUpperBound_lt_thirty (f : P03NormalForm) :
    p03CollisionUpperBound f < 30 := by
  cases f <;> decide

/-- Once completeness of the normal-form enumeration supplies one of the
four upper bounds, the p03 collision inequalities are inconsistent. -/
theorem p03_collision_contradiction (f : P03NormalForm) (edges : ℕ)
    (lower : 30 ≤ edges) (upper : edges ≤ p03CollisionUpperBound f) : False := by
  have hlt := p03CollisionUpperBound_lt_thirty f
  omega

end Quantum1435
