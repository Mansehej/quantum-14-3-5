import Quantum1435.OddArithmetic
import Mathlib.Tactic

/-!
# Source-row certificate for Identity 51

The external algebra scripts discovered the multipliers below, but Lean
checks their complete expansion.  Consequently the generators and JSON
transcripts are outside this arithmetic theorem's trusted base.

What remains outside this module is the mathematical proof that the actual
stabilizer, shadow, and extension enumerators satisfy these eight source
rows.
-/

namespace Quantum1435

/-- The eight elementary integer rows used to derive Identity 51. -/
structure Identity51SourceRows where
  A1 : ℕ
  A2 : ℕ
  A3 : ℕ
  A4 : ℕ
  A5 : ℕ
  A6 : ℕ
  A7 : ℕ
  A8 : ℕ
  A9 : ℕ
  A10 : ℕ
  A11 : ℕ
  A12 : ℕ
  A13 : ℕ
  A14 : ℕ
  E1 : ℕ
  E4 : ℕ
  total :
    (A1 : ℤ) + A2 + A3 + A4 + A5 + A6 + A7 + A8 + A9 + A10 + A11 +
      A12 + A13 + A14 = 2047
  evenTotal :
    (A2 : ℤ) + A4 + A6 + A8 + A10 + A12 + A14 = 1023
  macWilliams1 :
    -2010 * (A1 : ℤ) + 34 * A2 + 30 * A3 + 26 * A4 + 22 * A5 +
      18 * A6 + 14 * A7 + 10 * A8 + 6 * A9 + 2 * A10 - 2 * A11 -
      6 * A12 - 10 * A13 - 14 * A14 = -42
  macWilliams2 :
    663 * (A1 : ℤ) - 1525 * A2 + 399 * A3 + 291 * A4 + 199 * A5 +
      123 * A6 + 63 * A7 + 19 * A8 - 9 * A9 - 21 * A10 - 17 * A11 +
      3 * A12 + 39 * A13 + 91 * A14 = -819
  macWilliams3 :
    7020 * (A1 : ℤ) + 4788 * A2 + 1020 * A3 + 1796 * A4 + 908 * A5 +
      340 * A6 + 28 * A7 - 92 * A8 - 84 * A9 - 12 * A10 + 60 * A11 +
      68 * A12 - 52 * A13 - 364 * A14 = -9828
  macWilliams4 :
    50193 * (A1 : ℤ) + 28809 * A2 + 14817 * A3 + 4313 * A4 + 1841 * A5 -
      87 * A6 - 511 * A7 - 263 * A8 + 81 * A9 + 201 * A10 + 33 * A11 -
      231 * A12 - 143 * A13 + 1001 * A14 = -81081
  shadow1 :
    34 * (A2 : ℤ) + 26 * A4 + 18 * A6 + 10 * A8 + 2 * A10 - 6 * A12 -
      14 * A14 - 1024 * E1 = -42
  shadow4 :
    28809 * (A2 : ℤ) + 6361 * A4 - 87 * A6 - 263 * A8 + 201 * A10 -
      231 * A12 + 1001 * A14 - 1024 * E4 = -81081

/-- Soundness of the manuscript's Identity-51 row certificate.

The source-row multipliers are
`(-147,-148,-42,-42,-7,-7,8,4)`. -/
theorem identity51_of_sourceRows (d : Identity51SourceRows) :
    168 * d.A1 + 28 * d.A2 + 63 * d.A3 + 15 * d.A4 + 14 * d.A5 +
      4 * d.A6 + 2 * d.A14 + 4 * d.E1 + 2 * d.E4 = 51 := by
  have hscaled :
      (-2048 : ℤ) *
          (168 * d.A1 + 28 * d.A2 + 63 * d.A3 + 15 * d.A4 + 14 * d.A5 +
            4 * d.A6 + 2 * d.A14 + 4 * d.E1 + 2 * d.E4) =
        (-2048 : ℤ) * 51 := by
    linear_combination
      -147 * d.total - 148 * d.evenTotal - 42 * d.macWilliams1 -
      42 * d.macWilliams2 - 7 * d.macWilliams3 - 7 * d.macWilliams4 +
      8 * d.shadow1 + 4 * d.shadow4
  omega

/-- The source rows therefore imply the same three profiles. -/
theorem sourceRows_profile_trichotomy (d : Identity51SourceRows) :
    d.A1 = 0 ∧ d.A3 = 0 ∧
      ((d.A2 = 0 ∧ d.A4 = 1) ∨
       (d.A2 = 0 ∧ d.A4 = 3) ∨
       (d.A2 = 1 ∧ d.A4 = 1)) := by
  let data : Identity51Data :=
    { A1 := d.A1
      A2 := d.A2
      A3 := d.A3
      A4 := d.A4
      A5 := d.A5
      A6 := d.A6
      A14 := d.A14
      E1 := d.E1
      E4 := d.E4
      identity := identity51_of_sourceRows d }
  exact identity51_profile_trichotomy data

end Quantum1435
