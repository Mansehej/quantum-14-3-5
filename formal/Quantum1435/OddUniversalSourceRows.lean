import Mathlib.Data.Int.Basic

/-!
# Pure integer source rows for the universal odd formulas

Keeping these rows independent of the concrete stabilizer definitions makes
the arithmetic certificate small enough to elaborate with bounded memory.
-/

namespace Quantum1435

/-- The integer equations from which the two universal odd-branch rows are
derived. Keeping this certificate interface semantic-free bounds elaboration
memory without adding assumptions to the final proof. -/
structure OddUniversalSourceRows where
  A1 : ℤ
  A2 : ℤ
  A3 : ℤ
  A4 : ℤ
  A5 : ℤ
  A6 : ℤ
  A7 : ℤ
  A8 : ℤ
  A9 : ℤ
  A10 : ℤ
  A11 : ℤ
  A12 : ℤ
  A13 : ℤ
  A14 : ℤ
  S2 : ℤ
  S3 : ℤ
  S4 : ℤ
  a1Zero : A1 = 0
  a3Zero : A3 = 0
  total :
    A1 + A2 + A3 + A4 + A5 + A6 + A7 + A8 + A9 + A10 + A11 +
      A12 + A13 + A14 = 2047
  evenTotal : A2 + A4 + A6 + A8 + A10 + A12 + A14 = 1023
  macWilliams1 :
    -2010 * A1 + 34 * A2 + 30 * A3 + 26 * A4 + 22 * A5 +
      18 * A6 + 14 * A7 + 10 * A8 + 6 * A9 + 2 * A10 - 2 * A11 -
      6 * A12 - 10 * A13 - 14 * A14 = -42
  macWilliams2 :
    663 * A1 - 1525 * A2 + 399 * A3 + 291 * A4 + 199 * A5 +
      123 * A6 + 63 * A7 + 19 * A8 - 9 * A9 - 21 * A10 - 17 * A11 +
      3 * A12 + 39 * A13 + 91 * A14 = -819
  macWilliams3 :
    7020 * A1 + 4788 * A2 + 1020 * A3 + 1796 * A4 + 908 * A5 +
      340 * A6 + 28 * A7 - 92 * A8 - 84 * A9 - 12 * A10 + 60 * A11 +
      68 * A12 - 52 * A13 - 364 * A14 = -9828
  macWilliams4 :
    50193 * A1 + 28809 * A2 + 14817 * A3 + 4313 * A4 + 1841 * A5 -
      87 * A6 - 511 * A7 - 263 * A8 + 81 * A9 + 201 * A10 + 33 * A11 -
      231 * A12 - 143 * A13 + 1001 * A14 = -81081
  signedShadow2 :
    -663 * A1 + 523 * A2 - 399 * A3 + 291 * A4 - 199 * A5 +
      123 * A6 - 63 * A7 + 19 * A8 + 9 * A9 - 21 * A10 + 17 * A11 +
      3 * A12 - 39 * A13 + 91 * A14 - 2048 * S2 = -819
  signedShadow3 :
    -7020 * A1 + 4788 * A2 - 3068 * A3 + 1796 * A4 - 908 * A5 +
      340 * A6 - 28 * A7 - 92 * A8 + 84 * A9 - 12 * A10 - 60 * A11 +
      68 * A12 + 52 * A13 - 364 * A14 - 2048 * S3 = -9828
  signedShadow4 :
    -50193 * A1 + 28809 * A2 - 14817 * A3 + 6361 * A4 - 1841 * A5 -
      87 * A6 + 511 * A7 - 263 * A8 - 81 * A9 + 201 * A10 - 33 * A11 -
      231 * A12 + 143 * A13 + 1001 * A14 - 2048 * S4 = -81081

end Quantum1435
